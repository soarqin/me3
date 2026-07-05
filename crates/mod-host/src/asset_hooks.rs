use std::{
    alloc::{GlobalAlloc, Layout},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::{ErrorKind, Read, Write},
    os::windows::ffi::{OsStrExt, OsStringExt},
    path::{Path, PathBuf},
    ptr::NonNull,
    slice,
    sync::{Arc, Mutex, OnceLock},
};

use base64::{prelude::BASE64_STANDARD, Engine};
use eyre::{eyre, Context, OptionExt};
use me3_binary_analysis::{fd4_step::Fd4StepTables, rtti::ClassMap};
use me3_launcher_attach_protocol::AttachConfig;
use me3_mod_host_assets::{
    bhd5::Bhd5Header,
    dl_device::{self, DlDeviceManager, DlFileOperator},
    ebl::{mount_ebl, DlDeviceEblExt, EblFileManager},
    mapping::VfsOverrideMapping,
    wwise::{find_wwise_open_file, AkOpenMode},
};
use me3_mod_host_types::{alloc::DlStdAllocator, string::DlUtf16String};
use me3_mod_protocol::Game;
use miniz_oxide::{
    deflate::compress_to_vec,
    inflate::stream::{inflate, InflateState},
    DataFormat, MZFlush, MZStatus,
};
use pkcs1::der::Decode;
use rdvec::{RawVec, Vec as DynVec};
use tempfile::NamedTempFile;
use tracing::{debug, error, info, info_span, instrument, warn};
use windows::core::{PCSTR, PCWSTR};
use xxhash_rust::xxh3;

use crate::{alloc_hooks::MIMALLOC_DLALLOC, executable::Executable, host::ModHost};

fn read_cached_bhd(path: &Path, expected_len: usize) -> Result<Option<Vec<u8>>, eyre::Error> {
    let mut cached = match OpenOptions::new().read(true).open(path) {
        Ok(cached) => cached,
        Err(e) if e.kind() == ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e.into()),
    };

    let mut cached_len_bytes = [0; 4];
    match cached.read_exact(&mut cached_len_bytes) {
        Ok(()) => {}
        Err(e) if e.kind() == ErrorKind::UnexpectedEof => return Ok(None),
        Err(e) => return Err(e.into()),
    }

    if u32::from_le_bytes(cached_len_bytes) as usize != expected_len {
        return Ok(None);
    }

    let mut compressed = vec![];
    cached.read_to_end(&mut compressed)?;

    let mut contents = vec![0; expected_len];
    let mut state = InflateState::new_boxed(DataFormat::Raw);
    let result = inflate(&mut state, &compressed, &mut contents, MZFlush::Finish);

    if !matches!(result.status, Ok(MZStatus::StreamEnd))
        || result.bytes_consumed != compressed.len()
        || result.bytes_written != expected_len
    {
        return Err(eyre!(
            "invalid cached BHD payload: status={:?}, consumed={}/{}, written={}/{}",
            result.status,
            result.bytes_consumed,
            compressed.len(),
            result.bytes_written,
            expected_len,
        ));
    }

    Ok(Some(contents))
}

fn write_cached_bhd(
    cache_dir: &Path,
    target_path: PathBuf,
    file_size: u32,
    contents: &[u8],
) -> Result<(), eyre::Error> {
    let compressed = compress_to_vec(contents, 7);
    let mut temp = NamedTempFile::new_in(cache_dir)?;

    temp.write_all(&file_size.to_le_bytes())?;
    temp.write_all(&compressed)?;
    temp.flush()?;
    temp.as_file().sync_all()?;

    temp.persist(target_path)
        .map(|_| ())
        .map_err(|e| eyre!(e.error))
}

#[instrument(name = "assets", skip_all)]
pub fn attach_override(
    attach_config: Arc<AttachConfig>,
    exe: Executable,
    class_map: Arc<ClassMap<'static>>,
    step_tables: &Fd4StepTables,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    enable_loose_params(&attach_config, &mapping);

    hook_file_init(
        attach_config,
        exe,
        class_map.clone(),
        step_tables,
        mapping.clone(),
    )?;

    if let Err(e) = try_hook_wwise(exe, &class_map, mapping.clone()) {
        debug!("error" = &*e, "skipping Wwise hook");
    }

    Ok(())
}

fn enable_loose_params(attach_config: &AttachConfig, mapping: &VfsOverrideMapping) {
    // Some Dark Souls 3 mods use a legacy Mod Engine 2 option of loading "loose" param files
    // instead of Data0. For backwards compatibility me3 enables it below.
    if attach_config.game != Game::DarkSouls3 {
        return;
    }

    static LOOSE_PARAM_FILES: [&str; 3] = [
        "data1:/param/gameparam/gameparam.parambnd.dcx",
        "data1:/param/gameparam/gameparam_dlc1.parambnd.dcx",
        "data1:/param/gameparam/gameparam_dlc2.parambnd.dcx",
    ];

    if LOOSE_PARAM_FILES
        .iter()
        .any(|file| mapping.virtual_to_disk(file).is_some())
    {
        ModHost::get_attached()
            .override_game_property("Game.Debug.EnableRegulationFile", "false")
            .unwrap();
    }
}

#[instrument(name = "file_step", skip_all)]
fn hook_file_init(
    attach_config: Arc<AttachConfig>,
    exe: Executable,
    class_map: Arc<ClassMap<'static>>,
    step_tables: &Fd4StepTables,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    let init_fn = step_tables
        .by_name("CSFileStep::STEP_Init")
        .or_else(|| step_tables.by_name("SprjFileStep::STEP_Init"))
        .ok_or_eyre("FileStep::STEP_Init not found")?;

    debug!("FileStep::STEP_Init" = ?init_fn);

    ModHost::get_attached()
        .hook(init_fn)
        .with_span(info_span!("hook"))
        .with_closure(move |p1, p2, trampoline| {
            let result = hook_device_manager(exe, mapping.clone())
                .and_then(|_| hook_mount_ebl(attach_config.clone(), exe, mapping.clone()))
                .inspect_err(|e| error!("error" = &**e, "failed apply pre-hooks"));

            unsafe {
                trampoline(p1, p2);
            }

            // `STEP_Init` has now populated `virtual_roots` and finalized the working directory.
            // The file hooks were live throughout, but lookup caching was disabled, so every
            // lookup computed against the live (partial) state without pinning anything. Enable
            // the caches now that the state is stable; on a `STEP_Init` re-run this also drops
            // results cached under the previous device state.
            mapping.reset_lookup_caches();

            if result.is_ok()
                && let Err(e) = hook_ebl_utility(exe, &class_map, mapping.clone())
            {
                error!("error" = &*e, "failed to apply post-hooks");
            }
        })
        .install()?;

    Ok(())
}

#[instrument(name = "ebl", skip_all)]
fn hook_ebl_utility(
    exe: Executable,
    class_map: &ClassMap,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    let device_manager = locate_device_manager(exe)?;

    let make_ebl_object =
        EblFileManager::make_ebl_object(exe, class_map).ok_or_eyre("MakeEblObject not found")?;

    debug!(?make_ebl_object);

    ModHost::get_attached()
        .hook(make_ebl_object)
        .with_closure({
            let mapping = mapping.clone();

            move |p1, path, p3, trampoline| {
                // Overridden paths return `None` so the game falls back to its disk
                // resolution, where the disk-device hook serves the loose file. All other
                // paths go straight to the game: the mounts stay in the device manager
                // permanently, so no per-call lock or mount push/pop is needed.
                if mapping
                    .virtual_to_disk_cached(unsafe { path.as_wide() }, |p| {
                        DlDeviceManager::lock(device_manager).expand_path(p)
                    })
                    .is_some()
                {
                    return None;
                }

                unsafe { (trampoline)(p1, path, p3) }
            }
        })
        .install()?;

    hook_ebl_device_opens(exe, mapping)?;

    info!("applied asset override hook");

    Ok(())
}

/// Guards direct opens on mounted BND4 devices (e.g. a root-prefixed `data0:/regulation.bin`),
/// which would otherwise serve archive contents and shadow a loose-file override now that the
/// mounts stay in the device manager. Overridden paths are routed through the disk device,
/// whose hooked `open_file` rewrites them to the mod file.
fn hook_ebl_device_opens(
    exe: Executable,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    static HOOKED_OPEN_FNS: Mutex<Vec<usize>> = Mutex::new(Vec::new());

    let device_manager = locate_device_manager(exe)?;

    let (open_fns, disk_device, disk_open) = {
        let device_manager = DlDeviceManager::lock(device_manager);

        (
            device_manager.bnd4_device_open_fns(),
            device_manager.disk_device(),
            device_manager.open_disk_file(),
        )
    };

    let mut hooked = HOOKED_OPEN_FNS.lock().unwrap();

    for open_fn in open_fns {
        if hooked.contains(&(open_fn as usize)) {
            continue;
        }

        ModHost::get_attached()
            .hook(open_fn)
            .with_closure({
                let mapping = mapping.clone();

                move |device, path, path_cstr, p4, p5, p6, trampoline| {
                    let has_override = unsafe { path.as_ref() }.get().is_ok_and(|path| {
                        mapping
                            .virtual_to_disk_cached(path.as_slice(), |p| {
                                DlDeviceManager::lock(device_manager).expand_path(p)
                            })
                            .is_some()
                    });

                    if has_override {
                        unsafe { disk_open(disk_device, path, path_cstr, p4, p5, p6) }
                    } else {
                        unsafe { trampoline(device, path, path_cstr, p4, p5, p6) }
                    }
                }
            })
            .install()?;

        hooked.push(open_fn as usize);
    }

    Ok(())
}

#[instrument(name = "device_manager", skip_all)]
fn hook_device_manager(
    exe: Executable,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    let device_manager = locate_device_manager(exe)?;

    let open_disk_file = DlDeviceManager::lock(device_manager).open_disk_file();

    let override_path = {
        let mapping = mapping.clone();

        move |path: &DlUtf16String| {
            let path = path.get().ok()?;

            let mapped_override = mapping.virtual_to_uid_cached(path.as_slice(), |p| {
                DlDeviceManager::lock(device_manager).expand_path(p)
            })?;

            let mut path = path.clone();

            path.replace_from_slice(mapped_override.as_ref());

            Some(path)
        }
    };

    let hook_set_path = move |file_operator: NonNull<DlFileOperator>| {
        hook_set_path(exe, file_operator, mapping.clone())
            .inspect_err(|e| error!("Failed to hook DLFileOperator::SetPath: {e}"))
            .is_ok()
    };

    ModHost::get_attached()
        .hook(open_disk_file)
        .with_closure(move |p1, path, p3, p4, p5, p6, trampoline| {
            let file_operator = if let Some(path) = override_path(unsafe { path.as_ref() }) {
                unsafe {
                    trampoline(
                        p1,
                        NonNull::from(&path).cast(),
                        PCWSTR::from_raw(path.as_ptr()),
                        p4,
                        p5,
                        p6,
                    )
                }
            } else {
                unsafe { trampoline(p1, path, p3, p4, p5, p6) }
            };

            if let Some(file_operator) = file_operator {
                static HOOK_RESULT: OnceLock<bool> = OnceLock::new();

                let _ = HOOK_RESULT.get_or_init(|| hook_set_path(file_operator));

                return Some(file_operator);
            }

            None
        })
        .install()?;

    info!("applied asset override hook");

    Ok(())
}

fn hook_set_path(
    exe: Executable,
    file_operator: NonNull<DlFileOperator>,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    let vtable = unsafe { file_operator.as_ref().as_ref() };

    let device_manager = locate_device_manager(exe)?;

    let override_path = move |path: &DlUtf16String| {
        let path = path.get().ok()?;

        let mapped_override = mapping.virtual_to_uid_cached(path.as_slice(), |p| {
            DlDeviceManager::lock(device_manager).expand_path(p)
        })?;

        let mut path = path.clone();

        path.replace_from_slice(mapped_override.as_ref());

        Some(path)
    };

    for set_path in [vtable.set_path, vtable.set_path2, vtable.set_path3] {
        let override_path = override_path.clone();

        ModHost::get_attached()
            .hook(set_path)
            .with_closure(move |p1, path, p3, p4, trampoline| {
                if let Some(path) = override_path(unsafe { path.as_ref() }) {
                    unsafe { trampoline(p1, path.as_ref().into(), p3, p4) }
                } else {
                    unsafe { trampoline(p1, path, p3, p4) }
                }
            })
            .install()?;
    }

    Ok(())
}

#[instrument(name = "mount_ebl", skip_all)]
fn hook_mount_ebl(
    attach_config: Arc<AttachConfig>,
    exe: Executable,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    fn load_cached_ebl<P, F>(
        exe: Executable,
        cache_path: P,
        bhd_path: PCWSTR,
        key_c_str: PCSTR,
        allocator: DlStdAllocator,
        trampoline: F,
    ) -> Result<(), eyre::Error>
    where
        P: AsRef<Path>,
        F: Fn(PCWSTR) -> bool,
    {
        let mut device_manager = DlDeviceManager::lock(locate_device_manager(exe)?);

        let expanded = unsafe { device_manager.expand_path(bhd_path.as_wide()) };
        let bhd_path = OsString::from_wide(&expanded);

        // Parse the public RSA key to know the block size for decryption.
        let pub_key_size = key_size_from_pem_c_str(key_c_str)?;

        // Read the original file for hashing to use as the cached file name.
        let original = Arc::new(std::fs::read(&bhd_path)?);

        // When changing storage or compression defaults, don't forget to change the seed.
        let hash = std::thread::spawn({
            let original = original.clone();
            move || xxh3::xxh3_128_with_seed(&original, 1)
        });

        // Write a temporary file with the size of a single block and have the
        // game decrypt it, which creates an EblFileDevice and lets us read
        // the original file size.
        let mut stub_file = NamedTempFile::new().with_context(|| "creating stub file")?;
        stub_file.write_all(&original[..Ord::min(pub_key_size, original.len())])?;

        let snap = device_manager.snapshot()?;

        invoke_trampoline(&trampoline, &stub_file)?;

        let new_mounts = device_manager.extract_new(snap);

        let mut device = new_mounts
            .devices()
            .next()
            .ok_or_eyre("no devices were added")?;

        let original_len = unsafe {
            device
                .as_ref()
                .as_bhd_holder_unchecked()
                .bhd_header()
                .map(Bhd5Header::file_size)
        };

        let hash = hash.join().expect("thread panicked");

        let cached_bhd_path = cache_path.as_ref().join(format!("{hash:032x?}.bhd.zz"));

        let cached_contents = match original_len {
            Some(len) => match read_cached_bhd(&cached_bhd_path, len as usize) {
                Ok(contents) => contents,
                Err(e) => {
                    warn!(
                        error = %e,
                        path = %cached_bhd_path.display(),
                        "invalid cached BHD; falling back to game decrypt"
                    );
                    let _ = fs::remove_file(&cached_bhd_path);
                    None
                }
            },
            None => None,
        };

        if let Some(contents) = cached_contents {
            // Opened a cached decrypted file, validate/decompress and assign its contents.
            // Use the game's own allocator as it will be freed with it later.
            let buf = unsafe {
                let ptr = NonNull::new(
                    allocator.alloc(Layout::from_size_align_unchecked(contents.len(), 4096)),
                )
                .ok_or_eyre("failed to allocate buffer for cached file")?;

                slice::from_raw_parts_mut(ptr.as_ptr(), contents.len())
            };
            buf.copy_from_slice(&contents);

            unsafe {
                device
                    .as_mut()
                    .as_mut_bhd_holder_unchecked()
                    .assign_bhd_contents(buf.as_mut_ptr().cast());
            }

            device_manager.push_vfs_mounts_permanent(new_mounts);
        } else {
            let snap = device_manager.snapshot()?;

            invoke_trampoline(&trampoline, &bhd_path)?;

            let new_mounts = device_manager.extract_new(snap);

            let device = new_mounts
                .devices()
                .next()
                .ok_or_eyre("no devices were added")?;

            let header = unsafe {
                device
                    .as_ref()
                    .as_bhd_holder_unchecked()
                    .bhd_header()
                    .ok_or_eyre("BHD header is null")?
            };

            device_manager.push_vfs_mounts_permanent(new_mounts);

            // Successfully mounted the ebl, do not report subsequent caching errors.
            let _ = write_cached_bhd(
                cache_path.as_ref(),
                cached_bhd_path,
                header.file_size(),
                header.as_slice(),
            )
            .inspect_err(|e| warn!(error = %e, "failed to write cached BHD"));
        }

        Ok(())
    }

    fn key_size_from_pem_c_str(key_c_str: PCSTR) -> Result<usize, eyre::Error> {
        let key_str = unsafe { str::from_utf8(key_c_str.as_bytes())? };

        let mut lines = key_str.lines();

        let _ = lines
            .next()
            .filter(|str| *str == "-----BEGIN RSA PUBLIC KEY-----")
            .ok_or_eyre("malformed PEM")?;

        let _ = lines
            .next_back()
            .filter(|str| *str == "-----END RSA PUBLIC KEY-----")
            .ok_or_eyre("malformed PEM")?;

        let is_base64char = |c: &char| c.is_ascii_alphanumeric() | ['+', '/', '='].contains(c);

        let mut normalized = String::with_capacity(key_str.len());
        normalized.extend(lines.flat_map(|line| line.chars().filter(is_base64char)));

        let der = BASE64_STANDARD.decode(&normalized)?;
        let pub_key = pkcs1::RsaPublicKey::from_der(&der)?;

        let size = pub_key.modulus.len().try_into()?;

        Ok(size)
    }

    fn invoke_trampoline<S, F>(trampoline: &F, bhd_path: S) -> Result<(), eyre::Error>
    where
        S: AsRef<Path>,
        F: Fn(PCWSTR) -> bool,
    {
        let mut bhd_path = bhd_path.as_ref().to_owned().into_os_string();

        bhd_path.push("\0");
        let bhd_path = bhd_path.encode_wide().collect::<Vec<_>>();

        match trampoline(PCWSTR::from_raw(bhd_path.as_ptr())) {
            true => Ok(()),
            false => Err(eyre!("trampoline returned null")),
        }
    }

    let mount_ebl = mount_ebl(exe).ok_or_eyre("MountEbl not found")?;

    debug!(?mount_ebl);

    ModHost::get_attached()
        .hook(mount_ebl)
        .with_span(info_span!("hook"))
        .with_closure(move |p1, p2, p3, p4, p5, p6, trampoline| {
            let result = 'mount: {
                if attach_config.boot_boost && let Some(cache_path) = &attach_config.cache_path {
                    match load_cached_ebl(exe, cache_path, p2, p5, p4, |p2| unsafe {
                        trampoline(p1, p2, p3, p4, p5, p6)
                    }) {
                        Ok(()) => break 'mount true,
                        Err(e) => {
                            error!("error" = &*e, key = %unsafe { str::from_utf8(p5.as_bytes()).unwrap() });
                        }
                    }
                }

                unsafe { trampoline(p1, p2, p3, p4, p5, p6) }
            };

            // The mounts stay in the device manager permanently, so any device mounted
            // after `STEP_Init` needs its `open_file` hooked for override precedence too.
            if result && let Err(e) = hook_ebl_device_opens(exe, mapping.clone()) {
                error!("error" = &*e, "failed to hook EBL device opens");
            }

            result
        })
        .install()?;

    info!("applied asset override hook");

    Ok(())
}

#[instrument(name = "wwise", skip_all)]
fn try_hook_wwise(
    exe: Executable,
    class_map: &ClassMap,
    mapping: Arc<VfsOverrideMapping>,
) -> Result<(), eyre::Error> {
    let wwise_open_file =
        find_wwise_open_file(exe, class_map).ok_or_eyre("WwiseOpenFileByName not found")?;

    ModHost::get_attached()
        .hook(wwise_open_file)
        .with_closure(move |p1, path, open_mode, p4, p5, p6, trampoline| {
            let path_string = unsafe { path.to_string().unwrap() };

            if let Some(mapped_override) = mapping.wwise_override_cached(&path_string) {
                // Force lookup to wwise's ordinary read (from disk) mode instead of the EBL read.
                unsafe {
                    trampoline(
                        p1,
                        mapped_override.as_pcwstr(),
                        AkOpenMode::Read as _,
                        p4,
                        p5,
                        p6,
                    )
                }
            } else {
                unsafe { trampoline(p1, path, open_mode, p4, p5, p6) }
            }
        })
        .install()?;

    info!("applied asset override hook");

    Ok(())
}

fn locate_device_manager(
    exe: Executable,
) -> Result<NonNull<DlDeviceManager>, dl_device::FindError> {
    struct DeviceManager(Result<NonNull<DlDeviceManager>, dl_device::FindError>);

    static DEVICE_MANAGER: OnceLock<DeviceManager> = OnceLock::new();

    unsafe impl Send for DeviceManager {}
    unsafe impl Sync for DeviceManager {}

    DEVICE_MANAGER
        .get_or_init(|| DeviceManager(dl_device::find_device_manager(exe, Some(&MIMALLOC_DLALLOC))))
        .0
        .clone()
}

#[cfg(test)]
mod tests {
    use super::{read_cached_bhd, write_cached_bhd};
    use miniz_oxide::deflate::compress_to_vec;

    #[test]
    fn cached_bhd_round_trips() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("cache.bhd.zz");
        let contents = b"decrypted bhd contents";

        write_cached_bhd(temp.path(), target.clone(), contents.len() as u32, contents).unwrap();

        let cached = read_cached_bhd(&target, contents.len()).unwrap().unwrap();
        assert_eq!(cached, contents);
    }

    #[test]
    fn cached_bhd_length_mismatch_is_cache_miss() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("cache.bhd.zz");
        let contents = b"decrypted bhd contents";

        write_cached_bhd(temp.path(), target.clone(), contents.len() as u32, contents).unwrap();

        assert!(read_cached_bhd(&target, contents.len() + 1)
            .unwrap()
            .is_none());
    }

    #[test]
    fn cached_bhd_rejects_truncated_payload() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("cache.bhd.zz");
        let contents = b"decrypted bhd contents";
        let compressed = compress_to_vec(contents, 7);
        let mut file = (contents.len() as u32).to_le_bytes().to_vec();
        file.extend_from_slice(&compressed[..compressed.len() / 2]);

        std::fs::write(&target, file).unwrap();

        assert!(read_cached_bhd(&target, contents.len()).is_err());
    }

    #[test]
    fn cached_bhd_rejects_garbage_payload() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("cache.bhd.zz");
        let contents = b"decrypted bhd contents";
        let mut file = (contents.len() as u32).to_le_bytes().to_vec();
        file.extend_from_slice(b"not deflate data");

        std::fs::write(&target, file).unwrap();

        assert!(read_cached_bhd(&target, contents.len()).is_err());
    }
}
