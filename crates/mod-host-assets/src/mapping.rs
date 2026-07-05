use std::{
    borrow::{Borrow, Cow},
    collections::HashMap,
    env,
    ffi::{OsStr, OsString},
    fmt,
    fs::read_dir,
    hash::Hash,
    io, iter,
    os::windows::{
        ffi::{OsStrExt, OsStringExt},
        fs::FileTypeExt,
    },
    path::{Path, PathBuf, StripPrefixError},
    ptr::NonNull,
    sync::{
        atomic::{AtomicU64, Ordering},
        RwLock,
    },
};

use me3_mod_protocol::package::{AssetOverrideSource, Package};
use normpath::PathExt;
use rayon::iter::{ParallelBridge, ParallelIterator};
use slab::Slab;
use smallvec::{smallvec_inline, SmallVec};
use thiserror::Error;
use windows::core::PCWSTR;
use xxhash_rust::xxh3::Xxh3DefaultBuilder;

use crate::{mapping::savefile::SavefileOverrideMapping, platform::normalize_dos_path, wwise};

mod savefile;

/// A cached lookup result: a pointer into the frozen override slab (or the savefile `OnceLock`),
/// or `None` as a "no override" sentinel. Safe to share across threads because the targets are
/// stable after construction (see the `Send`/`Sync` impls below).
#[derive(Clone, Copy)]
struct CachedOverride(Option<NonNull<VfsOverride<'static>>>);

/// A cached virtual-path result for callers that must hand the game a fake `\\me3` UID instead
/// of the real disk path. Savefile overrides are kept as direct disk paths, matching
/// `virtual_to_uid`.
#[derive(Clone, Copy)]
struct CachedUidOverride(Option<CachedUidTarget>);

#[derive(Clone, Copy)]
enum CachedUidTarget {
    Static(NonNull<VfsOverride<'static>>),
    Indexed {
        index: usize,
        generation: Generation,
    },
}

enum VirtualTarget<'a> {
    Static(&'a VfsOverride<'static>),
    Indexed(usize),
}

// SAFETY: cached pointers target stable storage:
//  1. `VfsOverrideMapping::overrides` — frozen after directory scanning, before caches are enabled.
//  2. `SavefileOverrideMapping::override_path` — a `OnceLock` that is stable after first init.
// `VfsOverride` holds only owned `Box` data plus borrowed display strings that point at the same
// stable override storage. The cache `RwLock` write/read pair provides cross-thread visibility.
unsafe impl Send for CachedOverride {}
unsafe impl Sync for CachedOverride {}
unsafe impl Send for CachedUidOverride {}
unsafe impl Sync for CachedUidOverride {}

pub struct VfsOverrideMapping {
    current_dir: VfsKey,
    vfs_map: HashMap<VfsKey, usize, Xxh3DefaultBuilder>,
    overrides: Slab<VfsOverride<'static>>,
    savefile_override: Option<SavefileOverrideMapping>,
    /// Cache generation; [`Self::CACHES_DISABLED`] until the first `reset_lookup_caches` call.
    generation: AtomicU64,
    // INVARIANT: cached results are only valid for the `DlDeviceManager::virtual_roots` and
    // working-directory state they were computed against. The filling hooks (`CreateFile*`,
    // `open_disk_file`, `SetPath`, Wwise) go live before the game finalizes that state during
    // `STEP_Init`, so `cached_*_lookup` enforces two guards via `generation`:
    //  1. Caching is disabled (`generation == CACHES_DISABLED`) until `reset_lookup_caches` is
    //     first called right after `STEP_Init`; mid-init lookups always compute uncached.
    //  2. An insert re-checks the generation it was computed under, so a lookup that straddles
    //     a reset cannot pin a result computed against the previous device state.
    //
    // Each cache serves a single lookup semantics and must NOT be shared: the same bytes resolve
    // differently per key builder and per result type (`disk_or_uid_to_disk` yields disk paths,
    // `virtual_to_uid` yields fake UID paths for regular assets), so a shared `None` or hit would
    // poison another domain.
    /// Disk/UID-path wide-byte cache (CreateFileW/2, CreateDirectory*, DeleteFileW).
    disk_wide_cache: RwLock<HashMap<Box<[u16]>, CachedOverride>>,
    /// Disk/UID-path narrow-byte cache (CreateFileA, CreateDirectoryA, DeleteFileA).
    disk_narrow_cache: RwLock<HashMap<Box<[u8]>, CachedOverride>>,
    /// VFS-path wide-byte cache for callers that need the real disk override.
    virtual_disk_wide_cache: RwLock<HashMap<Box<[u16]>, CachedOverride>>,
    /// VFS-path wide-byte cache for callers that need a fake `\\me3` UID path.
    virtual_uid_wide_cache: RwLock<HashMap<Box<[u16]>, CachedUidOverride>>,
    /// Wwise sound-path narrow-byte cache (multi-prefix fan-out lookup).
    wwise_narrow_cache: RwLock<HashMap<Box<[u8]>, CachedOverride>>,
}

#[derive(Clone)]
pub struct VfsOverride<'a> {
    generation: Generation,
    wide_c_str: Box<[u16]>,
    display: Cow<'a, str>,
}

#[derive(Debug, Error)]
pub enum VfsOverrideMappingError {
    #[error("An error occurred while converting Linux paths for WINE")]
    Compatibility,

    #[error("Package source specified is not a directory {0}.")]
    InvalidDirectory(PathBuf),

    #[error("Could not read directory while discovering override assets {0}")]
    ReadDir(io::Error),

    #[error("Could not acquire directory entry")]
    StripPrefix(#[from] StripPrefixError),
}

impl VfsOverrideMapping {
    /// `generation` value under which lookup caching is disabled.
    const CACHES_DISABLED: u64 = 0;

    pub fn new() -> Result<Self, VfsOverrideMappingError> {
        let current_dir = env::current_dir()
            .and_then(VfsKey::for_disk_path)
            .map_err(VfsOverrideMappingError::ReadDir)?;

        Ok(Self {
            current_dir,
            vfs_map: HashMap::default(),
            overrides: Slab::new(),
            savefile_override: None,
            generation: AtomicU64::new(Self::CACHES_DISABLED),
            disk_wide_cache: RwLock::new(HashMap::new()),
            disk_narrow_cache: RwLock::new(HashMap::new()),
            virtual_disk_wide_cache: RwLock::new(HashMap::new()),
            virtual_uid_wide_cache: RwLock::new(HashMap::new()),
            wwise_narrow_cache: RwLock::new(HashMap::new()),
        })
    }

    /// Scans a set of directories, mapping discovered assets into itself.
    pub fn scan_directories<I>(&mut self, sources: I) -> Result<(), VfsOverrideMappingError>
    where
        I: Iterator<Item: AssetOverrideSource>,
    {
        fn scan_directories_inner(
            base_dir: &Path,
            root_key: &VfsKey,
        ) -> SmallVec<[Result<(VfsKey, VfsOverride<'static>), io::Error>; 1]> {
            let entries = match read_dir(base_dir) {
                Ok(entries) => entries,
                Err(e) => return smallvec_inline![Err(e)],
            };

            let result = entries
                .flatten()
                .par_bridge()
                .flat_map_iter(|dir_entry| match dir_entry.file_type() {
                    Ok(file_type) if file_type.is_dir() || file_type.is_symlink_dir() => {
                        scan_directories_inner(&dir_entry.path(), root_key)
                    }
                    Ok(_) => {
                        let path = dir_entry.path();

                        let result = VfsKey::for_asset_path(&path, root_key).map(|vfs_key| {
                            let display = path.to_string_lossy().into_owned();
                            (vfs_key, VfsOverride::new(path, Generation, display.into()))
                        });

                        smallvec_inline![result]
                    }
                    Err(e) => smallvec_inline![Err(e)],
                })
                .collect();

            SmallVec::from_vec(result)
        }

        for source in sources {
            let source_path = source.asset_path();
            let normalized_path = normalize_dos_path(source_path)?;
            let root_key = VfsKey::for_disk_path(&normalized_path)
                .map_err(VfsOverrideMappingError::ReadDir)?;

            let scanned_directories = scan_directories_inner(&normalized_path, &root_key);

            self.overrides.reserve(scanned_directories.len());
            self.vfs_map.reserve(scanned_directories.len());

            for result in scanned_directories {
                let (vfs_key, vfs_override) = result.map_err(VfsOverrideMappingError::ReadDir)?;

                let index = self.overrides.insert(vfs_override);
                self.vfs_map.insert(vfs_key, index);
            }
        }

        Ok(())
    }

    pub fn scan_directory<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> Result<(), VfsOverrideMappingError> {
        let package = Package::new(path.as_ref().to_owned());
        self.scan_directories(iter::once(&package))
    }

    pub fn add_savefile_override<P, F>(&mut self, savefile_dir: P, f: F) -> Result<(), io::Error>
    where
        P: AsRef<Path>,
        F: Fn(&Path) -> PathBuf + Send + Sync + 'static,
    {
        let savefile_override = SavefileOverrideMapping::new(savefile_dir, f)?;
        self.savefile_override = Some(savefile_override);
        Ok(())
    }

    pub fn virtual_to_disk<S: AsRef<OsStr>>(&self, path_str: S) -> Option<&VfsOverride<'static>> {
        match self.virtual_target(Path::new(&path_str))? {
            VirtualTarget::Static(vfs_override) => Some(vfs_override),
            VirtualTarget::Indexed(index) => self.overrides.get(index),
        }
    }

    pub fn virtual_to_uid<S: AsRef<OsStr>>(&self, path_str: S) -> Option<VfsOverride<'_>> {
        let target = self.virtual_to_uid_target(path_str)?;
        self.uid_target_to_override(target)
    }

    pub fn disk_or_uid_to_disk<S: AsRef<OsStr>>(
        &self,
        path_str: S,
    ) -> Option<&VfsOverride<'static>> {
        if let Some(from_uid) = self.uid_to_disk(path_str.as_ref()) {
            return Some(from_uid);
        }

        let key = VfsKey::for_asset_path(Path::new(&path_str), &self.current_dir).ok()?;
        let index = self.vfs_map.get(&key)?;

        self.overrides.get(*index)
    }

    fn virtual_target(&self, path: &Path) -> Option<VirtualTarget<'_>> {
        if let Some(savefile_override) = self.virtual_to_savefile(path) {
            return Some(VirtualTarget::Static(savefile_override));
        }

        let key = VfsKey::for_vfs_path(path);
        self.vfs_map.get(&key).copied().map(VirtualTarget::Indexed)
    }

    fn virtual_to_savefile(&self, path: &Path) -> Option<&VfsOverride<'static>> {
        let savefile_override = self.savefile_override.as_ref()?;
        let key = VfsKey::for_disk_path(path).ok()?;
        savefile_override.try_override(path, &key)
    }

    fn uid_to_disk(&self, uid_str: &OsStr) -> Option<&VfsOverride<'static>> {
        let VfsUid { generation, index } = VfsUid::try_parse(uid_str)?;
        let vfs_override = self.overrides.get(index)?;

        (generation == vfs_override.generation).then_some(vfs_override)
    }

    fn virtual_to_uid_target<S: AsRef<OsStr>>(&self, path_str: S) -> Option<CachedUidTarget> {
        match self.virtual_target(Path::new(&path_str))? {
            VirtualTarget::Static(vfs_override) => {
                Some(CachedUidTarget::Static(vfs_override.into()))
            }
            VirtualTarget::Indexed(index) => {
                let vfs_override = self.overrides.get(index)?;
                Some(CachedUidTarget::Indexed {
                    index,
                    generation: vfs_override.generation,
                })
            }
        }
    }

    fn uid_target_to_override(&self, target: CachedUidTarget) -> Option<VfsOverride<'_>> {
        match target {
            CachedUidTarget::Static(vfs_override) => {
                // SAFETY: points into stable override storage; see `CachedUidOverride`.
                Some(unsafe { vfs_override.as_ref() }.clone())
            }
            CachedUidTarget::Indexed { index, generation } => {
                let vfs_override = self.overrides.get(index)?;
                if vfs_override.generation != generation {
                    return None;
                }

                let vfs_uid = VfsUid::new(index, generation);
                let uid_path = vfs_uid.to_uid_string();

                Some(VfsOverride::new(
                    uid_path,
                    generation,
                    Cow::Borrowed(&vfs_override.display),
                ))
            }
        }
    }

    fn uid_target_display(&self, target: CachedUidTarget) -> Option<&str> {
        match target {
            CachedUidTarget::Static(vfs_override) => {
                // SAFETY: points into stable override storage; see `CachedUidOverride`.
                Some(unsafe { vfs_override.as_ref() }.as_display_str())
            }
            CachedUidTarget::Indexed { index, generation } => {
                let vfs_override = self.overrides.get(index)?;
                (vfs_override.generation == generation).then(|| vfs_override.as_display_str())
            }
        }
    }

    /// Strips trailing NUL units so the same input maps to one cache key regardless of
    /// NUL-termination (Windows path APIs return NUL-terminated strings; `DlUtf16String` does not).
    fn strip_trailing_null_wide(s: &[u16]) -> &[u16] {
        let n = s.iter().rev().take_while(|&&c| c == 0).count();
        &s[..s.len().saturating_sub(n)]
    }

    /// Strips trailing NUL bytes from a narrow-byte slice (CreateFileA path strings).
    fn strip_trailing_null_narrow(s: &[u8]) -> &[u8] {
        let n = s.iter().rev().take_while(|&&c| c == 0).count();
        &s[..s.len().saturating_sub(n)]
    }

    /// Serves `compute` results out of `cache`, keyed by `key`, including a `None` sentinel for
    /// "no override".
    ///
    /// Caching is generation-gated: while the caches are disabled (before the first
    /// [`Self::reset_lookup_caches`] call) every lookup computes uncached, and an insert is
    /// discarded when the generation advanced while computing, so a result computed against a
    /// previous device state can never be pinned into a newer generation.
    fn cached_override_lookup<'a, U>(
        &'a self,
        cache: &RwLock<HashMap<Box<[U]>, CachedOverride>>,
        key: &[U],
        compute: impl FnOnce() -> Option<&'a VfsOverride<'static>>,
    ) -> Option<&'a VfsOverride<'static>>
    where
        U: Copy + Eq + Hash,
    {
        let generation = self.generation.load(Ordering::Acquire);

        if generation == Self::CACHES_DISABLED {
            return compute();
        }

        if let Ok(cache) = cache.read() {
            if let Some(hit) = cache.get(key) {
                // SAFETY: cached pointers target the frozen override slab or savefile `OnceLock`,
                // both stable for the lifetime of `self` (see `CachedOverride`).
                return hit.0.map(|ptr| unsafe { ptr.as_ref() });
            }
        }

        let result = compute();

        // Log the resolved override on the compute path only: once per unique input path, never
        // on cache hits. Logging per open would emit formatted IPC messages for every hooked file
        // request, which can stall the game's asset-streaming threads.
        if let Some(mapped_override) = result {
            tracing::info!(r#override = %mapped_override);
        }

        if let Ok(mut cache) = cache.write() {
            if self.generation.load(Ordering::Acquire) == generation {
                cache.insert(key.into(), CachedOverride(result.map(NonNull::from)));
            }
        }

        result
    }

    fn cached_uid_lookup<'a, U>(
        &'a self,
        cache: &RwLock<HashMap<Box<[U]>, CachedUidOverride>>,
        key: &[U],
        compute: impl FnOnce() -> Option<CachedUidTarget>,
    ) -> Option<VfsOverride<'a>>
    where
        U: Copy + Eq + Hash,
    {
        let generation = self.generation.load(Ordering::Acquire);

        if generation == Self::CACHES_DISABLED {
            return compute().and_then(|target| self.uid_target_to_override(target));
        }

        if let Ok(cache) = cache.read() {
            if let Some(hit) = cache.get(key) {
                return hit.0.and_then(|target| self.uid_target_to_override(target));
            }
        }

        let result = compute();

        if let Some(target) = result
            && let Some(override_display) = self.uid_target_display(target)
        {
            tracing::info!(r#override = %override_display);
        }

        if let Ok(mut cache) = cache.write() {
            if self.generation.load(Ordering::Acquire) == generation {
                cache.insert(key.into(), CachedUidOverride(result));
            }
        }

        result.and_then(|target| self.uid_target_to_override(target))
    }

    /// Cached lookup for a wide-byte disk or fake-UID path (CreateFileW/2,
    /// CreateDirectoryW/ExW, DeleteFileW).
    pub fn disk_override_cached(&self, path: &[u16]) -> Option<&VfsOverride<'static>> {
        let path = Self::strip_trailing_null_wide(path);

        self.cached_override_lookup(&self.disk_wide_cache, path, || {
            self.disk_or_uid_to_disk(OsString::from_wide(path))
        })
    }

    /// Cached lookup for a narrow-byte disk or fake-UID path (CreateFileA, CreateDirectoryA,
    /// DeleteFileA).
    pub fn narrow_override_cached(&self, path: &[u8]) -> Option<&VfsOverride<'static>> {
        let path = Self::strip_trailing_null_narrow(path);

        self.cached_override_lookup(&self.disk_narrow_cache, path, || {
            std::str::from_utf8(path)
                .ok()
                .and_then(|s| self.disk_or_uid_to_disk(s))
        })
    }

    /// Cached lookup for an asset/VFS wide-byte path where the caller needs the real disk path.
    /// `expand` runs only on a miss and should expand virtual roots via `DlDeviceManager`.
    pub fn virtual_to_disk_cached<'a, 'p>(
        &'a self,
        path: &'p [u16],
        expand: impl FnOnce(&'p [u16]) -> Cow<'p, [u16]>,
    ) -> Option<&'a VfsOverride<'static>> {
        let path = Self::strip_trailing_null_wide(path);

        self.cached_override_lookup(&self.virtual_disk_wide_cache, path, || {
            let expanded = expand(path);
            self.virtual_to_disk(OsString::from_wide(&expanded))
        })
    }

    /// Cached lookup for an asset/VFS wide-byte path where the caller must expose a fake
    /// `\\me3` UID path to the game instead of the real disk path.
    pub fn virtual_to_uid_cached<'a, 'p>(
        &'a self,
        path: &'p [u16],
        expand: impl FnOnce(&'p [u16]) -> Cow<'p, [u16]>,
    ) -> Option<VfsOverride<'a>> {
        let path = Self::strip_trailing_null_wide(path);

        self.cached_uid_lookup(&self.virtual_uid_wide_cache, path, || {
            let expanded = expand(path);
            self.virtual_to_uid_target(OsString::from_wide(&expanded))
        })
    }

    /// Cached lookup for a Wwise sound path. The key is the raw input string bytes; the full
    /// multi-prefix fan-out (`find_override`) only runs on a miss. One hit skips up to 9
    /// `virtual_to_disk` calls and their `format!` allocations.
    pub fn wwise_override_cached(&self, input: &str) -> Option<&VfsOverride<'static>> {
        self.cached_override_lookup(&self.wwise_narrow_cache, input.as_bytes(), || {
            wwise::find_override(self, input)
        })
    }

    /// Advances the cache generation: the first call enables lookup caching, later calls also
    /// drop every result cached under previous generations.
    ///
    /// Called right after `CSFileStep::STEP_Init`, once `virtual_roots` and the working
    /// directory are finalized. Lookups made before then compute uncached (generation 0), and a
    /// lookup straddling a reset — computed under the old generation, inserted after — is
    /// discarded by the insert re-check in `cached_*_lookup`, so no result computed against a
    /// partial device state can be pinned. The bump precedes the clears: a hit served from a
    /// not-yet-cleared cache is no worse than the same lookup racing just before the reset.
    pub fn reset_lookup_caches(&self) {
        self.generation.fetch_add(1, Ordering::AcqRel);

        if let Ok(mut cache) = self.disk_wide_cache.write() {
            cache.clear();
        }
        if let Ok(mut cache) = self.disk_narrow_cache.write() {
            cache.clear();
        }
        if let Ok(mut cache) = self.virtual_disk_wide_cache.write() {
            cache.clear();
        }
        if let Ok(mut cache) = self.virtual_uid_wide_cache.write() {
            cache.clear();
        }
        if let Ok(mut cache) = self.wwise_narrow_cache.write() {
            cache.clear();
        }
    }
}

impl<'a> VfsOverride<'a> {
    fn new<P: AsRef<OsStr>>(path: P, generation: Generation, display: Cow<'a, str>) -> Self {
        Self {
            generation,
            wide_c_str: path.as_ref().encode_wide().chain([0]).collect(),
            display,
        }
    }

    pub fn to_path_buf(&self) -> PathBuf {
        PathBuf::from(OsString::from_wide(self.as_wide()))
    }

    pub fn to_c_string(&self) -> Vec<u8> {
        OsString::from_wide(self.as_wide_c_string()).into_encoded_bytes()
    }

    pub fn as_wide(&self) -> &[u16] {
        &self.wide_c_str[..self.wide_c_str.len() - 1]
    }

    pub fn as_wide_c_string(&self) -> &[u16] {
        &self.wide_c_str
    }

    pub fn as_pcwstr(&self) -> PCWSTR {
        PCWSTR(self.as_wide_c_string().as_ptr())
    }

    pub fn as_display_str(&self) -> &str {
        &self.display
    }
}

impl AsRef<[u16]> for VfsOverride<'_> {
    fn as_ref(&self) -> &[u16] {
        self.as_wide()
    }
}

impl From<&VfsOverride<'_>> for PCWSTR {
    fn from(vfs_override: &VfsOverride<'_>) -> Self {
        vfs_override.as_pcwstr()
    }
}

impl fmt::Debug for VfsOverride<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VfsOverride")
            .field("generation", &self.generation)
            .field("path", &self.to_path_buf())
            .field("display", &self.as_display_str())
            .finish()
    }
}

impl fmt::Display for VfsOverride<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_display_str())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct VfsUid {
    generation: Generation,
    index: usize,
}

// May become a `usize` in the future to implement asset reloading.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Generation;

impl VfsUid {
    const ROOT: &str = r"\\me3";

    fn new(index: usize, generation: Generation) -> Self {
        Self { generation, index }
    }

    pub fn to_uid_string(self) -> String {
        self.with_fmt_args(|fmt| format!("{fmt}"))
    }

    pub fn try_parse(str: &OsStr) -> Option<Self> {
        let str = str.to_str()?;

        let index_str = str.strip_prefix(Self::ROOT)?.strip_prefix("??")?;
        let index = usize::from_str_radix(index_str, 16).ok()?;

        Some(Self::new(index, Generation))
    }

    #[inline(always)]
    fn with_fmt_args<T>(&self, f: impl FnOnce(fmt::Arguments<'_>) -> T) -> T {
        let root = Self::ROOT;
        let generation = "";
        let index = self.index;

        f(format_args!("{root}?{generation}?{index:x}"))
    }
}

impl fmt::Display for VfsUid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with_fmt_args(|fmt| f.write_fmt(fmt))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct VfsKey(Box<Path>);

impl VfsKey {
    /// Turns a disk path into an asset lookup key that includes the root directory.
    fn for_disk_path<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> {
        let normalized = path
            .as_ref()
            .normalize_virtually()?
            .components()
            .map(|c| c.as_os_str().to_string_lossy().to_lowercase())
            .collect();

        Ok(Self(PathBuf::into_boxed_path(normalized)))
    }

    /// Turns a vfs path into an asset lookup key that does not include the root directory.
    fn for_vfs_path<P: AsRef<Path>>(path: P) -> Self {
        let normalized = path
            .as_ref()
            .components()
            .skip_while(|c| matches!(c.as_os_str().as_encoded_bytes().last(), Some(b':')))
            .map(|c| c.as_os_str().to_string_lossy().to_lowercase())
            .collect();

        Self(PathBuf::into_boxed_path(normalized))
    }

    /// Turns a disk path into an asset lookup key that does not include the root directory.
    fn for_asset_path<P: AsRef<Path>>(path: P, base: &Self) -> Result<Self, io::Error> {
        Self::for_disk_path(path)?.strip_prefix(base)
    }

    /// Strips the root directory from a disk asset lookup key.
    fn strip_prefix(&self, base: &Self) -> Result<Self, io::Error> {
        let stripped = self
            .0
            .strip_prefix(base)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidFilename, e))?;

        Ok(Self(stripped.into()))
    }
}

impl AsRef<Path> for VfsKey {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl Borrow<Path> for VfsKey {
    fn borrow(&self) -> &Path {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use std::{borrow::Cow, ffi::OsString, os::windows::ffi::OsStringExt, path::Path};

    use super::{VfsKey, VfsOverrideMapping};

    #[test]
    fn asset_path_lookup_keys() {
        const FAKE_MOD_BASE: &str = "D:/ModBase";
        let base_path = VfsKey::for_disk_path(Path::new(FAKE_MOD_BASE)).unwrap();

        assert_eq!(
            VfsKey::for_asset_path(
                Path::new(&format!(
                    "{FAKE_MOD_BASE}/parts/aet/aet007/aet007_071.tpf.dcx"
                )),
                &base_path
            )
            .unwrap()
            .as_ref(),
            Path::new("parts/aet/aet007/aet007_071.tpf.dcx"),
        );

        assert_eq!(
            VfsKey::for_asset_path(
                Path::new(&format!(
                    "{FAKE_MOD_BASE}/hkxbnd/m60_42_36_00/h60_42_36_00_423601.hkx.dcx"
                )),
                &base_path
            )
            .unwrap()
            .as_ref(),
            Path::new("hkxbnd/m60_42_36_00/h60_42_36_00_423601.hkx.dcx"),
        );

        assert_eq!(
            VfsKey::for_asset_path(
                Path::new(&format!("{FAKE_MOD_BASE}/regulation.bin")),
                &base_path
            )
            .unwrap()
            .as_ref(),
            Path::new("regulation.bin"),
        );
    }

    #[test]
    fn scan_directory_and_overrides() {
        let asset_mapping = test_mapping();

        assert!(
            asset_mapping
                .virtual_to_uid("data0:/regulation.bin")
                .is_some(),
            "override for regulation.bin was not found"
        );
        assert!(
            asset_mapping
                .virtual_to_uid("data0:/event/common.emevd.dcx")
                .is_some(),
            "override for event/common.emevd.dcx not found"
        );
        assert!(
            asset_mapping
                .virtual_to_uid("data0:/common.emevd.dcx")
                .is_none(),
            "event/common.emevd.dcx was found incorrectly under the regulation root"
        );
    }

    /// Build a mapping over the test mod directory. Lookup caching starts disabled, exactly as
    /// in production before `STEP_Init` completes.
    fn test_mapping() -> VfsOverrideMapping {
        let mut asset_mapping = VfsOverrideMapping::new().unwrap();
        let test_mod_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("test-data/test-mod");
        asset_mapping.scan_directory(test_mod_dir).unwrap();
        asset_mapping
    }

    /// Build a mapping with lookup caching enabled, as after `STEP_Init`.
    fn cached_test_mapping() -> VfsOverrideMapping {
        let mapping = test_mapping();
        mapping.reset_lookup_caches();
        mapping
    }

    #[test]
    fn virtual_to_disk_cached_matches_uncached() {
        let mapping = cached_test_mapping();

        let input = wstr_u16("data0:/regulation.bin");
        let uncached = mapping.virtual_to_disk(OsString::from_wide(&input));
        let cached = mapping.virtual_to_disk_cached(&input, |p| Cow::Borrowed(p));
        assert_eq!(
            uncached.map(|v| v.to_path_buf()),
            cached.map(|v| v.to_path_buf()),
            "cached hit must match uncached lookup"
        );
        assert!(cached.is_some(), "regulation.bin override should exist");
    }

    #[test]
    fn virtual_to_uid_cached_matches_uncached() {
        let mapping = cached_test_mapping();

        let input = wstr_u16("data0:/event/common.emevd.dcx");
        let uncached = mapping.virtual_to_uid(OsString::from_wide(&input));
        let cached = mapping.virtual_to_uid_cached(&input, |p| Cow::Borrowed(p));
        assert_eq!(
            uncached.as_ref().map(|v| v.as_wide()),
            cached.as_ref().map(|v| v.as_wide()),
            "cached UID path must match uncached UID path"
        );
        assert!(cached.is_some(), "override should exist");
    }

    #[test]
    fn virtual_to_disk_cached_miss_then_hit() {
        let mapping = cached_test_mapping();

        let miss_input = wstr_u16("data0:/nonexistent.file");
        let mut compute_calls = 0u32;
        let r1 = mapping.virtual_to_disk_cached(&miss_input, |p| {
            compute_calls += 1;
            Cow::Borrowed(p)
        });
        assert!(r1.is_none());
        assert_eq!(compute_calls, 1, "compute must run on first miss");

        let r2 = mapping.virtual_to_disk_cached(&miss_input, |_| {
            panic!("compute must not run when the cache has a sentinel");
        });
        assert!(r2.is_none(), "sentinel must reproduce the miss");
    }

    #[test]
    fn virtual_to_uid_cached_override_hit_is_cached() {
        let mapping = cached_test_mapping();
        let input = wstr_u16("data0:/event/common.emevd.dcx");

        let r1 = mapping.virtual_to_uid_cached(&input, |p| Cow::Borrowed(p));
        assert!(r1.is_some(), "override should exist");

        let r2 = mapping.virtual_to_uid_cached(&input, |_| {
            panic!("compute must not run on a cache hit");
        });
        assert!(r2.is_some());
        assert_eq!(
            r1.as_ref().unwrap().as_wide(),
            r2.as_ref().unwrap().as_wide(),
            "cached UID must resolve to the same fake path"
        );
    }

    #[test]
    fn virtual_to_disk_cached_strips_trailing_nul() {
        let mapping = cached_test_mapping();
        let no_nul = wstr_u16("data0:/regulation.bin");
        let with_nul = {
            let mut v = no_nul.clone();
            v.push(0);
            v
        };

        let r1 = mapping.virtual_to_disk_cached(&no_nul, |p| Cow::Borrowed(p));
        assert!(r1.is_some());

        let r2 = mapping.virtual_to_disk_cached(&with_nul, |_| {
            panic!("compute must not run; trailing NUL should match the stripped cache key");
        });
        assert!(r2.is_some());
        assert_eq!(r1.unwrap().to_path_buf(), r2.unwrap().to_path_buf());
    }

    #[test]
    fn disk_cache_resolves_fake_uid_paths() {
        let mapping = cached_test_mapping();
        let uid = mapping.virtual_to_uid("data0:/regulation.bin").unwrap();
        let disk = mapping.disk_override_cached(uid.as_wide()).unwrap();
        let direct = mapping.virtual_to_disk("data0:/regulation.bin").unwrap();

        assert_eq!(disk.to_path_buf(), direct.to_path_buf());
    }

    #[test]
    fn wwise_override_cached_matches_find_override() {
        use crate::wwise::find_override;

        let mapping = cached_test_mapping();

        let uncached = find_override(&mapping, "sd:/init.bnk");
        let cached = mapping.wwise_override_cached("sd:/init.bnk");
        assert_eq!(
            uncached.map(|v| v.to_path_buf()),
            cached.map(|v| v.to_path_buf()),
            "wwise cached result must equal find_override"
        );

        let cached_again = mapping.wwise_override_cached("sd:/init.bnk");
        assert!(cached_again.is_some());
        assert_eq!(
            cached.unwrap().to_path_buf(),
            cached_again.unwrap().to_path_buf()
        );
    }

    #[test]
    fn wwise_override_cached_miss_is_sentineled() {
        let mapping = cached_test_mapping();
        assert!(mapping
            .wwise_override_cached("sd:/does_not_exist.bnk")
            .is_none());
        assert!(mapping
            .wwise_override_cached("sd:/does_not_exist.bnk")
            .is_none());
    }

    /// Guards against cross-domain poisoning: a `None` cached by the disk-semantics lookup must
    /// not be served to a vfs-semantics lookup for the same bytes.
    #[test]
    fn disk_and_virtual_caches_do_not_share_entries() {
        let mapping = cached_test_mapping();
        let vfs_path = wstr_u16("data0:/regulation.bin");

        let disk_result = mapping.disk_override_cached(&vfs_path);
        assert!(
            disk_result.is_none(),
            "disk lookup of a vfs path should miss (not poison the virtual cache)"
        );

        let virtual_result = mapping.virtual_to_disk_cached(&vfs_path, |p| Cow::Borrowed(p));
        assert!(
            virtual_result.is_some(),
            "virtual lookup must not be poisoned by the disk cache's `None` sentinel"
        );
    }

    /// Before the first `reset_lookup_caches` call the caches are disabled: lookups made while
    /// the game is still populating `virtual_roots` recompute every time and pin nothing.
    #[test]
    fn caches_are_disabled_until_first_reset() {
        let mapping = test_mapping();
        let input = wstr_u16("data0:/regulation.bin");

        let mut compute_calls = 0u32;
        for _ in 0..2 {
            let mid_init = mapping.virtual_to_disk_cached(&input, |_| {
                compute_calls += 1;
                Cow::Owned(wstr_u16("data0:/nonexistent.file"))
            });
            assert!(mid_init.is_none());
        }
        assert_eq!(
            compute_calls, 2,
            "disabled caches must recompute every lookup"
        );

        mapping.reset_lookup_caches();

        let fresh = mapping.virtual_to_disk_cached(&input, |p| Cow::Borrowed(p));
        assert!(
            fresh.is_some(),
            "no mid-init result may be pinned; the post-init lookup must resolve the override"
        );
    }

    /// A later reset (`STEP_Init` re-run) drops entries cached under the previous generation.
    #[test]
    fn reset_drops_previous_generation_entries() {
        let mapping = cached_test_mapping();
        let input = wstr_u16("data0:/regulation.bin");

        assert!(mapping
            .virtual_to_disk_cached(&input, |_| Cow::Owned(wstr_u16("data0:/nonexistent.file")))
            .is_none());
        assert!(mapping
            .virtual_to_disk_cached(&input, |_| panic!("must hit the cached sentinel"))
            .is_none());

        mapping.reset_lookup_caches();

        let fresh = mapping.virtual_to_disk_cached(&input, |p| Cow::Borrowed(p));
        assert!(
            fresh.is_some(),
            "after a reset, the lookup must recompute and resolve the override"
        );
    }

    /// Regression test for the reset/insert race: a lookup that computes its result under one
    /// generation but only reaches its cache insert after a reset must not pin that result.
    #[test]
    fn straddling_insert_is_discarded() {
        let mapping = cached_test_mapping();
        let input = wstr_u16("data0:/regulation.bin");

        let straddler = mapping.virtual_to_disk_cached(&input, |_| {
            mapping.reset_lookup_caches();
            Cow::Owned(wstr_u16("data0:/nonexistent.file"))
        });
        assert!(straddler.is_none(), "the straddler itself sees its result");

        let mut compute_calls = 0u32;
        let fresh = mapping.virtual_to_disk_cached(&input, |p| {
            compute_calls += 1;
            Cow::Borrowed(p)
        });
        assert_eq!(
            compute_calls, 1,
            "the stale insert must have been discarded, forcing a recompute"
        );
        assert!(fresh.is_some(), "the recompute must resolve the override");
    }

    /// Encode a Rust string as UTF-16 units (no NUL terminator), mirroring `OsString::from_wide`.
    fn wstr_u16(s: &str) -> Vec<u16> {
        use std::os::windows::ffi::OsStrExt as _;
        std::ffi::OsStr::new(s).encode_wide().collect()
    }
}
