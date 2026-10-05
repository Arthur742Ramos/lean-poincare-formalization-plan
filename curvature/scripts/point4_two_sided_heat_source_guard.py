#!/usr/bin/env python3
"""Exact two-sided heat release union; source checks never certify a Lean build."""
from __future__ import annotations
import argparse
import functools
import hashlib
import importlib
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
sys.dont_write_bytecode = True

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = 'e6b54dd0d7e73a51eb8efb083764b68ae8305a5a'
R1_PATCH_SHA256 = 'aeb8a459b25e3eb45bf05dc8763f7ec00552a01136e4fe992d19f52e152bd1c6'
C2_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SOURCE_GUARD = 'curvature/scripts/point4_two_sided_heat_source_guard.py'
MODULE = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean'
PROBE = 'curvature/scripts/point4_two_sided_heat_probe.lean'
WORKFLOW = '.github/workflows/point4-two-sided-heat.yml'
METADATA = 'docs/point4/two-sided-initial-heat/formalization.yaml'
RELEASE_GUARD = SOURCE_GUARD
RELEASE_TEST = 'curvature/scripts/point4_two_sided_heat_mock_test.py'
SELF_PATHS = {RELEASE_GUARD, RELEASE_TEST}
# Self-authored guard/test bodies are reviewed source. All public paths are fixed;
# every reused R1 and inherited blob is additionally pinned by its exact identity.
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
C2_ORIGINAL_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
C2_ADAPTER = "\n# Reviewed two-sided heat inventory adapter. All inherited gate bodies remain\n# unchanged; the source guard pins this count-one insertion and exact union.\nif (ROOT / 'curvature/scripts/point4_two_sided_heat_source_guard.py').is_file():\n    import sys as _two_sided_sys\n    _two_sided_sys.dont_write_bytecode = True\n    import point4_two_sided_heat_source_guard as _two_sided_release\n    _two_sided_release.install_c2_inventory_adapter(globals())\n\n"
R1_FILE_SHA256 = {'.github/workflows/point4-two-sided-heat.yml': 'd87d08a5d5545ab69c6b579921078efbd70bfa20dcd6f058ed753f575b928ad7', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean': '488c1fdaa617f306e9bd2c714d5917b07319a88cc251195cd0e950b240747529', 'curvature/scripts/point4_two_sided_heat_probe.lean': '3b871129c36100927a141430678bed1bcd190e2f2ea0f7acbbfec0f9f3451af4', 'curvature/scripts/point4_two_sided_heat_source_guard.py': '601d74c08fb5d300dd7bb896f6441cd06e3c4f0b511026518f96bfc040debf11', 'docs/point4/two-sided-initial-heat.md': '0eb9f3eb41ca0712c0d2d203f07bcc720e65393342614f1c5560026b99a8793a'}
UNIT_FILE_SHA256 = {'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean': '488c1fdaa617f306e9bd2c714d5917b07319a88cc251195cd0e950b240747529', 'curvature/scripts/point4_two_sided_heat_probe.lean': '3b871129c36100927a141430678bed1bcd190e2f2ea0f7acbbfec0f9f3451af4', '.github/workflows/point4-two-sided-heat.yml': '376368cd2508cff7dd9c140204a86d2ea60088d032dfb8b619e2a126b1d026fa', 'docs/point4/two-sided-initial-heat.md': 'abf91c58ecdd81c340fd3d99e2caa351628dbd10b415720546a05f1e79672e84', 'docs/point4/two-sided-initial-heat/formalization.yaml': '2ef33efb616317d135381c7d059a70055cf9c99bc3cf4486491508f5ec370e43', 'docs/point4/two-sided-heat-release-integration.md': '5ccecfd232b1db16c86d52d0eeff21a5bc04d7419f8d01bb8289fe70031f2327'}


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def adapted_c2_guard(original: bytes) -> bytes:
    assert sha256(original) == C2_ORIGINAL_SHA256, 'Inherited guard original digest changed'
    source = original.decode()
    assert source.count(ENTRY_POINT) == 1, 'Inherited guard needs exactly one original entry point'
    assert C2_ADAPTER not in source, 'Inherited guard adapter already present'
    return source.replace(ENTRY_POINT, C2_ADAPTER + ENTRY_POINT.lstrip('\n'), 1).encode()


@functools.lru_cache(maxsize=1)
def baseline_sources() -> dict[str, tuple[str, bytes]]:
    records = git('ls-tree', '-rz', BASE)
    assert records.endswith(b'\0'), 'Baseline inventory must be NUL-terminated'
    result = {}
    for record in records.split(b'\0'):
        if not record:
            continue
        descriptor, path_bytes = record.split(b'\t', 1)
        mode, kind, object_id = descriptor.decode().split()
        path = path_bytes.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}, 'Unsupported baseline file type'
        assert path not in result, 'Duplicate baseline path'
        result[path] = (mode, git('show', f'{BASE}:{path}'))
    assert len(result) == 1641, 'Baseline source count changed'
    return result


def check_unit_blob(path: str, actual: bytes) -> None:
    assert path in UNIT_FILE_SHA256, f'Non-enumerated release blob: {path}'
    assert sha256(actual) == UNIT_FILE_SHA256[path], f'Exact release blob changed: {path}'
    if path in {MODULE, PROBE}:
        assert UNIT_FILE_SHA256[path] == R1_FILE_SHA256[path], f'Reviewed R1 proof/probe changed: {path}'


def expected_sources() -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline), 'New release path overlaps baseline'
    assert set(R1_FILE_SHA256) <= set(UNIT_FILE_SHA256) | SELF_PATHS, 'R1 path was omitted'
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256)), 'Guard/test path collision'
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    check_inventory()
    return expected


def public_paths() -> set[str]:
    return set(baseline_sources()) | set(UNIT_FILE_SHA256) | SELF_PATHS


def nul_records(output: bytes) -> list[bytes]:
    assert not output or output.endswith(b'\0'), 'Git inventory must be NUL-terminated'
    records = output.split(b'\0')[:-1] if output else []
    assert all(records), 'Empty inventory record'
    return records


def nul_paths(output: bytes) -> set[str]:
    paths = [record.decode() for record in nul_records(output)]
    assert len(paths) == len(set(paths)), 'Duplicate inventory path'
    return set(paths)


LAKE_ROOTS = ('curvature/.lake', 'hamilton-ivey-reaction/.lake')
MANIFESTS = ('curvature/lake-manifest.json', 'hamilton-ivey-reaction/lake-manifest.json')
OUTPUT_SUFFIXES = {'.olean', '.ilean', '.private', '.server', '.ir', '.sig', '.hash',
                   '.trace', '.lock', '.json', '.c', '.o', '.export', '.rsp', '.a', '.so', '.h',
                   '.dll', '.dylib', '.bc', '.exe', '.js', '.map', '.css', '.html',
                   '.svg', '.png', '.woff', '.woff2', '.wasm'}


def runtime_path(path: str) -> bool:
    return any(path.startswith(root + '/') for root in LAKE_ROOTS)


def lake_runtime_roots() -> set[str]:
    roots = set(LAKE_ROOTS)
    baseline = baseline_sources()
    for path in MANIFESTS:
        if path in baseline:
            manifest = json.loads(baseline[path][1])
            parent = pathlib.PurePosixPath(path).parent
            roots |= {str(parent / '.lake/packages' / package['name'] / '.lake')
                      for package in manifest['packages'] if package['type'] == 'git'}
    return roots


def generated_build_path(path: str) -> bool:
    p = pathlib.PurePosixPath(path)
    if '__pycache__' in p.parts or p.suffix in {'.lean', '.py', '.pyc', '.pyo'}:
        return False
    for root in lake_runtime_roots():
        relative = path.removeprefix(root + '/')
        if relative == path:
            continue
        if relative.startswith(('build/', 'config/')):
            return p.suffix in OUTPUT_SUFFIXES or relative in {'build/bin/cache', 'build/bin/leantar'}
        if relative.startswith('lakefile.olean'):
            return relative in {'lakefile.olean', 'lakefile.olean.trace', 'lakefile.olean.hash'}
    return False


def git_at(root: pathlib.Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(root), *args], env=ENV)


def git_blob_identity(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def dependency_inventory() -> tuple[set[str], set[str]]:
    # Dependency source is not an arbitrary .lake exemption: each physically
    # present package must have the pinned HEAD and every tracked blob/mode.
    # The full physical walk below rejects all other source and Python caches.
    sources, git_roots = set(), set()
    baseline = baseline_sources()
    for manifest_path in MANIFESTS:
        if manifest_path not in baseline:
            continue  # Small synthetic fixtures have no dependency manifests.
        manifest = json.loads(baseline[manifest_path][1])
        assert manifest['packagesDir'] == '.lake/packages', 'Dependency layout drift'
        parent = pathlib.PurePosixPath(manifest_path).parent
        packages_root = parent / '.lake/packages'
        wanted = {package['name']: package['rev'] for package in manifest['packages'] if package['type'] == 'git'}
        actual_root = ROOT / packages_root
        if not actual_root.exists():
            continue
        assert actual_root.is_dir() and not actual_root.is_symlink(), 'Non-directory dependency root'
        assert {p.name for p in actual_root.iterdir()} <= set(wanted), 'Unexpected dependency package'
        for package_dir in actual_root.iterdir():
            assert package_dir.is_dir() and not package_dir.is_symlink(), 'Symlink/non-directory dependency'
            revision = wanted[package_dir.name]
            assert git_at(package_dir, 'rev-parse', 'HEAD').decode().strip() == revision, 'Dependency HEAD drift'
            git_root = package_dir.relative_to(ROOT).as_posix() + '/.git'
            assert (package_dir / '.git').exists(), 'Missing dependency Git metadata'
            git_roots.add(git_root)
            for record in nul_records(git_at(package_dir, 'ls-tree', '-rz', revision)):
                descriptor, name = record.split(b'\t', 1)
                mode, kind, oid = descriptor.decode().split()
                path = package_dir / name.decode()
                assert kind == 'blob' and mode in {'100644', '100755', '120000'}, 'Unsupported dependency source type'
                relative = path.relative_to(ROOT).as_posix()
                assert relative not in sources, 'Duplicate dependency source'
                assert '__pycache__' not in pathlib.PurePosixPath(relative).parts and path.suffix not in {'.pyc', '.pyo'}, 'Dependency interpreter cache'
                if mode == '120000':
                    assert stat.S_ISLNK(path.lstat().st_mode), 'Pinned dependency symlink type drift'
                    data = os.readlink(path).encode()
                else:
                    check_mode(relative, path.lstat().st_mode, mode)
                    data = path.read_bytes()
                assert git_blob_identity(data) == oid, f'Dependency source drift: {relative}'
                sources.add(relative)
    return sources, git_roots


def check_inventory_sets(tracked: set[str], untracked: set[str], physical: set[str], dependencies: set[str] | None = None, git_roots: set[str] | None = None) -> None:
    assert not tracked & untracked, 'Overlapping tracked/untracked inventory'
    assert set(baseline_sources()) <= tracked, 'Inherited source must stay tracked'
    assert not any(runtime_path(path) for path in tracked), 'Tracked Lake cache forbidden'
    dependencies, git_roots = dependencies or set(), git_roots or set()
    def runtime_file(path):
        # Git reports an untracked nested repository as one trailing-slash
        # directory record. Its pinned source inventory was validated separately.
        return path in dependencies or generated_build_path(path) or any(
            path == root.removesuffix('/.git') + '/' or path == root or path.startswith(root + '/')
            for root in git_roots)
    untracked_source = {path for path in untracked if not runtime_file(path)}
    assert untracked_source <= set(UNIT_FILE_SHA256) | SELF_PATHS, 'Unexpected untracked/ignored source or cache'
    check_public_paths(tracked | untracked_source)
    check_public_paths(physical)


def check_inventory() -> None:
    tracked_modes = {}
    tracked_objects = {}
    for record in nul_records(git('ls-files', '--stage', '-z')):
        descriptor, name = record.split(b'\t', 1)
        mode, oid, stage = descriptor.decode().split()
        path = name.decode()
        assert stage == '0' and mode in {'100644', '100755'}, 'Unmerged/non-regular tracked source'
        assert path not in tracked_modes, 'Duplicate tracked path'
        tracked_modes[path] = mode
        assert re.fullmatch(r'[0-9a-f]{40}', oid), 'Unexpected tracked object identity'
        tracked_objects[path] = oid
    # --others deliberately includes ignored files; .gitignore cannot hide a
    # new proof, target, workflow, interpreter cache or arbitrary public blob.
    untracked = nul_paths(git('ls-files', '-z', '--others'))
    dependencies, git_roots = dependency_inventory()
    physical = set()
    for directory, directories, files in os.walk(ROOT, followlinks=False):
        for name in list(directories):
            child = pathlib.Path(directory) / name
            path = child.relative_to(ROOT).as_posix()
            if path == '.git' or path in git_roots:
                directories.remove(name)
            elif path in dependencies and child.is_symlink():
                # Exact pinned dependency symlink already checked without following.
                directories.remove(name)
            else:
                assert not child.is_symlink(), f'Symlinked public directory: {path}'
                assert name != '__pycache__', f'Interpreter cache forbidden: {path}'
        for name in files:
            path = (pathlib.Path(directory) / name).relative_to(ROOT).as_posix()
            if path == '.git' or path in git_roots:
                continue
            if path in dependencies:
                continue
            if generated_build_path(path):
                assert stat.S_ISREG((ROOT / path).lstat().st_mode), f'Non-regular runtime file: {path}'
            else:
                physical.add(path)
    check_inventory_sets(set(tracked_modes), untracked, physical, dependencies, git_roots)
    baseline = baseline_sources()
    for path in public_paths():
        wanted = baseline[path][0] if path in baseline else '100644'
        if path in tracked_modes:
            assert tracked_modes[path] == wanted, f'Tracked executable-mode drift: {path}'
            data = (ROOT / path).read_bytes()
            identity = git_blob_identity(data)
            assert identity == tracked_objects[path], f'Index/physical blob mismatch: {path}'
        check_mode(path, (ROOT / path).lstat().st_mode, wanted)


def check_public_paths(actual: set[str]) -> None:
    expected = public_paths()
    assert actual == expected, ('Unexpected/missing exact release public path', sorted(actual ^ expected))


def check_physical_lean(actual: set[str]) -> None:
    assert actual == {path for path in public_paths() if path.endswith('.lean')}, 'Physical proof inventory drift'


def check_mode(path: str, actual_mode: int, wanted: str) -> None:
    assert stat.S_ISREG(actual_mode), f'Non-regular/symlink public path: {path}'
    assert bool(actual_mode & 0o111) == (wanted == '100755'), f'Public executable-mode drift: {path}'


def check_modes() -> None:
    baseline = baseline_sources()
    for path in public_paths():
        mode = baseline[path][0] if path in baseline else '100644'
        check_mode(path, (ROOT / path).lstat().st_mode, mode)


def install_c2_inventory_adapter(namespace: dict) -> None:
    assert '_two_sided_release_original_expected_sources' not in namespace, 'Duplicate inventory adapter installation'
    original_expected = namespace['expected_sources']
    original_editable = set(namespace['EDITABLE'])
    original_added = set(namespace['ADDED'])
    assert original_added == {
        'curvature/scripts/point4_c2_initial_heat_source_test.py',
        'curvature/scripts/point4_c2_initial_heat_mock_test.py',
        '.github/workflows/point4-c2-initial-heat.yml',
        'docs/point4/c2-initial-heat-integration.md',
    }, 'Inherited C2 additions changed'
    assert original_editable == {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml',
                                 'docs/status.md', 'docs/point4/README.md'}, 'Inherited C2 edit scope changed'
    def full_expected_sources():
        # Execute the unchanged legacy reconstruction before admitting this unit.
        legacy = original_expected()
        baseline = baseline_sources()
        assert set(legacy) == set(baseline) - original_editable - original_added, 'Inherited exact union drift'
        for path, (_, data) in legacy.items():
            assert data == baseline[path][1], f'Inherited reconstruction no longer matches master: {path}'
        return expected_sources()
    namespace['_two_sided_release_original_expected_sources'] = original_expected
    namespace['expected_sources'] = full_expected_sources
    namespace['ADDED'] = original_added | SELF_PATHS
    # Import, provenance, axiom, type, audit and workflow checks are untouched.


def c2_guard():
    return importlib.import_module('point4_c2_initial_heat_source_test')


def check_root_metadata(source: str) -> None:
    c2_guard().check_metadata(source)
    assert source.encode() == baseline_sources()['curvature/formalization.yaml'][1], 'Root metadata must stay byte-identical'


def check_new_metadata(source: str) -> None:
    guard = c2_guard()
    parsed = guard.parse_metadata(source)
    entries = guard.metadata_entries(source)
    wanted = {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
        'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis',
    }
    assert set(entries) == wanted and all(value[0] == 'builds-on' for value in entries.values()), 'New parsed provenance drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope'], 'New supporting scope drift'
    assert parsed['review']['status'] == 'pending', 'Source checks cannot promote review status'
    check_unit_blob(METADATA, source.encode())


def check_new_probe(output: str) -> None:
    source = (ROOT / PROBE).read_text()
    names = c2_guard().check_axiom_output(source, output)
    assert len(names) == 12, 'Reviewed two-sided heat axiom surface count changed'


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
    parser.add_argument('--probe-log', type=pathlib.Path)
    parser.add_argument('--axiom-dir', type=pathlib.Path)
    parser.add_argument('--audit-json', type=pathlib.Path)
    parser.add_argument('--audit-rc', type=int)
    args = parser.parse_args(argv)
    guard = c2_guard()
    expected = expected_sources()
    for path, (_, wanted) in expected.items():
        guard.check_equal(path, (ROOT / path).read_bytes(), wanted)
    check_inventory()
    check_root_metadata((ROOT / 'curvature/formalization.yaml').read_text())
    metadata = (ROOT / METADATA).read_text()
    check_new_metadata(metadata)
    inherited_args = []
    for option, value in (('--schema', args.schema), ('--axiom-dir', args.axiom_dir),
                          ('--audit-json', args.audit_json), ('--audit-rc', args.audit_rc)):
        if value is not None:
            inherited_args.extend([option, str(value)])
    # Every original optional evidence gate keeps its original parser and requirements.
    guard.main(inherited_args)
    if args.schema:
        import jsonschema
        schema = args.schema.read_bytes()
        assert sha256(schema) == guard.SCHEMA_SHA256, 'Full official schema identity changed'
        jsonschema.validate(guard.parse_metadata(metadata), json.loads(schema))
    if args.probe_log:
        check_new_probe(args.probe_log.read_text())
    print(json.dumps({'baseline': BASE, 'public_paths': len(public_paths()),
                      'inherited_files_byte_identical': 1640, 'exact_inherited_guard_adapters': 1,
                      'r1_proof_and_probe_blobs_unchanged': True,
                      'root_imports_and_metadata_byte_identical': True,
                      'lean_verified': False, 'point4': 'OPEN'}, indent=2))
    print('Source-only release checks passed; exact Lean 4.33 module/probes/full-build/kernel gates remain separate')


if __name__ == '__main__':
    main()
