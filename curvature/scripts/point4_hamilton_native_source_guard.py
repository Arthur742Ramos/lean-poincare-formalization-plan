#!/usr/bin/env python3
"""Exact native Hamilton audit release union; source checks never certify a Lean build."""
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
REVIEWED_PATCH_SHA256 = '4212f9709dc8d80cb00bc8aa335531baf8f391a79c8ed40d702180a2b0a638e7'
HISTORICAL = '82d0a0e01a2a0669041c27f019205ca49b688665'
C2_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SOURCE_GUARD = 'curvature/scripts/point4_hamilton_native_source_guard.py'
RELEASE_TEST = 'curvature/scripts/point4_hamilton_native_mock_test.py'
SELF_PATHS = {SOURCE_GUARD, RELEASE_TEST}
# New guard/test bodies require independent source review at the frozen commit.
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
C2_ORIGINAL_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
C2_ADAPTER = "\n# Reviewed native Hamilton audit inventory adapter. All inherited gate bodies\n# remain unchanged; the source guard pins this count-one insertion and exact union.\nif (ROOT / 'curvature/scripts/point4_hamilton_native_source_guard.py').is_file():\n    import sys as _hamilton_native_sys\n    _hamilton_native_sys.dont_write_bytecode = True\n    import point4_hamilton_native_source_guard as _hamilton_native_release\n    _hamilton_native_release.install_c2_inventory_adapter(globals())\n\n"
REVIEWED_FILE_SHA256 = {'scripts/point4/audit-hamilton-release.py': '1380a57af471e0c6b062ab3e381f4c4cae095dfdf4bf1250f16a3fc677c2245e', 'scripts/point4/build-hamilton-batches.lean': '602e3207830355f3f23caf5c2a79ce57fc03442d7cfc245897ae5d179eb3c432', 'scripts/point4/observe-hamilton-compiler.py': '11db5d7be1197a841b997c946e08af3081fa1d9389319d43a162f4d87e0edd2e', 'scripts/point4/test_audit_hamilton_release.py': 'c7cb8aff1fc8277954c36301e6fa2e2e63b50958e2cb163d8dd9d361ae8ddddd', 'docs/point4/upstream-audit.md': 'dc93b426581e1ee593db6435f7b34619d844006f7d6868a583eee6de991d2b8e', '.github/workflows/point4-hamilton-release-audit.yml': 'c35493376e81b27036c332a1330a6ad8c324294c6f69d8b14035adeef3359cc5'}
UNIT_FILE_SHA256 = {'scripts/point4/audit-hamilton-release.py': '1380a57af471e0c6b062ab3e381f4c4cae095dfdf4bf1250f16a3fc677c2245e', 'scripts/point4/build-hamilton-batches.lean': '602e3207830355f3f23caf5c2a79ce57fc03442d7cfc245897ae5d179eb3c432', 'scripts/point4/observe-hamilton-compiler.py': '11db5d7be1197a841b997c946e08af3081fa1d9389319d43a162f4d87e0edd2e', 'scripts/point4/test_audit_hamilton_release.py': 'c7cb8aff1fc8277954c36301e6fa2e2e63b50958e2cb163d8dd9d361ae8ddddd', 'docs/point4/upstream-audit.md': 'dc93b426581e1ee593db6435f7b34619d844006f7d6868a583eee6de991d2b8e', '.github/workflows/point4-hamilton-release-audit.yml': '078fe0190561d9304f26c81268c085e716ee86bd0a362676e1796dc58d03243f', 'docs/point4/hamilton-native-current-master-integration.md': 'ca983a1675d00c33787245339017e4ae42f4f4bf6fd72a97853f8223a8645043'}
NATIVE_WORKFLOW = '.github/workflows/point4-hamilton-release-audit.yml'
NATIVE_GATE_ANCHOR = '      - name: Checkout immutable Apache-2.0 upstream release\n'
NATIVE_SOURCE_GATE = '      - name: Check exact current-master source integration before any native work\n        env:\n          PYTHONDONTWRITEBYTECODE: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          test "$(git -C campaign rev-parse HEAD)" = "$EXPECTED_SHA"\n          git -C campaign fetch --no-tags --unshallow origin\n          python3 -m pip install --disable-pip-version-check --only-binary=:all: --index-url https://pypi.org/simple PyYAML==6.0.2 jsonschema==4.25.1\n          curl --fail --location --proto \'=https\' --tlsv1.2 \\\n            --output "$RUNNER_TEMP/point4-hamilton-official-schema.json" \\\n            https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json\n          echo "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce  $RUNNER_TEMP/point4-hamilton-official-schema.json" | sha256sum --check\n          cd campaign\n          python3 curvature/scripts/point4_hamilton_native_source_guard.py --schema "$RUNNER_TEMP/point4-hamilton-official-schema.json"\n          python3 curvature/scripts/point4_hamilton_native_mock_test.py\n          python3 curvature/scripts/point4_c2_initial_heat_source_test.py\n          python3 curvature/scripts/point4_c2_initial_heat_mock_test.py\n          python3 curvature/scripts/point4_linear_heat_geometry_source_test.py\n          python3 curvature/scripts/point4_linear_heat_geometry_mock_test.py\n          python3 curvature/scripts/point4_weighted_initial_heat_guard.py\n          python3 curvature/scripts/point4_closed_contract_source_test.py\n          python3 scripts/check-doc-links.py\n'

# Importlib writes a module's bytecode before executing its body. Suppression
# must therefore be set by the interpreter-startup environment, never by a
# cache exemption or deletion after the inherited caller has imported C2.
STARTUP_ENV = "    env:\n      PYTHONDONTWRITEBYTECODE: '1'\n"
STARTUP_WORKFLOWS = {
    '.github/workflows/point4-linear-heat-geometry.yml': (
        '2cfd17bf27e5e5983bf8a524948382a1965dcd7f6a44a5a5efe44bae91dbf582',
        'linear_heat_geometry',
        '  linear_heat_geometry:\n    name: Exact-head combined source, all 127 axiom occurrences, closed contract and full audit\n'),
    '.github/workflows/point4-c2-initial-heat.yml': (
        'bb3efbcc8a477181aea2857a002f2d5eb7b7670ad34527dd231d9cfa5c543f3d',
        'c2_initial_heat',
        '  c2_initial_heat:\n    name: Exact-head C2 union, all 150 axiom occurrences, current contract and full audit\n'),
    '.github/workflows/point4-weighted-initial-heat.yml': (
        '3b52ebefb56317864cc95ba9dacf8276776d51d82e25f5ad83e2083638f4be8a',
        'weighted_initial_heat',
        '  weighted_initial_heat:\n    name: Exact-head weighted heat certificate with unchanged full audit\n'),
}


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


def parse_workflow(source: str) -> dict:
    import yaml
    class StrictWorkflowLoader(yaml.BaseLoader):
        def construct_mapping(self, node, deep=False):
            result = {}
            for key_node, value_node in node.value:
                key = self.construct_object(key_node, deep=deep)
                assert isinstance(key, str), 'Workflow mapping key must be a string'
                assert key not in result, f'Duplicate workflow YAML mapping key: {key}'
                result[key] = self.construct_object(value_node, deep=deep)
            return result
    data = yaml.load(source, Loader=StrictWorkflowLoader)
    assert isinstance(data, dict), 'Workflow must be a mapping'
    return data


def adapted_startup_workflow(path: str, original: bytes) -> bytes:
    assert path in STARTUP_WORKFLOWS, 'Unapproved startup workflow path'
    digest, job, anchor = STARTUP_WORKFLOWS[path]
    assert sha256(original) == digest, f'Inherited startup workflow original digest changed: {path}'
    source = original.decode()
    assert source.count(anchor) == 1, 'Startup workflow needs exactly one pinned job header'
    assert STARTUP_ENV not in source, 'Startup workflow adapter already present'
    before = parse_workflow(source)
    assert 'env' not in before and 'env' not in before['jobs'][job], 'Inherited startup environment changed'
    adapted = source.replace(anchor, anchor + STARTUP_ENV, 1)
    wanted = json.loads(json.dumps(before))
    wanted['jobs'][job]['env'] = {'PYTHONDONTWRITEBYTECODE': '1'}
    assert parse_workflow(adapted) == wanted, 'Startup workflow semantic remainder changed'
    assert adapted.count(STARTUP_ENV) == 1, 'Startup workflow adapter must occur once'
    assert adapted.replace(STARTUP_ENV, '', 1).encode() == original, 'Startup workflow byte remainder changed'
    return adapted.encode()


def restored_startup_workflow(path: str, actual: bytes) -> bytes:
    # Validate exact bytes and duplicate-free semantics before restoring the
    # original input for the unchanged inherited workflow validator.
    original = baseline_sources()[path][1]
    expected = adapted_startup_workflow(path, original)
    assert parse_workflow(actual.decode()) == parse_workflow(expected.decode()), 'Startup workflow semantic drift'
    assert actual == expected, f'Exact startup workflow changed: {path}'
    assert actual.decode().count(STARTUP_ENV) == 1, 'Startup workflow adapter count changed'
    restored = actual.decode().replace(STARTUP_ENV, '', 1).encode()
    assert restored == original, 'Startup workflow inherited remainder changed'
    return restored


def adapted_native_workflow(original: bytes) -> bytes:
    assert sha256(original) == REVIEWED_FILE_SHA256[NATIVE_WORKFLOW], 'Reviewed native workflow digest changed'
    source = original.decode()
    assert source.count(NATIVE_GATE_ANCHOR) == 1, 'Native source-gate anchor count changed'
    assert NATIVE_SOURCE_GATE not in source, 'Native source gate already present'
    before = parse_workflow(source)
    adapted = source.replace(NATIVE_GATE_ANCHOR, NATIVE_SOURCE_GATE + NATIVE_GATE_ANCHOR, 1)
    after = parse_workflow(adapted)
    steps = after['jobs']['upstream-endpoints']['steps']
    assert len(steps) == len(before['jobs']['upstream-endpoints']['steps']) + 1
    added = steps.pop(1)
    expected_step = parse_workflow('steps:\n' + NATIVE_SOURCE_GATE)['steps'][0]
    assert added == expected_step, 'Native source gate semantic drift'
    assert after == before, 'Native build/preflight/observer semantics changed'
    assert adapted.count(NATIVE_SOURCE_GATE) == 1
    assert adapted.replace(NATIVE_SOURCE_GATE, '', 1).encode() == original
    return adapted.encode()


def check_reviewed_unit() -> None:
    for path, digest in REVIEWED_FILE_SHA256.items():
        actual = (ROOT / path).read_bytes()
        if path == NATIVE_WORKFLOW:
            assert actual.decode().count(NATIVE_SOURCE_GATE) == 1, 'Native source-gate count changed'
            restored = actual.decode().replace(NATIVE_SOURCE_GATE, '', 1).encode()
            assert sha256(restored) == digest, 'Native workflow reviewed remainder changed'
            assert actual == adapted_native_workflow(restored), 'Native workflow transform drift'
        else:
            assert sha256(actual) == digest, f'Reviewed native source changed: {path}'


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


def expected_sources() -> dict[str, tuple[str, bytes]]:
    for ancestor in (BASE, HISTORICAL):
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', ancestor, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    for path in STARTUP_WORKFLOWS:
        expected[path] = (BASE, adapted_startup_workflow(path, baseline[path][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline), 'New release path overlaps baseline'
    assert set(REVIEWED_FILE_SHA256) <= set(UNIT_FILE_SHA256), 'Reviewed audit source was omitted'
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256)), 'Guard/test path collision'
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    check_reviewed_unit()
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


def manifests():
    return tuple(path for path in baseline_sources() if path.endswith('/lake-manifest.json'))

def lake_roots():
    return tuple(str(pathlib.PurePosixPath(path).parent / '.lake') for path in manifests())
OUTPUT_SUFFIXES = {'.olean', '.ilean', '.private', '.server', '.ir', '.sig', '.hash',
                   '.trace', '.lock', '.json', '.c', '.o', '.export', '.rsp', '.a', '.so', '.h',
                   '.dll', '.dylib', '.bc', '.exe', '.js', '.map', '.css', '.html',
                   '.svg', '.png', '.woff', '.woff2', '.wasm'}


def runtime_path(path: str) -> bool:
    return any(path.startswith(root + '/') for root in lake_roots())


def lake_runtime_roots() -> set[str]:
    roots = set(lake_roots())
    baseline = baseline_sources()
    for path in manifests():
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
    for manifest_path in manifests():
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
    assert '_hamilton_native_release_original_expected_sources' not in namespace, 'Duplicate inventory adapter installation'
    assert '_hamilton_native_release_original_check_workflow' not in namespace, 'Duplicate workflow adapter installation'
    original_expected = namespace['expected_sources']
    original_check_workflow = namespace['check_workflow']
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
    def startup_checked_workflow(actual: bytes):
        original = restored_startup_workflow('.github/workflows/point4-c2-initial-heat.yml', actual)
        original_check_workflow(original)
    namespace['_hamilton_native_release_original_expected_sources'] = original_expected
    namespace['_hamilton_native_release_original_check_workflow'] = original_check_workflow
    namespace['check_workflow'] = startup_checked_workflow
    namespace['expected_sources'] = full_expected_sources
    namespace['ADDED'] = original_added | SELF_PATHS
    # Import, provenance, axiom, type and audit functions are untouched. The
    # workflow wrapper checks one exact startup-only transform, then executes
    # the unchanged original validator on the reconstructed original bytes.


def c2_guard():
    return importlib.import_module('point4_c2_initial_heat_source_test')


def check_root_metadata(source: str) -> None:
    c2_guard().check_metadata(source)
    assert source.encode() == baseline_sources()['curvature/formalization.yaml'][1], 'Root metadata must stay byte-identical'


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
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
    inherited_args = []
    for option, value in (('--schema', args.schema), ('--axiom-dir', args.axiom_dir),
                          ('--audit-json', args.audit_json), ('--audit-rc', args.audit_rc)):
        if value is not None:
            inherited_args.extend([option, str(value)])
    # Every original optional evidence gate keeps its original parser and requirements.
    guard.main(inherited_args)
    print(json.dumps({'baseline': BASE, 'public_paths': len(public_paths()),
                      'inherited_files_byte_identical': 1637, 'exact_inherited_guard_adapters': 1,
                      'exact_startup_workflow_adapters': len(STARTUP_WORKFLOWS),
                      'reviewed_native_files_preserved': True,
                      'root_imports_and_metadata_byte_identical': True,
                      'lean_verified': False, 'point4': 'OPEN'}, indent=2))
    print('Source-only release checks passed; 2,270 upstream modules/endpoints and exact combined-head kernel gates remain unverified')


# BEGIN exact finite incoming-leaf-111
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == '1d9b4ad2f428f3f65cb84bbefb67befbb77cce8f3cd50d7f5408bbd305056f56', "Incoming composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
_curvature_comp.install_curvature_leaf(globals(),111)
# END exact finite incoming-leaf-111

if __name__ == '__main__':
    main()
