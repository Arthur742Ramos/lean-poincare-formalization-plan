#!/usr/bin/env python3
"""Exact manifold-only release union; source checks never certify a Lean build."""
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

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = 'e6b54dd0d7e73a51eb8efb083764b68ae8305a5a'
R2_PATCH_SHA256 = '7ad46de150fee41810bdc78b3751d8b0451b4d99f4b6c741e886789d94084134'
C2_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SOURCE_GUARD = 'curvature/scripts/point4_manifold_heat_source_test.py'
PROBE = 'curvature/scripts/point4_manifold_heat_probe.lean'
PROBE_ORIGINAL_HEAD = 'c1537f72b6f354f63c5f76678a4c4d33d55d52f7'
PROBE_OLD_OPTION = b'set_option pp.width 180\n'
PROBE_NEW_OPTION = b'set_option format.width 180\n'
WORKFLOW = '.github/workflows/point4-manifold-only-fixed-background-heat.yml'
METADATA = 'docs/point4/manifold-only-fixed-background-heat/formalization.yaml'
RELEASE_GUARD = 'curvature/scripts/point4_manifold_heat_release_guard.py'
RELEASE_TEST = 'curvature/scripts/point4_manifold_heat_release_mock_test.py'
SELF_PATHS = {RELEASE_GUARD, RELEASE_TEST}
# Self-authored guard/test bodies are reviewed source. All public paths are fixed;
# every reused R2 and inherited blob is additionally pinned by its exact identity.
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
C2_ORIGINAL_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
C2_ADAPTER = "\n# Reviewed manifold-only release inventory adapter. All inherited gate bodies\n# remain unchanged; the release guard pins this count-one transform and union.\nif (ROOT / 'curvature/scripts/point4_manifold_heat_release_guard.py').is_file():\n    import point4_manifold_heat_release_guard as _manifold_release\n    _manifold_release.install_c2_inventory_adapter(globals())\n\n"
R2_FILE_SHA256 = {'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatCoefficients.lean': 'd585dbb3ff601c57e325249c28a0f0698a9a2750e2f5759e9260bb751a83da0f',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatLocalization.lean': '026bae310bfc18ae5ceb20765222ef6d6852690a6b593e5be4e188d45b38ebb9',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatFixedBackground.lean': '2986e77ff34184000d57defba9675f363ceeb7cdb06ef48d8f9a6a18949c6a26',
 'curvature/scripts/point4_manifold_heat_probe.lean': 'dda0e8ebbfb3c11661df666fed6d739225ef66fa16eae5048d1b8b8b8e300537',
 'curvature/scripts/point4_manifold_heat_source_test.py': '76ecd1b174e95b795b157f2162058068ac17377bf6c3c0da4b637e297612ee09',
 'curvature/scripts/point4_manifold_heat_mock_test.py': '8fa11d167b71d949eb89885b3ea4285aec85cc8d20d3070b207e9f2c3200d5b0',
 'docs/point4/manifold-only-fixed-background-heat.md': 'a8e353f825b038e5c69e193b015837b1c5f7952079024b0c4735bb73a089ed43',
 'docs/point4/manifold-only-fixed-background-heat/formalization.yaml': '97aa852770bf9c88126eeca225c31145290a432fa64329e5bd0b7a4df63334fc',
 '.github/workflows/point4-manifold-only-fixed-background-heat.yml': '4eb796dce9bcb3949a004fca38ba9198b9684d4d3318c9545486ceb5104180c1'}
UNIT_FILE_SHA256 = {'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatCoefficients.lean': 'd585dbb3ff601c57e325249c28a0f0698a9a2750e2f5759e9260bb751a83da0f',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatLocalization.lean': '026bae310bfc18ae5ceb20765222ef6d6852690a6b593e5be4e188d45b38ebb9',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatFixedBackground.lean': '2986e77ff34184000d57defba9675f363ceeb7cdb06ef48d8f9a6a18949c6a26',
 'curvature/scripts/point4_manifold_heat_probe.lean': 'be26ae8baf105960e616b2bde500d318f972ec3b7858ede6b84e926e0f98edff',
 'curvature/scripts/point4_manifold_heat_source_test.py': '7bf46239191c67066bee4576c309daed6535cde2234b2dd4c4f8b5146c327f78',
 'curvature/scripts/point4_manifold_heat_mock_test.py': '8fa11d167b71d949eb89885b3ea4285aec85cc8d20d3070b207e9f2c3200d5b0',
 'docs/point4/manifold-only-fixed-background-heat.md': '80864bb52073f4fb420fdb109781d939a5e3985eb779c71632d2d820115cbb59',
 'docs/point4/manifold-only-fixed-background-heat/formalization.yaml': '5572cb0804cb1343ff49aaed805e4370b6c9bc409e3856a3dc46d6086e3bf759',
 '.github/workflows/point4-manifold-only-fixed-background-heat.yml': 'ec514eb318b5869a6ace7f99c8c70f958def3bb937ed76c4d286a1d807beb360',
 'docs/point4/manifold-only-heat-release-integration.md': '2de3a557978152e93d1e0a86b5abb834bc2678e29282a7f864088005e94f39fa'}


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


def repaired_probe(original: bytes) -> bytes:
    assert sha256(original) == R2_FILE_SHA256[PROBE], 'Historical R2 probe identity changed'
    assert original.count(PROBE_OLD_OPTION) == 1, 'Probe needs exactly one unsupported printer option'
    assert PROBE_NEW_OPTION not in original, 'Probe printer-option repair already present'
    return original.replace(PROBE_OLD_OPTION, PROBE_NEW_OPTION, 1)


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
    if path == PROBE:
        assert actual == repaired_probe(git('show', f'{PROBE_ORIGINAL_HEAD}:{PROBE}')), \
            'Probe differs beyond the exact printer-option repair'
    elif path.endswith('.lean') or path.endswith('point4_manifold_heat_mock_test.py'):
        assert UNIT_FILE_SHA256[path] == R2_FILE_SHA256[path], f'Reviewed R2 proof/probe/test changed: {path}'


def expected_sources() -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline), 'New release path overlaps baseline'
    assert set(R2_FILE_SHA256) <= set(UNIT_FILE_SHA256), 'R2 path was omitted'
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256)), 'Guard/test path collision'
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    return expected


def public_paths() -> set[str]:
    return set(baseline_sources()) | set(UNIT_FILE_SHA256) | SELF_PATHS


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
    assert '_manifold_release_original_expected_sources' not in namespace, 'Duplicate inventory adapter installation'
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
    namespace['_manifold_release_original_expected_sources'] = original_expected
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
        'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/58c6fc21bafeb8a659d6751a1a9db7a74127a300/curvature',
        'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Geometry/Manifold',
    }
    assert set(entries) == wanted and all(value[0] == 'builds-on' for value in entries.values()), 'New parsed provenance drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope'], 'New supporting scope drift'
    assert parsed['review']['status'] == 'pending', 'Review status cannot be promoted by source checks'
    check_unit_blob(METADATA, source.encode())


def check_new_probe(output: str) -> None:
    source_guard = importlib.import_module('point4_manifold_heat_source_test')
    source_guard.check_probe(output)
    source = (ROOT / source_guard.PROBE).read_text()
    names = c2_guard().check_axiom_output(source, output)
    assert len(names) == 11, 'Reviewed manifold-only axiom surface count changed'


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
    actual = guard.public_paths(guard.nul_paths(git('ls-files', '-z', '--cached')),
                                guard.nul_paths(git('ls-files', '-z', '--others', '--exclude-standard')))
    check_public_paths(actual)
    physical = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean')
                if not {'.git', '.lake', '.toolchain'} & set(p.parts)}
    check_physical_lean(physical)
    check_modes()
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
    source_guard = importlib.import_module('point4_manifold_heat_source_test')
    source_report = source_guard.check_sources(ROOT)
    assert source_report['inherited_files_unchanged'] == 1640
    assert source_report['exact_inherited_guard_adapters'] == 1
    if args.probe_log:
        check_new_probe(args.probe_log.read_text())
    print(json.dumps({'baseline': BASE, 'public_paths': len(public_paths()),
                      'inherited_files_byte_identical': 1640, 'exact_inherited_guard_adapters': 1,
                      'r2_proof_blobs_unchanged': True, 'exact_probe_printer_option_replacements': 1,
                      'root_imports_and_metadata_byte_identical': True,
                      'lean_verified': False, 'point4': 'OPEN'}, indent=2))
    print('Source-only release checks passed; exact Lean 4.33 producer/probes/full-build/kernel gates remain separate')


if __name__ == '__main__':
    main()
