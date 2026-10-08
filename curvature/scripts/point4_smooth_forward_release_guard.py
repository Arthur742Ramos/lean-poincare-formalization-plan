#!/usr/bin/env python3
"""Exact smooth support union; all original gate bodies and verdicts survive.

The inventory extension is scoped to gate execution. Inherited adversarial
fixtures retain their original baseline and run unchanged. This is a reviewed
source gate, not a self-certificate or a replacement for exact-head Lean gates.
"""
from __future__ import annotations
import argparse
import contextlib
import functools
import hashlib
import importlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = 'a0132cd55e2540b2fd26adecea9a07b51f1b8292'
LEGACY_GUARD = 'curvature/scripts/point4_manifold_heat_release_guard.py'
LEGACY_TEST = 'curvature/scripts/point4_manifold_heat_release_mock_test.py'
GUARD = 'curvature/scripts/point4_smooth_forward_release_guard.py'
TEST = 'curvature/scripts/point4_smooth_forward_release_mock_test.py'
METADATA = 'docs/point4/smooth-forward-model/formalization.yaml'
PROBE = 'curvature/scripts/point4_smooth_forward_probe.lean'
COMPLETION = 'curvature/scripts/point4_smooth_forward_completion.lean'
WORKFLOW = '.github/workflows/point4-smooth-forward-support.yml'
TARGET = 'RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel'
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
ORIGINAL_SHA256 = '713af9477a3595655ddbd2cde6dd4dfc5ce7230f4310b28593171407e33ab734'
ADAPTER_TEMPLATE = "\n# Reviewed smooth-forward inventory adapter. Gate bodies remain unchanged.\n_smooth_guard_path = ROOT / 'curvature/scripts/point4_smooth_forward_release_guard.py'\nassert stat.S_ISREG(_smooth_guard_path.lstat().st_mode) and not (_smooth_guard_path.lstat().st_mode & 0o111), 'Smooth guard mode changed'\nassert hashlib.sha256(_smooth_guard_path.read_bytes()).hexdigest() == '{guard_sha256}', 'Reviewed smooth executable changed'\nsys.modules.setdefault('point4_manifold_heat_release_guard', sys.modules[__name__])\nimport point4_smooth_forward_release_guard as _smooth_release\n_smooth_release.install_release_adapter(globals(), '{guard_sha256}')\n\n"
# Every non-self addition is pinned. This guard body still requires independent
# review; hashing itself would not establish trust. Paths and modes are exact.
FILE_SHA256 = {'.github/workflows/point4-smooth-forward-support.yml': '1c0941635dff686521a611db268489fbff8ed098bb91655024c633ae86d6f5c2', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardContract.lean': 'b096fe0ff63b6adc19c344a2239183b3fdb0921cef5a128c30e5cac49da47e30', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardRegularity.lean': '2e46cea0e6587f803e7d01cda26ea5bdb439d6216ec44b574a87dcae414607a6', 'curvature/scripts/point4_smooth_forward_audit.py': '358affd9a9f7c567ba8d01b05bea981b844f692c9acdcb2b728852d304bffcf2', 'curvature/scripts/point4_smooth_forward_completion.lean': '644d4fb1a354e11ef5e730652559f815c43ae5a13f8753708a0b19cfaafdd07d', 'curvature/scripts/point4_smooth_forward_interface_sha256.json': '6d4bf424f368d00c151a05c37ad56b52cf82bfb3e56c7e48a467d80eea0019a5', 'curvature/scripts/point4_smooth_forward_probe.lean': '24490add867b9e60adc1deeb52b6dfc347788f453727617ea7ef1be20f163821', 'curvature/scripts/point4_smooth_forward_release_mock_test.py': 'ee9d8133abb7fdf92d4f7bb9673e33ca6bb8a90458b135d06636cb35772f336a', 'docs/point4/smooth-forward-model-contract.md': '43749ea7bffea985011b397433eb6ba404de8345ab617f7f7864374da5e37093', 'docs/point4/smooth-forward-model/formalization.yaml': '5ad59f77a615dd6d77ed284e97b1d4eadc9b6efd76caae221cbcf2dd4545f7af', 'docs/point4/smooth-forward-release-integration.md': '8f8bcf4c250499d7c90c69fe49cd26fb029e8e81b2680dcab444c0454e508c8e', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/IntrinsicRicciReindex.lean': 'ef9d583295c0a686e352e90b79d1bdfb14b7ad7ebc8450483424f21b852d6c58', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardBasis.lean': '30e8451702e8dba230299613def494a49c839f8e54424573ee8805469c41ecba', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardTimeTranslate.lean': '1aed107075356aa2d7963ae65a56d8e9234ce79b09301fa2c20cc54f3f6e04e8', 'curvature/TimeTranslateVerification.lean': '52af9c3c59779129f8ade8ef90877c1fd96f4d03c27eda43d2da770d8dbbed98', 'curvature/Verification.lean': 'b545fe4883b5d9d3a9279dbd42b9e3d579b0a38803b244b3a4e5f5bba482a446', 'curvature/scripts/point4_smooth_forward_basis_probe.lean': '68eb6f85d35d8c61edf224171aaea1c80559dc86d8399bcf19da58f6e8915448', 'docs/point4/smooth-forward-finite-basis.md': '488042961cfdabaf7585ff5037879efe9424d2bce06c5533770713290bfb83c7'}
ADDED = frozenset(FILE_SHA256) | {GUARD}
_depth = 0
_active_namespace = None


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def legacy():
    return importlib.import_module('point4_manifold_heat_release_guard')


def adapted_release_guard(original: bytes, guard_sha256: str) -> bytes:
    assert sha256(original) == ORIGINAL_SHA256, 'Pinned PR131 release guard changed'
    source = original.decode()
    assert re.fullmatch(r'[0-9a-f]{64}', guard_sha256), 'Malformed reviewed guard binding'
    adapter = ADAPTER_TEMPLATE.format(guard_sha256=guard_sha256)
    assert source.count(ENTRY_POINT) == 1 and 'install_release_adapter(' not in source, 'Count-one adapter boundary changed'
    return source.replace(ENTRY_POINT, adapter + ENTRY_POINT.lstrip('\n'), 1).encode()


def parse_tree(data: bytes) -> dict[str, tuple[str, str]]:
    assert data.endswith(b'\0'), 'Full source tree must be NUL-terminated'
    result = {}
    for row in data.split(b'\0'):
        if not row:
            continue
        descriptor, path_bytes = row.split(b'\t', 1)
        mode, kind, identity = descriptor.decode().split()
        path = path_bytes.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}, 'Non-regular source tree entry'
        assert re.fullmatch(r'[0-9a-f]{40}', identity) and path not in result, 'Malformed/duplicate source identity'
        result[path] = mode, identity
    assert len(result) == 1653, 'Fresh master source count changed'
    return result


def reconstruct_baseline(namespace: dict, inventory) -> dict[str, tuple[str, bytes]]:
    # Run the complete unchanged PR131 reconstruction, including its original
    # ancestry, C2 adapter, proof/probe hashes and printer-option provenance.
    old = namespace['_smooth_original_expected_sources']()
    assert set(old) == set(inventory) - {LEGACY_GUARD, LEGACY_TEST}, 'PR131 reconstruction scope drift'
    baseline = {path: (inventory[path][0], data) for path, (_, data) in old.items()}
    for path in (LEGACY_GUARD, LEGACY_TEST):
        baseline[path] = inventory[path][0], namespace['git']('show', f'{BASE}:{path}')
    for path, (mode, data) in baseline.items():
        assert (mode, blob(data)) == inventory[path], f'PR131 reconstruction differs from fresh master: {path}'
    return baseline


def expected_sources(namespace: dict) -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'],
                   check=True, env=namespace['ENV'])
    inventory = parse_tree(namespace['git']('ls-tree', '-rz', BASE))
    assert not ADDED & set(inventory) and len(ADDED) == 19, 'Reviewed smooth addition inventory changed'
    original_guard = namespace['git']('show', f'{BASE}:{LEGACY_GUARD}')
    adapted = adapted_release_guard(original_guard, namespace['_smooth_guard_sha256'])
    # Validate the complete physical/public composed inventory before historical
    # reconstruction. No historical projection can hide a new executable file.
    c2 = namespace['c2_guard']()
    actual = c2.public_paths(c2.nul_paths(namespace['git']('ls-files', '-z', '--cached')),
                             c2.nul_paths(namespace['git']('ls-files', '-z', '--others', '--exclude-standard')))
    wanted_paths = set(inventory) | set(ADDED)
    assert actual == wanted_paths, ('Composed public path drift', sorted(actual ^ wanted_paths))
    physical = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean')
                if not {'.git', '.lake', '.toolchain'} & set(p.parts)}
    assert physical == {p for p in wanted_paths if p.endswith('.lean')}, 'Composed physical proof inventory drift'
    for path in sorted(wanted_paths):
        namespace['check_mode'](path, (ROOT / path).lstat().st_mode,
                                inventory[path][0] if path in inventory else '100644')
        data = (ROOT / path).read_bytes()  # Missing/unreadable files fail closed.
        if path == LEGACY_GUARD:
            assert data == adapted, 'Only the exact one-hook transformation is admitted'
        elif path in inventory:
            assert blob(data) == inventory[path][1], f'Inherited composed blob changed: {path}'
        else:
            identity = namespace['_smooth_guard_sha256'] if path == GUARD else FILE_SHA256[path]
            assert sha256(data) == identity, f'Reviewed new executable/support blob changed: {path}'
    baseline = reconstruct_baseline(namespace, inventory)
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[LEGACY_GUARD] = BASE, adapted
    assert not ADDED & set(baseline), 'Smooth support overlaps fresh master'
    assert len(ADDED) == 19, 'Reviewed smooth addition inventory changed'
    for path in ADDED:
        data = (ROOT / path).read_bytes()
        if path != GUARD:
            assert sha256(data) == FILE_SHA256[path], f'Exact smooth support blob changed: {path}'
        expected[path] = BASE, data
    return expected


@contextlib.contextmanager
def inventory_scope(namespace: dict):
    global _depth, _active_namespace
    if _depth:
        assert namespace is _active_namespace, 'Nested gate changed its owning namespace'
        _depth += 1
        try:
            yield
        finally:
            _depth -= 1
        return
    original_expected = namespace['expected_sources']
    original_paths = namespace['public_paths']
    assert original_expected is namespace['_smooth_original_expected_sources']
    assert original_paths is namespace['_smooth_original_public_paths']
    composed = expected_sources(namespace)
    namespace['expected_sources'] = lambda: composed
    namespace['public_paths'] = lambda: set(composed)
    _depth = 1
    _active_namespace = namespace
    try:
        yield
    finally:
        namespace['expected_sources'] = original_expected
        namespace['public_paths'] = original_paths
        _depth = 0
        _active_namespace = None


def gate_main(original, namespace):
    if getattr(original, '_smooth_scoped_gate', False):
        return original
    @functools.wraps(original)
    def wrapped(*args, **kwargs):
        with inventory_scope(namespace):
            return original(*args, **kwargs)
    wrapped._smooth_scoped_gate = True
    return wrapped


def install_release_adapter(namespace: dict, guard_sha256: str) -> None:
    assert '_smooth_original_expected_sources' not in namespace, 'Duplicate smooth adapter installation'
    assert namespace['RELEASE_GUARD'] == LEGACY_GUARD
    assert namespace['SELF_PATHS'] == {LEGACY_GUARD, LEGACY_TEST}, 'PR131 self scope drift'
    assert sha256((ROOT / GUARD).read_bytes()) == guard_sha256, 'Reviewed new guard executable binding changed'
    namespace['_smooth_guard_sha256'] = guard_sha256
    namespace['_smooth_original_expected_sources'] = namespace['expected_sources']
    namespace['_smooth_original_public_paths'] = namespace['public_paths']
    namespace['_smooth_original_main'] = namespace['main']
    original_install = namespace['install_c2_inventory_adapter']
    namespace['_smooth_original_install_c2_inventory_adapter'] = original_install
    def install_c2(c2_namespace):
        original_install(c2_namespace)
        c2_namespace['main'] = gate_main(c2_namespace['main'], namespace)
    namespace['install_c2_inventory_adapter'] = install_c2
    namespace['main'] = gate_main(namespace['main'], namespace)
    # Only main/inventory wiring changes; every original validation body survives.


def check_new_metadata(source: str) -> None:
    guard = legacy().c2_guard()
    parsed = guard.parse_metadata(source)
    entries = guard.metadata_entries(source)
    wanted = {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
        'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Geometry/Manifold',
        'https://github.com/qinz1yang/differential-geometry/tree/8bd406e35c33a200e9b88895cf11ee8429194e15',
    }
    assert set(entries) == wanted and all(v[0] == 'builds-on' for v in entries.values()), 'Smooth parsed provenance drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope']
    assert parsed['review']['status'] == 'pending', 'Source checks cannot promote review status'
    assert sha256(source.encode()) == FILE_SHA256[METADATA], 'Smooth metadata blob changed'


def check_support_probe(output: str) -> None:
    names = legacy().c2_guard().check_axiom_output((ROOT / PROBE).read_text(), output)
    assert len(names) == 6, 'Reviewed six smooth supporting axiom surfaces changed'
    assert TARGET not in names, 'Supporting proof evidence cannot certify general target'


def check_completion_open(output: str, rc: int) -> None:
    assert rc == 1, 'Absent smooth target must produce the expected failure'
    lines = [line for line in output.splitlines() if line.strip()]
    # The frozen completion probe has three exact assignments plus one axiom
    # query. Additional errors, warnings or producer diagnostics are not accepted.
    assert len(lines) == 4, 'Missing/extra smooth completion diagnostics'
    for line, position in zip(lines, (22, 34, 46, 48)):
        assert f'point4_smooth_forward_completion.lean:{position}:' in line
        assert 'error(lean.unknownIdentifier)' in line and TARGET in line, line
        assert re.search(r'Unknown (identifier|constant) `'+re.escape(TARGET)+r'`$', line), line


def check_smooth_audit_open(data: dict, rc: int) -> None:
    assert rc == 1 and data['target'] == TARGET
    assert data['scope'] == 'separate smooth forward model target'
    assert data['verdict'] == 'SMOOTH FORWARD TARGET OPEN'
    assert data['canonical_point4'] == 'NO STATUS CHANGE; canonical completion requires its own actual audit'
    wanted = {'pins': True, 'frozen_interfaces': True, 'source_scan': True,
              'official_version': True, 'full_build': True, 'new_module_build': True,
              'exact_type': False, 'standard_axioms': False}
    assert data['gates'] == wanted and all(type(v) is bool for v in data['gates'].values()), 'Exact smooth OPEN gate pattern changed'


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    for name in ('schema', 'probe-log', 'axiom-dir', 'audit-json', 'smooth-probe-log',
                 'smooth-completion-log', 'smooth-audit-json'):
        parser.add_argument('--'+name, type=pathlib.Path)
    for name in ('audit-rc', 'smooth-completion-rc', 'smooth-audit-rc'):
        parser.add_argument('--'+name, type=int)
    args = parser.parse_args(argv)
    inherited_args = []
    for name in ('schema', 'probe-log', 'axiom-dir', 'audit-json', 'audit-rc'):
        value = getattr(args, name.replace('-', '_'))
        if value is not None:
            inherited_args.extend(['--'+name, str(value)])
    release = legacy()
    release.main(inherited_args)  # Original full source/evidence gate bodies.
    metadata = (ROOT / METADATA).read_text()
    check_new_metadata(metadata)
    if args.schema:
        import jsonschema
        schema = args.schema.read_bytes()
        assert sha256(schema) == release.c2_guard().SCHEMA_SHA256
        jsonschema.validate(release.c2_guard().parse_metadata(metadata), json.loads(schema))
    for path in (PROBE, COMPLETION):
        assert sha256((ROOT / path).read_bytes()) == FILE_SHA256[path]
    if args.smooth_probe_log:
        check_support_probe(args.smooth_probe_log.read_text())
    assert (args.smooth_completion_log is None) == (args.smooth_completion_rc is None)
    if args.smooth_completion_log:
        check_completion_open(args.smooth_completion_log.read_text(), args.smooth_completion_rc)
    assert (args.smooth_audit_json is None) == (args.smooth_audit_rc is None)
    if args.smooth_audit_json:
        check_smooth_audit_open(json.loads(args.smooth_audit_json.read_text()), args.smooth_audit_rc)
    print(json.dumps({'base': BASE, 'public_paths': 1672, 'exact_inherited_release_adapters': 1,
                      'smooth_support_proofs': 'separate exact-head gates required',
                      'smooth_general_target': 'OPEN', 'canonical_point4': 'OPEN'}, indent=2))


# Reviewed finite smooth/master composition; original validator bodies survive.
import hashlib as _composition_hashlib, pathlib as _composition_pathlib, stat as _composition_stat, sys as _composition_sys
_composition_file = _composition_pathlib.Path(__file__).resolve().parents[2] / 'curvature/scripts/point4_smooth_master_composition.py'
assert _composition_stat.S_ISREG(_composition_file.lstat().st_mode) and not _composition_file.lstat().st_mode & 0o111
assert _composition_hashlib.sha256(_composition_file.read_bytes()).hexdigest() == '82c4563228912fd4a45c63279e40959f7d9e8262e29338292f485c3226b45bd8', 'Composition executable binding changed'
import point4_smooth_master_composition as _smooth_master
_smooth_master.install_smooth(globals())

if __name__ == '__main__':
    # Use one module identity even when the original guard imports this entry.
    sys.modules.setdefault('point4_smooth_forward_release_guard', sys.modules[__name__])
    main()
