#!/usr/bin/env python3
"""Exact pinned-parent source/evidence union; source checks are not kernel certification."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
MASTER = '0ae19db1b5f423e6c5db9b8199948769102c03c2'
TRACE = 'ba47fe1f4d8efad8bad68c61b4d25d0d8ff5387e'
WEIGHTED = '4c488607b92421e8e85e0d4911556e8a40e294b4'
OLD_MASTER = '60b6f8ef9d37d1fc5fac1f6113584e1b16370016'
HISTORICAL = '591c25914c80366d619ece00da204997ee2a65d7'
REPAIR = 'f908454fac787a720239e04feee6d61a9f9ab202'
LIBROOT = 'curvature/PoincareCurvature.lean'
METADATA = 'curvature/formalization.yaml'
GEOMETRY_GUARD = 'curvature/scripts/point4_linear_heat_geometry_source_test.py'
WEIGHTED_GUARD = 'curvature/scripts/point4_weighted_initial_heat_guard.py'
WEIGHTED_PROOF = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatWeightedInitialHolder.lean'
WEIGHTED_SHA256 = 'a1ca6c80dabcc0f9df8d788870869bc0a5eff453752e8fef1379cc8a2d0dca23'
WORKFLOW_SHA256 = 'ef766da73c4c7cbf98fa20ef4c9c95f968e5fff33c2fb2f8f5bd051ae3ba8a45'
SCHEMA_SHA256 = '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
# Exact inherited source files exempted only for the documented import union,
# provenance union and current-status integration summary. No proof is exempt.
EDITABLE = {LIBROOT, METADATA, 'docs/status.md', 'docs/point4/README.md'}
ADDED = {
    'curvature/scripts/point4_c2_initial_heat_source_test.py',
    'curvature/scripts/point4_c2_initial_heat_mock_test.py',
    '.github/workflows/point4-c2-initial-heat.yml',
    'docs/point4/c2-initial-heat-integration.md',
}
PROBES = (
    'contraction', 'coordinate_connection', 'coordinate_jet', 'coordinate_operator',
    'principal_remainder', 'chosen_lc_coordinate', 'chosen_lc_curvature',
    'standard_coordinate_operator', 'frozen_metric_principal', 'weak_laplacian',
    'boundaryless_chart_frames', 'c2_heat_trace', 'weighted_initial_heat',
)
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')

GEOMETRY_ADAPTER = "\n# Reviewed combined C2 integration adapter. The immutable legacy guard remains\n# above; the shared guard pins this precise adapter and the full parent union.\nif (ROOT / 'curvature/scripts/point4_c2_initial_heat_source_test.py').is_file():\n    import point4_c2_initial_heat_source_test as _c2_union\n    expected_sources = _c2_union.expected_sources\n    check_imports = _c2_union.check_imports\n    check_metadata = _c2_union.check_metadata\n    check_audit = _c2_union.check_audit\n\n"
WEIGHTED_ADAPTER = "\n# Reviewed combined C2 integration adapter. The original standalone checks\n# below remain historical; the shared guard pins this exact adapter and union.\nif (ROOT / 'curvature/scripts/point4_c2_initial_heat_source_test.py').is_file():\n    import point4_c2_initial_heat_source_test as _c2_union\n    _c2_union.main(['--schema', sys.argv[1]] if len(sys.argv) == 2 else [])\n    sys.exit(0)\n\n"

def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)


def tracked(sha: str) -> set[str]:
    return set(git('ls-tree', '-r', '--name-only', sha).decode().splitlines())


def blob(sha: str, path: str) -> bytes:
    return git('show', f'{sha}:{path}')


def check_ancestry() -> None:
    assert git('show', '-s', '--format=%P', TRACE).decode().split() == [HISTORICAL, OLD_MASTER]
    assert git('merge-base', MASTER, WEIGHTED).decode().strip() == OLD_MASTER
    for sha in (MASTER, TRACE, WEIGHTED, HISTORICAL, REPAIR):
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', sha, 'HEAD'], check=True, env=ENV)


def expected_sources() -> dict[str, tuple[str, bytes]]:
    check_ancestry()
    master_paths, weighted_paths = tracked(MASTER), tracked(WEIGHTED)
    expected = {p: (MASTER, blob(MASTER, p)) for p in master_paths if p not in EDITABLE}
    changed = set(git('diff', '--name-only', OLD_MASTER, WEIGHTED).decode().splitlines())
    for path in changed - EDITABLE:
        assert path in weighted_paths, f'Input deletes inherited path: {path}'
        assert path not in expected, f'Overlapping pinned source requires review: {path}'
        expected[path] = (WEIGHTED, blob(WEIGHTED, path))
    # Sole inherited script changes: exact byte transformations from pinned originals.
    original = blob(MASTER, GEOMETRY_GUARD).decode()
    assert original.count("if __name__ == '__main__':") == 1
    expected[GEOMETRY_GUARD] = (MASTER, original.replace("if __name__ == '__main__':", GEOMETRY_ADAPTER + "if __name__ == '__main__':").encode())
    original = blob(WEIGHTED, WEIGHTED_GUARD).decode()
    assert original.count('\ndef git(*args):') == 1
    expected[WEIGHTED_GUARD] = (WEIGHTED, original.replace('\ndef git(*args):', WEIGHTED_ADAPTER + '\ndef git(*args):').encode())
    return expected


def check_public_paths(actual: set[str], expected: set[str]) -> None:
    assert actual == expected | EDITABLE | ADDED, ('Unexpected/missing public path', sorted(actual ^ (expected | EDITABLE | ADDED)))


def check_workflow(actual: bytes) -> None:
    assert hashlib.sha256(actual).hexdigest() == WORKFLOW_SHA256, 'Combined exact-head workflow drift'


def check_equal(path: str, actual: bytes, expected: bytes) -> None:
    assert actual == expected, f'Immutable source changed: {path}'


def imports(source: bytes) -> list[bytes]:
    return re.findall(rb'^import (\S+)\s*$', source, re.M)


def check_imports(actual: bytes) -> None:
    sources = [blob(sha, LIBROOT) for sha in (MASTER, TRACE, WEIGHTED)]
    names = imports(actual)
    want = set.union(*(set(imports(s)) for s in sources))
    assert set(names) == want and len(names) == len(want), 'Missing/extra/duplicate root imports'
    def other_content(s: bytes) -> bytes:
        return b'\n'.join(line for line in s.splitlines() if line.strip() and not re.fullmatch(rb'import \S+', line.strip()))
    assert other_content(actual) == other_content(sources[0]), 'Unexpected root declaration/option/content'


def metadata_entries(source: str) -> dict[str, tuple[str, str]]:
    related = source.split('related_formalizations:\n', 1)[1].split('\nstatus:', 1)[0]
    result = {}
    for entry in re.findall(r'  - id:.*?(?=  - id:|\Z)', related, re.S):
        identity = re.search(r'  - id: "([^"]+)"', entry)[1]
        assert identity not in result, 'Duplicate provenance identity'
        relationship = re.search(r'    relationship: "([^"]+)"', entry)[1]
        note = ' '.join(entry.split('    note: >-\n', 1)[1].split())
        result[identity] = (relationship, note)
    return result


def check_metadata(source: str) -> None:
    actual = metadata_entries(source)
    parents = [metadata_entries(blob(s, METADATA).decode()) for s in (MASTER, TRACE, WEIGHTED)]
    want = set.union(*(set(p) for p in parents)) | {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{s}/curvature'
        for s in (MASTER, TRACE, WEIGHTED)
    }
    assert set(actual) == want, 'Missing/extra structured provenance'
    assert all(v[0] == 'builds-on' for v in actual.values())
    for parent in parents:
        for identity, (relationship, note) in parent.items():
            assert actual[identity][0] == relationship and note in actual[identity][1], 'Dropped/changed inherited provenance'
    def outside_related(s: str) -> str:
        a = s.index('related_formalizations:\n'); b = s.index('\nstatus:', a)
        return s[:a] + s[b:]
    assert outside_related(source) == outside_related(blob(MASTER, METADATA).decode()), 'Changed selected artifact/authorship/license/model history'


def probe_names(source: str) -> list[str]:
    names = re.findall(r'^#print axioms (\S+)', source, re.M)
    if 'open RicciFlow.AnalyticPDE' in source:
        names = [n if n.startswith(('PoincareCurvature.', 'RicciFlow.')) else 'RicciFlow.AnalyticPDE.' + n for n in names]
    assert names and len(names) == len(set(names)), 'Empty/duplicate source axiom surface'
    return names


def check_axiom_output(source: str, output: str) -> set[str]:
    expected = probe_names(source)
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [n for n, _ in entries] + clean
    assert set(names) == set(expected) and len(names) == len(expected), 'Missing/extra/duplicate actual axiom records'
    for name, axioms in entries:
        fields = [a.strip() for a in axioms.split(',') if a.strip()]
        assert len(fields) == len(set(fields)), 'Duplicate axiom record entry'
        assert set(fields) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, fields)
    return set(expected)


def check_boundaryless_types(output: str) -> None:
    assert output.count('BOUNDARYLESS_TYPES_BEGIN') == 1 and output.count('BOUNDARYLESS_TYPES_END') == 1
    types = output.split('BOUNDARYLESS_TYPES_BEGIN', 1)[1].split('BOUNDARYLESS_TYPES_END', 1)[0]
    assert types.count('BoundarylessManifold') == 7, types
    assert 'ModelWithCorners.Boundaryless' not in types and 'I.Boundaryless' not in types, types


def check_audit(data: dict, rc: int) -> None:
    assert data['build_run'] is True, 'Actual full audit/build is mandatory'
    assert data['verdict'] == 'OPEN' and rc == 1, 'This supporting union cannot claim canonical closure'
    assert data['target_base'] == 'intrinsicLocalExistenceUniquenessFamily_pointFour'
    assert data.get('fqn', '') == '', 'Canonical target must remain absent'
    statuses = {'G1_sorry_free': 'PASS', 'G2_build_green': 'PASS', 'G3_unconditional': 'FAIL', 'G4_axiom_clean': 'FAIL', 'G5_faithful_type': 'FAIL'}
    assert set(data['gates']) == set(statuses), 'Missing/extra audit gates'
    assert all(data['gates'][k]['status'] == v for k, v in statuses.items()), data


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
    parser.add_argument('--axiom-dir', type=pathlib.Path)
    parser.add_argument('--audit-json', type=pathlib.Path)
    parser.add_argument('--audit-rc', type=int)
    args = parser.parse_args(argv)
    expected = expected_sources()
    for path, (_, wanted) in expected.items():
        check_equal(path, (ROOT / path).read_bytes(), wanted)
    # Entire tracked public tree is pinned except four enumerated new integration paths.
    actual = set(git('ls-files', '--cached', '--others', '--exclude-standard').decode().splitlines())
    actual = {p for p in actual if '__pycache__' not in pathlib.PurePosixPath(p).parts}
    check_public_paths(actual, set(expected))
    check_workflow((ROOT / '.github/workflows/point4-c2-initial-heat.yml').read_bytes())
    physical_lean = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean') if not {'.git', '.lake', '.toolchain'} & set(p.parts)}
    assert physical_lean == {p for p in expected if p.endswith('.lean')} | {LIBROOT}, 'Unexpected/missing physical proof path'
    check_imports((ROOT / LIBROOT).read_bytes())
    metadata = (ROOT / METADATA).read_text(); check_metadata(metadata)
    assert hashlib.sha256((ROOT / WEIGHTED_PROOF).read_bytes()).hexdigest() == WEIGHTED_SHA256
    if args.schema:
        import jsonschema, yaml
        schema = args.schema.read_bytes()
        assert hashlib.sha256(schema).hexdigest() == SCHEMA_SHA256, 'Full official schema identity changed'
        jsonschema.validate(yaml.safe_load(metadata), json.loads(schema))
    if args.axiom_dir:
        assert {p.name for p in args.axiom_dir.iterdir()} == {p + '.log' for p in PROBES}, 'Missing/extra probe evidence files'
        total, distinct = 0, set()
        for name in PROBES:
            names = check_axiom_output((ROOT / f'curvature/scripts/point4_{name}_probe.lean').read_text(), (args.axiom_dir / f'{name}.log').read_text())
            total += len(names); distinct |= names
        assert total == 150 and len(distinct) == 144, (total, len(distinct))
        check_boundaryless_types((args.axiom_dir / 'boundaryless_chart_frames.log').read_text())
        print(f'Actual combined axiom evidence: {total} occurrences across {len(distinct)} declarations')
    if args.audit_json:
        assert args.audit_rc is not None
        check_audit(json.loads(args.audit_json.read_text()), args.audit_rc)
    assert args.audit_json or args.audit_rc is None, 'Audit exit status without audit evidence'
    print(f'Pinned combined public source union passed: {len(expected)} preserved paths; exact two reviewed guard adapters')
    print('No proof deleted/modified; inherited workflows, probes, canonical contract/negative fixtures, auditor, pins and notices retained')
    print('Source checks are not kernel certification; exact-head full builds and independent review remain mandatory; Point 4 OPEN')


if __name__ == '__main__':
    main()
