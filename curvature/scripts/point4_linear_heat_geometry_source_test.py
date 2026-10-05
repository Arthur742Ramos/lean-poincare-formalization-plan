#!/usr/bin/env python3
"""Immutable-parent integration guard; source validation is not Lean verification."""
from __future__ import annotations
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = '60b6f8ef9d37d1fc5fac1f6113584e1b16370016'
PARENTS = (
    '4e27b905a5645b27e0e101124fd011c4dbd00586',
    'f1ee137abbd46111f5d9722d41d4f62960e8f171',
    'ecb86c90b902b17cf6889c4f89a31e80702e39c9',
)
LIBROOT = 'curvature/PoincareCurvature.lean'
SCHEMA_SHA256 = '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
PROBES = (
    'contraction', 'coordinate_connection', 'coordinate_jet', 'coordinate_operator',
    'principal_remainder', 'chosen_lc_coordinate', 'chosen_lc_curvature',
    'standard_coordinate_operator', 'frozen_metric_principal', 'weak_laplacian',
    'boundaryless_chart_frames',
)


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def tracked(sha: str) -> set[str]:
    return set(git('ls-tree', '-r', '--name-only', sha).decode().splitlines())


def blob(sha: str, path: str) -> bytes:
    return git('show', f'{sha}:{path}')


def protected(path: str) -> bool:
    # Protect every inherited proof in the repository, all inherited workflows,
    # executable completion machinery, pins, attribution and the approved scope.
    return path.endswith('.lean') or path.startswith('.github/workflows/') or \
        path in {
            'AGENTS.md', 'LICENSE', 'curvature/lean-toolchain',
            'curvature/lake-manifest.json', 'curvature/lakefile.toml',
            'curvature/scripts/point4_audit.sh', 'curvature/scripts/point4_scan.py',
            'curvature/scripts/point4_done_verifier.sh', 'curvature/scripts/point4_target.txt',
            'curvature/scripts/point4_closed_contract_source_test.py',
            'docs/point4/closed-contract.md', 'docs/point4/closed-contract/formalization.yaml',
        } or re.fullmatch(r'curvature/AGENT-CONTRIBUTION(?:-\d+)?\.md', path) is not None


def expected_sources() -> dict[str, tuple[str, bytes]]:
    expected = {p: (BASE, blob(BASE, p)) for p in tracked(BASE) if protected(p)}
    touched: set[str] = set()
    for parent in PARENTS:
        ancestor = git('merge-base', BASE, parent).decode().strip()
        changed = git('diff', '--name-only', ancestor, parent).decode().splitlines()
        for path in changed:
            if protected(path) and path != LIBROOT:
                assert path not in touched, f'Overlapping parent mutation requires review: {path}'
                assert path in tracked(parent), f'Parent deleted protected file: {path}'
                expected[path] = (parent, blob(parent, path))
                touched.add(path)
    expected.pop(LIBROOT)
    return expected


def check_equal(path: str, actual: bytes, expected: bytes) -> None:
    assert actual == expected, f'Immutable source changed: {path}'


def imports(source: bytes) -> set[str]:
    return set(re.findall(rb'^import (\S+)\s*$', source, re.M))


def check_imports(actual: bytes) -> None:
    sources = [blob(sha, LIBROOT) for sha in (BASE, *PARENTS)]
    want = set.union(*(imports(s) for s in sources))
    assert imports(actual) == want, 'Root imports must be the full exact parent union'
    # The root is an import-only surface; no hidden declaration or option is allowed.
    def other_content(s: bytes) -> bytes:
        return b'\n'.join(line for line in s.splitlines()
                          if line.strip() and not re.fullmatch(rb'import \S+', line.strip()))
    assert other_content(actual) == other_content(sources[0]), 'Unexpected root library content'
    assert b'PoincareCurvature.Geometry.Manifold.RicciFlow.PointFourContract' in want
    assert b'PoincareCurvature.Geometry.Manifold.RicciFlow.StandardRicciDeTurckCoordinateOperator' in want


def metadata_ids(source: str) -> list[str]:
    related = source.split('related_formalizations:\n', 1)[1].split('\nstatus:', 1)[0]
    return re.findall(r'^  - id: "([^"]+)"', related, re.M)


def check_metadata(source: str) -> None:
    ids = metadata_ids(source)
    assert len(ids) == len(set(ids)), 'Duplicate related formalization identity'
    original = set.union(*(set(metadata_ids(blob(s, 'curvature/formalization.yaml').decode()))
                           for s in (BASE, *PARENTS)))
    expected = original | {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{s}/curvature'
        for s in (BASE, *PARENTS)
    }
    assert set(ids) == expected, 'Missing or unrelated structured provenance'
    def entries(s: str) -> dict[str, tuple[str, str]]:
        related = s.split('related_formalizations:\n', 1)[1].split('\nstatus:', 1)[0]
        result = {}
        for entry in re.findall(r'  - id:.*?(?=  - id:|\Z)', related, re.S):
            identity = re.search(r'  - id: "([^"]+)"', entry)[1]
            relationship = re.search(r'    relationship: "([^"]+)"', entry)[1]
            note = ' '.join(entry.split('    note: >-\n', 1)[1].split())
            result[identity] = (relationship, note)
        return result
    combined = entries(source)
    for sha in (BASE, *PARENTS):
        for identity, (relationship, note) in entries(blob(sha, 'curvature/formalization.yaml').decode()).items():
            assert combined[identity][0] == relationship, 'Changed provenance relationship'
            assert note in combined[identity][1], 'Dropped inherited provenance note'
    assert all(combined[identity][0] == 'builds-on' for identity in expected)
    # Preserve all original selected artifact metadata and model/history fields.
    def outside_related(s: str) -> str:
        a = s.index('related_formalizations:\n')
        b = s.index('\nstatus:', a)
        return (s[:a] + s[b:]).replace('method: "agent-assisted"', 'method: "agent"')
    assert outside_related(source) == outside_related(blob(BASE, 'curvature/formalization.yaml').decode()), \
        'Non-provenance metadata changed'


def check_axiom_output(source: str, output: str) -> set[str]:
    expected = set(re.findall(r'^#print axioms (\S+)', source, re.M))
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [n for n, _ in entries] + clean
    assert set(names) == expected and len(names) == len(expected), 'Missing/duplicate axiom evidence'
    for name, axioms in entries:
        actual = {a.strip() for a in axioms.split(',') if a.strip()}
        assert actual <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
    return expected


def check_boundaryless_types(output: str) -> None:
    types = output.split('BOUNDARYLESS_TYPES_BEGIN', 1)[1].split('BOUNDARYLESS_TYPES_END', 1)[0]
    assert types.count('BoundarylessManifold') == 7, types
    assert 'ModelWithCorners.Boundaryless' not in types and 'I.Boundaryless' not in types, types


def check_audit(data: dict, rc: int) -> None:
    assert data['build_run'] is True, 'Full build is mandatory'
    assert data['gates']['G1_sorry_free']['status'] == 'PASS', data
    assert data['gates']['G2_build_green']['status'] == 'PASS', data
    if data['verdict'] == 'CLOSED':
        assert rc == 0 and all(g['status'] == 'PASS' for g in data['gates'].values()), data
    else:
        assert data['verdict'] == 'OPEN' and rc == 1, data
        # This immutable supporting integration supplies no canonical theorem.
        assert all(data['gates'][k]['status'] == 'FAIL' for k in
                   ('G3_unconditional', 'G4_axiom_clean', 'G5_faithful_type')), data
        assert data['target_base'] == 'intrinsicLocalExistenceUniquenessFamily_pointFour', data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
    parser.add_argument('--axiom-dir', type=pathlib.Path)
    parser.add_argument('--audit-json', type=pathlib.Path)
    parser.add_argument('--audit-rc', type=int)
    args = parser.parse_args()
    for sha in (BASE, *PARENTS):
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', sha, 'HEAD'], check=True)
    expected = expected_sources()
    for path, (_, wanted) in expected.items():
        check_equal(path, (ROOT / path).read_bytes(), wanted)
    # Adding a new proof file would exceed the approved integration-only scope.
    actual_lean = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean')
                   if '.lake' not in p.parts and '.toolchain' not in p.parts and '.git' not in p.parts}
    assert actual_lean == {p for p in expected if p.endswith('.lean')} | {LIBROOT}, \
        'Unexpected added/deleted Lean source'
    check_imports((ROOT / LIBROOT).read_bytes())
    metadata = (ROOT / 'curvature/formalization.yaml').read_text()
    check_metadata(metadata)
    if args.schema:
        import jsonschema, yaml
        schema_bytes = args.schema.read_bytes()
        assert hashlib.sha256(schema_bytes).hexdigest() == SCHEMA_SHA256, 'Official schema bytes changed'
        jsonschema.validate(yaml.safe_load(metadata), json.loads(schema_bytes))
    if args.axiom_dir:
        total = 0
        distinct = set()
        for name in PROBES:
            source = (ROOT / f'curvature/scripts/point4_{name}_probe.lean').read_text()
            output = (args.axiom_dir / f'{name}.log').read_text()
            names = check_axiom_output(source, output)
            total += len(names)
            distinct |= names
        assert total == 127, total
        print(f'Combined axiom evidence: {total} audited occurrences; {len(distinct)} distinct declarations')
        check_boundaryless_types((args.axiom_dir / 'boundaryless_chart_frames.log').read_text())
    if args.audit_json:
        assert args.audit_rc is not None
        check_audit(json.loads(args.audit_json.read_text()), args.audit_rc)
    report = {}
    for path, (sha, wanted) in expected.items():
        report.setdefault(sha, 0)
        report[sha] += 1
    print('Immutable-parent integration source guards passed:', json.dumps(report, sort_keys=True))
    print('All inherited proof blobs, workflows, completion machinery and selected metadata preserved')
    print('Source checks do not certify Lean compilation or Point-4 completion')



# Reviewed combined C2 integration adapter. The immutable legacy guard remains
# above; the shared guard pins this precise adapter and the full parent union.
if (ROOT / 'curvature/scripts/point4_c2_initial_heat_source_test.py').is_file():
    import point4_c2_initial_heat_source_test as _c2_union
    expected_sources = _c2_union.expected_sources
    check_imports = _c2_union.check_imports
    check_metadata = _c2_union.check_metadata
    check_audit = _c2_union.check_audit

# Exact weighted-Hessian inventory dispatch. The original semantic gate body
# above is replayed from its byte/mode-pinned historical source reconstruction;
# current physical source and evidence checks are independently mandatory.
_weighted_hessian_historical_main = main
def main(argv=None):
    from point4_weighted_hessian_release_guard import run_inherited
    run_inherited('curvature/scripts/point4_linear_heat_geometry_source_test.py', argv)

if __name__ == '__main__':
    main()
