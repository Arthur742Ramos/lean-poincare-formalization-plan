#!/usr/bin/env python3
"""Frozen source and evidence gates; this does not certify a Lean proof."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import yaml

ROOT = pathlib.Path(__file__).resolve().parents[2]
MASTER = '0ae19db1b5f423e6c5db9b8199948769102c03c2'
TRACE = 'ba47fe1f4d8efad8bad68c61b4d25d0d8ff5387e'
INTEGRATION_PARENT = 'fe921dbc34918d22389e87f30bdffb73ed7ebeb9'
MATHLIB = 'db584cd6d46c92f209a44c0f1c829460d327499d'
TOOLCHAIN = 'leanprover/lean4:v4.33.0\n'
SCHEMA_SHA256 = '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
PREFIX = 'curvature/PoincareCurvature/'
MODULES = {
    PREFIX + 'Analysis/CompactlySupportedC2Jet.lean': '3dfa3d8bd3cea730bf08afc91fd8dd759ba3c0365790072ee0b52f5844dc997f',
    PREFIX + 'Analysis/FiniteCoordinateBilinear.lean': '1983651e92f98f5c7358e57508432d6aa8db503389c36ef1faef73dde0d96b59',
    PREFIX + 'Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanC2Localization.lean': '0a9d069693a71982da3903af6d6357bc4a29b97d700d049e93d8203c0e6eac57',
    PREFIX + 'Geometry/Manifold/RicciFlow/AnalyticPDE/PositiveFrozenC2Localization.lean': '792abb3502c66fe25dd520edb4ce94c8979c20945de25f3ff80eba886a194f0a',
    PREFIX + 'Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessInitialMetricLocalization.lean': 'b2334e88fb307d3978be6605f753046fe4d30db9102df71cf25800a99c29b424',
}
PROBE = 'curvature/scripts/point4_c2_metric_localization_probe.lean'
PROBE_SHA256 = 'c207ce99c603fae11dc46be04abb0e934884c177c071e28c7afe141b596afc02'
EDITABLE = {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml', 'docs/point4/README.md'}
ADDED = set(MODULES) | {PROBE,
    'curvature/scripts/point4_c2_metric_localization_source_test.py',
    'curvature/scripts/point4_c2_metric_localization_mock_test.py',
    '.github/workflows/point4-c2-metric-localization.yml',
    'docs/point4/c2-metric-localization.md',
}
PARENT_NOTE_SHA256 = 'c0a52690c6a3aba88362de1a48b464e50e1728160d4c27d2744ae706624f53ef'
LEGACY_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
LEGACY_GUARD_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
LEGACY_ADAPTER = "\n# Reviewed literal-C2 localization adapter. Every original definition, fixture\n# and evidence gate remains above. The literal-unit guard pins this count-one\n# transform of exact reviewed PR129 and extends only the enumerated source union.\nif (ROOT / 'curvature/scripts/point4_c2_metric_localization_source_test.py').is_file():\n    import point4_c2_metric_localization_source_test as _literal_unit\n    expected_sources = _literal_unit.legacy_expected_sources\n    check_imports = _literal_unit.legacy_check_imports\n    check_metadata = _literal_unit.legacy_check_metadata\n    ADDED = ADDED | _literal_unit.ADDED\n\n"
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SURFACES = {
    'PoincareCurvature.CompactlySupportedC2Jet.uniformContinuous_second',
    'PoincareCurvature.CompactlySupportedC2Jet.second_eq_fderiv_fderiv',
    'PoincareCurvature.FiniteCoordinateBilinear.norm_ofMatrix_le',
} | {'RicciFlow.AnalyticPDE.' + s for s in (
    'EuclideanBoundedC2Data.ofCompactSupport',
    'EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero_addConst_ofCompactSupport',
    'exists_positiveFrozenC2Bilinear', 'exists_positiveFrozenC2MatrixHeatData',
    'contDiffOn_initialMetricCoordinates', 'initialMetricCoordinates_pos_at_point',
    'exists_initialMetricLocalizedHeatData',
)}

class StrictLoader(yaml.SafeLoader):
    pass

def unique_mapping(loader, node, deep=False):
    result = {}
    for key, value in node.value:
        key = loader.construct_object(key, deep=deep)
        assert key not in result, f'Duplicate YAML key: {key}'
        result[key] = loader.construct_object(value, deep=deep)
    return result

StrictLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)

def strict_yaml(raw: bytes | str):
    return yaml.load(raw, Loader=StrictLoader)

def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)

def tree(sha: str) -> dict[str, str]:
    result = {}
    for entry in git('ls-tree', '-rz', sha).split(b'\0'):
        if not entry:
            continue
        metadata, path = entry.split(b'\t', 1)
        mode, kind, digest = metadata.decode().split()
        assert kind == 'blob', (path, kind)
        result[path.decode()] = digest
    return result

def blob(sha: str, path: str) -> bytes:
    return git('show', f'{sha}:{path}')

def check_hash(path: str, digest: str) -> None:
    p = ROOT / path
    assert p.is_file() and not p.is_symlink(), path
    assert hashlib.sha256(p.read_bytes()).hexdigest() == digest, f'Frozen source drift: {path}'

def check_ancestry() -> None:
    for sha in (INTEGRATION_PARENT, MASTER, TRACE):
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', sha, 'HEAD'], check=True, env=ENV)

def adapt_legacy_guard(original: bytes) -> bytes:
    assert hashlib.sha256(original).hexdigest() == LEGACY_GUARD_SHA256, 'Original PR129 guard drift'
    anchor = "\nif __name__ == '__main__':"
    text = original.decode()
    assert text.count(anchor) == 1, 'Adapter insertion must be count-one'
    return text.replace(anchor, LEGACY_ADAPTER + anchor, 1).encode()

def expected_hashes() -> dict[str, str]:
    expected = tree(INTEGRATION_PARENT)
    changed = adapt_legacy_guard(blob(INTEGRATION_PARENT, LEGACY_GUARD))
    expected[LEGACY_GUARD] = hashlib.sha1(b'blob ' + str(len(changed)).encode() + b'\0' + changed).hexdigest()
    return expected

def source_fingerprints() -> dict[str, str]:
    check_ancestry()
    expected = expected_hashes()
    protected = {p: h for p, h in expected.items() if p not in EDITABLE}
    for path, digest in protected.items():
        p = ROOT / path
        assert p.is_file() and not p.is_symlink(), path
        assert git('hash-object', '--', path).decode().strip() == digest, f'Inherited source/evidence drift: {path}'
    for path, digest in MODULES.items():
        check_hash(path, digest)
    check_hash(PROBE, PROBE_SHA256)
    return protected

def legacy_expected_sources() -> dict[str, tuple[str, bytes]]:
    # Validate the complete precise parent/adapter and authored proof hashes
    # before returning bytes to any preserved original guard or mock fixture.
    protected = source_fingerprints()
    result = {p: (INTEGRATION_PARENT, (ROOT / p).read_bytes()) for p in protected}
    for p in ADDED:
        result[p] = ('literal-C2-reviewed-unit', (ROOT / p).read_bytes())
    return result

def legacy_check_imports(actual: bytes) -> None:
    base = blob(INTEGRATION_PARENT, 'curvature/PoincareCurvature.lean')
    check_imports(actual, base, base)

def legacy_check_metadata(actual: str) -> None:
    base = blob(INTEGRATION_PARENT, 'curvature/formalization.yaml')
    check_metadata(actual.encode(), base, base)


def check_imports(raw: bytes, master: bytes, trace: bytes) -> None:
    def imports(text: bytes) -> list[str]:
        result = []
        for line in text.decode().splitlines():
            if not line.strip() or line.startswith('--'):
                continue
            assert re.fullmatch(r'import [A-Za-z0-9_.]+', line), f'Non-import root code: {line}'
            result.append(line)
        assert len(result) == len(set(result)), 'Duplicate root import'
        return result
    expected = set(imports(master)) | set(imports(trace)) | {
        'import ' + p.removeprefix('curvature/').removesuffix('.lean').replace('/', '.') for p in MODULES
    }
    assert set(imports(raw)) == expected, 'Root import union drift'
    def nonimports(text: bytes) -> bytes:
        return b'\n'.join(line for line in text.splitlines()
                          if line.strip() and not re.fullmatch(rb'import \S+', line.strip()))
    assert nonimports(raw) == nonimports(master), 'Root comment/non-import content drift'

def entries(data: dict) -> dict[str, dict]:
    out = {}
    for item in data['related_formalizations']:
        assert isinstance(item, dict) and set(item) == {'id', 'relationship', 'note'}, item
        assert isinstance(item['id'], str) and isinstance(item['note'], str), item
        assert item['id'] not in out, f'Duplicate related identity: {item["id"]}'
        assert item['relationship'] == 'builds-on', item
        out[item['id']] = item
    return out

def check_metadata(raw: bytes, master: bytes, trace: bytes) -> None:
    def outside_related(text: bytes) -> bytes:
        start = text.index(b'related_formalizations:\n')
        end = text.index(b'\nstatus:', start)
        return text[:start] + text[end:]
    assert outside_related(raw) == outside_related(master), 'Non-provenance metadata bytes drift'
    current, old, heat = map(strict_yaml, (raw, master, trace))
    assert {k: v for k, v in current.items() if k != 'related_formalizations'} == {
        k: v for k, v in old.items() if k != 'related_formalizations'}
    actual = entries(current)
    expected = {}
    for data in (old, heat):
        for key, value in entries(data).items():
            if key not in expected:
                expected[key] = dict(value)
            elif expected[key].get('note') != value.get('note'):
                expected[key]['note'] = expected[key].get('note', '').strip() + '\n' + value.get('note', '').strip()
    extra = {f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{INTEGRATION_PARENT}/curvature'}
    assert set(actual) == set(expected) | extra, 'Provenance identity union drift'
    for key, value in expected.items():
        actual_item = dict(actual[key]); expected_item = dict(value)
        actual_item['note'] = ' '.join(actual_item.get('note', '').split())
        expected_item['note'] = ' '.join(expected_item.get('note', '').split())
        assert actual_item == expected_item, f'Inherited provenance drift: {key}'
    for key in extra:
        assert actual[key]['relationship'] == 'builds-on' and actual[key].get('note'), key
        assert hashlib.sha256(' '.join(actual[key]['note'].split()).encode()).hexdigest() == PARENT_NOTE_SHA256, 'Literal parent note drift'

def check_no_cache(paths: set[str]) -> None:
    for path in paths:
        assert not any(part in {'.lake', '.development', '__pycache__'} for part in pathlib.PurePosixPath(path).parts), path
        assert not path.endswith(('.olean', '.ilean', '.olean.private', '.olean.server', '.pyc')), path

def check_axioms(output: str) -> None:
    found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [name for name, _ in found] + clean
    all_reports = re.findall(r"(?m)^'([^']+)' (?:depends on axioms:|does not depend on any axioms?)", output)
    assert len(all_reports) == len(names), 'Malformed or unparsed axiom report'
    assert len(names) == len(set(names)), 'Duplicate axiom result'
    assert set(names) == SURFACES, f'Missing/extra axiom surfaces: {set(names) ^ SURFACES}'
    for name, raw in found:
        fields = [a.strip() for a in raw.split(',') if a.strip()]
        assert len(fields) == len(set(fields)), 'Duplicate axiom within record'
        assert set(fields) <= AXIOMS, (name, fields)
    assert 'BoundarylessManifold' in output, 'Missing full endpoint type'
    assert 'ModelWithCorners.Boundaryless' not in output and 'I.Boundaryless' not in output

def check_audit(data: dict, rc: int) -> None:
    assert data['build_run'] is True, 'Fast audit cannot qualify'
    assert data['verdict'] == 'OPEN' and rc == 1, (data, rc)
    assert data['target_base'] == 'intrinsicLocalExistenceUniquenessFamily_pointFour', data
    assert data.get('fqn', '') == '', 'Canonical target must remain absent'
    assert set(data['gates']) == {
        'G1_sorry_free', 'G2_build_green', 'G3_unconditional', 'G4_axiom_clean', 'G5_faithful_type'
    }, 'Missing/extra canonical audit gates'
    assert data['gates']['G1_sorry_free']['status'] == 'PASS', data
    assert data['gates']['G2_build_green']['status'] == 'PASS', data
    for gate in ('G3_unconditional', 'G4_axiom_clean', 'G5_faithful_type'):
        assert data['gates'][gate]['status'] == 'FAIL', data
    assert 'not found in source' in data['gates']['G3_unconditional']['note'], data
    assert data['gates']['G4_axiom_clean']['note'] == 'target missing', data
    assert data['gates']['G5_faithful_type']['note'] == 'target missing', data

def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path, required=True)
    parser.add_argument('--manifest', type=pathlib.Path)
    args = parser.parse_args(argv)
    protected = source_fingerprints()
    expected = expected_hashes()
    tracked = set(git('ls-files', '-z').decode().split('\0')) - {''}
    check_no_cache(tracked)
    assert tracked <= set(expected) | ADDED, 'Unreviewed tracked source/evidence addition'
    assert {p for p in tracked if p.endswith('.lean')} <= set(protected) | set(MODULES) | {PROBE, 'curvature/PoincareCurvature.lean'}
    for path in ('curvature/lean-toolchain', 'curvature/lakefile.toml', 'curvature/lake-manifest.json',
                 'curvature/scripts/point4_audit.sh', 'curvature/scripts/point4_scan.py',
                 'curvature/scripts/point4_target.txt', 'curvature/scripts/point4_closed_contract_source_test.py'):
        assert (ROOT / path).read_bytes() == blob(INTEGRATION_PARENT, path), f'Pin/contract/auditor drift: {path}'
    assert (ROOT / 'curvature/lean-toolchain').read_text() == TOOLCHAIN
    check_imports((ROOT / 'curvature/PoincareCurvature.lean').read_bytes(), blob(INTEGRATION_PARENT, 'curvature/PoincareCurvature.lean'), blob(INTEGRATION_PARENT, 'curvature/PoincareCurvature.lean'))
    raw = (ROOT / 'curvature/formalization.yaml').read_bytes()
    check_metadata(raw, blob(INTEGRATION_PARENT, 'curvature/formalization.yaml'), blob(INTEGRATION_PARENT, 'curvature/formalization.yaml'))
    assert hashlib.sha256(args.schema.read_bytes()).hexdigest() == SCHEMA_SHA256
    import jsonschema
    jsonschema.validate(strict_yaml(raw), json.loads(args.schema.read_bytes()))
    for path in expected:
        if path.startswith('.github/workflows/'):
            assert (ROOT / path).read_bytes() == blob(INTEGRATION_PARENT, path), f'Inherited workflow drift: {path}'
    scanner = ROOT / 'curvature/scripts/point4_scan.py'
    result = subprocess.run(['python3', str(scanner), 'locate', 'intrinsicLocalExistenceUniquenessFamily_pointFour', str(ROOT / PREFIX)], capture_output=True)
    assert result.returncode != 0, 'This supporting milestone must not add a canonical target'
    subprocess.run(['python3', str(ROOT / 'curvature/scripts/point4_closed_contract_source_test.py')], check=True)
    cheats = subprocess.check_output(['python3', str(scanner), 'cheats', str(ROOT / PREFIX)], text=True)
    assert cheats.strip() == 'TOTAL 0', cheats
    if args.manifest:
        all_paths = set(protected) | ADDED | EDITABLE
        out = {'candidate': git('rev-parse', 'HEAD').decode().strip(), 'parents': [INTEGRATION_PARENT, MASTER, TRACE],
               'working_tree_is_commit_exact': not git('status', '--porcelain', '--untracked-files=no').strip(),
               'toolchain': TOOLCHAIN.strip(), 'mathlib': MATHLIB,
               'schema_sha256': SCHEMA_SHA256,
               'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(all_paths)}}
        args.manifest.write_text(json.dumps(out, indent=2) + '\n')
    print(f'Frozen five-module localization, {len(protected)} inherited files including all proof/probe sources, pins and canonical gates pass; source checks only')

if __name__ == '__main__':
    main()
