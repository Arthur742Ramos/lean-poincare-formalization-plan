#!/usr/bin/env python3
"""Additive manifold-only producer guard. Source tests are not Lean verification."""
from __future__ import annotations
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = 'e6b54dd0d7e73a51eb8efb083764b68ae8305a5a'
HISTORICAL_PRODUCER = '58c6fc21bafeb8a659d6751a1a9db7a74127a300'
PREFIX = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/'
MODULES = ('BoundarylessTensorHeatCoefficients.lean',
           'BoundarylessTensorHeatLocalization.lean',
           'BoundarylessTensorHeatFixedBackground.lean')
PROBE = 'curvature/scripts/point4_manifold_heat_probe.lean'
sys.path.insert(0, str(ROOT / 'curvature/scripts'))
from point4_scan import strip_comments


def git(repo: pathlib.Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args])


def check_sources(repo: pathlib.Path) -> dict:
    inherited = git(repo, 'ls-tree', '-r', '--name-only', BASE).decode().splitlines()
    for path in inherited:
        wanted = git(repo, 'show', f'{BASE}:{path}')
        # The release permits exactly one inherited source-guard transformation.
        # It is reconstructed from its digest-pinned master blob, never waived.
        if path == 'curvature/scripts/point4_c2_initial_heat_source_test.py':
            from point4_manifold_heat_release_guard import adapted_c2_guard
            wanted = adapted_c2_guard(wanted)
        assert (ROOT / path).read_bytes() == wanted, \
            f'Inherited source/workflow/pin/contract/auditor changed: {path}'
    codes = {name: '\n'.join(strip_comments((ROOT / (PREFIX + name)).read_text()))
             for name in MODULES}
    forbidden = re.compile(r'\b(sorry|admit|sorryAx|native_decide|axiom|opaque)\b|\bdecide!')
    for name, code in codes.items():
        assert not forbidden.search(code), (name, 'Forbidden proof token')
        assert '[I.Boundaryless]' not in code and 'ModelWithCorners.Boundaryless' not in code, name
        assert 'BoundarylessManifold I M' in code, name
        assert 'intrinsicLocalExistenceUniquenessFamily_pointFour' not in code, name
        assert 'instance' not in code or 'I.Boundaryless' not in code, name
    coeff = codes[MODULES[0]]
    assert 'PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target' in coeff
    assert 'fderivWithin_of_mem_nhds' in coeff and 'mfderivWithin_of_mem_nhds' in coeff
    assert 'contMDiffOn_localFrameGramMatrix_inv' in coeff
    assert 'contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two' in coeff
    assert 'contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one' in coeff
    for n in ('Principal', 'First', 'Zero'):
        assert f'contDiffOn_localTensorHeat{n}Coefficient' in coeff
    loc = codes[MODULES[1]]
    assert 'RicciFlow.AnalyticPDE.ManifoldBoundaryless.contDiffOn_actualTensorHeatCoefficients' in loc
    assert 'exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace' in loc
    assert 'FieldsAgreeOnUnitBall' in loc and 'initialTraceL' in loc
    prod = codes[MODULES[2]]
    assert '(g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)' in prod
    assert '[RiemannianBundle' not in prod, 'No ambient metric input'
    assert '[ContMDiffCovariantDerivative' not in prod, 'No supplied connection regularity'
    assert '[ContMDiffVectorBundle' not in prod, 'Derive tangent regularity'
    assert 'ContMDiffVectorBundle.of_le (n := ∞)' in prod
    assert 'exists_contMDiffAffineConnection_two' in prod
    for n in ('covariantTwoTensor_two', 'covariantThreeTensor_one'):
        assert f'contMDiffCovariantDerivative_{n}' in prod
    assert 'RicciFlow.AnalyticPDE.ManifoldBoundaryless.contDiffOn_actualTensorHeatCoefficients' in prod
    assert 'RicciFlow.AnalyticPDE.ManifoldBoundaryless.exists_radius_actualLocalTensorHeatUnitBall_zeroTrace' in prod
    assert 'g₀.toRiemannianMetric' in prod
    assert prod.index('letI : RiemannianBundle TM') < prod.index('letI : ∀ x : M, NormedAddCommGroup (T₃ x)')
    # The imported historical analytic inverse has no global-model assumption.
    original_loc = git(repo, 'show', f'{BASE}:{PREFIX}TensorHeatCoefficientLocalization.lean').decode()
    analytic = original_loc.split('theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace', 1)[1].split('/-- Local right-invertibility', 1)[0]
    assert 'I.Boundaryless' not in analytic
    historical = git(repo, 'show', f'{HISTORICAL_PRODUCER}:{PREFIX}TensorHeatFixedBackgroundProducer.lean').decode()
    assert '[I.Boundaryless]' in historical, 'Historical stronger restriction must stay explicit'
    metadata = (ROOT / 'docs/point4/manifold-only-fixed-background-heat/formalization.yaml').read_text()
    for sha in (BASE, HISTORICAL_PRODUCER):
        assert f'tree/{sha}/curvature' in metadata, sha
    assert 'relationship: "builds-on"' in metadata
    assert 'pending' in metadata and 'OPEN' in metadata
    return {'baseline': BASE, 'historical_producer': HISTORICAL_PRODUCER,
            'inherited_files_unchanged': len(inherited) - 1,
            'exact_inherited_guard_adapters': 1,
            'module_sha256': {n: hashlib.sha256((ROOT / (PREFIX + n)).read_bytes()).hexdigest() for n in MODULES},
            'lean_verified': False, 'point4': 'OPEN'}


def check_probe(output: str) -> None:
    expected = set(re.findall(r'^#print axioms (\S+)', (ROOT / PROBE).read_text(), re.M))
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    actual = [n for n, _ in entries] + clean
    assert set(actual) == expected and len(actual) == len(expected), 'Missing/duplicate axiom surfaces'
    for name, axioms in entries:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= \
            {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    assert output.count('MANIFOLD_HEAT_TYPES_BEGIN') == 1
    assert output.count('MANIFOLD_HEAT_TYPES_END') == 1
    types = output.split('MANIFOLD_HEAT_TYPES_BEGIN')[1].split('MANIFOLD_HEAT_TYPES_END')[0]
    assert types.count('BoundarylessManifold') == 4, types
    assert 'ModelWithCorners.Boundaryless' not in types and 'I.Boundaryless' not in types, types


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-repo', type=pathlib.Path, default=ROOT)
    parser.add_argument('--probe-log', type=pathlib.Path)
    args = parser.parse_args()
    report = check_sources(args.baseline_repo)
    if args.probe_log:
        check_probe(args.probe_log.read_text())
        report['probe_evidence_passed'] = True
    print(json.dumps(report, indent=2))
    print('Source/provenance checks passed; exact Lean 4.33 compilation, full build and independent review are separate gates')


if __name__ == '__main__':
    main()
