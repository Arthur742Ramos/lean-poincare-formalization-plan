#!/usr/bin/env python3
"""Read-only immutable-base/protected-source preflight, not a Lean build substitute."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
BASE = '591c25914c80366d619ece00da204997ee2a65d7'
NEW_MODULE = 'PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatWeightedInitialHolder'
NEW_PATH = 'curvature/' + NEW_MODULE.replace('.', '/') + '.lean'
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)

def original(path):
    return git('show', f'{BASE}:{path}')

# Every inherited proof file stays byte-identical, including the C² datum,
# canonical manifold scope, candidate classes and initial derivative contracts.
paths = git('ls-tree', '-r', '--name-only', BASE, 'curvature/PoincareCurvature').decode().splitlines()
for path in paths:
    if path.endswith('.lean'):
        assert (ROOT / path).read_bytes() == original(path), path

protected = [
    'AGENTS.md', 'LICENSE', 'curvature/lean-toolchain', 'curvature/lake-manifest.json',
    'curvature/scripts/point4_audit.sh', 'curvature/scripts/point4_scan.py',
    'curvature/scripts/point4_target.txt',
    'curvature/scripts/point4_c2_heat_trace_probe.lean',
    '.github/workflows/point4-c2-heat-trace.yml',
]
for path in protected:
    assert (ROOT / path).read_bytes() == original(path), path

root_path = 'curvature/PoincareCurvature.lean'
addition = ('import ' + NEW_MODULE + '\n').encode()
root_source = (ROOT / root_path).read_bytes()
assert root_source.count(addition) == 1
assert root_source.replace(addition, b'') == original(root_path)

sys.path.insert(0, str(ROOT / 'curvature/scripts'))
from point4_scan import strip_comments
code = '\n'.join(strip_comments((ROOT / NEW_PATH).read_text()))
assert not re.search(r'\b(sorry|admit|sorryAx|axiom|opaque|native_decide)\b|\bdecide!', code)
assert not re.search(r'\bstructure\s+EuclideanBoundedC2Data\b', code)
name = 'EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero'
signature = code.split('theorem ' + name, 1)[1].split(':=', 1)[0]
assert 'UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)' in signature
assert '{α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)' in signature
assert '(heatEvolvedWeightedC2AlphaData D ht hα.le hα1).hessianHolderConstant' in signature
for forbidden in ('IsHolderConst', 'HolderWith', 'Subsingleton', 'IsEmpty', 'finrank', 'hweighted'):
    assert forbidden not in signature, forbidden

# Full official cached schema validation is optional locally but required by
# the review/release preflight; no schema is downloaded by this guard.
if len(sys.argv) == 2:
    import jsonschema
    import yaml
    schema = json.loads(Path(sys.argv[1]).read_text())
    data = yaml.safe_load((ROOT / 'curvature/formalization.yaml').read_text())
    jsonschema.validate(data, schema)
    entries = data['related_formalizations']
    base_url = 'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/' + BASE + '/curvature'
    assert any(e['id'] == base_url and e['relationship'] == 'builds-on' for e in entries)
    print('Full supplied official v0.4 schema and exact stack provenance: PASS')

print(f'Inherited Lean proof blobs preserved: {sum(p.endswith(".lean") for p in paths)}')
print('Canonical contracts, initial C² data, audit, inherited workflow and toolchain pins: PASS')
print('New source signature/placeholder guard: PASS (compiled type and axiom gates still required)')
print('New proof SHA256:', hashlib.sha256((ROOT / NEW_PATH).read_bytes()).hexdigest())
