#!/usr/bin/env python3
"""Immutable parent-union source preflight; actual Lean gates remain mandatory."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
STACK = 'ba47fe1f4d8efad8bad68c61b4d25d0d8ff5387e'
FIX = 'f908454fac787a720239e04feee6d61a9f9ab202'
MASTER = '60b6f8ef9d37d1fc5fac1f6113584e1b16370016'
HISTORICAL = '591c25914c80366d619ece00da204997ee2a65d7'
NEW_MODULE = 'PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatWeightedInitialHolder'
NEW_PATH = 'curvature/' + NEW_MODULE.replace('.', '/') + '.lean'
NEW_SHA256 = 'a1ca6c80dabcc0f9df8d788870869bc0a5eff453752e8fef1379cc8a2d0dca23'
ROOT_PATH = 'curvature/PoincareCurvature.lean'
GUARD_PATH = 'curvature/scripts/point4_weighted_initial_heat_guard.py'
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)

def original(ref, path):
    return git('show', f'{ref}:{path}')

def tree(ref):
    result = {}
    for line in git('ls-tree', '-r', ref).decode().splitlines():
        info, path = line.split('\t', 1)
        mode, kind, digest = info.split()
        if kind == 'blob':
            result[path] = (mode, digest)
    return result

def blob_digest(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

# Require real immutable ancestry. In particular a copied old-baseline guard
# cannot silently qualify an unrelated candidate or omit the current contract.
assert git('show', '-s', '--format=%P', STACK).decode().split() == [HISTORICAL, MASTER]
for ref in (STACK, FIX, MASTER, HISTORICAL):
    git('merge-base', '--is-ancestor', ref, 'HEAD')
stack, fix, master = tree(STACK), tree(FIX), tree(MASTER)
proofs = {p: stack.get(p, fix.get(p)) for p in stack.keys() | fix.keys()
          if p.endswith('.lean') and p != ROOT_PATH}
for path in stack.keys() & fix.keys():
    if path in proofs:
        assert stack[path] == fix[path], ('Conflicting immutable proof parents', path)
for path, (mode, digest) in proofs.items():
    assert blob_digest((ROOT / path).read_bytes()) == digest, path

# Reject unknown/deleted tracked proof files throughout the repository and
# additional physical library files, not merely modifications to old files.
actual = {p for p in git('ls-files', '--cached', '--others', '--exclude-standard').decode().splitlines()
          if p.endswith('.lean') and p != ROOT_PATH}
actual |= {str(p.relative_to(ROOT)) for p in (ROOT / 'curvature/PoincareCurvature').rglob('*.lean')}
assert actual == set(proofs), ('Unexpected or missing Lean paths', sorted(actual ^ set(proofs)))

# Protect all inherited scripts/workflows, including current source fingerprints,
# negative-kernel fixtures and actual standard-operator probe/workflow. The only
# deliberate script change is this strengthened guard itself. The old auditor
# is replaced solely by the exact current canonical auditor, never weakened.
protected = {p for p in stack.keys() | fix.keys()
             if p.startswith(('.github/workflows/', 'curvature/scripts/')) and p != GUARD_PATH}
protected |= {'AGENTS.md', 'LICENSE', 'curvature/lean-toolchain', 'curvature/lake-manifest.json'}
for path in protected:
    ref = STACK if path in stack else FIX
    if path in stack and path in fix and stack[path] != fix[path]:
        assert path == 'curvature/scripts/point4_audit.sh', ('Unexpected protected parent conflict', path)
        assert stack[path] == master[path], path
    assert (ROOT / path).read_bytes() == original(ref, path), path

# Exactly one weighted public import is added to the immutable integrated root.
addition = ('import ' + NEW_MODULE + '\n').encode()
root_source = (ROOT / ROOT_PATH).read_bytes()
assert root_source.count(addition) == 1
assert root_source.replace(addition, b'') == original(STACK, ROOT_PATH)
assert (ROOT / NEW_PATH).read_bytes() == original(FIX, NEW_PATH)
assert hashlib.sha256((ROOT / NEW_PATH).read_bytes()).hexdigest() == NEW_SHA256

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

# Execute the exact byte-preserved current-master source invariant checker.
subprocess.check_call([sys.executable, str(ROOT / 'curvature/scripts/point4_closed_contract_source_test.py')], env=ENV)

# No downloads: supplied full official schema is a separate local/release gate.
if len(sys.argv) == 2:
    import jsonschema
    import yaml
    schema = json.loads(Path(sys.argv[1]).read_text())
    data = yaml.safe_load((ROOT / 'curvature/formalization.yaml').read_text())
    jsonschema.validate(data, schema)
    entries = data['related_formalizations']
    for ref in (STACK, MASTER, HISTORICAL):
        url = 'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/' + ref + '/curvature'
        assert any(e['id'] == url and e['relationship'] == 'builds-on' for e in entries), ref
    print('Full supplied official v0.4 schema and exact integrated stack provenance: PASS')

print(f'Immutable parent-union Lean proof blobs preserved: {len(proofs)}')
print(f'Integrated library Lean proof blobs preserved: {sum(p.startswith("curvature/PoincareCurvature/") for p in proofs)}')
print(f'Protected script/workflow/pin paths preserved: {len(protected)}')
print('Exact current canonical contract, negative fixtures, audit, inherited workflows and pins: PASS')
print('Unknown Lean proof paths rejected; exact repaired weighted proof SHA256:', NEW_SHA256)
print('Source-only preflight PASS; integrated head UNVERIFIED until actual Lean type/axiom/full-build gates and independent review pass')
