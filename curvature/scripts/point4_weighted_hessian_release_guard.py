#!/usr/bin/env python3
"""Exact reviewed weighted-Hessian source union. Source checks are not Lean verification."""
from __future__ import annotations
import argparse
import functools
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = '3a8ed697d1f0366f8370efb2fa9e524b68d27e97'
PREFIX = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/'
DOSSIER = 'docs/point4/weighted-duhamel-hessian/'
PROBE = 'curvature/scripts/point4_weighted_hessian_probe.lean'
WORKFLOW = '.github/workflows/point4-weighted-duhamel-hessian.yml'
MODULE = PREFIX + 'WeightedTimeKernel.lean'
METADATA = DOSSIER + 'formalization.yaml'
SELF_PATHS = {'curvature/scripts/point4_weighted_hessian_release_guard.py',
              'curvature/scripts/point4_weighted_hessian_release_mock_test.py'}
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
UNIT_FILE_SHA256 = {'docs/point4/weighted-duhamel-hessian.md': '699e456ad542d5096e7c67c3c8c40f911a200cee75bc33719122bb532035cadb', 'docs/point4/weighted-duhamel-hessian/inventory-adapters.json': '125156cbbdbfc582538fc70bfd3f6d140ad1140f46776659459a96de25e776dd', 'docs/point4/weighted-duhamel-hessian/runtime-inventory-source.json': '9c633da8d90fa63c7c1003c07bb340dd15bf76c651a9ed262b71d37fbc821800', 'docs/point4/weighted-duhamel-hessian/trace-review-history.json': '7eba118db43ed0d1c1057e47b0eafb8b9d3c96a5b473dc67e38375a998b22c7d', 'docs/point4/weighted-duhamel-hessian/reviewed-integral-source-review.md': 'f32c71416b00829393b59edce8915c2f9634f09b4de5c253dfca8d7cfece8702', 'docs/point4/weighted-duhamel-hessian/formalization.yaml': 'c5c7fa014e968c1d132927724d4e1f0b85e587d5fcab63a5546b6f99cfe425d2', 'docs/point4/weighted-duhamel-hessian/evidence-inventory.json': 'aa57b4d1cc3a7ee85e99446d5c906ed660232dae7ebb0e300929a0d4a3d49475', 'docs/point4/weighted-duhamel-hessian/declaration-surfaces.json': 'f4326629fa2e0e801823d9b3a2c2151ec67bc27ff0bc0017990628d8060c20ef', 'docs/point4/weighted-duhamel-hessian/reviewed-derivative-source-review.md': 'aa820cf617e9818a4ff93578e6f0a39ac18a9c1fa69e9733f714abf3c91b80c2', 'docs/point4/weighted-duhamel-hessian/reviewed-time-kernel-source-review.md': '827202e49c58d308daec6f2891a8cf3c34a4c9c986c1f1685bf6715a7ee5f277', 'docs/point4/weighted-duhamel-hessian/source-transformations.json': '712fcdb83587cfccbf9080b52f39445a4b8932dfb4835d0d57cce520a99c926c', 'docs/point4/weighted-duhamel-hessian/reviewed-regularizer-source-review.md': 'e8d1e766e147898b8bcce00e97ec4065e7ad4f122da80c2b2250bc6add7b02fc', 'docs/point4/weighted-duhamel-hessian/reviewed-trace-source-review.md': 'ec6e7c034511c2d1d8da976265a2f1cdb0fcf1bd6992789d2efb151952371536', 'docs/point4/weighted-duhamel-hessian/reviewed-source/EuclideanHeatRegularizerC2Trace.lean.txt': 'ca8598bd4eddf118a7bf2afa097e232cd872e8ffc7f3b2b9fe76bdf913531f44', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelIntegrand.lean.txt': '77da0c8aaad5fc44aae5dfd9bb9958da90528112d93eedba7082647f64d4a577', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedTimeKernel.lean.txt': '20ceba4efe5d3c2d0d302220e94db8394496be16ee336382c4d1049b470fc3a5', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelHessianIntegral.lean.txt': '84ff76aeee604c8824d2daa226f2b876d6146b14e5a292f37f18693c4c9fd8f2', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelHessianDerivative.lean.txt': '19e8ec44954e3c1ad6b75042465a2251de48124ab0ea923a1b90dd24e422a381', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelHessianFrechetTrace.lean.txt': '3af628927dd651ea247f07159243a8dd100267bdabcaabb06fb9263882ff7b08', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelFrechet.lean.txt': 'a817cc34a6be25422e6bef2f30faaba65aaccea706b0204eab671b5e9b02c900', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedDuhamelHessianTrace.lean.txt': '64f8f5bc8cfd468fe9b46b60be39c5686dec4b870b481b766403d9e52cda9d33', 'docs/point4/weighted-duhamel-hessian/reviewed-source/WeightedHessianTimeEnvelope.lean.txt': '4283e582912f8556266e2944e9453a2ed475522e8d4e95a5cba19ec39deb070d', 'curvature/scripts/point4_weighted_hessian_probe.lean': '9b5b14ea6d9289699e84d8d609af14c0adad074b41f1065b77b0131b8953adba', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatRegularizerC2Trace.lean': '688c4879791b4afd629eaf29ab2fcdf2d8821ed7ce255986ee225906fd9fd96b', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedTimeKernel.lean': '20ceba4efe5d3c2d0d302220e94db8394496be16ee336382c4d1049b470fc3a5', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelHessianTrace.lean': '026f7f603a567f54e3e55a36b8378400714c00b92c4f7346627303c53b8b449b', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelFrechet.lean': 'e88a56c21d0f04ab9a106a2f380be7cef982afb3a990a2ccbff7c6cd91fedd00', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelIntegrand.lean': 'f8d067d0bcf72973693e59ed0b8c6d0b716aa72e0f9a6baa9c4f3f023f9fd372', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelHessianDerivative.lean': 'b26e872c205995c466fb371b6a54e28e5df2ab646edb81b41dca84bca7dfadd6', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelHessianFrechetTrace.lean': 'd391d949ceec351ecb52c4c55d2a14d252eeb92e9d1009e047e6c50f5a9b8c7e', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedDuhamelHessianIntegral.lean': 'e87862d112c345e5a5ae18759962445c542777a6e81f2350be0f3558c4f584c5', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/WeightedHessianTimeEnvelope.lean': '120930e97935c4c86c0dd26aa2340aafde77bb33c8ba0002bbcd48b8c7365699', '.github/workflows/point4-weighted-duhamel-hessian.yml': '363baa9f3060cfaa5f5f462dfd0ccd6bc2e0cafca55e80c93464e82e0b1a72ef'}
TRANSFORM_SHA256 = '712fcdb83587cfccbf9080b52f39445a4b8932dfb4835d0d57cce520a99c926c'
ADAPTER_SHA256 = '125156cbbdbfc582538fc70bfd3f6d140ad1140f46776659459a96de25e776dd'
RUNTIME_INVENTORY_FRAGMENT_SHA256 = '41e5e5e853d8dd79ead807f76124d5bdaec723548493a4b6540b5de90515b6c2'

# Exact old primary workflow plus two reversible, independent Git checkpoints.
EXACT_HEAD_WORKFLOW_BASE = '24a0b6532304116ff25f1c793a4dbc6696251b9e'
EXACT_HEAD_WORKFLOW_PATH = '.github/workflows/point4-weighted-duhamel-hessian.yml'
EXACT_HEAD_WORKFLOW_JOB = 'weighted_hessian'
EXACT_HEAD_WORKFLOW_ORIGINAL_SHA256 = '3880cbee7ece768a2fbdf76003f9fd545a1c9029a8eb9991612cfa409a2906c9'
EXACT_HEAD_WORKFLOW_SHA256 = '363baa9f3060cfaa5f5f462dfd0ccd6bc2e0cafca55e80c93464e82e0b1a72ef'
EXACT_HEAD_BEFORE_ANCHOR = '      - name: Install pinned safe YAML parser from the official package registry\n'
EXACT_HEAD_AFTER_ANCHOR = '      - name: Preserve exact-head evidence\n'
EXACT_HEAD_PREFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness before candidate gates\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'
EXACT_HEAD_POSTFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness after candidate gates\n        if: always()\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'


def raw_git(*args: str) -> bytes:
    """Read the actual committed self objects without Git replacement refs."""
    return subprocess.check_output(['/usr/bin/git', '--no-replace-objects', '-C', str(ROOT), *args], env=ENV)


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def nul_records(output):
    assert not output or output.endswith(b'\0'), 'Git inventory must be NUL-terminated'
    records = output.split(b'\0')[:-1] if output else []
    assert all(records), 'Empty inventory record'
    return records

def nul_paths(output):
    paths = [record.decode() for record in nul_records(output)]
    assert len(paths) == len(set(paths)), 'Duplicate inventory path'
    return set(paths)

@functools.lru_cache(maxsize=1)
def baseline_sources():
    result = {}
    for record in nul_records(git('ls-tree', '-rz', BASE)):
        descriptor, name = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = name.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}
        assert path not in result
        result[path] = (mode, git('show', f'{BASE}:{path}'))
    assert len(result) == 1653, 'Historical source inventory changed'
    return result

def checked_json(path, digest):
    data = (ROOT / path).read_bytes()
    assert sha256(data) == digest, f'Exact reconstruction record changed: {path}'
    return json.loads(data)

def adapters():
    data = checked_json(DOSSIER + 'inventory-adapters.json', ADAPTER_SHA256)
    assert data['base'] == BASE
    return data['adapters']

def reconstruct_adapter(path, original):
    spec = adapters()[path]
    assert sha256(original) == spec['original_sha256'], 'Inherited adapter input changed'
    before, after = spec['before'].encode(), spec['after'].encode()
    assert spec['count'] == 1 and original.count(before) == 1 and after not in original
    result = original.replace(before, after, 1)
    assert sha256(result) == spec['transformed_sha256'], 'Inherited adapter result changed'
    assert result.count(after) == 1 and result.replace(after, before, 1) == original
    if 'startup_job' in spec:
        job = spec['startup_job']
        old = parse_workflow(original.decode())
        assert 'env' not in old and 'env' not in old['jobs'][job]
        wanted = json.loads(json.dumps(old))
        wanted['jobs'][job]['env'] = {'PYTHONDONTWRITEBYTECODE': '1'}
        assert parse_workflow(result.decode()) == wanted, 'Startup semantic remainder changed'
        env = b"    env:\n      PYTHONDONTWRITEBYTECODE: '1'\n"
        assert result.count(env) == 1 and result.replace(env,b'',1) == original
    return result

def source_transformations():
    data = checked_json(DOSSIER + 'source-transformations.json', TRANSFORM_SHA256)
    assert data['base'] == BASE and data['point4'] == 'OPEN'
    return data['modules']

# These exact additional edits repair two observed modern/legacy import errors.
# They apply only to the new reviewed helper and regularizer, never inherited source.
MODULE_COMPATIBILITY_EDITS = {
    PREFIX + 'WeightedDuhamelIntegrand.lean': (
        ('import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessian\n'
         'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedHessianTimeEnvelope\n',
         'module\n\n'
         'public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessian\n'
         'public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedHessianTimeEnvelope\n'),
        ('\nnoncomputable section\n', '\n@[expose] public noncomputable section\n'),
    ),
    PREFIX + 'EuclideanHeatRegularizerC2Trace.lean': (
        ('public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace\n',
         'public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatFrechet\n'
         'public import PoincareCurvature.Analysis.FiniteMomentApproximation\n'
         'public import Mathlib.Topology.UniformSpace.UniformConvergence\n'),
    ),
}

# Exactly three count-one proof repairs address the actual 24a0 compiler errors.
# No declaration header, definition, hypothesis, bound, or other module is changed.
REGULARIZER_PROOF_REPAIR_BASE = '24a0b6532304116ff25f1c793a4dbc6696251b9e'
REGULARIZER_PROOF_REPAIR_SHA256 = '177fdfdf992c95c77f8211f331379f92b58163764d91a8bd48678640715870b5'
REGULARIZER_PROOF_ONLY_EDITS = {
    PREFIX + 'EuclideanHeatRegularizerC2Trace.lean': (
        ('    simp only [heatHessianMajorantFirstMoment, if_pos rfl]\n',
         '    simp only [heatHessianMajorantFirstMoment, ↓reduceIte]\n'),
        ('    simpa only [M, mul_add] using\n      (integrable_abs_coord_mul_heatHessianMajorantND hh ell j).add\n        (integrable_abs_coord_mul_heatHessianMajorantND hh ell k)\n',
         '    have hsum : Integrable (fun z : Fin n → ℝ =>\n        |z ell| * heatHessianMajorantND h z j +\n          |z ell| * heatHessianMajorantND h z k)\n        (volume : Measure (Fin n → ℝ)) :=\n      (integrable_abs_coord_mul_heatHessianMajorantND hh ell j).fun_add\n        (integrable_abs_coord_mul_heatHessianMajorantND hh ell k)\n    exact hsum.congr (Eventually.of_forall fun z => by\n      dsimp only [M]\n      rw [mul_add])\n'),
        ('      time_mul_integral_abs_coord_heatHessianMajorantND hh ell j,\n      time_mul_integral_abs_coord_heatHessianMajorantND hh ell k]\n    ring\n  have htransWi : ∀ ell : Fin n,\n',
         '      time_mul_integral_abs_coord_heatHessianMajorantND hh ell j,\n      time_mul_integral_abs_coord_heatHessianMajorantND hh ell k]\n  have htransWi : ∀ ell : Fin n,\n'),
    ),
}

def reconstruct_module(path, original):
    spec = source_transformations()[path]
    assert sha256(original) == spec['original_sha256'], 'Reviewed module input changed'
    source = original
    compatibility = MODULE_COMPATIBILITY_EDITS.get(path, ())
    proof_edits = REGULARIZER_PROOF_ONLY_EDITS.get(path, ())
    seen_compatibility, seen_proof_edits = [], []
    for edit in spec['transformations']:
        before, after = edit['before'].encode(), edit['after'].encode()
        assert edit['count'] == 1 and source.count(before) == 1 and after not in source
        pair = (edit['before'], edit['after'])
        if pair in proof_edits:
            if not seen_proof_edits:
                assert spec['pre_proof_repair_commit'] == REGULARIZER_PROOF_REPAIR_BASE
                assert spec['pre_proof_repair_sha256'] == REGULARIZER_PROOF_REPAIR_SHA256
                assert sha256(source) == REGULARIZER_PROOF_REPAIR_SHA256, 'Proof repair input must be exact 24a0 bytes'
            seen_proof_edits.append(pair)
        elif pair in compatibility:
            seen_compatibility.append(pair)
        else:
            assert re.fullmatch(rb'(?:public )?import \S+\n', before)
            assert re.fullmatch(rb'(?:public )?import \S+\n', after)
            assert before.startswith(b'public ') == after.startswith(b'public '), 'Unrecorded visibility normalization forbidden'
        source = source.replace(before, after, 1)
    assert tuple(seen_compatibility) == compatibility, 'Exact module compatibility edits required'
    assert tuple(seen_proof_edits) == proof_edits, 'Exactly the three ordered proof repairs required'
    assert sha256(source) == spec['integrated_sha256'], 'Integrated module result changed'
    # Reverse the three exact proof edits to the immutable failed 24a0 input,
    # then reverse only the helper preamble before comparing every remaining byte.
    mathematical_source = source
    for before, after in reversed(proof_edits):
        assert mathematical_source.count(after.encode()) == 1, 'Non-unique proof repair output'
        mathematical_source = mathematical_source.replace(after.encode(), before.encode(), 1)
    if proof_edits:
        assert sha256(mathematical_source) == REGULARIZER_PROOF_REPAIR_SHA256
        assert mathematical_source == git('show', f'{REGULARIZER_PROOF_REPAIR_BASE}:{path}'), 'Historical 24a0 proof bytes changed'
    if path == PREFIX + 'WeightedDuhamelIntegrand.lean':
        for before, after in reversed(compatibility):
            mathematical_source = mathematical_source.replace(after.encode(), before.encode(), 1)
    erase = lambda data: re.sub(rb'^(?:public )?import \S+\n', b'', data, flags=re.M)
    assert erase(mathematical_source) == erase(original), 'Mathematical module byte drift'
    return source

def check_module_import_graph(sources=None):
    """Traverse real project sources; inspect every reachable project import edge.

    Mathlib/Lean external imports remain exact-toolchain verification obligations.
    The source union binds project sources independently of this graph check.
    """
    from point4_scan import strip_comments
    visited, visiting, edges, external = set(), set(), set(), set()
    def read(path):
        return (ROOT/path).read_text() if sources is None else sources[path].decode()
    def visit(path):
        assert path not in visiting, f'Project import cycle: {path}'
        if path in visited:
            return
        code = '\n'.join(strip_comments(read(path)))
        assert re.search(r'^module\s*$', code, re.M), f'Reachable non-module project import: {path}'
        visiting.add(path)
        for line in code.splitlines():
            match = re.fullmatch(r'\s*(public )?import (\S+)\s*', line)
            if not match:
                continue
            assert match[1], f'Non-public project graph import: {path}: {line.strip()}'
            name = match[2]
            if name.startswith('PoincareCurvature.'):
                target = 'curvature/' + name.replace('.', '/') + '.lean'
                assert target in public_paths(), f'Project import outside exact source union: {target}'
                edges.add((path, target))
                visit(target)
            else:
                external.add(name)
        visiting.remove(path)
        visited.add(path)
    for path in source_transformations():
        visit(path)
    return {'project_modules': len(visited), 'project_import_edges': len(edges),
            'external_import_modules': len(external), 'project_legacy_imports': 0}

def expected_sources():
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {p:(BASE,data) for p,(_,data) in baseline.items()}
    for path in adapters():
        expected[path] = (BASE, reconstruct_adapter(path, baseline[path][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline)
    for path, digest in UNIT_FILE_SHA256.items():
        data = (ROOT/path).read_bytes()
        assert sha256(data) == digest, f'New exact release blob changed: {path}'
        expected[path] = (BASE,data)
    for path, spec in source_transformations().items():
        assert path in expected and path not in baseline
        original = (ROOT/spec['original_path']).read_bytes()
        assert expected[path][1] == reconstruct_module(path, original)
    check_inventory()
    check_release_self_sources()
    restored_exact_head_workflow((ROOT / EXACT_HEAD_WORKFLOW_PATH).read_bytes())
    return expected

def public_paths():
    return set(baseline_sources()) | set(UNIT_FILE_SHA256) | SELF_PATHS


def check_release_self_sources() -> None:
    """Bind each reviewed self file to stage-zero index and committed HEAD.

    A source-only development tree can be staged, but it is not an exact-head
    release until the reviewed files are committed. No self digest is recursive.
    """
    paths = sorted(SELF_PATHS)
    head = {}
    for record in nul_records(raw_git('ls-tree', '-rz', 'HEAD', '--', *paths)):
        descriptor, name = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = name.decode()
        assert path in SELF_PATHS and path not in head, 'Committed self inventory drift'
        assert kind == 'blob' and mode == '100644' and re.fullmatch(r'[0-9a-f]{40}', oid), 'Committed self blob/mode drift'
        head[path] = (mode, oid)
    assert set(head) == SELF_PATHS, 'Missing committed self source'
    index = {}
    for record in nul_records(raw_git('ls-files', '--stage', '-z', '--', *paths)):
        descriptor, name = record.split(b'\t', 1)
        mode, oid, stage = descriptor.decode().split()
        path = name.decode()
        assert path in SELF_PATHS and path not in index and stage == '0', 'Unmerged/missing self index source'
        assert re.fullmatch(r'[0-9a-f]{40}', oid), 'Self index blob identity drift'
        index[path] = (mode, oid)
    assert index == head, 'Self index/committed HEAD blob or mode mismatch'
    for path, (mode, oid) in head.items():
        actual = ROOT / path
        physical = actual.lstat().st_mode
        assert stat.S_ISREG(physical) and not physical & 0o111, 'Self physical file/mode drift'
        data = actual.read_bytes()
        identity = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert identity == oid, 'Self physical/committed HEAD blob mismatch: ' + path



def adapted_exact_head_workflow(original: bytes) -> bytes:
    """Insert two independent checkpoints; every original byte stays exact."""
    assert sha256(original) == EXACT_HEAD_WORKFLOW_ORIGINAL_SHA256, 'Original primary workflow digest drift'
    source = original.decode()
    assert source.count(EXACT_HEAD_BEFORE_ANCHOR) == 1 and source.count(EXACT_HEAD_AFTER_ANCHOR) == 1, 'Primary workflow checkpoint anchor count drift'
    assert EXACT_HEAD_PREFLIGHT not in source and EXACT_HEAD_POSTFLIGHT not in source, 'Primary workflow checkpoints already present'
    adapted = source.replace(EXACT_HEAD_BEFORE_ANCHOR, EXACT_HEAD_PREFLIGHT + EXACT_HEAD_BEFORE_ANCHOR, 1)
    adapted = adapted.replace(EXACT_HEAD_AFTER_ANCHOR, EXACT_HEAD_POSTFLIGHT + EXACT_HEAD_AFTER_ANCHOR, 1)
    before = parse_workflow(source)
    after = parse_workflow(adapted)
    steps = after['jobs'][EXACT_HEAD_WORKFLOW_JOB]['steps']
    assert len(steps) == len(before['jobs'][EXACT_HEAD_WORKFLOW_JOB]['steps']) + 2, 'Primary workflow checkpoint count drift'
    assert steps.pop(-2) == parse_workflow('steps:\n' + EXACT_HEAD_POSTFLIGHT)['steps'][0], 'Post-gate exact-head checkpoint drift'
    assert steps.pop(1) == parse_workflow('steps:\n' + EXACT_HEAD_PREFLIGHT)['steps'][0], 'Pre-gate exact-head checkpoint drift'
    assert after == before, 'Original primary workflow semantics changed'
    assert adapted.count(EXACT_HEAD_PREFLIGHT) == adapted.count(EXACT_HEAD_POSTFLIGHT) == 1, 'Duplicate exact-head checkpoint'
    assert adapted.replace(EXACT_HEAD_PREFLIGHT, '', 1).replace(EXACT_HEAD_POSTFLIGHT, '', 1).encode() == original, 'Original primary workflow bytes changed'
    assert sha256(adapted.encode()) == EXACT_HEAD_WORKFLOW_SHA256, 'Adapted primary workflow digest drift'
    return adapted.encode()


def restored_exact_head_workflow(actual: bytes) -> bytes:
    original = git('show', EXACT_HEAD_WORKFLOW_BASE + ':' + EXACT_HEAD_WORKFLOW_PATH)
    expected = adapted_exact_head_workflow(original)
    assert parse_workflow(actual.decode()) == parse_workflow(expected.decode()), 'Primary workflow exact-head semantic drift'
    assert actual == expected, 'Primary workflow exact-head bytes changed'
    restored = actual.decode().replace(EXACT_HEAD_PREFLIGHT, '', 1).replace(EXACT_HEAD_POSTFLIGHT, '', 1).encode()
    assert restored == original, 'Primary workflow original remainder changed'
    return restored


LAKE_ROOTS = ('curvature/.lake', 'hamilton-ivey-reaction/.lake')
MANIFESTS = ('curvature/lake-manifest.json', 'hamilton-ivey-reaction/lake-manifest.json')
# The pinned ProofWidgets widgetPackageLock target uses Lake's text-file hash.
# Lake 4.33 writes exactly 16 lowercase hex bytes beside this tracked input.
# This is one fixed sidecar, never a package-wide or arbitrary .hash exemption.
PROOFWIDGETS_REV = '4be2e3d5087eeb272cf5a8853b8f9dd025ef5957'
PROOFWIDGETS_LOCK = 'curvature/.lake/packages/proofwidgets/widget/package-lock.json'
PROOFWIDGETS_LOCK_BLOB = '06d5baf2fae78fed1fdae485f4c2c054a0bccfb2'
PROOFWIDGETS_LOCK_SIZE = 172140
PROOFWIDGETS_FINGERPRINT = PROOFWIDGETS_LOCK + '.hash'
# Source-derived for the pinned Linux/little-endian Lean 4.33 text hash;
# this is not a compiler/runtime qualification claim. See release integration.
PROOFWIDGETS_LOCK_HASH = b'179e66574f04806e'
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


def runtime_fingerprints(dependencies: set[str]) -> set[str]:
    path = ROOT / PROOFWIDGETS_FINGERPRINT
    if not path.exists() and not path.is_symlink():
        return set()
    # Require the unchanged manifest entry, verified package HEAD and full
    # dependency inventory before reading the fixed regular source and sidecar.
    manifest = json.loads(baseline_sources()['curvature/lake-manifest.json'][1])
    assert manifest['packagesDir'] == '.lake/packages', 'Fingerprint dependency layout drift'
    packages = [p for p in manifest['packages'] if p['name'] == 'proofwidgets']
    assert len(packages) == 1, 'Fingerprint package identity drift'
    package = packages[0]
    assert (package['type'], package['url'], package['rev']) == (
        'git', 'https://github.com/leanprover-community/ProofWidgets4', PROOFWIDGETS_REV), 'Fingerprint package pin drift'
    assert PROOFWIDGETS_LOCK in dependencies, 'Fingerprint parent is not a verified dependency source'
    package_dir = ROOT / 'curvature/.lake/packages/proofwidgets'
    assert git_at(package_dir, 'rev-parse', 'HEAD').decode().strip() == PROOFWIDGETS_REV, 'Fingerprint dependency HEAD drift'
    for parent in path.parents:
        if parent == ROOT:
            break
        assert stat.S_ISDIR(parent.lstat().st_mode), f'Non-directory/symlink fingerprint parent: {parent}'
    source = ROOT / PROOFWIDGETS_LOCK
    check_mode(PROOFWIDGETS_LOCK, source.lstat().st_mode, '100644')
    assert source.stat().st_size == PROOFWIDGETS_LOCK_SIZE, 'Fingerprint source size drift'
    assert git_blob_identity(source.read_bytes()) == PROOFWIDGETS_LOCK_BLOB, 'Fingerprint source blob drift'
    check_mode(PROOFWIDGETS_FINGERPRINT, path.lstat().st_mode, '100644')
    assert path.stat().st_size == 16, 'Fingerprint must be exactly 16 bytes'
    with path.open('rb') as stream:
        fingerprint = stream.read(17)
    assert re.fullmatch(rb'[0-9a-f]{16}', fingerprint), 'Noncanonical Lake fingerprint'
    assert fingerprint == PROOFWIDGETS_LOCK_HASH, 'Pinned input fingerprint mismatch'
    return {PROOFWIDGETS_FINGERPRINT}


def check_inventory_sets(tracked: set[str], untracked: set[str], physical: set[str], dependencies: set[str] | None = None, git_roots: set[str] | None = None, fingerprints: set[str] | None = None) -> None:
    assert not tracked & untracked, 'Overlapping tracked/untracked inventory'
    assert set(baseline_sources()) <= tracked, 'Inherited source must stay tracked'
    assert not any(runtime_path(path) for path in tracked), 'Tracked Lake cache forbidden'
    dependencies, git_roots = dependencies or set(), git_roots or set()
    fingerprints = fingerprints or set()
    assert fingerprints <= {PROOFWIDGETS_FINGERPRINT}, 'Unapproved runtime fingerprint path'
    def runtime_file(path):
        # Git reports an untracked nested repository as one trailing-slash
        # directory record. Its pinned source inventory was validated separately.
        return path in dependencies or path in fingerprints or generated_build_path(path) or any(
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
    fingerprints = runtime_fingerprints(dependencies)
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
            if path in fingerprints or generated_build_path(path):
                assert stat.S_ISREG((ROOT / path).lstat().st_mode), f'Non-regular runtime file: {path}'
            else:
                physical.add(path)
    check_inventory_sets(set(tracked_modes), untracked, physical, dependencies, git_roots, fingerprints)
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


def parse_workflow(source):
    import yaml
    class StrictLoader(yaml.BaseLoader):
        def construct_mapping(self, node, deep=False):
            result = {}
            for key_node, value_node in node.value:
                key = self.construct_object(key_node, deep=deep)
                assert isinstance(key, str) and key not in result, f'Duplicate/non-string YAML key: {key}'
                result[key] = self.construct_object(value_node, deep=deep)
            return result
    result = yaml.load(source, Loader=StrictLoader)
    assert isinstance(result, dict)
    return result

def historical_c2():
    # Load the unchanged strict metadata/evidence helpers under a distinct name.
    # Its original inventory adapter may import the current release module, but
    # its parser, theorem evidence, contract, and audit functions are unchanged.
    path = ROOT / 'curvature/scripts/point4_c2_initial_heat_source_test.py'
    spec = importlib.util.spec_from_file_location('_weighted_hessian_c2_helpers', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def check_metadata(source, schema=None):
    helper = historical_c2()
    data = helper.parse_metadata(source)
    entries = helper.metadata_entries(source)
    wanted = {
      f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
      'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis',
      'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory',
    }
    assert set(entries) == wanted and all(v[0] == 'builds-on' for v in entries.values())
    assert data['status']['main_results'] == [] and 'OPEN' in data['status']['scope']
    assert data['review']['status'] == 'pending', 'Exact integrated review remains pending'
    assert sha256(source.encode()) == UNIT_FILE_SHA256[METADATA]
    if schema:
        import jsonschema
        raw = pathlib.Path(schema).read_bytes()
        assert sha256(raw) == helper.SCHEMA_SHA256
        jsonschema.validate(data, json.loads(raw))

def check_current(schema=None):
    source = (ROOT / 'curvature/scripts/point4_weighted_hessian_release_guard.py').read_text()
    fragment = source[source.index("LAKE_ROOTS ="):source.index('def parse_workflow')]
    assert sha256(fragment.encode()) == RUNTIME_INVENTORY_FRAGMENT_SHA256, 'Reviewed runtime inventory fragment changed'
    expected = expected_sources()
    for path,(_,data) in expected.items():
        assert (ROOT/path).read_bytes() == data, f'Exact inherited source changed: {path}'
    check_inventory()
    check_physical_lean({p for p in public_paths() if p.endswith('.lean')})
    helper = historical_c2()
    helper.check_imports((ROOT/helper.LIBROOT).read_bytes())
    helper.check_metadata((ROOT/helper.METADATA).read_text())
    check_metadata((ROOT/METADATA).read_text(), schema)
    workflow = (ROOT/WORKFLOW).read_text()
    parse_workflow(workflow)
    assert sha256(workflow.encode()) == UNIT_FILE_SHA256[WORKFLOW]
    from point4_scan import strip_comments
    for path in source_transformations():
        code = '\n'.join(strip_comments((ROOT/path).read_text()))
        assert not re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|opaque|native_decide)\b|\bdecide!', code)
        assert 'I.Boundaryless' not in code and 'intrinsicLocalExistenceUniquenessFamily_pointFour' not in code
    module_graph = check_module_import_graph()
    regression = (ROOT/'curvature/scripts/point4_closed_contract_regression.lean').read_text()
    assert regression.count('fail_if_success exact @bad') == 12
    return {'base':BASE, 'public_paths':len(public_paths()), 'inherited_byte_identical':1653-len(adapters()),
            'count_one_entrypoint_adapters':sum(p.endswith('.py') for p in adapters()),
            'count_one_startup_workflow_adapters':sum(p.endswith('.yml') for p in adapters()), 'new_modules':len(source_transformations()),
            'module_import_graph':module_graph,
            'root_imports_and_all_pins_unchanged':True, 'lean_verified':False, 'point4':'OPEN'}

def check_historical_reconstruction(target):
    run = lambda *args: subprocess.check_output(['git','-C',str(target),*args],env=ENV)
    assert run('rev-parse','HEAD').decode().strip() == BASE, 'Historical HEAD drift'
    assert run('write-tree') == git('rev-parse',BASE+'^{tree}'), 'Historical index tree drift'
    wanted = {(mode+' '+git_blob_identity(data)+' 0\t'+path).encode()
              for path,(mode,data) in baseline_sources().items()}
    assert set(nul_records(run('ls-files','--stage','-z'))) == wanted, 'Historical complete index/blob/mode drift'
    for path,(mode,data) in baseline_sources().items():
        assert (target/path).read_bytes() == data, f'Historical source drift: {path}'
        check_mode(path,(target/path).lstat().st_mode,mode)

def historical_gate(path, argv):
    assert path in adapters() and path.endswith('.py'), 'Unapproved historical gate target'
    assert (ROOT/path).read_bytes() == reconstruct_adapter(path, baseline_sources()[path][1])
    # This is a real detached source reconstruction, not mocked functions or
    # filtered evidence. Its Git index, files, modes and exact HEAD are checked.
    with tempfile.TemporaryDirectory(prefix='point4-weighted-historical-') as parent:
        target = pathlib.Path(parent)/'source'
        subprocess.run(['git','-C',str(ROOT),'worktree','add','--detach',str(target),BASE], check=True, env=ENV, stdout=subprocess.DEVNULL)
        try:
            check_historical_reconstruction(target)
            subprocess.run([sys.executable,str(target/path),*argv], cwd=target, check=True, env=ENV)
            assert not subprocess.check_output(['git','-C',str(target),'status','--porcelain','--untracked-files=all'],env=ENV), 'Historical gate mutated reconstruction'
            check_historical_reconstruction(target)
        finally:
            subprocess.run(['git','-C',str(ROOT),'worktree','remove',str(target)],check=True,env=ENV)

def run_inherited(path, argv=None):
    args = list(sys.argv[1:] if argv is None else argv)
    schema = args[args.index('--schema')+1] if '--schema' in args else None
    check_current(schema)
    historical_gate(path,args)
    check_current(schema)
    print('Exact original historical gate replayed; current physical/source union independently passed; Point 4 OPEN')

def check_probe(output):
    helper = historical_c2()
    source = (ROOT/PROBE).read_text()
    names = helper.check_axiom_output(source, output)
    assert len(names) == 74, 'New axiom surface drift'
    assert output.count('WEIGHTED_HESSIAN_TYPES_BEGIN') == 1 and output.count('WEIGHTED_HESSIAN_TYPES_END') == 1
    types = output.split('WEIGHTED_HESSIAN_TYPES_BEGIN')[1].split('WEIGHTED_HESSIAN_TYPES_END')[0]
    for name in helper.probe_names(source):
        assert types.count(name) >= 1, f'Missing complete theorem type: {name}'
    for token in ('IntervalIntegrable','Continuous','BoundedContinuousFunction','Fin n','heatDuhamelHessianEntryND','heatHessianEntryHolderMoment','LittleWeightedSpatialHolder','Tendsto','fderiv','UniformContinuous'):
        assert token in types, f'Missing full type component: {token}'
    for token in ('sorryAx','I.Boundaryless','ModelWithCorners.Boundaryless','Nonempty (IntrinsicLocalSolution'):
        assert token not in types
    assert output.count('WEIGHTED_HESSIAN_RANK_ZERO_BEGIN') == 1 and output.count('WEIGHTED_HESSIAN_RANK_ZERO_END') == 1
    rank = output.split('WEIGHTED_HESSIAN_RANK_ZERO_BEGIN')[1].split('WEIGHTED_HESSIAN_RANK_ZERO_END')[0]
    assert 'Fin 0' in rank
    rank_names = re.findall(r'^#check @(\S+) 0$', source, re.M)
    assert len(rank_names) == 8 and len(set(rank_names)) == 8, 'Exact zero-rank probe inventory drift'
    for name in rank_names:
        assert name.rsplit('.',1)[-1] in rank, f'Missing actual zero-rank specialization: {name}'
    assert not re.search(r'(^|\n).*error:', output), 'Compiler errors cannot count as evidence'

def check_compile_receipt(output, sha):
    modules = [path.removeprefix('curvature/').removesuffix('.lean').replace('/','.') for path in source_transformations()]
    wanted = 'WEIGHTED_HESSIAN_COMPILED ' + sha + ' ' + ' '.join(modules)
    assert output.splitlines()[-1] == wanted, 'All new compilation targets must precede probe'
    assert output.count(wanted) == 1

def check_evidence_inventory(directory):
    assert directory.is_dir() and not directory.is_symlink(), 'Non-directory/symlinked evidence root'
    paths = list(directory.rglob('*'))
    assert not any(p.is_symlink() for p in paths), 'Symlinked evidence forbidden'
    actual = {p.relative_to(directory).as_posix() for p in paths if p.is_file()}
    assert actual == EVIDENCE_PATHS, ('Missing/extra exact evidence inventory', sorted(actual ^ EVIDENCE_PATHS))
    for path in paths:
        if path.is_file():
            assert stat.S_ISREG(path.lstat().st_mode), 'Non-regular evidence file'
        else:
            assert path.is_dir(), 'Unsupported evidence type'
    allowed_directories = {'inherited-probes'}
    assert {p.relative_to(directory).as_posix() for p in paths if p.is_dir()} == allowed_directories, 'Unexplained/empty evidence directory'

def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema',type=pathlib.Path)
    parser.add_argument('--probe-log',type=pathlib.Path)
    parser.add_argument('--compile-log',type=pathlib.Path)
    parser.add_argument('--axiom-dir',type=pathlib.Path)
    parser.add_argument('--audit-json',type=pathlib.Path)
    parser.add_argument('--audit-rc',type=int)
    parser.add_argument('--evidence-dir',type=pathlib.Path)
    args = parser.parse_args(argv)
    if args.evidence_dir:
        assert args.schema and args.probe_log and args.compile_log and args.axiom_dir and args.audit_json and args.audit_rc is not None
        check_evidence_inventory(args.evidence_dir)
        for value,name in ((args.schema,'official-schema.json'),(args.compile_log,'compile.log'),
                           (args.probe_log,'probe.log'),(args.axiom_dir,'inherited-probes'),(args.audit_json,'audit.json')):
            assert value.resolve() == (args.evidence_dir/name).resolve(), 'Evidence argument/directory mismatch'
    report = check_current(args.schema)
    inherited = []
    for option,value in (('--schema',args.schema),('--axiom-dir',args.axiom_dir),('--audit-json',args.audit_json),('--audit-rc',args.audit_rc)):
        if value is not None: inherited.extend([option,str(value.resolve()) if isinstance(value,pathlib.Path) else str(value)])
    historical_gate('curvature/scripts/point4_manifold_heat_release_guard.py',inherited)
    if args.probe_log:
        assert args.compile_log, 'Actual probe requires prior mandatory compile receipt'
        check_compile_receipt(args.compile_log.read_text(),git('rev-parse','HEAD').decode().strip())
        check_probe(args.probe_log.read_text())
    assert args.probe_log or args.compile_log is None
    if args.evidence_dir:
        assert args.schema and args.probe_log and args.axiom_dir and args.audit_json and args.audit_rc is not None
        check_evidence_inventory(args.evidence_dir)
        for value,name in ((args.schema,'official-schema.json'),(args.compile_log,'compile.log'),
                           (args.probe_log,'probe.log'),(args.axiom_dir,'inherited-probes'),(args.audit_json,'audit.json')):
            assert value.resolve() == (args.evidence_dir/name).resolve(), 'Evidence argument/directory mismatch'
        head = git('rev-parse','HEAD').decode().strip()
        assert (args.evidence_dir/'sha.log').read_text() == head+'\n', 'Evidence SHA drift'
        for name in ('probe.log','manifold-probe.log','inherited-build.log','contract.log','regression.log'):
            assert not re.search(r'(^|\n).*error:',(args.evidence_dir/name).read_text()), f'Compiler errors in {name}'
        # PR131 adds eleven inherited surfaces and four complete types. Their
        # unchanged actual validator runs as well as the older 150/7 gate.
        historical_gate('curvature/scripts/point4_manifold_heat_release_guard.py',
                        ['--probe-log',str((args.evidence_dir/'manifold-probe.log').resolve())])

    check_current(args.schema)
    print(json.dumps(report,indent=2))
    print('Source-only integration checks passed; exact Lean compilation and current final review remain separate')

EVIDENCE_PATHS = {'inherited-probes/contraction.log', 'inherited-probes/chosen_lc_curvature.log', 'inherited-build.log', 'inherited-probes/weighted_initial_heat.log', 'sha.log', 'source.log', 'inherited-probes/weak_laplacian.log', 'inherited-probes/frozen_metric_principal.log', 'audit.json', 'inherited-probes/principal_remainder.log', 'inherited-probes/standard_coordinate_operator.log', 'audit.log', 'audit-build.log', 'inherited-probes/chosen_lc_coordinate.log', 'inherited-probes/boundaryless_chart_frames.log', 'probe.log', 'inherited-probes/c2_heat_trace.log', 'compile.log', 'inherited-probes/coordinate_connection.log', 'manifold-probe.log', 'regression.log', 'contract.log', 'inherited-probes/coordinate_operator.log', 'official-schema.json', 'inherited-probes/coordinate_jet.log'}

# Reviewed finite smooth/master composition; original validator bodies survive.
import hashlib as _composition_hashlib, pathlib as _composition_pathlib, stat as _composition_stat, sys as _composition_sys
_composition_file = _composition_pathlib.Path(__file__).resolve().parents[2] / 'curvature/scripts/point4_smooth_master_composition.py'
assert _composition_stat.S_ISREG(_composition_file.lstat().st_mode) and not _composition_file.lstat().st_mode & 0o111
assert _composition_hashlib.sha256(_composition_file.read_bytes()).hexdigest() == '82c4563228912fd4a45c63279e40959f7d9e8262e29338292f485c3226b45bd8', 'Composition executable binding changed'
_composition_sys.modules.setdefault('point4_weighted_hessian_release_guard', _composition_sys.modules[__name__])
import point4_smooth_master_composition as _smooth_master
_smooth_master.install_weighted(globals())

if __name__ == '__main__':
    main()
