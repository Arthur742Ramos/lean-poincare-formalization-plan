#!/usr/bin/env python3
"""Exact two-sided heat release union; source checks never certify a Lean build."""
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
R1_PATCH_SHA256 = 'aeb8a459b25e3eb45bf05dc8763f7ec00552a01136e4fe992d19f52e152bd1c6'
C2_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SOURCE_GUARD = 'curvature/scripts/point4_two_sided_heat_source_guard.py'
MODULE = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean'
PROBE = 'curvature/scripts/point4_two_sided_heat_probe.lean'
WORKFLOW = '.github/workflows/point4-two-sided-heat.yml'
METADATA = 'docs/point4/two-sided-initial-heat/formalization.yaml'
RELEASE_GUARD = SOURCE_GUARD
RELEASE_TEST = 'curvature/scripts/point4_two_sided_heat_mock_test.py'
SELF_PATHS = {RELEASE_GUARD, RELEASE_TEST}
# Self-authored guard/test bodies are reviewed source. All public paths are fixed;
# every reused R1 and inherited blob is additionally pinned by its exact identity.
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
C2_ORIGINAL_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
C2_ADAPTER = "\n# Reviewed two-sided heat inventory adapter. All inherited gate bodies remain\n# unchanged; the source guard pins this count-one insertion and exact union.\nif (ROOT / 'curvature/scripts/point4_two_sided_heat_source_guard.py').is_file():\n    import sys as _two_sided_sys\n    _two_sided_sys.dont_write_bytecode = True\n    import point4_two_sided_heat_source_guard as _two_sided_release\n    _two_sided_release.install_c2_inventory_adapter(globals())\n\n"
R1_FILE_SHA256 = {'.github/workflows/point4-two-sided-heat.yml': 'd87d08a5d5545ab69c6b579921078efbd70bfa20dcd6f058ed753f575b928ad7', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean': '488c1fdaa617f306e9bd2c714d5917b07319a88cc251195cd0e950b240747529', 'curvature/scripts/point4_two_sided_heat_probe.lean': '3b871129c36100927a141430678bed1bcd190e2f2ea0f7acbbfec0f9f3451af4', 'curvature/scripts/point4_two_sided_heat_source_guard.py': '601d74c08fb5d300dd7bb896f6441cd06e3c4f0b511026518f96bfc040debf11', 'docs/point4/two-sided-initial-heat.md': '0eb9f3eb41ca0712c0d2d203f07bcc720e65393342614f1c5560026b99a8793a'}
R1_SOURCE_COMMIT = '96e666f0520ca261fe745c5cf2c2a4abef38f645'
# Frozen R1 remains historical. Only these exact count-one proof-body edits
# are admitted; mathematical data, public statements and every other byte are fixed.
R1_PROOF_REPAIRS = (
    (
        '  simpa only [initialLaplacianBcf_apply] using hsum Finset.univ\n',
        '  have hfun : (D.initialLaplacianBcf : (Fin n → ℝ) → ℝ) =\n      fun x => ∑ k : Fin n, D.second k k x := by\n    funext x\n    exact D.initialLaplacianBcf_apply x\n  rw [hfun]\n  exact hsum Finset.univ\n',
    ),
    (
        '    simpa only [heatFlowPathBcf, dif_neg (lt_irrefl 0)] using\n',
        '    have hzero : heatFlowPathBcf D.value 0 = D.value := dif_neg (lt_irrefl 0)\n    simpa only [hzero] using\n',
    ),
    (
        '      simpa only [abs_zero, zero_mul] using\n        (continuous_abs.mul continuous_const).tendsto (0 : ℝ)\n',
        '      have hcont : Continuous (fun t : ℝ => |t| * ‖D.initialLaplacianBcf‖) :=\n        continuous_abs.mul continuous_const\n      simpa only [abs_zero, zero_mul] using hcont.tendsto (0 : ℝ)\n',
    ),
    (
        '    simpa only [BoundedContinuousFunction.add_apply,\n      BoundedContinuousFunction.smul_apply, smul_eq_mul] using\n      (D.hasDeriv_value k x).add\n        (((heatSmoothedBoundedC2Data (neg_pos.mpr ht)\n          D.initialLaplacianBcf).hasDeriv_value k x).const_mul t)\n',
        '    simp only [BoundedContinuousFunction.add_apply,\n      BoundedContinuousFunction.smul_apply]\n    apply HasDerivAt.fun_add\n    · exact D.hasDeriv_value k x\n    · exact ((heatSmoothedBoundedC2Data (neg_pos.mpr ht)\n        D.initialLaplacianBcf).hasDeriv_value k x).fun_const_smul t\n',
    ),
    (
        '    simpa only [BoundedContinuousFunction.add_apply,\n      BoundedContinuousFunction.smul_apply, smul_eq_mul] using\n      (D.hasDeriv_first j k x).add\n        (((heatSmoothedBoundedC2Data (neg_pos.mpr ht)\n          D.initialLaplacianBcf).hasDeriv_first j k x).const_mul t)\n',
        '    simp only [BoundedContinuousFunction.add_apply,\n      BoundedContinuousFunction.smul_apply]\n    apply HasDerivAt.fun_add\n    · exact D.hasDeriv_first j k x\n    · exact ((heatSmoothedBoundedC2Data (neg_pos.mpr ht)\n        D.initialLaplacianBcf).hasDeriv_first j k x).fun_const_smul t\n',
    ),
    (
        '      exact neg_pos.mpr ht\n',
        '      exact neg_pos.mpr (mem_Iio.mp ht)\n',
    ),
    (
        '    rw [slope_def_field, D.twoSidedHeatPathBcf_of_neg ht,\n',
        '    have htneg : t < 0 := mem_Iio.mp ht\n    rw [slope_def_field, D.twoSidedHeatPathBcf_of_neg htneg,\n',
    ),
    (
        '    simp only [smul_eq_mul, sub_zero, add_sub_cancel_left]\n    rw [mul_div_cancel_left₀ _ (ne_of_lt ht)]\n',
        '    simp only [Function.comp_apply, smul_eq_mul, sub_zero, add_sub_cancel_left]\n    rw [mul_div_cancel_left₀ _ (ne_of_lt htneg)]\n',
    ),
)
UNIT_FILE_SHA256 = {'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanHeatTwoSidedInitial.lean': '80570fc81fe42ad5cd958584ab2b1252c3145bc815877235b2de3d05be26c487', 'curvature/scripts/point4_two_sided_heat_probe.lean': '3b871129c36100927a141430678bed1bcd190e2f2ea0f7acbbfec0f9f3451af4', '.github/workflows/point4-two-sided-heat.yml': 'a0d70fbcda64c6b5feeadc1cab7787db978fcd64dac880eb94161a0332c0c573', 'docs/point4/two-sided-initial-heat.md': '62098f30c834757f8cc8bb8e4943bb19a48e9fbe0f2792f92d48aa1aa852447f', 'docs/point4/two-sided-initial-heat/formalization.yaml': '2ef33efb616317d135381c7d059a70055cf9c99bc3cf4486491508f5ec370e43', 'docs/point4/two-sided-heat-release-integration.md': 'f792ea70a2c19c49e8dc4ad2771bfe7cd7242f7cc5319de77dd2c043ac2161e9'}


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


# Exact old primary workflow plus two reversible, independent Git checkpoints.
EXACT_HEAD_WORKFLOW_BASE = '92e43cb0e58b8d063d3474b1e7a88aa5b258cf65'
EXACT_HEAD_WORKFLOW_PATH = '.github/workflows/point4-two-sided-heat.yml'
EXACT_HEAD_WORKFLOW_JOB = 'two_sided_heat'
EXACT_HEAD_WORKFLOW_ORIGINAL_SHA256 = '4b6716d8597c425d5eed4d71acfa379a7e7c4a0a95174f35311ef895297e1e0f'
EXACT_HEAD_WORKFLOW_SHA256 = 'a0d70fbcda64c6b5feeadc1cab7787db978fcd64dac880eb94161a0332c0c573'
EXACT_HEAD_BEFORE_ANCHOR = '      - name: Install pinned safe YAML parser from the official package registry\n'
EXACT_HEAD_AFTER_ANCHOR = '      - name: Preserve exact-head evidence\n'
EXACT_HEAD_PREFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness before candidate gates\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'
EXACT_HEAD_POSTFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness after candidate gates\n        if: always()\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'


def raw_git(*args: str) -> bytes:
    """Read the actual committed self objects without Git replacement refs."""
    return subprocess.check_output(['/usr/bin/git', '--no-replace-objects', '-C', str(ROOT), *args], env=ENV)


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
    if path == MODULE:
        assert actual == repaired_r1_module(historical_r1_module()), 'Exact R1 proof-only transform changed'
    if path == PROBE:
        assert UNIT_FILE_SHA256[path] == R1_FILE_SHA256[path], 'Reviewed R1 probe changed'


def historical_r1_module() -> bytes:
    original = git('show', f'{R1_SOURCE_COMMIT}:{MODULE}')
    assert sha256(original) == R1_FILE_SHA256[MODULE], 'Historical R1 proof digest changed'
    return original


def repaired_r1_module(original: bytes) -> bytes:
    assert sha256(original) == R1_FILE_SHA256[MODULE], 'R1 proof repair needs the frozen original'
    source = original.decode()
    for before, after in R1_PROOF_REPAIRS:
        assert source.count(before) == 1, 'R1 proof repair needs exactly one original block'
        assert after not in source, 'R1 proof repair block already present'
        source = source.replace(before, after, 1)
        assert source.count(after) == 1, 'R1 proof repair must occur once'
    repaired = source.encode()
    assert sha256(repaired) == UNIT_FILE_SHA256[MODULE], 'R1 proof-only repaired digest changed'
    return repaired



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


def expected_sources() -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    for path in STARTUP_WORKFLOWS:
        expected[path] = (BASE, adapted_startup_workflow(path, baseline[path][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline), 'New release path overlaps baseline'
    assert set(R1_FILE_SHA256) <= set(UNIT_FILE_SHA256) | SELF_PATHS, 'R1 path was omitted'
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256)), 'Guard/test path collision'
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    check_release_self_sources()
    restored_exact_head_workflow((ROOT / EXACT_HEAD_WORKFLOW_PATH).read_bytes())
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


def install_c2_inventory_adapter(namespace: dict) -> None:
    assert '_two_sided_release_original_expected_sources' not in namespace, 'Duplicate inventory adapter installation'
    assert '_two_sided_release_original_check_workflow' not in namespace, 'Duplicate workflow adapter installation'
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
    namespace['_two_sided_release_original_expected_sources'] = original_expected
    namespace['_two_sided_release_original_check_workflow'] = original_check_workflow
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


def check_new_metadata(source: str) -> None:
    guard = c2_guard()
    parsed = guard.parse_metadata(source)
    entries = guard.metadata_entries(source)
    wanted = {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
        'https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis',
    }
    assert set(entries) == wanted and all(value[0] == 'builds-on' for value in entries.values()), 'New parsed provenance drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope'], 'New supporting scope drift'
    assert parsed['review']['status'] == 'pending', 'Source checks cannot promote review status'
    check_unit_blob(METADATA, source.encode())


def check_new_probe(output: str) -> None:
    source = (ROOT / PROBE).read_text()
    names = c2_guard().check_axiom_output(source, output)
    assert len(names) == 12, 'Reviewed two-sided heat axiom surface count changed'


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
    check_inventory()
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
    if args.probe_log:
        check_new_probe(args.probe_log.read_text())
    print(json.dumps({'baseline': BASE, 'public_paths': len(public_paths()),
                      'inherited_files_byte_identical': 1637, 'exact_inherited_guard_adapters': 1,
                      'exact_startup_workflow_adapters': len(STARTUP_WORKFLOWS),
                      'historical_r1_proof_sha256': R1_FILE_SHA256[MODULE],
                      'exact_r1_proof_only_repairs': len(R1_PROOF_REPAIRS),
                      'r1_probe_blob_unchanged': True,
                      'root_imports_and_metadata_byte_identical': True,
                      'lean_verified': False, 'point4': 'OPEN'}, indent=2))
    print('Source-only release checks passed; exact Lean 4.33 module/probes/full-build/kernel gates remain separate')


# Bounded integration of merged PR131 with the separately reviewed PR132 unit.
# Historical e6/R1 reconstruction, source hashes and validators remain above.
JOINT_MASTER = 'a0132cd55e2540b2fd26adecea9a07b51f1b8292'
JOINT_MASTER_TREE = '9401fcd8272746e77db182de22b394d8605f901a'
JOINT_BYTECODE_PREFIX = '\nimport sys as _joint_release_sys\n_joint_release_sys.dont_write_bytecode = True\n'
JOINT_MANIFOLD_GUARD = 'curvature/scripts/point4_manifold_heat_release_guard.py'
JOINT_MANIFOLD_TEST = 'curvature/scripts/point4_manifold_heat_release_mock_test.py'
JOINT_MANIFOLD_SOURCE = 'curvature/scripts/point4_manifold_heat_source_test.py'
JOINT_MANIFOLD_SELF = {JOINT_MANIFOLD_GUARD, JOINT_MANIFOLD_TEST}
JOINT_MANIFOLD_ADDITIONS = {'.github/workflows/point4-manifold-only-fixed-background-heat.yml': '5e7340964ced277dd1841faf0a9bbc8af630f90a', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatCoefficients.lean': '97d7d90cfd997cba0a670f9b1c031c86c67d20a9', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatFixedBackground.lean': 'ed9935e3fa015f1393b62810ecfd94a1291e277f', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessTensorHeatLocalization.lean': 'aa784613c9d6529e2b6b6d3138bae246c083fa37', 'curvature/scripts/point4_manifold_heat_mock_test.py': '0752cc009d80c5b7d4e343b1ebe2d929a307e95e', 'curvature/scripts/point4_manifold_heat_probe.lean': '9cb41f0bcf985a3d419ba0b3d136cdf0b9008a09', 'curvature/scripts/point4_manifold_heat_release_guard.py': 'e61f9bf3dfa27a64b346db0da3c78640b7ca723c', 'curvature/scripts/point4_manifold_heat_release_mock_test.py': '0ddbe6e366fc13445d2f718cb7e1acbab73d1ce8', 'curvature/scripts/point4_manifold_heat_source_test.py': '874548ea0183420dd690cdf84e18ed1379472fcf', 'docs/point4/manifold-only-fixed-background-heat.md': '6fe6c401c8e6d7dfd97957146c830a8d57fbbe4c', 'docs/point4/manifold-only-fixed-background-heat/formalization.yaml': '8be2929a793a72cc4db9e6e29a1c19a4ccb3537a', 'docs/point4/manifold-only-heat-release-integration.md': '2b6c89bd0b9db87205d91448c5a8bf3a773de065'}
JOINT_SOURCE_TRANSFORMS = (
    ("        # The release permits exactly one inherited source-guard transformation.\n", "        # Exactly one C2 guard and three startup workflows are reconstructed.\n"),
    ("            wanted = adapted_c2_guard(wanted)\n", "            wanted = adapted_c2_guard(wanted)\n        elif path in _joint_release.STARTUP_WORKFLOWS:\n            wanted = _joint_release.adapted_startup_workflow(path, wanted)\n"),
    ("'inherited_files_unchanged': len(inherited) - 1,", "'inherited_files_unchanged': len(inherited) - 4,"),
    ("'exact_inherited_guard_adapters': 1,", "'exact_inherited_guard_adapters': 1,\n            'exact_inherited_startup_adapters': 3,"),
    ("from point4_scan import strip_comments\n", "from point4_scan import strip_comments\nimport point4_two_sided_heat_source_guard as _joint_release\n"),
)
_joint_two_sided_adapted_c2_guard = adapted_c2_guard
_joint_two_sided_installer = install_c2_inventory_adapter
_joint_two_sided_self_paths = set(SELF_PATHS)
SELF_PATHS = SELF_PATHS | JOINT_MANIFOLD_SELF


def joint_manifold_guard():
    return importlib.import_module('point4_manifold_heat_release_guard')


def adapted_c2_guard(original: bytes) -> bytes:
    # Both original constructors execute their count/digest checks independently.
    _joint_two_sided_adapted_c2_guard(original)
    manifold = joint_manifold_guard()
    manifold._joint_original_adapted_c2_guard(original)
    return original.replace(ENTRY_POINT.encode(),
        (JOINT_BYTECODE_PREFIX + manifold.C2_ADAPTER + C2_ADAPTER + ENTRY_POINT.lstrip('\n')).encode(), 1)


def joint_adapted_manifold_source(original: bytes) -> bytes:
    assert sha256(original) == joint_manifold_guard().UNIT_FILE_SHA256[JOINT_MANIFOLD_SOURCE], 'Historical manifold source guard changed'
    actual = original
    for old, new in JOINT_SOURCE_TRANSFORMS:
        assert actual.count(old.encode()) == 1, 'Missing/duplicate manifold source transform'
        actual = actual.replace(old.encode(), new.encode(), 1)
    restored = actual
    for old, new in reversed(JOINT_SOURCE_TRANSFORMS):
        assert restored.count(new.encode()) == 1, 'Ambiguous manifold reverse transform'
        restored = restored.replace(new.encode(), old.encode(), 1)
    assert restored == original
    return actual


def joint_check_manifold_source(actual: bytes) -> None:
    original = raw_git('show', JOINT_MASTER + ':' + JOINT_MANIFOLD_SOURCE)
    assert actual == joint_adapted_manifold_source(original), 'Manifold source guard differs beyond exact joint transform'


@functools.lru_cache(maxsize=1)
def joint_master_sources() -> dict[str, tuple[str, bytes]]:
    assert raw_git('rev-parse', JOINT_MASTER + '^{tree}').decode().strip() == JOINT_MASTER_TREE, 'Merged master tree identity changed'
    records = nul_records(raw_git('ls-tree', '-rz', JOINT_MASTER))
    inventory = {}
    for record in records:
        descriptor, name = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = name.decode()
        assert kind == 'blob' and mode in {'100644', '100755'} and path not in inventory
        inventory[path] = (mode, oid)
    baseline = baseline_sources()
    assert set(inventory) == set(baseline) | set(JOINT_MANIFOLD_ADDITIONS), 'Merged master exact addition union changed'
    assert not set(baseline) & set(JOINT_MANIFOLD_ADDITIONS)
    result = {}
    for path, (mode, oid) in inventory.items():
        data = raw_git('show', JOINT_MASTER + ':' + path)
        assert git_blob_identity(data) == oid, 'Merged master physical blob identity drift: ' + path
        if path in baseline:
            wanted = joint_manifold_guard()._joint_original_adapted_c2_guard(baseline[path][1]) if path == C2_GUARD else baseline[path][1]
            assert mode == baseline[path][0] and data == wanted, 'Merged master inherited byte/mode drift: ' + path
        else:
            assert (mode, oid) == ('100644', JOINT_MANIFOLD_ADDITIONS[path]), 'Merged master addition identity drift: ' + path
        result[path] = (mode, data)
    return result


def public_paths() -> set[str]:
    return set(baseline_sources()) | set(JOINT_MANIFOLD_ADDITIONS) | set(UNIT_FILE_SHA256) | SELF_PATHS


def expected_sources() -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    subprocess.run(['/usr/bin/git', '--no-replace-objects', '-C', str(ROOT), 'merge-base', '--is-ancestor', JOINT_MASTER, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    master = joint_master_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    for path in STARTUP_WORKFLOWS:
        expected[path] = (BASE, adapted_startup_workflow(path, baseline[path][1]))
    assert not set(UNIT_FILE_SHA256) & (set(baseline) | set(JOINT_MANIFOLD_ADDITIONS))
    assert set(R1_FILE_SHA256) <= set(UNIT_FILE_SHA256) | SELF_PATHS
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256))
    for path in set(JOINT_MANIFOLD_ADDITIONS) - JOINT_MANIFOLD_SELF:
        original = master[path][1]
        wanted = joint_adapted_manifold_source(original) if path == JOINT_MANIFOLD_SOURCE else original
        actual = (ROOT / path).read_bytes()
        assert actual == wanted, 'Merged manifold addition changed: ' + path
        joint_manifold_guard().check_unit_blob(path, actual)
        expected[path] = (JOINT_MASTER, wanted)
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    check_release_self_sources()
    restored_exact_head_workflow((ROOT / EXACT_HEAD_WORKFLOW_PATH).read_bytes())
    check_inventory()
    return expected


def joint_install_manifold_adapter(namespace: dict, original_installer) -> None:
    assert '_joint_manifold_installed' not in namespace, 'Duplicate joint manifold adapter'
    assert '_two_sided_release_original_expected_sources' not in namespace, 'Wrong joint adapter order'
    assert original_installer is joint_manifold_guard()._joint_original_installer
    original_installer(namespace)
    namespace['_joint_manifold_expected_wrapper'] = namespace['expected_sources']
    namespace['_joint_manifold_installed'] = True


def install_c2_inventory_adapter(namespace: dict) -> None:
    assert namespace.get('_joint_manifold_installed') is True, 'Joint manifold adapter must execute first'
    assert '_two_sided_release_original_expected_sources' not in namespace, 'Duplicate joint two-sided adapter'
    assert '_two_sided_release_original_check_workflow' not in namespace
    manifold = joint_manifold_guard()
    original_added = set(namespace['ADDED']) - JOINT_MANIFOLD_SELF
    assert set(namespace['ADDED']) == original_added | JOINT_MANIFOLD_SELF
    assert namespace['expected_sources'] is namespace['_joint_manifold_expected_wrapper'], 'Joint manifold wrapper changed'
    manifold_wrapper = namespace['expected_sources']
    namespace['expected_sources'] = namespace['_manifold_release_original_expected_sources']
    namespace['ADDED'] = original_added
    _joint_two_sided_installer(namespace)
    two_sided_wrapper = namespace['expected_sources']
    def full_joint_expected_sources():
        manifold_expected = manifold_wrapper()
        two_sided_expected = two_sided_wrapper()
        assert manifold_expected == two_sided_expected, 'Joint reconstructions disagree'
        return two_sided_expected
    namespace['expected_sources'] = full_joint_expected_sources
    namespace['ADDED'] = namespace['ADDED'] | JOINT_MANIFOLD_SELF


def joint_reset_c2_namespace(namespace: dict, install_manifold=True) -> dict:
    # Test reconstruction uses the actual saved legacy functions and exact scope.
    namespace = dict(namespace)
    namespace['expected_sources'] = namespace['_manifold_release_original_expected_sources']
    namespace['check_workflow'] = namespace['_two_sided_release_original_check_workflow']
    namespace['ADDED'] = set(namespace['ADDED']) - SELF_PATHS
    for key in ('_manifold_release_original_expected_sources',
                '_two_sided_release_original_expected_sources',
                '_two_sided_release_original_check_workflow',
                '_joint_manifold_expected_wrapper', '_joint_manifold_installed'):
        namespace.pop(key)
    if install_manifold:
        joint_manifold_guard().install_c2_inventory_adapter(namespace)
    return namespace

# BEGIN exact finite incoming-leaf-132
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == '21bc25ee9c5916a0675d48fa79f89d834e60c9cec184437bdbdab77bf5abcd6d', "Incoming composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
_curvature_comp.install_curvature_leaf(globals(),132)
# END exact finite incoming-leaf-132

if __name__ == '__main__':
    main()
