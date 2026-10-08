#!/usr/bin/env python3
"""Finite source composition; source/evidence validation is not Lean closure.

Current weighted checks are leaves. Historical subprocesses execute immutable
original entry points; no current adapter is installed in their checkouts.
"""
from __future__ import annotations
import argparse, base64, contextlib, functools, hashlib, importlib, json, os
import pathlib, re, stat, subprocess, sys, tempfile, types

ROOT = pathlib.Path(__file__).resolve().parents[2]
MASTER = 'e883681caa862277857ee825a547502e8f3ec036'
SUPPORT = '93ed035498e0bf02096202d2f2895d906fb88234'
LOCALIZATION = '6cdbc00828607d80e180a9cffc0cc3376b3b7e42'
WEIGHTED_MOCK_PARENT = 'f59fb6799f77d5d9cc298fef2632e8ebf887b97b'
TREES = {MASTER: '10740092a77d5457a981154ea0d75a11120c54dd',
         SUPPORT: '51b59d500108f632e3fa7d7993d14d74fd1491a7',
         WEIGHTED_MOCK_PARENT: '9ab0bbc6ba97352e903a0489cf89fddb97757a17'}
HELPER = 'curvature/scripts/point4_smooth_master_composition.py'
TEST = 'curvature/scripts/point4_smooth_master_composition_test.py'
MAP = 'docs/point4/smooth-master-composition/identity-map.json'
DOC = 'docs/point4/smooth-master-composition.md'
NEW = {HELPER, TEST, MAP, DOC}
WEIGHTED = 'curvature/scripts/point4_weighted_hessian_release_guard.py'
LOCAL = 'curvature/scripts/point4_c2_metric_localization_source_test.py'
CONSISTENCY = 'curvature/scripts/point4_pr130_pr133_inventory.py'
SMOOTH = 'curvature/scripts/point4_smooth_forward_release_guard.py'
FIXTURE = 'curvature/scripts/point4_smooth_forward_release_mock_test.py'
WORKFLOW = '.github/workflows/point4-smooth-forward-support.yml'
LOCALIZATION_WORKFLOW = '.github/workflows/point4-c2-metric-localization.yml'
LOCALIZATION_MOCK = 'curvature/scripts/point4_c2_metric_localization_mock_test.py'
LOCALIZATION_MOCK_FLAG = '--historical-localization-mocks'
MOCK_ROUTE_PARENT = '22f0f8a3c353f22600f94370a505bde0d10ea2c4'
MOCK_ROUTE_TREE = 'd48ce9af6ee5cfecf3bda717b6ede24942225cd2'
LOCALIZATION_MOCK_COMMAND = '          python3 curvature/scripts/point4_c2_metric_localization_mock_test.py 2>&1 | tee /tmp/point4-c2-metric-localization-adversarial.log\n'
LOCALIZATION_MOCK_ROUTE_COMMAND = '          python3 curvature/scripts/point4_c2_metric_localization_source_test.py --schema /tmp/point4-c2-metric-localization-schema.json --historical-localization-mocks 2>&1 | tee /tmp/point4-c2-metric-localization-adversarial.log\n'
LOCALIZATION_PROBE_COMMAND = '          lake env lean scripts/point4_c2_metric_localization_probe.lean 2>&1 | tee /tmp/point4-c2-metric-localization-axioms.log\n'
LOCALIZATION_CONTRACT_BUILD_COMMAND = '          lake build PoincareCurvature.Geometry.Manifold.RicciFlow.PointFourContract 2>&1 | tee /tmp/point4-c2-metric-localization-contract-build.log\n'
WEIGHTED_WORKFLOW = '.github/workflows/point4-weighted-duhamel-hessian.yml'
MANIFOLD_WORKFLOW = '.github/workflows/point4-manifold-only-fixed-background-heat.yml'
WEIGHTED_MOCK = 'curvature/scripts/point4_weighted_hessian_release_mock_test.py'
WEIGHTED_MOCK_FLAG = '--historical-weighted-mocks'
WEIGHTED_MOCK_COMMAND = '          python3 curvature/scripts/point4_weighted_hessian_release_mock_test.py\n'
WEIGHTED_MOCK_ROUTE_COMMAND = '          python3 curvature/scripts/point4_weighted_hessian_release_guard.py --schema /tmp/point4-weighted-hessian-evidence/official-schema.json --historical-weighted-mocks\n'
STARTUP_REPAIR_PARENT = '1664872ce762ee027b76cb515befb0ae829b2711'
STARTUP_REPAIR_TREE = '6d74e9612cf6e16f2d027012cede68e5e0a23483'
STARTUP_ANCHOR = '    timeout-minutes: 350\n    steps:\n'
STARTUP_ENV = '    env:\n      PYTHONDONTWRITEBYTECODE: "1"\n'
EDITED = {WEIGHTED, LOCAL, CONSISTENCY, SMOOTH, FIXTURE, WORKFLOW, LOCALIZATION_WORKFLOW, WEIGHTED_WORKFLOW, MANIFOLD_WORKFLOW}
SHARED = {'.github/workflows/point4-c2-initial-heat.yml',
 '.github/workflows/point4-linear-heat-geometry.yml',
 '.github/workflows/point4-weighted-initial-heat.yml',
 'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml',
 'curvature/scripts/point4_c2_initial_heat_mock_test.py',
 'curvature/scripts/point4_c2_initial_heat_source_test.py',
 'curvature/scripts/point4_linear_heat_geometry_mock_test.py',
 'curvature/scripts/point4_linear_heat_geometry_source_test.py',
 'curvature/scripts/point4_manifold_heat_release_guard.py',
 'curvature/scripts/point4_manifold_heat_release_mock_test.py',
 'curvature/scripts/point4_manifold_heat_source_test.py', 'docs/point4/README.md'}
ROOT_CHANGES = {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml', 'docs/point4/README.md'}
WEIGHTED_MISSING = {'.github/workflows/point4-c2-metric-localization.yml',
 'curvature/PoincareCurvature/Analysis/CompactlySupportedC2Jet.lean',
 'curvature/PoincareCurvature/Analysis/FiniteCoordinateBilinear.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessInitialMetricLocalization.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanC2Localization.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/PositiveFrozenC2Localization.lean',
 'curvature/scripts/point4_c2_metric_localization_mock_test.py',
 'curvature/scripts/point4_c2_metric_localization_probe.lean', LOCAL,
 'curvature/scripts/point4_pr130_pr131_inventory.py',
 'curvature/scripts/point4_pr130_pr131_inventory_test.py', CONSISTENCY,
 'curvature/scripts/point4_pr130_pr133_inventory_test.py',
 'docs/point4/c2-metric-localization.md',
 'docs/point4/pr130-pr131-desktop-integration.md',
 'docs/point4/pr130-pr133-desktop-integration.md'}
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
ENTRY = "\nif __name__ == '__main__':"
WF_ANCHOR = '      - name: Preserve exact-head evidence\n'
WF_STEP = '      - name: Check ordinary current composition and real historical validator routes\n        timeout-minutes: 125\n        env:\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          PYTHONDONTWRITEBYTECODE=1 python3 curvature/scripts/point4_smooth_master_composition_test.py --real-runtime --schema /tmp/point4-manifold-heat-official-schema.json\n'
_owner = None
_depth = 0

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def blob_id(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def git(*args, root=None):
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(root or ROOT), *args], env=ENV)

def parse_tree(data):
    assert data and data.endswith(b'\0'), 'Incomplete source tree'
    result = {}
    for record in data.split(b'\0')[:-1]:
        descriptor, path = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = path.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}
        assert re.fullmatch(r'[0-9a-f]{40}', oid) and path not in result
        assert not pathlib.PurePosixPath(path).is_absolute() and '..' not in pathlib.PurePosixPath(path).parts
        result[path] = mode, oid
    return result

def parent_tree(commit):
    if commit in TREES:
        assert git('rev-parse', commit+'^{tree}').decode().strip() == TREES[commit]
    return parse_tree(git('ls-tree', '-rz', commit))

def resolve_union(master, support):
    assert len(master) == 1704 and len(support) == 1672
    assert {p for p in master.keys() & support.keys() if master[p] != support[p]} == SHARED
    assert len(master.keys()-support.keys()) == 51 and len(support.keys()-master.keys()) == 19
    assert not NEW & (master.keys() | support.keys())
    result = dict(support)
    result.update(master)
    assert len(result) == 1723
    return result

def bootstrap(path, helper_sha):
    assert re.fullmatch(r'[0-9a-f]{64}', helper_sha)
    methods = {WEIGHTED: 'install_weighted', LOCAL: 'install_localization',
               CONSISTENCY: 'install_consistency', SMOOTH: 'install_smooth'}
    if path == FIXTURE:
        action = "if __name__ == '__main__':\n    _smooth_master.run_support_fixtures(sys.argv[1:])\n    raise SystemExit(0)\n"
    else:
        assert path in methods
        action = '_smooth_master.' + methods[path] + '(globals())\n'
    # Pin before import. These imports and count-one hooks are finite policy,
    # not records authorized by the descriptive JSON identity map.
    return ("\n# Reviewed finite smooth/master composition; original validator bodies survive.\n"
        "import hashlib as _composition_hashlib, pathlib as _composition_pathlib, stat as _composition_stat, sys as _composition_sys\n"
        "_composition_file = _composition_pathlib.Path(__file__).resolve().parents[2] / '" + HELPER + "'\n"
        "assert _composition_stat.S_ISREG(_composition_file.lstat().st_mode) and not _composition_file.lstat().st_mode & 0o111\n"
        "assert _composition_hashlib.sha256(_composition_file.read_bytes()).hexdigest() == '" + helper_sha + "', 'Composition executable binding changed'\n"
        + ("_composition_sys.modules.setdefault('point4_weighted_hessian_release_guard', _composition_sys.modules[__name__])\n" if path == WEIGHTED else '')
        + "import point4_smooth_master_composition as _smooth_master\n" + action)

def transform(path, original, helper_sha, fixture_sha=None, workflow_sha=None):
    source = original.decode()
    assert '_smooth_master.' not in source, 'Previously transformed source is not an input'
    if path == WEIGHTED_WORKFLOW:
        assert source.count(WEIGHTED_MOCK_COMMAND) == 1 and WEIGHTED_MOCK_FLAG not in source
        return source.replace(WEIGHTED_MOCK_COMMAND,WEIGHTED_MOCK_ROUTE_COMMAND,1).encode()
    if path == MANIFOLD_WORKFLOW:
        assert source.count(STARTUP_ANCHOR) == 1 and 'PYTHONDONTWRITEBYTECODE' not in source[:source.index('    steps:\n')]
        return source.replace(STARTUP_ANCHOR,STARTUP_ANCHOR.replace('    steps:\n',STARTUP_ENV+'    steps:\n'),1).encode()
    if path == LOCALIZATION_WORKFLOW:
        assert source.count(STARTUP_ANCHOR) == 1 and 'PYTHONDONTWRITEBYTECODE' not in source
        assert source.count(LOCALIZATION_MOCK_COMMAND) == 1 and LOCALIZATION_MOCK_FLAG not in source
        source=source.replace(LOCALIZATION_MOCK_COMMAND,LOCALIZATION_MOCK_ROUTE_COMMAND,1)
        assert source.count(LOCALIZATION_PROBE_COMMAND) == 1 and LOCALIZATION_CONTRACT_BUILD_COMMAND not in source
        source=source.replace(LOCALIZATION_PROBE_COMMAND,LOCALIZATION_CONTRACT_BUILD_COMMAND+LOCALIZATION_PROBE_COMMAND,1)
        return source.replace(STARTUP_ANCHOR, STARTUP_ANCHOR.replace('    steps:\n', STARTUP_ENV+'    steps:\n'), 1).encode()
    if path == WORKFLOW:
        assert source.count(WF_ANCHOR) == 1 and WF_STEP not in source
        assert source.count(STARTUP_ANCHOR) == 1 and STARTUP_ENV not in source
        source=source.replace(WF_ANCHOR, WF_STEP+WF_ANCHOR, 1)
        return source.replace(STARTUP_ANCHOR, STARTUP_ANCHOR.replace('    steps:\n', STARTUP_ENV+'    steps:\n'), 1).encode()
    if path == SMOOTH:
        assert fixture_sha and workflow_sha
        # Replace only the two selected FILE_SHA256 values, never other code.
        import ast
        a=source.index('FILE_SHA256 = ');b=source.index('\nADDED = ',a)
        mapping=ast.literal_eval(source[a+len('FILE_SHA256 = '):b])
        assert set(mapping)|{SMOOTH} == set(parent_tree(SUPPORT))-set(parent_tree(MASTER))
        mapping[FIXTURE]=fixture_sha;mapping[WORKFLOW]=workflow_sha
        source=source[:a]+'FILE_SHA256 = '+repr(mapping)+source[b:]
    assert path in EDITED and source.count(ENTRY) == 1, 'Adapter boundary must be count-one'
    return source.replace(ENTRY, bootstrap(path,helper_sha)+ENTRY,1).encode()

def original_bytes(path, master, support):
    parent = MASTER if path in master else SUPPORT
    data = git('show', parent+':'+path)
    assert blob_id(data) == (master if parent == MASTER else support)[path][1]
    return data

# First approved remaining-PR integration: finite sources, not a prefix grant.
HEAT_PARENT = '5286f8e76fe26c56eea662552e4591ef2d227da7'
HEAT_PARENT_TREE = '615db704840b205c64d299a3420520fbb4c96786'
HEAT_SOURCE = '0fce83f00a2e8832e5098ee43d8f260f3a98e9c9'
HEAT_SOURCE_TREE = 'd684b93cc338201628a9bcd6ac6c461c9975404d'
HEAT_ROOT = 'curvature/PoincareCurvature.lean'
HEAT_METADATA = 'curvature/formalization.yaml'
HEAT_DOC = 'docs/point4/README.md'
HEAT_DOMAIN = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineC2AlphaDomain.lean'
HEAT_MODULE = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckHeatInvariantClosure.lean'
HEAT_PROBE = 'curvature/scripts/point4_heat_invariant_probe.lean'
HEAT_WORKFLOW = '.github/workflows/point4-support.yml'
HEAT_ADDED = {HEAT_MODULE, HEAT_PROBE, HEAT_WORKFLOW}
HEAT_ROOTS = {HEAT_ROOT, HEAT_METADATA, HEAT_DOC}
HEAT_IMPORT_ANCHOR = 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckMatrixLittleHolderClosure\n'
HEAT_IMPORT = 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckHeatInvariantClosure\n'
HEAT_METADATA_NOTE = '  - id: "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/0fce83f00a2e8832e5098ee43d8f260f3a98e9c9/curvature"\n    relationship: "builds-on"\n    note: >-\n      Immutable PR110 source for AnalyticPDE/GenuineRicciDeTurckHeatInvariantClosure.lean,\n      scripts/point4_heat_invariant_probe.lean and the supporting proof workflow.\n      The exact eight-declaration proof/probe source and contributor notice are\n      preserved. Jet2Section remains an independent product of little-Holder\n      fields; the inherited domain edit corrects comments without changing\n      mathematical code. The new integration adds a root import, scoped status\n      discussion and finite source composition. It proves no derivative-compatible\n      geometric PDE solver, nonlinear Ricci-DeTurck existence, canonical Point-4\n      completion or smooth-target completion. Historical source-head verification\n      is distinct from fresh combined-head compilation, axioms and review.\n\n'
HEAT_DOC_BLOCK = '\n## Heat-invariant closure on independent jet fields\n\nThe PR110 supporting theorem fixes the Euclidean section under componentwise\nheat propagation, preserves its centered closed ball, derives the compact\nfiber-range premise from the small-ball bound, and packages the reaction in\nthe little-Hölder carrier with a full-norm Lipschitz estimate. Its source is\n[`GenuineRicciDeTurckHeatInvariantClosure.lean`](../../curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckHeatInvariantClosure.lean).\nIt retains `0 < α < 1`, `0 < R`,\n`2 * jet2LipConst d d * R < phiRDRadius d`, and the supplied fixed coordinate\nbackground coefficients. The eight-declaration probe and original supporting\nworkflow remain attached to this result.\n\nThree distinctions delimit what this closure proves:\n\n1. `UsesChosenBackground` chooses the Levi–Civita connection of the evolving\n   metric itself. The existing\n   `intrinsicRicciDeTurckRHS_chosenLeviCivitaFamily_eq_intrinsicRicciFlowRHS`\n   removes the DeTurck correction for that choice. Those conditional packages\n   do not construct the strictly parabolic fixed-background DeTurck equation.\n2. `Jet2Section` is a product of independent little-Hölder component fields.\n   It does not require first slots to differentiate the value field, or\n   second slots to differentiate first slots. Evaluating supplied components\n   with `jet2OfSection` does not establish derivative compatibility.\n3. `phiRDOfJet` is the full coordinate right-hand side `-2 Ric + Lie_W g`.\n   It is not the remainder after subtracting a frozen heat generator.\n   Propagating the independent fields with heat and reaction `(phiRD, 0, 0)`\n   does not identify an auxiliary product-space equation with the geometric PDE.\n\nThe canonical target still requires spatially C² initial data, its existing\nweak competitor class, ordinary initial derivatives, and a common closed\ntime interval under the approved `BoundarylessManifold I M` premise. The\nseparately named smooth forward target retains its own contract and audit.\nThis closure proves neither target. Derivative-compatible spaces, the\ngenerator/remainder identity, quasilinear existence, positivity, intrinsic\nidentification, gauge regularity, and uniqueness remain separate obligations.\n\nThe inherited PR110 source is\n[`0fce83f00a2e8832e5098ee43d8f260f3a98e9c9`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/0fce83f00a2e8832e5098ee43d8f260f3a98e9c9/curvature).\nIts successful [historical focused run](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37181895941)\nqualifies that old checkout. The integration starts from master\n`5286f8e76fe26c56eea662552e4591ef2d227da7`; fresh compilation, the eight\nstandard-axiom records, root elaboration, relevant audits, and independent\nreview of the combined head remain pending. Point 4 and the smooth target\nremain **OPEN**.\n\n'
HEAT_DOC_ANCHOR = '\n## Boundaryless chart transport\n'


def heat_transform(path, original):
    if path == HEAT_ROOT:
        anchor, addition = HEAT_IMPORT_ANCHOR.encode(), HEAT_IMPORT.encode()
        assert original.count(anchor) == 1 and addition not in original, 'Heat import anchor drift'
        return original.replace(anchor, anchor + addition, 1)
    if path == HEAT_METADATA:
        anchor, addition = b'related_formalizations:\n', HEAT_METADATA_NOTE.encode()
        assert original.count(anchor) == 1 and HEAT_SOURCE.encode() not in original, 'Heat provenance anchor drift'
        return original.replace(anchor, anchor + addition, 1)
    assert path == HEAT_DOC
    anchor, addition = HEAT_DOC_ANCHOR.encode(), HEAT_DOC_BLOCK.encode()
    assert original.count(anchor) == 1 and addition not in original, 'Heat scope anchor drift'
    return original.replace(anchor, addition + anchor, 1)


def heat_inverse(path, actual):
    assert path in HEAT_ROOTS
    original = git('show', HEAT_PARENT + ':' + path)
    assert blob_id(original) == parent_tree(HEAT_PARENT)[path][1]
    assert actual == heat_transform(path, original), 'Exact heat root/provenance/scope drift: ' + path
    return original


def heat_identity(expected, originals, changes):
    # Independently authenticate the complete landed base, including its legacy
    # dispatch/environment repair. Reconstruct its old digest-bound transforms
    # before applying this one integration, rather than trusting a new map.
    base, source = parent_tree(HEAT_PARENT), parent_tree(HEAT_SOURCE)
    assert len(base) == 1727 and len(source) == 1562
    assert set(base) == set(resolve_union(parent_tree(MASTER), parent_tree(SUPPORT))) | NEW
    old_helper = git('show', HEAT_PARENT + ':' + HELPER)
    assert blob_id(old_helper) == base[HELPER][1]
    old_digest = sha256(old_helper)
    prior = {p: transform(p, originals[p], old_digest) for p in EDITED - {SMOOTH}}
    prior[SMOOTH] = transform(SMOOTH, originals[SMOOTH], old_digest,
                             sha256(prior[FIXTURE]), sha256(prior[WORKFLOW]))
    for p, identity in expected.items():
        assert base[p] == (('100644', blob_id(prior[p])) if p in EDITED else identity), 'Landed base policy drift: ' + p
    assert not HEAT_ADDED & set(base)
    for p in sorted(HEAT_ADDED | {HEAT_DOMAIN}):
        assert source[p][0] == '100644'
        data = git('show', HEAT_SOURCE + ':' + p)
        assert blob_id(data) == source[p][1]
        if p == HEAT_DOMAIN:
            assert base[p][0] == '100644'
        else:
            assert p not in expected
        expected[p] = source[p]
        changes[p] = data
    for p in sorted(HEAT_ROOTS):
        original = git('show', HEAT_PARENT + ':' + p)
        assert blob_id(original) == base[p][1]
        originals[p] = original
        changes[p] = heat_transform(p, original)
        expected[p] = '100644', blob_id(changes[p])
    assert len(expected) == 1726  # Three fixed additions before the four NEW paths.
    return expected, originals, changes


def heat_check_imports(local, actual):
    original = heat_inverse(HEAT_ROOT, actual)
    local.legacy_check_imports(original)
    base = local.blob(local.INTEGRATION_PARENT, HEAT_ROOT)
    # Run the original semantic body against the actual current import union;
    # the one additional import is reconstructed from an authenticated source.
    local.check_imports(actual, heat_transform(HEAT_ROOT, base), base)


def heat_check_metadata(local, actual):
    raw = actual.encode() if isinstance(actual, str) else actual
    original = heat_inverse(HEAT_METADATA, raw)
    local.legacy_check_metadata(original.decode())
    base = local.blob(local.INTEGRATION_PARENT, HEAT_METADATA)
    # Only the master input receives the new entry, preventing duplicate-note
    # union semantics from changing the inherited entries or the literal note.
    local.check_metadata(raw, heat_transform(HEAT_METADATA, base), base)

TREES.update({HEAT_PARENT: HEAT_PARENT_TREE, HEAT_SOURCE: HEAT_SOURCE_TREE})


CONTRACTION_PARENT = 'e303730173222d39da842f7831372ddd001f6874'
CONTRACTION_PARENT_TREE = 'f358da765aedb8eb05fb7d844e0048048f59c9b3'
CONTRACTION_SOURCE = '93aa44010811b9145d6ff79abac3ed506ad51c29'
CONTRACTION_SOURCE_TREE = 'd3e7c360e957a54dfa51acd8959c27c0d080507a'
CONTRACTION_BASE = 'a0f0fafc2505f1db28c2b9f9b00ce11384f69c39'
CONTRACTION_BASE_TREE = 'f89511410ec16639199609238ba435fd64f9b16e'
CONTRACTION_ADDED = {'curvature/PoincareCurvature/Analysis/TimeDependentMetricContraction.lean',
    'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/MetricContractedDeTurckJointRegularity.lean'}
CONTRACTION_REPLACED = {'.github/workflows/point4-contraction.yml',
    'curvature/scripts/point4_contraction_probe.lean', 'docs/point4/contraction-repair.md'}
CONTRACTION_ROOTS = {HEAT_ROOT, HEAT_METADATA, HEAT_DOC}
CONTRACTION_PATHS = CONTRACTION_ADDED | CONTRACTION_REPLACED | {HEAT_ROOT, HEAT_DOC}
CONTRACTION_OPERATIONS = {'curvature/PoincareCurvature.lean': [{'old_utf8': '', 'new_utf8': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.MetricContractedDeTurckJointRegularity\n', 'anchor_utf8': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckPrincipalRemainder\n'}], 'docs/point4/README.md': [{'old_utf8': '', 'new_utf8': 'The conventional two-input-slot DeTurck repair now has a candidate joint-field\nfollow-up in `MetricContractedDeTurckJointRegularity.lean`. From a jointly smooth\nmetric representative agreeing with the defining metric and the actual jointly\nsmooth Levi--Civita correction tensor, it proves the conventional inverse-Gram\nvector formula and joint smoothness of the positive field and negative recovery\ngauge. The correction-functional corollary derives the tensor premise by the\nexisting geometric Gram/Riesz reconstruction, and a conditional compact-flow\nwrapper uses this same conventional gauge. These are explicit geometric\nregularity hypotheses, not assumptions about the final contracted field or a\nclaim of PDE existence. The generic contraction passed exact Lean-4.33 compilation; final\nverification of the new geometric adapter remains pending. See [contraction repair](contraction-repair.md) for the\nfield distinction and verification boundary. Point 4 remains OPEN.\n\n', 'anchor_utf8': 'The candidate algebraic principal/remainder milestone is packaged in\n`RicciDeTurckPrincipalRemainder.lean`. It derives an exact finite reaction split\n'}, {'old_utf8': 'with the manifold tensor-heat generator. No compilation of this candidate has\nbeen run yet. See [principal/remainder scope](principal-remainder.md) for the\n', 'new_utf8': 'with the manifold tensor-heat generator. Its exact Lean-4.33 full build and eleven standard-only axiom probes\npassed before the principal milestone was merged into master. See [principal/remainder scope](principal-remainder.md) for the\n', 'anchor_utf8': ''}]}
CONTRACTION_METADATA_NOTE = '  - id: "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/93aa44010811b9145d6ff79abac3ed506ad51c29/curvature"\n    relationship: "builds-on"\n    note: >-\n      Immutable PR115 source for Analysis/TimeDependentMetricContraction.lean,\n      Geometry/Manifold/RicciFlow/GaugeReduction/MetricContractedDeTurckJointRegularity.lean,\n      scripts/point4_contraction_probe.lean and the contraction proof workflow.\n      The inherited mathematical declarations, smooth-metric and correction-tensor\n      regularity hypotheses, compact boundaryless nonempty flow scope, proofs,\n      thirteen-declaration probe and contributor notices are preserved.\n      The integration adds an exact root import, structured provenance and finite\n      source composition; it constructs no geometric PDE solution, Hamilton\n      identification or uniqueness bridge. Both Point-4 targets remain OPEN.\n      Historical source-head verification is distinct from combined-head\n      compilation, standard-axiom checks, completion audits and review.\n\n'
TREES.update({CONTRACTION_PARENT:CONTRACTION_PARENT_TREE,
              CONTRACTION_SOURCE:CONTRACTION_SOURCE_TREE, CONTRACTION_BASE:CONTRACTION_BASE_TREE})

def contraction_transform(path, original):
    assert path in CONTRACTION_ROOTS
    if path == HEAT_METADATA:
        anchor, addition = b'related_formalizations:\n', CONTRACTION_METADATA_NOTE.encode()
        assert original.count(anchor) == 1 and CONTRACTION_SOURCE.encode() not in original, 'Contraction provenance anchor drift'
        return original.replace(anchor, anchor+addition, 1)
    data = original
    for operation in CONTRACTION_OPERATIONS[path]:
        old, new = operation['old_utf8'].encode(), operation['new_utf8'].encode()
        if old:
            assert data.count(old) == 1, 'Contraction replacement anchor drift: '+path
            data = data.replace(old, new, 1)
        else:
            anchor = operation['anchor_utf8'].encode()
            assert data.count(anchor) == 1 and new not in data, 'Contraction insertion anchor drift: '+path
            data = data.replace(anchor, new+anchor, 1)
    return data

def contraction_inverse(path, actual):
    assert path in CONTRACTION_ROOTS
    original = git('show', CONTRACTION_PARENT+':'+path)
    assert blob_id(original) == parent_tree(CONTRACTION_PARENT)[path][1]
    assert actual == contraction_transform(path, original), 'Exact contraction root/provenance/scope drift: '+path
    return original

def contraction_identity(expected, originals, changes):
    base, source, merge_base = (parent_tree(c) for c in (CONTRACTION_PARENT, CONTRACTION_SOURCE, CONTRACTION_BASE))
    assert len(base) == 1730 and len(source) == 1570 and len(merge_base) == 1568
    assert {p for p in set(source)|set(merge_base) if source.get(p)!=merge_base.get(p)} == CONTRACTION_PATHS
    # Reconstruct all of the approved predecessor policy with its authentic old
    # digest before extending it. The new current helper cannot certify its base.
    old_helper = git('show', CONTRACTION_PARENT+':'+HELPER)
    assert blob_id(old_helper) == base[HELPER][1]
    old_digest = sha256(old_helper)
    prior_changes = {p:transform(p,originals[p],old_digest) for p in EDITED-{SMOOTH}}
    prior_changes[SMOOTH] = transform(SMOOTH,originals[SMOOTH],old_digest,
        sha256(prior_changes[FIXTURE]),sha256(prior_changes[WORKFLOW]))
    prior = resolve_union(parent_tree(MASTER),parent_tree(SUPPORT))
    prior.update({p:('100644',blob_id(b)) for p,b in prior_changes.items()})
    prior, _, _ = heat_identity(prior,dict(originals),dict(prior_changes))
    for p in NEW:prior[p]=base[p]
    assert prior == base, 'Published PR110 predecessor policy drift'
    assert not CONTRACTION_ADDED & set(base)
    for path in sorted(CONTRACTION_ADDED|CONTRACTION_REPLACED):
        assert source[path][0] == '100644'
        if path in CONTRACTION_REPLACED:
            assert base[path] == merge_base[path], 'Contraction replacement base drift: '+path
        else:
            assert path not in expected and path not in merge_base
        data = git('show',CONTRACTION_SOURCE+':'+path)
        assert blob_id(data) == source[path][1], 'Contraction source bytes drift: '+path
        expected[path] = source[path]; changes[path] = data
    for path in sorted(CONTRACTION_ROOTS):
        original = git('show',CONTRACTION_PARENT+':'+path)
        assert base[path] == ('100644',blob_id(original))
        assert changes[path] == original, 'Prior heat root reconstruction drift: '+path
        changes[path] = contraction_transform(path,original)
        expected[path] = '100644',blob_id(changes[path])
    assert len(expected) == 1728  # Two additions before the four NEW paths.
    return expected, originals, changes

def contraction_check_imports(local, actual):
    prior = contraction_inverse(HEAT_ROOT,actual)
    local.legacy_check_imports(heat_inverse(HEAT_ROOT,prior))
    base = local.blob(local.INTEGRATION_PARENT,HEAT_ROOT)
    local.check_imports(actual,contraction_transform(HEAT_ROOT,heat_transform(HEAT_ROOT,base)),base)

def contraction_check_metadata(local, actual):
    raw = actual.encode() if isinstance(actual,str) else actual
    prior = contraction_inverse(HEAT_METADATA,raw)
    local.legacy_check_metadata(heat_inverse(HEAT_METADATA,prior).decode())
    base = local.blob(local.INTEGRATION_PARENT,HEAT_METADATA)
    # Add both new entries only to the master input; keep literal notes unique.
    local.check_metadata(raw,contraction_transform(HEAT_METADATA,heat_transform(HEAT_METADATA,base)),base)


FIXED_PARENT = '5185860656456a078acef144772511b6f21428f6'
FIXED_PARENT_TREE = '1ef8247dd73c8c2baf1527cff36a78df06c7ac98'
FIXED_SOURCE = '58c6fc21bafeb8a659d6751a1a9db7a74127a300'
FIXED_SOURCE_TREE = '83037024feb3b82499385632c3eb535fca1cdcb7'
FIXED_BASE = '99aa49484f8decc5a6344591d5e319011ebea73b'
FIXED_BASE_TREE = 'dbb6b63ffcceed96ac133bc4f5e835e33fda2518'
FIXED_STATUS = 'docs/status.md'
FIXED_ADDED = {'curvature/scripts/point4_fixed_background_heat_probe.lean', 'docs/point4/fixed-background-heat.md', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatFixedBackgroundProducer.lean', '.github/workflows/point4-fixed-background-heat.yml', 'curvature/scripts/point4_fixed_background_heat_source_test.py'}
FIXED_ROOTS = {HEAT_ROOT,HEAT_METADATA,HEAT_DOC,FIXED_STATUS}
FIXED_PATHS = FIXED_ADDED | FIXED_ROOTS
FIXED_OPERATIONS = {'curvature/PoincareCurvature.lean': [{'kind': 'append-exact-branch-suffix', 'new_utf8': '\nimport PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFixedBackgroundProducer\n', 'count': 1, 'authenticated_old_context_utf8': '\nimport PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateCurvature\n'}], 'curvature/formalization.yaml': [{'kind': 'insert-before-anchor', 'anchor_utf8': '  - id: "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/73212853b1c48e5fea511191e89072dd003b2d0a/curvature"\n    relationship: "builds-on"\n', 'new_utf8': '  - id: "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/99aa49484f8decc5a6344591d5e319011ebea73b/curvature"\n    relationship: "builds-on"\n    note: >-\n      Immutable same-repository source for the existing global C2 affine\n      connection constructor in CovariantDerivative/LeviCivita.lean, induced\n      tensor-connection regularity in InducedHomRegularity.lean, actual\n      geometric tensor-heat coefficient regularity, and scale-correct\n      zero-trace local right-inverse in TensorHeatCoefficientLocalization.lean.\n      The new TensorHeatFixedBackgroundProducer.lean composes those actual\n      constructors for the literal supplied arbitrary C2 metric and chooses\n      one global auxiliary connection before all chart/interval choices.\n      Existing implementation, contributor notices and registry selection\n      remain unchanged. This is supporting local linear theory, not a new\n      selected registry entry or a Ricci-flow/PDE existence claim.\n', 'count': 1}, {'kind': 'already-applied', 'old_utf8': '    - method: "agent-assisted"\n', 'new_utf8': '    - method: "agent"\n', 'count': 1}], 'docs/point4/README.md': [{'kind': 'append-exact-branch-suffix', 'new_utf8': '\nThe fixed-background local-heat candidate composes the existing global C²\nauxiliary-connection constructor with actual coefficient regularity and\nscale-correct zero-trace local right-inverses for the literal arbitrary C²\nmetric. No connection, induced-regularity, coefficient-regularity or solver\nwitness is an input. Its stronger `I.Boundaryless` and unweighted Hölder source\nscope remain explicit; exact Lean-4.33 verification is pending. See\n[the precise local linear boundary](fixed-background-heat.md).\nThe canonical Point-4 theorem and **OPEN** verdict remain unchanged.\n', 'count': 1, 'authenticated_old_context_utf8': 'Exact Lean-4.33 compilation is pending; the Lie/DeTurck, analytic and PDE\nboundaries and the Point-4 **OPEN** verdict remain.\n'}], 'docs/status.md': [{'kind': 'append-exact-branch-suffix', 'new_utf8': '\nThe fixed-background local-heat candidate composes the existing global C²\nauxiliary-connection constructor with actual coefficient regularity and\nscale-correct zero-trace local right-inverses for the literal arbitrary C²\nmetric. No connection, induced-regularity, coefficient-regularity or solver\nwitness is an input. Its stronger `I.Boundaryless` and unweighted Hölder source\nscope remain explicit; exact Lean-4.33 verification is pending. See\n[the precise local linear boundary](point4/fixed-background-heat.md).\nThe canonical Point-4 theorem and **OPEN** verdict remain unchanged.\n', 'count': 1, 'authenticated_old_context_utf8': '5. preserve partial or failed approaches in `docs/history/` only when they are\n   useful research records.\n'}]}
FIXED_METADATA_NOTE = '  - id: "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/58c6fc21bafeb8a659d6751a1a9db7a74127a300/curvature"\n    relationship: "builds-on"\n    note: >-\n      Immutable PR126 source for TensorHeatFixedBackgroundProducer.lean,\n      scripts/point4_fixed_background_heat_probe.lean, the original source\n      regression, proof workflow and precise fixed-background heat scope.\n      The literal supplied C2 metric, constructed global auxiliary connection,\n      actual coefficient regularity, scale-correct localized zero-trace\n      right-inverse, proofs and contributor notices are inherited unchanged.\n      Finite source composition, import/provenance reconciliation and bounded\n      regression routing are the integration additions. The newer baseline\n      TensorHeatGeometricRegularity.lean is preserved and needs focused native\n      qualification against its actual bytes. No nonlinear Ricci-flow solver,\n      Hamilton identification, gauge or uniqueness bridge is constructed.\n      Historical source-head proof evidence does not qualify the combined\n      checkout. Both Point-4 targets remain OPEN; registry selection is unchanged.\n\n'
TREES.update({FIXED_PARENT:FIXED_PARENT_TREE,FIXED_SOURCE:FIXED_SOURCE_TREE,FIXED_BASE:FIXED_BASE_TREE})

def fixed_transform(path, original):
    assert path in FIXED_ROOTS
    data=original
    for op in FIXED_OPERATIONS[path]:
        new=op['new_utf8'].encode()
        if op['kind']=='already-applied':
            assert op['old_utf8'].encode() not in data and data.count(new)==1, 'Fixed-background method drift'
        elif op['kind']=='append-exact-branch-suffix':
            assert data.endswith(b'\n') and new not in data, 'Fixed-background suffix drift: '+path
            data+=new
        else:
            assert op['kind']=='insert-before-anchor'
            anchor=op['anchor_utf8'].encode()
            assert anchor and data.count(anchor)==1 and new not in data, 'Fixed-background provenance anchor drift'
            data=data.replace(anchor,new+anchor,1)
    if path==HEAT_METADATA:
        anchor=b'related_formalizations:\n';note=FIXED_METADATA_NOTE.encode()
        assert data.count(anchor)==1 and FIXED_SOURCE.encode() not in data, 'Fixed-background source provenance drift'
        data=data.replace(anchor,anchor+note,1)
    return data

def fixed_inverse(path, actual):
    assert path in FIXED_ROOTS and re.fullmatch(r'[0-9a-f]{40}',FIXED_PARENT or '')
    original=git('show',FIXED_PARENT+':'+path)
    assert parent_tree(FIXED_PARENT)[path]==('100644',blob_id(original))
    assert actual==fixed_transform(path,original), 'Exact fixed-background root/provenance/scope drift: '+path
    return original

def fixed_identity(expected, originals, changes):
    assert re.fullmatch(r'[0-9a-f]{40}',FIXED_PARENT or ''), 'Actual repaired PR115 commit pin is required'
    base,source,merge_base=(parent_tree(c) for c in (FIXED_PARENT,FIXED_SOURCE,FIXED_BASE))
    assert len(base)==1732 and len(source)==1607 and len(merge_base)==1602
    assert {p for p in set(source)|set(merge_base) if source.get(p)!=merge_base.get(p)}==FIXED_PATHS
    old_helper=git('show',FIXED_PARENT+':'+HELPER)
    assert base[HELPER]==('100644',blob_id(old_helper))
    old_digest=sha256(old_helper)
    prior_changes={p:transform(p,originals[p],old_digest) for p in EDITED-{SMOOTH}}
    prior_changes[SMOOTH]=transform(SMOOTH,originals[SMOOTH],old_digest,
        sha256(prior_changes[FIXTURE]),sha256(prior_changes[WORKFLOW]))
    prior=resolve_union(parent_tree(MASTER),parent_tree(SUPPORT))
    prior.update({p:('100644',blob_id(b)) for p,b in prior_changes.items()})
    prior,prior_originals,prior_final_changes=heat_identity(prior,dict(originals),dict(prior_changes))
    prior,_,_=contraction_identity(prior,prior_originals,prior_final_changes)
    for p in NEW:prior[p]=base[p]
    assert prior==base,'Repaired PR115 complete predecessor policy drift'
    assert not FIXED_ADDED&set(base)
    for path in sorted(FIXED_ADDED):
        assert path not in expected and path not in merge_base and source[path][0]=='100644'
        data=git('show',FIXED_SOURCE+':'+path)
        assert blob_id(data)==source[path][1], 'Fixed-background branch bytes drift: '+path
        changes[path]=data;expected[path]=source[path]
    for path in sorted(FIXED_ROOTS):
        original=git('show',FIXED_PARENT+':'+path)
        assert base[path]==('100644',blob_id(original))
        if path!=FIXED_STATUS:assert changes[path]==original, 'Prior contraction root reconstruction drift: '+path
        else:assert expected[path]==base[path], 'Fixed-background status predecessor drift'
        changes[path]=fixed_transform(path,original)
        expected[path]='100644',blob_id(changes[path])
    assert len(expected)==1733 # Five additions before the four externally bound NEW paths.
    return expected,originals,changes

def fixed_check_imports(local, actual):
    prior=fixed_inverse(HEAT_ROOT,actual)
    local.legacy_check_imports(heat_inverse(HEAT_ROOT,contraction_inverse(HEAT_ROOT,prior)))
    base=local.blob(local.INTEGRATION_PARENT,HEAT_ROOT)
    local.check_imports(actual,fixed_transform(HEAT_ROOT,
        contraction_transform(HEAT_ROOT,heat_transform(HEAT_ROOT,base))),base)

def fixed_check_metadata(local, actual):
    raw=actual.encode() if isinstance(actual,str) else actual
    prior=fixed_inverse(HEAT_METADATA,raw)
    local.legacy_check_metadata(heat_inverse(HEAT_METADATA,contraction_inverse(HEAT_METADATA,prior)).decode())
    base=local.blob(local.INTEGRATION_PARENT,HEAT_METADATA)
    local.check_metadata(raw,fixed_transform(HEAT_METADATA,
        contraction_transform(HEAT_METADATA,heat_transform(HEAT_METADATA,base))),base)

# BEGIN authenticated finite tensor extension
TENSOR_PARENT = '40dc2d8a2e50161fdd51ccf1b858d941a5949b3b'
TENSOR_SOURCE = 'c79ff28d5f1d4ca10613c7417b1e22a65ac4eaa9'
TENSOR_BASE = '13fa15d6a8352ed08bf71b3533b1c2e922c21388'
TENSOR_DEPENDENCY = '67548685d8bf842eef18f74139c734d49936c179'
TENSOR_TREES = {'40dc2d8a2e50161fdd51ccf1b858d941a5949b3b': '859824bbde4983cc59087799e4f4c9894f5ae6a8', 'c79ff28d5f1d4ca10613c7417b1e22a65ac4eaa9': 'eea916e4ebcdb9dfd7bf01d971a37ea84478f7ea', '13fa15d6a8352ed08bf71b3533b1c2e922c21388': '1258b799cd16e954a97518531c070c6b67d7fcbc', '67548685d8bf842eef18f74139c734d49936c179': '2afb1c1eda1340c865f4ec6ce50e1773866ce207'}
TENSOR_MECHANICAL = '.github/workflows/symmetric-tensor-heat-palomar-mechanical.yml'
TENSOR_PATHS = {'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionTensorRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacian.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/VectorValuedBilinearPairing.lean', 'symmetric-tensor-heat/lake-manifest.json', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarEvolution.lean', 'symmetric-tensor-heat/VERIFICATION.md', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2CoordinateBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/BilinearEvaluation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckQuadraticRemainderAlgebra.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/LeastEigenvalue.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyScalarC2Regularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasAffineCorrection.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderCommutatorSeminorm.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteSourceExtension.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckHolderDifference.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorialCommutator.lean', 'symmetric-tensor-heat/lakefile.toml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/MetricInverseVariation.lean', 'symmetric-tensor-heat/lean-toolchain', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/UniformSmallness.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyManifoldLieBracketMixedRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/DuhamelLocalExistence.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponentsLowering.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricDefectTensorDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/HomBundleComp.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponentsSliceRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2FlowBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowMilestone41.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/LocalExtremaSecondDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/TimeAugmentedDeTurckODE.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceAssembly.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/StandardDeTurckCoordinateAlgebra.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalChosenBackground.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatSemigroupCommutator.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderCommutatorSeminormControl.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/JointSpatialMVFDeriv.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellationLaplacian.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2PicardRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorGramCovariantDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalAssemblyBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponents.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellationTrace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/MixedTimeSpace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/FixedTensorHeatUniqueness.lean', '.github/workflows/symmetric-tensor-heat-palomar-current.yml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanSection.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatGeometricRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/DuhamelContraction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacianMaximum.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceRegularityBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasShortCommutatorLift.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaCorrectionKoszul.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckCorrectionBackground.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacianProduct.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Bianchi.lean', 'symmetric-tensor-heat/scripts/verify-comparator.sh', 'symmetric-tensor-heat/RESEARCH_INTEREST.md', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorNormSq.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckFiberMap.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TangentFrameCoordinate.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionMetricDefect.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciNorm.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMovingConnectionVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Existence.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFixedTimeRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/TorsionFreeAuxiliaryBackground.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowCoherentModelComparison.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurck.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/NemytskiiChainRule.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/RieszMapC3Regularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyDerivedMovingConnectionVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupportLaplacian.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckLittleHolderDuhamel.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowCutoffComparison.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/EndomorphismTrace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GeometricDuhamelData.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarOpenInitialPotential.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/ModelGaugeFlowODE.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicTraceGeometry.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalTimeBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyLieBracketMixedRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicEndpointRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/RiccatiBarrier.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaCorrectionDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ConcreteRicciDeTurck.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HomEvaluation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderHeatSemigroupRestriction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderJointContinuity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciConnectionChange.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianIntrinsic.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/InducedHomRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricTensorCurvatureAction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatPropagatorData.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowModelComparison.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianLocalFrame.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckBackgroundAssembly.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceRegularityC3.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TaylorCommutatorPointwise.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCorrectionFunctionalSliceRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatEuclidean.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiClosureC11.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchiUnconditional.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckLinearization.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointFieldCompactGaugeFlow.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyOperatorC2Regularity.lean', 'symmetric-tensor-heat/PROVENANCE.md', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckWitnessPhase1.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowTimeDerivative.lean', 'symmetric-tensor-heat/TensorHeatSolution.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckRaisedCompactGaugeFlow.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/NormalizedCutoff.lean', '.github/workflows/symmetric-tensor-heat-palomar-render.yml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasGeometricUniqueness.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckMatrixLittleHolderClosure.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalBracketBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSectionCore.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckLittleHolderOutput.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckNemytskii.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckJointRegularity.lean', '.github/workflows/symmetric-tensor-heat-palomar-mechanical.yml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckOperatorLipschitz.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatLocalReconstruction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckIntrinsicTraceDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyScalarBarrier.lean', 'symmetric-tensor-heat/scripts/check-closed-statement.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointOneFormRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/InitialValueProblemBackground.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckCorrectionRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckEquation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/InverseGramDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupportEvolution.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMixedRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TorsionRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianCoordinate.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TraceLaplacian.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCoordinatePicardEstimates.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/DowngradeNormFree.lean', 'symmetric-tensor-heat/README.md', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckHolderSmoothing.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/TensorHeatNormMaximum.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionLocalFrame.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderComposition.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorDivergence.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasClosedReconstruction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/VectorValuedBilinearFrameCoordinate.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianTraceFreezing.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacian.lean', 'symmetric-tensor-heat/comparator.json', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyKoszulVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyRicciC2Regularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteCylinderInterpolation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiClosure.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ThreeDimensionalRicciNorm.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/RicciCorrectionDerivativeExpansion.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckPrincipalPart.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckPicardRegularityReduction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarParabolicInvariant.lean', 'symmetric-tensor-heat/TensorHeatGeometricSymmetry.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyOperatorLaplacian.lean', 'symmetric-tensor-heat/REVIEW_REMEDIATION.md', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciDerivativeTrace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/MatrixInverseDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyParabolic.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatKernel1D.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderHeatSemigroup.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckDerivativeExpansion.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckTraceDerivative.lean', 'symmetric-tensor-heat/scripts/check-challenge-boundary.py', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyKoszul.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/JointSpatialDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyGeometricEvolution.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicGeometricEvolution.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckBackgroundFormula.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchiBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HrangeDischarge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TranslationMeasurability.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricDefectLocalFrame.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorNormSqLocalFrame.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/InitialValueProblemBackgroundTorsion.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyConnectionVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicConnectionVariation.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFixedTimeC2CoordinateBridge.lean', '.github/workflows/symmetric-tensor-heat-palomar-current-render.yml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/MetricFamilyLocalFrameGram.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarOpenInitialInvariant.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteInitialTrace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalDataBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAuxiliaryBackground.lean', 'symmetric-tensor-heat/vendor/curvature/lake-manifest.json', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/InterpolationLemma.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineC2AlphaDomain.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderDuhamel.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/FirstOrderParallelExtension.lean', 'symmetric-tensor-heat/scripts/check-package.py', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalWitness.lean', 'symmetric-tensor-heat/TensorHeatChallenge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/CovariantTwoTensorConnectionChange.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/ModelGaugeFlowODECore.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RaisedRicci.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderDuhamelInstance.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/RieszCovariantDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupport.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatSemigroupVariance.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/JointRegularityUpgrade.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasShortContraction.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySpectrum.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianChart.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ThreeDimensionalDecomposition.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreMetricCurvature.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/BanachSpace.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/AffineMetricTraceDerivative.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/BackgroundNormalFrameBridge.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/CompactCoefficientExtension.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckHessianPrincipalCore.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionSymmetry.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/FiniteTensorHeatUniqueness.lean', 'symmetric-tensor-heat/scripts/check-provenance.py', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMetricMixedRegularity.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean', 'symmetric-tensor-heat/formalization.yaml', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/InducedHomCurvature.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ConnectionChange.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/MatrixC0Alpha.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiPath.lean', 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarParabolicBarrier.lean'}
TENSOR_DELTA = {'.github/workflows/symmetric-tensor-heat-palomar-current-render.yml': {'before': None, 'source': ['100644', 'f32b2fdeb0083ceb9db612c1d8ea833af84d0c16'], 'final': ['100644', 'f32b2fdeb0083ceb9db612c1d8ea833af84d0c16'], 'resolution': 'exact-source'}, '.github/workflows/symmetric-tensor-heat-palomar-current.yml': {'before': None, 'source': ['100644', 'fa8df09e3c42889cdb01ab375fa7cad80f201c99'], 'final': ['100644', '413224c930a5efb13a4f7ce61d9747f5d33a82d9'], 'resolution': 'exact-boundary-workflow-integration'}, '.github/workflows/symmetric-tensor-heat-palomar-mechanical.yml': {'before': ['100644', 'bd64285830e359d22ca07cdc05b56389231ca43e'], 'source': ['100644', 'abe40ff3d7affe682b1ad121a242be7b50e76df8'], 'final': ['100644', '4a2a9e7e367af6d1d873a2451acbf0fb5803ea6f'], 'resolution': 'preserve-qualified-master'}, '.github/workflows/symmetric-tensor-heat-palomar-render.yml': {'before': ['100644', '46b8c33a2e2846ec3c1e081d712b9cc3d1252d23'], 'source': ['100644', '6d6cb4b169ed1b8ed17f63a48fdbbc3751131ea7'], 'final': ['100644', '46b8c33a2e2846ec3c1e081d712b9cc3d1252d23'], 'resolution': 'preserve-qualified-master'}, 'symmetric-tensor-heat/PROVENANCE.md': {'before': ['100644', 'bb36b1ea70a2b795cf0a30218a047b27dfe55f54'], 'source': ['100644', '8bb4943f995777739391e7c647e04ebb5ccb4efb'], 'final': ['100644', '8bb4943f995777739391e7c647e04ebb5ccb4efb'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/README.md': {'before': ['100644', '06f4bb78d5aa001eb592163dd7dd5325efde2ada'], 'source': ['100644', '351bbf107f7fc12841c6323ba096d6ae3f0edc65'], 'final': ['100644', '351bbf107f7fc12841c6323ba096d6ae3f0edc65'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/RESEARCH_INTEREST.md': {'before': ['100644', '037f8add8ded54b4c1f770fd90187312757616b0'], 'source': ['100644', '19150576d0aa666bac0baa679979b3e74be1aed8'], 'final': ['100644', '19150576d0aa666bac0baa679979b3e74be1aed8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/REVIEW_REMEDIATION.md': {'before': ['100644', 'a5a41ca5c24514408e84ad323059c2fb8e67ad3e'], 'source': ['100644', '4902954b61d5add31770a08aa09a226bbfefe067'], 'final': ['100644', '4902954b61d5add31770a08aa09a226bbfefe067'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/TensorHeatChallenge.lean': {'before': ['100644', '4e4bb907023d614cd49aa21774d3bbbe8626e07b'], 'source': ['100644', '1c297dc74606b594d39be7c45f8fa9454d350383'], 'final': ['100644', '1c297dc74606b594d39be7c45f8fa9454d350383'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/TensorHeatGeometricSymmetry.lean': {'before': ['100644', '0c870113ffe2709e8bb41a6fa8c85bab72022888'], 'source': ['100644', '18f12d3162ac5bce3c786e0847ffe0f0e6964a8a'], 'final': ['100644', '18f12d3162ac5bce3c786e0847ffe0f0e6964a8a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/TensorHeatSolution.lean': {'before': ['100644', 'a9ca92609ba20bb45076ca29362bede8c5bb4622'], 'source': ['100644', '0c39a49bb8afe90a5d86c5e46a63ec704b6c17a5'], 'final': ['100644', '0c39a49bb8afe90a5d86c5e46a63ec704b6c17a5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/VERIFICATION.md': {'before': ['100644', '7617ede89932c95a0d1b913fa92eb9d074126ead'], 'source': ['100644', 'c2130da1b1c29517f96be5bee9e99a0ae266b761'], 'final': ['100644', 'c2130da1b1c29517f96be5bee9e99a0ae266b761'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/comparator.json': {'before': ['100644', '4aec7f2f3be2734e2a1139735bca2e2c111807f5'], 'source': ['100644', 'd4c7423c60d3fa7b819f9c10236da37cad635c62'], 'final': ['100644', 'd4c7423c60d3fa7b819f9c10236da37cad635c62'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/formalization.yaml': {'before': ['100644', 'ec9f62c6d013953e855e00ef2d681efecdf5ec6f'], 'source': ['100644', 'f3a740610b07a81f9f69827284ca808dc5e7983c'], 'final': ['100644', 'f3a740610b07a81f9f69827284ca808dc5e7983c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/lake-manifest.json': {'before': ['100644', '5425ac207789096750810fd8f11acc41cc1f8e24'], 'source': ['100644', '61fe43bd98714234230f5d9187b317acbe52246b'], 'final': ['100644', '61fe43bd98714234230f5d9187b317acbe52246b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/lakefile.toml': {'before': ['100644', '91a3803db67477d3ccd623e0b615169a8f7790eb'], 'source': ['100644', '5a441df84f18ced57631fc0a2401f1c464bdefde'], 'final': ['100644', '5a441df84f18ced57631fc0a2401f1c464bdefde'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/lean-toolchain': {'before': ['100644', '025e59548e48cf71f2744154e2890beefe30a258'], 'source': ['100644', 'acc704ffe6eefbbe8ec09452a276202748aac923'], 'final': ['100644', 'acc704ffe6eefbbe8ec09452a276202748aac923'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/scripts/check-challenge-boundary.py': {'before': ['100644', 'd535ad69b0de1e2f86ba3e61755e43cccaea4df5'], 'source': ['100644', 'fc1005c1487c508c374202cf8fb28330cb7d40bd'], 'final': ['100644', 'fc1005c1487c508c374202cf8fb28330cb7d40bd'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/scripts/check-closed-statement.lean': {'before': ['100644', '4a4c4b88f622f5a61f49aeb6d765b8185243dc2a'], 'source': ['100644', '0f69ca1e31e1a637f7f0e0f84103c728c8e66316'], 'final': ['100644', '0f69ca1e31e1a637f7f0e0f84103c728c8e66316'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/scripts/check-package.py': {'before': ['100644', '6de443afcc5054c81ff9935c4930695ce215fcb5'], 'source': ['100644', '2264c20780ad35ee8bffdb067695f199fe7ac27e'], 'final': ['100644', '35eb56a53b2d2b706cf536907ca0da45d015c89b'], 'resolution': 'exact-count-one-workflow-guard'}, 'symmetric-tensor-heat/scripts/check-provenance.py': {'before': ['100644', '45f605d7c729249b505196e83b8242dceaf0b620'], 'source': ['100644', '9b173d7f68b2eb467baace5ce61bcff0dcc15aac'], 'final': ['100644', '9b173d7f68b2eb467baace5ce61bcff0dcc15aac'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/scripts/verify-comparator.sh': {'before': ['100755', 'c772acf9df591556705dae91776330e851e8aab1'], 'source': ['100755', '8f9ab0c0e3d04e17482e46c77ae518e93a3f912d'], 'final': ['100755', '8f9ab0c0e3d04e17482e46c77ae518e93a3f912d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature.lean': {'before': ['100644', '38201aeb9f4bb2820563969291a9a34a509c047d'], 'source': ['100644', '45e30a0ba98177371ce47a991dde1c35aed3f196'], 'final': ['100644', '45e30a0ba98177371ce47a991dde1c35aed3f196'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/JointSpatialDerivative.lean': {'before': None, 'source': ['100644', '9d4c94d31c0451aadb1482c6d34d245b5e3a992d'], 'final': ['100644', '9d4c94d31c0451aadb1482c6d34d245b5e3a992d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/JointSpatialMVFDeriv.lean': {'before': None, 'source': ['100644', 'dd00eda63904a892967c5e46e52ad0d97e913474'], 'final': ['100644', 'dd00eda63904a892967c5e46e52ad0d97e913474'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/LeastEigenvalue.lean': {'before': None, 'source': ['100644', '83d7e38940d1cc9a6b6dfc237deb0de7853c43d9'], 'final': ['100644', '83d7e38940d1cc9a6b6dfc237deb0de7853c43d9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/LocalExtremaSecondDerivative.lean': {'before': None, 'source': ['100644', 'e65812a52050cc8131a41550b975d3f9b4475ab2'], 'final': ['100644', 'e65812a52050cc8131a41550b975d3f9b4475ab2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/MatrixInverseDerivative.lean': {'before': None, 'source': ['100644', '546ce5745ffda9053cd39c430bc9241afbff7a60'], 'final': ['100644', '546ce5745ffda9053cd39c430bc9241afbff7a60'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/MixedTimeSpace.lean': {'before': None, 'source': ['100644', 'b71cdbc502da0ba50dcc2f18b872e7f559ba8c52'], 'final': ['100644', 'b71cdbc502da0ba50dcc2f18b872e7f559ba8c52'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Analysis/RiccatiBarrier.lean': {'before': None, 'source': ['100644', 'fcdc75c88d3755c59a5061f2be83f10e49a75fe9'], 'final': ['100644', 'fcdc75c88d3755c59a5061f2be83f10e49a75fe9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ConcreteRicciDeTurck.lean': {'before': None, 'source': ['100644', 'c04760e40539291da3ec4ca92f42c7dff60ebf40'], 'final': ['100644', 'c04760e40539291da3ec4ca92f42c7dff60ebf40'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/DuhamelContraction.lean': {'before': None, 'source': ['100644', 'cb69f9247deb1ac099ff08328f0c458fbffada51'], 'final': ['100644', 'cb69f9247deb1ac099ff08328f0c458fbffada51'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/DuhamelLocalExistence.lean': {'before': None, 'source': ['100644', '85649e7cdfc6dc74e95ff032a7cdcabc0f5a1e79'], 'final': ['100644', '85649e7cdfc6dc74e95ff032a7cdcabc0f5a1e79'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanSection.lean': {'before': None, 'source': ['100644', '1e8273e04f0b3b92c88213309cbb729ac51baa6c'], 'final': ['100644', '1e8273e04f0b3b92c88213309cbb729ac51baa6c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/FiniteTensorHeatUniqueness.lean': {'before': None, 'source': ['100644', '2f821d97348b2ca436f77e3b711c04a758cc605b'], 'final': ['100644', '2f821d97348b2ca436f77e3b711c04a758cc605b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineC2AlphaDomain.lean': {'before': None, 'source': ['100644', 'ad07de8ee22021b795121c569f7320fada916d22'], 'final': ['100644', 'ad07de8ee22021b795121c569f7320fada916d22'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckFiberMap.lean': {'before': None, 'source': ['100644', 'a5cbf7bc8362c80fe0c7e62b2fb5eab91cec2b1c'], 'final': ['100644', 'a5cbf7bc8362c80fe0c7e62b2fb5eab91cec2b1c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckHolderDifference.lean': {'before': None, 'source': ['100644', 'b6f83ccbf7c58d692ad9b5796a01322fbef6bbf7'], 'final': ['100644', 'b6f83ccbf7c58d692ad9b5796a01322fbef6bbf7'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckLittleHolderDuhamel.lean': {'before': None, 'source': ['100644', '8ebf7ee8a7a7d1ae166495222adff13628f9b488'], 'final': ['100644', '8ebf7ee8a7a7d1ae166495222adff13628f9b488'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckLittleHolderOutput.lean': {'before': None, 'source': ['100644', '432a6dfdfd2e0c0e7c6dad81917e1558350c56f0'], 'final': ['100644', '432a6dfdfd2e0c0e7c6dad81917e1558350c56f0'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckMatrixLittleHolderClosure.lean': {'before': None, 'source': ['100644', '2d3cb87cbe023104650cf2e5f5127d1da8d32ee1'], 'final': ['100644', '2d3cb87cbe023104650cf2e5f5127d1da8d32ee1'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GenuineRicciDeTurckNemytskii.lean': {'before': None, 'source': ['100644', '1778508d5383dd5d490a93726e176b155b020c22'], 'final': ['100644', '1778508d5383dd5d490a93726e176b155b020c22'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/GeometricDuhamelData.lean': {'before': None, 'source': ['100644', '876d791a7eb9ce15a5f2d9512f0ba82281f6740c'], 'final': ['100644', '876d791a7eb9ce15a5f2d9512f0ba82281f6740c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatKernel1D.lean': {'before': ['100644', '9bfa7841809cef83dfa8551827ee825a847d50c6'], 'source': ['100644', 'f2bd8a7a761284f03bf882097b0792e03ac71cfb'], 'final': ['100644', 'f2bd8a7a761284f03bf882097b0792e03ac71cfb'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatPropagatorData.lean': {'before': None, 'source': ['100644', '01ca3aeeefd57c6290b47196148b76afd435766e'], 'final': ['100644', '01ca3aeeefd57c6290b47196148b76afd435766e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatSemigroupCommutator.lean': {'before': None, 'source': ['100644', '73ef2ac0fc950ebed7e5de0ddcb1087603d27ba4'], 'final': ['100644', '73ef2ac0fc950ebed7e5de0ddcb1087603d27ba4'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatSemigroupVariance.lean': {'before': None, 'source': ['100644', '1b9aacdacde2238b28f910f846428916b7ce35c9'], 'final': ['100644', '1b9aacdacde2238b28f910f846428916b7ce35c9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderCommutatorSeminorm.lean': {'before': None, 'source': ['100644', '2ce58e5f482500d215e316ca980f03b0ec74cd11'], 'final': ['100644', '2ce58e5f482500d215e316ca980f03b0ec74cd11'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderCommutatorSeminormControl.lean': {'before': None, 'source': ['100644', 'aac984fc17cfde14880e710f5ddb7b1c12e4c2b2'], 'final': ['100644', 'aac984fc17cfde14880e710f5ddb7b1c12e4c2b2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderComposition.lean': {'before': None, 'source': ['100644', 'cc02cce8a808abc82db609f5b4bbdbf53bf188a9'], 'final': ['100644', 'cc02cce8a808abc82db609f5b4bbdbf53bf188a9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderHeatSemigroup.lean': {'before': None, 'source': ['100644', '8f22251e27412b464688c82d1085763bb22b1dfe'], 'final': ['100644', '8f22251e27412b464688c82d1085763bb22b1dfe'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HolderHeatSemigroupRestriction.lean': {'before': None, 'source': ['100644', '2dd728212e7ceb1d00a5cc90919b7f1c3e1d038e'], 'final': ['100644', '2dd728212e7ceb1d00a5cc90919b7f1c3e1d038e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HrangeDischarge.lean': {'before': None, 'source': ['100644', 'b8d721ee23ec85f8a9b0c790e8cd03e69c116f51'], 'final': ['100644', 'b8d721ee23ec85f8a9b0c790e8cd03e69c116f51'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/InterpolationLemma.lean': {'before': None, 'source': ['100644', 'fd5afddafbdfb8e23ca6d05a55dfec43c29cb61d'], 'final': ['100644', 'fd5afddafbdfb8e23ca6d05a55dfec43c29cb61d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/JointRegularityUpgrade.lean': {'before': None, 'source': ['100644', 'd1565efc76bd5ac972fb3a9b64f36c234e0ca3e4'], 'final': ['100644', 'd1565efc76bd5ac972fb3a9b64f36c234e0ca3e4'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderDuhamel.lean': {'before': None, 'source': ['100644', '8923b301aee0a1faf2242e5607d553c1f9d454bd'], 'final': ['100644', '8923b301aee0a1faf2242e5607d553c1f9d454bd'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderDuhamelInstance.lean': {'before': None, 'source': ['100644', '05121a9562876342fd8bf9b36f848e160ff6d8c8'], 'final': ['100644', '05121a9562876342fd8bf9b36f848e160ff6d8c8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderJointContinuity.lean': {'before': None, 'source': ['100644', '12e70eadc71d12720b81056317bf060c628a6d14'], 'final': ['100644', '12e70eadc71d12720b81056317bf060c628a6d14'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiClosure.lean': {'before': None, 'source': ['100644', '64aed6cb7d51756cbee7e1519954acb3111387e0'], 'final': ['100644', '64aed6cb7d51756cbee7e1519954acb3111387e0'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiClosureC11.lean': {'before': None, 'source': ['100644', 'b689c2f526f61bb87638c7ffe0085befd37a4d88'], 'final': ['100644', 'b689c2f526f61bb87638c7ffe0085befd37a4d88'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/LittleHolderNemytskiiPath.lean': {'before': None, 'source': ['100644', '0f7d1efa6c76cdd1375304c9871fa7623fb3c067'], 'final': ['100644', '0f7d1efa6c76cdd1375304c9871fa7623fb3c067'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/MetricFamilyLocalFrameGram.lean': {'before': None, 'source': ['100644', '895dce8fe14c631ee2d0d90159a13a00a98d0da5'], 'final': ['100644', '895dce8fe14c631ee2d0d90159a13a00a98d0da5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/NemytskiiChainRule.lean': {'before': None, 'source': ['100644', '7c7f1ef3d69c2c47c731102c885cdec454e295f8'], 'final': ['100644', '7c7f1ef3d69c2c47c731102c885cdec454e295f8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/BanachSpace.lean': {'before': ['100644', '99daabe4776341a63060d4324f65ba8fa12b5dc3'], 'source': ['100644', '358d904668bc027f78eb3ae5f78fce844c94ad68'], 'final': ['100644', '358d904668bc027f78eb3ae5f78fce844c94ad68'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/CompactCoefficientExtension.lean': {'before': ['100644', '784dafd415e4aec4db75ab1d19c9e8c5365074f5'], 'source': ['100644', 'd6019d5bd14690d4d17ad34e358dc0bdcf5ce86c'], 'final': ['100644', 'd6019d5bd14690d4d17ad34e358dc0bdcf5ce86c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteCylinderInterpolation.lean': {'before': ['100644', 'e16ed1392ef39aa021b8b73a689aaa8fc42a6421'], 'source': ['100644', 'bed6cc555ecee8582f75faa6eb2ad63cdb3e42c9'], 'final': ['100644', 'bed6cc555ecee8582f75faa6eb2ad63cdb3e42c9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteInitialTrace.lean': {'before': ['100644', '9fa7cc55fa6182102e68081ac473bc4337f0051b'], 'source': ['100644', 'a323d548ed0788ac9f8e3cfe30439b9491d87733'], 'final': ['100644', 'a323d548ed0788ac9f8e3cfe30439b9491d87733'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteSourceExtension.lean': {'before': ['100644', '56bd21047acc41c434f1c55e8cc7fbb9ebead143'], 'source': ['100644', '2a06377287e313e0e389e1b982a6e367e15e6161'], 'final': ['100644', '2a06377287e313e0e389e1b982a6e367e15e6161'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/MatrixC0Alpha.lean': {'before': ['100644', 'a4f2b016ae974f8d86f619b8d838aef99dc0d3a7'], 'source': ['100644', 'b344e08b0bd7c0de3e40933c75c2ec483ac70dbf'], 'final': ['100644', 'b344e08b0bd7c0de3e40933c75c2ec483ac70dbf'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/NormalizedCutoff.lean': {'before': ['100644', '7839722bf213ea31339094e9bd3a8deda0602a40'], 'source': ['100644', '8fbbd5ef126cddccaa210100b3d9d3fe86725290'], 'final': ['100644', '8fbbd5ef126cddccaa210100b3d9d3fe86725290'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckHolderSmoothing.lean': {'before': None, 'source': ['100644', '3796fc0e114a22d1a14332e658d3f878c03ade14'], 'final': ['100644', '3796fc0e114a22d1a14332e658d3f878c03ade14'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckLinearization.lean': {'before': None, 'source': ['100644', '4904b7a825b0b4a09cc86371fe6d7c91ff256071'], 'final': ['100644', '4904b7a825b0b4a09cc86371fe6d7c91ff256071'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/RicciDeTurckOperatorLipschitz.lean': {'before': None, 'source': ['100644', '7be848f7ff29a87932d8388eac7abe655b89d0d5'], 'final': ['100644', '7be848f7ff29a87932d8388eac7abe655b89d0d5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean': {'before': ['100644', 'f51be67d184f62539a2eb048b6d0473f46de8e9b'], 'source': ['100644', '0d9704c96ed3dcd7213e37f66ec9e8afbb039659'], 'final': ['100644', '0d9704c96ed3dcd7213e37f66ec9e8afbb039659'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/StandardDeTurckCoordinateAlgebra.lean': {'before': None, 'source': ['100644', '05ef1d798c169943dab736d86ba07dc52230926f'], 'final': ['100644', '05ef1d798c169943dab736d86ba07dc52230926f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TaylorCommutatorPointwise.lean': {'before': None, 'source': ['100644', '843c31250c4f575004ffb3b4c861086f934d1507'], 'final': ['100644', '843c31250c4f575004ffb3b4c861086f934d1507'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasAffineCorrection.lean': {'before': ['100644', 'bfeb1fe279d66937996f34ff0147cba073fd8af4'], 'source': ['100644', 'f5ebb88fa6a5449de5dbacf73d41da54a38dd8ee'], 'final': ['100644', 'f5ebb88fa6a5449de5dbacf73d41da54a38dd8ee'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasClosedReconstruction.lean': {'before': None, 'source': ['100644', 'e977362d3600e3a08d7acee57a90b37d0f3e3b1c'], 'final': ['100644', 'e977362d3600e3a08d7acee57a90b37d0f3e3b1c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasGeometricUniqueness.lean': {'before': None, 'source': ['100644', '02fd1a04ca9d6541ea00cc92b11b0bb4b3d05c9f'], 'final': ['100644', '02fd1a04ca9d6541ea00cc92b11b0bb4b3d05c9f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasShortCommutatorLift.lean': {'before': ['100644', 'a6f686cb65080d74c6353ecd723549959905006d'], 'source': ['100644', '146a811a648f46cd1900ecf84663dc8a9cdaf942'], 'final': ['100644', '146a811a648f46cd1900ecf84663dc8a9cdaf942'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasShortContraction.lean': {'before': ['100644', '591eb73582d6fbbe61c1dc01f507c7f2f277cd22'], 'source': ['100644', '954ff396a414eed5ea660ff903104a8131cf923a'], 'final': ['100644', '954ff396a414eed5ea660ff903104a8131cf923a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAuxiliaryBackground.lean': {'before': None, 'source': ['100644', '7329ec8ab2309760aace5e83b8f355aa1e2c1a84'], 'final': ['100644', '7329ec8ab2309760aace5e83b8f355aa1e2c1a84'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatEuclidean.lean': {'before': ['100644', '6cc401572252566b41cd6418f8732cf1f034c3d8'], 'source': ['100644', 'c13e7cf24e22d2f0d5a674923379bb9aefdf23e6'], 'final': ['100644', 'c13e7cf24e22d2f0d5a674923379bb9aefdf23e6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatGeometricRegularity.lean': {'before': ['100644', '650dfaff63a7c9e402a6b4bf1256d5a54cb6088b'], 'source': ['100644', '90ac6992f0c1f2e5d92f36b40b6711083a72c7fa'], 'final': ['100644', '90ac6992f0c1f2e5d92f36b40b6711083a72c7fa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatLocalReconstruction.lean': {'before': ['100644', '7875f8b0a3706df324246d5b0a30d5453eb40ee4'], 'source': ['100644', '846cfd57d4f9ad8efa93b322f07aee508bf72b88'], 'final': ['100644', '846cfd57d4f9ad8efa93b322f07aee508bf72b88'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorialCommutator.lean': {'before': None, 'source': ['100644', '5c03b38e23d7af2889b6fa2ae6579396eadfc92d'], 'final': ['100644', '5c03b38e23d7af2889b6fa2ae6579396eadfc92d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TranslationMeasurability.lean': {'before': None, 'source': ['100644', 'a17f8cef99768fe9e82db0dac7cac7539fedf946'], 'final': ['100644', 'a17f8cef99768fe9e82db0dac7cac7539fedf946'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/UniformSmallness.lean': {'before': None, 'source': ['100644', 'c89756a2adcca31cabe59f4e074fb4e555a3aba3'], 'final': ['100644', 'c89756a2adcca31cabe59f4e074fb4e555a3aba3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/BackgroundNormalFrameBridge.lean': {'before': None, 'source': ['100644', 'f320c89417a169abed367a863031576c8dfecea5'], 'final': ['100644', 'f320c89417a169abed367a863031576c8dfecea5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean': {'before': ['100644', '4b3105634f0cdd1bb29a51e3815f70af36582401'], 'source': ['100644', '39181a8c54985a4fab4d6db4a414d9eb3e26971b'], 'final': ['100644', '39181a8c54985a4fab4d6db4a414d9eb3e26971b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckJointRegularity.lean': {'before': None, 'source': ['100644', 'e9e3ac1d33dbdf9d5ab53ef836d5bbb659de8d3f'], 'final': ['100644', 'e9e3ac1d33dbdf9d5ab53ef836d5bbb659de8d3f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionLocalFrame.lean': {'before': None, 'source': ['100644', 'a81c0cd07dcbc299d0665a1861aa8243e8cb848f'], 'final': ['100644', 'a81c0cd07dcbc299d0665a1861aa8243e8cb848f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionMetricDefect.lean': {'before': None, 'source': ['100644', 'd47fb95438a11a05ce539462cff407afd15ff66c'], 'final': ['100644', 'd47fb95438a11a05ce539462cff407afd15ff66c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ExplicitLeviCivitaCorrectionSymmetry.lean': {'before': None, 'source': ['100644', '97f1365b43b5f02170bdc1bb9885d12be6566903'], 'final': ['100644', '97f1365b43b5f02170bdc1bb9885d12be6566903'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/FixedTensorHeatUniqueness.lean': {'before': None, 'source': ['100644', '047fbb13c0a18c2304f0c15d3654a1a4ca127818'], 'final': ['100644', '047fbb13c0a18c2304f0c15d3654a1a4ca127818'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowCoherentModelComparison.lean': {'before': None, 'source': ['100644', '3ca882af191a6253c522536c4db242741a09ffb5'], 'final': ['100644', '3ca882af191a6253c522536c4db242741a09ffb5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowCutoffComparison.lean': {'before': None, 'source': ['100644', 'ce57b9718b016abc1115a284dfc0851ca532d8b9'], 'final': ['100644', 'ce57b9718b016abc1115a284dfc0851ca532d8b9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCompactFlowModelComparison.lean': {'before': None, 'source': ['100644', '835cb11227b88676eaaa68bf69c95e1ba7939bf3'], 'final': ['100644', '835cb11227b88676eaaa68bf69c95e1ba7939bf3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCoordinatePicardEstimates.lean': {'before': None, 'source': ['100644', '3a541be6cbe4931355a4a1f4f2298f011b2bc6fa'], 'final': ['100644', '3a541be6cbe4931355a4a1f4f2298f011b2bc6fa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckCorrectionFunctionalSliceRegularity.lean': {'before': None, 'source': ['100644', '85c0473c5e616cf252b0623a335fe14df5e75aec'], 'final': ['100644', '85c0473c5e616cf252b0623a335fe14df5e75aec'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFixedTimeC2CoordinateBridge.lean': {'before': None, 'source': ['100644', 'aaae18307c2f45ee83b8616c119268e7f69b8150'], 'final': ['100644', 'aaae18307c2f45ee83b8616c119268e7f69b8150'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFixedTimeRegularity.lean': {'before': None, 'source': ['100644', 'cb4b06090d76c2b6979911019ba64a3b4a195750'], 'final': ['100644', 'cb4b06090d76c2b6979911019ba64a3b4a195750'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalAssemblyBridge.lean': {'before': None, 'source': ['100644', 'd3921ec05eb0ec474c7424e15b2ae68350b3084f'], 'final': ['100644', 'd3921ec05eb0ec474c7424e15b2ae68350b3084f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalBracketBridge.lean': {'before': None, 'source': ['100644', '5e64803afc1a5da1613fb76aa1c0b360af17246b'], 'final': ['100644', '5e64803afc1a5da1613fb76aa1c0b360af17246b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalChosenBackground.lean': {'before': None, 'source': ['100644', '42a7e908dcfa722dfc54af90acf38cae05ab4ba8'], 'final': ['100644', '42a7e908dcfa722dfc54af90acf38cae05ab4ba8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalDataBridge.lean': {'before': None, 'source': ['100644', 'e9b2f26f4cda0ed0f7beffbb0b832da36da30970'], 'final': ['100644', 'e9b2f26f4cda0ed0f7beffbb0b832da36da30970'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalTimeBridge.lean': {'before': None, 'source': ['100644', '5b61dbf91158e379dc34cc57ea5aa2ac88fa3517'], 'final': ['100644', '5b61dbf91158e379dc34cc57ea5aa2ac88fa3517'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckFlowVariationalWitness.lean': {'before': None, 'source': ['100644', '48ec3c72fa93a6d2b22a9f9933b401804c91fbe8'], 'final': ['100644', '48ec3c72fa93a6d2b22a9f9933b401804c91fbe8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2CoordinateBridge.lean': {'before': None, 'source': ['100644', 'b263c747e58242b805b2b6cdb2a1525824cf697b'], 'final': ['100644', 'b263c747e58242b805b2b6cdb2a1525824cf697b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2FlowBridge.lean': {'before': None, 'source': ['100644', '41605e1a40b85c6bcaa90723dcd10519d1543629'], 'final': ['100644', '41605e1a40b85c6bcaa90723dcd10519d1543629'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointC2PicardRegularity.lean': {'before': None, 'source': ['100644', '2a1c071f146d98868a549e31908fe96b712957d2'], 'final': ['100644', '2a1c071f146d98868a549e31908fe96b712957d2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponents.lean': {'before': None, 'source': ['100644', '353ccabdf441cfd729ca01baeedc0a089756770b'], 'final': ['100644', '353ccabdf441cfd729ca01baeedc0a089756770b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponentsLowering.lean': {'before': None, 'source': ['100644', 'ff21275782a029d1b49e37023996b006a2d02b75'], 'final': ['100644', 'ff21275782a029d1b49e37023996b006a2d02b75'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionFunctionalComponentsSliceRegularity.lean': {'before': None, 'source': ['100644', '695489ce52577566e63ce2e2c8b73d6d9b8bedfa'], 'final': ['100644', '695489ce52577566e63ce2e2c8b73d6d9b8bedfa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointCorrectionTensorRegularity.lean': {'before': None, 'source': ['100644', '7f25ba2f21f5a15738b0ea1d48851d34a2e55afd'], 'final': ['100644', '7f25ba2f21f5a15738b0ea1d48851d34a2e55afd'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointFieldCompactGaugeFlow.lean': {'before': None, 'source': ['100644', '45cff9c02f3ae59fdb07524e67c684c3c3904e4e'], 'final': ['100644', '45cff9c02f3ae59fdb07524e67c684c3c3904e4e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckJointOneFormRegularity.lean': {'before': None, 'source': ['100644', '750f2f35a0b6840c9b3550c932003ada6d7a50b8'], 'final': ['100644', '750f2f35a0b6840c9b3550c932003ada6d7a50b8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckPicardRegularityReduction.lean': {'before': None, 'source': ['100644', 'fef30ae86e2afd4eaafd49db5ea463c71304c60f'], 'final': ['100644', 'fef30ae86e2afd4eaafd49db5ea463c71304c60f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckRaisedCompactGaugeFlow.lean': {'before': None, 'source': ['100644', 'dbedf6f27d0bb34ed5e70f5aee283282937973e1'], 'final': ['100644', 'dbedf6f27d0bb34ed5e70f5aee283282937973e1'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/DeTurckWitnessPhase1.lean': {'before': None, 'source': ['100644', '98d41938c63139804a4e00b03de439abc88a56c6'], 'final': ['100644', '98d41938c63139804a4e00b03de439abc88a56c6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowDerivative.lean': {'before': ['100644', 'd94b4b6079f16f452e2ce8e6460436a76561f7cc'], 'source': ['100644', '8019934ede15f1bbb56fe9606896d45ad201fc94'], 'final': ['100644', '8019934ede15f1bbb56fe9606896d45ad201fc94'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowMilestone41.lean': {'before': None, 'source': ['100644', 'ee5f9d0f2e303dac9b955d69657280ab51df7385'], 'final': ['100644', 'ee5f9d0f2e303dac9b955d69657280ab51df7385'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowTimeDerivative.lean': {'before': ['100644', 'd273672ee2b53b6dd518c0955de67c7ff52a52fe'], 'source': ['100644', '847d06f44e9ec49b8810eb924b84e76f235b5288'], 'final': ['100644', '847d06f44e9ec49b8810eb924b84e76f235b5288'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/ModelGaugeFlowODE.lean': {'before': ['100644', '08468af22e4589178eb665bad52d57a86386dc8f'], 'source': ['100644', '5b0a6ad43c4ea86a541bf2dbea3428fcde43146b'], 'final': ['100644', '5b0a6ad43c4ea86a541bf2dbea3428fcde43146b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/ModelGaugeFlowODECore.lean': {'before': None, 'source': ['100644', '1080931bee5632f3f1154f6aae7a644e432815bf'], 'final': ['100644', '1080931bee5632f3f1154f6aae7a644e432815bf'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeReduction/TimeAugmentedDeTurckODE.lean': {'before': None, 'source': ['100644', '2ffdf61814e60c36c77e2d1a352cb3aebd713784'], 'final': ['100644', '2ffdf61814e60c36c77e2d1a352cb3aebd713784'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyConnectionVariation.lean': {'before': None, 'source': ['100644', '9fcba90b3c44df00887f7dc4f3e213da7ead5c78'], 'final': ['100644', '9fcba90b3c44df00887f7dc4f3e213da7ead5c78'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyDerivedMovingConnectionVariation.lean': {'before': None, 'source': ['100644', 'd28f077cb1e9faa0da9a6ceab76c6191326e351c'], 'final': ['100644', 'd28f077cb1e9faa0da9a6ceab76c6191326e351c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyGeometricEvolution.lean': {'before': None, 'source': ['100644', '62b9350b14afa12835e4f3703f37c68ea978f3d6'], 'final': ['100644', '62b9350b14afa12835e4f3703f37c68ea978f3d6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicConnectionVariation.lean': {'before': None, 'source': ['100644', 'd8f1307ba8476d52ab3b1c78eb83ed7f1b3c7882'], 'final': ['100644', 'd8f1307ba8476d52ab3b1c78eb83ed7f1b3c7882'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicEndpointRegularity.lean': {'before': None, 'source': ['100644', 'ff4269451cdfb5d2c953ae345cd0d15e311d0e81'], 'final': ['100644', 'ff4269451cdfb5d2c953ae345cd0d15e311d0e81'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicGeometricEvolution.lean': {'before': None, 'source': ['100644', 'bc1d76fcde13e617e1de2922271443b663e8a29f'], 'final': ['100644', 'bc1d76fcde13e617e1de2922271443b663e8a29f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceAssembly.lean': {'before': None, 'source': ['100644', '9a01e481dcac7781bf37c26b6afb50620cbf5836'], 'final': ['100644', '9a01e481dcac7781bf37c26b6afb50620cbf5836'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceRegularityBridge.lean': {'before': None, 'source': ['100644', 'b1a863e87cea81a42121528c4c814b1a1afaa68c'], 'final': ['100644', 'b1a863e87cea81a42121528c4c814b1a1afaa68c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicSliceRegularityC3.lean': {'before': None, 'source': ['100644', 'f2f3dd3ba0cf819829495f108e0c8f7ac81d17c0'], 'final': ['100644', 'f2f3dd3ba0cf819829495f108e0c8f7ac81d17c0'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicTraceGeometry.lean': {'before': None, 'source': ['100644', 'ab672527668f56f0eadfdffa7692ef32683c0f16'], 'final': ['100644', 'ab672527668f56f0eadfdffa7692ef32683c0f16'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyIntrinsicVariation.lean': {'before': None, 'source': ['100644', '8c61705ec91124eb3568e005e6c58d24935043e7'], 'final': ['100644', '8c61705ec91124eb3568e005e6c58d24935043e7'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyKoszul.lean': {'before': None, 'source': ['100644', '44011c44937f9fe33385a3bc89dafb468403615f'], 'final': ['100644', '44011c44937f9fe33385a3bc89dafb468403615f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyKoszulVariation.lean': {'before': None, 'source': ['100644', 'f253a518d965964cca9abb46a25aa6dd7295acd4'], 'final': ['100644', 'f253a518d965964cca9abb46a25aa6dd7295acd4'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyLieBracketMixedRegularity.lean': {'before': None, 'source': ['100644', '233dad1afbc401a974617f17533c446851f7e7ca'], 'final': ['100644', '233dad1afbc401a974617f17533c446851f7e7ca'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyManifoldLieBracketMixedRegularity.lean': {'before': None, 'source': ['100644', '3fa404a658ade0f7efaf6fcf9fa5ee73205a53b8'], 'final': ['100644', '3fa404a658ade0f7efaf6fcf9fa5ee73205a53b8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMetricMixedRegularity.lean': {'before': None, 'source': ['100644', '400003b608f6ee3b837d16ead9194eccb8be11dd'], 'final': ['100644', '400003b608f6ee3b837d16ead9194eccb8be11dd'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMixedRegularity.lean': {'before': None, 'source': ['100644', 'abb22e6e3d895d8139ea601314a385464fa6811b'], 'final': ['100644', 'abb22e6e3d895d8139ea601314a385464fa6811b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyMovingConnectionVariation.lean': {'before': None, 'source': ['100644', 'a8feb8f4d1875db813667fd2c8cf4b28dbc6c0bd'], 'final': ['100644', 'a8feb8f4d1875db813667fd2c8cf4b28dbc6c0bd'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyOperatorC2Regularity.lean': {'before': None, 'source': ['100644', '114ce9e76a621739cbb9c3450919d9ade7313063'], 'final': ['100644', '114ce9e76a621739cbb9c3450919d9ade7313063'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyOperatorLaplacian.lean': {'before': None, 'source': ['100644', '068fc7a14d6d47fe603b40440ae979432e455f42'], 'final': ['100644', '068fc7a14d6d47fe603b40440ae979432e455f42'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyParabolic.lean': {'before': None, 'source': ['100644', '9fe8fdf9188f7f1ed4e5b765aa443ebe3de056e4'], 'final': ['100644', '9fe8fdf9188f7f1ed4e5b765aa443ebe3de056e4'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyRicciC2Regularity.lean': {'before': None, 'source': ['100644', 'aeab51c9cbe2526df01c3a05bb27984bae53d465'], 'final': ['100644', 'aeab51c9cbe2526df01c3a05bb27984bae53d465'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyScalarBarrier.lean': {'before': None, 'source': ['100644', 'c2886eaeb29c43ce10aab3c449bb33e146518960'], 'final': ['100644', 'c2886eaeb29c43ce10aab3c449bb33e146518960'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveyScalarC2Regularity.lean': {'before': None, 'source': ['100644', '5e56de2f6bed5f2685fbfb2ed42af80369219f08'], 'final': ['100644', '5e56de2f6bed5f2685fbfb2ed42af80369219f08'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySpectrum.lean': {'before': None, 'source': ['100644', '09f5ac2d724b7011f7e5f8f40679e030ae2e7e7d'], 'final': ['100644', '09f5ac2d724b7011f7e5f8f40679e030ae2e7e7d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupport.lean': {'before': None, 'source': ['100644', 'c1f42a7731dff88812f3f07ad681ae6ce1b85a76'], 'final': ['100644', 'c1f42a7731dff88812f3f07ad681ae6ce1b85a76'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupportEvolution.lean': {'before': None, 'source': ['100644', '5dbdba64e59af4d286f88e6d5c59e7d3b708bef7'], 'final': ['100644', '5dbdba64e59af4d286f88e6d5c59e7d3b708bef7'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/HamiltonIveySupportLaplacian.lean': {'before': None, 'source': ['100644', 'f0b972f7968e69bcda6503474079640ee4bfe804'], 'final': ['100644', 'f0b972f7968e69bcda6503474079640ee4bfe804'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/InitialValueProblemBackground.lean': {'before': None, 'source': ['100644', '1dfe97d5a9960f4217f7dd824a98a2e947ae1e49'], 'final': ['100644', '1dfe97d5a9960f4217f7dd824a98a2e947ae1e49'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/InitialValueProblemBackgroundTorsion.lean': {'before': None, 'source': ['100644', '8bb267e8072f77a4af5a09d60ec9a1b9caa0265a'], 'final': ['100644', '8bb267e8072f77a4af5a09d60ec9a1b9caa0265a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/MetricInverseVariation.lean': {'before': None, 'source': ['100644', '3e081c9abd6b2c2389d262f29266d1b0bfea2011'], 'final': ['100644', '3e081c9abd6b2c2389d262f29266d1b0bfea2011'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/RicciCorrectionDerivativeExpansion.lean': {'before': None, 'source': ['100644', 'c9a56eeca19d336546b073193001c57336f9082e'], 'final': ['100644', 'c9a56eeca19d336546b073193001c57336f9082e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarEvolution.lean': {'before': None, 'source': ['100644', '2280e37313de1ed4409edaf81b72733aa0a2adf3'], 'final': ['100644', '2280e37313de1ed4409edaf81b72733aa0a2adf3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarOpenInitialInvariant.lean': {'before': None, 'source': ['100644', '314156bc8b90c17b303fa96df509799d40ea5f8c'], 'final': ['100644', '314156bc8b90c17b303fa96df509799d40ea5f8c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarOpenInitialPotential.lean': {'before': None, 'source': ['100644', '0555b4b87d976e2e7cf2c67e5d61c873c25c0976'], 'final': ['100644', '0555b4b87d976e2e7cf2c67e5d61c873c25c0976'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarParabolicBarrier.lean': {'before': None, 'source': ['100644', '7b700be24a4a111a8c053e5d0ea4cefaa7c5a6de'], 'final': ['100644', '7b700be24a4a111a8c053e5d0ea4cefaa7c5a6de'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/ScalarParabolicInvariant.lean': {'before': None, 'source': ['100644', '8cba4f6abbb517e1b2bcf9c4fa602fa662a6081f'], 'final': ['100644', '8cba4f6abbb517e1b2bcf9c4fa602fa662a6081f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurck.lean': {'before': None, 'source': ['100644', '37c36cfe12b49ce4a632016b439f98e0d25090fa'], 'final': ['100644', '37c36cfe12b49ce4a632016b439f98e0d25090fa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckBackgroundAssembly.lean': {'before': None, 'source': ['100644', '4c24eed03e5ab76c4e08f885a2c0682377c199e6'], 'final': ['100644', '4c24eed03e5ab76c4e08f885a2c0682377c199e6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckBackgroundFormula.lean': {'before': None, 'source': ['100644', 'd472f6c22a62483466f4e383c55bab13d2bc53dc'], 'final': ['100644', 'd472f6c22a62483466f4e383c55bab13d2bc53dc'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckCorrectionBackground.lean': {'before': None, 'source': ['100644', '1bce8c10332590bc390c9f6f2305f69f23135b24'], 'final': ['100644', '1bce8c10332590bc390c9f6f2305f69f23135b24'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckCorrectionRegularity.lean': {'before': None, 'source': ['100644', 'cfc4627445b63f944e7d2d8cf970cdeb47b37ec2'], 'final': ['100644', 'cfc4627445b63f944e7d2d8cf970cdeb47b37ec2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckDerivative.lean': {'before': None, 'source': ['100644', 'b512026278ef5f359652d7d9db8b61fcfafe8b53'], 'final': ['100644', 'b512026278ef5f359652d7d9db8b61fcfafe8b53'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckDerivativeExpansion.lean': {'before': None, 'source': ['100644', '1f84252cc92131321ca43d0705b0d94b65573331'], 'final': ['100644', '1f84252cc92131321ca43d0705b0d94b65573331'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckEquation.lean': {'before': None, 'source': ['100644', 'fcbf0eec31e29aed4e23ca98e6ca5ceed3365d7b'], 'final': ['100644', 'fcbf0eec31e29aed4e23ca98e6ca5ceed3365d7b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckHessianPrincipalCore.lean': {'before': None, 'source': ['100644', 'a0ddc5531fa38bdc6e03496fd495071f0ff531c8'], 'final': ['100644', 'a0ddc5531fa38bdc6e03496fd495071f0ff531c8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckIntrinsicTraceDerivative.lean': {'before': None, 'source': ['100644', '3ae72002d91217be9f8000b800adb6ba0ca3216e'], 'final': ['100644', '3ae72002d91217be9f8000b800adb6ba0ca3216e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckPrincipalPart.lean': {'before': None, 'source': ['100644', 'f0caa330e4f944c98d71d0ce5b6d215242871e0f'], 'final': ['100644', 'f0caa330e4f944c98d71d0ce5b6d215242871e0f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckQuadraticRemainderAlgebra.lean': {'before': None, 'source': ['100644', '3347afd146e3a468179e43ff726bb75374644901'], 'final': ['100644', '3347afd146e3a468179e43ff726bb75374644901'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckRegularity.lean': {'before': None, 'source': ['100644', 'accc4f0328d48aad9274c89b2244d49c39180123'], 'final': ['100644', 'accc4f0328d48aad9274c89b2244d49c39180123'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/StandardDeTurckTraceDerivative.lean': {'before': None, 'source': ['100644', '51e9b1fd17d009e52e035c128303a69986ecebd2'], 'final': ['100644', '51e9b1fd17d009e52e035c128303a69986ecebd2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/TensorHeatNormMaximum.lean': {'before': None, 'source': ['100644', '6d06d1a171f5ddd5eca28998a4a065ed8ac2d283'], 'final': ['100644', '6d06d1a171f5ddd5eca28998a4a065ed8ac2d283'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/TorsionFreeAuxiliaryBackground.lean': {'before': None, 'source': ['100644', '2e7902eddfd38f19f4a143d10f92445913f554b3'], 'final': ['100644', '2e7902eddfd38f19f4a143d10f92445913f554b3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean': {'before': ['100644', '5d8a958fbaeb2613f1bfe2e6e6eb020f01adbe00'], 'source': ['100644', 'baf278e74b280231a360592fc13823ae08ab6ee5'], 'final': ['100644', 'baf278e74b280231a360592fc13823ae08ab6ee5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/AffineMetricTraceDerivative.lean': {'before': None, 'source': ['100644', '9739d248f26d2f86cfa0658d13e0108a5ca2aeb0'], 'final': ['100644', '9739d248f26d2f86cfa0658d13e0108a5ca2aeb0'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/BilinearEvaluation.lean': {'before': None, 'source': ['100644', 'c6bd69852e3881a1ccf1e7a8870807ad3cdda452'], 'final': ['100644', 'c6bd69852e3881a1ccf1e7a8870807ad3cdda452'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacian.lean': {'before': ['100644', 'b8f06b207a86a147f31d6eb596b52185c5652059'], 'source': ['100644', '1595adcdd1ad9fabdafa91ca5d4c73a0766649bc'], 'final': ['100644', '1595adcdd1ad9fabdafa91ca5d4c73a0766649bc'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianChart.lean': {'before': ['100644', 'b9792a3c763fe8c6c2377b480b783aef87f6c61c'], 'source': ['100644', 'e4e7059e0b67b9457098700c93731a9af95db5a3'], 'final': ['100644', 'e4e7059e0b67b9457098700c93731a9af95db5a3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianCoordinate.lean': {'before': ['100644', '5950213161556b66db7eccbd0dc5d37f36f87a92'], 'source': ['100644', '3a3bf3f3ac55fcdf5e629bf9b639f706b6ffc669'], 'final': ['100644', '3a3bf3f3ac55fcdf5e629bf9b639f706b6ffc669'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianIntrinsic.lean': {'before': None, 'source': ['100644', 'd5efd812bdedfe1f0aa235dffe7814dc376e81b9'], 'final': ['100644', 'd5efd812bdedfe1f0aa235dffe7814dc376e81b9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianLocalFrame.lean': {'before': ['100644', 'b3225b2e003c10992076cf8966e0538b8c32776c'], 'source': ['100644', 'f1cd274634a93a617287e8ae193d82d70f4d738d'], 'final': ['100644', 'f1cd274634a93a617287e8ae193d82d70f4d738d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianTraceFreezing.lean': {'before': None, 'source': ['100644', 'adef39dc57b60b0371c8ccceab3dd27489e83a4f'], 'final': ['100644', 'adef39dc57b60b0371c8ccceab3dd27489e83a4f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/CovariantTwoTensorConnectionChange.lean': {'before': None, 'source': ['100644', 'd2cfd681bb601be2a0ba24b7107a5960340cdc18'], 'final': ['100644', 'd2cfd681bb601be2a0ba24b7107a5960340cdc18'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Bianchi.lean': {'before': ['100644', '8a485f4e3d713afd12016d09201f9d57981421a4'], 'source': ['100644', 'd1d0440d6558225e0881c37e811a2afc0158c8d2'], 'final': ['100644', 'd1d0440d6558225e0881c37e811a2afc0158c8d2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ConnectionChange.lean': {'before': None, 'source': ['100644', '74c08517ff3e6b47e0a54b72720ef08102a7d8fa'], 'final': ['100644', '74c08517ff3e6b47e0a54b72720ef08102a7d8fa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchiBridge.lean': {'before': ['100644', 'bb959450d76c4643a3a9d50da1b07ed109c452e9'], 'source': ['100644', '77dfd43c03fd3f76afce6897aa89b8e9c142337b'], 'final': ['100644', '77dfd43c03fd3f76afce6897aa89b8e9c142337b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchiUnconditional.lean': {'before': None, 'source': ['100644', 'db1083c04e45b372c93a722bdcd55955099461c9'], 'final': ['100644', 'db1083c04e45b372c93a722bdcd55955099461c9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/InducedHomCurvature.lean': {'before': None, 'source': ['100644', 'c52b099eceaea3ed46f0d93aa2bbc5acf145de09'], 'final': ['100644', 'c52b099eceaea3ed46f0d93aa2bbc5acf145de09'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RaisedRicci.lean': {'before': None, 'source': ['100644', 'f04e905e1d3caa2f6ddd5ab2fc50b291a465248e'], 'final': ['100644', 'f04e905e1d3caa2f6ddd5ab2fc50b291a465248e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciConnectionChange.lean': {'before': None, 'source': ['100644', 'e53df04630258909955c53bcb118697bbc52be9e'], 'final': ['100644', 'e53df04630258909955c53bcb118697bbc52be9e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciDerivativeTrace.lean': {'before': None, 'source': ['100644', '9847923dfe6141387119719a37bff1f41cefad80'], 'final': ['100644', '9847923dfe6141387119719a37bff1f41cefad80'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/RicciNorm.lean': {'before': None, 'source': ['100644', '233b8da930f6474b5f79817052000e1d053178b3'], 'final': ['100644', '233b8da930f6474b5f79817052000e1d053178b3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean': {'before': ['100644', '4b887b01c3d90ef1a2b645610f281829c12808a9'], 'source': ['100644', '572bf2071c038f7b5ad8e4e18898baf2948eed5b'], 'final': ['100644', '572bf2071c038f7b5ad8e4e18898baf2948eed5b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ThreeDimensionalDecomposition.lean': {'before': None, 'source': ['100644', '0717b5310d808d9f296455e5aa222ba15dcef6a3'], 'final': ['100644', '0717b5310d808d9f296455e5aa222ba15dcef6a3'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ThreeDimensionalRicciNorm.lean': {'before': None, 'source': ['100644', '08b8d2faed629d7b684bc8ced131d37b95dfd29e'], 'final': ['100644', '08b8d2faed629d7b684bc8ced131d37b95dfd29e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/DowngradeNormFree.lean': {'before': ['100644', 'cb6e05ec51e2933cc563cde4efc6bb1f90b880ac'], 'source': ['100644', 'd0d08ced853fe1747c7bf5715877f3cd835ac807'], 'final': ['100644', 'd0d08ced853fe1747c7bf5715877f3cd835ac807'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/EndomorphismTrace.lean': {'before': None, 'source': ['100644', 'd195da17871b1cefb25b06b6dadde33106182655'], 'final': ['100644', 'd195da17871b1cefb25b06b6dadde33106182655'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Existence.lean': {'before': ['100644', '7bbe6ee228f46fee8f85329d9ee3601ae8a4548f'], 'source': ['100644', '398ca2aa3cd1d3d5d4a1f000b6f4d693a634f19a'], 'final': ['100644', '398ca2aa3cd1d3d5d4a1f000b6f4d693a634f19a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/FirstOrderParallelExtension.lean': {'before': None, 'source': ['100644', '10bab760254505523890a1f99fe7211bbc6897cc'], 'final': ['100644', '10bab760254505523890a1f99fe7211bbc6897cc'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellation.lean': {'before': None, 'source': ['100644', 'ff554dcd5bf48994211ec68c9cf2259778988510'], 'final': ['100644', 'ff554dcd5bf48994211ec68c9cf2259778988510'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellationLaplacian.lean': {'before': None, 'source': ['100644', 'f4c3c61a7b04459792c8e140372e366d23affb1b'], 'final': ['100644', 'f4c3c61a7b04459792c8e140372e366d23affb1b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreCancellationTrace.lean': {'before': None, 'source': ['100644', '77e7e063c2c1b8c2836b9af05da63b8a8a44e6d7'], 'final': ['100644', '77e7e063c2c1b8c2836b9af05da63b8a8a44e6d7'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HessianCoreMetricCurvature.lean': {'before': None, 'source': ['100644', 'cc6195aabd6bcc703aed4313f2bc641c2c1bb440'], 'final': ['100644', 'cc6195aabd6bcc703aed4313f2bc641c2c1bb440'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/HomEvaluation.lean': {'before': None, 'source': ['100644', '4b0063880510a985ba7c8a1e0169f320cfcb25a6'], 'final': ['100644', '4b0063880510a985ba7c8a1e0169f320cfcb25a6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/InducedHomRegularity.lean': {'before': None, 'source': ['100644', 'c4010b478a67689f9cd389124a2a4419a5ae101d'], 'final': ['100644', 'c4010b478a67689f9cd389124a2a4419a5ae101d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/InverseGramDerivative.lean': {'before': None, 'source': ['100644', '7c962da762b83e25e10f3f6f7c13a50debc7bb1d'], 'final': ['100644', '7c962da762b83e25e10f3f6f7c13a50debc7bb1d'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean': {'before': ['100644', '31a79f8cc30b8dbed94396a2575274effbd83f54'], 'source': ['100644', '85a4e541c3729fdd897382e4aab56e47e2ad170f'], 'final': ['100644', '85a4e541c3729fdd897382e4aab56e47e2ad170f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaCorrectionDerivative.lean': {'before': None, 'source': ['100644', 'db17778d4eab0304ad5486dc3b3e48925b3f06aa'], 'final': ['100644', 'db17778d4eab0304ad5486dc3b3e48925b3f06aa'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaCorrectionKoszul.lean': {'before': None, 'source': ['100644', 'fbba0be6a51490d6fe2ecdee348bb1916c7c5fd6'], 'final': ['100644', 'fbba0be6a51490d6fe2ecdee348bb1916c7c5fd6'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivitaRegularity.lean': {'before': None, 'source': ['100644', '3c9cce045c00158c944f57175cd735d5e3c32bca'], 'final': ['100644', '3c9cce045c00158c944f57175cd735d5e3c32bca'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricDefectLocalFrame.lean': {'before': None, 'source': ['100644', 'adaa0931d16a9b384c462c8e00bba398e6daf3ae'], 'final': ['100644', 'adaa0931d16a9b384c462c8e00bba398e6daf3ae'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricDefectTensorDerivative.lean': {'before': None, 'source': ['100644', 'ca42e0a7fce09da2cebb9873a1fc24ec5bc0232b'], 'final': ['100644', 'ca42e0a7fce09da2cebb9873a1fc24ec5bc0232b'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/MetricTensorCurvatureAction.lean': {'before': None, 'source': ['100644', '335e81379b32d9ebbcd485de5e8d55e30a5a1194'], 'final': ['100644', '335e81379b32d9ebbcd485de5e8d55e30a5a1194'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/RieszCovariantDerivative.lean': {'before': None, 'source': ['100644', '4f4d34507d39d18d4ccefb32e89ad9f6ded97635'], 'final': ['100644', '4f4d34507d39d18d4ccefb32e89ad9f6ded97635'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/RieszMapC3Regularity.lean': {'before': None, 'source': ['100644', 'efeed159f7931b0be88fcd1eb812e324edfda432'], 'final': ['100644', 'efeed159f7931b0be88fcd1eb812e324edfda432'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacian.lean': {'before': None, 'source': ['100644', '6a075efe0548ce94ea7aabeb282a8651222224d5'], 'final': ['100644', '6a075efe0548ce94ea7aabeb282a8651222224d5'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacianMaximum.lean': {'before': None, 'source': ['100644', '4607ce345ee13fe196b3f8ff722e936bffebff45'], 'final': ['100644', '4607ce345ee13fe196b3f8ff722e936bffebff45'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ScalarLaplacianProduct.lean': {'before': None, 'source': ['100644', '4769e86a4d6499601995e1b679122a9f4e1e1fc7'], 'final': ['100644', '4769e86a4d6499601995e1b679122a9f4e1e1fc7'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TangentFrameCoordinate.lean': {'before': None, 'source': ['100644', 'fa5841eca1aa5608e0db4f324a61591182002c5a'], 'final': ['100644', 'fa5841eca1aa5608e0db4f324a61591182002c5a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorDivergence.lean': {'before': None, 'source': ['100644', '49603d4b480859e7c0eb3f3a41f59754f647934a'], 'final': ['100644', '49603d4b480859e7c0eb3f3a41f59754f647934a'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorGramCovariantDerivative.lean': {'before': None, 'source': ['100644', 'b440702cb15a9106b2aa91f71bab7023502278b8'], 'final': ['100644', 'b440702cb15a9106b2aa91f71bab7023502278b8'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorNormSq.lean': {'before': None, 'source': ['100644', 'd8b7bcf0845baaa0a96ed3ad32b6ee0d734dd32f'], 'final': ['100644', 'd8b7bcf0845baaa0a96ed3ad32b6ee0d734dd32f'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorNormSqLocalFrame.lean': {'before': None, 'source': ['100644', '1b73ad9d0b1a063b9d2ef51224f271b960a1caf2'], 'final': ['100644', '1b73ad9d0b1a063b9d2ef51224f271b960a1caf2'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TorsionRegularity.lean': {'before': None, 'source': ['100644', '20609de028299452c1a1547c20dfa788f1296d89'], 'final': ['100644', '20609de028299452c1a1547c20dfa788f1296d89'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TraceLaplacian.lean': {'before': None, 'source': ['100644', '2285fe61a836557a22f2ce57a384727d396d97ef'], 'final': ['100644', '2285fe61a836557a22f2ce57a384727d396d97ef'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/VectorValuedBilinearFrameCoordinate.lean': {'before': None, 'source': ['100644', 'bc9293a1a35f7587a2ae301a752cbadc62c7e3ad'], 'final': ['100644', 'bc9293a1a35f7587a2ae301a752cbadc62c7e3ad'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/VectorValuedBilinearPairing.lean': {'before': None, 'source': ['100644', '2c22a9cbebc9c123cd3eb74056de71d9a8c1f8a9'], 'final': ['100644', '2c22a9cbebc9c123cd3eb74056de71d9a8c1f8a9'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/HomBundleComp.lean': {'before': ['100644', 'bfdbd06290f24aae86a50b3e7e8d9dff01b4addd'], 'source': ['100644', 'c690f4294896885ab5ce3a70aebb1b58b55251df'], 'final': ['100644', 'c690f4294896885ab5ce3a70aebb1b58b55251df'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean': {'before': ['100644', 'f250764aa6e576e55a1183e71ca8eafc3f3cfc8c'], 'source': ['100644', '485bcc9537a06ac8ce5322a75e00dab5fe6bdb6c'], 'final': ['100644', '485bcc9537a06ac8ce5322a75e00dab5fe6bdb6c'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSectionCore.lean': {'before': None, 'source': ['100644', 'cb5dec9d602b6985aabff94fe4522ac86afc356e'], 'final': ['100644', 'cb5dec9d602b6985aabff94fe4522ac86afc356e'], 'resolution': 'exact-source'}, 'symmetric-tensor-heat/vendor/curvature/lake-manifest.json': {'before': ['100644', 'dc942b90c4caeafd654f90dae2164209bf1c930a'], 'source': ['100644', '6f43d98dc0d1e168146656d4570dc53ea80593d4'], 'final': ['100644', '6f43d98dc0d1e168146656d4570dc53ea80593d4'], 'resolution': 'exact-source'}}
TENSOR_RETAINED = {'.github/workflows/symmetric-tensor-heat-palomar-render.yml', '.github/workflows/symmetric-tensor-heat-palomar-mechanical.yml'}
TENSOR_BOUNDARY_WORKFLOW = '.github/workflows/symmetric-tensor-heat-palomar-current.yml'
TENSOR_BOUNDARY_OPERATION = ('jobs:\n  current-mechanical:\n', 'jobs:\n  candidate-boundary:\n    name: Exact tensor 4.35 dependency boundary and compiled statement closure\n    runs-on: ubuntu-latest\n    timeout-minutes: 90\n    env:\n      PYTHONDONTWRITEBYTECODE: \'1\'\n      EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n    steps:\n      - name: Checkout exact tensor candidate\n        uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1\n        with:\n          repository: ${{ github.event.pull_request.head.repo.full_name || github.repository }}\n          ref: ${{ github.event.pull_request.head.sha || github.sha }}\n          persist-credentials: false\n          fetch-depth: 0\n      - name: Authenticate complete tracked source before compiler checks\n        shell: bash\n        run: |\n          set -euo pipefail\n          mkdir -p "$RUNNER_TEMP/tensor-boundary"\n          python3 -I -B - <<\'PY\' | tee "$RUNNER_TEMP/tensor-boundary/source-before.json"\n          import hashlib, json, os, pathlib, re, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          head = os.environ[\'EXPECTED_SHA\']\n          assert re.fullmatch(r\'[0-9a-f]{40}\', head)\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == head\n          entries = {}\n          for row in git(\'ls-tree\', \'-rz\', head).split(b\'\\0\')[:-1]:\n              descriptor, name = row.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in entries\n              assert not pathlib.PurePosixPath(path).is_absolute() and \'..\' not in pathlib.PurePosixPath(path).parts\n              entries[path] = (mode, oid)\n          index = {}\n          for row in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = row.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == entries, \'Complete tensor source index drift\'\n          for path, (mode, oid) in entries.items():\n              file = root / path\n              for parent in file.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Tensor source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = file.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Tensor source mode drift\'\n              data = file.read_bytes()\n              assert hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest() == oid, \'Tensor source blob drift: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == head\n          print(json.dumps({\'head\': head, \'tree\': git(\'rev-parse\', head+\'^{tree}\').decode().strip(), \'tracked_paths\': len(entries), \'source_checked\': True}, sort_keys=True))\n          PY\n      - uses: actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97\n        with:\n          python-version: \'3.11.10\'\n      - name: Check actual tensor package and immutable provenance\n        working-directory: symmetric-tensor-heat\n        shell: bash\n        run: |\n          set -euo pipefail\n          python -m pip install --disable-pip-version-check jsonschema==4.26.0 PyYAML==6.0.3\n          python scripts/check-package.py 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/package.log"\n          python scripts/check-provenance.py 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/provenance.log"\n      - name: Install the unchanged pinned elan distribution\n        shell: bash\n        run: |\n          set -euo pipefail\n          curl --fail --location --proto \'=https\' --tlsv1.2 \\\n            --output "$RUNNER_TEMP/elan.tar.gz" \\\n            https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz\n          echo "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2  $RUNNER_TEMP/elan.tar.gz" | sha256sum --check\n          mkdir "$RUNNER_TEMP/tensor-boundary-elan"\n          tar -xzf "$RUNNER_TEMP/elan.tar.gz" -C "$RUNNER_TEMP/tensor-boundary-elan"\n          "$RUNNER_TEMP/tensor-boundary-elan/elan-init" -y --no-modify-path --default-toolchain none\n          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"\n      - name: Compile only the selected Challenge and run both original kernel guards\n        working-directory: symmetric-tensor-heat\n        shell: bash\n        run: |\n          set -euo pipefail\n          test "$(cat lean-toolchain)" = leanprover/lean4:v4.35.0-rc2\n          lake exe cache get 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/dependency-cache.log"\n          lake env lean --version | tee "$RUNNER_TEMP/tensor-boundary/compiler.log"\n          grep -Eq \'^Lean \\(version 4\\.35\\.0-rc2,\' "$RUNNER_TEMP/tensor-boundary/compiler.log"\n          test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = 065356127b1dc0016f66b7283ce0ce2c4055aa55\n          lake build TensorHeatChallenge 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/challenge-build.log"\n          python scripts/check-challenge-boundary.py 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/dependency-only-boundary.log"\n          lake env lean scripts/check-closed-statement.lean 2>&1 | tee "$RUNNER_TEMP/tensor-boundary/compiled-statement-closure.log"\n      - name: Authenticate complete tracked source after compiler checks\n        if: always()\n        shell: bash\n        run: |\n          set -euo pipefail\n          mkdir -p "$RUNNER_TEMP/tensor-boundary"\n          python3 -I -B - <<\'PY\' | tee "$RUNNER_TEMP/tensor-boundary/source-after.json"\n          import hashlib, json, os, pathlib, re, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          head = os.environ[\'EXPECTED_SHA\']\n          assert re.fullmatch(r\'[0-9a-f]{40}\', head)\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == head\n          entries = {}\n          for row in git(\'ls-tree\', \'-rz\', head).split(b\'\\0\')[:-1]:\n              descriptor, name = row.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in entries\n              assert not pathlib.PurePosixPath(path).is_absolute() and \'..\' not in pathlib.PurePosixPath(path).parts\n              entries[path] = (mode, oid)\n          index = {}\n          for row in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = row.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == entries, \'Complete tensor source index drift\'\n          for path, (mode, oid) in entries.items():\n              file = root / path\n              for parent in file.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Tensor source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = file.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Tensor source mode drift\'\n              data = file.read_bytes()\n              assert hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest() == oid, \'Tensor source blob drift: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == head\n          print(json.dumps({\'head\': head, \'tree\': git(\'rev-parse\', head+\'^{tree}\').decode().strip(), \'tracked_paths\': len(entries), \'source_checked\': True}, sort_keys=True))\n          PY\n      - name: Preserve exact tensor boundary and compiler evidence\n        if: always()\n        uses: actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a\n        with:\n          name: tensor-boundary-${{ github.event.pull_request.head.sha || github.sha }}\n          path: ${{ runner.temp }}/tensor-boundary\n          if-no-files-found: error\n          retention-days: 90\n\n  current-mechanical:\n    needs: candidate-boundary\n')
TENSOR_PACKAGE = 'symmetric-tensor-heat/scripts/check-package.py'
TENSOR_PACKAGE_OPERATIONS = [('import json\n', 'import hashlib\nimport json\n'), ('        require("  push:" not in path.read_text(encoding="utf-8"),\n                f"duplicate push trigger in {name} workflow")\n', '        if name in {"mechanical", "renderer"}:\n            expected_hashes = {\'mechanical\': \'aa67ea8abed6e5189fb49f92ec02b8b5812020ad306e8772c3ecafe678ebb319\', \'renderer\': \'15b28d6b108ded509cec5bf8fd0ece125429609243b3640bbedf3863fb057c45\'}\n            require(hashlib.sha256(path.read_bytes()).hexdigest() == expected_hashes[name],\n                    f"exact qualified-master automatic {name} workflow drift")\n        else:\n            require("  push:" not in path.read_text(encoding="utf-8"),\n                    f"duplicate push trigger in {name} workflow")\n'), ('    require("  pull_request:" not in mechanical and "  workflow_dispatch:" in mechanical,\n            "historical mechanical replay must be manual only")\n', '    require(hashlib.sha256(workflows["mechanical"].read_bytes()).hexdigest() == \'aa67ea8abed6e5189fb49f92ec02b8b5812020ad306e8772c3ecafe678ebb319\',\n            "exact qualified-master automatic mechanical workflow drift")\n')]
TENSOR_HELPER_EDITS = [('    expected,originals,changes=expected_identity()\n', '    expected,originals,changes=tensor_identity(*expected_identity())\n'), ("    assert json.loads((ROOT/MAP).read_text())==map_record(expected,originals,changes), 'Descriptive identity map drift'\n", "    assert tensor_strict_json((ROOT/MAP).read_bytes())==tensor_map_record(expected,originals,changes), 'Descriptive identity map drift'\n"), ('        inherited=original_expected() # original ancestry/transform/self/workflow validation\n', '        inherited=tensor_reconstructed_sources(namespace,original_expected(),expected) # genuine old body, exact predecessor/current reconstruction\n')]
TENSOR_TEST_EDITS = [('    def test_full_finite_identity_and_selected_source_bytes(self):\n        with self.sources() as (trees,read):\n            expected,originals,changes=comp.expected_identity()\n', '    def test_full_finite_identity_and_selected_source_bytes(self):\n        with self.sources() as (trees,read):\n            expected,originals,changes=comp.tensor_identity(*comp.expected_identity())\n'), ('    def test_full_controlled_identity_and_unchanged_selected_mathematics(self):\n        with fixed_sources() as (trees, reader):\n            expected, originals, changes = comp.expected_identity()\n', '    def test_full_controlled_identity_and_unchanged_selected_mathematics(self):\n        with fixed_sources() as (trees, reader):\n            expected, originals, changes = comp.tensor_identity(*comp.expected_identity())\n'), ('self.assertEqual(len(expected),1737)', 'self.assertEqual(len(expected),1920)'), ('self.assertEqual(len(expected), 1737)', 'self.assertEqual(len(expected), 1920)'), ('comp.FIXED_ROOTS\n            self.assertTrue(all(expected[p]', 'comp.FIXED_ROOTS-comp.TENSOR_PATHS\n            self.assertTrue(all(expected[p]'), ('comp.NEW - comp.FIXED_ROOTS\n            self.assertTrue(all((expected[p]', 'comp.NEW - comp.FIXED_ROOTS - comp.TENSOR_PATHS\n            self.assertTrue(all((expected[p]'), ('json.loads((comp.ROOT/comp.MAP).read_bytes()),comp.map_record(expected,originals,changes)', 'comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()),comp.tensor_map_record(expected,originals,changes)'), ('json.loads((comp.ROOT/comp.MAP).read_bytes()), comp.map_record(expected, originals, changes)', 'comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()), comp.tensor_map_record(expected, originals, changes)'), ('current=ast.parse((comp.ROOT/comp.HELPER).read_bytes())', 'current=ast.parse(comp.tensor_helper_inverse((comp.ROOT/comp.HELPER).read_bytes()))'), ('    if REAL:suite.addTests', '    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(TensorCompositionTests))\n    if REAL:suite.addTests')]

def tensor_pins():
    result = {}
    for commit in (TENSOR_PARENT,TENSOR_SOURCE,TENSOR_BASE,TENSOR_DEPENDENCY):
        assert re.fullmatch(r'[0-9a-f]{40}',commit or ''), 'Tensor immutable pin drift'
        assert git('rev-parse',commit+'^{tree}').decode().strip()==TENSOR_TREES[commit], 'Tensor pinned tree drift'
        result[commit]=parent_tree(commit)
    assert git('merge-base',TENSOR_PARENT,TENSOR_SOURCE).decode().strip()==TENSOR_BASE, 'Tensor merge-base drift'
    return result

def tensor_inverse(raw, path, edits, marker):
    source=raw.decode()
    start='# BEGIN authenticated finite tensor '+marker+'\n'
    end='# END authenticated finite tensor '+marker+'\n'
    assert source.count(start)==source.count(end)==1, 'Tensor extension boundary drift'
    first=source.index(start);last=source.index(end,first)+len(end)
    source=source[:first]+source[last:]
    for before,after in edits:
        assert source.count(after)==1, 'Tensor count-one hook drift'
        source=source.replace(after,before,1)
    original=git('show',TENSOR_PARENT+':'+path)
    # Byte-for-byte recovery authenticates all original module state and bodies.
    assert source.encode()==original, 'Tensor predecessor executable recovery drift'
    return original

def tensor_helper_inverse(raw):
    return tensor_inverse(raw,HELPER,TENSOR_HELPER_EDITS,'extension')

def tensor_test_inverse(raw):
    return tensor_inverse(raw,TEST,TENSOR_TEST_EDITS,'tests')

def tensor_strict_json(raw):
    def pairs(rows):
        result={}
        for name,value in rows:
            assert name not in result, 'Duplicate tensor identity-map record'
            result[name]=value
        return result
    return json.loads(raw,object_pairs_hook=pairs)

def tensor_predecessor(expected, originals, changes, snapshots):
    base=snapshots[TENSOR_PARENT]
    assert len(base)==1737
    old_helper=git('show',TENSOR_PARENT+':'+HELPER)
    assert base[HELPER]==('100644',blob_id(old_helper))
    tensor_helper_inverse((ROOT/HELPER).read_bytes())
    old_test=tensor_test_inverse((ROOT/TEST).read_bytes())
    assert base[TEST]==('100644',blob_id(old_test))
    digest=sha256(old_helper)
    prior_changes=dict(changes)
    for p in EDITED-{SMOOTH}:prior_changes[p]=transform(p,originals[p],digest)
    prior_changes[SMOOTH]=transform(SMOOTH,originals[SMOOTH],digest,
        sha256(prior_changes[FIXTURE]),sha256(prior_changes[WORKFLOW]))
    for path in EDITED:
        if path in changes:
            assert (ROOT/path).read_bytes()==changes[path], 'Current digest-bound executable drift: '+path
        assert base[path]==('100644',blob_id(prior_changes[path])), 'Whole predecessor bootstrap recovery drift: '+path
    prior={p:v for p,v in expected.items() if p not in TENSOR_PATHS or p in base}
    for p in TENSOR_PATHS:
        if p in base:prior[p]=base[p]
    prior.update({p:('100644',blob_id(prior_changes[p])) for p in EDITED})
    prior.update({p:base[p] for p in NEW})
    assert prior==base, 'Complete tensor predecessor source reconstruction drift'
    raw=git('show',TENSOR_PARENT+':'+MAP)
    assert base[MAP]==('100644',blob_id(raw))
    assert tensor_strict_json(raw)==map_record(prior,originals,prior_changes), 'Complete predecessor identity-map drift'
    return prior,prior_changes

def tensor_delta(snapshots):
    base,source,anchor=(snapshots[c] for c in (TENSOR_PARENT,TENSOR_SOURCE,TENSOR_BASE))
    assert len(source)==1741 and len(anchor)==1558
    actual={p for p in set(source)|set(anchor) if source.get(p)!=anchor.get(p)}
    assert actual==TENSOR_PATHS and len(actual)==237, 'Exact tensor delta drift'
    assert len(set(source)-set(anchor))==183 and not set(anchor)-set(source), 'Tensor additions/deletions drift'
    assert {p for p in actual if base.get(p)!=anchor.get(p)}=={TENSOR_MECHANICAL}, 'Tensor predecessor overlap drift'
    # The alternate compiler branch is the exact pre-optimization source tree.
    dependency=snapshots[TENSOR_DEPENDENCY]
    equal_commit='76f39722d0c30f4b3d5849d9ff0e9a90454ee604'
    assert git('rev-parse',equal_commit+'^{tree}').decode().strip()==TENSOR_TREES[TENSOR_DEPENDENCY], 'Tensor compiler dependency tree drift'
    assert parent_tree(equal_commit)==dependency, 'Tensor compiler dependency source drift'
    for commit in (TENSOR_SOURCE,TENSOR_DEPENDENCY,TENSOR_PARENT):
        subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'merge-base','--is-ancestor',commit,'HEAD'],check=True,env=ENV)
    record={p:{'before':list(anchor[p]) if p in anchor else None,
               'source':list(source[p]),'final':list(base[p] if p in TENSOR_RETAINED else ('100644',blob_id(tensor_package_transform(git('show',TENSOR_SOURCE+':'+p)))) if p==TENSOR_PACKAGE else ('100644',blob_id(tensor_boundary_transform(git('show',TENSOR_SOURCE+':'+p)))) if p==TENSOR_BOUNDARY_WORKFLOW else source[p]),
               'resolution':'preserve-qualified-master' if p in TENSOR_RETAINED else 'exact-count-one-workflow-guard' if p==TENSOR_PACKAGE else 'exact-boundary-workflow-integration' if p==TENSOR_BOUNDARY_WORKFLOW else 'exact-source'} for p in sorted(actual)}
    assert record==TENSOR_DELTA, 'Tensor exact mode/blob/provenance drift'
    return record

def tensor_package_transform(original):
    source=original.decode()
    for before,after in TENSOR_PACKAGE_OPERATIONS:
        assert source.count(before)==1 and after not in source, 'Tensor package count-one guard drift'
        source=source.replace(before,after,1)
    return source.encode()

def tensor_package_inverse(actual):
    original=git('show',TENSOR_SOURCE+':'+TENSOR_PACKAGE)
    assert actual==tensor_package_transform(original), 'Tensor whole package executable drift'
    return original

def tensor_boundary_transform(original):
    before,after=TENSOR_BOUNDARY_OPERATION
    source=original.decode()
    assert source.count(before)==1 and 'candidate-boundary:' not in source, 'Tensor boundary job count-one drift'
    return source.replace(before,after,1).encode()

def tensor_boundary_inverse(actual):
    original=git('show',TENSOR_SOURCE+':'+TENSOR_BOUNDARY_WORKFLOW)
    assert actual==tensor_boundary_transform(original), 'Tensor complete boundary workflow drift'
    return original

def tensor_identity(expected, originals, changes):
    snapshots=tensor_pins()
    tensor_predecessor(expected,originals,changes,snapshots)
    delta=tensor_delta(snapshots)
    for path,record in delta.items():
        if path in TENSOR_RETAINED:
            assert expected[path]==tuple(record['final']), 'Master mechanical workflow drift'
            continue
        data=git('show',TENSOR_SOURCE+':'+path)
        assert blob_id(data)==record['source'][1], 'Tensor exact source bytes drift'
        if path==TENSOR_PACKAGE:data=tensor_package_transform(data)
        if path==TENSOR_BOUNDARY_WORKFLOW:data=tensor_boundary_transform(data)
        assert (record['source'][0],blob_id(data))==tuple(record['final']), 'Tensor exact final source drift'
        changes[path]=data;expected[path]=tuple(record['final'])
    assert len(expected)==1920
    return expected,originals,changes

def tensor_map_record(expected, originals, changes):
    snapshots=tensor_pins()
    tensor_predecessor(expected,originals,changes,snapshots)
    record=map_record(expected,originals,changes)
    record['tensor_heat_integration']={
        'parents':dict(TENSOR_TREES),'delta':tensor_delta(snapshots),
        'predecessor_helper_blob':snapshots[TENSOR_PARENT][HELPER][1],
        'predecessor_map_blob':snapshots[TENSOR_PARENT][MAP][1],
        'scope':'Exact cumulative PR103/104/105 tensor source and PR109 compiler ancestry; tensor Lean 4.35rc2 is distinct from curvature Lean 4.33. Compilation, Comparator, kernel and rendering qualification pending; both Point4 targets OPEN.'}
    return record
def tensor_reconstructed_sources(namespace, inherited, expected):
    """Authenticate genuine old records before admitting exact tensor replacements."""
    assert namespace['SELF_PATHS']=={WEIGHTED,WEIGHTED_MOCK}, 'Inherited weighted self inventory drift'
    old_keys=set(parent_tree(MASTER))-WEIGHTED_MISSING-namespace['SELF_PATHS']
    assert set(inherited)==old_keys, 'Inherited weighted missing/extra reconstruction record'
    assert namespace['BASE']=='3a8ed697d1f0366f8370efb2fa9e524b68d27e97', 'Inherited weighted provenance pin drift'
    assert all(provenance==namespace['BASE'] for provenance,data in inherited.values()), 'Inherited weighted provenance record drift'
    snapshots=tensor_pins()
    delta=tensor_delta(snapshots)
    prior=snapshots[TENSOR_PARENT]
    result=dict(inherited)
    for path in set(inherited)&TENSOR_PATHS:
        provenance,data=inherited[path]
        assert path in prior, 'Tensor reconstruction invented predecessor record: '+path
        assert blob_id(data)==prior[path][1], 'Tensor inherited predecessor bytes drift: '+path
        assert expected[path]==tuple(delta[path]['final']), 'Tensor reconstructed final mode/blob drift: '+path
        actual=(ROOT/path).read_bytes()
        assert blob_id(actual)==expected[path][1], 'Tensor reconstructed current bytes drift: '+path
        result[path]=('current-tensor-exact-composition',actual)
    return result

# END authenticated finite tensor extension
def expected_identity():
    master, support = parent_tree(MASTER), parent_tree(SUPPORT)
    union = resolve_union(master, support)
    helper_sha = sha256((ROOT/HELPER).read_bytes())
    originals = {p:original_bytes(p,master,support) for p in EDITED}
    changes = {p:transform(p,originals[p],helper_sha) for p in EDITED-{SMOOTH}}
    changes[SMOOTH]=transform(SMOOTH,originals[SMOOTH],helper_sha,
        sha256(changes[FIXTURE]),sha256(changes[WORKFLOW]))
    expected = dict(union)
    for path,data in changes.items():expected[path]='100644',blob_id(data)
    expected, originals, changes = heat_identity(expected, originals, changes)
    expected, originals, changes = contraction_identity(expected, originals, changes)
    expected, originals, changes = fixed_identity(expected, originals, changes)
    # New code/docs are bound to the exact committed HEAD/index/physical bytes.
    # Independent review must approve that external head; this is no self-review.
    head = parse_tree(git('ls-tree','-rz','HEAD'))
    for path in NEW:
        assert path in head and head[path][0]=='100644'
        expected[path]=head[path]
    return expected, originals, changes

def prior_map_record(expected, originals, changes):
    master,support=parent_tree(MASTER),parent_tree(SUPPORT)
    # Authenticate immutable snapshots for this record construction.
    heat_parent_tree=parent_tree(HEAT_PARENT)
    heat_source_tree=parent_tree(HEAT_SOURCE)
    return {'parents':{c:TREES[c] for c in (MASTER,SUPPORT,HEAT_PARENT,HEAT_SOURCE)},
        'heat_invariant_integration':{'base':HEAT_PARENT,'source':HEAT_SOURCE,
            'base_tree':HEAT_PARENT_TREE,'source_tree':HEAT_SOURCE_TREE,
            'source_identity':{p:list(heat_source_tree[p]) for p in sorted(heat_source_tree)},
            'base_identity':{p:list(heat_parent_tree[p]) for p in sorted(heat_parent_tree)},
            'fixed_source_paths':{p:list(heat_source_tree[p]) for p in sorted(HEAT_ADDED|{HEAT_DOMAIN})},
            'transforms':{p:{'original_blob':blob_id(originals[p]),'final_blob':blob_id(contraction_inverse(p,fixed_inverse(p,changes[p]))),
                'original_sha256':sha256(originals[p]),'final_sha256':sha256(contraction_inverse(p,fixed_inverse(p,changes[p]))),'count':1} for p in sorted(HEAT_ROOTS)},
            'historical_run':37181895941,'scope':'Independent jet-field heat/reaction closure only; combined-head proof checks UNRUN; both targets OPEN'},
        'paths':len(expected),'canonical_point4':'OPEN','smooth_general_target':'OPEN',
        'localization_mock_route':{'parent':MOCK_ROUTE_PARENT,'parent_tree':MOCK_ROUTE_TREE,
            'failed_workflow_run':37450437571,'flag':LOCALIZATION_MOCK_FLAG,
            'historical_commit':LOCALIZATION,'historical_path':LOCALIZATION_MOCK,'historical_test_count':29,
            'current_coverage':'Complete source identity and localization semantic/import/canonical/schema PRE/POST checks; historical mock coverage stays historical.'},
        'ordinary_startup_repair':{'parent':STARTUP_REPAIR_PARENT,'parent_tree':STARTUP_REPAIR_TREE,
            'failed_workflow_run':37417941512,'failed_smooth_workflow_run':37417941491,
            'workflows':[LOCALIZATION_WORKFLOW,WORKFLOW],
            'note':'Job-scoped bytecode suppression before repository imports and nested audit Python; cache rejection and original validator bodies preserved. Prior smooth real runtime step18 was skipped.'},
        'provenance':[{'id':'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/'+c+'/curvature',
            'relationship':'builds-on','note':'Exact inherited mathematical/probe source; only finite validator composition is new.'} for c in (MASTER,SUPPORT)],
        'weighted_missing_master':{p:list(master[p]) for p in sorted(WEIGHTED_MISSING)},
        'parent_identity':{MASTER:{p:list(master[p]) for p in sorted(master)},SUPPORT:{p:list(support[p]) for p in sorted(support)}},
        'resolutions':{p:{'selected':'master','master':list(master[p]),'support':list(support[p])} for p in sorted(SHARED)},
        'transforms':{p:{'parent':MASTER if p in master else SUPPORT,'original_blob':blob_id(originals[p]),
            'original_sha256':sha256(originals[p]),'final_blob':blob_id(changes[p]),'final_sha256':sha256(changes[p]),
            'mode':'100644','count':1} for p in sorted(EDITED)},
        'identity':{p:([expected[p][0],'<committed-HEAD>'] if p==MAP else list(expected[p])) for p in sorted(expected)}}

def contraction_map_record(expected, originals, changes):
    record = prior_map_record(expected, originals, changes)
    # Authenticate immutable snapshots for this record construction.
    contraction_parent_tree=parent_tree(CONTRACTION_PARENT)
    contraction_source_tree=parent_tree(CONTRACTION_SOURCE)
    contraction_base_tree=parent_tree(CONTRACTION_BASE)
    record['parents'].update({c:TREES[c] for c in (CONTRACTION_PARENT,CONTRACTION_SOURCE,CONTRACTION_BASE)})
    record['metric_contraction_integration'] = {
        'base':CONTRACTION_PARENT,'base_tree':CONTRACTION_PARENT_TREE,
        'source':CONTRACTION_SOURCE,'source_tree':CONTRACTION_SOURCE_TREE,
        'merge_base':CONTRACTION_BASE,'merge_base_tree':CONTRACTION_BASE_TREE,
        'base_identity':{p:list(contraction_parent_tree[p]) for p in sorted(contraction_parent_tree)},
        'source_identity':{p:list(contraction_source_tree[p]) for p in sorted(contraction_source_tree)},
        'merge_base_identity':{p:list(contraction_base_tree[p]) for p in sorted(contraction_base_tree)},
        'fixed_source_paths':{p:list(contraction_source_tree[p]) for p in sorted(CONTRACTION_ADDED|CONTRACTION_REPLACED)},
        'transforms':{p:{'original_blob':contraction_parent_tree[p][1],
            'final_blob':blob_id(fixed_inverse(p,changes[p])),'count':1} for p in sorted(CONTRACTION_ROOTS)},
        'historical_run':37202841805,
        'scope':'Smooth metric contraction and conditional compact gauge flow only; combined-head checks UNRUN; both targets OPEN'}
    return record


def map_record(expected, originals, changes):
    record=contraction_map_record(expected,originals,changes)
    # Authenticate immutable snapshots for this record construction.
    fixed_parent_tree=parent_tree(FIXED_PARENT)
    fixed_source_tree=parent_tree(FIXED_SOURCE)
    fixed_base_tree=parent_tree(FIXED_BASE)
    record['parents'].update({c:TREES[c] for c in (FIXED_PARENT,FIXED_SOURCE,FIXED_BASE)})
    record['fixed_background_heat_integration']={
        'base':FIXED_PARENT,'base_tree':FIXED_PARENT_TREE,
        'source':FIXED_SOURCE,'source_tree':FIXED_SOURCE_TREE,
        'merge_base':FIXED_BASE,'merge_base_tree':FIXED_BASE_TREE,
        'base_identity':{p:list(fixed_parent_tree[p]) for p in sorted(fixed_parent_tree)},
        'source_identity':{p:list(fixed_source_tree[p]) for p in sorted(fixed_source_tree)},
        'merge_base_identity':{p:list(fixed_base_tree[p]) for p in sorted(fixed_base_tree)},
        'fixed_source_paths':{p:list(fixed_source_tree[p]) for p in sorted(FIXED_ADDED)},
        'transforms':{p:{'original_blob':fixed_parent_tree[p][1],
            'final_blob':blob_id(changes[p]),'original_sha256':sha256(fixed_inverse(p,changes[p])),
            'final_sha256':sha256(changes[p]),'count':1} for p in sorted(FIXED_ROOTS)},
        'historical_run':37233402239,
        'changed_dependency':'TensorHeatGeometricRegularity.lean newer baseline preserved; focused native qualification required',
        'scope':'Literal C2 metric local linear zero-trace right-inverse only; combined-head proof gates UNRUN; both targets OPEN'}
    record['current_axiom_inventory']={'immutable_predecessor':MASTER,
        'contraction_source':CONTRACTION_SOURCE,'probe':'contraction',
        'inherited_combined':[150,144],'current_combined':[157,151],
        'inherited_linear':[127,121],'current_linear':[134,128],
        'exact_appended_endpoints':list(CONTRACTION_AXIOM_ADDITIONS),
        'policy':'Preserve every inherited per-probe occurrence and append exactly seven authenticated contraction endpoints; original actual-output and standard-axiom checker unchanged'}
    record['historical_axiom_routing']={'weighted_validator':'3a8ed697d1f0366f8370efb2fa9e524b68d27e97',
        'smooth_validator':SUPPORT,'probe_surface':MASTER,
        'policy':'Verify complete current output first; execute the authenticated immutable six-entry contraction probe under current Lean 4.33; reuse other raw logs only for byte-identical probe sources; check both input sets after the immutable validator',
        'evidence':'Raw contraction bytes, commands, observed compiler ID and exit codes, current/historical hashes in scoped uploaded routing receipts; current compiled sources, not a historical Lean rebuild'}
    return record


def verify_current():
    assert re.fullmatch(r'[0-9a-f]{40}',FIXED_PARENT or ''), 'Actual repaired PR115 commit pin is required'
    head = git('rev-parse','HEAD').decode().strip()
    assert re.fullmatch(r'[0-9a-f]{40}',head)
    if os.environ.get('EXPECTED_SHA'):assert head==os.environ['EXPECTED_SHA'], 'External expected HEAD drift'
    for commit in (MASTER,SUPPORT,STARTUP_REPAIR_PARENT,MOCK_ROUTE_PARENT,WEIGHTED_MOCK_PARENT,HEAT_PARENT,HEAT_SOURCE,CONTRACTION_PARENT,CONTRACTION_SOURCE,CONTRACTION_BASE,FIXED_PARENT,FIXED_SOURCE,FIXED_BASE):
        subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'merge-base','--is-ancestor',commit,'HEAD'],check=True,env=ENV)
    expected,originals,changes=tensor_identity(*expected_identity())
    committed=parse_tree(git('ls-tree','-rz','HEAD'))
    assert committed==expected, 'Committed full source identity differs from finite policy'
    index={}
    for record in git('ls-files','--stage','-z').split(b'\0')[:-1]:
        descriptor,path=record.split(b'\t',1);mode,oid,stage=descriptor.decode().split();path=path.decode()
        assert stage=='0' and path not in index
        index[path]=mode,oid
    assert index==expected, 'Complete current index identity drift'
    for path,(mode,oid) in expected.items():
        file=ROOT/path
        for parent in file.parents:
            assert stat.S_ISDIR(parent.lstat().st_mode), 'Public symlink/non-directory parent'
            if parent==ROOT:break
        st=file.lstat().st_mode
        assert stat.S_ISREG(st) and bool(st&0o111)==(mode=='100755'), 'Current public mode drift: '+path
        assert blob_id(file.read_bytes())==oid, 'Current physical source drift: '+path
    physical={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean') if not {'.git','.lake','.toolchain'}&set(p.parts)}
    assert physical=={p for p in expected if p.endswith('.lean')}, 'Current physical proof inventory drift'
    # Reuse the unchanged reviewed runtime classifier for the complete public
    # physical/untracked inventory, not only tracked files and Lean suffixes.
    weighted=importlib.import_module('point4_weighted_hessian_release_guard')
    with replacements(weighted.__dict__,{'public_paths':lambda:set(expected)}):
        weighted.check_inventory()
    assert tensor_strict_json((ROOT/MAP).read_bytes())==tensor_map_record(expected,originals,changes), 'Descriptive identity map drift'
    assert git('rev-parse','HEAD').decode().strip()==head
    return expected

@contextlib.contextmanager
def replacements(namespace, updates):
    global _owner,_depth
    if _depth:
        assert namespace is _owner, 'Nested callback ownership changed'
    originals={name:namespace[name] for name in updates}
    first=not _depth
    if first:_owner=namespace
    _depth+=1
    try:
        namespace.update(updates)
        yield
    finally:
        namespace.update(originals)
        _depth-=1
        if first:_owner=None

def weighted_leaf(namespace, schema=None):
    expected=verify_current()
    local=importlib.import_module('point4_c2_metric_localization_source_test')
    if schema:current_root_schema(schema,local)
    original_expected=namespace['expected_sources']
    original_helpers=namespace['historical_c2']
    touched=[]
    def helpers():
        module=original_helpers()
        before=module.check_imports,module.check_metadata
        touched.append((module,before))
        # These genuine functions keep their own exact INTEGRATION_PARENT blobs.
        module.check_imports=lambda actual:fixed_check_imports(local,actual)
        module.check_metadata=lambda actual:fixed_check_metadata(local,actual)
        return module
    def composed_sources():
        inherited=tensor_reconstructed_sources(namespace,original_expected(),expected) # genuine old body, exact predecessor/current reconstruction
        assert set(parent_tree(MASTER))-namespace['_composition_original_public_paths']()==WEIGHTED_MISSING
        for path,(_,data) in inherited.items():
            if path == MANIFOLD_WORKFLOW:
                assert transform(path,data,sha256((ROOT/HELPER).read_bytes())) == (ROOT/path).read_bytes(), 'Exact manifold workflow startup transform drift'
            elif path == HEAT_DOMAIN:
                assert blob_id(data) == parent_tree(HEAT_PARENT)[path][1], 'Inherited domain source drift'
                assert (ROOT/path).read_bytes() == git('show',HEAT_SOURCE+':'+path), 'Exact comment-only domain transform drift'
            elif path in CONTRACTION_REPLACED:
                assert blob_id(data) == parent_tree(CONTRACTION_PARENT)[path][1], 'Inherited contraction predecessor drift: '+path
                assert (ROOT/path).read_bytes() == git('show',CONTRACTION_SOURCE+':'+path), 'Exact contraction replacement drift: '+path
            elif path == FIXED_STATUS:
                assert blob_id(data) == parent_tree(FIXED_PARENT)[path][1], 'Inherited fixed-background status predecessor drift'
                original = git('show',FIXED_PARENT+':'+path)
                assert (ROOT/path).read_bytes() == fixed_transform(path,original), 'Exact fixed-background status transform drift'
            elif path not in ROOT_CHANGES:
                assert blob_id(data)==expected[path][1], 'Inherited weighted reconstruction drift: '+path
        return {p:('current-finite-composition',(ROOT/p).read_bytes()) for p in expected}
    original_workflow=namespace['restored_exact_head_workflow']
    original_units=namespace['UNIT_FILE_SHA256']
    units=dict(original_units)
    units[WEIGHTED_WORKFLOW]=sha256((ROOT/WEIGHTED_WORKFLOW).read_bytes())
    def workflow(actual):
        original=git('show',MASTER+':'+WEIGHTED_WORKFLOW)
        assert blob_id(original)==parent_tree(MASTER)[WEIGHTED_WORKFLOW][1]
        assert actual==transform(WEIGHTED_WORKFLOW,original,sha256((ROOT/HELPER).read_bytes())), 'Exact weighted mock workflow transform drift'
        return original_workflow(original)
    try:
        with replacements(namespace,{'expected_sources':composed_sources,
             'public_paths':lambda:set(expected),'historical_c2':helpers,
             'UNIT_FILE_SHA256':units,'restored_exact_head_workflow':workflow}):
            report=namespace['_composition_original_check_current'](schema)
        return {'scope':'current master/smooth composition', 'public_paths':len(expected),
            'master_root_imports_provenance_validated':True,'canonical_point4':'OPEN','smooth_general_target':'OPEN',
            'lean_verified':False,'original_weighted_report_historical_inventory_shape_only':report}
    finally:
        for module,before in reversed(touched):module.check_imports,module.check_metadata=before
        primary = sys.exception()
        postchecks = [verify_current]
        if schema:postchecks.append(lambda:current_root_schema(schema,local))
        post_failures = []
        for check in postchecks:
            try:check()
            except BaseException as error:post_failures.append(error)
        if post_failures:
            if primary is None:
                primary = post_failures.pop(0)
                for error in post_failures:primary.add_note('Additional current POST check failure: '+repr(error))
                raise primary
            for error in post_failures:primary.add_note('Current POST check failure during unwind: '+repr(error))

PATH_FLAGS={'--schema','--probe-log','--axiom-dir','--audit-json','--compile-log',
 '--evidence-dir','--smooth-probe-log','--smooth-completion-log','--smooth-audit-json','--baseline-repo','--manifest'}
def absolute_arguments(args):
    result=list(args)
    for i,value in enumerate(result):
        if value in PATH_FLAGS:
            assert i+1<len(result), 'Missing path argument'
            result[i+1]=str(pathlib.Path(result[i+1]).resolve())
        elif any(value.startswith(flag+'=') for flag in PATH_FLAGS):
            flag,path=value.split('=',1);result[i]=flag+'='+str(pathlib.Path(path).resolve())
    return result

def historical(commit,path,args):
    args=absolute_arguments(args)
    with tempfile.TemporaryDirectory(prefix='point4-composition-history-') as directory:
        target=pathlib.Path(directory)/'source'
        subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'worktree','add','--detach',str(target),commit],check=True,env=ENV)
        try:
            def verify():
                assert git('rev-parse','HEAD',root=target).decode().strip()==commit
                assert git('write-tree',root=target).strip()==git('rev-parse',commit+'^{tree}').strip()
                wanted=parent_tree(commit)
                assert parse_tree(git('ls-tree','-rz','HEAD',root=target))==wanted
                for p,(mode,oid) in wanted.items():
                    file=target/p;st=file.lstat().st_mode
                    for parent in file.parents:
                        assert stat.S_ISDIR(parent.lstat().st_mode)
                        if parent==target:break
                    assert stat.S_ISREG(st) and bool(st&0o111)==(mode=='100755')
                    assert blob_id(file.read_bytes())==oid
                assert not git('status','--porcelain','--untracked-files=all',root=target)
            verify()
            print('HISTORICAL_VALIDATOR_BEGIN',commit,path,flush=True)
            historical_args=list(args)
            if '--manifest' in historical_args:
                i=historical_args.index('--manifest')+1
                historical_args[i]=str(pathlib.Path(historical_args[i]).with_name(pathlib.Path(historical_args[i]).name+'.historical-'+commit+'.json'))
            elif any(a.startswith('--manifest=') for a in historical_args):
                i=next(i for i,a in enumerate(historical_args) if a.startswith('--manifest='))
                path_arg=pathlib.Path(historical_args[i].split('=',1)[1])
                historical_args[i]='--manifest='+str(path_arg.with_name(path_arg.name+'.historical-'+commit+'.json'))
            subprocess.run([sys.executable,'-B',str(target/path),*historical_args],cwd=target,check=True,env=ENV)
            verify()
            print('HISTORICAL_VALIDATOR_END',commit,path,flush=True)
        finally:
            subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'worktree','remove',str(target)],check=True,env=ENV)

def evidence_parser(path):
    parser=argparse.ArgumentParser()
    if path.endswith('_mock_test.py'):return None
    common=['schema','axiom-dir','audit-json']
    if path.endswith('point4_manifold_heat_source_test.py'):
        common=['baseline-repo','probe-log']
    elif path.endswith('point4_manifold_heat_release_guard.py'):
        common+=['probe-log']
    for name in common:parser.add_argument('--'+name,type=pathlib.Path)
    if 'audit-json' in common:parser.add_argument('--audit-rc',type=int)
    return parser

INHERITED_AXIOM_PROBES = (
    'contraction', 'coordinate_connection', 'coordinate_jet', 'coordinate_operator',
    'principal_remainder', 'chosen_lc_coordinate', 'chosen_lc_curvature',
    'standard_coordinate_operator', 'frozen_metric_principal', 'weak_laplacian',
    'boundaryless_chart_frames', 'c2_heat_trace', 'weighted_initial_heat',
)
CONTRACTION_AXIOM_ADDITIONS = (
    'PoincareCurvature.ParametrizedInner.contMDiffOn_timeDependentMetricContraction',
    'PoincareCurvature.ParametrizedInner.contMDiff_paramSection_neg',
    'RicciFlow.metricContractedDeTurckVectorField_eq_sum_inverseGram_correction',
    'RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correction',
    'RicciFlow.contMDiff_metricContractedDeTurckGaugeField_of_joint_correction',
    'RicciFlow.exists_pos_metricContractedDiffeomorph3GaugeFlowOn_of_joint_correction',
    'RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correctionFunctional',
)

def current_axiom_inventory(path, inherited):
    """Preserve the immutable occurrence surface and allow one exact extension."""
    def probe_names(source):
        names = re.findall(r'^#print axioms (\S+)', source, re.M)
        if 'open RicciFlow.AnalyticPDE' in source:
            names = [n if n.startswith(('PoincareCurvature.', 'RicciFlow.')) else 'RicciFlow.AnalyticPDE.' + n for n in names]
        assert names and len(names) == len(set(names)), 'Empty/duplicate source axiom surface'
        return names
    combined = 'c2_initial' in path or 'manifold_heat_release' in path
    probes = INHERITED_AXIOM_PROBES if combined else INHERITED_AXIOM_PROBES[:11]
    assert tuple(inherited.PROBES) == probes, 'Inherited axiom probe inventory drift'
    master = parent_tree(MASTER)
    inventory = {}; original_occurrences = []; current_occurrences = []
    for name in probes:
        source_path = f'curvature/scripts/point4_{name}_probe.lean'
        original = original_bytes(source_path, master, {}).decode('utf8')
        before = tuple(probe_names(original))
        source = (ROOT / source_path).read_text(encoding='utf8')
        after = tuple(probe_names(source))
        expected = before + CONTRACTION_AXIOM_ADDITIONS if name == 'contraction' else before
        assert after == expected, 'Changed inherited occurrence or unapproved endpoint: ' + name
        inventory[name] = source, expected
        original_occurrences.extend(before); current_occurrences.extend(after)
    assert (len(original_occurrences), len(set(original_occurrences))) == ((150,144) if combined else (127,121)), 'Immutable predecessor occurrence surface drift'
    assert len(CONTRACTION_AXIOM_ADDITIONS) == len(set(CONTRACTION_AXIOM_ADDITIONS)) == 7
    assert not set(CONTRACTION_AXIOM_ADDITIONS) & set(original_occurrences), 'Extension repeats inherited declaration'
    assert (len(current_occurrences), len(set(current_occurrences))) == ((157,151) if combined else (134,128)), 'Exact seven-endpoint extension drift'
    return inventory


def current_evidence(path,args):
    verify_current()
    parser=evidence_parser(path)
    if parser is None:return
    parsed=parser.parse_args(args)
    if getattr(parsed,'schema',None):current_root_schema(parsed.schema)
    module=importlib.import_module(pathlib.PurePosixPath(path).stem)
    inherited=module.c2_guard() if 'manifold_heat_release' in path else module
    if getattr(parsed,'axiom_dir',None):
        folder=parsed.axiom_dir
        if 'c2_initial' in path or 'manifold_heat_release' in path:
            assert {p.name for p in folder.iterdir()}=={p+'.log' for p in inherited.PROBES}
        inventory=current_axiom_inventory(path,inherited)
        total=0;distinct=set()
        for name,(source,expected_names) in inventory.items():
            names=inherited.check_axiom_output(source,(folder/(name+'.log')).read_text())
            assert names==set(expected_names), 'Current axiom endpoint evidence drift: '+name
            total+=len(names);distinct|=names
        combined='c2_initial' in path or 'manifold_heat_release' in path
        assert (total,len(distinct))==((157,151) if combined else (134,128))
        inherited.check_boundaryless_types((folder/'boundaryless_chart_frames.log').read_text())
    if getattr(parsed,'audit_json',None):
        assert parsed.audit_rc is not None
        (module.c2_guard() if 'manifold_heat_release' in path else module).check_audit(json.loads(parsed.audit_json.read_text()),parsed.audit_rc)
    if getattr(parsed,'probe_log',None):
        function=module.check_new_probe if 'release_guard' in path else module.check_probe
        function(parsed.probe_log.read_text())

def axiom_argument(args):
    slots=[(i,False) for i,a in enumerate(args) if a=='--axiom-dir']
    slots += [(i,True) for i,a in enumerate(args) if a.startswith('--axiom-dir=')]
    assert len(slots)<=1, 'Duplicate axiom directory argument'
    if not slots:return None
    i,inline=slots[0]
    assert inline or i+1<len(args), 'Missing axiom directory argument'
    return i,inline,pathlib.Path(args[i].split('=',1)[1] if inline else args[i+1]).resolve()

def raw_axiom_files(folder):
    assert stat.S_ISDIR(folder.lstat().st_mode) and not folder.is_symlink(), 'Invalid axiom directory'
    files={}
    for file in folder.iterdir():
        assert stat.S_ISREG(file.lstat().st_mode) and not file.is_symlink(), 'Invalid axiom evidence file'
        files[file.name]=file.read_bytes()
    assert set(files) in ({n+'.log' for n in INHERITED_AXIOM_PROBES},
                         {n+'.log' for n in INHERITED_AXIOM_PROBES[:11]}), 'Missing/extra axiom files'
    return files

def routing_receipt_path(folder):
    # The weighted immutable inventory allows only its original files. Append
    # the receipt to its existing guard log, never to an actual axiom log.
    if folder.parent.name=='point4-weighted-hessian-evidence':
        return folder.parent/'source.log'
    # All other inherited workflows upload their scoped /tmp/<prefix>-*.log.
    return folder.with_name(folder.name+'-historical-routing.log')

@contextlib.contextmanager
def historical_axiom_arguments(commit,path,args):
    """Replay an authenticated historical probe against current compiled sources.

    Current logs remain complete and unchanged. Raw historical outputs are
    separate; no declaration record is selected, truncated or manufactured.
    """
    slot=axiom_argument(args)
    if slot is None:
        yield list(args)
        return
    i,inline,folder=slot
    evidence_path=path if path!=SMOOTH else 'curvature/scripts/point4_manifold_heat_release_guard.py'
    current_evidence(evidence_path,['--axiom-dir',str(folder)])
    before=raw_axiom_files(folder)
    tree=parent_tree(commit)
    module=importlib.import_module(pathlib.PurePosixPath(evidence_path).stem)
    checker=module.c2_guard() if 'manifold_heat_release' in evidence_path else module
    sources={}
    for name in sorted(before):
        probe='curvature/scripts/point4_'+name.removesuffix('.log')+'_probe.lean'
        source=git('show',commit+':'+probe)
        assert blob_id(source)==tree[probe][1], 'Historical probe provenance drift'
        if name!='contraction.log':
            assert (ROOT/probe).read_bytes()==source, 'Unsupported inherited probe byte drift: '+name
        else:
            baseline=git('show',MASTER+':'+probe)
            assert blob_id(baseline)==parent_tree(MASTER)[probe][1] and source==baseline, 'Historical contraction probe drift'
        sources[name]=(probe,source)
    receipt={'head':git('rev-parse','HEAD').decode().strip(),'historical_validator':commit,
        'scope':'Pinned historical probe surface evaluated against current compiled sources; no historical Lean rebuild',
        'current_sha256':{n:sha256(b) for n,b in before.items()},
        'probe_sources':{n:{'path':p,'blob':blob_id(b),'sha256':sha256(b)} for n,(p,b) in sources.items()}}
    with tempfile.TemporaryDirectory(prefix='point4-historical-axioms-') as directory:
        root=pathlib.Path(directory);view=root/'logs';view.mkdir()
        probe=root/'contraction.lean';probe.write_bytes(sources['contraction.log'][1])
        version_command=['lake','env','lean','--version']
        command=['lake','env','lean',str(probe)]
        receipt.update({'compiler_command':version_command,'probe_command':command,'cwd':str(ROOT/'curvature')})
        try:
            version=subprocess.run(version_command,cwd=ROOT/'curvature',capture_output=True,env=ENV)
            receipt.update({'compiler_exit':version.returncode,'compiler_stdout_base64':base64.b64encode(version.stdout).decode(),
                            'compiler_stderr_base64':base64.b64encode(version.stderr).decode()})
            assert version.returncode==0 and version.stdout.startswith(b'Lean (version 4.33.0,'), 'Current Lean compiler identity drift'
            result=subprocess.run(command,cwd=ROOT/'curvature',stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=ENV)
            receipt.update({'probe_exit':result.returncode,'raw_contraction_base64':base64.b64encode(result.stdout).decode(),
                            'historical_contraction_sha256':sha256(result.stdout)})
            assert result.returncode==0, 'Historical contraction probe failed in current environment'
            assert len(checker.check_axiom_output(sources['contraction.log'][1].decode('utf8'),result.stdout.decode('utf8')))==6, 'Historical six-entry surface drift'
            historical_files=dict(before);historical_files['contraction.log']=result.stdout
            for name,data in historical_files.items():(view/name).write_bytes(data)
            # Check the full immutable occurrence surface, not only contraction.
            for name in checker.PROBES:
                checker.check_axiom_output(sources[name+'.log'][1].decode('utf8'),historical_files[name+'.log'].decode('utf8'))
            checker.check_boundaryless_types(historical_files['boundaryless_chart_frames.log'].decode('utf8'))
            receipt['historical_sha256']={n:sha256(b) for n,b in historical_files.items()}
            routed=list(args)
            routed[i if inline else i+1]=('--axiom-dir=' if inline else '')+str(view)
            try:
                yield routed
            finally:
                assert probe.read_bytes()==sources['contraction.log'][1], 'Historical probe input mutation'
                assert raw_axiom_files(view)==historical_files, 'Historical axiom input mutation'
        finally:
            # Preserve raw probe bytes and provenance on success and failure.
            receipt_path=routing_receipt_path(folder)
            if receipt_path.exists() or receipt_path.is_symlink():
                assert stat.S_ISREG(receipt_path.lstat().st_mode) and not receipt_path.is_symlink(), 'Invalid routing receipt file'
            with receipt_path.open('ab') as output:
                output.write(b'\nHISTORICAL_AXIOM_ROUTING_RECEIPT '+json.dumps(receipt,sort_keys=True).encode()+b'\n')
            assert raw_axiom_files(folder)==before, 'Current axiom input mutation'
            current_evidence(evidence_path,['--axiom-dir',str(folder)])

def current_root_schema(schema,local=None):
    local=local or importlib.import_module('point4_c2_metric_localization_source_test')
    raw=pathlib.Path(schema).read_bytes()
    assert sha256(raw)==local.SCHEMA_SHA256, 'Current root official schema digest drift'
    import jsonschema
    jsonschema.validate(local.strict_yaml((ROOT/'curvature/formalization.yaml').read_bytes()),json.loads(raw))

def weighted_current_inherited_evidence(namespace,args):
    parser=argparse.ArgumentParser()
    for name in ('schema','probe-log','compile-log','axiom-dir','audit-json','evidence-dir'):
        parser.add_argument('--'+name,type=pathlib.Path)
    parser.add_argument('--audit-rc',type=int)
    parsed=parser.parse_args(args)
    inherited=[]
    for name in ('schema','axiom-dir','audit-json','audit-rc'):
        value=getattr(parsed,name.replace('-','_'))
        if value is not None:
            inherited.extend(['--'+name,str(value.resolve()) if isinstance(value,pathlib.Path) else str(value)])
    path='curvature/scripts/point4_manifold_heat_release_guard.py'
    current_evidence(path,inherited)
    if parsed.evidence_dir:
        # The original direct weighted body also validates this directory and
        # its paths. Its requested manifold evidence must be checked currently.
        namespace['check_evidence_inventory'](parsed.evidence_dir)
        current_evidence(path,['--probe-log',str((parsed.evidence_dir/'manifold-probe.log').resolve())])

def current_smooth_evidence(namespace,args):
    parser=argparse.ArgumentParser()
    for name in ('schema','probe-log','axiom-dir','audit-json','smooth-probe-log',
                 'smooth-completion-log','smooth-audit-json'):
        parser.add_argument('--'+name,type=pathlib.Path)
    for name in ('audit-rc','smooth-completion-rc','smooth-audit-rc'):
        parser.add_argument('--'+name,type=int)
    parsed=parser.parse_args(args)
    inherited=[]
    for name in ('schema','probe-log','axiom-dir','audit-json','audit-rc'):
        value=getattr(parsed,name.replace('-','_'))
        if value is not None:inherited.extend(['--'+name,str(value)])
    current_evidence('curvature/scripts/point4_manifold_heat_release_guard.py',inherited)
    metadata=(ROOT/namespace['METADATA']).read_text()
    namespace['check_new_metadata'](metadata)
    if parsed.schema:
        import jsonschema
        raw=parsed.schema.read_bytes()
        guard=namespace['legacy']().c2_guard()
        assert sha256(raw)==guard.SCHEMA_SHA256
        jsonschema.validate(guard.parse_metadata(metadata),json.loads(raw))
    for path in (namespace['PROBE'],namespace['COMPLETION']):
        assert sha256((ROOT/path).read_bytes())==namespace['FILE_SHA256'][path]
    if parsed.smooth_probe_log:namespace['check_support_probe'](parsed.smooth_probe_log.read_text())
    assert (parsed.smooth_completion_log is None)==(parsed.smooth_completion_rc is None)
    if parsed.smooth_completion_log:
        namespace['check_completion_open'](parsed.smooth_completion_log.read_text(),parsed.smooth_completion_rc)
    assert (parsed.smooth_audit_json is None)==(parsed.smooth_audit_rc is None)
    if parsed.smooth_audit_json:
        namespace['check_smooth_audit_open'](json.loads(parsed.smooth_audit_json.read_text()),parsed.smooth_audit_rc)
    verify_current()

@contextlib.contextmanager
def weighted_execution(namespace):
    def historical_gate(path,args):
        print('HISTORICAL_WEIGHTED_BASE_BEGIN',namespace['BASE'],path,flush=True)
        with historical_axiom_arguments(namespace['BASE'],path,args) as routed:
            namespace['_composition_original_historical_gate'](path,routed)
        print('HISTORICAL_WEIGHTED_BASE_END',namespace['BASE'],path,flush=True)
    with replacements(namespace,{'check_current':lambda schema=None:weighted_leaf(namespace,schema),
                                 'historical_gate':historical_gate}):yield

def install_weighted(namespace):
    assert '_composition_original_main' not in namespace, 'Duplicate weighted composition installation'
    for name in ('main','run_inherited','check_current','public_paths','historical_gate'):
        namespace['_composition_original_'+name]=namespace[name]
    original_main=namespace['main'];original_run=namespace['run_inherited']
    @functools.wraps(original_run)
    def run(path,argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        current_evidence(path,args)
        with weighted_execution(namespace):original_run(path,args)
        current_evidence(path,args)
    @functools.wraps(original_main)
    def main(argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        weighted_current_inherited_evidence(namespace,args)
        with weighted_execution(namespace):result=original_main(args)
        weighted_current_inherited_evidence(namespace,args)
        return result
    def dispatch(argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        if WEIGHTED_MOCK_FLAG in args:
            assert args.count(WEIGHTED_MOCK_FLAG)==1, 'Duplicate weighted mock route flag'
            parser=argparse.ArgumentParser(allow_abbrev=False)
            parser.add_argument('--schema',type=pathlib.Path,required=True)
            parser.add_argument(WEIGHTED_MOCK_FLAG,action='store_true',required=True)
            parsed=parser.parse_args(args)
            current_args=['--schema',str(parsed.schema)]
            try:
                main(current_args)
                historical(WEIGHTED_MOCK_PARENT,WEIGHTED_MOCK,[])
            finally:
                weighted_leaf(namespace,parsed.schema)
                weighted_current_inherited_evidence(namespace,current_args)
            return
        return main(args)
    namespace['run_inherited']=run;namespace['main']=dispatch

def localization_current(namespace,schema):
    namespace['check_ancestry']()
    fixed_check_imports(types.SimpleNamespace(**namespace),(ROOT/'curvature/PoincareCurvature.lean').read_bytes())
    raw=(ROOT/'curvature/formalization.yaml').read_text()
    fixed_check_metadata(types.SimpleNamespace(**namespace),raw)
    schema=pathlib.Path(schema)
    assert sha256(schema.read_bytes())==namespace['SCHEMA_SHA256']
    import jsonschema
    jsonschema.validate(namespace['strict_yaml'](raw),json.loads(schema.read_bytes()))
    for p in ('curvature/lean-toolchain','curvature/lakefile.toml','curvature/lake-manifest.json',
              'curvature/scripts/point4_audit.sh','curvature/scripts/point4_scan.py',
              'curvature/scripts/point4_target.txt','curvature/scripts/point4_closed_contract_source_test.py'):
        assert (ROOT/p).read_bytes()==namespace['blob'](namespace['INTEGRATION_PARENT'],p)
    assert (ROOT/'curvature/lean-toolchain').read_text()==namespace['TOOLCHAIN']
    scanner=ROOT/'curvature/scripts/point4_scan.py'
    result=subprocess.run([sys.executable,str(scanner),'locate','intrinsicLocalExistenceUniquenessFamily_pointFour',str(ROOT/namespace['PREFIX'])],capture_output=True)
    assert result.returncode!=0
    subprocess.run([sys.executable,str(ROOT/'curvature/scripts/point4_closed_contract_source_test.py')],check=True,env=ENV)
    cheats=subprocess.check_output([sys.executable,str(scanner),'cheats',str(ROOT/namespace['PREFIX'])],text=True)
    assert cheats.strip()=='TOTAL 0'

def install_localization(namespace):
    assert '_composition_original_main' not in namespace
    namespace['_composition_original_main']=namespace['main']
    def main(argv=None):
        parser=argparse.ArgumentParser(allow_abbrev=False)
        parser.add_argument('--schema',type=pathlib.Path,required=True);parser.add_argument('--manifest',type=pathlib.Path)
        parser.add_argument(LOCALIZATION_MOCK_FLAG,action='store_true')
        args=absolute_arguments(sys.argv[1:] if argv is None else argv);parsed=parser.parse_args(args)
        if args.count(LOCALIZATION_MOCK_FLAG)>1:parser.error('Historical localization mock flag must occur once')
        source_args=[arg for arg in args if arg!=LOCALIZATION_MOCK_FLAG]
        verify_current();localization_current(namespace,parsed.schema)
        # Historical manifest output remains external and is not relabelled current.
        try:
            historical(LOCALIZATION,LOCAL,source_args)
            if parsed.historical_localization_mocks:
                historical(LOCALIZATION,LOCALIZATION_MOCK,[])
        finally:
            verify_current();localization_current(namespace,parsed.schema)
        if parsed.manifest:
            parsed.manifest.write_text(json.dumps({'candidate':git('rev-parse','HEAD').decode().strip(),
                'parents':[MASTER,SUPPORT],'source_only':True,'point4':'OPEN',
                'source_sha256':{p:sha256((ROOT/p).read_bytes()) for p in verify_current()}},indent=2)+'\n')
            verify_current()
    namespace['main']=main

def install_consistency(namespace):
    assert '_composition_original_main' not in namespace
    namespace['_composition_original_main']=namespace['main']
    def main():
        argparse.ArgumentParser().parse_args()
        verify_current();historical(MASTER,CONSISTENCY,[]);verify_current()
    namespace['main']=main

def install_smooth(namespace):
    assert '_composition_original_main' not in namespace
    original=namespace['main'];namespace['_composition_original_main']=original
    @functools.wraps(original)
    def main(argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        current_identity=verify_current()
        print('CURRENT_SMOOTH_SEMANTIC_BODY_BEGIN: original inventory counters are historical shape; current identity is '+str(len(current_identity))+' paths',flush=True)
        original(args) # current real smooth metadata/schema/probe/completion/audit gates
        print('CURRENT_SMOOTH_SEMANTIC_BODY_END',flush=True)
        with historical_axiom_arguments(SUPPORT,SMOOTH,args) as routed:
            historical(SUPPORT,SMOOTH,routed) # original scoped route; no current hooks
        current_smooth_evidence(namespace,args)
        if any(a=='--smooth-audit-rc' or a.startswith('--smooth-audit-rc=') for a in args):
            # Retain the caller's observed auditor status, after both real routes
            # have validated it. The inherited artifact wildcard includes this log.
            output=pathlib.Path(tempfile.gettempdir())/'point4-smooth-forward-composition-inputs.log'
            output.write_text(json.dumps({'head':git('rev-parse','HEAD').decode().strip(),
                'validated_current_arguments':args,'source_only':True})+'\n')
    namespace['main']=main

def run_support_fixtures(argv):
    parser=argparse.ArgumentParser();parser.add_argument('--real-composed',action='store_true')
    parser.parse_args(argv)
    verify_current();historical(SUPPORT,FIXTURE,argv)
    subprocess.run([sys.executable,'-B',str(ROOT/TEST)],cwd=ROOT,check=True,env=ENV)
    verify_current()
