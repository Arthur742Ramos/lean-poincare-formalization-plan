#!/usr/bin/env python3
"""Scalar unit checks. Source fixtures are not compiler or canonical evidence."""
from __future__ import annotations
import argparse
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCE = 'curvature/PoincareCurvature/Analysis/C2Resonance.lean'
PROBE = 'curvature/scripts/point4_c2_resonance_probe.lean'
DOC = 'docs/point4/c2-resonance.md'
METADATA = 'docs/point4/c2-resonance/formalization.yaml'
WORKFLOW = '.github/workflows/point4-c2-resonance.yml'
GUARD = 'curvature/scripts/point4_c2_resonance_guard.py'
TEST = 'curvature/scripts/point4_c2_resonance_mock_test.py'
UNIT_PATHS = frozenset({SOURCE, PROBE, DOC, METADATA, WORKFLOW, GUARD, TEST})
BASE = 'a0132cd55e2540b2fd26adecea9a07b51f1b8292'
SMOOTH_PARENT = '229533f83c83e45e8b7725adda50b53d88699aba'
MATHLIB = 'db584cd6d46c92f209a44c0f1c829460d327499d'
NAMES = tuple('RicciFlow.C2Resonance.' + name for name in (
    'hasDerivAt_profile', 'hasDerivAt_profileSlope',
    'resonant_profile_identity', 'tendsto_profile_atBot'))
STANDARD_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
# These five source identities and exact printed types are generated from the
# reviewed scalar bytes and recorded owned exact-4.33 type oracle. The staged
# integration adapter must independently bind all seven unit blobs and modes.
PINNED = {'curvature/PoincareCurvature/Analysis/C2Resonance.lean': 'f2c0f2ec234e570e626e0ae436a5de156465b15d17b4ca3d73e8ec10b4df61cc', 'curvature/scripts/point4_c2_resonance_probe.lean': '9bd3092ffc5bcf090e12473492f1d6f488a8848df72fc230e664cceed7085ee3', 'docs/point4/c2-resonance.md': 'd3465cce3f95243c8d74dfe8cd5ce4a4a9a749b52c1fd4b67cebdc11f12abf5f', 'docs/point4/c2-resonance/formalization.yaml': '33c022bac42fa4c90a0bee496664750407c0245bd2f83a5508f6e14b88007f33', '.github/workflows/point4-c2-resonance.yml': 'e4f39177d37c5edba8815c97c5d348f4341fe6db9363484f20b326db1978ae74'}
EXPECTED_TYPES = 'RicciFlow.C2Resonance.hasDerivAt_profile : ∀ (ε L : ℝ), Ne.{1} L 0 → HasDerivAt.{0, 0} (RicciFlow.C2Resonance.profile ε) (RicciFlow.C2Resonance.profileSlope ε L) L RicciFlow.C2Resonance.hasDerivAt_profileSlope : ∀ (ε L : ℝ), Ne.{1} L 0 → HasDerivAt.{0, 0} (RicciFlow.C2Resonance.profileSlope ε) (RicciFlow.C2Resonance.profileSecond ε L) L RicciFlow.C2Resonance.resonant_profile_identity : ∀ (ε L : ℝ), Ne.{1} L 0 → Eq.{1} (HSub.hSub.{0, 0, 0} (RicciFlow.C2Resonance.profileSecond ε L) (HMul.hMul.{0, 0, 0} 4 (RicciFlow.C2Resonance.profileSlope ε L))) (HMul.hMul.{0, 0, 0} ε (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 6 L) (HDiv.hDiv.{0, 0, 0} 5 (HMul.hMul.{0, 0, 0} 2 (HPow.hPow.{0, 0, 0} L 2)))) (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 2 (HPow.hPow.{0, 0, 0} L 3))))) RicciFlow.C2Resonance.tendsto_profile_atBot : ∀ (ε : ℝ), LT.lt.{0} 0 ε → Filter.Tendsto.{0, 0} (RicciFlow.C2Resonance.profile ε) Filter.atTop.{0} Filter.atBot.{0}'


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_unit_blobs(blobs: dict[str, bytes]) -> None:
    assert set(blobs) == set(PINNED), 'Missing/extra digest-pinned scalar blob'
    for path, wanted in PINNED.items():
        assert sha256(blobs[path]) == wanted, f'Scalar source identity changed: {path}'


def check_probe(output: str) -> None:
    assert not re.search(r'\b(?:error|warning):', output), 'Compiler diagnostic in probe evidence'
    assert output.count('C2_RESONANCE_TYPES_BEGIN') == 1
    assert output.count('C2_RESONANCE_TYPES_END') == 1
    start = output.index('C2_RESONANCE_TYPES_BEGIN')
    end = output.index('C2_RESONANCE_TYPES_END')
    assert start < end, 'Reversed type markers'
    actual_types = output[start + len('C2_RESONANCE_TYPES_BEGIN'):end]
    normalize = lambda text: ' '.join(text.split())
    assert normalize(actual_types) == EXPECTED_TYPES, 'Full scalar theorem types changed'
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [name for name, _ in entries] + clean
    assert len(names) == len(NAMES) and set(names) == set(NAMES), 'Missing/extra/duplicate scalar axiom record'
    for name, fields in entries:
        # The two universe-polymorphic standard axioms may print .{u}; propext
        # has no universe annotation. Reject every other spelling explicitly.
        raw_axioms = [field.strip() for field in fields.split(',') if field.strip()]
        assert set(raw_axioms) <= {'propext', 'Classical.choice', 'Classical.choice.{u}',
                                  'Quot.sound', 'Quot.sound.{u}'}, (name, raw_axioms)
        axioms = [field.removesuffix('.{u}') for field in raw_axioms]
        assert len(axioms) == len(set(axioms)), 'Duplicate axiom entry'
        assert set(axioms) <= STANDARD_AXIOMS, (name, axioms)


def check_metadata(source: str) -> None:
    import point4_c2_initial_heat_source_test as inherited
    parsed = inherited.parse_metadata(source)
    entries = inherited.metadata_entries(source)
    assert set(entries) == {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{SMOOTH_PARENT}/curvature',
        f'https://github.com/leanprover-community/mathlib4/tree/{MATHLIB}/Mathlib/Analysis',
    }, 'Scalar parsed provenance inventory drift'
    assert all(value[0] == 'builds-on' for value in entries.values()), 'Scalar provenance relationship drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope']
    assert parsed['review']['status'] == 'pending'
    assert sha256(source.encode()) == PINNED[METADATA], 'Scalar metadata bytes changed'


def check_sources() -> None:
    check_unit_blobs({path: (ROOT / path).read_bytes() for path in PINNED})
    check_metadata((ROOT / METADATA).read_text(encoding='utf-8'))


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
    parser.add_argument('--probe-log', type=pathlib.Path)
    args = parser.parse_args(argv)
    # The separately reviewed staged smooth/scalar adapter must validate the
    # complete composed inventory before entering this inherited gate. Its
    # exact bytes, fixed unit paths, and exception unwind have separate review.
    # Enter through the reviewed hook: it verifies smooth mode and full hash
    # before importing any smooth executable. Use only its bound module.
    import point4_manifold_heat_release_guard as trusted_release
    inherited_release = trusted_release._smooth_release
    inherited_release.main(['--schema', str(args.schema)] if args.schema else [])
    check_sources()
    if args.schema:
        import jsonschema
        import point4_c2_initial_heat_source_test as inherited
        data = args.schema.read_bytes()
        assert sha256(data) == inherited.SCHEMA_SHA256
        jsonschema.validate(inherited.parse_metadata((ROOT / METADATA).read_text(encoding='utf-8')), json.loads(data))
    if args.probe_log:
        check_probe(args.probe_log.read_text(encoding='utf-8'))
    print(json.dumps({'scalar_paths': sorted(UNIT_PATHS), 'probe_evidence_checked': bool(args.probe_log),
                      'lean_verified': False, 'point4': 'OPEN'}))
    print('Scalar supporting unit checked; exact-head builds, full inherited gates and independent review are separate')


# BEGIN exact finite auxiliary-136
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == '21bc25ee9c5916a0675d48fa79f89d834e60c9cec184437bdbdab77bf5abcd6d', "Auxiliary composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
_curvature_comp.install_curvature_auxiliary(globals(),136)
# END exact finite auxiliary-136

if __name__ == '__main__':
    main()
