#!/usr/bin/env python3
"""Synthetic rejection fixtures. No test output certifies a Lean theorem."""

# BEGIN exact finite auxiliary-136
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == 'c82ce9939d310076d1b40ce72017e05a20ee22db12ce332a61537a4f8e77f264', "Auxiliary composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
if __name__ == '__main__':
    _curvature_comp.run_curvature_auxiliary_mocks(136,'curvature/scripts/point4_c2_resonance_mock_test.py',_curvature_sys.argv[1:])
    raise SystemExit(0)
# END exact finite auxiliary-136
import sys
import types
import unittest
import hashlib
import os
import pathlib
import stat
import subprocess
import tempfile
from unittest import mock
import point4_c2_resonance_guard as scalar


class ScalarEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.blobs = {path: (scalar.ROOT / path).read_bytes() for path in scalar.PINNED}
        cls.output = '\n'.join(
            f"'{name}' depends on axioms: [propext, Classical.choice.{{u}}, Quot.sound.{{u}}]"
            for name in scalar.NAMES)
        cls.output += '\nC2_RESONANCE_TYPES_BEGIN\n' + scalar.EXPECTED_TYPES + '\nC2_RESONANCE_TYPES_END\n'

    def test_exact_source_and_explicit_unit_paths(self):
        scalar.check_unit_blobs(self.blobs)
        self.assertEqual(len(scalar.UNIT_PATHS), 7)
        self.assertEqual(len(scalar.PINNED), 5)
        self.assertEqual(scalar.PINNED[scalar.SOURCE], 'f2c0f2ec234e570e626e0ae436a5de156465b15d17b4ca3d73e8ec10b4df61cc')
        self.assertEqual(set(scalar.PINNED) | {scalar.GUARD, scalar.TEST}, set(scalar.UNIT_PATHS))

    def test_each_pinned_blob_rejects_any_body_edit(self):
        for path in self.blobs:
            wrong = dict(self.blobs); wrong[path] += b'\n'
            with self.subTest(path=path), self.assertRaises(AssertionError):
                scalar.check_unit_blobs(wrong)

    def test_each_missing_blob_and_arbitrary_extra_rejected(self):
        for path in self.blobs:
            wrong = dict(self.blobs); del wrong[path]
            with self.subTest(path=path), self.assertRaises(AssertionError):
                scalar.check_unit_blobs(wrong)
        for path in ('extra.lean', 'CanonicalTarget.lean', scalar.GUARD):
            with self.subTest(path=path), self.assertRaises(AssertionError):
                scalar.check_unit_blobs(dict(self.blobs, **{path: b''}))

    def test_full_exact_synthetic_probe_and_whitespace_normalization(self):
        scalar.check_probe(self.output)
        scalar.check_probe(self.output.replace(scalar.EXPECTED_TYPES, scalar.EXPECTED_TYPES.replace(' ', '  ')))

    def test_type_markers_must_be_unique_and_ordered(self):
        for wrong in (self.output.replace('C2_RESONANCE_TYPES_BEGIN', ''),
                      self.output.replace('C2_RESONANCE_TYPES_END', ''),
                      self.output + 'C2_RESONANCE_TYPES_BEGIN\n',
                      self.output + 'C2_RESONANCE_TYPES_END\n',
                      self.output.replace('C2_RESONANCE_TYPES_BEGIN', 'TEMP').replace('C2_RESONANCE_TYPES_END', 'C2_RESONANCE_TYPES_BEGIN').replace('TEMP', 'C2_RESONANCE_TYPES_END')):
            with self.assertRaises(AssertionError): scalar.check_probe(wrong)

    def test_full_types_reject_missing_nonzero_or_positive_domain(self):
        for before, after in (('Ne.{1} L 0 →', ''), ('LT.lt.{0} 0 ε →', ''),
                              ('Ne.{1} L 0', 'Ne.{1} L 1'), ('LT.lt.{0} 0 ε', 'LT.lt.{0} ε 0')):
            self.assertIn(before, self.output)
            with self.subTest(before=before), self.assertRaises(AssertionError):
                scalar.check_probe(self.output.replace(before, after, 1))

    def test_full_types_reject_changed_operator_sign_or_conclusion(self):
        for before, after in (('Filter.atBot.{0}', 'Filter.atTop.{0}'),
                              ('HSub.hSub.', 'HAdd.hAdd.'), ('HPow.hPow.{0, 0, 0} L 3', 'HPow.hPow.{0, 0, 0} L 4'),
                              ('HasDerivAt.{0, 0}', 'ContinuousAt.{0}')):
            self.assertIn(before, self.output)
            with self.subTest(before=before), self.assertRaises(AssertionError):
                scalar.check_probe(self.output.replace(before, after, 1))

    def test_axiom_records_reject_missing_extra_or_duplicate_declarations(self):
        first = self.output.splitlines()[0] + '\n'
        for wrong in (self.output.removeprefix(first), first + self.output,
                      self.output + "'extra' does not depend on any axioms\n"):
            with self.assertRaises(AssertionError): scalar.check_probe(wrong)

    def test_axiom_records_reject_duplicate_custom_sorry_or_wrong_universes(self):
        for replacement in ('Custom.KrylovSafonov', 'sorryAx', 'Classical.choice.{v}', 'propext', 'Quot.sound.{u}, Quot.sound.{u}'):
            with self.subTest(replacement=replacement), self.assertRaises(AssertionError):
                scalar.check_probe(self.output.replace('Quot.sound.{u}', replacement, 1))
        with self.assertRaises(AssertionError):
            scalar.check_probe(self.output.replace('propext', 'propext.{u}', 1))

    def test_compiler_diagnostics_rejected_even_with_complete_records(self):
        for diagnostic in ('error: failed elaboration', "warning: declaration uses 'sorry'"):
            with self.assertRaises(AssertionError): scalar.check_probe(self.output + diagnostic)

    def test_inherited_gate_failure_propagates_before_unit_validation(self):
        def failed_gate(argv): raise RuntimeError('inherited-gate-failed')
        module = types.SimpleNamespace(main=failed_gate)
        trusted = types.SimpleNamespace(_smooth_release=module)
        with mock.patch.dict(sys.modules, {'point4_manifold_heat_release_guard': trusted}), \
             mock.patch.object(scalar, 'check_sources') as check:
            with self.assertRaisesRegex(RuntimeError, 'inherited-gate-failed'):
                scalar.main([])
            check.assert_not_called()

    def test_inherited_schema_argument_and_unit_failure_are_not_swallowed(self):
        calls = []
        module = types.SimpleNamespace(main=lambda argv: calls.append(argv))
        trusted = types.SimpleNamespace(_smooth_release=module)
        with mock.patch.dict(sys.modules, {'point4_manifold_heat_release_guard': trusted}), \
             mock.patch.object(scalar, 'check_sources', side_effect=AssertionError('scalar-unit-failed')):
            with self.assertRaisesRegex(AssertionError, 'scalar-unit-failed'):
                scalar.main(['--schema', 'exact-schema.json'])
        self.assertEqual(calls, [['--schema', 'exact-schema.json']])


class ScalarFreshProcessBootstrapTests(unittest.TestCase):
    """Real direct-main imports in new interpreters, with private attack files.

    Windows lstat lacks Unix executable/symlink representations. Only that
    external filesystem result is injected for those two local cases; Linux
    uses actual chmod/symlink files. No production admission rule inspects
    fixture names, flags, caller identity or platform-specific test choices.
    """
    child = '''import pathlib, stat, sys, types
scripts = pathlib.Path(sys.argv[1])
sys.path.insert(0, str(scripts))
target = scripts / 'point4_smooth_forward_release_guard.py'
marker = target.with_name('malicious-executed.marker')
if sys.argv[2] in ('windows-executable', 'windows-symlink'):
    original_lstat = pathlib.Path.lstat
    bad_mode = stat.S_IFREG | 0o755 if sys.argv[2] == 'windows-executable' else stat.S_IFLNK | 0o777
    def fixture_lstat(path):
        return types.SimpleNamespace(st_mode=bad_mode) if path == target else original_lstat(path)
    pathlib.Path.lstat = fixture_lstat
import point4_c2_resonance_guard as scalar
try:
    scalar.main([])
except (AssertionError, OSError) as error:
    assert not marker.exists(), 'Malicious smooth top-level code executed'
    assert 'point4_smooth_forward_release_guard' not in sys.modules, 'Smooth executable was imported'
    print('REJECTED_BEFORE_SMOOTH_IMPORT:' + type(error).__name__)
else:
    raise AssertionError('Direct scalar entry admitted attack')
'''
    malicious = b"from pathlib import Path\nPath(__file__).with_name('malicious-executed.marker').write_text('MALICIOUS_TOP_EXECUTED\\n')\nraise RuntimeError('MALICIOUS_TOP_EXECUTED')\n"

    def private_files(self, root):
        scripts = root/'curvature/scripts'
        scripts.mkdir(parents=True)
        for name in ('point4_c2_resonance_guard.py', 'point4_manifold_heat_release_guard.py',
                     'point4_smooth_forward_release_guard.py'):
            (scripts/name).write_bytes((scalar.ROOT/'curvature/scripts'/name).read_bytes())
        return scripts

    def attack(self, kind):
        with tempfile.TemporaryDirectory() as directory:
            scripts = self.private_files(pathlib.Path(directory))
            target = scripts/'point4_smooth_forward_release_guard.py'
            hook = scripts/'point4_manifold_heat_release_guard.py'
            original_hash = hashlib.sha256(target.read_bytes()).hexdigest()
            fixture = 'physical'
            if kind == 'missing':
                target.unlink()
            else:
                target.write_bytes(self.malicious)
                if kind in ('executable', 'symlink'):
                    # Bind the payload's exact hash in this private hook so the
                    # independent mode rejection is not confounded by hash drift.
                    text = hook.read_text(encoding='utf-8')
                    self.assertEqual(text.count(original_hash), 2)
                    hook.write_text(text.replace(original_hash, hashlib.sha256(self.malicious).hexdigest()), encoding='utf-8')
                    if os.name == 'nt':
                        fixture = 'windows-' + kind
                    elif kind == 'executable':
                        target.chmod(0o755)
                    else:
                        payload = scripts/'attack-payload.py'
                        payload.write_bytes(self.malicious)
                        target.unlink()
                        target.symlink_to(payload.name)
            result = subprocess.run([sys.executable, '-I', '-B', '-c', self.child, str(scripts), fixture],
                                    cwd=directory, capture_output=True, text=True, encoding='utf-8', timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertTrue(result.stdout.startswith('REJECTED_BEFORE_SMOOTH_IMPORT:'), result.stdout)
            self.assertNotIn('MALICIOUS_TOP_EXECUTED', result.stderr)
            self.assertFalse(target.with_name('malicious-executed.marker').exists())

    def test_fresh_direct_main_rejects_edited_smooth_before_top_level(self):
        self.attack('edited')

    def test_fresh_direct_main_rejects_missing_smooth_before_import(self):
        self.attack('missing')

    def test_fresh_direct_main_rejects_executable_smooth_before_top_level(self):
        self.attack('executable')

    def test_fresh_direct_main_rejects_symlink_smooth_before_top_level(self):
        self.attack('symlink')

    def test_fresh_positive_hook_binds_original_smooth_module(self):
        with tempfile.TemporaryDirectory() as directory:
            scripts = self.private_files(pathlib.Path(directory))
            program = "import sys;sys.path.insert(0,sys.argv[1]);import point4_manifold_heat_release_guard as trusted;assert trusted._smooth_release is sys.modules['point4_smooth_forward_release_guard'];print('TRUSTED_BOOTSTRAP_BOUND')"
            result = subprocess.run([sys.executable, '-I', '-B', '-c', program, str(scripts)],
                                    cwd=directory, capture_output=True, text=True, encoding='utf-8', timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout.strip(), 'TRUSTED_BOOTSTRAP_BOUND')

    def test_retired_direct_import_variant_reproduces_review_witness(self):
        # A harmless private mutation is a negative control for the fixture:
        # restore the rejected direct import, which must execute the marker.
        with tempfile.TemporaryDirectory() as directory:
            scripts = self.private_files(pathlib.Path(directory))
            file = scripts/'point4_c2_resonance_guard.py'
            text = file.read_text(encoding='utf-8')
            safe = '    import point4_manifold_heat_release_guard as trusted_release\n    inherited_release = trusted_release._smooth_release\n'
            self.assertEqual(text.count(safe), 1)
            file.write_text(text.replace(safe, '    import point4_smooth_forward_release_guard as inherited_release\n', 1), encoding='utf-8')
            target = scripts/'point4_smooth_forward_release_guard.py'
            target.write_bytes(self.malicious)
            result = subprocess.run([sys.executable, '-I', '-B', '-c', self.child, str(scripts), 'physical'],
                                    cwd=directory, capture_output=True, text=True, encoding='utf-8', timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('RuntimeError: MALICIOUS_TOP_EXECUTED', result.stderr)
            self.assertTrue(target.with_name('malicious-executed.marker').exists())


class ScalarMetadataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (scalar.ROOT / scalar.METADATA).read_text(encoding='utf-8')

    def test_exact_parsed_provenance_and_pending_scope(self):
        scalar.check_metadata(self.source)

    def test_duplicate_yaml_and_provenance_semantic_drift_rejected(self):
        relation = '    relationship: "builds-on"\n'
        for wrong in (self.source.replace('version: "v0.4"', 'version: "v0.4"\nversion: "v0.3"'),
                      self.source.replace(relation, relation + '    relationship: "independent"\n', 1),
                      self.source.replace(relation, '    relationship: "formalizes"\n', 1),
                      self.source.replace(scalar.BASE, '0' * 40),
                      self.source.replace(scalar.SMOOTH_PARENT, '0' * 40),
                      self.source.replace('status: "pending"', 'status: "approved"'),
                      self.source.replace('remains OPEN', 'is CLOSED')):
            with self.assertRaises(AssertionError): scalar.check_metadata(wrong)


if __name__ == '__main__':
    unittest.main()
