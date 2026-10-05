#!/usr/bin/env python3
"""Adversarial release fixtures; no compiler evidence or working-tree mutation."""
import copy
import stat
import unittest
import sys
sys.dont_write_bytecode = True
import point4_manifold_heat_release_guard as release


class ManifoldReleaseGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.guard = release.c2_guard()
        cls.baseline = release.baseline_sources()
        cls.expected = release.expected_sources()
        cls.root_metadata = (release.ROOT / 'curvature/formalization.yaml').read_text()
        cls.new_metadata = (release.ROOT / release.METADATA).read_text()

    def test_exact_count_one_digest_pinned_inherited_adapter(self):
        original = self.baseline[release.C2_GUARD][1]
        expected = release.adapted_c2_guard(original)
        self.assertEqual(expected, (release.ROOT / release.C2_GUARD).read_bytes())
        self.assertEqual(expected.decode().count(release.C2_ADAPTER), 1)
        for wrong in (original + b'\n', original.replace(b'check_audit', b'waive_audit'), expected,
                      original.replace(release.ENTRY_POINT.encode(), b''),
                      original + release.ENTRY_POINT.encode()):
            with self.subTest(identity=release.sha256(wrong)), self.assertRaises(AssertionError):
                release.adapted_c2_guard(wrong)
        for wrong in (expected.replace(release.C2_ADAPTER.encode(), b''), expected + b'\n',
                      expected.replace(release.C2_ADAPTER.encode(), release.C2_ADAPTER.encode() * 2),
                      expected.replace(b'check_audit', b'waive_audit')):
            with self.assertRaises(AssertionError):
                self.guard.check_equal(release.C2_GUARD, wrong, expected)

    def test_legacy_reconstruction_runs_and_gate_functions_are_untouched(self):
        namespace = release._joint_release().joint_reset_c2_namespace(vars(self.guard), install_manifold=False)
        names = ('main', 'check_imports', 'check_metadata', 'check_axiom_output',
                 'check_boundaryless_types', 'check_audit', 'check_workflow',
                 'check_public_paths', 'public_paths', 'nul_paths')
        before = {name: namespace[name] for name in names}
        release.install_c2_inventory_adapter(namespace)
        self.assertEqual({name: namespace[name] for name in names}, before)
        self.assertEqual(set(namespace['expected_sources']()), set(self.expected))
        with self.assertRaises(AssertionError):
            release.install_c2_inventory_adapter(namespace)
        for key in ('EDITABLE', 'ADDED'):
            wrong = release._joint_release().joint_reset_c2_namespace(vars(self.guard), install_manifold=False)
            wrong[key] = set(wrong[key]) | {'arbitrary/exception.lean'}
            with self.subTest(key=key), self.assertRaises(AssertionError):
                release.install_c2_inventory_adapter(wrong)

    def test_every_inherited_file_and_r2_proof_probe_and_fixture_is_pinned(self):
        self.assertEqual(len(self.baseline), 1641)
        for path, (_, original) in self.baseline.items():
            wanted = (release.adapted_c2_guard(original) if path == release.C2_GUARD else
                      release._joint_release().adapted_startup_workflow(path, original) if path in release._joint_release().STARTUP_WORKFLOWS else original)
            with self.subTest(path=path):
                self.assertEqual((release.ROOT / path).read_bytes(), wanted)
                with self.assertRaises(AssertionError):
                    self.guard.check_equal(path, wanted + b'\nunauthorized edit\n', wanted)
        for path in release.R2_FILE_SHA256:
            actual = (release.ROOT / path).read_bytes()
            release.check_unit_blob(path, actual)
            if path != release.PROBE and (path.endswith('.lean') or path.endswith('point4_manifold_heat_mock_test.py')):
                self.assertEqual(release.sha256(actual), release.R2_FILE_SHA256[path])
        for path in release.UNIT_FILE_SHA256:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_unit_blob(path, (release.ROOT / path).read_bytes() + b'\n')
        with self.assertRaises(AssertionError):
            release.check_unit_blob('unknown.lean', b'')

    def test_exact_count_one_printer_repair_preserves_all_probe_commands(self):
        original = release.git('show', f'{release.PROBE_ORIGINAL_HEAD}:{release.PROBE}')
        actual = (release.ROOT / release.PROBE).read_bytes()
        self.assertEqual(actual, release.repaired_probe(original))
        self.assertEqual(actual.replace(release.PROBE_NEW_OPTION, release.PROBE_OLD_OPTION, 1), original)
        commands = lambda data: [line for line in data.splitlines() if line.startswith(b'#')]
        self.assertEqual(commands(actual), commands(original))
        self.assertEqual(sum(line.startswith(b'#print axioms ') for line in commands(actual)), 11)
        self.assertEqual(sum(line.startswith(b'#check @') for line in commands(actual)), 4)
        for wrong in (original + b'\n', actual,
                      original.replace(release.PROBE_OLD_OPTION, b''),
                      original.replace(release.PROBE_OLD_OPTION, release.PROBE_OLD_OPTION * 2),
                      original.replace(b'#check @', b'#check ', 1)):
            with self.subTest(identity=release.sha256(wrong)), self.assertRaises(AssertionError):
                release.repaired_probe(wrong)
        for wrong in (original, actual + b'\n',
                      actual.replace(release.PROBE_NEW_OPTION, b'set_option format.width 80\n'),
                      actual.replace(b'#print axioms ', b'#check ', 1)):
            with self.subTest(identity=release.sha256(wrong)), self.assertRaises(AssertionError):
                release.check_unit_blob(release.PROBE, wrong)

    def test_precise_public_union_no_missing_or_arbitrary_extra_path(self):
        valid = release.public_paths()
        self.assertEqual(len(valid), 1661)
        release.check_public_paths(valid)
        for path in valid:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_public_paths(valid - {path})
        for path in ('extra.lean', 'extra.txt', '.github/workflows/unknown.yml',
                     'curvature/scripts/unknown.py', 'docs/point4/unapproved.md',
                     'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/CanonicalTarget.lean',
                     'name\nwith-newline.bin'):
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_public_paths(valid | {path})

    def test_tracked_cache_and_non_cache_noise_are_never_exempted(self):
        valid = release.public_paths()
        generated = 'curvature/scripts/__pycache__/point4_scan.cpython-311.pyc'
        release.check_public_paths(self.guard.public_paths(valid, {generated}))
        for path in (generated, '__pycache__/arbitrary.txt', '__pycache__/hidden.lean',
                     '__pycache__/unknown.pyc', '__pycache__/nested\npublic.bin'):
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_public_paths(self.guard.public_paths(valid | {path}, set()))
        for path in ('__pycache__/arbitrary.txt', '__pycache__/hidden.lean', '__pycache__/unknown.pyc'):
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_public_paths(self.guard.public_paths(valid, {path}))
        self.assertEqual(self.guard.nul_paths(b'one\ntwo\0three\0'), {'one\ntwo', 'three'})
        with self.assertRaises(AssertionError):
            self.guard.nul_paths(b'not terminated')

    def test_physical_lean_union_no_ignored_or_hidden_canonical_target(self):
        valid = {path for path in release.public_paths() if path.endswith('.lean')}
        release.check_physical_lean(valid)
        for path in valid:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_physical_lean(valid - {path})
        for path in ('ignored/hidden.lean', '__pycache__/hidden.lean', 'CanonicalTarget.lean'):
            with self.assertRaises(AssertionError):
                release.check_physical_lean(valid | {path})

    def test_regular_file_modes_reject_symlink_and_executable_drift(self):
        release.check_mode('plain', stat.S_IFREG | 0o644, '100644')
        release.check_mode('script', stat.S_IFREG | 0o755, '100755')
        for mode, wanted in ((stat.S_IFLNK | 0o777, '100644'), (stat.S_IFDIR | 0o755, '100644'),
                             (stat.S_IFREG | 0o755, '100644'), (stat.S_IFREG | 0o644, '100755')):
            with self.subTest(mode=mode, wanted=wanted), self.assertRaises(AssertionError):
                release.check_mode('path', mode, wanted)
        release.check_modes()

    def test_root_imports_and_all_selected_metadata_are_byte_identical(self):
        root_path = 'curvature/PoincareCurvature.lean'
        actual = (release.ROOT / root_path).read_bytes()
        self.assertEqual(actual, self.baseline[root_path][1])
        release.check_root_metadata(self.root_metadata)
        for wrong in (self.root_metadata + '\n',
                      self.root_metadata.replace('David Barros Hulak', 'Other author'),
                      self.root_metadata.replace('Apache-2.0', 'MIT'),
                      self.root_metadata.replace('GPT-5 Codex', 'Other model'),
                      self.root_metadata.replace('version: "v0.4"', 'version: "v0.3"'),
                      self.root_metadata.replace('relationship: "builds-on"', 'relationship: "formalizes"', 1)):
            with self.assertRaises(AssertionError):
                release.check_root_metadata(wrong)
        for wrong in (actual + b'import Unauthorized.Module\n', actual + b'def wrong := 0\n'):
            with self.assertRaises(AssertionError):
                self.guard.check_equal(root_path, wrong, self.baseline[root_path][1])

    def test_new_provenance_rejects_duplicate_keys_id_and_semantic_drift(self):
        release.check_new_metadata(self.new_metadata)
        relationship = '    relationship: "builds-on"\n'
        first_id = next(line for line in self.new_metadata.splitlines() if line.startswith('  - id:'))
        cases = (
            self.new_metadata.replace(relationship, relationship + '    relationship: "independent"\n', 1),
            self.new_metadata.replace(first_id + '\n', first_id + '\n    id: "https://example.invalid/wrong"\n', 1),
            self.new_metadata.replace('    note: >-\n', '    note: "overwritten"\n    note: >-\n', 1),
            self.new_metadata.replace(relationship, relationship + '    unexpected: "field"\n', 1),
            self.new_metadata.replace(relationship, '    relationship: "formalizes"\n', 1),
            self.new_metadata.replace(first_id, '  - id: ["not-a-string"]', 1),
            self.new_metadata.replace('version: "v0.4"\n', 'version: "v0.4"\n"version": "v0.3"\n', 1),
            self.new_metadata.replace('review:\n  status: "pending"', 'review:\n  status: "approved"'),
            self.new_metadata.replace('Point-4 theorem remains absent and OPEN', 'Point-4 theorem is CLOSED'),
        )
        for wrong in cases:
            with self.assertRaises(AssertionError):
                release.check_new_metadata(wrong)
        marker = 'related_formalizations:\n'
        first = self.new_metadata.split(marker, 1)[1].split('  - id:', 2)[1]
        with self.assertRaises(AssertionError):
            release.check_new_metadata(self.new_metadata.replace(marker, marker + '  - id:' + first))

    def test_inherited_workflows_and_focused_evidence_are_pinned(self):
        for path, (_, data) in self.baseline.items():
            if path.startswith('.github/workflows/'):
                self.assertEqual((release.ROOT / path).read_bytes(), data)
        workflow = (release.ROOT / release.WORKFLOW).read_bytes()
        release.check_unit_blob(release.WORKFLOW, workflow)
        replacements = (
            (b'persist-credentials: false', b'persist-credentials: true'),
            (b'contents: read', b'contents: write'), (b'fetch-depth: 0', b'fetch-depth: 1'),
            (b'lake build PoincareCurvature.', b'echo skipped PoincareCurvature.'),
            (b'scripts/point4_closed_contract_regression.lean', b'scripts/missing.lean'),
            (b'bash scripts/point4_audit.sh --json', b'echo skip --json'),
            (b'--axiom-dir /tmp/point4-manifold-heat-inherited-probes', b'--no-axiom-evidence'),
            (b'point4_c2_initial_heat_mock_test.py', b'missing_test.py'),
            (b'point4_linear_heat_geometry_mock_test.py', b'missing_test.py'),
            (b'point4_manifold_heat_mock_test.py', b'missing_test.py'),
        )
        for before, after in replacements:
            self.assertIn(before, workflow)
            with self.subTest(before=before), self.assertRaises(AssertionError):
                release.check_unit_blob(release.WORKFLOW, workflow.replace(before, after, 1))

    def test_new_probe_rejects_missing_duplicate_axiom_records_and_scope_drift(self):
        import re
        probe = (release.ROOT / 'curvature/scripts/point4_manifold_heat_probe.lean').read_text()
        names = re.findall(r'^#print axioms (\S+)', probe, re.M)
        self.assertEqual(len(names), 11)
        output = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)
        output += '\nMANIFOLD_HEAT_TYPES_BEGIN\n' + 'BoundarylessManifold I M\n' * 4 + 'MANIFOLD_HEAT_TYPES_END\n'
        release.check_new_probe(output)
        for wrong in ('\n'.join(output.splitlines()[1:]), output.splitlines()[0] + '\n' + output,
                      output.replace('Quot.sound', 'propext', 1),
                      output.replace('Quot.sound', 'Custom.axiom', 1),
                      output.replace('BoundarylessManifold I M', 'I.Boundaryless', 1),
                      output + '\nMANIFOLD_HEAT_TYPES_BEGIN',
                      output + "\n'extra' does not depend on any axioms"):
            with self.assertRaises(AssertionError):
                release.check_new_probe(wrong)

    def test_full_open_audit_cannot_accept_a_hidden_canonical_target_or_false_closure(self):
        data = {'build_run': True, 'target_base': 'intrinsicLocalExistenceUniquenessFamily_pointFour',
                'fqn': '', 'verdict': 'OPEN', 'gates': {
                    'G1_sorry_free': {'status': 'PASS'}, 'G2_build_green': {'status': 'PASS'},
                    'G3_unconditional': {'status': 'FAIL'}, 'G4_axiom_clean': {'status': 'FAIL'},
                    'G5_faithful_type': {'status': 'FAIL'}}}
        self.guard.check_audit(data, 1)
        for key, value in (('build_run', False), ('build_run', 1), ('fqn', 'RicciFlow.intrinsicLocalExistenceUniquenessFamily_pointFour'),
                           ('target_base', 'other'), ('verdict', 'CLOSED')):
            wrong = copy.deepcopy(data); wrong[key] = value
            with self.subTest(key=key), self.assertRaises(AssertionError):
                self.guard.check_audit(wrong, 1)
        wrong = copy.deepcopy(data); wrong['verdict'] = 'CLOSED'
        for gate in wrong['gates'].values():
            gate['status'] = 'PASS'
        with self.assertRaises(AssertionError):
            self.guard.check_audit(wrong, 0)


if __name__ == '__main__':
    unittest.main()
