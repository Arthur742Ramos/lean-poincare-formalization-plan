#!/usr/bin/env python3
"""Negative source/evidence fixtures; no compiler and no working-tree mutations."""
import copy
import unittest
import point4_linear_heat_geometry_source_test as guard


class IntegrationGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.metadata = (guard.ROOT / 'curvature/formalization.yaml').read_text()
        cls.root_imports = (guard.ROOT / guard.LIBROOT).read_bytes()
        cls.expected = guard.expected_sources()

    def test_every_parent_blob_matches(self):
        for path, (_, expected) in self.expected.items():
            guard.check_equal(path, (guard.ROOT / path).read_bytes(), expected)

    def test_each_protected_blob_rejects_mutation(self):
        for path, (_, expected) in self.expected.items():
            with self.subTest(path=path), self.assertRaises(AssertionError):
                guard.check_equal(path, expected + b'\n-- unauthorized edit\n', expected)

    def test_root_union(self):
        guard.check_imports(self.root_imports)

    def test_missing_contract_import(self):
        changed = b'\n'.join(l for l in self.root_imports.splitlines() if b'PointFourContract' not in l)
        with self.assertRaises(AssertionError):
            guard.check_imports(changed)

    def test_missing_actual_rhs_import(self):
        changed = b'\n'.join(l for l in self.root_imports.splitlines() if b'StandardRicciDeTurckCoordinateOperator' not in l)
        with self.assertRaises(AssertionError):
            guard.check_imports(changed)

    def test_hidden_root_declaration(self):
        with self.assertRaises(AssertionError):
            guard.check_imports(self.root_imports + b'\ndef wrong := 0\n')

    def test_metadata(self):
        guard.check_metadata(self.metadata)
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace('Immutable combined spatial-stack source', 'Changed provenance note'))
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace('relationship: "builds-on"', 'relationship: "formalizes"', 1))

    def test_missing_each_parent_provenance(self):
        for sha in (guard.BASE, *guard.PARENTS):
            with self.subTest(sha=sha), self.assertRaises(AssertionError):
                guard.check_metadata(self.metadata.replace(sha, '0' * 40))

    def test_changed_model_history(self):
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace('GPT-5 Codex', 'Other model'))

    def test_changed_authorship(self):
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace('David Barros Hulak', 'Other author'))

    def test_changed_license(self):
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace('Apache-2.0', 'MIT'))

    def test_each_probe_rejects_missing_extra_and_disallowed_axioms(self):
        for name in guard.PROBES:
            source = (guard.ROOT / f'curvature/scripts/point4_{name}_probe.lean').read_text()
            names = guard.re.findall(r'^#print axioms (\S+)', source, guard.re.M)
            output = '\n'.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
            self.assertEqual(guard.check_axiom_output(source, output), set(names))
            for bad in ('\n'.join(output.splitlines()[1:]), output + "\n'extra' does not depend on any axioms", output.replace('Quot.sound', 'sorryAx'), output + '\n' + output.splitlines()[0]):
                with self.subTest(probe=name), self.assertRaises(AssertionError):
                    guard.check_axiom_output(source, bad)

        types = 'BOUNDARYLESS_TYPES_BEGIN\n' + 'BoundarylessManifold\n' * 7 + 'BOUNDARYLESS_TYPES_END'
        guard.check_boundaryless_types(types)
        for bad in (types.replace('BoundarylessManifold\n', '', 1), types.replace('BoundarylessManifold', 'ModelWithCorners.Boundaryless'), types.replace('BoundarylessManifold', 'I.Boundaryless')):
            with self.assertRaises(AssertionError):
                guard.check_boundaryless_types(bad)

    def test_full_open_audit_and_negative_fixtures(self):
        data = {'build_run': True, 'target_base': 'intrinsicLocalExistenceUniquenessFamily_pointFour', 'verdict': 'OPEN', 'gates': {
            'G1_sorry_free': {'status': 'PASS'}, 'G2_build_green': {'status': 'PASS'},
            'G3_unconditional': {'status': 'FAIL'}, 'G4_axiom_clean': {'status': 'FAIL'},
            'G5_faithful_type': {'status': 'FAIL'}}}
        guard.check_audit(data, 1)
        cases = []
        bad = copy.deepcopy(data); bad['build_run'] = False; cases.append((bad, 1))
        bad = copy.deepcopy(data); bad['verdict'] = 'CLOSED'; cases.append((bad, 0))
        cases.append((data, 0))
        for key in data['gates']:
            bad = copy.deepcopy(data)
            bad['gates'][key]['status'] = 'FAIL' if key in ('G1_sorry_free', 'G2_build_green') else 'PASS'
            cases.append((bad, 1))
        for bad, rc in cases:
            with self.assertRaises(AssertionError):
                guard.check_audit(bad, rc)


if __name__ == '__main__':
    from point4_weighted_hessian_release_guard import run_inherited
    run_inherited('curvature/scripts/point4_linear_heat_geometry_mock_test.py')
