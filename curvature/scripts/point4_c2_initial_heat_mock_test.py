#!/usr/bin/env python3
"""Adversarial source/evidence fixtures; no Lean simulation or source mutations."""
import copy
import unittest
import point4_c2_initial_heat_source_test as guard


class C2IntegrationGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = guard.expected_sources()
        cls.root = (guard.ROOT / guard.LIBROOT).read_bytes()
        cls.metadata = (guard.ROOT / guard.METADATA).read_text()

    def test_every_pinned_public_blob_and_reviewed_adapter(self):
        for path, (_, wanted) in self.expected.items():
            with self.subTest(path=path):
                guard.check_equal(path, (guard.ROOT / path).read_bytes(), wanted)
                with self.assertRaises(AssertionError):
                    guard.check_equal(path, wanted + b'\nunauthorized mutation\n', wanted)

    def test_no_added_or_deleted_public_paths(self):
        expected = set(self.expected)
        actual = expected | guard.EDITABLE | guard.ADDED
        guard.check_public_paths(actual, expected)
        for path in actual:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                guard.check_public_paths(actual - {path}, expected)
        for path in ('extra.lean', '.github/workflows/unknown.yml', 'curvature/scripts/unknown.py'):
            with self.assertRaises(AssertionError):
                guard.check_public_paths(actual | {path}, expected)
        workflow = (guard.ROOT / '.github/workflows/point4-c2-initial-heat.yml').read_bytes()
        guard.check_workflow(workflow)
        for before, after in ((b'persist-credentials: false', b'persist-credentials: true'), (b'contents: read', b'contents: write'), (b'run: lake build', b'run: echo skipped'), (b'scripts/point4_closed_contract_regression.lean', b'scripts/missing.lean'), (b'fetch-depth: 0', b'fetch-depth: 1')):
            with self.subTest(before=before), self.assertRaises(AssertionError):
                guard.check_workflow(workflow.replace(before, after))

    def test_tracked_cache_is_never_exempted(self):
        expected = set(self.expected)
        valid = expected | guard.EDITABLE | guard.ADDED
        generated = 'curvature/scripts/__pycache__/point4_scan.cpython-311.pyc'
        self.assertEqual(guard.public_paths(valid, {generated}), valid)
        for bad in (generated, '__pycache__/arbitrary.txt', 'curvature/scripts/__pycache__/hidden.lean', '__pycache__/nested\npublic.bin'):
            with self.subTest(path=bad), self.assertRaises(AssertionError):
                guard.check_public_paths(guard.public_paths(valid | {bad}, set()), expected)
        for bad in ('__pycache__/arbitrary.txt', 'curvature/scripts/__pycache__/hidden.lean', '__pycache__/unknown.pyc'):
            with self.subTest(path=bad), self.assertRaises(AssertionError):
                guard.check_public_paths(guard.public_paths(valid, {bad}), expected)
        self.assertEqual(guard.nul_paths(b'a\nname\0second\0'), {'a\nname', 'second'})
        with self.assertRaises(AssertionError):
            guard.nul_paths(b'not terminated')

    def test_duplicate_yaml_keys_and_parsed_provenance_drift(self):
        relationship = '    relationship: "builds-on"\n'
        start = self.metadata.index('related_formalizations:\n')
        provenance = self.metadata[start:]
        first_id = next(line for line in provenance.splitlines() if line.startswith('  - id:'))
        note = '    note: >-\n'
        cases = (
            self.metadata.replace(relationship, relationship + '    relationship: "independent"\n', 1),
            self.metadata.replace(first_id + '\n', first_id + '\n' + '    id: "https://example.invalid/wrong"\n', 1),
            self.metadata.replace(note, '    note: "overwritten note"\n' + note, 1),
            self.metadata.replace(relationship, relationship + '    unexpected: "field"\n', 1),
            self.metadata.replace(relationship, '    relationship: "independent"\n', 1),
            self.metadata.replace(first_id, '  - id: ["not-a-string"]', 1),
            self.metadata.replace('version: "v0.4"\n', 'version: "v0.4"\nversion: "v0.3"\n', 1),
        )
        for bad in cases:
            with self.assertRaises(AssertionError):
                guard.check_metadata(bad)
        # Quoted spellings cannot hide a duplicate key from parsed validation.
        with self.assertRaises(AssertionError):
            guard.parse_metadata('key: value\n"key": replacement\n')

    def test_root_union_and_each_missing_import(self):
        guard.check_imports(self.root)
        for line in self.root.splitlines():
            if line.startswith(b'import '):
                with self.subTest(line=line), self.assertRaises(AssertionError):
                    guard.check_imports(self.root.replace(line + b'\n', b''))
        for extra in (self.root.splitlines()[0] + b'\n', b'import Unauthorized.Module\n', b'def wrong := 0\n', b'set_option autoImplicit false\n'):
            with self.assertRaises(AssertionError):
                guard.check_imports(self.root + extra)

    def test_complete_provenance_and_selected_artifact(self):
        guard.check_metadata(self.metadata)
        for identity in guard.metadata_entries(self.metadata):
            with self.subTest(identity=identity), self.assertRaises(AssertionError):
                guard.check_metadata(self.metadata.replace(identity, identity + '/wrong'))
        marker = 'related_formalizations:\n'
        first = self.metadata.split(marker, 1)[1].split('  - id:', 2)[1]
        duplicate = '  - id:' + first
        with self.assertRaises(AssertionError):
            guard.check_metadata(self.metadata.replace(marker, marker + duplicate))
        for before, after in (('David Barros Hulak', 'Other author'), ('Apache-2.0', 'MIT'), ('GPT-5 Codex', 'Other model'), ('Immutable combined spatial-stack source', 'Dropped original note'), ('relationship: "builds-on"', 'relationship: "formalizes"')):
            with self.subTest(before=before), self.assertRaises(AssertionError):
                guard.check_metadata(self.metadata.replace(before, after, 1))

    def test_every_probe_missing_extra_duplicate_and_nonstandard_evidence(self):
        count, distinct = 0, set()
        for probe in guard.PROBES:
            source = (guard.ROOT / f'curvature/scripts/point4_{probe}_probe.lean').read_text()
            names = guard.probe_names(source); count += len(names); distinct |= set(names)
            output = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)
            self.assertEqual(guard.check_axiom_output(source, output), set(names))
            clean = '\n'.join(f"'{name}' does not depend on any axioms" for name in names)
            self.assertEqual(guard.check_axiom_output(source, clean), set(names))
            invalid = ( '\n'.join(output.splitlines()[1:]), output + "\n'extra' does not depend on any axioms", output + '\n' + output.splitlines()[0], output.replace('Quot.sound', 'sorryAx'), output.replace('Quot.sound', 'Custom.axiom'), output.replace('Quot.sound', 'propext'))
            for bad in invalid:
                with self.subTest(probe=probe), self.assertRaises(AssertionError):
                    guard.check_axiom_output(source, bad)
        self.assertEqual((count, len(distinct)), (150, 144))

    def test_exact_boundaryless_type_markers_and_scope(self):
        types = 'BOUNDARYLESS_TYPES_BEGIN\n' + 'BoundarylessManifold\n' * 7 + 'BOUNDARYLESS_TYPES_END'
        guard.check_boundaryless_types(types)
        for bad in (types.replace('BoundarylessManifold\n', '', 1), types + '\nBOUNDARYLESS_TYPES_BEGIN', types.replace('BoundarylessManifold', 'ModelWithCorners.Boundaryless'), types.replace('BoundarylessManifold', 'I.Boundaryless')):
            with self.assertRaises(AssertionError):
                guard.check_boundaryless_types(bad)

    def test_full_build_open_audit_and_false_closed_claim(self):
        data = {'build_run': True, 'target_base': 'intrinsicLocalExistenceUniquenessFamily_pointFour', 'fqn': '', 'verdict': 'OPEN', 'gates': {
            'G1_sorry_free': {'status': 'PASS'}, 'G2_build_green': {'status': 'PASS'},
            'G3_unconditional': {'status': 'FAIL'}, 'G4_axiom_clean': {'status': 'FAIL'}, 'G5_faithful_type': {'status': 'FAIL'}}}
        guard.check_audit(data, 1)
        cases = [(data, 0)]
        for key, value in (('build_run', False), ('build_run', 1), ('verdict', 'CLOSED'), ('fqn', 'RicciFlow.intrinsicLocalExistenceUniquenessFamily_pointFour'), ('target_base', 'other')):
            bad = copy.deepcopy(data); bad[key] = value; cases.append((bad, 1))
        for key in data['gates']:
            bad = copy.deepcopy(data); bad['gates'][key]['status'] = 'SKIP'; cases.append((bad, 1))
            bad = copy.deepcopy(data); del bad['gates'][key]; cases.append((bad, 1))
        bad = copy.deepcopy(data); bad['gates']['G6_extra'] = {'status': 'PASS'}; cases.append((bad, 1))
        # Even fabricated all-PASS records may not close this immutable supporting union.
        bad = copy.deepcopy(data); bad['verdict'] = 'CLOSED'
        for gate in bad['gates'].values(): gate['status'] = 'PASS'
        cases.append((bad, 0))
        for bad, rc in cases:
            with self.assertRaises(AssertionError):
                guard.check_audit(bad, rc)


if __name__ == '__main__':
    unittest.main()
