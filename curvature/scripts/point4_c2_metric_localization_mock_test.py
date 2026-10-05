#!/usr/bin/env python3
"""Adversarial gate tests, independent of a Lean compiler."""
from __future__ import annotations
import copy
import json
import unittest
import yaml
import point4_c2_metric_localization_source_test as guard

class GateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.master = guard.blob(guard.INTEGRATION_PARENT, 'curvature/formalization.yaml')
        cls.trace = guard.blob(guard.INTEGRATION_PARENT, 'curvature/formalization.yaml')
        cls.current = (guard.ROOT / 'curvature/formalization.yaml').read_bytes()
        cls.mroot = guard.blob(guard.INTEGRATION_PARENT, 'curvature/PoincareCurvature.lean')
        cls.troot = guard.blob(guard.INTEGRATION_PARENT, 'curvature/PoincareCurvature.lean')
        cls.root = (guard.ROOT / 'curvature/PoincareCurvature.lean').read_bytes()
        cls.axioms = '\n'.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in sorted(guard.SURFACES)) + '\nBoundarylessManifold\n'
        cls.audit = {'build_run': True, 'verdict': 'OPEN', 'gates': {
            'G1_sorry_free': {'status': 'PASS'}, 'G2_build_green': {'status': 'PASS'},
            'G3_unconditional': {'status': 'FAIL', 'note': 'target not found in source'},
            'G4_axiom_clean': {'status': 'FAIL', 'note': 'target missing'},
            'G5_faithful_type': {'status': 'FAIL', 'note': 'target missing'},
        }}

    def reject(self, fn, *args):
        with self.assertRaises((AssertionError, ValueError, yaml.YAMLError)):
            fn(*args)

    def test_positive_controls(self):
        guard.check_metadata(self.current, self.master, self.trace)
        guard.check_imports(self.root, self.mroot, self.troot)
        guard.check_axioms(self.axioms)
        guard.check_audit(self.audit, 1)

    def test_duplicate_yaml_key(self):
        self.reject(guard.strict_yaml, 'key: 1\nkey: 2\n')
        self.reject(guard.strict_yaml, 'top:\n  child: 1\n  child: 2\n')

    def test_duplicate_related_identity(self):
        data = guard.strict_yaml(self.current)
        data['related_formalizations'].append(copy.deepcopy(data['related_formalizations'][0]))
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_duplicate_identity_other_relationship(self):
        data = guard.strict_yaml(self.current)
        item = copy.deepcopy(data['related_formalizations'][0]); item['relationship'] = 'formalizes'
        data['related_formalizations'].append(item)
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_missing_inherited_note(self):
        data = guard.strict_yaml(self.current)
        data['related_formalizations'][0]['note'] = 'replacement'
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_changed_author(self):
        data = guard.strict_yaml(self.current); data['project']['authors'] = ['replacement']
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_unrequested_provenance_identity(self):
        data = guard.strict_yaml(self.current)
        data['related_formalizations'].append({'id': 'unexpected', 'relationship': 'builds-on', 'note': 'x'})
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_missing_or_extra_import(self):
        self.reject(guard.check_imports, b'\n'.join(self.root.splitlines()[:-1]), self.mroot, self.troot)
        self.reject(guard.check_imports, self.root + b'\nimport Unknown.Module\n', self.mroot, self.troot)

    def test_duplicate_import(self):
        self.reject(guard.check_imports, self.root + b'\nimport PoincareCurvature.Basic\n', self.mroot, self.troot)

    def test_nonimport_root_code(self):
        self.reject(guard.check_imports, self.root + b'\ndef hidden : True := True.intro\n', self.mroot, self.troot)
        self.reject(guard.check_imports, self.root + self.root.splitlines()[0] + b'\n', self.mroot, self.troot)

    def test_tracked_cache_artifacts(self):
        for path in ('curvature/.lake/build/x.olean', 'curvature/.lake/packages/mathlib/x.lean', '.development/foo', 'curvature/scripts/__pycache__/foo.pyc'):
            self.reject(guard.check_no_cache, {path})

    def test_changed_authored_proof(self):
        path = next(iter(guard.MODULES))
        self.reject(guard.check_hash, path, '0' * 64)

    def test_exact_count_one_legacy_transform(self):
        original = guard.blob(guard.INTEGRATION_PARENT, guard.LEGACY_GUARD)
        transformed = guard.adapt_legacy_guard(original)
        self.assertEqual(transformed.replace(guard.LEGACY_ADAPTER.encode(), b'', 1), original)
        self.assertEqual(transformed.count(guard.LEGACY_ADAPTER.encode()), 1)
        self.assertEqual((guard.ROOT / guard.LEGACY_GUARD).read_bytes(), transformed)
        self.reject(guard.adapt_legacy_guard, original + b'\nunauthorized change\n')
        self.reject(guard.adapt_legacy_guard, original.replace(b"\nif __name__ == '__main__':", b'\nremoved:'))
        self.reject(guard.adapt_legacy_guard, original + b"\nif __name__ == '__main__':\n    main()\n")

    def test_literal_parent_note_drift(self):
        data = guard.strict_yaml(self.current)
        data['related_formalizations'][-1]['note'] = 'replacement'
        self.reject(guard.check_metadata, yaml.safe_dump(data).encode(), self.master, self.trace)

    def test_all_inherited_workflows_remain_exact(self):
        for path in guard.tree(guard.INTEGRATION_PARENT):
            if path.startswith('.github/workflows/'):
                self.assertEqual((guard.ROOT / path).read_bytes(), guard.blob(guard.INTEGRATION_PARENT, path))

    def test_missing_axiom_surface(self):
        self.reject(guard.check_axioms, '\n'.join(self.axioms.splitlines()[1:]))

    def test_extra_axiom_surface(self):
        self.reject(guard.check_axioms, self.axioms + "'Unknown.extra' does not depend on any axioms\n")

    def test_duplicate_axiom_surface(self):
        self.reject(guard.check_axioms, self.axioms + self.axioms.splitlines()[0] + '\n')

    def test_nonstandard_axiom(self):
        self.reject(guard.check_axioms, self.axioms.replace('propext', 'sorryAx', 1))

    def test_malformed_extra_axiom(self):
        self.reject(guard.check_axioms, self.axioms + "'Unknown.extra' depends on axioms: [truncated\n")

    def test_model_boundary_restriction(self):
        self.reject(guard.check_axioms, self.axioms + 'ModelWithCorners.Boundaryless\n')

    def test_open_with_bad_canonical_target(self):
        data = copy.deepcopy(self.audit); data['gates']['G3_unconditional']['note'] = 'canonical target fails assignment'
        self.reject(guard.check_audit, data, 1)
        data = copy.deepcopy(self.audit); data['gates']['G5_faithful_type']['note'] = 'full assignment failed'
        self.reject(guard.check_audit, data, 1)

    def test_fast_failed_build_closed_or_wrong_rc(self):
        data = copy.deepcopy(self.audit); data['build_run'] = False
        self.reject(guard.check_audit, data, 1)
        data = copy.deepcopy(self.audit); data['gates']['G2_build_green']['status'] = 'FAIL'
        self.reject(guard.check_audit, data, 1)
        data = copy.deepcopy(self.audit); data['verdict'] = 'CLOSED'
        self.reject(guard.check_audit, data, 0)
        self.reject(guard.check_audit, self.audit, 0)

if __name__ == '__main__':
    unittest.main()
