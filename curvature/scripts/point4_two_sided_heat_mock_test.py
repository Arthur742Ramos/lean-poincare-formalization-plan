#!/usr/bin/env python3
"""Adversarial release fixtures; no compiler evidence or working-tree mutation."""
import copy
import sys
sys.dont_write_bytecode = True
import pathlib
import tempfile
from unittest import mock
import stat
import unittest
import point4_two_sided_heat_source_guard as release


class TwoSidedReleaseGuardTests(unittest.TestCase):
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
        namespace = vars(self.guard).copy()
        original = namespace.pop('_two_sided_release_original_expected_sources')
        namespace['expected_sources'] = original
        namespace['ADDED'] = namespace['ADDED'] - release.SELF_PATHS
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
            wrong = vars(self.guard).copy()
            wrong.pop('_two_sided_release_original_expected_sources')
            wrong['expected_sources'] = original
            wrong['ADDED'] = wrong['ADDED'] - release.SELF_PATHS
            wrong[key] = set(wrong[key]) | {'arbitrary/exception.lean'}
            with self.subTest(key=key), self.assertRaises(AssertionError):
                release.install_c2_inventory_adapter(wrong)

    def test_every_inherited_file_and_r1_proof_probe_is_pinned(self):
        self.assertEqual(len(self.baseline), 1641)
        for path, (_, original) in self.baseline.items():
            wanted = release.adapted_c2_guard(original) if path == release.C2_GUARD else original
            with self.subTest(path=path):
                self.assertEqual((release.ROOT / path).read_bytes(), wanted)
                with self.assertRaises(AssertionError):
                    self.guard.check_equal(path, wanted + b'\nunauthorized edit\n', wanted)
        for path in (release.MODULE, release.PROBE):
            actual = (release.ROOT / path).read_bytes()
            release.check_unit_blob(path, actual)
            self.assertEqual(release.sha256(actual), release.R1_FILE_SHA256[path])
        for path in release.UNIT_FILE_SHA256:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_unit_blob(path, (release.ROOT / path).read_bytes() + b'\n')
        with self.assertRaises(AssertionError):
            release.check_unit_blob('unknown.lean', b'')

    def test_precise_public_union_no_missing_or_arbitrary_extra_path(self):
        valid = release.public_paths()
        self.assertEqual(len(valid), 1649)
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

    def test_exact_tracked_untracked_ignored_inventory_and_caches(self):
        valid = release.public_paths()
        baseline = set(self.baseline)
        additions = valid - baseline
        release.check_inventory_sets(valid, set(), valid)
        release.check_inventory_sets(baseline, additions, valid)
        release.check_inventory_sets(valid, {'curvature/.lake/build/lib/Foo.olean'}, valid)
        for path in valid:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid - {path}, set(), valid - {path})
        bad_paths = ('extra.lean', 'extra.txt', '.github/workflows/unknown.yml',
                     '__pycache__/scan.cpython-311.pyc', '__pycache__/hidden.lean',
                     'curvature/scripts/__pycache__/scan.cpython-311.pyc',
                     'ignored/new-target.lean', 'curvature/.toolchain/hidden.lean',
                     'other/.lake/cache.olean', 'name\nwith-newline.bin',
                     'curvature/.lake/hidden.lean', 'curvature/.lake/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/Hidden.lean',
                     'curvature/.lake/__pycache__/hidden.cpython-311.pyc',
                     'curvature/.lake/packages/mathlib/Unpinned.lean',
                     'curvature/PoincareCurvature/CanonicalTarget.lean')
        for path in bad_paths:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid | {path}, set(), valid | {path})
            with self.subTest(untracked=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid, {path}, valid | {path})
        with self.assertRaises(AssertionError):
            release.check_inventory_sets(valid | {'curvature/.lake/hidden.lean'}, set(), valid)
        with self.assertRaises(AssertionError):
            release.check_inventory_sets(valid, {release.MODULE}, valid)
        self.assertEqual(release.nul_paths(b'one\ntwo\0three\0'), {'one\ntwo', 'three'})
        for wrong in (b'not terminated', b'dup\0dup\0', b'\0', b'one\0\0'):
            with self.assertRaises(AssertionError):
                release.nul_paths(wrong)

    def test_real_physical_ignored_files_caches_symlinks_and_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'base.lean').write_text('base')
            (root / 'guard.py').write_text('guard')
            def identity(data):
                return release.hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest().encode()
            records = b'100644 ' + identity(b'base') + b' 0\tbase.lean\0'
            records += b'100644 ' + identity(b'guard') + b' 0\tguard.py\0'
            def fake_git(*args):
                return records if args == ('ls-files', '--stage', '-z') else b''
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value={'base.lean': ('100644', b'base')}), \
                 mock.patch.object(release, 'UNIT_FILE_SHA256', {}), \
                 mock.patch.object(release, 'SELF_PATHS', {'guard.py'}), \
                 mock.patch.object(release, 'git', side_effect=fake_git):
                release.check_inventory()
                for name in ('curvature/.lake/hidden.lean', 'curvature/.lake/CanonicalTarget.lean',
                             'curvature/.lake/build/lib/Hidden.lean',
                             'curvature/.lake/__pycache__/hidden.cpython-311.pyc',
                             'curvature/.lake/packages/mathlib/Unpinned.lean',
                             'hamilton-ivey-reaction/.lake/build/Hidden.lean'):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b'arbitrary hidden source or cache')
                    with self.subTest(hidden=name), self.assertRaises(AssertionError):
                        release.check_inventory()
                    path.unlink()
                    while path.parent != root and not any(path.parent.iterdir()):
                        parent = path.parent
                        parent.rmdir()
                        path = parent
                for name in ('ignored.lean', 'hidden.txt', 'odd\nname.bin'):
                    path = root / name
                    path.write_bytes(b'extra')
                    with self.subTest(name=name), self.assertRaises(AssertionError):
                        release.check_inventory()
                    path.unlink()
                cache = root / '__pycache__'
                cache.mkdir()
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                cache.rmdir()
                (root / 'linked').symlink_to(root, target_is_directory=True)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'linked').unlink()
                original = (root / 'guard.py').read_bytes()
                (root / 'guard.py').unlink()
                (root / 'guard.py').symlink_to(root / 'base.lean')
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'guard.py').unlink()
                (root / 'guard.py').write_bytes(original)
                (root / 'guard.py').chmod(0o755)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'guard.py').chmod(0o644)
                release.check_inventory()
                (root / 'guard.py').write_bytes(b'unstaged different bytes')
                with self.assertRaises(AssertionError):
                    release.check_inventory()

    def test_bounded_runtime_outputs_and_path_dependency_build_root(self):
        valid = release.public_paths()
        outputs = ('curvature/.lake/build/lib/lean/Foo.olean',
                   'curvature/.lake/build/lib/lean/Foo.olean.private',
                   'curvature/.lake/build/lib/lean/Foo.olean.server',
                   'curvature/.lake/build/ir/Foo.c.o.export',
                   'curvature/.lake/config/1/lakefile.olean.lock',
                   'curvature/.lake/build/bin/cache',
                   'hamilton-ivey-reaction/.lake/build/ir/HamiltonIveyReaction.c',
                   'curvature/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean')
        for path in outputs:
            self.assertTrue(release.generated_build_path(path), path)
        release.check_inventory_sets(valid, set(outputs), valid)
        for path in ('curvature/.lake/hidden.txt', 'curvature/.lake/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/__pycache__/x.cpython-311.pyc',
                     'curvature/.lake/packages/unknown/.lake/build/lib/Foo.olean',
                     'curvature/.lake/packages/mathlib/Unpinned.lean'):
            self.assertFalse(release.generated_build_path(path), path)

    def test_dependency_pinned_head_blob_mode_and_symlink_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            package = root / 'curvature/.lake/packages/mathlib'
            package.mkdir(parents=True)
            (package / '.git').mkdir()
            (package / 'Known.lean').write_bytes(b'known source')
            (package / 'Pinned.py').symlink_to('Known.lean')
            revision = 'c' * 40
            manifest = {'packagesDir': '.lake/packages', 'packages': [
                {'type': 'git', 'name': 'mathlib', 'rev': revision}]}
            tree = ('100644 blob ' + release.git_blob_identity(b'known source') + '\tKnown.lean\0'
                    + '120000 blob ' + release.git_blob_identity(b'Known.lean') + '\tPinned.py\0').encode()
            def package_git(path, *args):
                return (revision + '\n').encode() if args == ('rev-parse', 'HEAD') else tree
            baseline = {'curvature/lake-manifest.json': ('100644', release.json.dumps(manifest).encode())}
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'git_at', side_effect=package_git):
                sources, git_roots = release.dependency_inventory()
                self.assertEqual(sources, {'curvature/.lake/packages/mathlib/Known.lean',
                                           'curvature/.lake/packages/mathlib/Pinned.py'})
                self.assertEqual(git_roots, {'curvature/.lake/packages/mathlib/.git'})
                (package / 'Known.lean').write_bytes(b'wrong source')
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
                (package / 'Known.lean').write_bytes(b'known source')
                (package / 'Known.lean').chmod(0o755)
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
                (package / 'Known.lean').chmod(0o644)
                (package / 'Pinned.py').unlink()
                (package / 'Pinned.py').symlink_to('different target')
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'git_at', return_value=b'wrong-head\n'):
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()

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
            self.new_metadata.replace('Point 4 is OPEN', 'Point 4 is CLOSED'),
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
            (b'--axiom-dir /tmp/point4-two-sided-heat-inherited-probes', b'--no-axiom-evidence'),
            (b'point4_c2_initial_heat_mock_test.py', b'missing_test.py'),
            (b'point4_linear_heat_geometry_mock_test.py', b'missing_test.py'),
            (b'point4_two_sided_heat_mock_test.py', b'missing_test.py'),
        )
        for before, after in replacements:
            self.assertIn(before, workflow)
            with self.subTest(before=before), self.assertRaises(AssertionError):
                release.check_unit_blob(release.WORKFLOW, workflow.replace(before, after, 1))

    def test_new_probe_rejects_missing_extra_duplicate_and_nonstandard_axioms(self):
        probe = (release.ROOT / release.PROBE).read_text()
        names = self.guard.probe_names(probe)
        self.assertEqual(len(names), 12)
        output = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)
        release.check_new_probe(output)
        clean = '\n'.join(f"'{name}' does not depend on any axioms" for name in names)
        release.check_new_probe(clean)
        for wrong in ('\n'.join(output.splitlines()[1:]), output.splitlines()[0] + '\n' + output,
                      output.replace('Quot.sound', 'propext', 1),
                      output.replace('Quot.sound', 'Custom.axiom', 1),
                      output.replace('Quot.sound', 'sorryAx', 1),
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
