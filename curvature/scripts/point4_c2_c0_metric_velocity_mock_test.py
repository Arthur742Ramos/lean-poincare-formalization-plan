#!/usr/bin/env python3
"""Adversarial release fixtures; no compiler evidence or working-tree mutation."""

# BEGIN exact finite incoming-leaf-134
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == '1d9b4ad2f428f3f65cb84bbefb67befbb77cce8f3cd50d7f5408bbd305056f56', "Incoming composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
if __name__ == '__main__':
    _curvature_comp.run_curvature_mocks(134,'curvature/scripts/point4_c2_c0_metric_velocity_mock_test.py',_curvature_sys.argv[1:])
    raise SystemExit(0)
# END exact finite incoming-leaf-134
import copy
from contextlib import contextmanager
import os
import py_compile
import subprocess
import sys
sys.dont_write_bytecode = True
import pathlib
import tempfile
from unittest import mock
import stat
import unittest
import point4_c2_c0_metric_velocity_source_guard as release


class MetricVelocityReleaseGuardTests(unittest.TestCase):
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

    def test_three_count_one_startup_workflow_adapters_pin_all_original_bytes(self):
        self.assertEqual(len(release.STARTUP_WORKFLOWS), 3)
        for path, (_, job, anchor) in release.STARTUP_WORKFLOWS.items():
            original = self.baseline[path][1]
            adapted = release.adapted_startup_workflow(path, original)
            self.assertEqual(adapted, (release.ROOT / path).read_bytes())
            self.assertEqual(adapted.decode().count(anchor), 1)
            self.assertEqual(adapted.decode().count(release.STARTUP_ENV), 1)
            self.assertEqual(release.restored_startup_workflow(path, adapted), original)
            parsed = release.parse_workflow(adapted.decode())
            self.assertEqual(parsed['jobs'][job]['env'], {'PYTHONDONTWRITEBYTECODE': '1'})
            del parsed['jobs'][job]['env']
            self.assertEqual(parsed, release.parse_workflow(original.decode()))
            for wrong in (original + b'\n', adapted, original.replace(anchor.encode(), b''),
                          original + anchor.encode()):
                with self.subTest(path=path, original=release.sha256(wrong)), self.assertRaises(AssertionError):
                    release.adapted_startup_workflow(path, wrong)
            wrong_cases = (
                adapted.replace(release.STARTUP_ENV.encode(), b''),
                adapted.replace(release.STARTUP_ENV.encode(), release.STARTUP_ENV.encode() * 2),
                adapted.replace(b"PYTHONDONTWRITEBYTECODE: '1'", b"PYTHONDONTWRITEBYTECODE: '0'"),
                adapted.replace(b"PYTHONDONTWRITEBYTECODE: '1'", b'PYTHONDONTWRITEBYTECODE: 1'),
                adapted.replace(b"PYTHONDONTWRITEBYTECODE: '1'", b"PYTHONDONTWRITEBYTECODE: '1'\n      PYTHONPATH: /tmp"),
                adapted.replace(b'contents: read', b'contents: write'),
                adapted.replace(b'fetch-depth: 0', b'fetch-depth: 1'),
                adapted.replace(b'      - name: Checkout', b"      - env: {PYTHONDONTWRITEBYTECODE: '0'}\n        name: Checkout", 1),
                adapted + b'\n',
            )
            for wrong in wrong_cases:
                with self.subTest(path=path, adapted=release.sha256(wrong)), self.assertRaises(AssertionError):
                    release.restored_startup_workflow(path, wrong)
        with self.assertRaises(AssertionError):
            release.adapted_startup_workflow('unapproved.yml', b'')

    def test_duplicate_workflow_yaml_keys_rejected_at_all_mapping_levels(self):
        for source in (
            "jobs: {}\njobs: {}\n",
            "jobs:\n  gate:\n    env: {}\n    env: {}\n",
            "jobs:\n  gate:\n    env:\n      PYTHONDONTWRITEBYTECODE: '1'\n      PYTHONDONTWRITEBYTECODE: '0'\n",
            "jobs:\n  gate:\n    steps:\n      - run: echo good\n        run: echo bad\n",
            "permissions: {contents: read, contents: write}\n",
        ):
            with self.subTest(source=source), self.assertRaises(AssertionError):
                release.parse_workflow(source)

    def test_workflow_wrapper_checks_exact_transform_then_runs_original_validator(self):
        namespace = vars(self.guard).copy()
        namespace['expected_sources'] = namespace.pop('_metric_velocity_release_original_expected_sources')
        namespace['ADDED'] = namespace['ADDED'] - release.SELF_PATHS
        namespace.pop('_metric_velocity_release_original_check_workflow')
        original_validator = mock.Mock(wraps=self.guard._metric_velocity_release_original_check_workflow)
        namespace['check_workflow'] = original_validator
        release.install_c2_inventory_adapter(namespace)
        path = '.github/workflows/point4-c2-initial-heat.yml'
        original = self.baseline[path][1]
        adapted = (release.ROOT / path).read_bytes()
        namespace['check_workflow'](adapted)
        original_validator.assert_called_once_with(original)
        original_validator.reset_mock()
        for wrong in (original, adapted + b'\n', adapted.replace(b'contents: read', b'contents: write')):
            with self.assertRaises(AssertionError):
                namespace['check_workflow'](wrong)
        original_validator.assert_not_called()

    def ordinary_startup_env(self, workflow):
        # Ignore any ambient caller flag. Reproduce GitHub's pinned job env with
        # the ordinary interpreter command, without -B or per-command prefixes.
        env = dict(os.environ)
        env.pop('PYTHONDONTWRITEBYTECODE', None)
        env.pop('PYTHONPYCACHEPREFIX', None)
        _, job, _ = release.STARTUP_WORKFLOWS[workflow]
        env.update(release.parse_workflow((release.ROOT / workflow).read_text())['jobs'][job]['env'])
        return env

    def test_clean_ordinary_python_startup_matches_inherited_job_environments(self):
        self.assertFalse(any(path.name == '__pycache__' for path in release.ROOT.rglob('__pycache__')))
        entries = (
            ('point4-linear-heat-geometry', 'point4_linear_heat_geometry_source_test.py'),
            ('point4-linear-heat-geometry', 'point4_linear_heat_geometry_mock_test.py'),
            ('point4-c2-initial-heat', 'point4_c2_initial_heat_source_test.py'),
            ('point4-c2-initial-heat', 'point4_c2_initial_heat_mock_test.py'),
            ('point4-weighted-initial-heat', 'point4_weighted_initial_heat_guard.py'),
        )
        for workflow, entry in entries:
            with self.subTest(entry=entry):
                result = subprocess.run([sys.executable, 'curvature/scripts/' + entry],
                                        cwd=release.ROOT, env=self.ordinary_startup_env('.github/workflows/' + workflow + '.yml'),
                                        capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertFalse(any(release.ROOT.rglob('__pycache__')), result.stdout + result.stderr)
        # The new guard's main entry is also safe with no startup environment.
        env = dict(os.environ)
        env.pop('PYTHONDONTWRITEBYTECODE', None)
        env.pop('PYTHONPYCACHEPREFIX', None)
        result = subprocess.run([sys.executable, release.SOURCE_GUARD], cwd=release.ROOT,
                                env=env, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(any(release.ROOT.rglob('__pycache__')))

    def test_preexisting_empty_hidden_stale_and_identical_python_caches_still_rejected(self):
        # Separate exact-index checkout: attack fixtures never alter the release
        # tree. Ordinary startup must preserve and reject every existing cache.
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory) / 'candidate'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], check=True)
            tree = release.git('write-tree').decode().strip()
            subprocess.run(['git', '-C', str(root), 'read-tree', tree], check=True)
            subprocess.run(['git', '-C', str(root), 'checkout-index', '-a'], check=True)
            cache = root / 'curvature/scripts/__pycache__'
            cache.mkdir()
            own_pyc = cache / ('point4_c2_initial_heat_source_test.' + sys.implementation.cache_tag + '.pyc')
            cases = ('empty', 'hidden.lean', 'stale.pyc', 'identical-own-pyc')
            for case in cases:
                attack = None
                if case == 'hidden.lean':
                    attack = cache / 'hidden.lean'; attack.write_bytes(b'axiom hidden : False\n')
                elif case == 'stale.pyc':
                    attack = own_pyc; attack.write_bytes(b'preexisting invalid cache')
                elif case == 'identical-own-pyc':
                    attack = own_pyc
                    py_compile.compile(str(root / release.C2_GUARD), cfile=str(attack), doraise=True)
                before = attack.read_bytes() if attack else None
                with self.subTest(case=case):
                    result = subprocess.run([sys.executable, 'curvature/scripts/point4_linear_heat_geometry_source_test.py'],
                                            cwd=root, env=self.ordinary_startup_env('.github/workflows/point4-linear-heat-geometry.yml'),
                                            capture_output=True, text=True, timeout=120)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn('Interpreter cache forbidden:', result.stderr)
                    self.assertTrue(cache.is_dir())
                    if attack:
                        self.assertEqual(attack.read_bytes(), before, 'Gate erased/overwrote preexisting cache evidence')
                if attack:
                    attack.unlink()
            cache.rmdir()

    def test_legacy_reconstruction_runs_and_gate_functions_are_untouched(self):
        namespace = vars(self.guard).copy()
        original = namespace.pop('_metric_velocity_release_original_expected_sources')
        namespace['expected_sources'] = original
        namespace['ADDED'] = namespace['ADDED'] - release.SELF_PATHS
        namespace['check_workflow'] = namespace.pop('_metric_velocity_release_original_check_workflow')
        names = ('main', 'check_imports', 'check_metadata', 'check_axiom_output',
                 'check_boundaryless_types', 'check_audit',
                 'check_public_paths', 'public_paths', 'nul_paths')
        before = {name: namespace[name] for name in names}
        release.install_c2_inventory_adapter(namespace)
        self.assertEqual({name: namespace[name] for name in names}, before)
        self.assertEqual(set(namespace['expected_sources']()), set(self.expected))
        with self.assertRaises(AssertionError):
            release.install_c2_inventory_adapter(namespace)
        for key in ('EDITABLE', 'ADDED'):
            wrong = vars(self.guard).copy()
            wrong.pop('_metric_velocity_release_original_expected_sources')
            wrong['check_workflow'] = wrong.pop('_metric_velocity_release_original_check_workflow')
            wrong['expected_sources'] = original
            wrong['ADDED'] = wrong['ADDED'] - release.SELF_PATHS
            wrong[key] = set(wrong[key]) | {'arbitrary/exception.lean'}
            with self.subTest(key=key), self.assertRaises(AssertionError):
                release.install_c2_inventory_adapter(wrong)

    def test_every_inherited_file_and_frozen003_proof_is_pinned(self):
        self.assertEqual(len(self.baseline), 1641)
        for path, (_, original) in self.baseline.items():
            wanted = (release.adapted_c2_guard(original) if path == release.C2_GUARD else
                      release.adapted_startup_workflow(path, original) if path in release.STARTUP_WORKFLOWS else original)
            with self.subTest(path=path):
                self.assertEqual((release.ROOT / path).read_bytes(), wanted)
                with self.assertRaises(AssertionError):
                    self.guard.check_equal(path, wanted + b'\nunauthorized edit\n', wanted)
        for path in release.UNIT_FILE_SHA256:
            actual = (release.ROOT / path).read_bytes()
            release.check_unit_blob(path, actual)
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_unit_blob(path, actual + b'\n')
        with self.assertRaises(AssertionError):
            release.check_unit_blob('unknown.lean', b'')

    def test_five_count_one_proof_repairs_reverse_to_complete_approved_source(self):
        actual = (release.ROOT / release.PROOF_REPAIR_PATH).read_bytes()
        original = release.git('show', f'{release.PROOF_REPAIR_PARENT}:{release.PROOF_REPAIR_PATH}')
        self.assertEqual(len(release.PROOF_REPAIR_TRANSFORMS), 5)
        self.assertEqual(release.adapted_gaussian_proofs(original), actual)
        self.assertEqual(release.restored_gaussian_proofs(actual), original)
        for before, after in release.PROOF_REPAIR_TRANSFORMS:
            wrong_sources = (original.replace(before, b'', 1), original + before,
                             original.replace(before, after, 1))
            for wrong in wrong_sources:
                with self.assertRaises(AssertionError):
                    release.adapted_gaussian_proofs(wrong)
            wrong_sources = (actual.replace(after, b'', 1), actual + after,
                             actual.replace(after, before, 1))
            for wrong in wrong_sources:
                with self.assertRaises(AssertionError):
                    release.restored_gaussian_proofs(wrong)
        for before, after in ((b'def smoothingTime', b'def changedTime'),
                              (b'UniformContinuous', b'Continuous'),
                              (b'HasDerivAt', b'HasDerivWithinAt'),
                              ('ContDiff ℝ 2'.encode(), 'ContDiff ℝ 1'.encode())):
            self.assertIn(before, actual)
            with self.assertRaises(AssertionError):
                release.restored_gaussian_proofs(actual.replace(before, after, 1))
        with self.assertRaises(AssertionError):
            release.restored_gaussian_proofs(actual + b'\naxiom hidden : False\n')

    def test_reviewed_module_bytes_and_source_closure(self):
        release.check_source_closure()
        frozen = release.json.loads((release.ROOT / release.DOSSIER / 'FINAL-SOURCE-MANIFEST.json').read_text())
        self.assertEqual(frozen['current_source_identity'], 'frozen-003')
        self.assertEqual(len(frozen['current_files']), 4)
        for row in frozen['current_files']:
            path = release.MODULE_PREFIX + row['file']
            data = (release.ROOT / path).read_bytes()
            if path == release.PROOF_REPAIR_PATH:
                data = release.restored_gaussian_proofs(data)
            self.assertEqual(release.sha256(data), row['sha256'])
            self.assertEqual(release.git_blob_identity(data), row['git_blob_sha1'])
        closure = release.json.loads((release.ROOT / release.CLOSURE_MANIFEST).read_text())
        for key, value in (('base', '0' * 40), ('inherited_module_count', 58),
                           ('external_graph_complete', True), ('project_module_count', 62)):
            wrong = copy.deepcopy(closure); wrong[key] = value
            with mock.patch.object(release.json, 'loads', return_value=wrong), self.assertRaises(AssertionError):
                release.check_source_closure()
        for field, value in (('sha256', '0' * 64), ('git_blob_sha1', '0' * 40),
                             ('imports', ['Unauthorized.Module']), ('legacy', False)):
            wrong = copy.deepcopy(closure); wrong['records'][0][field] = value
            with mock.patch.object(release.json, 'loads', return_value=wrong), self.assertRaises(AssertionError):
                release.check_source_closure()
        self.assertEqual(len(closure['records']), 59)
        wrong = copy.deepcopy(closure); wrong['records'].append(wrong['records'][0])
        with mock.patch.object(release.json, 'loads', return_value=wrong), self.assertRaises(AssertionError):
            release.check_source_closure()

    def test_precise_public_union_no_missing_or_arbitrary_extra_path(self):
        valid = release.public_paths()
        self.assertEqual(len(valid), len(self.baseline) + len(release.UNIT_FILE_SHA256) + len(release.SELF_PATHS))
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
            release.check_inventory_sets(valid, {release.MODULES[0]}, valid)
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

    @contextmanager
    def fingerprint_fixture(self):
        # Physical candidate with a synthetic pinned source, no compiler/cache
        # download. Only the fixture's source identity/size are substituted.
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            package = root / 'curvature/.lake/packages/proofwidgets'
            (package / 'widget').mkdir(parents=True)
            (package / '.git').mkdir()
            lock = root / release.PROOFWIDGETS_LOCK
            source = b'verified synthetic lockfile\n'
            lock.write_bytes(source)
            fingerprint = root / release.PROOFWIDGETS_FINGERPRINT
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            manifest = {'packagesDir': '.lake/packages', 'packages': [{
                'name': 'proofwidgets', 'type': 'git', 'rev': release.PROOFWIDGETS_REV,
                'url': 'https://github.com/leanprover-community/ProofWidgets4'}]}
            baseline = {'base.lean': ('100644', b'base'),
                        'curvature/lake-manifest.json': ('100644', release.json.dumps(manifest).encode())}
            for name, (_, data) in baseline.items():
                (root / name).write_bytes(data)
            (root / 'guard.py').write_bytes(b'guard')
            records = b''.join(('100644 ' + release.git_blob_identity(data) + ' 0\t' + name + '\0').encode()
                               for name, data in {**{p: d for p, (_, d) in baseline.items()}, 'guard.py': b'guard'}.items())
            tree = ('100644 blob ' + release.git_blob_identity(source) + '\twidget/package-lock.json\0').encode()
            def root_git(*args):
                return records if args == ('ls-files', '--stage', '-z') else b'curvature/.lake/packages/proofwidgets/\0'
            def package_git(path, *args):
                self.assertEqual(path, package)
                return (release.PROOFWIDGETS_REV + '\n').encode() if args == ('rev-parse', 'HEAD') else tree
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'UNIT_FILE_SHA256', {}), \
                 mock.patch.object(release, 'SELF_PATHS', {'guard.py'}), \
                 mock.patch.object(release, 'PROOFWIDGETS_LOCK_SIZE', len(source)), \
                 mock.patch.object(release, 'PROOFWIDGETS_LOCK_BLOB', release.git_blob_identity(source)), \
                 mock.patch.object(release, 'git', side_effect=root_git), \
                 mock.patch.object(release, 'git_at', side_effect=package_git):
                release.check_inventory()
                yield root, lock, fingerprint, source, baseline
                release.check_inventory()

    def test_exact_verified_fingerprint_rejects_bad_oversized_and_wrong_hash(self):
        with self.fingerprint_fixture() as (_, _, fingerprint, _, _):
            cases = (b'', b'0' * 15, b'0' * 17, b'0' * 65536,
                     b'0' * 16, b'g' * 16, b'179E66574F04806E',
                     release.PROOFWIDGETS_LOCK_HASH + b'\n', b'\0' * 16)
            for wrong in cases:
                fingerprint.write_bytes(wrong)
                with self.subTest(size=len(wrong)), self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertEqual(fingerprint.read_bytes(), wrong, 'Gate changed rejected fingerprint evidence')
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            self.assertFalse(release.generated_build_path(release.PROOFWIDGETS_FINGERPRINT))
            sources, _ = release.dependency_inventory()
            self.assertEqual(release.runtime_fingerprints(sources), {release.PROOFWIDGETS_FINGERPRINT})
            with self.assertRaises(AssertionError):
                release.runtime_fingerprints(set())

    def test_exact_verified_fingerprint_rejects_symlink_directory_and_mode_drift(self):
        with self.fingerprint_fixture() as (_, lock, fingerprint, source, _):
            fingerprint.unlink()
            for target in (lock, fingerprint.parent / 'missing'):
                fingerprint.symlink_to(target)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertTrue(fingerprint.is_symlink())
                fingerprint.unlink()
            fingerprint.mkdir()
            with self.assertRaises(AssertionError):
                release.check_inventory()
            fingerprint.rmdir()
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            fingerprint.chmod(0o755)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            fingerprint.chmod(0o644)
            lock.unlink()
            lock.symlink_to(fingerprint)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            lock.unlink()
            lock.write_bytes(source)
            lock.chmod(0o755)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            lock.chmod(0o644)

    def test_exact_verified_fingerprint_rejects_parent_source_head_and_manifest_drift(self):
        with self.fingerprint_fixture() as (_, lock, fingerprint, source, baseline):
            lock.write_bytes(source.replace(b'verified', b'modified'))
            with self.assertRaises(AssertionError):
                release.check_inventory()
            self.assertNotEqual(lock.read_bytes(), source)
            lock.write_bytes(source)
            with mock.patch.object(release, 'git_at', return_value=b'wrong-head\n'), self.assertRaises(AssertionError):
                release.check_inventory()
            sources, _ = release.dependency_inventory()
            for field, value in (('rev', 'a' * 40), ('url', 'https://example.invalid/ProofWidgets4'),
                                 ('name', 'wrong-package'), ('type', 'path')):
                wrong = copy.deepcopy(release.json.loads(baseline['curvature/lake-manifest.json'][1]))
                wrong['packages'][0][field] = value
                altered = dict(baseline)
                altered['curvature/lake-manifest.json'] = ('100644', release.json.dumps(wrong).encode())
                with mock.patch.object(release, 'baseline_sources', return_value=altered), self.assertRaises(AssertionError):
                    release.runtime_fingerprints(sources)
            widget = lock.parent
            renamed = widget.with_name('displaced-widget')
            widget.rename(renamed)
            widget.symlink_to(renamed, target_is_directory=True)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            widget.unlink()
            renamed.rename(widget)
            self.assertEqual(fingerprint.read_bytes(), release.PROOFWIDGETS_LOCK_HASH)

    def test_fingerprint_does_not_admit_other_paths_hidden_lean_or_caches(self):
        with self.fingerprint_fixture() as (root, _, fingerprint, _, _):
            paths = (
                'curvature/.lake/packages/proofwidgets/widget/package.json.hash',
                'curvature/.lake/packages/proofwidgets/widget/package-lock.json.hash.extra',
                'curvature/.lake/packages/proofwidgets/widget/other/package-lock.json.hash',
                'curvature/.lake/packages/mathlib/widget/package-lock.json.hash',
                'hamilton-ivey-reaction/.lake/packages/proofwidgets/widget/package-lock.json.hash',
                'curvature/.lake/packages/proofwidgets/widget/Hidden.lean',
                'curvature/.lake/packages/proofwidgets/widget/__pycache__/hidden.lean',
                'curvature/.lake/packages/proofwidgets/widget/stale.pyc',
                'curvature/.lake/packages/proofwidgets/.lake/build/Hidden.lean',
            )
            for name in paths:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
                with self.subTest(path=name), self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertEqual(path.read_bytes(), release.PROOFWIDGETS_LOCK_HASH)
                path.unlink()
                while path.parent != root and not any(path.parent.iterdir()):
                    parent = path.parent
                    parent.rmdir()
                    path = parent
            fingerprint.unlink()
            release.check_inventory()  # Sidecar is optional before Lake writes it.
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            public = release.public_paths()
            with self.assertRaises(AssertionError):
                release.check_inventory_sets(public | {release.PROOFWIDGETS_FINGERPRINT}, set(), public)
            with self.assertRaises(AssertionError):
                release.check_inventory_sets(public, set(), public, fingerprints={'other.hash'})

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
                wanted = release.adapted_startup_workflow(path, data) if path in release.STARTUP_WORKFLOWS else data
                self.assertEqual((release.ROOT / path).read_bytes(), wanted)
        workflow = (release.ROOT / release.WORKFLOW).read_bytes()
        release.check_new_workflow(workflow)
        replacements = (
            (b'persist-credentials: false', b'persist-credentials: true'),
            (b'contents: read', b'contents: write'), (b'fetch-depth: 0', b'fetch-depth: 1'),
            (b'lake build PoincareCurvature.', b'echo skipped PoincareCurvature.'),
            (b'scripts/point4_closed_contract_regression.lean', b'scripts/missing.lean'),
            (b'bash scripts/point4_audit.sh --json', b'echo skip --json'),
            (b'--axiom-dir /tmp/point4-c2-c0-metric-velocity-inherited-probes', b'--no-axiom-evidence'),
            (b'point4_c2_initial_heat_mock_test.py', b'missing_test.py'),
            (b'point4_linear_heat_geometry_mock_test.py', b'missing_test.py'),
            (b'point4_c2_c0_metric_velocity_mock_test.py', b'missing_test.py'),
        )
        for before, after in replacements:
            self.assertIn(before, workflow)
            with self.subTest(before=before), self.assertRaises(AssertionError):
                release.check_new_workflow(workflow.replace(before, after, 1))

    def test_new_probe_rejects_missing_extra_duplicate_and_nonstandard_axioms(self):
        source = (release.ROOT / release.PROBE).read_text()
        names = self.guard.probe_names(source)
        self.assertEqual(len(names), 29)
        printed = release.re.findall(r'^#print (?!axioms)(\S+)', source, release.re.M)
        types = ('C2_C0_METRIC_VELOCITY_TYPES_BEGIN\n' + '\n'.join(printed) +
                 '\nHasDerivAt BoundarylessManifold\nC2_C0_METRIC_VELOCITY_TYPES_END')
        output = types + '\n' + '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)
        release.check_new_probe(output)
        invalid = (output.replace("'" + names[0] + "' depends on axioms: [propext, Classical.choice, Quot.sound]", ''),
                   output + "\n'extra' does not depend on any axioms",
                   output + "\n'" + names[0] + "' does not depend on any axioms",
                   output.replace('Quot.sound', 'sorryAx'), output.replace('Quot.sound', 'Custom.axiom'),
                   output.replace('Quot.sound', 'propext'), output.replace('BoundarylessManifold', 'I.Boundaryless'),
                   output.replace('HasDerivAt', 'HasDerivWithinAt'),
                   output.replace('C2_C0_METRIC_VELOCITY_TYPES_END', 'BoundedC3 C2_C0_METRIC_VELOCITY_TYPES_END'),
                   output + '\nC2_C0_METRIC_VELOCITY_TYPES_BEGIN')
        for bad in invalid:
            with self.assertRaises(AssertionError):
                release.check_new_probe(bad)
        for token in ('ExpectedC2C0MetricVelocity', 'c2C0MetricVelocityFullSignatureAssignment',
                      'ContinuousSymmetricVelocity', 'RicciFlow.MetricFamily',
                      'c2C0MetricVelocityRankZeroContext', 'c2C0MetricVelocityEmptyManifoldContext'):
            with self.subTest(token=token), self.assertRaises(AssertionError):
                release.check_new_probe(output.replace(token, 'missing'))

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


    def test_exact_primary_workflow_checkpoints_preserve_every_original_byte_and_gate(self):
        actual = (release.ROOT / release.EXACT_HEAD_WORKFLOW_PATH).read_bytes()
        original = release.git('show', release.EXACT_HEAD_WORKFLOW_BASE + ':' + release.EXACT_HEAD_WORKFLOW_PATH)
        self.assertEqual(release.restored_exact_head_workflow(actual), original)
        self.assertEqual(release.adapted_exact_head_workflow(original), actual)
        self.assertEqual(release.sha256(actual), release.EXACT_HEAD_WORKFLOW_SHA256)
        parsed = release.parse_workflow(actual.decode())
        old = release.parse_workflow(original.decode())
        steps = parsed['jobs'][release.EXACT_HEAD_WORKFLOW_JOB]['steps']
        self.assertEqual(steps[1]['env'], {
            'GIT_NO_LAZY_FETCH': '1',
            'EXPECTED_SHA': '${{ github.event.pull_request.head.sha || github.sha }}'})
        self.assertNotIn('if', steps[1])
        self.assertEqual(steps[-2]['if'], 'always()')
        steps.pop(-2); steps.pop(1)
        self.assertEqual(parsed, old)
        for wrong in (
                original + b'\n', actual,
                original.replace(release.EXACT_HEAD_BEFORE_ANCHOR.encode(), b''),
                original + release.EXACT_HEAD_AFTER_ANCHOR.encode()):
            with self.subTest(original=release.sha256(wrong)), self.assertRaises(AssertionError):
                release.adapted_exact_head_workflow(wrong)
        for wrong in (
                original, actual + b'\n',
                actual.replace(release.EXACT_HEAD_PREFLIGHT.encode(), b'', 1),
                actual.replace(release.EXACT_HEAD_POSTFLIGHT.encode(), b'', 1),
                actual.replace(release.EXACT_HEAD_POSTFLIGHT.encode(), release.EXACT_HEAD_POSTFLIGHT.encode() * 2, 1),
                actual.replace(b'--cached', b'--quiet', 1),
                actual.replace(b'set -euo pipefail', b'set +e', 1),
                actual.replace(b'contents: read', b'contents: write', 1),
                actual.replace(b'        if: always()\n        env:\n          GIT_NO_LAZY_FETCH:', b'        if: success()\n        env:\n          GIT_NO_LAZY_FETCH:', 1)):
            with self.subTest(actual=release.sha256(wrong)), self.assertRaises(AssertionError):
                release.restored_exact_head_workflow(wrong)

    def test_real_committed_self_blob_mode_index_binding_and_actual_source_failure(self):
        # A separate committed checkout and independent index preserve the release.
        # Comments are harmless; this exercises source identity, not Lean validity.
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory) / 'candidate'
            env = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], env=env, check=True)
            head = release.git('rev-parse', 'HEAD').decode().strip()
            subprocess.run(['git', '-C', str(root), 'checkout', '--quiet', '--detach', head], env=env, check=True)
            def local_git(*args):
                return subprocess.check_output(['git', '-C', str(root), *args], env=env)
            guard_path = pathlib.Path(release.__file__).resolve().relative_to(release.ROOT).as_posix()
            with mock.patch.object(release, 'ROOT', root):
                release.check_release_self_sources()
                for path in sorted(release.SELF_PATHS):
                    physical = root / path
                    before = physical.read_bytes()
                    for mutation in ('unstaged_comment', 'staged_comment', 'unstaged_mode', 'staged_mode'):
                        if mutation.endswith('comment'):
                            physical.write_bytes(before + b'\n# Benign exact-head self-source regression.\n')
                        else:
                            physical.chmod(0o755)
                        if mutation.startswith('staged_'):
                            local_git('add', '--', path)
                        with self.subTest(path=path, mutation=mutation), self.assertRaises(AssertionError):
                            release.check_release_self_sources()
                        self.assertEqual(local_git('rev-parse', 'HEAD').decode().strip(), head)
                        if mutation == 'staged_comment':
                            # The actual current source-gate process must reject;
                            # no mocked successful source result substitutes for it.
                            result = subprocess.run([release.sys.executable, guard_path], cwd=root, env=env,
                                                    capture_output=True, text=True, timeout=180)
                            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                            self.assertIn('Self index/committed HEAD blob or mode mismatch', result.stderr)
                            self.assertEqual(physical.read_bytes(), before + b'\n# Benign exact-head self-source regression.\n')
                        physical.write_bytes(before); physical.chmod(0o644)
                        local_git('reset', '--quiet', 'HEAD', '--', path)
                        release.check_release_self_sources()
                self.assertFalse(local_git('status', '--porcelain=v1', '--untracked-files=all'))

    def test_real_independent_workflow_pre_post_cleanliness_and_failure_propagation(self):
        with tempfile.TemporaryDirectory() as directory:
            container = pathlib.Path(directory)
            root = container / ('campaign' if '-C campaign' in release.EXACT_HEAD_PREFLIGHT else 'candidate')
            env = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], env=env, check=True)
            head = release.git('rev-parse', 'HEAD').decode().strip()
            subprocess.run(['git', '-C', str(root), 'checkout', '--quiet', '--detach', head], env=env, check=True)
            env.update(EXPECTED_SHA=head, CHECKPOINT_LOG=str(container / 'failed-gate.log'),
                       CHECKPOINT_RECEIPT=str(container / 'unexpected-success'))
            cwd = container if root.name == 'campaign' else root
            before = release.parse_workflow('steps:\n' + release.EXACT_HEAD_PREFLIGHT)['steps'][0]['run']
            after = release.parse_workflow('steps:\n' + release.EXACT_HEAD_POSTFLIGHT)['steps'][0]['run']
            def shell(code):
                return subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code],
                                      cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
            def local_git(*args):
                return subprocess.check_output(['git', '-C', str(root), *args], env=env)
            for code in (before, after):
                result = shell(code)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            path = sorted(release.SELF_PATHS)[0]; physical = root / path; original = physical.read_bytes()
            for stage in (False, True):
                physical.write_bytes(original + b'\n# Benign independent workflow dirty-source control.\n')
                if stage:
                    local_git('add', '--', path)
                for code in (before, after):
                    result = shell(code)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(local_git('rev-parse', 'HEAD').decode().strip(), head)
                physical.write_bytes(original); local_git('reset', '--quiet', 'HEAD', '--', path)
            # A candidate-owned gate that exits successfully after staging a
            # comment cannot turn dirty source into exact-head qualification.
            gate = 'printf "\\n# Benign mutation during candidate gate.\\n" >> ' + str(physical) + '\ngit -C ' + str(root) + ' add -- ' + path
            self.assertEqual(shell(before).returncode, 0)
            self.assertEqual(shell(gate).returncode, 0)
            self.assertNotEqual(shell(after).returncode, 0)
            physical.write_bytes(original); local_git('reset', '--quiet', 'HEAD', '--', path)
            # GitHub's pinned bash -e/pipefail run behavior must propagate a
            # failing producer through tee, even with a clean post-check body.
            gate = 'python3 -c "raise SystemExit(9)" | tee "$CHECKPOINT_LOG"'
            result = shell(before + '\n' + gate + '\n' + after + '\ntouch "$CHECKPOINT_RECEIPT"')
            self.assertEqual(result.returncode, 9, result.stdout + result.stderr)
            self.assertFalse((container / 'unexpected-success').exists())
            self.assertEqual(shell(after).returncode, 0)
            # A clean index/worktree at a different HEAD is still the wrong release.
            local_git('-c', 'user.name=Owned regression', '-c', 'user.email=owned-regression@example.invalid',
                      'commit', '--quiet', '--allow-empty', '-m', 'Owned wrong-HEAD regression')
            for code in (before, after):
                self.assertNotEqual(shell(code).returncode, 0)
            local_git('reset', '--hard', '--quiet', head)
            self.assertFalse(local_git('status', '--porcelain=v1', '--untracked-files=all'))



    def test_independent_workflow_physical_identity_cannot_be_hidden_by_git_index_flags(self):
        with tempfile.TemporaryDirectory() as directory:
            container = pathlib.Path(directory)
            root = container / ('campaign' if '-C campaign' in release.EXACT_HEAD_PREFLIGHT else 'candidate')
            env = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], env=env, check=True)
            head = release.git('rev-parse', 'HEAD').decode().strip()
            subprocess.run(['git', '-C', str(root), 'checkout', '--quiet', '--detach', head], env=env, check=True)
            env['EXPECTED_SHA'] = head
            cwd = container if root.name == 'campaign' else root
            checks = [release.parse_workflow('steps:\n' + step)['steps'][0]['run']
                      for step in (release.EXACT_HEAD_PREFLIGHT, release.EXACT_HEAD_POSTFLIGHT)]
            path = sorted(release.SELF_PATHS)[0]; physical = root / path; original = physical.read_bytes()
            for flag in ('--assume-unchanged', '--skip-worktree'):
                subprocess.run(['git', '-C', str(root), 'update-index', flag, path], env=env, check=True)
                physical.write_bytes(original + b'\n# Benign source hidden from Git stat/diff shortcuts.\n')
                # Confirm the regression reproduces a real Git diff blind spot.
                result = subprocess.run(['git', '-C', str(root), 'diff', '--exit-code', '--', path], env=env, capture_output=True)
                self.assertEqual(result.returncode, 0)
                for code in checks:
                    result = subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code],
                                            cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn('Independent tracked physical/HEAD blob mismatch:', result.stderr)
                self.assertEqual(physical.read_bytes(), original + b'\n# Benign source hidden from Git stat/diff shortcuts.\n')
                self.assertEqual(subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], env=env).decode().strip(), head)
                physical.write_bytes(original)
                subprocess.run(['git', '-C', str(root), 'update-index', '--no-assume-unchanged', '--no-skip-worktree', path], env=env, check=True)
            for code in checks:
                self.assertEqual(subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], cwd=cwd, env=env).returncode, 0)


    def test_expected_release_head_is_bound_with_real_clean_head_shift_and_path_spoof(self):
        with tempfile.TemporaryDirectory() as directory:
            container = pathlib.Path(directory)
            root = container / ('campaign' if '-C campaign' in release.EXACT_HEAD_PREFLIGHT else 'candidate')
            env = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
            subprocess.run(['/usr/bin/git', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], env=env, check=True)
            expected = release.git('rev-parse', 'HEAD').decode().strip()
            subprocess.run(['/usr/bin/git', '-C', str(root), 'checkout', '--quiet', '--detach', expected], env=env, check=True)
            env['EXPECTED_SHA'] = expected
            cwd = container if root.name == 'campaign' else root
            checks = [release.parse_workflow('steps:\n' + step)['steps'][0]['run']
                      for step in (release.EXACT_HEAD_PREFLIGHT, release.EXACT_HEAD_POSTFLIGHT)]
            isolated = [code[code.index('/usr/bin/python3 -I -B -'):] for code in checks]
            def shell(code):
                return subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
            for code in checks + isolated:
                result = shell(code)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # A real clean checkout at the old source head reproduces the
            # independent reviewer's attack without modifying any Lean source.
            actual = release.EXACT_HEAD_WORKFLOW_BASE
            self.assertNotEqual(actual, expected)
            subprocess.run(['/usr/bin/git', '-C', str(root), 'checkout', '--quiet', '--detach', actual], env=env, check=True)
            self.assertFalse(subprocess.check_output(['/usr/bin/git', '-C', str(root), 'status', '--porcelain=v1', '--untracked-files=all'], env=env))
            fake_bin = container / 'fake-bin'; fake_bin.mkdir()
            fake = fake_bin / 'git'
            fake.write_text('#!/bin/sh\ncase "$*" in\n  "rev-parse HEAD"|"-C campaign rev-parse HEAD") printf "%s\n" "$EXPECTED_SHA" ;;\n  *) exec /usr/bin/git "$@" ;;\nesac\n')
            fake.chmod(0o755)
            env['PATH'] = str(fake_bin) + os.pathsep + env['PATH']
            prefix = ['-C', 'campaign'] if root.name == 'campaign' else []
            spoofed = subprocess.check_output(['git', *prefix, 'rev-parse', 'HEAD'], cwd=cwd, env=env).decode().strip()
            self.assertEqual(spoofed, expected)
            self.assertEqual(subprocess.check_output(['/usr/bin/git', '-C', str(root), 'rev-parse', 'HEAD'], env=env).decode().strip(), actual)
            for code in checks:
                result = shell(code)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            # The isolated Python check also rejects independently, even when
            # the shell HEAD check is not included in this fixture invocation.
            for code in isolated:
                result = shell(code)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('Independent expected release HEAD mismatch', result.stderr)
            subprocess.run(['/usr/bin/git', '-C', str(root), 'checkout', '--quiet', '--detach', expected], env=env, check=True)
            for code in checks + isolated:
                result = shell(code)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


    def test_raw_source_identity_rejects_replace_refs_and_custom_replace_namespace(self):
        with tempfile.TemporaryDirectory() as directory:
            container = pathlib.Path(directory)
            root = container / ('campaign' if '-C campaign' in release.EXACT_HEAD_PREFLIGHT else 'candidate')
            env = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
            env.pop('GIT_REPLACE_REF_BASE', None)
            subprocess.run(['/usr/bin/git', '--no-replace-objects', 'clone', '--quiet', '--shared', '--no-checkout', str(release.ROOT), str(root)], env=env, check=True)
            expected = release.raw_git('rev-parse', 'HEAD').decode().strip()
            subprocess.run(['/usr/bin/git', '--no-replace-objects', '-C', str(root), 'checkout', '--quiet', '--detach', expected], env=env, check=True)
            env['EXPECTED_SHA'] = expected
            cwd = container if root.name == 'campaign' else root
            checks = [release.parse_workflow('steps:\n' + step)['steps'][0]['run']
                      for step in (release.EXACT_HEAD_PREFLIGHT, release.EXACT_HEAD_POSTFLIGHT)]
            isolated = [code[code.index('/usr/bin/python3 -I -B -'):] for code in checks]
            def git(*args, raw=False):
                prefix = ['/usr/bin/git'] + (['--no-replace-objects'] if raw else [])
                return subprocess.check_output(prefix + ['-C', str(root), *args], env=env)
            path = sorted(release.SELF_PATHS)[0]
            source = root / path; original = source.read_bytes()
            source.write_bytes(original + b'\n# Benign immutable-object replacement control.\n')
            git('add', '--', path, raw=True)
            tree = git('write-tree', raw=True).decode().strip()
            command = ['/usr/bin/git', '--no-replace-objects', '-C', str(root), '-c', 'user.name=Owned replacement regression', '-c', 'user.email=owned-replacement@example.invalid', 'commit-tree', tree, '-p', expected]
            replacement = subprocess.check_output(command, input=b'Owned immutable-object replacement regression\n', env=env).decode().strip()
            for namespace in ('refs/replace/', 'refs/owned-replacement-control/'):
                git('reset', '--hard', '--quiet', expected, raw=True)
                if namespace == 'refs/replace/':
                    env.pop('GIT_REPLACE_REF_BASE', None)
                else:
                    env['GIT_REPLACE_REF_BASE'] = namespace
                git('update-ref', namespace + expected, replacement, raw=True)
                git('reset', '--hard', '--quiet', expected)
                self.assertEqual(git('rev-parse', 'HEAD').decode().strip(), expected)
                self.assertFalse(git('status', '--porcelain=v1', '--untracked-files=all'))
                self.assertEqual(source.read_bytes(), original + b'\n# Benign immutable-object replacement control.\n')
                self.assertNotEqual(git('ls-tree', '-rz', expected, '--', path),
                                    git('ls-tree', '-rz', expected, '--', path, raw=True))
                for code in checks + isolated:
                    result = subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                with mock.patch.object(release, 'ROOT', root), mock.patch.object(release, 'ENV', env):
                    with self.assertRaises(AssertionError):
                        (release.check_self_sources if hasattr(release, 'check_self_sources') else release.check_release_self_sources)()
                self.assertEqual(source.read_bytes(), original + b'\n# Benign immutable-object replacement control.\n')
                git('update-ref', '-d', namespace + expected, raw=True)
                git('reset', '--hard', '--quiet', expected, raw=True)
            env.pop('GIT_REPLACE_REF_BASE', None)
            for code in checks + isolated:
                result = subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail', '-c', code], cwd=cwd, env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
