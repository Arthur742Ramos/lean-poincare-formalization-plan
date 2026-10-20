"""Small cache-contract controls. No Lean invocation or project imports."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import sys
import unittest
from unittest import mock

import point4_ci_cache as cache


class CacheControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='point4-cache-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.identity = dict(schema=cache.SCHEMA, head='a' * 40, tree='b' * 40,
                             toolchain_sha256='c' * 64, manifest_sha256='d' * 64,
                             config_sha256='e' * 64, compiler_binary_sha256='f' * 64,
                             compiler_version='pinned', package='curvature',
                             package_source='0' * 64, effective_package_options={'leanOptions': {'x': True}},
                             option_environment_sha256={'LEAN_PATH': '1' * 64},
                             dependencies=[{'head': '2' * 40, 'tree': '3' * 40}, {'source': '4' * 64}],
                             targets=['PoincareCurvature.Example'], build_arguments=[],
                             platform={'os': 'Linux', 'machine': 'x86_64', 'image_version': '1'},
                             provider_scope={'GITHUB_REPOSITORY': 'owner/repo', 'GITHUB_REF': 'refs/pull/1/merge',
                                             'GITHUB_WORKFLOW_REF': 'owner/repo/workflow@ref', 'GITHUB_WORKFLOW_SHA': '5' * 40},
                             source_repository='owner/repo', output_root='curvature/.lake/build')

    def snapshot(self):
        snapshot = self.root / 'transport'
        payload = snapshot / 'payload'
        (payload / 'lib/lean').mkdir(parents=True)
        (payload / 'lib/lean/Example.olean').write_bytes(b'candidate-output\0\xff')
        records = cache.inventory(payload)
        manifest = dict(schema=cache.SCHEMA, identity=self.identity, key=cache.cache_key(self.identity),
                        provider_scope=self.identity['provider_scope'], inventory=records,
                        bytes=sum(row['bytes'] for row in records.values()))
        cache.write_json(snapshot / cache.MANIFEST, manifest)
        return snapshot

    def test_every_identity_dimension_invalidates_exact_key(self):
        changes = {
            'head': 'new-head', 'tree': 'new-tree', 'toolchain_sha256': 'new-toolchain',
            'manifest_sha256': 'new-manifest', 'config_sha256': 'new-config',
            'compiler_binary_sha256': 'new-compiler', 'compiler_version': 'new-version',
            'package': 'other-package', 'package_source': 'new-source',
            'effective_package_options': {'leanOptions': {'x': False}},
            'option_environment_sha256': {'LEAN_PATH': 'changed'},
            'dependencies': [{'head': 'changed'}, {'source': 'changed-local-path'}],
            'targets': ['PoincareCurvature.Other'], 'build_arguments': ['-Kchanged'],
            'platform': {'os': 'Linux', 'machine': 'aarch64'},
            'provider_scope': {**self.identity['provider_scope'], 'GITHUB_REF': 'refs/heads/other'},
            'source_repository': 'fork/repo', 'output_root': 'other/build'}
        original = cache.cache_key(self.identity)
        for name, value in changes.items():
            with self.subTest(name=name):
                changed = copy.deepcopy(self.identity)
                changed[name] = value
                self.assertNotEqual(original, cache.cache_key(changed))
        self.assertEqual(original, cache.cache_key(dict(reversed(list(self.identity.items())))))

    def test_pinned_compiler_and_literal_target_controls(self):
        cache.validate_compiler('Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit ' + cache.COMPILER_COMMIT + ', Release)')
        for bad in ('Lean (version 4.33.1, x, commit ' + cache.COMPILER_COMMIT + ', Release)',
                    'Lean (version 4.33.0, x, commit ' + '0' * 40 + ', Release)', 'Lean 4.33.0'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                cache.validate_compiler(bad)
        for bad in ('[]', '["A","A"]', '["A; touch /tmp/no"]', '[{}]', 'true'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                cache.parse_targets(bad)

    def test_external_search_roots_fail_before_source_or_tool_execution(self):
        for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PLUGIN_PATH'):
            with self.subTest(name=name), mock.patch.dict(os.environ, {name: '/unsealed/root'}):
                with mock.patch.object(cache, 'clean') as clean, self.assertRaises(ValueError):
                    cache.identity(self.root, 'curvature', ['Example'], [])
                clean.assert_not_called()

    def test_tracked_path_dependency_bytes_and_modes(self):
        source = self.root / 'dependency'
        source.mkdir()
        leaf = source / 'Lake.lean'
        leaf.write_bytes(b'def original := 1\n')
        def git(*args):
            return subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True, timeout=10)
        git('init', '-q')
        git('add', 'dependency')
        git('-c', 'user.name=Cache Test', '-c', 'user.email=cache-test@example.invalid', 'commit', '-qm', 'fixture')
        expected = cache.tracked_source(self.root, source)
        self.assertEqual(len(expected), 64)
        leaf.write_bytes(b'def changed := 2\n')
        with self.assertRaises(ValueError):
            cache.tracked_source(self.root, source)
        leaf.write_bytes(b'def original := 1\n')
        os.chmod(leaf, 0o755)
        with self.assertRaises(ValueError):
            cache.tracked_source(self.root, source)

    def test_production_identity_extracts_actual_package_and_dependency_closure(self):
        project = self.root / 'project'
        package = project / 'curvature'
        dependency = package / '.lake/packages/mathlib'
        local = project / 'hamilton-ivey-reaction'
        dependency.mkdir(parents=True)
        local.mkdir()
        def git(directory, *args):
            return subprocess.check_output(['git', '-c', 'user.name=Cache Test',
                                           '-c', 'user.email=cache-test@example.invalid', *args],
                                          cwd=directory, timeout=10).decode().strip()
        git(dependency, 'init', '-q')
        dep_leaf = dependency / 'Mathlib.lean'
        dep_leaf.write_bytes(b'-- synthetic fixture dependency\n')
        git(dependency, 'add', '.')
        git(dependency, 'commit', '-qm', 'synthetic dependency')
        dep_head = git(dependency, 'rev-parse', 'HEAD')
        dep_tree = git(dependency, 'rev-parse', 'HEAD^{tree}')
        toolchain = b'leanprover/lean4:v4.33.0\n'
        config = b'name = "PoincareCurvature"\n[leanOptions]\n"pp.unicode.fun" = true\n'
        local_raw = b'-- actual committed local path dependency\n'
        (package / 'lean-toolchain').write_bytes(toolchain)
        (package / 'lakefile.toml').write_bytes(config)
        (package / 'PoincareCurvature.lean').write_bytes(b'-- fixture candidate\n')
        (local / 'Main.lean').write_bytes(local_raw)
        (project / '.gitignore').write_text('.lake/\n')
        manifest = {'version': '1.2.0', 'packagesDir': '.lake/packages', 'packages': [
            {'type': 'git', 'name': 'mathlib', 'url': 'https://github.com/leanprover-community/mathlib4', 'rev': dep_head},
            {'type': 'path', 'name': 'HamiltonIveyReaction', 'dir': '../hamilton-ivey-reaction'}]}
        cache.write_json(package / 'lake-manifest.json', manifest)
        git(project, 'init', '-q')
        git(project, 'add', '.')
        git(project, 'commit', '-qm', 'synthetic candidate')
        self.assertFalse((project / 'lean-toolchain').exists())
        self.assertFalse((project / 'lake-manifest.json').exists())
        prefix = self.root / 'fixture-toolchain'
        (prefix / 'bin').mkdir(parents=True)
        compiler_bytes = b'fixture binary bytes; never executed\n'
        (prefix / 'bin/lean').write_bytes(compiler_bytes)
        real_command = cache.command
        def command(directory, *args):
            if args == ('lake', 'env', 'lean', '--version'):
                self.assertEqual(directory, package)
                return 'Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit ' + cache.COMPILER_COMMIT + ', Release)'
            if args == ('lake', 'env', 'lean', '--print-prefix'):
                self.assertEqual(directory, package)
                return str(prefix)
            return real_command(directory, *args)  # All Git/source checks are real.
        scope = {'GITHUB_REPOSITORY': 'fixture/repo', 'GITHUB_REF': 'refs/pull/1/merge',
                 'GITHUB_WORKFLOW_REF': 'fixture/repo/.github/workflows/pilot.yml@ref',
                 'GITHUB_WORKFLOW_SHA': '9' * 40, 'P4_SOURCE_REPOSITORY': 'fixture/repo', 'CFLAGS': '-O2'}
        environment = {k: v for k, v in os.environ.items() if not k.startswith(('LEAN_', 'LAKE_'))}
        environment.update(scope)
        environment['EXPECTED_SHA'] = git(project, 'rev-parse', 'HEAD')
        # A synthetic Git commit cannot have the production Mathlib SHA. Bind the
        # expected fixture pin to its real commit; do not fake any Git response.
        with mock.patch.dict(os.environ, environment, clear=True), mock.patch.object(cache, 'MATHLIB', dep_head), \
                mock.patch.object(cache, 'command', side_effect=command):
            result = cache.identity(project, 'curvature', ['PoincareCurvature.Example'], [])
            self.assertEqual(result['head'], git(project, 'rev-parse', 'HEAD'))
            self.assertEqual(result['tree'], git(project, 'rev-parse', 'HEAD^{tree}'))
            self.assertEqual(result['toolchain_sha256'], hashlib.sha256(toolchain).hexdigest())
            self.assertEqual(result['config_sha256'], hashlib.sha256(config).hexdigest())
            self.assertEqual(result['manifest_sha256'], hashlib.sha256((package / 'lake-manifest.json').read_bytes()).hexdigest())
            self.assertEqual(result['compiler_binary_sha256'], hashlib.sha256(compiler_bytes).hexdigest())
            self.assertEqual(result['effective_package_options']['leanOptions'], {'pp.unicode.fun': True})
            self.assertEqual(result['targets'], ['PoincareCurvature.Example'])
            self.assertEqual(result['provider_scope'], {k: v for k, v in scope.items() if k.startswith('GITHUB_')})
            self.assertEqual(result['option_environment_sha256']['CFLAGS'], hashlib.sha256(b'-O2').hexdigest())
            self.assertEqual(result['dependencies'][0]['head'], dep_head)
            self.assertEqual(result['dependencies'][0]['tree'], dep_tree)
            local_oid = hashlib.sha1(b'blob ' + str(len(local_raw)).encode() + b'\0' + local_raw).hexdigest()
            local_records = {'hamilton-ivey-reaction/Main.lean': ['100644', local_oid, hashlib.sha256(local_raw).hexdigest()]}
            expected_local = hashlib.sha256(json.dumps(local_records, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            self.assertEqual(result['dependencies'][1]['source'], expected_local)
            self.assertEqual(result['dependencies'][1]['directory'], 'hamilton-ivey-reaction')
            package_records = {}
            for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'PoincareCurvature.lean'):
                raw = (package / name).read_bytes()
                oid = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
                package_records['curvature/' + name] = ['100644', oid, hashlib.sha256(raw).hexdigest()]
            expected_package = hashlib.sha256(json.dumps(package_records, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            self.assertEqual(result['package_source'], expected_package)
            manifest['packages'][0]['rev'] = '0' * 40
            cache.write_json(package / 'lake-manifest.json', manifest)
            git(project, 'add', 'curvature/lake-manifest.json')
            git(project, 'commit', '-qm', 'wrong declared revision')
            os.environ['EXPECTED_SHA'] = git(project, 'rev-parse', 'HEAD')
            with self.assertRaises(ValueError):
                cache.identity(project, 'curvature', ['PoincareCurvature.Example'], [])
            manifest['packages'][0]['rev'] = dep_head
            cache.write_json(package / 'lake-manifest.json', manifest)
            git(project, 'add', 'curvature/lake-manifest.json')
            git(project, 'commit', '-qm', 'restore declared revision')
            os.environ['EXPECTED_SHA'] = git(project, 'rev-parse', 'HEAD')
            dep_leaf.write_bytes(b'-- dirty dependency\n')
            with self.assertRaises(subprocess.CalledProcessError):
                cache.identity(project, 'curvature', ['PoincareCurvature.Example'], [])

    def test_inventory_corruption_missing_extra_and_identity_rejected(self):
        snapshot = self.snapshot()
        leaf = snapshot / 'payload/lib/lean/Example.olean'
        original = leaf.read_bytes()
        leaf.write_bytes(b'forged')
        with self.assertRaises(ValueError):
            cache.validate_snapshot(snapshot, self.identity)
        leaf.unlink()
        with self.assertRaises(ValueError):
            cache.validate_snapshot(snapshot, self.identity)
        leaf.write_bytes(original)
        extra = snapshot / 'payload/extra'
        extra.write_text('extra')
        with self.assertRaises(ValueError):
            cache.validate_snapshot(snapshot, self.identity)
        extra.unlink()
        changed = {**self.identity, 'head': 'changed'}
        with self.assertRaises(ValueError):
            cache.validate_snapshot(snapshot, changed)
        self.assertEqual(cache.validate_snapshot(snapshot, self.identity)['bytes'], len(original))

    def test_manifest_path_and_strict_json_rejections(self):
        snapshot = self.snapshot()
        manifest_path = snapshot / cache.MANIFEST
        original = manifest_path.read_bytes()
        manifest = json.loads(original)
        manifest['inventory']['../escape'] = manifest['inventory'].pop('lib/lean/Example.olean')
        cache.write_json(manifest_path, manifest)
        with self.assertRaises(ValueError):
            cache.validate_snapshot(snapshot, self.identity)
        for raw in (b'{"key":1,"key":2}', b'{"x":NaN}', b'{"x":1e999}'):
            manifest_path.write_bytes(raw)
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                cache.strict_json(manifest_path)

    def test_symlink_special_file_alias_and_resource_limits(self):
        payload = self.root / 'payload'
        payload.mkdir()
        outside = self.root / 'outside'
        outside.write_bytes(b'outside')
        link = payload / 'link'
        link.symlink_to(outside)
        with self.assertRaises(ValueError):
            cache.inventory(payload)
        link.unlink()
        os.mkfifo(link)
        with self.assertRaises(ValueError):
            cache.inventory(payload)
        link.unlink()
        (payload / 'A').mkdir()
        (payload / 'a').mkdir()
        with self.assertRaises(ValueError):
            cache.inventory(payload)
        (payload / 'a').rmdir()
        (payload / 'A/file').write_bytes(b'123')
        with mock.patch.object(cache, 'MAX_BYTES', 2), self.assertRaises(ValueError):
            cache.inventory(payload)
        with mock.patch.object(cache, 'MAX_FILES', 0), self.assertRaises(ValueError):
            cache.inventory(payload)

    def test_verified_restore_replaces_outputs_and_removes_backup(self):
        snapshot = self.snapshot()
        target = self.root / self.identity['output_root']
        target.mkdir(parents=True)
        (target / 'old').write_text('old')
        restored = cache.replace_outputs(self.root, snapshot, self.identity)
        self.assertEqual(restored, len(b'candidate-output\0\xff'))
        self.assertFalse((target / 'old').exists())
        self.assertEqual((target / 'lib/lean/Example.olean').read_bytes(), b'candidate-output\0\xff')
        self.assertFalse(target.with_name('point4-cache-build-backup').exists())

    def test_corrupt_restore_never_modifies_active_outputs(self):
        snapshot = self.snapshot()
        target = self.root / self.identity['output_root']
        target.mkdir(parents=True)
        (target / 'old').write_text('preserved')
        (snapshot / 'payload/lib/lean/Example.olean').write_text('corrupt')
        with self.assertRaises(ValueError):
            cache.replace_outputs(self.root, snapshot, self.identity)
        self.assertEqual((target / 'old').read_text(), 'preserved')

    def test_failed_post_injection_validation_rolls_back(self):
        snapshot = self.snapshot()
        target = self.root / self.identity['output_root']
        target.mkdir(parents=True)
        (target / 'old').write_text('preserved')
        real_inventory = cache.inventory
        def fail_final(path):
            if path == target and target.with_name('point4-cache-build-backup').exists():
                raise ValueError('simulated post-injection failure')
            return real_inventory(path)
        with mock.patch.object(cache, 'inventory', side_effect=fail_final), self.assertRaises(ValueError):
            cache.replace_outputs(self.root, snapshot, self.identity)
        self.assertEqual((target / 'old').read_text(), 'preserved')
        self.assertFalse(target.with_name('point4-cache-build-backup').exists())

    def test_symlink_ancestor_is_rejected_before_writing(self):
        snapshot = self.snapshot()
        outside = self.root / 'outside'
        outside.mkdir()
        (self.root / 'curvature').symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            cache.replace_outputs(self.root, snapshot, self.identity)
        self.assertEqual(list(outside.iterdir()), [])

    def test_cold_miss_requires_manual_success_and_rechecks_identity(self):
        repo, state = self.root / 'repo', self.root / 'state'
        repo.mkdir()
        def phase(name, *extra, identity=None):
            argv = ['point4_ci_cache.py', name, '--root', str(repo), '--state-dir', str(state),
                    '--targets-json', '["Example"]', *extra]
            with mock.patch.object(sys, 'argv', argv), mock.patch.object(cache, 'identity', return_value=identity or self.identity), \
                    mock.patch.dict(os.environ, {'GITHUB_OUTPUT': '', 'GITHUB_STEP_SUMMARY': ''}):
                cache.main()
        phase('identity')
        with self.assertRaises(ValueError):
            phase('restore', identity={**self.identity, 'head': 'changed'})
        phase('restore')
        with self.assertRaises(ValueError):
            phase('snapshot', '--manual-success', 'false')
        output = repo / self.identity['output_root']
        output.mkdir(parents=True)
        (output / 'Example.olean').write_bytes(b'compiled-cold-fixture')
        phase('snapshot', '--manual-success', 'true')
        saved = cache.strict_json(state / 'state.json')
        self.assertTrue(saved['save_requested'])
        self.assertFalse(saved['cache_hit'])
        self.assertEqual(saved['restored_bytes'], 0)
        self.assertEqual(cache.validate_snapshot(state / 'snapshot', self.identity)['bytes'], 21)
        phase('report', '--save-step-outcome', 'success')
        self.assertEqual(cache.strict_json(state / 'state.json')['save_action_step_outcome'], 'success')


if __name__ == '__main__':
    unittest.main(verbosity=2)
