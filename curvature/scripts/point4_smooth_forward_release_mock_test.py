#!/usr/bin/env python3
"""Bounded composed-inventory fixtures. Synthetic records are not Lean evidence."""
from __future__ import annotations
import copy
import ast
import contextlib
import importlib
import io
import json
import pathlib
import re
import stat
import sys
import hashlib
import tempfile
import types
import unittest
from unittest.mock import patch
import point4_smooth_forward_release_guard as smooth

NEWLY_ADMITTED_MATH_PATHS = ('curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/IntrinsicRicciReindex.lean', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardBasis.lean', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/SmoothForwardTimeTranslate.lean', 'curvature/TimeTranslateVerification.lean', 'curvature/Verification.lean', 'curvature/scripts/point4_smooth_forward_basis_probe.lean', 'docs/point4/smooth-forward-finite-basis.md')


class SmoothReleaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source_root = smooth.ROOT
        cls.temp = tempfile.TemporaryDirectory()
        cls.root = pathlib.Path(cls.temp.name)
        for path in smooth.ADDED:
            dest = cls.root/path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes((cls.source_root/path).read_bytes())
        release = (cls.source_root/smooth.LEGACY_GUARD).read_bytes()
        # Reconstruct original guard from the one reviewed hook; verify its
        # independently pinned digest before creating mocked immutable Git data.
        cls.guard_hash = smooth.sha256((cls.source_root/smooth.GUARD).read_bytes())
        adapter = smooth.ADAPTER_TEMPLATE.format(guard_sha256=cls.guard_hash).encode()
        assert release.count(adapter) == 1
        original = release.replace(adapter, b'\n', 1)
        assert smooth.sha256(original) == smooth.ORIGINAL_SHA256
        cls.baseline = {smooth.LEGACY_GUARD: ('100644', original),
                        smooth.LEGACY_TEST: ('100644', (cls.source_root/smooth.LEGACY_TEST).read_bytes())}
        for i in range(1651):
            cls.baseline[f'inherited/{i:04}.txt'] = '100644', f'immutable {i}\n'.encode()
        for path, (_, data) in cls.baseline.items():
            dest = cls.root/path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(release if path == smooth.LEGACY_GUARD else data)
        cls.tree = b''.join(f'{mode} blob {smooth.blob(data)}\t{path}\0'.encode()
                            for path, (mode, data) in cls.baseline.items())

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def setUp(self):
        self.root_patch = patch.object(smooth, 'ROOT', self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.trace = []
        self.cached = set(self.baseline) | set(smooth.ADDED)
        self.untracked = set()
        self.tree = type(self).tree
        self.expected_error = None
        self.mode_error = None
        self.fail_body = False
        def git(*argv):
            self.trace.append(('git', argv))
            if argv == ('ls-tree', '-rz', smooth.BASE):
                return self.tree
            if argv[:1] == ('show',):
                ref, path = argv[1].split(':', 1)
                assert ref == smooth.BASE
                return self.baseline[path][1]
            if argv == ('ls-files', '-z', '--cached'):
                return ''.join(path+'\0' for path in sorted(self.cached)).encode()
            if argv == ('ls-files', '-z', '--others', '--exclude-standard'):
                return ''.join(path+'\0' for path in sorted(self.untracked)).encode()
            raise AssertionError(('Unexpected mocked remote Git request', argv))
        def nul(data):
            assert not data or data.endswith(b'\0')
            return {path.decode() for path in data.split(b'\0') if path}
        def original_expected():
            self.trace.append(('historical',))
            if self.expected_error:
                raise self.expected_error
            return {p: (smooth.BASE, data) for p, (_, data) in self.baseline.items()
                    if p not in {smooth.LEGACY_GUARD, smooth.LEGACY_TEST}}
        def mode(path, actual, wanted):
            self.trace.append(('mode', path))
            assert stat.S_ISREG(actual) and bool(actual & 0o111) == (wanted == '100755')
            if path == self.mode_error:
                raise AssertionError('Mode fixture')
        self.c2 = types.SimpleNamespace(public_paths=lambda cached, other: cached | other,
                                        nul_paths=nul)
        def body(argv=None):
            self.trace.append(('body', argv))
            assert set(self.ns['expected_sources']()) == self.cached
            assert self.ns['public_paths']() == self.cached
            if self.fail_body:
                raise RuntimeError('Inherited validator failed')
        self.ns = {'RELEASE_GUARD': smooth.LEGACY_GUARD,
                   'SELF_PATHS': {smooth.LEGACY_GUARD, smooth.LEGACY_TEST},
                   'expected_sources': original_expected,
                   'public_paths': lambda: set(self.baseline),
                   'install_c2_inventory_adapter': lambda ns: None,
                   'main': body, 'git': git, 'check_mode': mode,
                   'c2_guard': lambda: self.c2, 'ENV': {}}
        smooth.install_release_adapter(self.ns, self.guard_hash)
        self.original_expected = self.ns['expected_sources']
        self.original_paths = self.ns['public_paths']
        self.run_patch = patch.object(smooth.subprocess, 'run', return_value=types.SimpleNamespace(returncode=0))
        self.run = self.run_patch.start()
        self.addCleanup(self.run_patch.stop)

    def assert_restored(self):
        self.assertIs(self.ns['expected_sources'], self.original_expected)
        self.assertIs(self.ns['public_paths'], self.original_paths)
        self.assertEqual(smooth._depth, 0)
        self.assertIsNone(smooth._active_namespace)

    def test_scoped_gate_wrapper_composed_union_precedes_historical_projection(self):
        self.ns['main'](['--schema', 'schema.json'])
        first_history = self.trace.index(('historical',))
        modes = [item for item in self.trace[:first_history] if item[0] == 'mode']
        self.assertEqual(len(modes), 1672)
        self.assertEqual(self.trace[-1], ('body', ['--schema', 'schema.json']))
        self.run.assert_called_once_with(['git', '-C', str(self.root), 'merge-base', '--is-ancestor', smooth.BASE, 'HEAD'], check=True, env={})
        self.assert_restored()
        # Outside actual gate mains the historical fixture inventory is exact.
        self.assertEqual(len(self.ns['public_paths']()), 1653)

    def test_smooth_cli_wrapper_forwards_all_inherited_evidence(self):
        release = types.SimpleNamespace(main=self.ns['main'])
        with patch.object(smooth, 'legacy', return_value=release), \
             patch.object(smooth, 'check_new_metadata') as provenance, \
             patch('builtins.print'):
            smooth.main(['--probe-log', 'old.log', '--axiom-dir', 'axioms',
                         '--audit-json', 'audit.json', '--audit-rc', '1'])
        provenance.assert_called_once_with((self.root/smooth.METADATA).read_text())
        self.assertIn(('body', ['--probe-log', 'old.log', '--axiom-dir', 'axioms',
                               '--audit-json', 'audit.json', '--audit-rc', '1']), self.trace)
        self.assert_restored()

    def test_mocked_remote_extra_omission_and_wrong_base_fail_before_projection(self):
        for added, removed in (({'unapproved.py'}, set()), (set(), {smooth.GUARD}),
                               (set(), {smooth.PROBE}), (set(), {'inherited/0000.txt'})):
            original = self.cached.copy()
            self.cached = (self.cached | added) - removed
            self.trace.clear()
            with self.assertRaises(AssertionError):
                self.ns['main']()
            self.assertNotIn(('historical',), self.trace)
            self.assert_restored()
            self.cached = original
        self.run.side_effect = smooth.subprocess.CalledProcessError(1, 'wrong ancestry')
        with self.assertRaises(smooth.subprocess.CalledProcessError):
            self.ns['main']()
        self.assert_restored()

    def test_source_hook_and_executable_edits_fail_before_projection(self):
        for path in (smooth.LEGACY_GUARD, smooth.GUARD, smooth.TEST, smooth.PROBE,
                     smooth.METADATA, 'inherited/0000.txt'):
            file = self.root/path
            original = file.read_bytes()
            for wrong in (original+b'\nunauthorized executable body\n',):
                file.write_bytes(wrong)
                try:
                    self.trace.clear()
                    with self.assertRaises(AssertionError):
                        self.ns['main']()
                    self.assertNotIn(('historical',), self.trace)
                    self.assert_restored()
                finally:
                    file.write_bytes(original)
        file = self.root/smooth.LEGACY_GUARD
        original = file.read_bytes()
        hook = smooth.ADAPTER_TEMPLATE.format(guard_sha256=self.guard_hash).encode()
        for wrong in (original.replace(hook, b'', 1), original.replace(hook, hook*2, 1),
                      hook + original.replace(hook, b'', 1)):
            file.write_bytes(wrong)
            try:
                with self.assertRaises(AssertionError):
                    self.ns['main']()
            finally:
                file.write_bytes(original)
            self.assert_restored()

    def test_missing_unreadable_mode_and_symlink_fail_closed(self):
        file = self.root/smooth.PROBE
        original = file.read_bytes()
        file.unlink()
        try:
            with self.assertRaises((OSError, AssertionError)):
                self.ns['main']()
        finally:
            file.write_bytes(original)
        real_read = pathlib.Path.read_bytes
        def unreadable(path):
            if path == file:
                raise PermissionError('Unreadable fixture')
            return real_read(path)
        with patch.object(pathlib.Path, 'read_bytes', unreadable), self.assertRaises(PermissionError):
            self.ns['main']()
        self.mode_error = smooth.TEST
        with self.assertRaises(AssertionError):
            self.ns['main']()
        self.mode_error = None
        real_stat = pathlib.Path.lstat
        def symlink(path):
            if path == file:
                return types.SimpleNamespace(st_mode=stat.S_IFLNK | 0o777)
            return real_stat(path)
        with patch.object(pathlib.Path, 'lstat', symlink), self.assertRaises(AssertionError):
            self.ns['main']()
        self.assert_restored()

    def test_failure_unwinds_nested_repeated_and_cross_namespace_calls(self):
        for where in ('historical', 'body'):
            self.expected_error = RuntimeError('Historical gate failed') if where == 'historical' else None
            self.fail_body = where == 'body'
            with self.assertRaises(RuntimeError):
                self.ns['main']()
            self.assert_restored()
        self.expected_error = None
        self.fail_body = False
        with smooth.inventory_scope(self.ns):
            for _ in range(2):
                self.ns['main']()
                self.assertEqual(smooth._depth, 1)
            with self.assertRaises(AssertionError):
                with smooth.inventory_scope(dict(self.ns)):
                    pass
        self.assert_restored()
        for _ in range(2):
            self.ns['main']()
            self.assert_restored()
        with self.assertRaises(AssertionError):
            smooth.install_release_adapter(self.ns, self.guard_hash)

    def test_tree_duplicate_truncated_nonregular_and_blob_drift(self):
        first = self.tree.split(b'\0', 1)[0]+b'\0'
        for wrong in (self.tree[:-1], self.tree+first, self.tree.replace(b'100644 blob', b'120000 blob', 1),
                      self.tree.replace(b'100644 blob', b'100644 tree', 1),
                      self.tree.replace(b' blob ', b' blob Z', 1)):
            with self.assertRaises((AssertionError, ValueError)):
                smooth.parse_tree(wrong)
        real_tree = self.tree
        self.tree = self.tree.replace(smooth.blob(self.baseline['inherited/0000.txt'][1]).encode(), b'0'*40)
        with self.assertRaises(AssertionError):
            self.ns['main']()
        self.tree = real_tree
        self.assert_restored()

    def test_real_hook_rejects_missing_or_arbitrary_guard_before_import(self):
        hook = smooth.ADAPTER_TEMPLATE.format(guard_sha256=self.guard_hash)
        namespace = {'ROOT': self.root, 'stat': stat, 'hashlib': hashlib,
                     'sys': sys, '__name__': 'smooth_hook_fixture'}
        fake_owner = types.ModuleType('smooth_hook_fixture')
        module_state = {'smooth_hook_fixture': fake_owner,
                        'point4_manifold_heat_release_guard': fake_owner}
        with patch.dict(sys.modules, module_state), patch.object(smooth, 'install_release_adapter') as install:
            exec(compile(hook, '<exact reviewed hook>', 'exec'), namespace)
            install.assert_called_once_with(namespace, self.guard_hash)
            install.reset_mock()
            path = self.root/smooth.GUARD
            original = path.read_bytes()
            path.write_bytes(b"raise RuntimeError('arbitrary executable must never import')\n")
            try:
                with self.assertRaises(AssertionError):
                    exec(compile(hook, '<exact reviewed hook>', 'exec'), namespace)
                install.assert_not_called()
            finally:
                path.write_bytes(original)
            path.unlink()
            try:
                with self.assertRaises(OSError):
                    exec(compile(hook, '<exact reviewed hook>', 'exec'), namespace)
                install.assert_not_called()
            finally:
                path.write_bytes(original)
            with self.assertRaises(AssertionError):
                exec(compile(smooth.ADAPTER_TEMPLATE.format(guard_sha256='0'*64), '<wrong guard hash>', 'exec'), namespace)
            install.assert_not_called()

    def test_smooth_negative_completion_and_full_open_audit_are_exact(self):
        log = '\n'.join(f'point4_smooth_forward_completion.lean:{n}:3: error(lean.unknownIdentifier): Unknown identifier `{smooth.TARGET}`'
                        for n in (22, 34, 46, 48))
        smooth.check_completion_open(log, 1)
        for wrong in ('\n'.join(log.splitlines()[:-1]), log+'\nwarning: extra',
                      log.replace(smooth.TARGET, 'Other.target', 1), log.replace(':22:', ':23:', 1)):
            with self.assertRaises(AssertionError):
                smooth.check_completion_open(wrong, 1)
        with self.assertRaises(AssertionError):
            smooth.check_completion_open(log, 0)
        report = {'scope': 'separate smooth forward model target', 'target': smooth.TARGET,
                  'verdict': 'SMOOTH FORWARD TARGET OPEN',
                  'canonical_point4': 'NO STATUS CHANGE; canonical completion requires its own actual audit',
                  'gates': {'pins': True, 'frozen_interfaces': True, 'source_scan': True,
                            'official_version': True, 'full_build': True, 'new_module_build': True,
                            'exact_type': False, 'standard_axioms': False}}
        smooth.check_smooth_audit_open(report, 1)
        for key in report['gates']:
            wrong = copy.deepcopy(report)
            wrong['gates'][key] = not wrong['gates'][key]
            with self.assertRaises(AssertionError):
                smooth.check_smooth_audit_open(wrong, 1)
        for key, value in (('full_build', 1), ('extra_gate', True)):
            wrong = copy.deepcopy(report); wrong['gates'][key] = value
            with self.assertRaises(AssertionError):
                smooth.check_smooth_audit_open(wrong, 1)
        with self.assertRaises(AssertionError):
            smooth.check_smooth_audit_open(report, 0)

    def test_newly_admitted_math_paths_have_exact_reviewed_hashes(self):
        self.assertEqual(len(NEWLY_ADMITTED_MATH_PATHS), 7)
        for path in NEWLY_ADMITTED_MATH_PATHS:
            file = self.root/path
            original = file.read_bytes()
            self.assertEqual(smooth.sha256(original), smooth.FILE_SHA256[path])
            file.write_bytes(original+b'\nunauthorized mathematical source edit\n')
            try:
                self.trace.clear()
                with self.subTest(path=path), self.assertRaises(AssertionError):
                    self.ns['main']()
                self.assertNotIn(('historical',), self.trace)
                self.assert_restored()
            finally:
                file.write_bytes(original)

    def test_newly_admitted_math_path_omissions_fail_before_reconstruction(self):
        for path in NEWLY_ADMITTED_MATH_PATHS:
            self.cached.remove(path)
            try:
                self.trace.clear()
                with self.subTest(path=path), self.assertRaises(AssertionError):
                    self.ns['main']()
                self.assertNotIn(('historical',), self.trace)
                self.assert_restored()
            finally:
                self.cached.add(path)

    def test_newly_admitted_math_path_mode_drift_fails_before_reconstruction(self):
        real_stat = pathlib.Path.lstat
        for target in NEWLY_ADMITTED_MATH_PATHS:
            def executable_mode(path):
                if path == self.root/target:
                    return types.SimpleNamespace(st_mode=stat.S_IFREG | 0o755)
                return real_stat(path)
            self.trace.clear()
            with patch.object(pathlib.Path, 'lstat', executable_mode), \
                 self.subTest(path=target), self.assertRaises(AssertionError):
                self.ns['main']()
            self.assertNotIn(('historical',), self.trace)
            self.assert_restored()


    def test_six_support_axiom_surfaces_use_unchanged_inherited_parser(self):
        # Execute only the unchanged parser functions from the pinned C2 source;
        # no synthetic YAML module or optional parser dependency is introduced.
        source = (self.source_root/'curvature/scripts/point4_c2_initial_heat_source_test.py').read_text()
        nodes = [node for node in ast.parse(source).body if isinstance(node, ast.FunctionDef)
                 and node.name in {'probe_names', 'check_axiom_output'}]
        self.assertEqual(len(nodes), 2)
        namespace = {'re': re}
        exec(compile(ast.Module(body=nodes, type_ignores=[]), '<unchanged inherited axiom parser>', 'exec'), namespace)
        parser = types.SimpleNamespace(check_axiom_output=namespace['check_axiom_output'])
        release = types.SimpleNamespace(c2_guard=lambda: parser)
        names = re.findall(r'^#print axioms (\S+)', (self.root/smooth.PROBE).read_text(), re.M)
        self.assertEqual(len(names), 6)
        output = '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)
        with patch.object(smooth, 'legacy', return_value=release):
            smooth.check_support_probe(output)
            for wrong in ('\n'.join(output.splitlines()[1:]), output+'\n'+output.splitlines()[0],
                          output.replace('Quot.sound', 'Hidden.oracle', 1),
                          output.replace('Quot.sound', 'propext', 1),
                          output+"\n'Extra.target' does not depend on any axioms"):
                with self.assertRaises(AssertionError):
                    smooth.check_support_probe(wrong)


class RealComposedGateTests(unittest.TestCase):
    """Required on the complete CI checkout after official parser/schema setup.

    Every main and validator is the actual imported function. Only external
    immutable Git reads are intercepted/cached; real physical files and YAML/
    schema parsers are retained. Synthetic logs test evidence rejection only.
    """
    @classmethod
    def setUpClass(cls):
        cls.release = smooth.legacy()
        cls.c2 = cls.release.c2_guard()
        cls.source = importlib.import_module('point4_manifold_heat_source_test')
        cls.schema = pathlib.Path('/tmp/point4-manifold-heat-official-schema.json')
        assert cls.schema.is_file(), 'Required real composed gate needs the workflow official schema'
        assert smooth.sha256(cls.schema.read_bytes()) == cls.c2.SCHEMA_SHA256
        cls.temp = tempfile.TemporaryDirectory()
        cls.evidence = pathlib.Path(cls.temp.name)
        cls.axioms = cls.evidence/'axioms'
        cls.axioms.mkdir()
        for name in cls.c2.PROBES:
            names = cls.c2.probe_names((smooth.ROOT/f'curvature/scripts/point4_{name}_probe.lean').read_text())
            output = cls.axiom_output(names)
            if name == 'boundaryless_chart_frames':
                output += '\nBOUNDARYLESS_TYPES_BEGIN\n'+'BoundarylessManifold I M\n'*7+'BOUNDARYLESS_TYPES_END\n'
            (cls.axioms/(name+'.log')).write_text(output)
        cls.old_probe = cls.evidence/'old-probe.log'
        names = cls.c2.probe_names((smooth.ROOT/cls.release.PROBE).read_text())
        cls.old_probe.write_text(cls.axiom_output(names)+'\nMANIFOLD_HEAT_TYPES_BEGIN\n'+
                                'BoundarylessManifold I M\n'*4+'MANIFOLD_HEAT_TYPES_END\n')
        cls.support = cls.evidence/'support.log'
        cls.support.write_text(cls.axiom_output(cls.c2.probe_names((smooth.ROOT/smooth.PROBE).read_text())))
        cls.completion = cls.evidence/'completion.log'
        cls.completion.write_text('\n'.join(f'point4_smooth_forward_completion.lean:{n}:3: error(lean.unknownIdentifier): Unknown identifier `{smooth.TARGET}`' for n in (22,34,46,48)))
        cls.canonical = cls.evidence/'canonical.json'
        cls.canonical.write_text(json.dumps({'build_run': True, 'target_base': 'intrinsicLocalExistenceUniquenessFamily_pointFour',
                                             'fqn': '', 'verdict': 'OPEN', 'gates': {
            'G1_sorry_free': {'status': 'PASS'}, 'G2_build_green': {'status': 'PASS'},
            'G3_unconditional': {'status': 'FAIL'}, 'G4_axiom_clean': {'status': 'FAIL'},
            'G5_faithful_type': {'status': 'FAIL'}}}))
        cls.smooth_audit = cls.evidence/'smooth.json'
        cls.smooth_audit.write_text(json.dumps({'scope': 'separate smooth forward model target', 'target': smooth.TARGET,
            'verdict': 'SMOOTH FORWARD TARGET OPEN', 'canonical_point4': 'NO STATUS CHANGE; canonical completion requires its own actual audit',
            'gates': {'pins': True, 'frozen_interfaces': True, 'source_scan': True, 'official_version': True,
                      'full_build': True, 'new_module_build': True, 'exact_type': False, 'standard_axioms': False}}))
        cls.argv = ['--schema', str(cls.schema), '--probe-log', str(cls.old_probe),
                    '--axiom-dir', str(cls.axioms), '--audit-json', str(cls.canonical), '--audit-rc', '1',
                    '--smooth-probe-log', str(cls.support), '--smooth-completion-log', str(cls.completion),
                    '--smooth-completion-rc', '1', '--smooth-audit-json', str(cls.smooth_audit), '--smooth-audit-rc', '1']
        cls.git_cache = {}
        cls.real_git = staticmethod(cls.release.git)

    @staticmethod
    def axiom_output(names):
        return '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    @contextlib.contextmanager
    def external_git_reads(self):
        self.external_calls = []
        def remote(*argv):
            self.external_calls.append(argv)
            if argv not in self.git_cache:
                self.git_cache[argv] = self.real_git(*argv)
            return self.git_cache[argv]
        def source_remote(repo, *argv):
            assert repo == smooth.ROOT
            return remote(*argv)
        with patch.object(self.release, 'git', side_effect=remote), \
             patch.object(self.c2, 'git', side_effect=remote), \
             patch.object(self.source, 'git', side_effect=source_remote):
            yield

    def test_actual_inherited_mains_and_all_original_validator_bodies_run(self):
        # Profile calls without replacing, wrapping or stubbing any validator.
        functions = [self.release._smooth_original_main, self.c2.main.__wrapped__,
                     self.c2.check_equal, self.c2.check_public_paths, self.c2.check_imports,
                     self.c2.check_metadata, self.c2.check_workflow, self.c2.check_axiom_output,
                     self.c2.check_boundaryless_types, self.c2.check_audit,
                     self.release.check_modes, self.release.check_public_paths,
                     self.release.check_physical_lean, self.release.check_root_metadata,
                     self.release.check_new_metadata, self.release.check_new_probe,
                     self.source.check_sources, self.source.check_probe, smooth.check_new_metadata,
                     smooth.check_support_probe, smooth.check_completion_open, smooth.check_smooth_audit_open]
        required = {fn.__code__ for fn in functions}
        called = set()
        previous = sys.getprofile()
        def profile(frame, event, arg):
            if event == 'call' and frame.f_code in required:
                called.add(frame.f_code)
        expected_before = self.release.expected_sources
        paths_before = self.release.public_paths
        try:
            with self.external_git_reads(), contextlib.redirect_stdout(io.StringIO()):
                sys.setprofile(profile)
                smooth.main(self.argv)
        finally:
            sys.setprofile(previous)
        self.assertEqual(called, required, 'A real inherited validator body was not executed')
        self.assertTrue(self.external_calls)
        self.assertIs(self.release.expected_sources, expected_before)
        self.assertIs(self.release.public_paths, paths_before)
        self.assertEqual(smooth._depth, 0)
        self.assertIsNone(smooth._active_namespace)

    def test_real_inherited_axiom_and_canonical_failures_propagate_and_restore(self):
        for file, wrong in ((self.old_probe, self.old_probe.read_text().replace('Quot.sound', 'Hidden.oracle', 1)),
                            (self.canonical, self.canonical.read_text().replace('"build_run": true', '"build_run": false', 1))):
            original = file.read_text()
            file.write_text(wrong)
            expected_before = self.release.expected_sources
            paths_before = self.release.public_paths
            try:
                with self.external_git_reads(), contextlib.redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
                    smooth.main(self.argv)
            finally:
                file.write_text(original)
            self.assertIs(self.release.expected_sources, expected_before)
            self.assertIs(self.release.public_paths, paths_before)
            self.assertEqual(smooth._depth, 0)
            self.assertIsNone(smooth._active_namespace)


# Reviewed finite smooth/master composition; original validator bodies survive.
import hashlib as _composition_hashlib, pathlib as _composition_pathlib, stat as _composition_stat, sys as _composition_sys
_composition_file = _composition_pathlib.Path(__file__).resolve().parents[2] / 'curvature/scripts/point4_smooth_master_composition.py'
assert _composition_stat.S_ISREG(_composition_file.lstat().st_mode) and not _composition_file.lstat().st_mode & 0o111
assert _composition_hashlib.sha256(_composition_file.read_bytes()).hexdigest() == '16dd081d6873024649fa235294d570db3aa0a61818c07ee96a4157f4bd32b64d', 'Composition executable binding changed'
import point4_smooth_master_composition as _smooth_master
if __name__ == '__main__':
    _smooth_master.run_support_fixtures(sys.argv[1:])
    raise SystemExit(0)

if __name__ == '__main__':
    # Fixture selection only; the admission gate never consults this flag or
    # knows which test invokes it. Hosted CI must request both fixture classes.
    real_composed = '--real-composed' in sys.argv
    if real_composed:
        sys.argv.remove('--real-composed')
    classes = [SmoothReleaseTests] + ([RealComposedGateTests] if real_composed else [])
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(cls) for cls in classes)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
