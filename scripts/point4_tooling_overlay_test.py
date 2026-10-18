"""Native Git regressions for the finite tooling overlay, without Lean builds."""
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import stat
import tempfile
import unittest
from unittest import mock

PATH = Path(__file__).absolute().with_name('point4_tooling_overlay.py')
SPEC = importlib.util.spec_from_file_location('point4_overlay_under_test', PATH)
OVERLAY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(OVERLAY)


class ToolingOverlayTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='point4-overlay-regression-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Local fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        # A complete finite baseline fixture, including actual proof-like bytes.
        self.proof = 'curvature/Fixture.lean'
        self.write(self.proof, b'theorem fixture : True := True.intro\n')
        self.transport_before = b'name: Original dispatch\non:\n  workflow_dispatch:\njobs:\n  upstream-checkpoint:\n    steps: original-unchanged\n'
        changed = self.transport_before.decode()
        for before, after in OVERLAY.TRANSPORT_REQUIRED_PORTS:
            self.assertEqual(changed.count(before), 1)
            changed = changed.replace(before, after, 1)
        self.transport_after = (changed + OVERLAY.TRANSPORT_REQUIRED_APPEND).encode()
        self.write(OVERLAY.TRANSPORT_PATH, self.transport_before)
        self.legacy_before = {}
        for path in sorted(OVERLAY.LEGACY_PATHS):
            raw = ('original legacy Source: ' + path + '\n').encode()
            self.write(path, raw)
            self.legacy_before[path] = raw
        for index in range(2166):
            self.write('baseline/%04d.txt' % index, ('baseline-%d\n' % index).encode())
        self.git('add', '--all')
        self.git('commit', '-qm', 'Baseline fixture')
        self.base = self.git('rev-parse', 'HEAD').decode().strip()
        self.base_tree = self.git('rev-parse', 'HEAD^{tree}').decode().strip()
        rows = {}
        for path in sorted(OVERLAY.OTHER_PATHS):
            raw = ('reviewed tooling: ' + path + '\n').encode()
            self.write(path, raw)
            mode = '100755' if path == 'scripts/point4_ci/command_broker.py' else '100644'
            if mode == '100755':
                (self.root / path).chmod(0o755)
            rows[path] = dict(mode=mode, blob=OVERLAY.blob_id(raw),
                              sha256=OVERLAY.sha256(raw), bytes=len(raw))
        self.write(OVERLAY.TRANSPORT_PATH, self.transport_after)
        transport = dict(before_blob=OVERLAY.blob_id(self.transport_before),
                         before_sha256=OVERLAY.sha256(self.transport_before),
                         after_blob=OVERLAY.blob_id(self.transport_after),
                         after_sha256=OVERLAY.sha256(self.transport_after),
                         after_bytes=len(self.transport_after),
                         ports=json.loads(json.dumps(OVERLAY.TRANSPORT_REQUIRED_PORTS)),
                         append_exact=OVERLAY.TRANSPORT_REQUIRED_APPEND)
        legacy = {}
        for path in sorted(OVERLAY.LEGACY_PATHS - {OVERLAY.LEGACY_MAP}):
            raw = ('reviewed legacy Source: ' + path + '\n').encode()
            self.write(path, raw)
            before = self.legacy_before[path]
            legacy[path] = dict(before_mode='100644', before_blob=OVERLAY.blob_id(before),
                                before_sha256=OVERLAY.sha256(before), before_bytes=len(before),
                                mode='100644', blob=OVERLAY.blob_id(raw),
                                sha256=OVERLAY.sha256(raw), bytes=len(raw))
        self.derived_map = b'{"fixture": "exact derived current MAP"}\n'
        self.write(OVERLAY.LEGACY_MAP, self.derived_map)
        self.write(OVERLAY.SELF, PATH.read_bytes())
        self.git('add', '--all')
        self.git('commit', '-qm', 'Finite tooling fixture')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        self.patch = mock.patch.multiple(OVERLAY, BASE_HEAD=self.base, BASE_TREE=self.base_tree,
                                         ADDITIONS=rows, POLICY_SHA256=OVERLAY.sha256(OVERLAY.canonical(rows)),
                                         TRANSPORT=transport, TRANSPORT_POLICY_SHA256=OVERLAY.sha256(OVERLAY.canonical(transport)),
                                         LEGACY_REPLACEMENTS=legacy, LEGACY_POLICY_SHA256=OVERLAY.sha256(OVERLAY.canonical(legacy)))
        self.patch.start()
        self.addCleanup(self.patch.stop)
        # Isolated unit boundary fixture only: no actual tooling checkout or
        # legacy Source/native qualification is represented by this mock.
        def fixture_derived_gate(root, head, expected, additions, transport, rows):
            if (root / OVERLAY.LEGACY_MAP).read_bytes() != self.derived_map:
                raise RuntimeError('Fixture complete derived MAP equality rejected')
            self.assertEqual(root, self.root)
            self.assertEqual(head, self.head)
            self.assertEqual(len(expected), 2196)
            self.assertEqual(rows, legacy)
            return {'isolated_unit_boundary_fixture': True}
        self.legacy_gate_patch = mock.patch.object(OVERLAY, 'verify_legacy_epoch', side_effect=fixture_derived_gate)
        self.legacy_gate = self.legacy_gate_patch.start()
        self.addCleanup(self.legacy_gate_patch.stop)

    def git(self, *args):
        return subprocess.check_output(['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', '-C', str(self.root), *args], stderr=subprocess.PIPE)

    def write(self, path, raw):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        return target

    def check(self):
        return OVERLAY.verify_tooling_overlay(self.head, self.root)

    def test_complete_overlay_accepts_without_native_credit(self):
        receipt = self.check()
        self.assertEqual(receipt['source_paths'], 2196)
        self.assertEqual(receipt['execution_head'], self.head)
        self.assertEqual(receipt['proof_base_head'], self.base)
        self.assertTrue(receipt['all_lean_sources_unchanged'])
        self.assertFalse(receipt['native_qualification'])
        self.assertFalse(receipt['workflow_status_credit'])

    def test_unknown_tracked_addition_rejected(self):
        self.write('scripts/unreviewed.py', b'print("unreviewed")\n')
        self.git('add', '--all')
        self.git('commit', '-qm', 'Unreviewed addition')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_unknown_ignored_addition_rejected(self):
        self.write('.git/info/exclude', b'hidden.py\n')
        self.write('hidden.py', b'pass\n')
        with self.assertRaisesRegex(RuntimeError, 'Untracked tooling'):
            self.check()

    def test_committed_proof_change_rejected(self):
        self.write(self.proof, b'axiom fixture : False\n')
        self.git('add', '--all')
        self.git('commit', '-qm', 'Forbidden proof change')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_committed_base_mode_change_rejected(self):
        self.git('update-index', '--chmod=+x', self.proof)
        self.git('commit', '-qm', 'Forbidden mode change')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_special_physical_mode_rejected(self):
        target = self.root / self.proof
        target.chmod(target.stat().st_mode | stat.S_ISUID)
        with self.assertRaisesRegex(RuntimeError, 'physical mode/native blob'):
            self.check()

    def test_unreviewed_transport_change_rejected(self):
        self.write(OVERLAY.TRANSPORT_PATH, self.transport_after + b'jobs: altered-original-job\n')
        self.git('add', '--all')
        self.git('commit', '-qm', 'Forbidden dispatch body change')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_transport_inverse_must_recover_whole_original(self):
        bad = json.loads(json.dumps(OVERLAY.TRANSPORT))
        bad['ports'][0][0] = 'wrong original Source\n'
        with self.assertRaisesRegex(RuntimeError, 'Whole dispatch Source inverse'):
            OVERLAY.transport_inverse(self.transport_after, self.transport_before, bad)

    def test_dispatch_default_false_cannot_be_changed(self):
        bad = json.loads(json.dumps(OVERLAY.TRANSPORT))
        bad['ports'][0][1] = bad['ports'][0][1].replace('default: false', 'default: true')
        with mock.patch.multiple(OVERLAY, TRANSPORT=bad,
                                 TRANSPORT_POLICY_SHA256=OVERLAY.sha256(OVERLAY.canonical(bad))):
            with self.assertRaisesRegex(RuntimeError, 'Dispatch default/mode/append behavior'):
                self.check()

    def test_broker_requires_executable_native_mode(self):
        self.git('update-index', '--chmod=-x', 'scripts/point4_ci/command_broker.py')
        self.git('commit', '-qm', 'Forbidden broker mode removal')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_other_tool_cannot_gain_executable_native_mode(self):
        self.git('update-index', '--chmod=+x', 'scripts/point4_ci/identity.py')
        self.git('commit', '-qm', 'Forbidden extra executable')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_dirty_index_rejected(self):
        self.write(self.proof, b'-- dirty indexed proof\n')
        self.git('add', self.proof)
        with self.assertRaisesRegex(RuntimeError, 'index differs'):
            self.check()

    def test_self_physical_blob_change_rejected(self):
        self.write(OVERLAY.SELF, PATH.read_bytes() + b'\n# uncommitted mutation\n')
        with self.assertRaisesRegex(RuntimeError, 'physical mode/native blob'):
            self.check()

    def test_reviewed_tool_physical_change_rejected(self):
        self.write(next(iter(OVERLAY.OTHER_PATHS)), b'changed after commit\n')
        with self.assertRaisesRegex(RuntimeError, 'physical mode/native blob'):
            self.check()

    def test_source_symlink_rejected(self):
        target = self.root / self.proof
        raw = target.read_bytes()
        target.unlink()
        external = self.root.parent / (self.root.name + '-external')
        external.write_bytes(raw)
        self.addCleanup(external.unlink)
        target.symlink_to(external)
        with self.assertRaisesRegex(RuntimeError, 'Nonregular tooling input'):
            self.check()

    def test_source_directory_symlink_rejected(self):
        source = self.root / 'baseline'
        moved = self.root.parent / (self.root.name + '-moved')
        source.rename(moved)
        import shutil
        self.addCleanup(shutil.rmtree, moved)
        source.symlink_to(moved, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'Nonreal tooling input parent'):
            self.check()

    def test_wrong_external_head_rejected(self):
        with self.assertRaisesRegex(RuntimeError, 'Tooling HEAD drift'):
            OVERLAY.verify_tooling_overlay(self.base, self.root)

    def test_wrong_base_tree_rejected(self):
        with mock.patch.object(OVERLAY, 'BASE_TREE', '0' * 40):
            with self.assertRaisesRegex(RuntimeError, 'baseline tree drift'):
                self.check()

    def test_unfrozen_policy_rejected(self):
        with mock.patch.object(OVERLAY, 'ADDITIONS', None):
            with self.assertRaisesRegex(RuntimeError, 'Unfrozen tooling policy'):
                self.check()

    def test_policy_mutation_rejected(self):
        changed = json.loads(json.dumps(OVERLAY.ADDITIONS))
        changed[next(iter(changed))]['sha256'] = '0' * 64
        with mock.patch.object(OVERLAY, 'ADDITIONS', changed):
            with self.assertRaisesRegex(RuntimeError, 'policy mutation'):
                self.check()

    def test_git_environment_override_rejected(self):
        with mock.patch.dict(os.environ, {'GIT_INDEX_FILE': str(self.root / 'foreign-index')}):
            with self.assertRaisesRegex(RuntimeError, 'Git environment override'):
                self.check()


    def test_actual_legacy_boundary_is_required_once(self):
        receipt = self.check()
        self.legacy_gate.assert_called_once()
        self.assertTrue(receipt['legacy_epoch_complete_current_identity_verified'])
        self.assertFalse(receipt['legacy_helper_and_map_unchanged'])

    def test_legacy_boundary_failure_cannot_be_skipped(self):
        self.legacy_gate.side_effect = RuntimeError('Actual legacy verifier refused')
        with self.assertRaisesRegex(RuntimeError, 'Actual legacy verifier refused'):
            self.check()

    def test_committed_derived_map_tamper_rejected_by_required_gate(self):
        self.write(OVERLAY.LEGACY_MAP, b'{"fixture": "unreviewed MAP"}\n')
        self.git('add', OVERLAY.LEGACY_MAP)
        self.git('commit', '-qm', 'Fixture committed MAP tamper')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'derived MAP equality'):
            self.check()

    def test_committed_legacy_body_tamper_rejected(self):
        self.write(OVERLAY.LEGACY_HELPER, b'raise RuntimeError("unreviewed helper")\n')
        self.git('add', OVERLAY.LEGACY_HELPER)
        self.git('commit', '-qm', 'Fixture legacy Source tamper')
        self.head = self.git('rev-parse', 'HEAD').decode().strip()
        with self.assertRaisesRegex(RuntimeError, 'Unknown tracked'):
            self.check()

    def test_legacy_policy_sha_mutation_rejected(self):
        bad = json.loads(json.dumps(OVERLAY.LEGACY_REPLACEMENTS))
        bad[OVERLAY.LEGACY_HELPER]['sha256'] = '0' * 64
        with mock.patch.object(OVERLAY, 'LEGACY_REPLACEMENTS', bad):
            with self.assertRaisesRegex(RuntimeError, 'legacy epoch replacement policy mutation'):
                self.check()

    def test_legacy_original_sha_provenance_rejected(self):
        bad = json.loads(json.dumps(OVERLAY.LEGACY_REPLACEMENTS))
        bad[OVERLAY.LEGACY_HELPER]['before_sha256'] = '0' * 64
        with mock.patch.multiple(OVERLAY, LEGACY_REPLACEMENTS=bad,
                                 LEGACY_POLICY_SHA256=OVERLAY.sha256(OVERLAY.canonical(bad))):
            with self.assertRaisesRegex(RuntimeError, 'Original legacy whole Source'):
                self.check()


class BrokerModeGuardTests(unittest.TestCase):
    """Execute actual guard functions with finite index records and real lstat modes."""
    GUARDS = (
        'curvature/scripts/point4_weighted_hessian_release_guard.py',
        'curvature/scripts/point4_two_sided_heat_source_guard.py',
        'curvature/scripts/point4_c2_c0_metric_velocity_source_guard.py',
        'curvature/scripts/point4_hamilton_native_source_guard.py',
    )
    BROKER = 'scripts/point4_ci/command_broker.py'

    def functions(self, path):
        import ast
        import hashlib
        import re
        source = (PATH.parents[1] / path).read_bytes()
        names = {'check_inventory', 'check_mode', 'check_modes', 'check_inventory_sets',
                 'nul_records', 'nul_paths', 'git_blob_identity'}
        nodes = [n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name in names]
        self.assertEqual({n.name for n in nodes}, names)
        ns = dict(os=os, pathlib=__import__('pathlib'), stat=stat, re=re, hashlib=hashlib)
        exec(compile(ast.Module(body=nodes, type_ignores=[]), str(PATH.parents[1] / path), 'exec'), ns)
        return ns

    def run_case(self, path, name, actual, tracked, baseline, method='check_inventory'):
        ns = self.functions(path)
        with tempfile.TemporaryDirectory(prefix='point4-mode-guard-') as temp:
            root = Path(temp)
            target = root / name
            target.parent.mkdir(parents=True)
            data = b'finite actual physical source\n'
            target.write_bytes(data)
            target.chmod(actual)
            oid = ns['git_blob_identity'](data)
            records = (tracked + ' ' + oid + ' 0\t' + name).encode() + b'\0'
            def finite_git(*args):
                if args == ('ls-files', '--stage', '-z'):
                    return records
                self.assertEqual(args, ('ls-files', '-z', '--others'))
                return b''
            def exact_public(paths):
                self.assertEqual(set(paths), {name})
            ns.update(ROOT=root, git=finite_git, dependency_inventory=lambda: (set(), set()),
                      runtime_fingerprints=lambda deps: set(), generated_build_path=lambda p: False,
                      baseline_sources=lambda: dict(baseline), public_paths=lambda: {name},
                      runtime_path=lambda p: False, PROOFWIDGETS_FINGERPRINT='unused',
                      UNIT_FILE_SHA256={}, SELF_PATHS=set(), check_public_paths=exact_public)
            ns[method]()

    def test_current_broker0755_actual_inventory_and_weighted_modes(self):
        for path in self.GUARDS:
            with self.subTest(path=path):
                self.run_case(path, self.BROKER, 0o755, '100755', {})
        self.run_case(self.GUARDS[0], self.BROKER, 0o755, '100755', {}, 'check_modes')

    def test_broker0644_real_physical_rejected(self):
        for path in self.GUARDS:
            with self.subTest(path=path), self.assertRaisesRegex(AssertionError, 'Public executable-mode drift'):
                self.run_case(path, self.BROKER, 0o644, '100755', {})
        with self.assertRaisesRegex(AssertionError, 'Public executable-mode drift'):
            self.run_case(self.GUARDS[0], self.BROKER, 0o644, '100755', {}, 'check_modes')

    def test_broker0644_index_rejected(self):
        for path in self.GUARDS:
            with self.subTest(path=path), self.assertRaisesRegex(AssertionError, 'Tracked executable-mode drift'):
                self.run_case(path, self.BROKER, 0o755, '100644', {})

    def test_unknown_executable_rejected_by_actual_guards(self):
        for path in self.GUARDS:
            with self.subTest(path=path), self.assertRaisesRegex(AssertionError, 'Tracked executable-mode drift'):
                self.run_case(path, 'scripts/new_unknown.py', 0o755, '100755', {})
        with self.assertRaisesRegex(AssertionError, 'Public executable-mode drift'):
            self.run_case(self.GUARDS[0], 'scripts/new_unknown.py', 0o755, '100755', {}, 'check_modes')

    def test_inherited_baseline_mode_precedes_broker_exception(self):
        for path in self.GUARDS:
            with self.subTest(path=path):
                self.run_case(path, self.BROKER, 0o644, '100644', {self.BROKER: ('100644', 'fixture')})
                self.run_case(path, 'inherited/executable', 0o755, '100755', {'inherited/executable': ('100755', 'fixture')})
        self.run_case(self.GUARDS[0], self.BROKER, 0o644, '100644', {self.BROKER: ('100644', 'fixture')}, 'check_modes')

    def test_exact_mode_constructor_inverse_and_compiler_binding(self):
        import ast
        import hashlib
        helper = PATH.parents[1] / OVERLAY.LEGACY_HELPER
        tree = ast.parse(helper.read_bytes())
        literals = {}
        for node in tree.body:
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                try:
                    literals[node.targets[0].id] = ast.literal_eval(node.value)
                except (ValueError, TypeError):
                    pass
        names = {'curvature_tooling_policy_check', 'curvature_tooling_broker_mode_current',
                 'curvature_tooling_broker_mode_inverse'}
        nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
        ns = dict(literals, json=json, sha256=lambda data: hashlib.sha256(data).hexdigest())
        exec(compile(ast.Module(body=nodes, type_ignores=[]), str(helper), 'exec'), ns)
        forward = ns['curvature_tooling_broker_mode_current']
        inverse = ns['curvature_tooling_broker_mode_inverse']
        ports = ns['CURVATURE_TOOLING_POLICY']['broker_mode_ports']
        self.assertEqual(sum(map(len, ports.values())), 6)
        def functions(raw, filename):
            return {c.co_name: c for c in compile(raw, filename, 'exec').co_consts if isinstance(c, type((lambda: None).__code__))}
        for path in self.GUARDS:
            current = (PATH.parents[1] / path).read_bytes()
            previous = inverse(path, current)
            self.assertEqual(forward(path, previous), current)
            with self.assertRaisesRegex(AssertionError, 'inverse Source port drift'):
                inverse(path, previous)
            before, after = ports[path][0]
            with self.assertRaisesRegex(AssertionError, 'inverse Source port drift'):
                inverse(path, current + after.encode())
            actual_codes = functions(current, path)
            reference_codes = functions(forward(path, previous), path)
            old_codes = functions(previous, path)
            self.assertEqual(actual_codes['check_inventory'], reference_codes['check_inventory'])
            self.assertNotEqual(actual_codes['check_inventory'], old_codes['check_inventory'])
            if path != self.GUARDS[0]:
                self.assertEqual(actual_codes['check_modes'], old_codes['check_modes'])
        unchanged = b'def unrelated():\n    return 1\n'
        self.assertEqual(forward('unrelated.py', unchanged), unchanged)
        self.assertEqual(inverse('unrelated.py', unchanged), unchanged)


class VerifierLocalPureValueTests(unittest.TestCase):
    """Isolate real pure function wrappers; never execute production verify_current."""
    def setUp(self):
        import ast
        import contextlib
        import hashlib
        import re
        import threading
        helper = PATH.parents[1] / OVERLAY.LEGACY_HELPER
        tree = ast.parse(helper.read_bytes())
        ns = dict(hashlib=hashlib, re=re, pathlib=__import__('pathlib'), json=json,
                  os=os, contextlib=contextlib, _curvature_tooling_pure_threading=threading)
        for node in tree.body:
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                try:
                    ns[node.targets[0].id] = ast.literal_eval(node.value)
                except (ValueError, TypeError):
                    pass
        functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
        originals = [next(n for n in functions if n.name == name) for name in ('sha256', 'parse_tree')]
        exec(compile(ast.Module(body=originals, type_ignores=[]), str(helper), 'exec'), ns)
        self.calls = dict(sha=0, tree=0, verify=0)
        def counted(kind, function):
            def call(data):
                self.calls[kind] += 1
                return function(data)
            return call
        ns['_curvature_before_tooling_pure_sha256'] = counted('sha', ns['sha256'])
        ns['_curvature_before_tooling_pure_parse_tree'] = counted('tree', ns['parse_tree'])
        def full_verifier_boundary():
            self.calls['verify'] += 1
            return {'original_verifier_called': self.calls['verify']}
        ns['_curvature_before_tooling_pure_verify_current'] = full_verifier_boundary
        ns['_curvature_tooling_pure_owner'] = None
        selected = [n for n in functions if n.name.startswith('curvature_tooling_pure_')]
        selected += [next(n for n in functions if n.name == 'curvature_tooling_policy_check')]
        selected += [next(n for n in reversed(functions) if n.name == name)
                     for name in ('sha256', 'parse_tree', 'verify_current')]
        exec(compile(ast.Module(body=selected, type_ignores=[]), str(helper), 'exec'), ns)
        self.ns = ns

    def tree(self, count=1, prefix='source'):
        return b''.join(('100644 blob %040x\t%s%d\0' % (i + 1, prefix, i)).encode() for i in range(count))

    def test_same_bytes_reuse_value_without_dictionary_alias(self):
        with self.ns['curvature_tooling_pure_values']():
            before = dict(self.calls)
            self.assertEqual(self.ns['sha256'](b'new exact bytes'), self.ns['sha256'](bytes(bytearray(b'new exact bytes'))))
            self.assertEqual(self.calls['sha'] - before['sha'], 1)
            data = self.tree()
            first = self.ns['parse_tree'](data)
            first['injected'] = ('100755', '0' * 40)
            second = self.ns['parse_tree'](bytes(bytearray(data)))
            self.assertEqual(second, {'source0': ('100644', '%040x' % 1)})
            self.assertIsNot(first, second)
            second.clear()
            self.assertEqual(len(self.ns['parse_tree'](data)), 1)
            self.assertEqual(self.calls['tree'] - before['tree'], 1)

    def test_new_bytes_and_malformed_bytes_always_get_correct_behavior(self):
        with self.ns['curvature_tooling_pure_values']():
            self.assertNotEqual(self.ns['sha256'](b'one'), self.ns['sha256'](b'two'))
            self.assertNotEqual(self.ns['parse_tree'](self.tree(prefix='one')), self.ns['parse_tree'](self.tree(prefix='two')))
            before = self.calls['tree']
            for _ in range(2):
                with self.assertRaises(AssertionError):
                    self.ns['parse_tree'](b'incomplete')
            self.assertEqual(self.calls['tree'] - before, 2)
            self.assertNotIn(b'incomplete', self.ns['_curvature_tooling_pure_owner']['tree'])
            before = self.calls['sha']
            self.ns['sha256'](bytearray(b'mutable'))
            self.ns['sha256'](bytearray(b'mutable'))
            self.assertEqual(self.calls['sha'] - before, 2)

    def test_entry_bound_falls_back_and_keeps_existing_exact_hits(self):
        with self.ns['curvature_tooling_pure_values']():
            owner = self.ns['_curvature_tooling_pure_owner']
            for i in range(owner['limits']['entries']):
                self.ns['sha256'](('entry%d' % i).encode())
            self.assertEqual(owner['entries'], 256)
            before = self.calls['sha']
            self.ns['sha256'](b'overflow'); self.ns['sha256'](b'overflow')
            self.assertEqual(self.calls['sha'] - before, 2)
            before = self.calls['sha']
            self.ns['sha256'](b'entry0')
            self.assertEqual(self.calls['sha'], before)
            self.assertEqual(owner['entries'], 256)

    def test_key_size_and_total_key_byte_bounds_fall_back(self):
        with self.ns['curvature_tooling_pure_values']():
            owner = self.ns['_curvature_tooling_pure_owner']
            maximum = owner['limits']['key_bytes']
            oversized = b'x' * (maximum + 1)
            before = self.calls['sha']
            self.ns['sha256'](oversized); self.ns['sha256'](oversized)
            self.assertEqual(self.calls['sha'] - before, 2)
            self.assertEqual(owner['entries'], 0)
            del oversized
            for i in range(8):
                self.ns['sha256'](bytes([i]) * maximum)
            self.assertEqual(owner['key_bytes'], 64 * 1024**2)
            before = self.calls['sha']
            self.ns['sha256'](b'full'); self.ns['sha256'](b'full')
            self.assertEqual(self.calls['sha'] - before, 2)
            self.assertEqual(owner['key_bytes'], 64 * 1024**2)

    def test_per_tree_and_total_row_bounds_fall_back(self):
        with self.ns['curvature_tooling_pure_values']():
            owner = self.ns['_curvature_tooling_pure_owner']
            oversized = self.tree(4097)
            before = self.calls['tree']
            self.ns['parse_tree'](oversized); self.ns['parse_tree'](oversized)
            self.assertEqual(self.calls['tree'] - before, 2)
            self.assertEqual(owner['entries'], 0)
            for i in range(16):
                self.ns['parse_tree'](self.tree(4096, 'set%d-' % i))
            self.assertEqual(owner['tree_rows'], 65536)
            data = self.tree(1, 'overflow')
            before = self.calls['tree']
            self.ns['parse_tree'](data); self.ns['parse_tree'](data)
            self.assertEqual(self.calls['tree'] - before, 2)
            self.assertEqual(owner['tree_rows'], 65536)

    def test_exception_cleanup_and_fresh_invocation(self):
        owner = None
        with self.assertRaisesRegex(RuntimeError, 'original failure'):
            with self.ns['curvature_tooling_pure_values']():
                self.ns['sha256'](b'not retained across calls')
                owner = self.ns['_curvature_tooling_pure_owner']
                raise RuntimeError('original failure')
        self.assertIsNone(self.ns['_curvature_tooling_pure_owner'])
        self.assertEqual(owner['sha'], {})
        self.assertEqual(owner['tree'], {})
        self.assertEqual(owner['entries'], 0)
        with self.ns['curvature_tooling_pure_values']():
            before = self.calls['sha']
            self.ns['sha256'](b'not retained across calls')
            self.assertEqual(self.calls['sha'] - before, 1)
            self.assertIsNot(self.ns['_curvature_tooling_pure_owner'], owner)

    def test_nested_full_verifier_is_not_skipped_and_preserves_outer_owner(self):
        with self.ns['curvature_tooling_pure_values']():
            owner = self.ns['_curvature_tooling_pure_owner']
            self.ns['sha256'](b'outer')
            self.ns['verify_current'](); self.ns['verify_current']()
            self.assertEqual(self.calls['verify'], 2)
            self.assertIs(self.ns['_curvature_tooling_pure_owner'], owner)
            self.assertIn(b'outer', owner['sha'])
        self.assertIsNone(self.ns['_curvature_tooling_pure_owner'])
        def original_failure():
            raise RuntimeError('old verifier failure')
        self.ns['_curvature_before_tooling_pure_verify_current'] = original_failure
        with self.assertRaisesRegex(RuntimeError, 'old verifier failure'):
            self.ns['verify_current']()
        self.assertIsNone(self.ns['_curvature_tooling_pure_owner'])

    def test_foreign_thread_and_pid_bypass_memos_without_owner_replacement(self):
        import threading
        with self.ns['curvature_tooling_pure_values']():
            owner = self.ns['_curvature_tooling_pure_owner']
            errors = []
            def foreign():
                try:
                    self.ns['sha256'](b'foreign'); self.ns['sha256'](b'foreign')
                    self.ns['parse_tree'](self.tree()); self.ns['parse_tree'](self.tree())
                    self.ns['verify_current']()
                except BaseException as exc:
                    errors.append(exc)
            before = dict(self.calls)
            thread = threading.Thread(target=foreign)
            thread.start(); thread.join()
            self.assertEqual(errors, [])
            self.assertEqual(self.calls['sha'] - before['sha'], 2)
            self.assertEqual(self.calls['tree'] - before['tree'], 2)
            self.assertEqual(self.calls['verify'] - before['verify'], 1)
            self.assertIs(self.ns['_curvature_tooling_pure_owner'], owner)
            self.assertEqual(owner['entries'], 0)
            with mock.patch.object(os, 'getpid', return_value=-1):
                before = self.calls['sha']
                self.ns['sha256'](b'foreign pid'); self.ns['sha256'](b'foreign pid')
                self.assertEqual(self.calls['sha'] - before, 2)
            self.assertEqual(owner['entries'], 0)


class WeightedRuntimeFragmentSealTests(unittest.TestCase):
    """Actual check_current body with finite Source/index/files; no Git HEAD emulation."""
    WEIGHTED = 'curvature/scripts/point4_weighted_hessian_release_guard.py'
    BROKER = 'scripts/point4_ci/command_broker.py'
    BEFORE = '41e5e5e853d8dd79ead807f76124d5bdaec723548493a4b6540b5de90515b6c2'
    CURRENT = '019345bdc43d4eb227ee6b5810c8b03382940513c61b871a67f99019f2bdd0ff'

    def actual_current_fixture(self, stale=False, tamper=False, broker_mode=0o755):
        import ast
        import hashlib
        import sys
        import types
        source = (PATH.parents[1] / self.WEIGHTED).read_bytes()
        text = source.decode()
        if stale:
            before = "RUNTIME_INVENTORY_FRAGMENT_SHA256 = '" + self.CURRENT + "'"
            self.assertEqual(text.count(before), 1)
            text = text.replace(before, "RUNTIME_INVENTORY_FRAGMENT_SHA256 = '" + self.BEFORE + "'", 1)
        if tamper:
            self.assertEqual(text.count('\nLAKE_ROOTS ='), 1)
            text = text.replace('\nLAKE_ROOTS =', '\nLAKE_ROOTS = ', 1)
        ns = BrokerModeGuardTests.functions(self, self.WEIGHTED)
        names = {'check_current', 'check_public_paths', 'check_physical_lean'}
        nodes = [n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name in names]
        self.assertEqual({n.name for n in nodes}, names)
        exec(compile(ast.Module(body=nodes, type_ignores=[]), str(PATH.parents[1] / self.WEIGHTED), 'exec'), ns)
        with tempfile.TemporaryDirectory(prefix='point4-weighted-fragment-') as temp:
            root = Path(temp)
            workflow = '.github/workflows/finite.yml'
            meta = 'docs/finite-weighted.toml'
            lib = 'curvature/PoincareCurvature.lean'
            oldmeta = 'docs/finite-original.toml'
            regression = 'curvature/scripts/point4_closed_contract_regression.lean'
            files = {self.WEIGHTED: text.encode(), self.BROKER: b'finite broker bytes\n',
                     workflow: b'name: finite fixture\n', meta: b'finite weighted metadata\n',
                     oldmeta: b'finite historical metadata\n', lib: b'-- finite import fixture\n',
                     regression: b'-- finite Source test only\n' + b'fail_if_success exact @bad\n' * 12}
            for name, raw in files.items():
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
                target.chmod(broker_mode if name == self.BROKER else 0o644)
            staged = b''.join((('100755' if name == self.BROKER else '100644') + ' ' + ns['git_blob_identity'](raw) + ' 0\t' + name).encode() + b'\0' for name, raw in sorted(files.items()))
            def finite_git(*args):
                if args == ('ls-files', '--stage', '-z'):
                    return staged
                self.assertEqual(args, ('ls-files', '-z', '--others'))
                return b''
            def exact(actual, expected):
                self.assertEqual(actual, expected)
            # Explicit external semantic boundaries only. The actual failing
            # fragment check, inherited byte loop, complete inventory, physical
            # modes/blob checks and regression-count assertions all execute.
            historical = types.SimpleNamespace(LIBROOT=lib, METADATA=oldmeta,
                check_imports=lambda value: exact(value, files[lib]),
                check_metadata=lambda value: exact(value, files[oldmeta].decode()))
            ns.update(ROOT=root, git=finite_git, sha256=lambda value: hashlib.sha256(value).hexdigest(),
                      RUNTIME_INVENTORY_FRAGMENT_SHA256=self.BEFORE if stale else self.CURRENT,
                      expected_sources=lambda: {name: ('fixture', raw) for name, raw in files.items()},
                      public_paths=lambda: set(files), baseline_sources=lambda: {},
                      dependency_inventory=lambda: (set(), set()), runtime_fingerprints=lambda deps: set(),
                      generated_build_path=lambda name: False, runtime_path=lambda name: False,
                      PROOFWIDGETS_FINGERPRINT='unused', UNIT_FILE_SHA256={workflow: hashlib.sha256(files[workflow]).hexdigest()},
                      SELF_PATHS=set(), historical_c2=lambda: historical,
                      METADATA=meta, WORKFLOW=workflow,
                      check_metadata=lambda value, schema: exact((value, schema), (files[meta].decode(), None)),
                      parse_workflow=lambda value: exact(value, files[workflow].decode()),
                      source_transformations=lambda: {}, check_module_import_graph=lambda: {'finite_external_boundary': True},
                      BASE='finite_fixture_source_scope', adapters=lambda: [])
            with mock.patch.dict(sys.modules, {'point4_scan': types.SimpleNamespace(strip_comments=lambda value: value.splitlines())}):
                result = ns['check_current']()
            self.assertEqual(result['public_paths'], len(files))
            self.assertFalse(result['lean_verified'])
            self.assertEqual(result['point4'], 'OPEN')

    def test_actual_check_current_reproduces_stale_seal_failure(self):
        with self.assertRaisesRegex(AssertionError, 'Reviewed runtime inventory fragment changed'):
            self.actual_current_fixture(stale=True)

    def test_actual_check_current_accepts_exact_rebound_fragment(self):
        self.actual_current_fixture()

    def test_actual_check_current_rejects_one_fragment_byte_change(self):
        with self.assertRaisesRegex(AssertionError, 'Reviewed runtime inventory fragment changed'):
            self.actual_current_fixture(tamper=True)

    def test_actual_check_current_still_rejects_wrong_broker_physical_mode(self):
        with self.assertRaisesRegex(AssertionError, 'Public executable-mode drift'):
            self.actual_current_fixture(broker_mode=0o644)

if __name__ == '__main__':
    unittest.main(verbosity=2)
