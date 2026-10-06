"""Ordinary driver tests with finite fixtures; no Lean, Lake or workflow execution."""
from pathlib import Path
import ast, hashlib, json, signal, tempfile, types, unittest

HERE = Path(__file__).resolve().parent
SOURCE = (HERE / 'chart_port_ci.py').read_text()
TREE = ast.parse(SOURCE)
LIMIT = 6 * 1024 ** 3
PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'
COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'

def execute_nodes(nodes, namespace):
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(HERE / 'chart_port_ci.py'), 'exec'), namespace)

def function(name, namespace):
    execute_nodes([next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == name)], namespace)
    return namespace[name]

def digest(data):
    return hashlib.sha256(data).hexdigest()

class DriverControls(unittest.TestCase):
    def model(self, setup_only, *, memory=LIMIT, quota=200000, invalid_pin=False, reject_probe=False):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            pkg, evidence, prefix, src = [root / p for p in ('curvature', 'evidence', 'compiler', 'sources')]
            for p in (pkg, evidence, prefix / 'bin', src / 'Cache'):
                p.mkdir(parents=True, exist_ok=True)
            (prefix / 'bin/lean').write_bytes(b'fixture compiler identity')
            (src / 'Cache/Main.lean').write_bytes(b'module\n')
            (pkg / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
            dep = pkg / '.lake/packages/mathlib'
            dep.mkdir(parents=True)
            (pkg / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages',
                'packages': [{'type': 'git', 'name': 'mathlib', 'rev': PIN}]}))
            prov = pkg / 'third-party/differential-geometry/SOURCE-PROVENANCE.json'
            prov.parent.mkdir(parents=True)
            prov.write_text('{"mathlib_support_sources": []}')
            group = root / 'cgroup/bounded'
            group.mkdir(parents=True)
            for name, value in {'memory.max': memory, 'cpu.max': f'{quota} 100000', 'memory.peak': 4096}.items():
                (group / name).write_text(str(value))
            cgroup_info = root / 'self-cgroup'
            cgroup_info.write_text('0::/bounded\n')
            closure = []
            for i in range(71):
                name = 'ChartPort.ChartIdentityEvidence' if i == 70 else f'PoincareCurvature.Fixture{i}'
                path = 'curvature/' + name.replace('.', '/') + '.lean'
                p = root / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(b'fixture source, not compiled\n')
                closure.append(dict(module=name, path=path, sha256=digest(p.read_bytes())))
            admission = dict(closure=closure, external_mathlib_roots=[], physical_inventory={})
            trace = dict(run=[], compile=[], admit=[], affinity=[])
            receipt = dict(source_admission='PENDING', build='RUNNING', environment_setup='PENDING',
                           full_candidate_qualification='NOT_RUN', stages=[], point4='OPEN', general_targets='OPEN')
            def fake_path(value):
                if str(value) == '/proc/self/cgroup': return cgroup_info
                if str(value) == '/sys/fs/cgroup': return root / 'cgroup'
                return Path(value)
            def admit(*args):
                trace['admit'].append(args)
                return admission
            def run(argv, label, **kwargs):
                trace['run'].append((argv, label, kwargs))
                if label == 'compiler-version': return b'Lean (version 4.33.0, fixture)\n'
                if label == 'compiler-commit': return (COMMIT + '\n').encode()
                if label == 'compiler-prefix': return (str(prefix) + '\n').encode()
                if label == 'compiler-libdir': return (str(prefix / 'lib/lean') + '\n').encode()
                if label == 'lake-environment': return json.dumps({'LEAN_PATH': '', 'LEAN_SRC_PATH': str(src)}).encode()
                return b'fixture log'
            def git(argv):
                if 'rev-parse' in argv: return (('0' * 40 if invalid_pin else PIN) + '\n').encode()
                return b''
            def check_probe(data):
                if reject_probe: raise AssertionError('Rejected fixture probe')
                return {'fixture_probe': True}
            ns = dict(Path=fake_path, LIMIT=LIMIT, ROOT=root, PKG=pkg, EVIDENCE=evidence,
                args=types.SimpleNamespace(expected_sha='a' * 40, expected_tree='b' * 40, setup_only=setup_only),
                receipt=receipt, save=lambda: None, json=json, hashlib=hashlib,
                os=types.SimpleNamespace(sched_getaffinity=lambda _: {0, 1, 2},
                    sched_setaffinity=lambda _, cpus: trace['affinity'].append(cpus), environ={}, pathsep=';'),
                subprocess=types.SimpleNamespace(check_output=git), run=run, digest=digest, admit=admit,
                tree_entries=lambda *args: {}, artifact_status=lambda *args: {'ready': True},
                serial_compile=lambda *args: trace['compile'].append(args), imports=lambda _: [],
                check_probe=check_probe, time=types.SimpleNamespace(time=lambda: 0),
                resource=types.SimpleNamespace(RLIMIT_AS=1, setrlimit=lambda *a: self.fail('Virtual-address ceiling restored')))
            failure = None
            try:
                execute_nodes([next(n for n in TREE.body if isinstance(n, ast.ClassDef) and n.name == '_SetupOnlyComplete'),
                               next(n for n in TREE.body if isinstance(n, ast.Try))], ns)
            except BaseException as exc:
                failure = exc
            return receipt, trace, failure

    def test_setup_only_stops_before_cache_and_proofs(self):
        receipt, trace, failure = self.model(True)
        self.assertIsNone(failure)
        self.assertEqual(receipt['build'], 'SETUP_ONLY_PASSED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertEqual((receipt['fresh_local_modules'], receipt['fresh_probe']), (0, 0))
        self.assertEqual(len(trace['admit']), 2)
        self.assertEqual(trace['compile'], [])
        self.assertEqual([r[1] for r in trace['run']], ['compiler-version', 'compiler-commit', 'compiler-prefix', 'lake-environment'])
        self.assertEqual(trace['affinity'], [[0, 1]])

    def test_default_full_mode_requires_all_70_sources_and_probe(self):
        receipt, trace, failure = self.model(False)
        self.assertIsNone(failure)
        self.assertEqual(receipt['full_candidate_qualification'], 'PASSED')
        self.assertEqual(receipt['build'], 'PASSED')
        self.assertEqual(len(trace['compile']), 70)
        self.assertTrue(all(call[-1] is True for call in trace['compile']))
        self.assertEqual(len(trace['admit']), 3)
        probe = [r for r in trace['run'] if r[1] == 'full-type-proof-axiom-probe']
        self.assertEqual(len(probe), 1)
        self.assertEqual(probe[0][0][1:5], ['-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3'])

    def test_rejected_probe_cannot_qualify(self):
        receipt, trace, failure = self.model(False, reject_probe=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')

    def test_wrong_pin_cannot_pass_setup(self):
        receipt, trace, failure = self.model(True, invalid_pin=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(receipt['environment_setup'], 'PENDING')
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(trace['compile'], [])

    def test_wrong_memory_or_cpu_cgroup_denies_both_modes(self):
        for setup_only in (False, True):
            for params in ({'memory': LIMIT + 1}, {'quota': 200001}):
                with self.subTest(setup_only=setup_only, params=params):
                    receipt, trace, failure = self.model(setup_only, **params)
                    self.assertIsInstance(failure, AssertionError)
                    self.assertEqual(receipt['build'], 'FAILED')
                    self.assertEqual(trace['run'], [])

    def test_setup_workflow_has_separate_check_and_full_workflow_has_no_escape(self):
        repo = HERE.parents[1]
        full = (repo / '.github/workflows/point4-local-chart-connection.yml').read_text()
        setup = (repo / '.github/workflows/point4-local-chart-environment-setup.yml').read_text()
        self.assertIn('  chart_connection:', full)
        self.assertNotIn('--setup-only', full)
        self.assertIn('  pull_request:', full)
        self.assertIn('  chart_environment_setup:', setup)
        self.assertNotIn('  chart_connection:', setup)
        self.assertNotIn('  pull_request:', setup)
        self.assertIn('--setup-only', setup)
        for workflow in (full, setup):
            self.assertIn('  group: local-chart-connection-', workflow)
            for bound in ('MemoryMax=6442450944', 'MemorySwapMax=0', 'CPUQuota=200%',
                          'OOMPolicy=kill', 'KillMode=control-group', 'PYTHONDONTWRITEBYTECODE=1'):
                self.assertIn(bound, workflow)

class OwnedResourceMonitor(unittest.TestCase):
    def exercise(self, *, pages=1, extra_compiler=False, overdue=False, survivor=False):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); procdir = root / 'proc'; procdir.mkdir()
            def stat(pid, session, rss):
                fields = ['S'] + ['0'] * 50; fields[3] = str(session); fields[21] = str(rss)
                p = procdir / str(pid); p.mkdir(exist_ok=True)
                (p / 'stat').write_text(f'{pid} (fixture) ' + ' '.join(fields))
            stat(100, 100, pages)
            stat(200, 200, 10 ** 12)  # Unrelated process must never enter the owned sums.
            if extra_compiler or survivor: stat(101, 100, 1)
            events = []; receipt = {'stages': []}
            class Proc:
                pid = 100; returncode = 0; polls = 0
                def poll(self):
                    self.polls += 1
                    return None if self.polls == 1 else 0
                def wait(self, timeout):
                    events.append(('wait', timeout)); return 0
            def launch(*args, **kwargs):
                self.assertIs(kwargs['start_new_session'], True); return Proc()
            def kill(pid, sig):
                events.append(('kill', pid, sig)); stat(100, 0, 0)
                if (procdir / '101').exists() and not survivor: stat(101, 0, 0)
            clock = iter([0, 601, 602] if overdue else [0, 1, 2])
            ns = dict(Path=lambda p: procdir if str(p) == '/proc' else Path(p),
                EVIDENCE=root, PKG=root, LIMIT=LIMIT, receipt=receipt, save=lambda: None,
                subprocess=types.SimpleNamespace(Popen=launch), signal=types.SimpleNamespace(SIGKILL=9), digest=digest,
                time=types.SimpleNamespace(time=lambda: 0, monotonic=lambda: next(clock), sleep=lambda _: None),
                os=types.SimpleNamespace(sysconf=lambda _: 4096, killpg=kill,
                    readlink=lambda p: '/bin/lean' if extra_compiler or Path(p).parent.name == '100' else '/bin/child'))
            failure = None
            try: function('run', ns)(['fixture'], 'stage')
            except BaseException as exc: failure = exc
            return receipt['stages'][0], events, failure

    def test_unrelated_memory_is_excluded_and_owner_is_drained(self):
        stage, events, failure = self.exercise()
        self.assertIsNone(failure)
        self.assertEqual(stage['peak_rss_bytes'], 4096)
        self.assertTrue(stage['owner_reaped'])
        self.assertEqual(stage['remaining_session_pids'], [])
        self.assertIn(('kill', 100, 9), events)
        self.assertIn(('wait', 10), events)

    def test_owned_rss_parallel_compiler_and_deadline_are_still_rejected(self):
        for params, kind in (({'pages': LIMIT // 4096 + 1}, RuntimeError),
                             ({'extra_compiler': True}, RuntimeError), ({'overdue': True}, TimeoutError)):
            with self.subTest(params=params):
                stage, events, failure = self.exercise(**params)
                self.assertIsInstance(failure, kind)
                self.assertTrue(stage['owner_reaped'])
                self.assertIn(('kill', 100, 9), events)
                self.assertIn(('wait', 10), events)

    def test_surviving_owned_session_is_rejected(self):
        stage, events, failure = self.exercise(survivor=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(stage['remaining_session_pids'], [101])

    def test_serial_compiler_keeps_heap_thread_flags_and_companion_guard(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); source = root / 'Fixture/Source.lean'; source.parent.mkdir()
            source.write_text('module\n')
            calls = []
            ns = dict(Path=Path, run=lambda argv, *args, **kwargs: calls.append(argv),
                artifact_status=lambda *args: {'ready': False})
            with self.assertRaisesRegex(AssertionError, 'required Lean 4.33 import companions'):
                function('serial_compile', ns)('Fixture.Source', source, root / 'outputs', 'lean', {}, 'compile')
            self.assertEqual(calls[0][1:5], ['-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3'])

if __name__ == '__main__':
    unittest.main(verbosity=2)
