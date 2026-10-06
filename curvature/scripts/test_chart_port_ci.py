"""Ordinary driver tests with finite fixtures; no Lean, Lake or workflow execution."""
from pathlib import Path
import ast, hashlib, json, os, signal, tempfile, types, unittest
from unittest.mock import patch
import chart_port_candidate_check as admission

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


# Exact public documentation blob from the fixed Batteries pin. No code is loaded.
BATTERIES_README = (
    b'# Batteries\n'
    b'\n'
    b'The "batteries included" extended library for Lean 4. This is a collection of data structures and tactics intended for use by both computer-science applications and mathematics applications of Lean 4.\n'
    b'\n'
    b'# Using `batteries`\n'
    b'\n'
    b'To use `batteries` in your project, add the following to your `lakefile.lean`:\n'
    b'```lean\n'
    b'require "leanprover-community" / "batteries" @ git "main"\n'
    b'```\n'
    b'Or add the following to your `lakefile.toml`:\n'
    b'```toml\n'
    b'[[require]]\n'
    b'name = "batteries"\n'
    b'scope = "leanprover-community"\n'
    b'rev = "main"\n'
    b'```\n'
    b'\n'
    b"Additionally, please make sure that you're using the version of Lean that the current version of `batteries` expects. The easiest way to do this is to copy the [`lean-toolchain`](./lean-toolchain) file from this repository to your project. Once you've added the dependency declaration, the command `lake update` checks out the current version of `batteries` and writes it to the Lake manifest file. Don't run this command again unless you're prepared to potentially also update your Lean compiler version, as it will retrieve the latest version of dependencies and add them to the manifest.\n"
    b'\n'
    b'# Build instructions\n'
    b'\n'
    b'* Get the newest version of `elan`. If you already have installed a version of Lean, you can run\n'
    b'  ```sh\n'
    b'  elan self update\n'
    b'  ```\n'
    b'  If the above command fails, or if you need to install `elan`, run\n'
    b'  ```sh\n'
    b'  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh\n'
    b'  ```\n'
    b'  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).\n'
    b'* To build `batteries` run `lake build`.\n'
    b'* To build and run all tests, run `lake test`.\n'
    b'* To run the environment linter, run `lake lint`.\n'
    b'* If you added a new file, run the command `scripts/updateBatteries.sh` to update the imports.\n'
    b'\n'
    b'# Documentation\n'
    b'\n'
    b'You can generate `batteries` documentation with\n'
    b'\n'
    b'```sh\n'
    b'cd docs\n'
    b'lake build Batteries:docs\n'
    b'```\n'
    b'\n'
    b'The top-level HTML file will be located at `docs/doc/index.html`, though to actually expose the\n'
    b'documentation you need to run an HTTP server (e.g. `python3 -m http.server`) in the `docs/doc` directory.\n'
    b'\n'
    b'Note that documentation for the latest nightly of `batteries` is also available as part of [the Mathlib 4\n'
    b'documentation][mathlib4 docs].\n'
    b'\n'
    b'[mathlib4 docs]: https://leanprover-community.github.io/mathlib4_docs/Batteries.html\n'
    b'\n'
    b'# Contributing\n'
    b'\n'
    b'The first step to contribute is to create a fork of Batteries.\n'
    b'Then add your contributions to a branch of your fork and make a PR to Batteries.\n'
    b'Do not make your changes to the main branch of your fork, that may lead to complications on your end.\n'
    b'\n'
    b'Every pull request should have exactly one of the status labels `awaiting-review`, `awaiting-author`\n'
    b'or `WIP` (in progress).\n'
    b'To change the status label of a pull request, add a comment containing one of these options and\n'
    b'_nothing else_.\n'
    b'This will remove the previous label and replace it by the requested status label.\n'
    b'These labels are used for triage.\n'
    b'\n'
    b'One of the easiest ways to contribute is to find a missing proof and complete it. The\n'
    b'[`proof_wanted`](https://github.com/search?q=repo%3Aleanprover-community%2Fbatteries+language%3ALean+%2F^proof_wanted%2F&type=code)\n'
    b'declaration documents statements that have been identified as being useful, but that have not yet\n'
    b'been proven.\n'
    b'\n'
    b'### Mathlib Adaptations\n'
    b'\n'
    b'Batteries PRs often affect Mathlib, a key component of the Lean ecosystem.\n'
    b'When Batteries changes in a significant way, Mathlib must adapt promptly.\n'
    b'When necessary, Batteries contributors are expected to either create an adaptation PR on Mathlib, or ask for assistance for and to collaborate with this necessary process.\n'
    b'\n'
    b'Every Batteries PR has an automatically created [Mathlib Nightly Testing](https://github.com/leanprover-community/mathlib4-nightly-testing/) branch called `batteries-pr-testing-N` where `N` is the number of the Batteries PR.\n'
    b'This is a clone of Mathlib where the Batteries requirement points to the Batteries PR branch instead of the main branch.\n'
    b'Batteries uses this branch to check whether the Batteries PR needs Mathlib adaptations.\n'
    b'A tag `builds-mathlib` will be issued when this branch needs no adaptation; a tag `breaks-mathlib` will be issued when the branch does need an adaptation.\n'
    b'\n'
    b'The first step in creating an adaptation PR is to switch to the `batteries-pr-testing-N` branch and push changes to that branch until the Mathlib CI process works.\n'
    b'You may need to ask for write access to [Mathlib Nightly Testing](https://github.com/leanprover-community/mathlib4-nightly-testing/) to do that.\n'
    b'Changes to the Batteries PR will be integrated automatically as you work on this process.\n'
    b'Do not redirect the Batteries requirement to main until the Batteries PR is merged.\n'
    b'Please ask questions to Batteries and Mathlib maintainers if you run into issues with this process.\n'
    b'\n'
    b'When everything works, create an adaptation PR on Mathlib from the `batteries-pr-testing-N` branch.\n'
    b"You may need to ping a Mathlib maintainer to review the PR, ask if you don't know who to ping.\n"
    b"Once the Mathlib adaptation PR and the original Batteries PR have been reviewed and accepted, the Batteries PR will be merged first. Then, the Mathlib PR's lakefile needs to be repointed to the Batteries main branch: change the Batteries line to\n"
    b'```lean\n'
    b'require "leanprover-community" / "batteries" @ git "main"\n'
    b'```\n'
    b'Once CI once again checks out on Mathlib, the adaptation PR can be merged using the regular Mathlib process.\n'
)

class PinnedDependencyLinkControls(unittest.TestCase):
    def entries(self):
        path, link_blob, _, target, target_blob, _ = admission.BATTERIES_LINK
        return {path: ('120000', 'blob', link_blob), target: ('100644', 'blob', target_blob)}

    def catalog(self, entries=None, pin=None, dep=None):
        entries = self.entries() if entries is None else entries
        dep = admission.BATTERIES_ROOT if dep is None else dep
        with patch.object(admission, 'git', return_value=((pin or admission.BATTERIES_PIN)+'\n').encode()), \
             patch.object(admission, 'tree_entries', return_value=entries):
            return admission.dependency_links(Path('fixture'), {dep: entries})

    def test_catalog_binds_exact_public_pin_modes_blobs_and_documentation_bytes(self):
        self.assertEqual(admission.BATTERIES_PIN, '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d')
        self.assertEqual(admission.BATTERIES_LINK, ('docs/README.md', '32d46ee883b58d6a383eed06eb98f33aa6530ded',
            b'../README.md', 'README.md', '4cd48268d7a14d8f5867862c549534cac08ebd45', 5427))
        self.assertEqual(len(BATTERIES_README), 5427)
        self.assertEqual(hashlib.sha1(b'blob 5427\0'+BATTERIES_README).hexdigest(), admission.BATTERIES_LINK[4])
        self.assertEqual(set(self.catalog()), {admission.BATTERIES_ROOT+'/docs/README.md'})
        self.assertEqual(admission.dependency_links(Path('fixture'), {}), {})

    def test_wrong_pin_and_pinned_tree_inventory_are_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'pin differs'):
            self.catalog(pin='0'*40)
        with patch.object(admission, 'git', return_value=(admission.BATTERIES_PIN+'\n').encode()), \
             patch.object(admission, 'tree_entries', return_value={}):
            with self.assertRaisesRegex(AssertionError, 'inventory differs'):
                admission.dependency_links(Path('fixture'), {admission.BATTERIES_ROOT: self.entries()})

    def test_link_and_regular_target_declarations_are_exact(self):
        cases = []
        for path in ('docs/README.md', 'README.md'):
            for entry in [('100755', 'blob', self.entries()[path][2]),
                          (self.entries()[path][0], 'tree', self.entries()[path][2]),
                          (self.entries()[path][0], 'blob', '0'*40)]:
                entries = self.entries(); entries[path] = entry; cases.append(entries)
            entries = self.entries(); del entries[path]; cases.append(entries)
        entries = self.entries(); entries['README.md'] = self.entries()['docs/README.md']; cases.append(entries)
        for entries in cases:
            with self.subTest(entries=entries), self.assertRaises(AssertionError):
                self.catalog(entries)

    def test_additional_code_documentation_or_other_package_links_are_rejected(self):
        for name in ('Batteries/Fixture.lean', 'docs/OTHER.md'):
            entries = self.entries(); entries[name] = entries['docs/README.md']
            with self.subTest(name=name), self.assertRaisesRegex(AssertionError, 'catalog differs'):
                self.catalog(entries)
        with self.assertRaisesRegex(AssertionError, 'Undeclared dependency link'):
            self.catalog(dep='curvature/.lake/packages/other')

    def exercise(self, *, raw=b'../README.md', target_data=BATTERIES_README, virtual=True,
                 omit_link=False, omit_target=False, extra_link=None, target_link=False,
                 public_link=False, regular_link=False):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); dep = root/admission.BATTERIES_ROOT
            (dep/'docs').mkdir(parents=True)
            link = dep/'docs/README.md'; target = dep/'README.md'
            if not omit_target: target.write_bytes(target_data)
            if not omit_link:
                if virtual or regular_link: link.write_bytes(b'finite placeholder, never followed')
                else: os.symlink(raw, os.fsencode(link))
            public = {}
            extra = root/extra_link if extra_link else None
            if extra:
                extra.parent.mkdir(parents=True, exist_ok=True)
                extra.write_bytes(b'finite placeholder, never followed')
                if public_link: public[extra_link] = self.entries()['docs/README.md']
            virtual_paths = ({link} if virtual and not omit_link and not regular_link else set())
            if target_link and not omit_target: virtual_paths.add(target)
            if extra: virtual_paths.add(extra)
            real_scandir = os.scandir
            def scan(directory):
                items = list(real_scandir(directory))
                return [types.SimpleNamespace(path=i.path, is_symlink=lambda: True)
                        if Path(i.path) in virtual_paths else i for i in items]
            reads = []
            def readlink(path):
                self.assertIsInstance(path, bytes)
                self.assertEqual(path, os.fsencode(link))
                reads.append(path); return raw
            with patch.object(admission, 'configuration_outputs', return_value=set()), \
                 patch.object(admission, 'git', return_value=(admission.BATTERIES_PIN+'\n').encode()), \
                 patch.object(admission, 'tree_entries', return_value=self.entries()), \
                 patch.object(admission.os, 'scandir', side_effect=scan):
                if virtual:
                    with patch.object(admission.os, 'readlink', side_effect=readlink):
                        result = admission.physical_inventory(root, public, {admission.BATTERIES_ROOT: self.entries()})
                    self.assertEqual(len(reads), 1)
                else:
                    result = admission.physical_inventory(root, public, {admission.BATTERIES_ROOT: self.entries()})
            return result

    def test_finite_physical_link_is_accounted_with_raw_and_regular_target_identities(self):
        receipt = self.exercise()
        self.assertEqual(receipt['dependency_files'], 2)
        self.assertEqual(receipt['declared_build_outputs'], [])
        self.assertTrue(receipt['full_physical_inventory_checked'])
        self.assertFalse(receipt['local_project_cache_admitted'])
        self.assertEqual(receipt['declared_source_links'], [dict(path=admission.BATTERIES_ROOT+'/docs/README.md',
            pin=admission.BATTERIES_PIN, link_blob=admission.BATTERIES_LINK[1], raw_bytes=12,
            raw_sha256=digest(b'../README.md'), target=admission.BATTERIES_ROOT+'/README.md',
            target_blob=admission.BATTERIES_LINK[4])])

    def test_changed_raw_link_text_and_target_documentation_are_rejected(self):
        for raw in (b'../README.md\n', b'../OTHER.md', b'../../README.md', b'/README.md'):
            with self.subTest(raw=raw), self.assertRaisesRegex(AssertionError, 'link text differs'):
                self.exercise(raw=raw)
        for data in (b'changed documentation', b'!'+BATTERIES_README[1:]):
            with self.subTest(size=len(data)), self.assertRaises(AssertionError):
                self.exercise(target_data=data)

    def test_missing_link_target_and_regularized_link_are_rejected(self):
        for options in ({'omit_link': True}, {'omit_target': True}, {'regular_link': True}, {'target_link': True}):
            with self.subTest(options=options), self.assertRaises(AssertionError):
                self.exercise(**options)

    def test_undeclared_public_and_code_physical_links_are_rejected(self):
        for options in ({'extra_link': 'curvature/Fixture.lean', 'public_link': True},
                        {'extra_link': admission.BATTERIES_ROOT+'/Batteries/Fixture.lean'},
                        {'extra_link': admission.BATTERIES_ROOT+'/docs/OTHER.md'}):
            with self.subTest(options=options), self.assertRaisesRegex(AssertionError, 'Physical symlink|Unexpected physical directory'):
                self.exercise(**options)

    def test_identity_git_reads_disable_replace_objects_per_command(self):
        with patch.object(admission.subprocess, 'check_output', return_value=b'identity') as read:
            self.assertEqual(admission.git(Path('fixture'), 'rev-parse', 'HEAD'), b'identity')
        read.assert_called_once_with(['git', '--no-replace-objects', '-C', 'fixture', 'rev-parse', 'HEAD'])
        for node in ast.walk(TREE):
            if isinstance(node, ast.List) and node.elts and isinstance(node.elts[0], ast.Constant) and node.elts[0].value == 'git':
                self.assertEqual(node.elts[1].value, '--no-replace-objects')

    @unittest.skipUnless(os.name == 'posix', 'Genuine Unix symlink behavior UNRUN on Windows; no link-creation workaround')
    def test_genuine_unix_link_and_raw_bytes(self):
        self.assertEqual(len(self.exercise(virtual=False)['declared_source_links']), 1)
        with self.assertRaisesRegex(AssertionError, 'link text differs'):
            self.exercise(virtual=False, raw=b'../README.md\n')

if __name__ == '__main__':
    unittest.main(verbosity=2)
