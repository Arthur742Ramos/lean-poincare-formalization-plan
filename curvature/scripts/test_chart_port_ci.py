"""Ordinary driver tests with finite fixtures; no Lean, Lake or workflow execution."""
from pathlib import Path
import ast, hashlib, io, json, os, signal, stat, tempfile, types, unittest
from unittest.mock import patch
import chart_port_candidate_check as admission

HERE = Path(__file__).resolve().parent
SOURCE = (HERE / 'chart_port_ci.py').read_text()
TREE = ast.parse(SOURCE)
LIMIT = 6 * 1024 ** 3
PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'
COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
PINNED_LOGIC_SOURCE = b'/-\nCopyright (c) 2014 Microsoft Corporation. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro\n-/\nmodule\n\npublic import Batteries.Tactic.Alias\n\n@[expose] public section\n\ninstance {f : \xce\xb1 \xe2\x86\x92 \xce\xb2} [DecidablePred p] : DecidablePred (p \xe2\x88\x98 f) :=\n  inferInstanceAs <| DecidablePred fun x => p (f x)\n\n/-! ## id -/\n\ntheorem Function.id_def : @id \xce\xb1 = fun x => x := rfl\n\n/-! ## decidable -/\n\nprotected alias \xe2\x9f\xa8Decidable.exists_not_of_not_forall, _\xe2\x9f\xa9 := Decidable.not_forall\n\n/-! ## classical logic -/\n\nnamespace Classical\n\nalias \xe2\x9f\xa8exists_not_of_not_forall, _\xe2\x9f\xa9 := not_forall\n\nend Classical\n\n/-! ## equality -/\n\ntheorem heq_iff_eq {a b : \xce\xb1} : a \xe2\x89\x8d b \xe2\x86\x94 a = b := \xe2\x9f\xa8eq_of_heq, heq_of_eq\xe2\x9f\xa9\n\n@[simp] theorem eq_rec_constant {\xce\xb1 : Sort _} {a a\' : \xce\xb1} {\xce\xb2 : Sort _} (y : \xce\xb2) (h : a = a\') :\n    (@Eq.rec \xce\xb1 a (fun _ _ => \xce\xb2) y a\' h) = y := by cases h; rfl\n\ntheorem congrArg\xe2\x82\x82 (f : \xce\xb1 \xe2\x86\x92 \xce\xb2 \xe2\x86\x92 \xce\xb3) {x x\' : \xce\xb1} {y y\' : \xce\xb2}\n    (hx : x = x\') (hy : y = y\') : f x y = f x\' y\' := by subst hx hy; rfl\n\ntheorem congrFun\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) :\n    f a b = g a b :=\n  congrFun (congrFun h _) _\n\ntheorem congrFun\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n      {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) (c : \xce\xb3 a b) :\n    f a b c = g a b c :=\n  congrFun\xe2\x82\x82 (congrFun h _) _ _\n\ntheorem funext\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : \xe2\x88\x80 a b, f a b = g a b) : f = g :=\n  funext fun _ => funext <| h _\n\ntheorem funext\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : \xe2\x88\x80 a b c, f a b c = g a b c) : f = g :=\n  funext fun _ => funext\xe2\x82\x82 <| h _\n\nprotected theorem Eq.congr (h\xe2\x82\x81 : x\xe2\x82\x81 = y\xe2\x82\x81) (h\xe2\x82\x82 : x\xe2\x82\x82 = y\xe2\x82\x82) : x\xe2\x82\x81 = x\xe2\x82\x82 \xe2\x86\x94 y\xe2\x82\x81 = y\xe2\x82\x82 := by\n  subst h\xe2\x82\x81; subst h\xe2\x82\x82; rfl\n\ntheorem Eq.congr_left {x y z : \xce\xb1} (h : x = y) : x = z \xe2\x86\x94 y = z := by rw [h]\n\ntheorem Eq.congr_right {x y z : \xce\xb1} (h : x = y) : z = x \xe2\x86\x94 z = y := by rw [h]\n\nalias congr_arg := congrArg\nalias congr_arg\xe2\x82\x82 := congrArg\xe2\x82\x82\nalias congr_fun := congrFun\nalias congr_fun\xe2\x82\x82 := congrFun\xe2\x82\x82\nalias congr_fun\xe2\x82\x83 := congrFun\xe2\x82\x83\n\ntheorem heq_of_cast_eq : \xe2\x88\x80 (e : \xce\xb1 = \xce\xb2) (_ : cast e a = a\'), a \xe2\x89\x8d a\'\n  | rfl, rfl => .rfl\n\ntheorem cast_eq_iff_heq : cast e a = a\' \xe2\x86\x94 a \xe2\x89\x8d a\' :=\n  \xe2\x9f\xa8heq_of_cast_eq _, fun h => by cases h; rfl\xe2\x9f\xa9\n\ntheorem eqRec_eq_cast {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') :\n    @Eq.rec \xce\xb1 a motive x a\' e = cast (e \xe2\x96\xb8 rfl) x := by\n  subst e; rfl\n\n--Porting note: new theorem. More general version of `eqRec_heq`\ntheorem eqRec_heq_self {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') : @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d x := by\n  subst e; rfl\n\n@[deprecated eqRec_heq_iff (since := "12-07-2026")]\ntheorem eqRec_heq_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d y \xe2\x86\x94 x \xe2\x89\x8d y := by\n  subst e; rfl\n\n\n@[deprecated heq_eqRec_iff (since := "12-07-2026")]\ntheorem heq_eqRec_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    y \xe2\x89\x8d @Eq.rec \xce\xb1 a motive x a\' e \xe2\x86\x94 y \xe2\x89\x8d x := by\n  subst e; rfl\n\n/-! ## miscellaneous -/\n\n@[simp] theorem not_nonempty_empty  : \xc2\xacNonempty Empty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n@[simp] theorem not_nonempty_pempty : \xc2\xacNonempty PEmpty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n\n-- TODO(Mario): profile first, this is a dangerous instance\n-- instance (priority := 10) {\xce\xb1} [Subsingleton \xce\xb1] : DecidableEq \xce\xb1\n--   | a, b => isTrue (Subsingleton.elim a b)\n\n-- TODO(Mario): profile adding `@[simp]` to `eq_iff_true_of_subsingleton`\n\n/-- If all points are equal to a given point `x`, then `\xce\xb1` is a subsingleton. -/\ntheorem subsingleton_of_forall_eq (x : \xce\xb1) (h : \xe2\x88\x80 y, y = x) : Subsingleton \xce\xb1 :=\n  \xe2\x9f\xa8fun a b => h a \xe2\x96\xb8 h b \xe2\x96\xb8 rfl\xe2\x9f\xa9\n\ntheorem subsingleton_iff_forall_eq (x : \xce\xb1) : Subsingleton \xce\xb1 \xe2\x86\x94 \xe2\x88\x80 y, y = x :=\n  \xe2\x9f\xa8fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x\xe2\x9f\xa9\n\ntheorem congr_eqRec {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} (f : (x : \xce\xb1) \xe2\x86\x92 \xce\xb2 x \xe2\x86\x92 \xce\xb3) (h : x = x\') (y : \xce\xb2 x) :\n  f x\' (Eq.rec y h) = f x y := by cases h; rfl\n'

def execute_nodes(nodes, namespace):
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(HERE / 'chart_port_ci.py'), 'exec'), namespace)

def function(name, namespace):
    execute_nodes([next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == name)], namespace)
    return namespace[name]

def digest(data):
    return hashlib.sha256(data).hexdigest()

class DriverControls(unittest.TestCase):
    def model(self, setup_only, *, memory=LIMIT, quota=200000, invalid_pin=False, reject_probe=False, reject_configured=False, missing_extension_field=None, missing_extension_contract=False, short_extension=False, changed_extension_source=False, reject_extension_probe=False):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            pkg, evidence, prefix, src = [root / p for p in ('curvature', 'evidence', 'compiler', 'sources')]
            for p in (pkg, evidence, prefix / 'bin', src / 'Cache'):
                p.mkdir(parents=True, exist_ok=True)
            (prefix / 'bin/lean').write_bytes(b'fixture compiler identity')
            (src / 'Cache/Main.lean').write_bytes(b'module\n')
            batteries = pkg / '.lake/packages/batteries'
            logic = batteries / 'Batteries/Logic.lean'
            logic.parent.mkdir(parents=True)
            logic.write_bytes(PINNED_LOGIC_SOURCE)
            (src / 'Mathlib').mkdir()
            (src / 'Mathlib/Fixture.lean').write_bytes(b'finite external source, never compiled\n')
            (pkg / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
            dep = pkg / '.lake/packages/mathlib'
            dep.mkdir(parents=True)
            (pkg / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages',
                'packages': [{'type': 'git', 'name': 'mathlib', 'rev': PIN},
                             {'type': 'git', 'name': 'batteries', 'rev': '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d'}]}))
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
            extension_closure = []
            extension_contracts = []
            for i in range(23):
                name = f'ChartPort.ExtensionFixture{i}'
                path = 'curvature/' + name.replace('.', '/') + '.lean'
                p = root / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(b'extension fixture source, not compiled\n')
                role = 'mathematical source' if i < 13 else 'probe'
                row = dict(module=name, path=path, sha256=digest(p.read_bytes()), role=role)
                extension_closure.append(row)
                if role == 'probe':
                    extension_contracts.append(dict(module=name, source_sha256=row['sha256']))
            if short_extension: extension_closure.pop()
            if missing_extension_contract: extension_contracts.pop()
            if changed_extension_source:
                (root / extension_closure[0]['path']).write_bytes(b'changed extension fixture source\n')
            admission = dict(closure=closure, external_mathlib_roots=['Mathlib.Fixture'], physical_inventory={},
                extension_closure=extension_closure, extension_probe_contracts=extension_contracts)
            if missing_extension_field is not None: del admission[missing_extension_field]
            trace = dict(run=[], compile=[], extension_compile=[], extension_probe=[], admit=[], affinity=[], roots=[], root_receipt_written_before_admit=False)
            receipt = dict(source_admission='PENDING', build='RUNNING', environment_setup='PENDING',
                           full_candidate_qualification='NOT_RUN', stages=[], point4='OPEN', general_targets='OPEN')
            def fake_path(value):
                if str(value) == '/proc/self/cgroup': return cgroup_info
                if str(value) == '/sys/fs/cgroup': return root / 'cgroup'
                return Path(value)
            def admit(*args):
                trace['admit'].append(args)
                if len(args) == 4:
                    trace['root_receipt_written_before_admit'] = (evidence / 'package-root-relationships.json').is_file()
                    if reject_configured: raise AssertionError('Finite configured admission rejection')
                return admission
            def run(argv, label, **kwargs):
                trace['run'].append((argv, label, kwargs))
                if label == 'compiler-version': return b'Lean (version 4.33.0, fixture)\n'
                if label == 'compiler-commit': return (COMMIT + '\n').encode()
                if label == 'compiler-prefix': return (str(prefix) + '\n').encode()
                if label == 'compiler-libdir': return (str(prefix / 'lib/lean') + '\n').encode()
                if label == 'lake-environment': return json.dumps({'LEAN_PATH': '', 'LEAN_SRC_PATH': os.pathsep.join((str(src), str(batteries)))}).encode()
                return b'fixture log'
            def git(argv):
                if 'rev-parse' in argv:
                    if argv[-1] == 'HEAD:Batteries/Logic.lean':
                        data = logic.read_bytes()
                        return (hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() + '\n').encode()
                    pin = '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d' if str(batteries) in argv else PIN
                    return (('0' * 40 if invalid_pin else pin) + '\n').encode()
                return b''
            def roots(*args):
                trace['roots'].append(args)
                return {'diagnostic_only': True, 'root_link_exceptions_granted': False}
            def check_probe(data):
                if reject_probe: raise AssertionError('Rejected fixture probe')
                return {'fixture_probe': True}
            def serial_compile(*args):
                target = 'extension_compile' if args[5].startswith('ricci-extension-local-') else 'compile'
                trace[target].append(args)
            def check_extension_probe(data, contract):
                self.assertEqual(data, b'fixture log')
                self.assertEqual(contract['source_sha256'], next(row['sha256'] for row in extension_closure if row['module'] == contract['module']))
                trace['extension_probe'].append(contract['module'])
                if reject_extension_probe: raise AssertionError('Rejected finite extension probe')
                return {'fixture_extension_probe': contract['module']}
            ns = dict(Path=fake_path, LIMIT=LIMIT, ROOT=root, PKG=pkg, EVIDENCE=evidence,
                args=types.SimpleNamespace(expected_sha='a' * 40, expected_tree='b' * 40, setup_only=setup_only),
                receipt=receipt, save=lambda: None, json=json, hashlib=hashlib,
                os=types.SimpleNamespace(sched_getaffinity=lambda _: {0, 1, 2},
                    sched_setaffinity=lambda _, cpus: trace['affinity'].append(cpus), environ={}, pathsep=os.pathsep),
                subprocess=types.SimpleNamespace(check_output=git), run=run, digest=digest, admit=admit,
                tree_entries=lambda *args: {}, package_root_relationships=roots,
                pinned_cache_query_context=lambda mathlib,names: dict(finite_synthetic_source_context=True,
                    package_root=str(mathlib),admitted_roots=list(names)),
                compiler_run=lambda argv,label,source,module,env=None: run(argv,label,env=env), artifact_status=lambda *args: {'ready': True},
                serial_compile=serial_compile, imports=lambda _: [],
                check_probe=check_probe, check_ricci_extension_probe=check_extension_probe, time=types.SimpleNamespace(time=lambda: 0),
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

    def test_root_receipt_is_saved_before_configured_admission_failure(self):
        receipt, trace, failure = self.model(True, reject_configured=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertTrue(trace['root_receipt_written_before_admit'])
        self.assertEqual(len(trace['roots']), 1)
        self.assertEqual(len(trace['admit']), 2)
        self.assertEqual(trace['compile'], [])
        self.assertIn('package_root_relationships_sha256', receipt)

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

    def test_extension_model_requires_all_13_sources_and10_probes(self):
        receipt, trace, failure = self.model(False)
        self.assertIsNone(failure)
        self.assertEqual(len(trace['compile']), 70)
        self.assertEqual(len(trace['extension_compile']), 13)
        self.assertTrue(all(call[-1] is True for call in trace['extension_compile']))
        self.assertEqual(len(trace['extension_probe']), 10)
        self.assertEqual(len(set(trace['extension_probe'])), 10)
        self.assertEqual(receipt['legacy_geometric_gate'], 'PASSED')
        self.assertEqual(receipt['ricci_extension_gate'], 'PASSED')
        self.assertEqual((receipt['fresh_local_modules'], receipt['fresh_probe']), (70, 1))
        self.assertEqual((receipt['fresh_extension_modules'], receipt['fresh_extension_probes']), (13, 10))
        self.assertEqual((receipt['fresh_combined_modules'], receipt['fresh_combined_probes']), (83, 11))
        self.assertEqual(receipt['admitted_local_modules'], 94)
        self.assertEqual(receipt['full_candidate_qualification'], 'PASSED')
        probes = [row for row in trace['run'] if row[1].startswith('ricci-extension-probe-')]
        self.assertEqual(len(probes), 10)
        self.assertTrue(all(row[0][1:5] == ['-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3'] for row in probes))

    def test_missing_extension_schema_fields_cannot_qualify(self):
        for field in ('extension_probe_contracts', 'extension_closure'):
            with self.subTest(field=field):
                receipt, trace, failure = self.model(False, missing_extension_field=field)
                self.assertIsInstance(failure, KeyError)
                self.assertEqual(failure.args, (field,))
                self.assertEqual(len(trace['compile']), 70)
                self.assertEqual(trace['extension_compile'], [])
                self.assertEqual(trace['extension_probe'], [])
                self.assertEqual(receipt['build'], 'FAILED')
                self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
                self.assertNotEqual(receipt['ricci_extension_gate'], 'PASSED')

    def test_missing_extension_contract_cannot_qualify(self):
        receipt, trace, failure = self.model(False, missing_extension_contract=True)
        self.assertIsInstance(failure, KeyError)
        self.assertEqual(len(trace['extension_compile']), 13)
        self.assertEqual(len(trace['extension_probe']), 9)
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertNotEqual(receipt['ricci_extension_gate'], 'PASSED')

    def test_incomplete_extension_counts_cannot_qualify(self):
        receipt, trace, failure = self.model(False, short_extension=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(len(trace['extension_compile']), 13)
        self.assertEqual(len(trace['extension_probe']), 9)
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertNotEqual(receipt['ricci_extension_gate'], 'PASSED')

    def test_changed_extension_source_cannot_qualify(self):
        receipt, trace, failure = self.model(False, changed_extension_source=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(len(trace['compile']), 70)
        self.assertEqual(trace['extension_compile'], [])
        self.assertEqual(trace['extension_probe'], [])
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')

    def test_rejected_extension_probe_cannot_qualify(self):
        receipt, trace, failure = self.model(False, reject_extension_probe=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(str(failure), 'Rejected finite extension probe')
        self.assertEqual(len(trace['extension_compile']), 13)
        self.assertEqual(len(trace['extension_probe']), 1)
        self.assertEqual(receipt['build'], 'FAILED')
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertNotEqual(receipt['ricci_extension_gate'], 'PASSED')

    def test_setup_only_runs_no_extension_stage(self):
        receipt, trace, failure = self.model(True)
        self.assertIsNone(failure)
        self.assertEqual(trace['extension_compile'], [])
        self.assertEqual(trace['extension_probe'], [])
        self.assertEqual(receipt['full_candidate_qualification'], 'NOT_RUN')

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
            function('owned_process_identity', ns)
            function('is_exact_official_prefix_query', ns)
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
            ns = dict(Path=Path, compiler_run=lambda argv, *args, **kwargs: calls.append(argv),
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


# Authenticated archived benchmark targets are finite byte fixtures, never executed.
BENCH_LEAN = (
    b'#!/usr/bin/env python3\n'
    b'\n'
    b'import argparse\n'
    b'import json\n'
    b'import os\n'
    b'import re\n'
    b'import subprocess\n'
    b'import sys\n'
    b'from pathlib import Path\n'
    b'\n'
    b'# Global paths\n'
    b'BENCH_DIR = Path(os.environ["BENCH_DIR"])\n'
    b'WRAPPER_OUT = Path(os.environ["WRAPPER_OUT"])\n'
    b'WRAPPER_PREFIX = Path(os.environ["WRAPPER_PREFIX"])\n'
    b'\n'
    b'# Other config\n'
    b'BENCHMARK = "build"\n'
    b'\n'
    b'sys.path.append(str(BENCH_DIR))\n'
    b'import measure  # noqa: E402\n'
    b'\n'
    b'\n'
    b'def save_measurement(metric: str, value: float, unit: str | None = None) -> None:\n'
    b'    data = {"metric": metric, "value": value}\n'
    b'    if unit is not None:\n'
    b'        data["unit"] = unit\n'
    b'    with open(WRAPPER_OUT, "a") as f:\n'
    b'        f.write(f"{json.dumps(data)}\\n")\n'
    b'\n'
    b'\n'
    b'def run(*command: str) -> None:\n'
    b'    result = subprocess.run(command)\n'
    b'    if result.returncode != 0:\n'
    b'        sys.exit(result.returncode)\n'
    b'\n'
    b'\n'
    b'def get_module(setup: Path) -> str:\n'
    b'    with open(setup) as f:\n'
    b'        return json.load(f)["name"]\n'
    b'\n'
    b'\n'
    b'def count_lines(module: str, path: Path) -> None:\n'
    b'    with open(path) as f:\n'
    b'        lines = sum(1 for _ in f)\n'
    b'    save_measurement(f"{BENCHMARK}/module/{module}//lines", lines)\n'
    b'\n'
    b'\n'
    b'def run_lean(module: str) -> None:\n'
    b'    _, stderr = measure.main(\n'
    b'        cmd=["lean", "--profile", "-Dprofiler.threshold=9999999", *sys.argv[1:]],\n'
    b'        output=WRAPPER_OUT,\n'
    b'        topics=[f"{BENCHMARK}/module/{module}"],\n'
    b'        metrics={"instructions"},\n'
    b'        append=True,\n'
    b'        capture=True,\n'
    b'    )\n'
    b'\n'
    b'    # Output of `lean --profile`\n'
    b'    # See timeit.cpp for the time format\n'
    b'    for line in stderr.splitlines():\n'
    b'        if match := re.fullmatch(r"\\t(.*) ([\\d.]+)(m?s)", line):\n'
    b'            name = match.group(1)\n'
    b'            seconds = float(match.group(2))\n'
    b'            if match.group(3) == "ms":\n'
    b'                seconds = seconds / 1000\n'
    b'            save_measurement(f"{BENCHMARK}/profile/{name}//wall-clock", seconds, "s")\n'
    b'\n'
    b'\n'
    b'def main() -> None:\n'
    b'    if sys.argv[1:] == ["--print-prefix"]:\n'
    b'        print(WRAPPER_PREFIX)\n'
    b'        return\n'
    b'\n'
    b'    if sys.argv[1:] == ["--githash"]:\n'
    b'        run("lean", "--githash")\n'
    b'        return\n'
    b'\n'
    b'    parser = argparse.ArgumentParser()\n'
    b'    parser.add_argument("lean", type=Path)\n'
    b'    parser.add_argument("--setup", type=Path)\n'
    b'    args, _ = parser.parse_known_args()\n'
    b'\n'
    b'    lean: Path = args.lean\n'
    b'    setup: Path = args.setup\n'
    b'\n'
    b'    module = get_module(setup)\n'
    b'    count_lines(module, lean)\n'
    b'    run_lean(module)\n'
    b'\n'
    b'\n'
    b'if __name__ == "__main__":\n'
    b'    main()\n'
)
BENCH_RUN = (
    b'#!/usr/bin/env python3\n'
    b'\n'
    b'import json\n'
    b'import os\n'
    b'from pathlib import Path\n'
    b'from typing import Generator\n'
    b'\n'
    b'OUTFILE = Path(os.environ["OUTPUT_FILE"])\n'
    b'\n'
    b'\n'
    b'def output_result(\n'
    b'    topic: str,\n'
    b'    category: str,\n'
    b'    value: float,\n'
    b'    unit: str | None = None,\n'
    b') -> None:\n'
    b'    data = {"metric": f"{topic}//{category}", "value": value}\n'
    b'    if unit is not None:\n'
    b'        data["unit"] = unit\n'
    b'    with open(OUTFILE, "a") as f:\n'
    b'        f.write(f"{json.dumps(data)}\\n")\n'
    b'\n'
    b'\n'
    b'def find_lean_files() -> Generator[Path, None, None]:\n'
    b'    for p in Path().iterdir():\n'
    b'        if p.name.startswith("."):\n'
    b'            continue\n'
    b'        elif p.is_dir():\n'
    b'            yield from p.glob("**/*.lean")\n'
    b'        elif p.name.endswith(".lean"):\n'
    b'            yield p\n'
    b'\n'
    b'\n'
    b'def measure_lines(topic: str, *paths: Path) -> None:\n'
    b'    for path in paths:\n'
    b'        if path.is_file():\n'
    b'            lines = len(path.read_text().splitlines())\n'
    b'            output_result(topic, "lines", lines)\n'
    b'            output_result(topic, "files", 1)\n'
    b'\n'
    b'\n'
    b'def measure_bytes(topic: str, *paths: Path) -> None:\n'
    b'    for path in paths:\n'
    b'        if path.is_file():\n'
    b'            bytes = path.stat().st_size\n'
    b'            output_result(topic, "bytes", bytes, "B")\n'
    b'            output_result(topic, "files", 1)\n'
    b'\n'
    b'\n'
    b'if __name__ == "__main__":\n'
    b'    measure_lines("size/.lean", *find_lean_files())\n'
    b'    measure_bytes("size/.olean", *Path().glob(".lake/build/**/*.olean"))\n'
    b'    measure_bytes("size/.olean.server", *Path().glob(".lake/build/**/*.olean.server"))\n'
    b'    measure_bytes("size/.olean.private", *Path().glob(".lake/build/**/*.olean.private"))\n'
)

class PinnedDependencyLinkControls(unittest.TestCase):
    def entries(self):
        result = {name: {} for name in admission.PINNED_GIT_DEPENDENCIES}
        for name, records in admission.PINNED_DEPENDENCY_LINKS.items():
            for path, link_blob, _, target, target_mode, target_blob, _ in records:
                result[name][path] = ('120000', 'blob', link_blob)
                result[name][target] = (target_mode, 'blob', target_blob)
        return result

    def dependencies(self, entries):
        return {'curvature/.lake/packages/'+name: rows for name, rows in entries.items()}

    def catalog(self, entries=None, wrong_pin=None, tree_override=None):
        entries = self.entries() if entries is None else entries
        def git(path, *args):
            name = Path(path).name
            return (('0'*40 if name == wrong_pin else admission.PINNED_GIT_DEPENDENCIES[name])+'\n').encode()
        def tree(path, ref):
            name = Path(path).name
            self.assertEqual(ref, admission.PINNED_GIT_DEPENDENCIES[name])
            return tree_override if tree_override is not None else entries[name]
        with patch.object(admission, 'git', side_effect=git), patch.object(admission, 'tree_entries', side_effect=tree):
            return admission.dependency_links(Path('fixture'), self.dependencies(entries))

    def records(self):
        for name, records in admission.PINNED_DEPENDENCY_LINKS.items():
            for row in records: yield name, row

    def target_data(self, name, path):
        return BATTERIES_README if name == 'batteries' else BENCH_LEAN if path.endswith('/lean') else BENCH_RUN

    def test_complete_catalog_has_only_the_three_authenticated_alias_records(self):
        self.assertEqual(len(admission.PINNED_GIT_DEPENDENCIES), 9)
        manifest = json.loads((HERE.parents[1] / 'curvature/lake-manifest.json').read_text())
        self.assertEqual(admission.PINNED_GIT_DEPENDENCIES,
            {p['name']: p['rev'] for p in manifest['packages'] if p['type'] == 'git'})
        self.assertEqual(admission.BATTERIES_LINK, ('docs/README.md', '32d46ee883b58d6a383eed06eb98f33aa6530ded',
            b'../README.md', 'README.md', '4cd48268d7a14d8f5867862c549534cac08ebd45', 5427))
        self.assertEqual(admission.PINNED_DEPENDENCY_LINKS['mathlib'], (
            ('scripts/bench/build/fake-root/bin/lean.py', '819298943e1a8c331413fb55e2c4bbc98d05e562', b'lean',
             'scripts/bench/build/fake-root/bin/lean', '100755', '2ce14c08b2c7ba3d38c6e552e1c5d25de7f1a527', 2336),
            ('scripts/bench/size/run.py', 'e5224d533ef27b001224859a9b36696846a7e7fe', b'run',
             'scripts/bench/size/run', '100755', '38bea958139cfd9297e73219d509adb63c811eb3', 1545)))
        expected = set()
        for name, (path, link_blob, raw, target, _, target_blob, size) in self.records():
            data = self.target_data(name, target)
            self.assertEqual(len(data), size)
            self.assertEqual(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(), link_blob)
            self.assertEqual(hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest(), target_blob)
            expected.add('curvature/.lake/packages/'+name+'/'+path)
        self.assertEqual(set(self.catalog()), expected)
        self.assertEqual(len(expected), 3)
        self.assertEqual(admission.dependency_links(Path('fixture'), {}), {})

    def test_all_nine_pins_and_exact_tree_inventories_are_required(self):
        for name in admission.PINNED_GIT_DEPENDENCIES:
            with self.subTest(name=name), self.assertRaisesRegex(AssertionError, 'pin differs'):
                self.catalog(wrong_pin=name)
        with self.assertRaisesRegex(AssertionError, 'inventory differs'):
            self.catalog(tree_override={})
        for name in admission.PINNED_GIT_DEPENDENCIES:
            entries = self.entries(); del entries[name]
            with self.subTest(missing=name), self.assertRaisesRegex(AssertionError, 'root inventory differs'):
                self.catalog(entries)

    def test_each_declared_link_and_regular_target_mode_kind_blob_is_exact(self):
        for name, (path, _, _, target, _, _, _) in self.records():
            for chosen in (path, target):
                entry = self.entries()[name][chosen]
                alternatives = [('100644' if entry[0] != '100644' else '100755', entry[1], entry[2]),
                    (entry[0], 'tree', entry[2]), (entry[0], entry[1], '0'*40), None]
                for replacement in alternatives:
                    entries = self.entries()
                    if replacement is None: del entries[name][chosen]
                    else: entries[name][chosen] = replacement
                    with self.subTest(path=chosen, replacement=replacement), self.assertRaises(AssertionError):
                        self.catalog(entries)
            entries = self.entries(); entries[name][target] = entries[name][path]
            with self.subTest(target_link=target), self.assertRaises(AssertionError): self.catalog(entries)

    def test_unlisted_Lean_guard_loader_and_other_package_aliases_are_rejected(self):
        for name in admission.PINNED_GIT_DEPENDENCIES:
            for path in ('Mathlib/Fixture.lean', 'scripts/chart_port_candidate_check.py', 'Cache/Main.lean', 'docs/OTHER.md'):
                entries = self.entries(); entries[name][path] = ('120000','blob',admission.BATTERIES_LINK[1])
                with self.subTest(name=name,path=path), self.assertRaisesRegex(AssertionError,'link catalog differs'):
                    self.catalog(entries)

    def exercise(self, *, virtual=True, changed_raw=None, changed_target=None, omit=None,
                 regular_alias=None, target_alias=None, extra_link=None, public_link=False):
        entries = self.entries()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); virtual_nodes = set(); raw_links = {}
            for name in entries: (root/'curvature/.lake/packages'/name).mkdir(parents=True)
            for name, (path, _, raw, target, target_mode, _, _) in self.records():
                prefix = 'curvature/.lake/packages/'+name+'/'
                link = root/(prefix+path); dest = root/(prefix+target)
                link.parent.mkdir(parents=True,exist_ok=True); dest.parent.mkdir(parents=True,exist_ok=True)
                if omit != prefix+target:
                    data = self.target_data(name,target)
                    if changed_target == prefix+target: data = b'!'+data[1:]
                    dest.write_bytes(data)
                    if os.name == 'posix': dest.chmod(0o755 if target_mode == '100755' else 0o644)
                if omit != prefix+path:
                    data = raw+b'\n' if changed_raw == prefix+path else raw
                    raw_links[os.fsencode(link)] = data
                    if virtual or regular_alias == prefix+path:
                        link.write_bytes(b'finite placeholder, never followed')
                        if regular_alias != prefix+path: virtual_nodes.add(link)
                    else: os.symlink(data, os.fsencode(link))
                if target_alias == prefix+target: virtual_nodes.add(dest)
            public = {}
            if extra_link:
                node = root/extra_link
                if not node.exists():
                    node.parent.mkdir(parents=True,exist_ok=True); node.write_bytes(b'finite placeholder, never followed')
                virtual_nodes.add(node)
                if public_link: public[extra_link] = ('120000','blob',admission.BATTERIES_LINK[1])
            real_scandir = os.scandir; reads = []
            def scan(directory):
                with real_scandir(directory) as iterator: items = list(iterator)
                return [types.SimpleNamespace(path=i.path,is_symlink=lambda:True) if Path(i.path) in virtual_nodes else i for i in items]
            def readlink(path):
                self.assertIsInstance(path,bytes); reads.append(path); return raw_links[path]
            def git(path,*args): return (admission.PINNED_GIT_DEPENDENCIES[Path(path).name]+'\n').encode()
            def tree(path,ref): return entries[Path(path).name]
            with patch.object(admission,'configuration_outputs',return_value=set()), \
                 patch.object(admission,'git',side_effect=git), patch.object(admission,'tree_entries',side_effect=tree), \
                 patch.object(admission.os,'scandir',side_effect=scan):
                if virtual:
                    with patch.object(admission.os,'readlink',side_effect=readlink):
                        result = admission.physical_inventory(root,public,self.dependencies(entries))
                    self.assertEqual(len(reads),3)
                else: result = admission.physical_inventory(root,public,self.dependencies(entries))
            return result

    def test_all_three_physical_aliases_and_regular_targets_are_in_exact_inventory(self):
        receipt = self.exercise()
        self.assertEqual(receipt['dependency_files'],6)
        self.assertEqual(receipt['declared_build_outputs'],[])
        self.assertTrue(receipt['full_physical_inventory_checked'])
        self.assertFalse(receipt['local_project_cache_admitted'])
        self.assertEqual(len(receipt['declared_source_links']),3)
        for row in receipt['declared_source_links']:
            name = row['path'].split('/')[3]
            self.assertEqual(row['pin'],admission.PINNED_GIT_DEPENDENCIES[name])
            record = next(r for r in admission.PINNED_DEPENDENCY_LINKS[name] if row['path'].endswith('/'+r[0]))
            self.assertEqual(row['link_blob'],record[1]); self.assertEqual(row['raw_bytes'],len(record[2]))
            self.assertEqual(row['raw_sha256'],digest(record[2])); self.assertEqual(row['target_blob'],record[5])

    def test_changed_raw_alias_bytes_and_regular_target_bytes_are_rejected(self):
        for name, (path, _, _, target, _, _, _) in self.records():
            prefix = 'curvature/.lake/packages/'+name+'/'
            with self.subTest(alias=path), self.assertRaisesRegex(AssertionError,'link text differs'):
                self.exercise(changed_raw=prefix+path)
            with self.subTest(target=target), self.assertRaisesRegex(AssertionError,'Physical bytes differ'):
                self.exercise(changed_target=prefix+target)

    def test_missing_regularized_and_nonregular_alias_targets_are_rejected(self):
        for name, (path, _, _, target, _, _, _) in self.records():
            prefix = 'curvature/.lake/packages/'+name+'/'
            for options in ({'omit':prefix+path},{'omit':prefix+target},{'regular_alias':prefix+path},{'target_alias':prefix+target}):
                with self.subTest(options=options), self.assertRaises(AssertionError): self.exercise(**options)

    def test_public_unlisted_and_generated_package_root_links_are_rejected(self):
        paths = ['curvature/Fixture.lean','curvature/.lake/packages/mathlib/Mathlib/Fixture.lean',
            'curvature/.lake/packages/mathlib/Cache/Main.lean','curvature/.lake/packages/mathlib',
            'curvature/.lake/packages/HamiltonIveyReaction']
        for path in paths:
            with self.subTest(path=path), self.assertRaisesRegex(AssertionError,'Physical symlink|Unexpected physical directory'):
                self.exercise(extra_link=path,public_link=path == 'curvature/Fixture.lean')

    def test_git_identity_reads_keep_command_scoped_no_replace_objects(self):
        with patch.object(admission.subprocess,'check_output',return_value=b'identity') as read:
            self.assertEqual(admission.git(Path('fixture'),'rev-parse','HEAD'),b'identity')
        read.assert_called_once_with(['git','--no-replace-objects','-C','fixture','rev-parse','HEAD'])
        for node in ast.walk(TREE):
            if isinstance(node,ast.List) and node.elts and isinstance(node.elts[0],ast.Constant) and node.elts[0].value == 'git':
                self.assertEqual(node.elts[1].value,'--no-replace-objects')

    @unittest.skipUnless(os.name == 'posix','Genuine Unix alias behavior UNRUN on Windows; no workaround')
    def test_genuine_unix_three_aliases_and_changed_raw_bytes(self):
        self.assertEqual(len(self.exercise(virtual=False)['declared_source_links']),3)
        for name,(path,*_) in self.records():
            with self.subTest(path=path), self.assertRaisesRegex(AssertionError,'link text differs'):
                self.exercise(virtual=False,changed_raw='curvature/.lake/packages/'+name+'/'+path)

class RootRelationshipControls(unittest.TestCase):
    def fixture(self,root,*,missing=False):
        pkg = root/'curvature'; pkg.mkdir()
        (root/'hamilton-ivey-reaction').mkdir()
        packages = [dict(name=name,type='git',rev=pin) for name,pin in admission.PINNED_GIT_DEPENDENCIES.items()]
        for p in packages:
            if not (missing and p['name'] == 'mathlib'): (pkg/'.lake/packages'/p['name']).mkdir(parents=True)
        packages.insert(0,dict(name='HamiltonIveyReaction',type='path',dir='../hamilton-ivey-reaction'))
        return pkg, dict(packagesDir='.lake/packages',packages=packages)

    def test_actual_regular_roots_and_path_dependency_relationship_are_diagnostic(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); pkg,manifest = self.fixture(root)
            artifact = root/'fixture-artifacts'; artifact.mkdir()
            def git(path,*args): return (admission.PINNED_GIT_DEPENDENCIES[Path(path).name]+'\n').encode()
            with patch.object(admission,'git',side_effect=git):
                receipt = admission.package_root_relationships(root,pkg,manifest,
                    {'LEAN_SRC_PATH':str(root/'hamilton-ivey-reaction'),'LEAN_PATH':str(artifact)})
            self.assertTrue(receipt['diagnostic_only']); self.assertFalse(receipt['root_link_exceptions_granted'])
            self.assertEqual(len(receipt['packages']),10)
            path = receipt['packages'][0]
            self.assertEqual(path['manifest_type'],'path'); self.assertTrue(path['observed_expected_root_relationship'])
            self.assertEqual(path['root']['node_kind'],'directory')
            self.assertEqual(path['generated_package_mirror']['node_kind'],'missing')
            for row in receipt['packages'][1:]:
                self.assertTrue(row['pins_match']); self.assertEqual(row['root']['node_kind'],'directory')
                self.assertNotIn('raw_link_text',row['root'])
            self.assertEqual(receipt['configured_paths']['LEAN_PATH']['observations'][0]['resolved_path'],str(artifact.resolve()))

    def test_missing_root_and_wrong_observed_pin_are_recorded_without_admission(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); pkg,manifest = self.fixture(root,missing=True)
            with patch.object(admission,'git',return_value=('0'*40+'\n').encode()):
                receipt = admission.package_root_relationships(root,pkg,manifest,{})
            mathlib = next(r for r in receipt['packages'] if r['name'] == 'mathlib')
            self.assertEqual(mathlib['root']['node_kind'],'missing'); self.assertIsNone(mathlib['actual_pin'])
            self.assertFalse(mathlib['pins_match'])
            self.assertFalse(next(r for r in receipt['packages'] if r['name'] == 'batteries')['pins_match'])
            self.assertFalse(receipt['root_link_exceptions_granted'])

    def test_configured_path_observations_are_bounded(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); pkg,manifest=self.fixture(root)
            with patch.object(admission,'git',return_value=('0'*40+'\n').encode()):
                receipt=admission.package_root_relationships(root,pkg,manifest,
                    {'LEAN_PATH':os.pathsep.join('finite'+str(i) for i in range(129))})
            self.assertTrue(receipt['configured_paths']['LEAN_PATH']['truncated'])
            self.assertEqual(len(receipt['configured_paths']['LEAN_PATH']['observations']),128)

    @unittest.skipUnless(os.name == 'posix','Genuine Unix root lstat/readlink behavior UNRUN on Windows')
    def test_genuine_unix_root_link_is_observed_without_exception_grant(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); pkg,manifest=self.fixture(root,missing=True)
            target=root/'finite-mathlib-source'; target.mkdir()
            path=pkg/'.lake/packages/mathlib'; os.symlink(os.fsencode(target),os.fsencode(path))
            with patch.object(admission,'git',return_value=(admission.PINNED_GIT_DEPENDENCIES['mathlib']+'\n').encode()):
                receipt=admission.package_root_relationships(root,pkg,manifest,{})
            row=next(r for r in receipt['packages'] if r['name']=='mathlib')
            self.assertEqual(row['root']['node_kind'],'symlink')
            self.assertEqual(bytes.fromhex(row['root']['raw_link_hex']),os.fsencode(target))
            self.assertEqual(row['root']['resolved_path'],str(target.resolve()))
            self.assertFalse(receipt['root_link_exceptions_granted'])


class FirstCompilerFailureLogging(unittest.TestCase):
    def fixture(self, root, *, exception=None, source_missing=False, cleanup=None):
        source=root/'Fixture/Source.lean'; source.parent.mkdir()
        if not source_missing: source.write_bytes(b'finite source bytes; never compiled\n')
        stdout=b'error: finite first stdout diagnostic\n'+b'a'*70000+b'\xfflast stdout byte\n'
        stderr=b'finite first stderr diagnostic\n'+b'b'*70000+b'last stderr byte\n'
        output=io.BytesIO(); saved=[]
        receipt=dict(candidate_sha='a'*40,candidate_tree='b'*40,stages=[],owner_pid=42,
            memory_limit_bytes=LIMIT,cpu_affinity=[0,1],cgroup='/finite/owned/cgroup')
        argv=['finite-compiler','-j1','-M5632','-DautoImplicit=false','-DmaxSynthPendingDepth=3',str(source)]
        def run(argv,label,env=None):
            (root/(label+'.stdout')).write_bytes(stdout); (root/(label+'.stderr')).write_bytes(stderr)
            stage=dict(argv=argv,cwd=str(root),status='FAILED' if exception else 'SUCCEEDED',exit_code=1 if exception else 0,
                timeout_seconds=600,peak_rss_bytes=4096,owner_reaped=True,remaining_session_pids=[],
                stdout_sha256=digest(stdout),stderr_sha256=digest(stderr))
            if cleanup:
                stage.update(cleanup)
                if cleanup.get('owner_reaped') is None: stage.pop('owner_reaped')
            receipt['stages'].append(stage)
            if exception: raise exception
            return stdout
        ns=dict(Path=Path,EVIDENCE=root,receipt=receipt,json=json,hashlib=hashlib,digest=digest,
            sys=types.SimpleNamespace(stdout=types.SimpleNamespace(buffer=output)),
            run=run,save=lambda:saved.append(True),
            print=lambda value,**kw:output.write((str(value)+'\n').encode()))
        execute_nodes([next(n for n in TREE.body if isinstance(n,ast.FunctionDef) and n.name==name)
            for name in ('compiler_log_identity','record_first_compiler_failure','compiler_run')],ns)
        return ns,source,argv,receipt,output,stdout,stderr,saved

    def test_success_does_not_create_or_emit_failure_evidence(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); ns,source,argv,receipt,output,stdout,*_=self.fixture(root)
            self.assertEqual(ns['compiler_run'](argv,'local-0',source,'Fixture.Source'),stdout)
            self.assertFalse((root/'first-compiler-failure.json').exists())
            self.assertEqual(output.getvalue(),b'')
            self.assertNotIn('first_compiler_failure',receipt)

    def test_actual_failure_streams_complete_raw_logs_and_binds_source_stage_and_summary(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); failure=AssertionError('finite owned stage failed')
            ns,source,argv,receipt,output,stdout,stderr,saved=self.fixture(root,exception=failure)
            with self.assertRaises(AssertionError) as raised: ns['compiler_run'](argv,'local-0',source,'Fixture.Source')
            self.assertIs(raised.exception,failure)
            self.assertEqual(output.getvalue(),b'\n=== first failed compiler stage local-0: stdout ===\n'+stdout+
                b'\n=== first failed compiler stage local-0: stderr ===\n'+stderr)
            raw=(root/'first-compiler-failure.json').read_bytes(); summary=json.loads(raw)
            self.assertLess(len(raw),16384)  # The raw logs belong to retained files/job output, not this small summary.
            self.assertEqual((root/'first-compiler-failure.sha256').read_text(),digest(raw)+'  first-compiler-failure.json\n')
            self.assertEqual(summary['stage'],'local-0'); self.assertEqual(summary['argv'],argv)
            self.assertEqual(summary['source_identity']['sha256'],digest(source.read_bytes()))
            self.assertTrue(summary['source_identity']['observed_before_owned_stage'])
            self.assertEqual(summary['failure_exception'],{'type':'AssertionError','message':str(failure)})
            self.assertEqual(summary['owned_stage_receipt'],receipt['stages'][-1])
            self.assertEqual(summary['driver_resource_receipt']['memory_limit_bytes'],LIMIT)
            self.assertEqual(summary['owned_stage_receipt']['remaining_session_pids'],[])
            for suffix,data in (('stdout',stdout),('stderr',stderr)):
                self.assertEqual(summary['logs'][suffix]['sha256'],digest(data))
                self.assertEqual(summary['logs'][suffix]['bytes'],len(data))
                self.assertEqual((root/('local-0.'+suffix)).read_bytes(),data)
            self.assertEqual(receipt['first_compiler_failure']['summary_sha256'],digest(raw))
            self.assertEqual(saved,[True])

    def test_later_failure_never_replaces_first_summary_or_its_hash(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); ns,source,argv,receipt,output,*_=self.fixture(root,exception=RuntimeError('first'))
            for label in ('local-0','local-1'):
                with self.assertRaises(RuntimeError): ns['compiler_run'](argv,label,source,'Fixture.Source')
                if label=='local-0':
                    first=(root/'first-compiler-failure.json').read_bytes()
                    companion=(root/'first-compiler-failure.sha256').read_bytes(); emitted=output.getvalue()
            self.assertEqual((root/'first-compiler-failure.json').read_bytes(),first)
            self.assertEqual((root/'first-compiler-failure.sha256').read_bytes(),companion)
            self.assertEqual(output.getvalue(),emitted)
            self.assertEqual(receipt['first_compiler_failure']['stage'],'local-0')
            self.assertTrue((root/'local-1.stdout').exists())

    def test_exception_and_incomplete_cleanup_remain_visible_without_forged_completion(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); failure=TimeoutError('finite compiler deadline')
            ns,source,argv,receipt,output,*_=self.fixture(root,exception=failure,
                cleanup={'owner_reaped':None,'remaining_session_pids':[123],'exception_type':'TimeoutError'})
            with self.assertRaises(TimeoutError): ns['compiler_run'](argv,'local-0',source,'Fixture.Source')
            summary=json.loads((root/'first-compiler-failure.json').read_text())
            self.assertEqual(summary['failure_exception']['type'],'TimeoutError')
            self.assertEqual(summary['owned_stage_receipt']['remaining_session_pids'],[123])
            self.assertNotIn('owner_reaped',summary['owned_stage_receipt'])

    def test_source_identity_unavailable_is_explicit(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); ns,source,argv,*_=self.fixture(root,exception=RuntimeError('finite failure'),source_missing=True)
            with self.assertRaises(RuntimeError): ns['compiler_run'](argv,'local-0',source,'Fixture.Source')
            identity=json.loads((root/'first-compiler-failure.json').read_text())['source_identity']
            self.assertEqual(identity['identity_read_exception'],'FileNotFoundError')
            self.assertNotIn('sha256',identity)

    def test_reporting_write_error_preserves_original_exception_and_emits_retained_logs(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); failure=RuntimeError('original finite compiler failure')
            ns,source,argv,receipt,output,stdout,stderr,_=self.fixture(root,exception=failure)
            ordinary_open=Path.open
            def open_path(path,*args,**kwargs):
                if path==root/'first-compiler-failure.json' and args and args[0]=='xb':
                    raise OSError('finite summary-write failure')
                return ordinary_open(path,*args,**kwargs)
            with patch.object(Path,'open',open_path):
                with self.assertRaises(RuntimeError) as raised: ns['compiler_run'](argv,'local-0',source,'Fixture.Source')
            self.assertIs(raised.exception,failure)
            self.assertIn(stdout,output.getvalue()); self.assertIn(stderr,output.getvalue())
            self.assertEqual(receipt['first_compiler_failure_reporting_error']['type'],'OSError')

    def test_reporting_and_fallback_output_failure_preserve_identical_original_exception(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); failure=RuntimeError('identical original finite compiler failure')
            ns,source,argv,receipt,output,stdout,stderr,_=self.fixture(root,exception=failure)
            attempts=[]
            class FailedJobOutput:
                def write(self, data):
                    attempts.append('reporting output')
                    raise BrokenPipeError('finite reporting output failure')
                def flush(self):
                    raise BrokenPipeError('finite reporting flush failure')
            ns['sys'].stdout.buffer=FailedJobOutput()
            def fallback_print(*args, **kwargs):
                attempts.append('fallback output')
                raise BrokenPipeError('finite fallback output failure')
            ns['print']=fallback_print
            with self.assertRaises(RuntimeError) as raised:
                ns['compiler_run'](argv,'local-0',source,'Fixture.Source')
            self.assertIs(raised.exception,failure)
            self.assertEqual(attempts,['reporting output','fallback output'])
            self.assertEqual(receipt['first_compiler_failure_reporting_error']['type'],'BrokenPipeError')
            self.assertEqual((root/'local-0.stdout').read_bytes(),stdout)
            self.assertEqual((root/'local-0.stderr').read_bytes(),stderr)

    def test_small_summary_upload_is_separate_and_complete_archive_guard_is_retained(self):
        workflow=(HERE.parents[1]/'.github/workflows/point4-local-chart-connection.yml').read_text()
        small=workflow.split('      - name: Preserve small first compiler failure summary independently\n')[1]
        small,complete=small.split('      - name: Preserve exact candidate source and build receipts\n')
        self.assertIn('if: always()',small)
        self.assertIn('local-chart-first-compiler-failure-',small)
        self.assertIn('/first-compiler-failure.json',small); self.assertIn('/first-compiler-failure.sha256',small)
        self.assertNotIn('.stdout',small); self.assertNotIn('.stderr',small)
        self.assertIn('if-no-files-found: error',complete)
        serial=ast.get_source_segment(SOURCE,next(n for n in TREE.body if isinstance(n,ast.FunctionDef) and n.name=='serial_compile'))
        self.assertIn('compiler_run(argv, label, source, name, env=env)',serial)
        self.assertIn("'full-type-proof-axiom-probe', source, row['module'], env=env",SOURCE)

class OwnedProcessIdentityAndPrefixQuery(unittest.TestCase):
    path = '/official/bin/lean'
    stage_argv = [path, '-j1', '-M5632', '-o', 'fresh.olean', '-c', 'fresh.c', 'fixture.lean']

    def rows(self):
        import copy
        owner = dict(pid=100, ppid=50, pgrp=100, session=100, starttime_ticks=20,
            exe=self.path, exe_sha256='a'*64, argv=list(self.stage_argv),
            image_identity=[1,2,3,4,5], stable=True, errors=[], state='R', recheck=dict(state='S'))
        query = copy.deepcopy(owner)
        query.update(pid=101, ppid=100, starttime_ticks=21, argv=['lean','--print-prefix'])
        official = dict(compiler_path=self.path, compiler_sha256='a'*64,
            compiler_commit='d8b18978322de05a8f3dba51ef03cf5461676c17')
        return query, owner, official

    def classify(self, query, owner, official, argv=None):
        return function('is_exact_official_prefix_query', {})(query, owner,
            self.stage_argv if argv is None else argv, official)

    def test_exact_executed_same_official_binary_query_only(self):
        query,owner,official=self.rows()
        self.assertTrue(self.classify(query,owner,official))
        query['argv']=[self.path,'--print-prefix']
        self.assertTrue(self.classify(query,owner,official))

    def test_actual_second_compiler_and_inherited_preexec_image_count(self):
        query,owner,official=self.rows()
        for argv in (list(self.stage_argv), [self.path,'second.lean'], ['lean','--print-prefix','extra'],
                ['unknown','--print-prefix'], ['lean','--version'], []):
            with self.subTest(argv=argv):
                query['argv']=argv
                self.assertFalse(self.classify(query,owner,official))

    def test_wrong_executable_hash_image_or_official_commit_reject(self):
        for key,value in (('exe','/other/bin/lean'),('exe_sha256','b'*64),('image_identity',[9,2,3,4,5])):
            query,owner,official=self.rows();query[key]=value
            self.assertFalse(self.classify(query,owner,official),key)
        query,owner,official=self.rows();official['compiler_commit']='wrong'
        self.assertFalse(self.classify(query,owner,official))

    def test_wrong_parentage_session_group_or_reused_pid_reject(self):
        for key,value in (('pid',100),('ppid',99),('session',200),('pgrp',200),('starttime_ticks',19)):
            query,owner,official=self.rows();query[key]=value
            self.assertFalse(self.classify(query,owner,official),key)
        query,owner,official=self.rows();owner['argv']=['other']
        self.assertFalse(self.classify(query,owner,official))

    def test_unknown_raced_disappeared_or_zombie_identity_reject(self):
        for target in ('query','owner'):
            for key,value in (('stable',False),('errors',[dict(type='FileNotFoundError')]),
                    ('state','Z'),('recheck',dict(state='Z'))):
                query,owner,official=self.rows();(query if target=='query' else owner)[key]=value
                self.assertFalse(self.classify(query,owner,official),(target,key))
        query,owner,official=self.rows()
        del query['exe_sha256']
        self.assertFalse(self.classify(query,owner,official))
        self.assertFalse(self.classify({},owner,official))
        self.assertFalse(self.classify(owner,{},{}))

    def test_noncompiler_or_unverified_stage_cannot_exempt(self):
        query,owner,official=self.rows()
        for argv in ([self.path,'--print-prefix'], ['lean']+self.stage_argv[1:],
                self.stage_argv[:-1]+['not-source'], []):
            self.assertFalse(self.classify(query,owner,official,argv))
        self.assertFalse(self.classify(query,owner,{}))

    def exercise(self, *, child_argv=None, race=False, disappear=False, unknown=False, snapshot_only=False, pages=2, overdue=False, missing_owner=False, exe_race=False, reverse_exe_race=False, reverse_order=False, child_state=None, terminal_change=None, terminal_read_error=None, zombie_survivor=False, owner_argv=None, cache_context=None):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);procdir=root/'proc';procdir.mkdir()
            image_bytes=b'finite synthetic executed official executable identity'
            image=root/'official-image';image.write_bytes(image_bytes)
            def stat(pid, session=100):
                fields=['S']+['0']*50;fields[1]='50' if pid==100 else '100'
                fields[2]=str(session);fields[3]=str(session);fields[19]=str(20 if pid==100 else 21);fields[21]=str(pages)
                if pid==101 and child_state is not None:
                    fields[0]=child_state
                    if child_state=='Z':fields[21]='0'
                (procdir/str(pid)/'stat').write_text(str(pid)+' (fixture) '+' '.join(fields))
            for pid,args in ((100,self.stage_argv if owner_argv is None else owner_argv),(101,['lean','--print-prefix'] if child_argv is None else child_argv)):
                if missing_owner and pid==100:continue
                p=procdir/str(pid);p.mkdir();stat(pid)
                (p/'cmdline').write_bytes(b'\0'.join(x.encode() for x in args)+b'\0')
                (p/'exe').write_bytes(image_bytes)
            receipt=dict(stages=[],compiler_path=self.path,compiler_sha256=hashlib.sha256(image_bytes).hexdigest(),
                compiler_commit='d8b18978322de05a8f3dba51ef03cf5461676c17')
            events=[]
            class Proc:
                pid=100;returncode=0;polls=0
                def poll(self):
                    self.polls+=1
                    return None if self.polls==1 else 0
                def wait(self,timeout):events.append(('wait',timeout));return self.returncode
            def kill(pid,sig):
                events.append(('kill',pid,sig))
                for n in (100,101):
                    if (procdir/str(n)).exists() and not (zombie_survivor and n==101):stat(n,0)
            exe_reads=0
            def readlink(p):
                nonlocal exe_reads
                if Path(p).parent.name=='101':
                    exe_reads+=1
                    if child_state=='Z':raise FileNotFoundError('finite zombie executable absent')
                    if unknown:raise PermissionError('finite unreadable executable')
                    if exe_race and exe_reads==1:return '/official/bin/helper'
                    if reverse_exe_race and exe_reads==2:return '/official/bin/helper'
                return self.path
            clock=iter([0,601,602] if overdue else [0,1,2])
            def proc_entries():
                entries=sorted(procdir.iterdir(),key=lambda p:int(p.name))
                return iter(list(reversed(entries)) if reverse_order else entries)
            fixture_proc=types.SimpleNamespace(iterdir=proc_entries)
            ns=dict(Path=lambda p:fixture_proc if str(p)=='/proc' else Path(p),EVIDENCE=root,PKG=root,
                LIMIT=6*1024**3,receipt=receipt,save=lambda:None,
                subprocess=types.SimpleNamespace(Popen=lambda *a,**kw:Proc()),
                signal=types.SimpleNamespace(SIGKILL=9),digest=lambda b:hashlib.sha256(b).hexdigest(),
                time=types.SimpleNamespace(time=lambda:123,monotonic=lambda:next(clock),sleep=lambda _:None),
                os=types.SimpleNamespace(readlink=readlink,killpg=kill,sysconf=lambda _:4096))
            function('owned_process_identity',ns);function('is_exact_official_prefix_query',ns)
            original_stat,original_read=Path.stat,Path.read_bytes
            original_text=Path.read_text;stat_reads=0
            def terminal_stat_read(p,*args,**kwargs):
                nonlocal stat_reads
                raw=original_text(p,*args,**kwargs)
                if p.name=='stat' and p.parent.name=='101':
                    stat_reads+=1
                    if child_state=='Z' and stat_reads==2:
                        if terminal_read_error:raise terminal_read_error('finite terminal stat read failed')
                        if terminal_change:
                            pid_part,tail=raw.rsplit(')',1);fields=tail.split()
                            indices={'state':0,'ppid':1,'pgrp':2,'session':3,'starttime_ticks':19,'rss_bytes':21}
                            if terminal_change=='pid':pid_part='102 (fixture'
                            else:
                                index=indices[terminal_change]
                                fields[index]='R' if terminal_change=='state' else str(int(fields[index])+1)
                            raw=pid_part+') '+' '.join(fields)
                return raw
            reads=0
            def image_stat(p,*a,**kw):
                return original_stat(image) if p.name=='exe' else original_stat(p,*a,**kw)
            def cmdline_read(p):
                nonlocal reads
                if p.name=='cmdline' and p.parent.name=='101':
                    reads+=1
                    if reads==2:
                        if disappear:raise FileNotFoundError('finite process disappeared before recheck')
                        if race:return b'lean\0second.lean\0'
                return original_read(p)
            failure=None
            with patch.object(Path,'stat',image_stat),patch.object(Path,'read_bytes',cmdline_read),patch.object(Path,'read_text',terminal_stat_read):
                if snapshot_only:
                    fields=(procdir/'101/stat').read_text().rsplit(')',1)[1].split()
                    return ns['owned_process_identity'](procdir/'101',fields)
                try:function('run',ns)(list(self.stage_argv if owner_argv is None else owner_argv),'fixture',
                    **({} if cache_context is None else dict(cache_query_context=cache_context)))
                except BaseException as exc:failure=exc
            return receipt['stages'][0],events,failure

    def process(self,stage,pid):
        rows=[row for row in stage['owned_process_snapshot']['processes'] if row['pid']==pid]
        self.assertEqual(len(rows),1,'Exact fixture PID must have one observed identity')
        row=rows[0]
        self.assertEqual(row['session'],100);self.assertEqual(row['pgrp'],100)
        if pid==101:self.assertEqual(row['ppid'],100)
        return row

    def test_both_enumeration_orders_preserve_query_compiler_race_and_resource_assertions(self):
        cases=[(dict(),1,True,None),
            (dict(child_argv=[self.path,'second.lean']),2,False,RuntimeError),
            (dict(child_argv=self.stage_argv),2,False,RuntimeError),
            (dict(child_argv=['lean','--print-prefix','extra']),2,False,RuntimeError),
            (dict(exe_race=True),2,False,RuntimeError),
            (dict(exe_race=True,disappear=True),2,False,RuntimeError),
            (dict(reverse_exe_race=True),2,False,RuntimeError),
            (dict(race=True),2,False,RuntimeError),
            (dict(disappear=True),2,False,RuntimeError),
            (dict(unknown=True),2,False,RuntimeError),
            (dict(pages=10**9),1,True,RuntimeError),
            (dict(overdue=True),1,True,TimeoutError),
            (dict(missing_owner=True),1,False,RuntimeError)]
        for reverse in (False,True):
            for kwargs,count,query,exception in cases:
                with self.subTest(reverse_order=reverse,kwargs=kwargs):
                    stage,events,failure=self.exercise(reverse_order=reverse,**kwargs)
                    snapshot=stage['owned_process_snapshot']
                    expected=[101] if kwargs.get('missing_owner') else ([101,100] if reverse else [100,101])
                    self.assertEqual([row['pid'] for row in snapshot['processes']],expected)
                    self.assertEqual(snapshot['counted_compilers'],count)
                    child=self.process(stage,101)
                    self.assertEqual(child['exact_official_prefix_query'],query)
                    self.assertEqual(child['counted_compiler'],not query)
                    if exception:self.assertIsInstance(failure,exception)
                    else:self.assertIsNone(failure)
                    if any(kwargs.get(k) for k in ('exe_race','reverse_exe_race','race','disappear','unknown')):
                        self.assertTrue(child['errors']);self.assertFalse(child['stable'])
                    if kwargs.get('exe_race'):
                        self.assertEqual(child['exe'],'/official/bin/helper')
                        self.assertEqual(child['recheck']['exe'],self.path)
                    self.assertTrue(stage['owner_reaped']);self.assertEqual(stage['remaining_session_pids'],[])
                    self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_snapshot_contains_full_identity_rechecks_and_raw_argv(self):
        row=self.exercise(snapshot_only=True)
        self.assertTrue(row['stable']);self.assertEqual(row['errors'],[])
        self.assertEqual(row['argv'],['lean','--print-prefix'])
        self.assertEqual(row['cmdline_hex'],b'lean\0--print-prefix\0'.hex())
        for field in ('pid','starttime_ticks','exe','exe_sha256','ppid','pgrp','session','state',
                'observed_at','rechecked_at','rss_bytes','image_identity','recheck'):
            self.assertIn(field,row)

    def test_legitimate_query_classified_but_rss_and_cleanup_include_it(self):
        stage,events,failure=self.exercise()
        self.assertIsNone(failure);self.assertEqual(stage['peak_rss_bytes'],4*4096)
        snap=stage['owned_process_snapshot'];self.assertEqual(snap['counted_compilers'],1)
        self.assertEqual([(pid,self.process(stage,pid)['exact_official_prefix_query']) for pid in (100,101)],[(100,False),(101,True)])
        self.assertTrue(stage['owner_reaped']);self.assertEqual(stage['remaining_session_pids'],[])
        self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_query_remains_subject_to_rss_limit_and_stage_timeout(self):
        for kwargs,exception in ((dict(pages=10**9),RuntimeError),(dict(overdue=True),TimeoutError)):
            stage,events,failure=self.exercise(**kwargs)
            self.assertIsInstance(failure,exception)
            self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],1)
            self.assertTrue(self.process(stage,101)['exact_official_prefix_query'])
            self.assertTrue(stage['owner_reaped']);self.assertEqual(len(events),2)

    def test_missing_owner_identity_cannot_admit_observed_child(self):
        stage,_,failure=self.exercise(missing_owner=True)
        self.assertIsInstance(failure,RuntimeError)
        self.assertEqual(str(failure),'Owned process identities observed without compiler owner identity')
        self.assertFalse(self.process(stage,101)['exact_official_prefix_query'])

    def test_actual_second_compiler_rejects_with_snapshot_before_cleanup(self):
        stage,events,failure=self.exercise(child_argv=[self.path,'second.lean'])
        self.assertIsInstance(failure,RuntimeError)
        self.assertEqual(str(failure),'More than one Lean compiler in an owned stage')
        self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)
        self.assertEqual(self.process(stage,101)['argv'],[self.path,'second.lean'])
        self.assertEqual(stage['error'],str(failure));self.assertEqual(stage['exception_type'],'RuntimeError')
        self.assertTrue(stage['owner_reaped']);self.assertEqual(len(events),2)
        self.assertEqual(stage['stdout_sha256'],hashlib.sha256(b'').hexdigest())
        self.assertEqual(stage['stderr_sha256'],hashlib.sha256(b'').hexdigest())

    def test_nonlean_to_lean_recheck_race_is_counted_and_rejected(self):
        stage,events,failure=self.exercise(exe_race=True)
        self.assertIsInstance(failure,RuntimeError)
        self.assertEqual(str(failure),'More than one Lean compiler in an owned stage')
        row=self.process(stage,101)
        self.assertEqual(row['exe'],'/official/bin/helper')
        self.assertEqual(row['recheck']['exe'],self.path)
        self.assertEqual(row['errors'][0]['type'],'IdentityRace')
        self.assertFalse(row['stable']);self.assertFalse(row['exact_official_prefix_query'])
        self.assertTrue(row['counted_compiler'])
        self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)
        self.assertTrue(stage['owner_reaped']);self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_recheck_lean_survives_later_cmdline_read_error_and_is_counted(self):
        row=self.exercise(exe_race=True,disappear=True,snapshot_only=True)
        self.assertEqual(row['exe'],'/official/bin/helper')
        self.assertEqual(row['recheck']['exe'],self.path)
        self.assertNotIn('cmdline_hex',row['recheck'])
        self.assertEqual(row['errors'][0]['type'],'FileNotFoundError')
        self.assertFalse(row['stable'])
        stage,events,failure=self.exercise(exe_race=True,disappear=True)
        self.assertIsInstance(failure,RuntimeError)
        self.assertEqual(str(failure),'More than one Lean compiler in an owned stage')
        row=self.process(stage,101)
        self.assertEqual(row['recheck']['exe'],self.path)
        self.assertTrue(row['counted_compiler']);self.assertFalse(row['exact_official_prefix_query'])
        self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)
        self.assertEqual(stage['error'],str(failure));self.assertEqual(stage['exception_type'],'RuntimeError')
        self.assertEqual(stage['stdout_sha256'],hashlib.sha256(b'').hexdigest())
        self.assertEqual(stage['stderr_sha256'],hashlib.sha256(b'').hexdigest())
        self.assertTrue(stage['owner_reaped']);self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_initial_lean_remains_counted_after_nonlean_recheck(self):
        stage,_,failure=self.exercise(reverse_exe_race=True)
        self.assertIsInstance(failure,RuntimeError)
        row=self.process(stage,101)
        self.assertEqual(row['exe'],self.path)
        self.assertEqual(row['recheck']['exe'],'/official/bin/helper')
        self.assertTrue(row['counted_compiler']);self.assertFalse(row['exact_official_prefix_query'])
        self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)

    def test_race_disappearance_unknown_and_preexec_fail_conservatively(self):
        for kwargs in (dict(race=True),dict(disappear=True),dict(unknown=True),dict(child_argv=self.stage_argv)):
            with self.subTest(kwargs=kwargs):
                stage,_,failure=self.exercise(**kwargs)
                self.assertIsInstance(failure,RuntimeError)
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)
                row=self.process(stage,101)
                self.assertFalse(row['exact_official_prefix_query'])
                if not 'child_argv' in kwargs:self.assertTrue(row['errors'])

    def test_verified_terminal_zombie_is_not_currently_compiling(self):
        for reverse in (False, True):
            with self.subTest(reverse_order=reverse):
                stage, events, failure = self.exercise(child_state='Z', reverse_order=reverse)
                self.assertIsNone(failure)
                row = self.process(stage,101)
                self.assertEqual(row['state'], 'Z')
                self.assertEqual(row['terminal_recheck']['state'], 'Z')
                self.assertTrue(row['verified_terminated_zombie'])
                self.assertEqual(row['terminal_errors'], [])
                self.assertTrue(row['conservative_executable_count'])
                self.assertFalse(row['counted_compiler'])
                self.assertFalse(row['exact_official_prefix_query'])
                self.assertNotIn('exe', row); self.assertNotIn('argv', row)
                self.assertEqual(row['errors'][0]['type'], 'FileNotFoundError')
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 1)
                self.assertEqual(stage['peak_rss_bytes'], 2*4096)
                self.assertTrue(stage['owner_reaped']); self.assertEqual(stage['remaining_session_pids'], [])
                self.assertEqual(events, [('kill',100,9),('wait',10)])

    def test_terminal_identity_changes_still_count_conservatively(self):
        for field in ('pid','state','ppid','pgrp','session','starttime_ticks','rss_bytes'):
            with self.subTest(field=field):
                stage, _, failure = self.exercise(child_state='Z', terminal_change=field)
                self.assertIsInstance(failure, RuntimeError)
                self.assertEqual(str(failure), 'More than one Lean compiler in an owned stage')
                row=self.process(stage,101)
                self.assertFalse(row['verified_terminated_zombie'])
                self.assertTrue(row['terminal_errors']); self.assertTrue(row['counted_compiler'])
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_terminal_read_errors_still_count_conservatively(self):
        for exception in (FileNotFoundError, PermissionError, ValueError, IndexError):
            with self.subTest(exception=exception):
                stage, _, failure=self.exercise(child_state='Z', terminal_read_error=exception)
                self.assertIsInstance(failure, RuntimeError)
                row=self.process(stage,101)
                self.assertFalse(row['verified_terminated_zombie']); self.assertTrue(row['counted_compiler'])
                self.assertEqual(row['terminal_errors'][0]['type'], exception.__name__)
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_alive_unreadable_and_preexec_images_still_count(self):
        for kwargs in (dict(unknown=True),dict(child_argv=self.stage_argv),dict(child_argv=[self.path,'second.lean'])):
            with self.subTest(kwargs=kwargs):
                stage, _, failure=self.exercise(**kwargs)
                self.assertIsInstance(failure, RuntimeError)
                row=self.process(stage,101)
                self.assertFalse(row['verified_terminated_zombie']); self.assertTrue(row['counted_compiler'])
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_terminal_zombie_does_not_waive_rss_or_deadline(self):
        for kwargs,exception in ((dict(pages=10**9),RuntimeError),(dict(overdue=True),TimeoutError)):
            with self.subTest(kwargs=kwargs):
                stage, events, failure=self.exercise(child_state='Z',**kwargs)
                self.assertIsInstance(failure,exception)
                self.assertTrue(self.process(stage,101)['verified_terminated_zombie'])
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],1)
                self.assertTrue(stage['owner_reaped']); self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_terminal_zombie_survivor_still_fails_cleanup(self):
        stage,events,failure=self.exercise(child_state='Z',zombie_survivor=True)
        self.assertIsInstance(failure,AssertionError)
        self.assertEqual(str(failure),'Owned session not drained')
        self.assertEqual(stage['remaining_session_pids'],[101])
        self.assertTrue(self.process(stage,101)['verified_terminated_zombie'])
        self.assertTrue(stage['owner_reaped']); self.assertEqual(events,[('kill',100,9),('wait',10)])

    def cache_context(self):
        context=dict(mathlib_pin=PIN,package_root='/finite/curvature/.lake/packages/mathlib',
            source='/finite/curvature/.lake/packages/mathlib/Cache/Main.lean',source_sha256='dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044',
            initializer='/finite/curvature/.lake/packages/mathlib/Cache/IO.lean',initializer_sha256='8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82',
            admitted_roots=['Mathlib.Fixture','Mathlib.OtherFixture'])
        argv=[self.path,'-j1','-M5632','-R',context['package_root'],'--run',context['source'],'get',*context['admitted_roots']]
        query,owner,official=self.rows();owner['argv']=argv
        return context,argv,query,owner,official

    def cache_classify(self, context, argv, query, owner, official):
        return function('is_exact_official_prefix_query',{})(query,owner,argv,official,context)

    def test_pinned_cache_helper_reads_both_exact_sources_and_rejects_changed_or_missing_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'Cache').mkdir()
            source=root/'Cache/Main.lean';io_source=root/'Cache/IO.lean'
            source.write_bytes(b'finite Cache.Main source');io_source.write_bytes(b'finite Cache.IO source')
            # Explicit source-hash fixture; real pinned source verification is
            # separately logged by the local source preflight, never inferred here.
            hashes={b'finite Cache.Main source':'dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044',b'finite Cache.IO source':'8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82'}
            reads=[]
            def finite_digest(data):reads.append(data);return hashes.get(data,digest(data))
            helper=function('pinned_cache_query_context',dict(digest=finite_digest))
            context=helper(root,['Mathlib.Fixture'])
            self.assertEqual(reads,[b'finite Cache.Main source',b'finite Cache.IO source'])
            self.assertEqual(context['mathlib_pin'],PIN)
            self.assertEqual(context['admitted_roots'],['Mathlib.Fixture'])
            self.assertEqual(context['source'],str(source));self.assertEqual(context['initializer'],str(io_source))
            for target,original in ((source,b'finite Cache.Main source'),(io_source,b'finite Cache.IO source')):
                target.write_bytes(b'changed finite source')
                with self.assertRaises(AssertionError):helper(root,['Mathlib.Fixture'])
                target.unlink()
                with self.assertRaises(FileNotFoundError):helper(root,['Mathlib.Fixture'])
                target.write_bytes(original)
            for roots in ([],None,(),['Mathlib'],['Mathlib.Foo','--scope=HEAD'],['Batteries.Foo'],['Mathlib.Foo/Bar'],[3]):
                with self.subTest(roots=roots):
                    with self.assertRaises(AssertionError):helper(root,roots)

    def test_pinned_cache_context_accepts_only_exact_executed_prefix_query(self):
        context,argv,query,owner,official=self.cache_context()
        self.assertFalse(function('is_exact_official_prefix_query',{})(query,owner,argv,official))
        for child_argv in (['lean','--print-prefix'],[self.path,'--print-prefix']):
            query['argv']=child_argv
            self.assertTrue(self.cache_classify(context,argv,query,owner,official))
        self.assertFalse(self.cache_classify(context,argv,owner,owner,official))
        for child_argv in (argv,[self.path,'second.lean'],['lean','--print-prefix','extra'],['lean','--version'],[]):
            query['argv']=child_argv
            self.assertFalse(self.cache_classify(context,argv,query,owner,official))

    def test_cache_context_rejects_other_source_pin_hash_roots_commands_flags_and_missing_fields(self):
        import copy
        context,argv,query,owner,official=self.cache_context()
        for key in context:
            altered=copy.deepcopy(context);del altered[key]
            self.assertFalse(self.cache_classify(altered,argv,query,owner,official),key)
        for key,value in (('mathlib_pin','0'*40),('source','/other/Main.lean'),('initializer','/other/IO.lean'),
                ('source_sha256','0'*64),('initializer_sha256','0'*64),('package_root','/other'),
                ('admitted_roots',[]),('admitted_roots',None),('admitted_roots',['Mathlib']),
                ('admitted_roots',['Mathlib.Fixture','--scope=HEAD']),('admitted_roots',['Mathlib.Added'])):
            altered=copy.deepcopy(context);altered[key]=value
            self.assertFalse(self.cache_classify(altered,argv,query,owner,official),(key,value))
        for altered in (argv+['Mathlib.Added'],argv[:-1],argv[:7]+['get!']+argv[8:],
                argv[:7]+['query']+argv[8:],argv[:7]+['put']+argv[8:],
                [self.path,'--run',context['source'],'get',*context['admitted_roots']],
                [self.path,'--print-prefix'],['lean']+argv[1:]):
            owner['argv']=altered
            self.assertFalse(self.cache_classify(context,altered,query,owner,official),altered)

    def test_cache_context_preserves_all_existing_process_identity_requirements(self):
        import copy
        context,argv,query,owner,official=self.cache_context()
        mutations=[('stable',False),('errors',[dict(type='FileNotFoundError')]),('state','Z'),
            ('recheck',dict(state='Z')),('exe','/other/bin/lean'),('exe_sha256','0'*64),
            ('image_identity',[9,2,3,4,5])]
        for target in ('query','owner'):
            for key,value in mutations:
                q,o=copy.deepcopy(query),copy.deepcopy(owner);(q if target=='query' else o)[key]=value
                self.assertFalse(self.cache_classify(context,argv,q,o,official),(target,key))
        for key,value in (('pid',100),('ppid',99),('session',200),('pgrp',200),('starttime_ticks',19)):
            q=copy.deepcopy(query);q[key]=value
            self.assertFalse(self.cache_classify(context,argv,q,owner,official),key)
        wrong=copy.deepcopy(official);wrong['compiler_commit']='wrong'
        self.assertFalse(self.cache_classify(context,argv,query,owner,wrong))
        wrong_owner=copy.deepcopy(owner);wrong_owner['argv']=argv+['Mathlib.Added']
        self.assertFalse(self.cache_classify(context,argv,query,wrong_owner,official))

    def test_cache_stage_caller_passes_only_admitted_context_and_preserves_full_geometry_gates(self):
        receipt,trace,failure=DriverControls().model(False)
        self.assertIsNone(failure)
        cache=[row for row in trace['run'] if row[1]=='ordinary-pinned-cache-read']
        self.assertEqual(len(cache),1)
        argv,label,kwargs=cache[0];context=kwargs['cache_query_context']
        self.assertTrue(context['finite_synthetic_source_context'])
        self.assertEqual(argv[3:8],['-R',context['package_root'],'--run',str(Path(context['package_root'])/'Cache/Main.lean'),'get'])
        self.assertEqual(argv[8:],context['admitted_roots'])
        self.assertEqual(kwargs['timeout'],1800)
        self.assertEqual((receipt['fresh_combined_modules'],receipt['fresh_combined_probes']),(83,11))
        self.assertTrue(all('cache_query_context' not in row[2] for row in trace['run'] if row[1]!=label))

    def test_cache_query_both_enumeration_orders_include_rss_and_cleanup_without_exempting_owner(self):
        context,argv,*_=self.cache_context()
        for reverse in (False,True):
            for child in (['lean','--print-prefix'],[self.path,'--print-prefix']):
                stage,events,failure=self.exercise(owner_argv=argv,cache_context=context,child_argv=child,reverse_order=reverse)
                self.assertIsNone(failure)
                self.assertEqual(stage['cache_query_context'],context)
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],1)
                self.assertFalse(self.process(stage,100)['exact_official_prefix_query'])
                self.assertTrue(self.process(stage,100)['counted_compiler'])
                self.assertTrue(self.process(stage,101)['exact_official_prefix_query'])
                self.assertEqual(stage['peak_rss_bytes'],4*4096)
                self.assertTrue(stage['owner_reaped']);self.assertEqual(stage['remaining_session_pids'],[])
                self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_cache_query_duplicate_ambiguous_preexec_and_contextless_processes_still_reject(self):
        context,argv,*_=self.cache_context()
        cases=[dict(child_argv=[self.path,'second.lean']),dict(child_argv=argv),
            dict(child_argv=['lean','--print-prefix','extra']),dict(exe_race=True),dict(reverse_exe_race=True),
            dict(race=True),dict(disappear=True),dict(unknown=True),dict(missing_owner=True)]
        for reverse in (False,True):
            for options in cases:
                with self.subTest(reverse=reverse,options=options):
                    stage,events,failure=self.exercise(owner_argv=argv,cache_context=context,reverse_order=reverse,**options)
                    self.assertIsInstance(failure,RuntimeError)
                    self.assertFalse(self.process(stage,101)['exact_official_prefix_query'])
                    self.assertTrue(self.process(stage,101)['counted_compiler'])
                    self.assertTrue(stage['owner_reaped']);self.assertEqual(stage['remaining_session_pids'],[])
                    self.assertEqual(events,[('kill',100,9),('wait',10)])
        stage,_,failure=self.exercise(owner_argv=argv)
        self.assertIsInstance(failure,RuntimeError)
        self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)

    def test_cache_query_retains_rss_timeout_and_survivor_failures(self):
        context,argv,*_=self.cache_context()
        for options,exception in ((dict(pages=10**9),RuntimeError),(dict(overdue=True),TimeoutError)):
            stage,events,failure=self.exercise(owner_argv=argv,cache_context=context,**options)
            self.assertIsInstance(failure,exception)
            self.assertTrue(self.process(stage,101)['exact_official_prefix_query'])
            self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],1)
            self.assertTrue(stage['owner_reaped']);self.assertEqual(events,[('kill',100,9),('wait',10)])
        stage,events,failure=self.exercise(owner_argv=argv,cache_context=context,child_state='Z',zombie_survivor=True)
        self.assertIsInstance(failure,AssertionError);self.assertEqual(str(failure),'Owned session not drained')
        self.assertEqual(stage['remaining_session_pids'],[101]);self.assertTrue(stage['owner_reaped'])

if __name__ == '__main__':
    unittest.main(verbosity=2)
