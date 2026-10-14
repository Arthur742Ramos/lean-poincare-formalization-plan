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
PINNED_LIBRARY_NOTE_SOURCE = b'/-\nCopyright (c) 2022 Gabriel Ebner. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Gabriel Ebner\n-/\nmodule\n\npublic meta import Lean.Elab.Command\n\npublic meta section\n\n/-!\n# Define the `library_note` command.\n-/\n\nnamespace Batteries.Util\n\nopen Lean\n\n/-- A library note is identified by the name of its declaration, and its content should be contained\nin its doc-string. -/\n@[expose] def LibraryNote := Unit\nderiving Inhabited\n\nnamespace LibraryNote\n\n/-- Entry for library notes in the environment extension.\n\nWe only store the name, and look up the constant\'s docstring to find its contents.\n-/\n@[expose] def LibraryNoteEntry := Name\nderiving Inhabited\n\n/-- Encode a name to be safe for the Lean export format.\n\nThe current export format (used by `lean4export` and consumed by external type checkers like\n`nanoda_lib`) does not support whitespace in declaration names. Library notes often have\nhuman-readable names with spaces like `\xc2\xabmy library note\xc2\xbb`, which would produce declarations\nlike `LibraryNote.\xc2\xabmy library note\xc2\xbb` that cannot be exported.\n\nThis function replaces spaces with underscores to produce export-safe names like\n`LibraryNote.my_library_note`.\n-/\ndef encodeNameForExport (n : Name) : Name :=\n  n.componentsRev.foldl (init := .anonymous) fun acc c =>\n    match c with\n    | .str _ s => .str acc (s.replace " " "_")\n    | .num _ k => .num acc k\n    | .anonymous => acc\n\n/-- Environment extension supporting `library_note`. -/\ninitialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) \xe2\x86\x90\n  registerSimplePersistentEnvExtension {\n    addEntryFn := Array.push\n    addImportedFn := Array.flatMap id\n  }\n\nopen Elab Command in\n/-- `library_note \xc2\xabmy note\xc2\xbb /-- documentation -/` creates a library note named `my note`\nin the `LibraryNote` namespace, whose content is `/-- documentation -/`.\nThis can then be cross-referenced using\n```\n-- See note [some tag]\n```\nin doc-comments.\nYou can access the contents using, for example, `#print LibraryNote.my_note`.\n(Note: spaces in the name are converted to underscores in the declaration name for\ncompatibility with the Lean export format.)\nUse `#help note "some tag"` to display all notes with the tag `"some tag"` in the infoview.\nThis command can be imported from Batteries.Tactic.HelpCmd .\n-/\nelab "library_note " name:ident ppSpace dc:docComment : command => do\n  let origName := name.getId\n  -- Store original name (with spaces) for lookup via `#help note`\n  modifyEnv (libraryNoteExt.addEntry \xc2\xb7 origName)\n  -- Use encoded name (spaces \xe2\x86\x92 underscores) for declaration, for export format compatibility\n  let safeName := encodeNameForExport origName\n  let stx \xe2\x86\x90 `(\n    $dc:docComment\n    meta def $(mkIdent (`_root_.LibraryNote ++ safeName)) : LibraryNote :=\n      default)\n  elabCommandTopLevel stx\n'
PINNED_LOGIC_SOURCE = b'/-\nCopyright (c) 2014 Microsoft Corporation. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro\n-/\nmodule\n\npublic import Batteries.Tactic.Alias\n\n@[expose] public section\n\ninstance {f : \xce\xb1 \xe2\x86\x92 \xce\xb2} [DecidablePred p] : DecidablePred (p \xe2\x88\x98 f) :=\n  inferInstanceAs <| DecidablePred fun x => p (f x)\n\n/-! ## id -/\n\ntheorem Function.id_def : @id \xce\xb1 = fun x => x := rfl\n\n/-! ## decidable -/\n\nprotected alias \xe2\x9f\xa8Decidable.exists_not_of_not_forall, _\xe2\x9f\xa9 := Decidable.not_forall\n\n/-! ## classical logic -/\n\nnamespace Classical\n\nalias \xe2\x9f\xa8exists_not_of_not_forall, _\xe2\x9f\xa9 := not_forall\n\nend Classical\n\n/-! ## equality -/\n\ntheorem heq_iff_eq {a b : \xce\xb1} : a \xe2\x89\x8d b \xe2\x86\x94 a = b := \xe2\x9f\xa8eq_of_heq, heq_of_eq\xe2\x9f\xa9\n\n@[simp] theorem eq_rec_constant {\xce\xb1 : Sort _} {a a\' : \xce\xb1} {\xce\xb2 : Sort _} (y : \xce\xb2) (h : a = a\') :\n    (@Eq.rec \xce\xb1 a (fun _ _ => \xce\xb2) y a\' h) = y := by cases h; rfl\n\ntheorem congrArg\xe2\x82\x82 (f : \xce\xb1 \xe2\x86\x92 \xce\xb2 \xe2\x86\x92 \xce\xb3) {x x\' : \xce\xb1} {y y\' : \xce\xb2}\n    (hx : x = x\') (hy : y = y\') : f x y = f x\' y\' := by subst hx hy; rfl\n\ntheorem congrFun\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) :\n    f a b = g a b :=\n  congrFun (congrFun h _) _\n\ntheorem congrFun\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n      {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) (c : \xce\xb3 a b) :\n    f a b c = g a b c :=\n  congrFun\xe2\x82\x82 (congrFun h _) _ _\n\ntheorem funext\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : \xe2\x88\x80 a b, f a b = g a b) : f = g :=\n  funext fun _ => funext <| h _\n\ntheorem funext\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : \xe2\x88\x80 a b c, f a b c = g a b c) : f = g :=\n  funext fun _ => funext\xe2\x82\x82 <| h _\n\nprotected theorem Eq.congr (h\xe2\x82\x81 : x\xe2\x82\x81 = y\xe2\x82\x81) (h\xe2\x82\x82 : x\xe2\x82\x82 = y\xe2\x82\x82) : x\xe2\x82\x81 = x\xe2\x82\x82 \xe2\x86\x94 y\xe2\x82\x81 = y\xe2\x82\x82 := by\n  subst h\xe2\x82\x81; subst h\xe2\x82\x82; rfl\n\ntheorem Eq.congr_left {x y z : \xce\xb1} (h : x = y) : x = z \xe2\x86\x94 y = z := by rw [h]\n\ntheorem Eq.congr_right {x y z : \xce\xb1} (h : x = y) : z = x \xe2\x86\x94 z = y := by rw [h]\n\nalias congr_arg := congrArg\nalias congr_arg\xe2\x82\x82 := congrArg\xe2\x82\x82\nalias congr_fun := congrFun\nalias congr_fun\xe2\x82\x82 := congrFun\xe2\x82\x82\nalias congr_fun\xe2\x82\x83 := congrFun\xe2\x82\x83\n\ntheorem heq_of_cast_eq : \xe2\x88\x80 (e : \xce\xb1 = \xce\xb2) (_ : cast e a = a\'), a \xe2\x89\x8d a\'\n  | rfl, rfl => .rfl\n\ntheorem cast_eq_iff_heq : cast e a = a\' \xe2\x86\x94 a \xe2\x89\x8d a\' :=\n  \xe2\x9f\xa8heq_of_cast_eq _, fun h => by cases h; rfl\xe2\x9f\xa9\n\ntheorem eqRec_eq_cast {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') :\n    @Eq.rec \xce\xb1 a motive x a\' e = cast (e \xe2\x96\xb8 rfl) x := by\n  subst e; rfl\n\n--Porting note: new theorem. More general version of `eqRec_heq`\ntheorem eqRec_heq_self {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') : @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d x := by\n  subst e; rfl\n\n@[deprecated eqRec_heq_iff (since := "12-07-2026")]\ntheorem eqRec_heq_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d y \xe2\x86\x94 x \xe2\x89\x8d y := by\n  subst e; rfl\n\n\n@[deprecated heq_eqRec_iff (since := "12-07-2026")]\ntheorem heq_eqRec_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    y \xe2\x89\x8d @Eq.rec \xce\xb1 a motive x a\' e \xe2\x86\x94 y \xe2\x89\x8d x := by\n  subst e; rfl\n\n/-! ## miscellaneous -/\n\n@[simp] theorem not_nonempty_empty  : \xc2\xacNonempty Empty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n@[simp] theorem not_nonempty_pempty : \xc2\xacNonempty PEmpty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n\n-- TODO(Mario): profile first, this is a dangerous instance\n-- instance (priority := 10) {\xce\xb1} [Subsingleton \xce\xb1] : DecidableEq \xce\xb1\n--   | a, b => isTrue (Subsingleton.elim a b)\n\n-- TODO(Mario): profile adding `@[simp]` to `eq_iff_true_of_subsingleton`\n\n/-- If all points are equal to a given point `x`, then `\xce\xb1` is a subsingleton. -/\ntheorem subsingleton_of_forall_eq (x : \xce\xb1) (h : \xe2\x88\x80 y, y = x) : Subsingleton \xce\xb1 :=\n  \xe2\x9f\xa8fun a b => h a \xe2\x96\xb8 h b \xe2\x96\xb8 rfl\xe2\x9f\xa9\n\ntheorem subsingleton_iff_forall_eq (x : \xce\xb1) : Subsingleton \xce\xb1 \xe2\x86\x94 \xe2\x88\x80 y, y = x :=\n  \xe2\x9f\xa8fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x\xe2\x9f\xa9\n\ntheorem congr_eqRec {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} (f : (x : \xce\xb1) \xe2\x86\x92 \xce\xb2 x \xe2\x86\x92 \xce\xb3) (h : x = x\') (y : \xce\xb2 x) :\n  f x\' (Eq.rec y h) = f x y := by cases h; rfl\n'

def execute_nodes(nodes, namespace):
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(HERE / 'chart_port_ci.py'), 'exec'), namespace)

def function(name, namespace):
    execute_nodes([next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == name)], namespace)
    return namespace[name]

def digest(data):
    return hashlib.sha256(data).hexdigest()

class DriverControls(unittest.TestCase):
    def model(self, setup_only, *, memory=LIMIT, quota=200000, invalid_pin=False, reject_probe=False, reject_configured=False, missing_extension_field=None, missing_extension_contract=False, short_extension=False, changed_extension_source=False, reject_extension_probe=False, changed_cache_source=False):
        import re
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            pkg, evidence, prefix, src = [root / p for p in ('curvature', 'evidence', 'compiler', 'sources')]
            for p in (pkg, evidence, prefix / 'bin', src / 'Cache'):
                p.mkdir(parents=True, exist_ok=True)
            (prefix / 'bin/lean').write_bytes(b'fixture compiler identity')
            # Cache bootstrap fixtures belong to the admitted dependency root.
            batteries = pkg / '.lake/packages/batteries'
            logic = batteries / 'Batteries/Logic.lean'
            logic.parent.mkdir(parents=True)
            logic.write_bytes(PINNED_LOGIC_SOURCE)
            library_note = batteries / 'Batteries/Util/LibraryNote.lean'
            library_note.parent.mkdir(parents=True)
            library_note.write_bytes(PINNED_LIBRARY_NOTE_SOURCE)
            (src / 'Mathlib').mkdir()
            (src / 'Mathlib/Fixture.lean').write_bytes(b'finite external source, never compiled\n')
            (pkg / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
            dep = pkg / '.lake/packages/mathlib'
            dep.mkdir(parents=True)
            (dep / 'Cache').mkdir()
            cache_originals = {'Cache/Main.lean': b'module\n', 'Cache/IO.lean': b'finite synthetic Cache.IO original; never compiled\n'}
            for name, data in cache_originals.items():
                (dep / name).write_bytes(data)
            if changed_cache_source:
                (dep / 'Cache/IO.lean').write_bytes(b'changed finite synthetic Cache.IO source\n')
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
            trace = dict(run=[], compile=[], cache_source_authentication=[], bootstrap_compile=[], extension_compile=[], extension_probe=[], admit=[], affinity=[], roots=[], root_receipt_written_before_admit=False)
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
                if label == 'lake-environment': return json.dumps({'LEAN_PATH': '', 'LEAN_SRC_PATH': os.pathsep.join((str(dep), str(src), str(batteries)))}).encode()
                return b'fixture log'
            def git(argv):
                if 'rev-parse' in argv:
                    if argv[-1] in ('HEAD:Cache/IO.lean', 'HEAD:Cache/Main.lean'):
                        self.assertEqual(argv[argv.index('-C') + 1], str(dep))
                        name = argv[-1].removeprefix('HEAD:')
                        source = dep / name
                        trace['cache_source_authentication'].append((source, digest(source.read_bytes())))
                        data = cache_originals[name]
                        return (hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() + '\n').encode()
                    if argv[-1] in ('HEAD:Batteries/Logic.lean', 'HEAD:Batteries/Util/LibraryNote.lean'):
                        data = (logic if argv[-1]=='HEAD:Batteries/Logic.lean' else library_note).read_bytes()
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
                target = 'bootstrap_compile' if args[5].startswith('cache-bootstrap-') else ('extension_compile' if args[5].startswith('ricci-extension-local-') else 'compile')
                trace[target].append(args)
            def check_extension_probe(data, contract):
                self.assertEqual(data, b'fixture log')
                self.assertEqual(contract['source_sha256'], next(row['sha256'] for row in extension_closure if row['module'] == contract['module']))
                trace['extension_probe'].append(contract['module'])
                if reject_extension_probe: raise AssertionError('Rejected finite extension probe')
                return {'fixture_extension_probe': contract['module']}
            def finite_cache_view(mathlib, compiler_prefix, official, env, owned):
                derived = owned / 'Cache/IO.lean'
                derived.parent.mkdir(parents=True)
                derived.write_bytes(b'finite synthetic derived Cache.IO; never compiled\n')
                return dict(env, POINT4_AUTHENTICATED_CACHE_LEANTAR='finite-fixture'), {'original': {'path': str(dep / 'Cache/IO.lean')}, 'derived': {'path': str(derived)}, 'finite_synthetic_only': True}
            def finite_cache_split(mathlib, lean, env, compiler_prefix, cache_source_view, names, inventory, bootstrap):
                # This is only the existing finite driver orchestration fixture.
                # Production manifest/process policy is tested independently below.
                planner = evidence / 'cache-source-view/CachePlan.lean'
                run([lean, '-j1', '-M5632', '-R', str(planner.parent), '--run', str(planner), *names],
                    'cache-hash-plan', env=env, timeout=1800)
                receipt['cache_phase_split'] = dict(finite_synthetic_source_context=True,
                    planner=str(planner), admitted_roots=list(names),
                    planner_reaped_before_acquisition=True, acquisition_zero_Lean=True,
                    physical_Source_POST='UNCHANGED')
            ns = dict(Path=fake_path, LIMIT=LIMIT, ROOT=root, PKG=pkg, EVIDENCE=evidence,
                args=types.SimpleNamespace(expected_sha='a' * 40, expected_tree='b' * 40, setup_only=setup_only),
                receipt=receipt, save=lambda: None, json=json, hashlib=hashlib, re=re,
                os=types.SimpleNamespace(sched_getaffinity=lambda _: {0, 1, 2},
                    sched_setaffinity=lambda _, cpus: trace['affinity'].append(cpus), environ={}, pathsep=os.pathsep),
                subprocess=types.SimpleNamespace(check_output=git), run=run, digest=digest, admit=admit,
                tree_entries=lambda *args: {}, package_root_relationships=roots,
                pinned_compiler_environment=lambda env,official: dict(env, PATH=str(Path(official['compiler_path']).parent)),
                prepare_pinned_cache_source_view=finite_cache_view,
                verify_pinned_cache_source_view=lambda context,env,official: self.assertEqual(env.get('POINT4_AUTHENTICATED_CACHE_LEANTAR'), 'finite-fixture'),
                ENV_KEY='POINT4_AUTHENTICATED_CACHE_LEANTAR',
                acquire_pinned_cache_phase_split=finite_cache_split,
                pinned_cache_query_context=lambda mathlib,names: dict(finite_synthetic_source_context=True,
                    package_root=str(mathlib),admitted_roots=list(names)),
                materialize_pinned_mathlib_cache=lambda *args: dict(finite_synthetic_copy=True),
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
        self.assertEqual([call[0] for call in trace['bootstrap_compile']], ['Cache.IO', 'Cache.Main'])
        self.assertIn('cache-source-view', str(trace['bootstrap_compile'][0][1]))
        originals = trace['cache_source_authentication']
        self.assertEqual([p.name for p, _ in originals], ['IO.lean', 'Main.lean'])
        self.assertTrue(all(p.parent.parent.name == 'mathlib' for p, _ in originals))
        self.assertEqual([h for _, h in originals], [digest(b'finite synthetic Cache.IO original; never compiled\n'), digest(b'module\n')])
        self.assertNotEqual(trace['bootstrap_compile'][0][1], originals[0][0])
        self.assertEqual(trace['bootstrap_compile'][1][1], originals[1][0])
        self.assertTrue(receipt['cache_source_view_removed_before_mathematics'])
        self.assertTrue(all(call[-1] is True for call in trace['compile']))
        self.assertEqual(len(trace['admit']), 3)
        probe = [r for r in trace['run'] if r[1] == 'full-type-proof-axiom-probe']
        self.assertEqual(len(probe), 1)
        self.assertEqual(probe[0][0][1:5], ['-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3'])
        bad_receipt, bad_trace, bad_failure = self.model(False, changed_cache_source=True)
        self.assertIsInstance(bad_failure, AssertionError)
        self.assertEqual(bad_receipt['build'], 'FAILED')
        self.assertEqual(bad_receipt['full_candidate_qualification'], 'NOT_RUN')
        self.assertEqual(bad_trace['bootstrap_compile'], [])
        self.assertEqual(bad_trace['compile'], [])

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

    def exercise(self, *, child_argv=None, race=False, disappear=False, unknown=False, snapshot_only=False, pages=2, overdue=False, missing_owner=False, exe_race=False, reverse_exe_race=False, reverse_order=False, child_state=None, terminal_change=None, terminal_read_error=None, zombie_survivor=False, owner_argv=None, cache_context=None, terminal_transition=False, terminal_fault_read=2):
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
                    if child_state=='Z' or terminal_transition:raise FileNotFoundError('finite terminal-transition executable absent')
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
                    if terminal_transition and stat_reads>=2:
                        prefix,tail=raw.rsplit(')',1);fields=tail.split()
                        fields[0]='Z';fields[21]='0';raw=prefix+') '+' '.join(fields)
                    if (child_state=='Z' or terminal_transition) and stat_reads==terminal_fault_read:
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
        cache=[row for row in trace['run'] if row[1]=='cache-hash-plan']
        self.assertEqual(len(cache),1)
        argv,label,kwargs=cache[0];context=receipt['cache_phase_split']
        self.assertTrue(context['finite_synthetic_source_context'])
        self.assertEqual(argv[3:7],['-R',str(Path(context['planner']).parent),'--run',context['planner']])
        self.assertEqual(argv[7:],context['admitted_roots'])
        self.assertTrue(context['planner_reaped_before_acquisition'])
        self.assertTrue(context['acquisition_zero_Lean'])
        self.assertEqual(context['physical_Source_POST'],'UNCHANGED')
        self.assertEqual(kwargs['timeout'],1800)
        self.assertEqual((receipt['fresh_combined_modules'],receipt['fresh_combined_probes']),(83,11))
        self.assertTrue(all('cache_query_context' not in row[2] for row in trace['run']))

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

class CombinedBootstrapImportControls(unittest.TestCase):
    """Actual pinned header/DFS regression; no Lean or native qualification."""
    PINNED = {'Batteries.Logic': {'data': b'/-\nCopyright (c) 2014 Microsoft Corporation. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro\n-/\nmodule\n\npublic import Batteries.Tactic.Alias\n\n@[expose] public section\n\ninstance {f : \xce\xb1 \xe2\x86\x92 \xce\xb2} [DecidablePred p] : DecidablePred (p \xe2\x88\x98 f) :=\n  inferInstanceAs <| DecidablePred fun x => p (f x)\n\n/-! ## id -/\n\ntheorem Function.id_def : @id \xce\xb1 = fun x => x := rfl\n\n/-! ## decidable -/\n\nprotected alias \xe2\x9f\xa8Decidable.exists_not_of_not_forall, _\xe2\x9f\xa9 := Decidable.not_forall\n\n/-! ## classical logic -/\n\nnamespace Classical\n\nalias \xe2\x9f\xa8exists_not_of_not_forall, _\xe2\x9f\xa9 := not_forall\n\nend Classical\n\n/-! ## equality -/\n\ntheorem heq_iff_eq {a b : \xce\xb1} : a \xe2\x89\x8d b \xe2\x86\x94 a = b := \xe2\x9f\xa8eq_of_heq, heq_of_eq\xe2\x9f\xa9\n\n@[simp] theorem eq_rec_constant {\xce\xb1 : Sort _} {a a\' : \xce\xb1} {\xce\xb2 : Sort _} (y : \xce\xb2) (h : a = a\') :\n    (@Eq.rec \xce\xb1 a (fun _ _ => \xce\xb2) y a\' h) = y := by cases h; rfl\n\ntheorem congrArg\xe2\x82\x82 (f : \xce\xb1 \xe2\x86\x92 \xce\xb2 \xe2\x86\x92 \xce\xb3) {x x\' : \xce\xb1} {y y\' : \xce\xb2}\n    (hx : x = x\') (hy : y = y\') : f x y = f x\' y\' := by subst hx hy; rfl\n\ntheorem congrFun\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) :\n    f a b = g a b :=\n  congrFun (congrFun h _) _\n\ntheorem congrFun\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n      {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : f = g) (a : \xce\xb1) (b : \xce\xb2 a) (c : \xce\xb3 a b) :\n    f a b c = g a b c :=\n  congrFun\xe2\x82\x82 (congrFun h _) _ _\n\ntheorem funext\xe2\x82\x82 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b, \xce\xb3 a b} (h : \xe2\x88\x80 a b, f a b = g a b) : f = g :=\n  funext fun _ => funext <| h _\n\ntheorem funext\xe2\x82\x83 {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} {\xce\xb3 : \xe2\x88\x80 a, \xce\xb2 a \xe2\x86\x92 Sort _} {\xce\xb4 : \xe2\x88\x80 a b, \xce\xb3 a b \xe2\x86\x92 Sort _}\n    {f g : \xe2\x88\x80 a b c, \xce\xb4 a b c} (h : \xe2\x88\x80 a b c, f a b c = g a b c) : f = g :=\n  funext fun _ => funext\xe2\x82\x82 <| h _\n\nprotected theorem Eq.congr (h\xe2\x82\x81 : x\xe2\x82\x81 = y\xe2\x82\x81) (h\xe2\x82\x82 : x\xe2\x82\x82 = y\xe2\x82\x82) : x\xe2\x82\x81 = x\xe2\x82\x82 \xe2\x86\x94 y\xe2\x82\x81 = y\xe2\x82\x82 := by\n  subst h\xe2\x82\x81; subst h\xe2\x82\x82; rfl\n\ntheorem Eq.congr_left {x y z : \xce\xb1} (h : x = y) : x = z \xe2\x86\x94 y = z := by rw [h]\n\ntheorem Eq.congr_right {x y z : \xce\xb1} (h : x = y) : z = x \xe2\x86\x94 z = y := by rw [h]\n\nalias congr_arg := congrArg\nalias congr_arg\xe2\x82\x82 := congrArg\xe2\x82\x82\nalias congr_fun := congrFun\nalias congr_fun\xe2\x82\x82 := congrFun\xe2\x82\x82\nalias congr_fun\xe2\x82\x83 := congrFun\xe2\x82\x83\n\ntheorem heq_of_cast_eq : \xe2\x88\x80 (e : \xce\xb1 = \xce\xb2) (_ : cast e a = a\'), a \xe2\x89\x8d a\'\n  | rfl, rfl => .rfl\n\ntheorem cast_eq_iff_heq : cast e a = a\' \xe2\x86\x94 a \xe2\x89\x8d a\' :=\n  \xe2\x9f\xa8heq_of_cast_eq _, fun h => by cases h; rfl\xe2\x9f\xa9\n\ntheorem eqRec_eq_cast {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') :\n    @Eq.rec \xce\xb1 a motive x a\' e = cast (e \xe2\x96\xb8 rfl) x := by\n  subst e; rfl\n\n--Porting note: new theorem. More general version of `eqRec_heq`\ntheorem eqRec_heq_self {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    (x : motive a rfl) {a\' : \xce\xb1} (e : a = a\') : @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d x := by\n  subst e; rfl\n\n@[deprecated eqRec_heq_iff (since := "12-07-2026")]\ntheorem eqRec_heq_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    @Eq.rec \xce\xb1 a motive x a\' e \xe2\x89\x8d y \xe2\x86\x94 x \xe2\x89\x8d y := by\n  subst e; rfl\n\n\n@[deprecated heq_eqRec_iff (since := "12-07-2026")]\ntheorem heq_eqRec_iff_heq {\xce\xb1 : Sort _} {a : \xce\xb1} {motive : (a\' : \xce\xb1) \xe2\x86\x92 a = a\' \xe2\x86\x92 Sort _}\n    {x : motive a rfl} {a\' : \xce\xb1} {e : a = a\'} {\xce\xb2 : Sort _} {y : \xce\xb2} :\n    y \xe2\x89\x8d @Eq.rec \xce\xb1 a motive x a\' e \xe2\x86\x94 y \xe2\x89\x8d x := by\n  subst e; rfl\n\n/-! ## miscellaneous -/\n\n@[simp] theorem not_nonempty_empty  : \xc2\xacNonempty Empty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n@[simp] theorem not_nonempty_pempty : \xc2\xacNonempty PEmpty := fun \xe2\x9f\xa8h\xe2\x9f\xa9 => h.elim\n\n-- TODO(Mario): profile first, this is a dangerous instance\n-- instance (priority := 10) {\xce\xb1} [Subsingleton \xce\xb1] : DecidableEq \xce\xb1\n--   | a, b => isTrue (Subsingleton.elim a b)\n\n-- TODO(Mario): profile adding `@[simp]` to `eq_iff_true_of_subsingleton`\n\n/-- If all points are equal to a given point `x`, then `\xce\xb1` is a subsingleton. -/\ntheorem subsingleton_of_forall_eq (x : \xce\xb1) (h : \xe2\x88\x80 y, y = x) : Subsingleton \xce\xb1 :=\n  \xe2\x9f\xa8fun a b => h a \xe2\x96\xb8 h b \xe2\x96\xb8 rfl\xe2\x9f\xa9\n\ntheorem subsingleton_iff_forall_eq (x : \xce\xb1) : Subsingleton \xce\xb1 \xe2\x86\x94 \xe2\x88\x80 y, y = x :=\n  \xe2\x9f\xa8fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x\xe2\x9f\xa9\n\ntheorem congr_eqRec {\xce\xb2 : \xce\xb1 \xe2\x86\x92 Sort _} (f : (x : \xce\xb1) \xe2\x86\x92 \xce\xb2 x \xe2\x86\x92 \xce\xb3) (h : x = x\') (y : \xce\xb2 x) :\n  f x\' (Eq.rec y h) = f x y := by cases h; rfl\n', 'sha256': 'dcfc3dd1580feebc8a29b6f9d65e32a0eadbce486fd02c5b1ce03c43fcf872ce', 'blob': '9b19aa8cc98740132dd729351050a08bb386474e'}, 'Batteries.Tactic.Alias': {'data': b'/-\nCopyright (c) 2017 Mario Carneiro. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Mario Carneiro, David Renshaw, Fran\xc3\xa7ois G. Dorais\n-/\nmodule\n\npublic meta import Lean.Elab.Command\npublic meta import Lean.Elab.DeclarationRange\npublic meta import Lean.Compiler.NoncomputableAttr\npublic meta import Lean.DocString\npublic meta import Batteries.CodeAction.Deprecated\n\npublic meta section\n\n/-!\n# The `alias` command\n\nThe `alias` command is used to create synonyms. The plain command can create a synonym of any\ndeclaration. There is also a version to create synonyms for the forward and reverse implications of\nan iff theorem.\n-/\n\nnamespace Batteries.Tactic.Alias\n\nopen Lean Elab Parser.Command\n\n/-- An alias can be in one of three forms -/\ninductive AliasInfo where\n  /-- Plain alias -/\n  | plain (n : Name)\n  /-- Forward direction of an iff alias -/\n  | forward (n : Name)\n  /-- Reverse direction of an iff alias -/\n  | reverse (n : Name)\nderiving Inhabited\n\n/-- The name underlying an alias target -/\ndef AliasInfo.name : AliasInfo \xe2\x86\x92 Name\n  | plain n => n\n  | forward n => n\n  | reverse n => n\n\n/-- The docstring for an alias. -/\ndef AliasInfo.toString : AliasInfo \xe2\x86\x92 String\n  | plain n => s!"**Alias** of `{n}`."\n  | forward n => s!"**Alias** of the forward direction of `{n}`."\n  | reverse n => s!"**Alias** of the reverse direction of `{n}`."\n\n/--\nAdd a docstring to the alias `declName` if it doesn\'t already have one.\nThis needs to run after elaboration of attributes, because e.g. `inherit_doc` could a add docstring.\nThis is also used in `to_additive`/`to_dual`.\n-/\ndef addAliasDocstring (declName : Name) (info : AliasInfo) : CoreM Unit := do\n  if (\xe2\x86\x90 findDocString? (\xe2\x86\x90 getEnv) declName).isNone then\n    let mut doc := info.toString\n    if let some origDoc \xe2\x86\x90 findDocString? (\xe2\x86\x90 getEnv) info.name then\n      doc := s!"{doc}\\n\\n---\\n\\n{origDoc}"\n    addDocStringCore declName doc\n\n/-- Environment extension for registering aliases -/\ninitialize aliasExt : MapDeclarationExtension AliasInfo \xe2\x86\x90 mkMapDeclarationExtension\n\n/-- Get the alias information for a name -/\ndef getAliasInfo?  [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) := do\n  return aliasExt.find? (\xe2\x86\x90 getEnv) name\n\n/-- Get the old alias information for a name. -/\npartial def getOldAliasInfo? [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) := do\n  match \xe2\x86\x90 getAliasInfo? name with\n  | some (.plain n) => getOldAliasInfo? n\n  | some (.forward n) =>\n    if let some (.plain n\') \xe2\x86\x90 getOldAliasInfo? n then\n      return some (.forward n\')\n    else\n      return some (.forward n)\n  | some (.reverse n) =>\n    if let some (.plain n\') \xe2\x86\x90 getOldAliasInfo? n then\n      return some (.reverse n\')\n    else\n      return some (.reverse n)\n  | none => return none\n\n/-- Get the alias information for a name -/\n@[deprecated "use `getAliasInfo?` or `getOldAliasInfo?` for the original behavior"\n  (since := "2026-04-11")]\ndef getAliasInfo [Monad m] [MonadEnv m] (name : Name) : m (Option AliasInfo) :=\n  getOldAliasInfo? name\n\n/-- Returns the path of aliases starting at a given name.\n\nThe return value is a pair `(mps, name)` where `name` is the final non-aliased name in the\nalias chain and `mps` is a list of `Bool` indicating the sequence of forward (`true`) and\nreverse (`false`) aliases along the chain.\n-/\npartial def getAliasPath [Monad m] [MonadEnv m] (name : Name) : m (List Bool \xc3\x97 Name) := do\n  match \xe2\x86\x90 getAliasInfo? name with\n  | some (.plain name) => getAliasPath name\n  | some (.forward name) =>\n    let (p, name) \xe2\x86\x90 getAliasPath name\n    return (true :: p, name)\n  | some (.reverse name) =>\n    let (p, name) \xe2\x86\x90 getAliasPath name\n    return (false :: p, name)\n  | none => return ([], name)\n\n/-- Set the alias info for a new declaration -/\ndef setAliasInfo [MonadEnv m] (info : AliasInfo) (declName : Name) : m Unit :=\n  modifyEnv (aliasExt.insert \xc2\xb7 declName info)\n\n/-- Updates the `deprecated` declaration to point to `target` if no target is provided. -/\ndef setDeprecatedTarget (target : Name) (arr : Array Attribute) : Array Attribute \xc3\x97 Bool :=\n  StateT.run (m := Id) (s := false) do\n    arr.mapM fun s => do\n      if s.name == `deprecated then\n        if let `(deprecated| deprecated%$tk $[$desc:str]? $[(since := $since)]?) := s.stx then\n          set true\n          let stx := Unhygienic.run\n            `(deprecated| deprecated%$tk $(mkCIdent target) $[$desc:str]? $[(since := $since)]?)\n          pure { s with stx }\n        else pure s\n      else pure s\n\n/--\n  The command `alias name := target` creates a synonym of `target` with the given name.\n\n  The command `alias \xe2\x9f\xa8fwd, rev\xe2\x9f\xa9 := target` creates synonyms for the forward and reverse directions\n  of an iff theorem. Use `_` if only one direction is required.\n\n  These commands accept all modifiers and attributes that `def` and `theorem` do.\n -/\nelab (name := alias) mods:declModifiers "alias " alias:ident " := " nameStx:ident : command => do\n  Lean.withExporting (isExporting := (\xe2\x86\x90 Command.getScope).isPublic) do\n  Command.liftTermElabM do\n    -- Whether we may access private `name`s here depends on whether it is a theorem, so first\n    -- resolve in private scope always\n    let name \xe2\x86\x90 withoutExporting <| realizeGlobalConstNoOverloadWithInfo nameStx\n    let cinfo \xe2\x86\x90 withoutExporting <| getConstInfo name\n    let declMods \xe2\x86\x90 elabModifiers mods\n    Lean.withExporting (isExporting := declMods.isInferredPublic (\xe2\x86\x90 getEnv)) do\n    unless wasOriginallyTheorem (\xe2\x86\x90 getEnv) name do\n      -- Now check again in correct scope for defs\n      discard <| realizeGlobalConstNoOverloadWithInfo nameStx\n    let (attrs, machineApplicable) := setDeprecatedTarget name declMods.attrs\n    let env \xe2\x86\x90 getEnv\n    let declMods := { declMods with\n      computeKind :=\n        if isNoncomputable env name then .noncomputable\n        else if isMarkedMeta env name then .meta\n        else declMods.computeKind\n      isUnsafe := declMods.isUnsafe || cinfo.isUnsafe\n      attrs\n    }\n    let (declName, _) \xe2\x86\x90 mkDeclName (\xe2\x86\x90 getCurrNamespace) declMods alias.getId\n    let decl : Declaration := if wasOriginallyTheorem (\xe2\x86\x90 getEnv) name then\n      .thmDecl { cinfo.toConstantVal with\n        name := declName\n        value := mkConst name (cinfo.toConstantVal.levelParams.map mkLevelParam)\n      }\n    else\n      .defnDecl { cinfo.toConstantVal with\n        name := declName\n        value := mkConst name (cinfo.levelParams.map mkLevelParam)\n        hints := .regular 0 -- FIXME\n        safety := if declMods.isUnsafe then .unsafe else .safe\n      }\n    checkNotAlreadyDeclared declName\n    addDecl decl\n    if !declMods.isNoncomputable then\n      if declMods.isMeta then\n        modifyEnv (markMeta \xc2\xb7 declName)\n      compileDecl decl\n    addDeclarationRangesFromSyntax declName (\xe2\x86\x90 getRef) alias\n    Term.addTermInfo\' alias (\xe2\x86\x90 mkConstWithLevelParams declName) (isBinder := true)\n    if let some doc := declMods.docString? then\n      addDocString declName (mkNullNode #[]) doc\n    enableRealizationsForConst declName\n    let info := AliasInfo.plain name\n    setAliasInfo info declName\n    Term.applyAttributes declName declMods.attrs\n    if machineApplicable then\n      modifyEnv (machineApplicableDeprecated.tag \xc2\xb7 declName)\n    addAliasDocstring declName info\n\n/--\nGiven a possibly forall-quantified iff expression `prf`, produce a value for one\nof the implication directions (determined by `mp`).\n-/\ndef mkIffMpApp (mp : Bool) (ty prf : Expr) : MetaM Expr := do\n  Meta.forallTelescope ty fun xs ty => do\n    let some (lhs, rhs) := ty.iff?\n      | throwError "Target theorem must have the form `\xe2\x88\x80 x y z, a \xe2\x86\x94 b`"\n    Meta.mkLambdaFVars xs <|\n      mkApp3 (mkConst (if mp then ``Iff.mp else ``Iff.mpr)) lhs rhs (mkAppN prf xs)\n\nprivate def addSide (mp : Bool) (declName : Name) (declMods : Modifiers) (thm : ConstantInfo) :\n    TermElabM Unit := do\n  checkNotAlreadyDeclared declName\n  let value \xe2\x86\x90 mkIffMpApp mp thm.type (mkConst thm.name (thm.levelParams.map mkLevelParam))\n  let type \xe2\x86\x90 Meta.inferType value\n  addDecl <| Declaration.thmDecl {\n    name := declName\n    value := value\n    type := type\n    levelParams := thm.levelParams\n  }\n  if let some doc := declMods.docString? then\n    addDocString declName (mkNullNode #[]) doc\n  let info := if mp then AliasInfo.forward thm.name else AliasInfo.reverse thm.name\n  setAliasInfo info declName\n  Term.applyAttributes declName declMods.attrs\n  addAliasDocstring declName info\n\n@[inherit_doc \xc2\xabalias\xc2\xbb]\nelab (name := aliasLR) mods:declModifiers "alias "\n    "\xe2\x9f\xa8" aliasFwd:binderIdent ", " aliasRev:binderIdent "\xe2\x9f\xa9" " := " name:ident : command => do\n  Lean.withExporting (isExporting := (\xe2\x86\x90 Command.getScope).isPublic) do\n  Command.liftTermElabM do\n    -- The target of an iff alias is always a theorem, so resolve in non-exporting mode to\n    -- support private theorem targets even when the aliases themselves are public.\n    let name \xe2\x86\x90 withoutExporting <| realizeGlobalConstNoOverloadWithInfo name\n    let thm \xe2\x86\x90 withoutExporting <| getConstInfo name\n    let declMods \xe2\x86\x90 elabModifiers mods\n    let declMods := { declMods with attrs := (setDeprecatedTarget name declMods.attrs).1 }\n    -- Now enter scope where we want to put the new decls\n    Lean.withExporting (isExporting := declMods.isInferredPublic (\xe2\x86\x90 getEnv)) do\n    if let `(binderIdent| $idFwd:ident) := aliasFwd then\n      let (declName, _) \xe2\x86\x90 mkDeclName (\xe2\x86\x90 getCurrNamespace) declMods idFwd.getId\n      addSide true declName declMods thm\n      addDeclarationRangesFromSyntax declName (\xe2\x86\x90 getRef) idFwd\n      Term.addTermInfo\' idFwd (\xe2\x86\x90 mkConstWithLevelParams declName) (isBinder := true)\n    if let `(binderIdent| $idRev:ident) := aliasRev then\n      let (declName, _) \xe2\x86\x90 mkDeclName (\xe2\x86\x90 getCurrNamespace) declMods idRev.getId\n      addSide false declName declMods thm\n      addDeclarationRangesFromSyntax declName (\xe2\x86\x90 getRef) idRev\n      Term.addTermInfo\' idRev (\xe2\x86\x90 mkConstWithLevelParams declName) (isBinder := true)\n', 'sha256': 'f8b2a18c6c39c653bda7d8dc38e55d5f692b446c8a7254d613eebb8386eb53d7', 'blob': '2ef7bd902bc7035ae4805293ea5485c7aa581ebb'}, 'Batteries.CodeAction.Deprecated': {'data': b'/-\nCopyright (c) 2023 Mario Carneiro. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Mario Carneiro\n-/\nmodule\n\npublic meta import Lean.Server.CodeActions.Provider\n\npublic meta section\n\n/-!\n# Code action for @[deprecated] replacements\n\nThis is an opt-in mechanism for making machine-applicable `@[deprecated]` definitions. When enabled\n(by setting the `machineApplicableDeprecated` tag attribute), a code action will be triggered\nwhenever the deprecation lint also fires, allowing the user to replace the usage of the deprecated\nconstant.\n-/\n\nnamespace Batteries\n\nopen Lean Elab Server Lsp RequestM CodeAction\n\n/-- An environment extension for identifying `@[deprecated]` definitions which can be auto-fixed -/\ninitialize machineApplicableDeprecated : TagDeclarationExtension \xe2\x86\x90 mkTagDeclarationExtension\n\nnamespace CodeAction\n\n/-- A code action which applies replacements for `@[deprecated]` definitions. -/\n@[code_action_provider]\ndef deprecatedCodeActionProvider : CodeActionProvider := fun params snap => do\n  let mut i := 0\n  let doc \xe2\x86\x90 readDoc\n  let mut msgs := #[]\n  for m in snap.msgLog.toList do\n    if m.data.isDeprecationWarning then\n      if h : _ then\n        msgs := msgs.push (snap.cmdState.messages.toList[i]\'h)\n    i := i + 1\n  if msgs.isEmpty then return #[]\n  let start := doc.meta.text.lspPosToUtf8Pos params.range.start\n  let stop := doc.meta.text.lspPosToUtf8Pos params.range.end\n  for msg in msgs do\n    let some endPos := msg.endPos | continue\n    let pos := doc.meta.text.ofPosition msg.pos\n    let endPos\' := doc.meta.text.ofPosition endPos\n    unless start \xe2\x89\xa4 endPos\' && pos \xe2\x89\xa4 stop do continue\n    let some (ctx, .node (.ofTermInfo info@{ expr := .const c .., ..}) _) :=\n      findInfoTree? identKind \xe2\x9f\xa8pos, endPos\'\xe2\x9f\xa9 none snap.infoTree fun _ i =>\n        (i matches .ofTermInfo { elaborator := .anonymous, expr := .const .., ..})\n      | continue\n    unless machineApplicableDeprecated.isTagged snap.cmdState.env c do continue\n    let some c\' := Linter.getDeprecatedNewName snap.cmdState.env c | continue\n    let eager : CodeAction := {\n      title := s!"Replace {c} with {c\'}"\n      kind? := "quickfix"\n      isPreferred? := true\n    }\n    return #[{\n      eager\n      lazy? := some do\n        let c\' \xe2\x86\x90 info.runMetaM ctx (unresolveNameGlobal c\')\n        let pos := doc.meta.text.leanPosToLspPos msg.pos\n        let endPos\' := doc.meta.text.leanPosToLspPos endPos\n        pure { eager with\n          edit? := some <| .ofTextEdit doc.versionedIdentifier {\n            range := \xe2\x9f\xa8pos, endPos\'\xe2\x9f\xa9\n            newText := toString c\'\n          }\n        }\n    }]\n  return #[]\n', 'sha256': 'eb8e4c2b5e86626e3fc291c77d31b29f036e788808d838df6c3b6d4f0d8a5b84', 'blob': '1cb2ba4a49dd27890007a520eb2437b75bbbb2de'}, 'Batteries.Util.LibraryNote': {'data': b'/-\nCopyright (c) 2022 Gabriel Ebner. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Gabriel Ebner\n-/\nmodule\n\npublic meta import Lean.Elab.Command\n\npublic meta section\n\n/-!\n# Define the `library_note` command.\n-/\n\nnamespace Batteries.Util\n\nopen Lean\n\n/-- A library note is identified by the name of its declaration, and its content should be contained\nin its doc-string. -/\n@[expose] def LibraryNote := Unit\nderiving Inhabited\n\nnamespace LibraryNote\n\n/-- Entry for library notes in the environment extension.\n\nWe only store the name, and look up the constant\'s docstring to find its contents.\n-/\n@[expose] def LibraryNoteEntry := Name\nderiving Inhabited\n\n/-- Encode a name to be safe for the Lean export format.\n\nThe current export format (used by `lean4export` and consumed by external type checkers like\n`nanoda_lib`) does not support whitespace in declaration names. Library notes often have\nhuman-readable names with spaces like `\xc2\xabmy library note\xc2\xbb`, which would produce declarations\nlike `LibraryNote.\xc2\xabmy library note\xc2\xbb` that cannot be exported.\n\nThis function replaces spaces with underscores to produce export-safe names like\n`LibraryNote.my_library_note`.\n-/\ndef encodeNameForExport (n : Name) : Name :=\n  n.componentsRev.foldl (init := .anonymous) fun acc c =>\n    match c with\n    | .str _ s => .str acc (s.replace " " "_")\n    | .num _ k => .num acc k\n    | .anonymous => acc\n\n/-- Environment extension supporting `library_note`. -/\ninitialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) \xe2\x86\x90\n  registerSimplePersistentEnvExtension {\n    addEntryFn := Array.push\n    addImportedFn := Array.flatMap id\n  }\n\nopen Elab Command in\n/-- `library_note \xc2\xabmy note\xc2\xbb /-- documentation -/` creates a library note named `my note`\nin the `LibraryNote` namespace, whose content is `/-- documentation -/`.\nThis can then be cross-referenced using\n```\n-- See note [some tag]\n```\nin doc-comments.\nYou can access the contents using, for example, `#print LibraryNote.my_note`.\n(Note: spaces in the name are converted to underscores in the declaration name for\ncompatibility with the Lean export format.)\nUse `#help note "some tag"` to display all notes with the tag `"some tag"` in the infoview.\nThis command can be imported from Batteries.Tactic.HelpCmd .\n-/\nelab "library_note " name:ident ppSpace dc:docComment : command => do\n  let origName := name.getId\n  -- Store original name (with spaces) for lookup via `#help note`\n  modifyEnv (libraryNoteExt.addEntry \xc2\xb7 origName)\n  -- Use encoded name (spaces \xe2\x86\x92 underscores) for declaration, for export format compatibility\n  let safeName := encodeNameForExport origName\n  let stx \xe2\x86\x90 `(\n    $dc:docComment\n    meta def $(mkIdent (`_root_.LibraryNote ++ safeName)) : LibraryNote :=\n      default)\n  elabCommandTopLevel stx\n', 'sha256': 'ecc6ebe4c32eb3c90bb94d0f4ef9eb8d530d95469ba48c0b1995f7c2172c93d8', 'blob': '4539971956d58b5a9e4785dd7c3cc364d9ae6875'}}

    def nodes(self):
        owner = next(n for n in TREE.body if isinstance(n, ast.Try))
        return {n.name: n for n in owner.body if isinstance(n, ast.FunctionDef)}

    def reader(self):
        import re
        ns = {'re': re, 'imports': admission.imports}
        execute_nodes([self.nodes()['cache_bootstrap_imports']], ns)
        return ns['cache_bootstrap_imports']

    def test_combined_headers_preserve_legacy_order_and_comment_exclusion(self):
        reader = self.reader()
        data = (b'import Cache.Legacy\n/- outer\npublic meta import Hidden.Comment\n'
                b'/- nested public meta import Hidden.Nested -/\n-/\n'
                b'public\tmeta import all Batteries.CodeAction.Deprecated Lean.Elab.Tactic.Basic -- ignored\n'
                b'meta import Lean.Hygiene\npublic import Batteries.Logic\n'
                b'-- public meta import Hidden.Line\nmeta public import Hidden.Invalid\n')
        legacy = ['Cache.Legacy', 'Lean.Hygiene', 'Batteries.Logic']
        self.assertEqual(admission.imports(data), legacy)
        self.assertEqual(reader(data), ['Cache.Legacy', 'Batteries.CodeAction.Deprecated',
                                      'Lean.Elab.Tactic.Basic', 'Lean.Hygiene', 'Batteries.Logic'])
        for name, row in self.PINNED.items():
            self.assertEqual(digest(row['data']), row['sha256'])
            blob = hashlib.sha1(b'blob ' + str(len(row['data'])).encode() + b'\0' + row['data']).hexdigest()
            self.assertEqual(blob, row['blob'])
        alias = reader(self.PINNED['Batteries.Tactic.Alias']['data'])
        self.assertEqual(alias, ['Lean.Elab.Command', 'Lean.Elab.DeclarationRange',
                                'Lean.Compiler.NoncomputableAttr', 'Lean.DocString',
                                'Batteries.CodeAction.Deprecated'])
        self.assertEqual(reader(self.PINNED['Batteries.CodeAction.Deprecated']['data']),
                         ['Lean.Server.CodeActions.Provider'])
        self.assertEqual(reader(self.PINNED['Batteries.Util.LibraryNote']['data']),['Lean.Elab.Command'])

    def test_actual_bootstrap_dfs_orders_pinned_dependencies_and_retains_rejections(self):
        import re
        with tempfile.TemporaryDirectory() as temp:
            pkg = Path(temp);root = pkg / '.lake/packages/batteries'
            root.mkdir(parents=True)
            rows = {name: row['data'] for name, row in self.PINNED.items()}
            paths = {}
            for name, data in rows.items():
                path = root / (name.replace('.', '/') + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                paths[name] = path
            expected = {path.relative_to(root).as_posix():
                        hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                        for name, data in rows.items() for path in [paths[name]]}
            def git(argv):
                self.assertEqual(argv[:4], ['git', '--no-replace-objects', '-C', str(root)])
                self.assertEqual(argv[4], 'rev-parse')
                self.assertTrue(argv[5].startswith('HEAD:'))
                return (expected[argv[5][5:]] + '\n').encode()
            def state(ready=None):
                ns = dict(re=re, imports=admission.imports, hashlib=hashlib,PKG=pkg,digest=digest,
                          dependency_roots=[root], subprocess=types.SimpleNamespace(check_output=git),
                          cache_order=[], seen=set(), active=set(),
                          source_path=lambda name: paths[name],
                          artifact_exists=ready or (lambda name: name.startswith('Lean.')))
                definitions = self.nodes()
                execute_nodes([definitions['verify_dependency_source'],
                               definitions['cache_bootstrap_imports'], definitions['bootstrap_visit']], ns)
                return ns
            ns = state()
            ns['bootstrap_visit']('Batteries.Logic')
            self.assertEqual([name for name, _ in ns['cache_order']],
                             ['Batteries.CodeAction.Deprecated', 'Batteries.Tactic.Alias', 'Batteries.Logic'])
            self.assertEqual(ns['active'], set())
            owner=next(n for n in TREE.body if isinstance(n,ast.Try))
            start=next(i for i,n in enumerate(owner.body) if isinstance(n,ast.Assign)
                       and any(isinstance(t,ast.Name) and t.id=='library_note_source' for t in n.targets))
            authenticated_root=owner.body[start:start+5]
            self.assertEqual(len(authenticated_root),5)
            execute_nodes(authenticated_root,ns)
            execute_nodes(authenticated_root,ns)
            self.assertEqual([name for name,_ in ns['cache_order']],
                ['Batteries.CodeAction.Deprecated','Batteries.Tactic.Alias','Batteries.Logic','Batteries.Util.LibraryNote'])
            self.assertEqual(ns['active'],set())
            wrong=state();wrong['source_path']=lambda name:paths['Batteries.Logic']
            with self.assertRaisesRegex(AssertionError,'LibraryNote source root drift'):execute_nodes(authenticated_root,wrong)
            note=paths['Batteries.Util.LibraryNote'];note_raw=note.read_bytes()
            try:
                for bad in (note_raw[:-1],note_raw+note_raw,note_raw.replace(b'namespace',b'namespacE',1)):
                    self.assertNotEqual(bad,note_raw);note.write_bytes(bad)
                    with self.assertRaises(AssertionError):execute_nodes(authenticated_root,state())
            finally:note.write_bytes(note_raw)
            bounded=state();bounded['cache_order']=[('already_owned',root)]*200
            with self.assertRaisesRegex(AssertionError,'finite source bound'):execute_nodes(authenticated_root,bounded)
            for name, data in rows.items():
                self.assertEqual(paths[name].read_bytes(), data)
            ns = state()
            with self.assertRaisesRegex(AssertionError, 'Unexpected cache bootstrap source'):
                ns['bootstrap_visit']('Unadmitted.Fixture')
            ns = state()
            ns['active'].add('Batteries.Logic')
            with self.assertRaises(AssertionError):
                ns['bootstrap_visit']('Batteries.Logic')
            alias = paths['Batteries.Tactic.Alias']
            original = alias.read_bytes()
            try:
                alias.write_bytes(original + b'\nchanged pinned dependency\n')
                ns = state()
                with self.assertRaises(AssertionError):
                    ns['bootstrap_visit']('Batteries.Logic')
            finally:
                alias.write_bytes(original)
            self.assertEqual(alias.read_bytes(), original)


import pathlib
from chart_port_artifacts import materialize_pinned_mathlib_cache as materialize

class CoherentNamespaceTests(unittest.TestCase):
 def fixture(self, root):
  source=root/'mathlib';cached=source/'.lake/build/lib/lean';owned=root/'owned';owned.mkdir()
  src=source/'Mathlib/Fixture/Module.lean';src.parent.mkdir(parents=True);raw=b'module\nimport Lean\n';src.write_bytes(raw)
  catalog={'Mathlib/Fixture/Module.lean':('100644','blob',hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest())}
  files={}
  for suffix in ('.olean','.olean.private','.olean.server','.ir.sig','.ir','.trace'):
   p=cached/('Mathlib/Fixture/Module'+suffix);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(suffix.encode());files[p]=p.read_bytes()
  return source,cached,owned,src,catalog,files

 def test_exact_cached_companions_and_input_bytes_retained_with_zero_fresh_build_credit(self):
  with tempfile.TemporaryDirectory() as tmp:
   source,cache,owned,src,catalog,files=self.fixture(pathlib.Path(tmp))
   result=materialize(cache,owned,source,catalog)
   self.assertEqual(result['fresh_local_compilations'],0)
   self.assertEqual(len(result['cached_companions']),5)
   self.assertFalse((owned/'Mathlib/Fixture/Module.trace').exists())
   for path,raw in files.items():
    self.assertEqual(path.read_bytes(),raw)
    if path.suffix!='.trace':self.assertEqual((owned/path.relative_to(cache)).read_bytes(),raw)

 def test_source_corruption_and_unknown_cached_module_fail_before_qualification(self):
  for mode in ('source','unknown'):
   with tempfile.TemporaryDirectory() as tmp:
    source,cache,owned,src,catalog,_=self.fixture(pathlib.Path(tmp))
    if mode=='source':src.write_bytes(src.read_bytes()+b'changed')
    else:(cache/'Mathlib/Unknown.olean').write_bytes(b'unknown')
    with self.assertRaises(AssertionError):materialize(cache,owned,source,catalog)

 def test_added_metadata_deleted_companion_and_added_directory_are_input_mutation(self):
  for mode in ('extra_metadata','deleted_companion','extra_directory'):
   with tempfile.TemporaryDirectory() as tmp:
    source,cache,owned,src,catalog,_=self.fixture(pathlib.Path(tmp));original=pathlib.Path.open;fired=[]
    def opened(path,*args,**kwargs):
     if args and args[0]=='xb' and not fired:
      fired.append(True)
      if mode=='extra_metadata':(cache/'Mathlib/Unexpected.trace').write_bytes(b'new')
      elif mode=='deleted_companion':(cache/'Mathlib/Fixture/Module.olean.server').unlink()
      else:(cache/'Mathlib/Unexpected').mkdir()
     return original(path,*args,**kwargs)
    with patch.object(pathlib.Path,'open',opened):
     with self.assertRaises((AssertionError,FileNotFoundError)):materialize(cache,owned,source,catalog)
    self.assertTrue(fired)

 def test_source_catalog_mutation_and_extra_owned_file_are_rejected(self):
  for mode in ('catalog','owned'):
   with tempfile.TemporaryDirectory() as tmp:
    source,cache,owned,src,catalog,_=self.fixture(pathlib.Path(tmp));original=pathlib.Path.open;fired=[]
    def opened(path,*args,**kwargs):
     if args and args[0]=='xb' and not fired:
      fired.append(True)
      if mode=='catalog':catalog['Mathlib/Added.lean']=('100644','blob','0'*40)
      else:(owned/'Mathlib/Unexpected.olean').write_bytes(b'extra')
     return original(path,*args,**kwargs)
    with patch.object(pathlib.Path,'open',opened):
     with self.assertRaises(AssertionError):materialize(cache,owned,source,catalog)
    self.assertTrue(fired)

 def test_cached_and_owned_ancestor_link_types_fail_closed(self):
  import os,stat
  for relative in ('.lake/build/lib','Mathlib/Fixture'):
   with tempfile.TemporaryDirectory() as tmp:
    source,cache,owned,src,catalog,_=self.fixture(pathlib.Path(tmp));original=pathlib.Path.lstat
    target=source/relative if relative.startswith('.') else cache/relative
    def lstat(path,*args,**kwargs):
     if path==target:
      actual=original(path,*args,**kwargs);values=list(actual);values[0]=stat.S_IFLNK|0o777;return os.stat_result(values)
     return original(path,*args,**kwargs)
    with patch.object(pathlib.Path,'lstat',lstat):
     with self.assertRaises(AssertionError):materialize(cache,owned,source,catalog)


class PackageRootResolutionTests(unittest.TestCase):
    def test_first_package_root_hides_a_later_complete_leaf(self):
        from chart_port_artifacts import artifact_status
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);first=root/'first';second=root/'second'
            (first/'Batteries').mkdir(parents=True)
            later=second/'Batteries/Lean/Position.olean';later.parent.mkdir(parents=True);later.write_bytes(b'fixture')
            result=artifact_status('Batteries.Lean.Position',[first,second],b'import Lean\n')
            self.assertFalse(result['ready'])
            self.assertEqual(result['selected_olean'],str(first/'Batteries/Lean/Position.olean'))
            self.assertEqual(artifact_status('Batteries.Lean.Position',[second],b'import Lean\n')['ready'],True)

    def test_all_module_companions_and_earlier_partial_root_remain_required(self):
        from chart_port_artifacts import artifact_status
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);first=root/'first';second=root/'second'
            for directory in (first,second):
                p=directory/'Mathlib/Fixture.olean';p.parent.mkdir(parents=True)
                for suffix in ('.olean','.olean.private','.olean.server','.ir.sig','.ir'):
                    p.with_name('Fixture'+suffix).write_bytes(b'fixture')
            for suffix in ('.olean','.olean.private','.olean.server','.ir.sig','.ir'):
                p=first/'Mathlib'/('Fixture'+suffix);p.unlink()
                self.assertFalse(artifact_status('Mathlib.Fixture',[first,second],b'module\n')['ready'])
                p.write_bytes(b'fixture')
            self.assertTrue(artifact_status('Mathlib.Fixture',[first,second],b'module\n')['ready'])

def function_source(name):
    return ast.get_source_segment(SOURCE, next(n for n in TREE.body if isinstance(n, ast.FunctionDef) and n.name == name))


class OfficialCompilerPathPrecedenceControls(unittest.TestCase):
    def helper(self):
        return function('pinned_compiler_environment', dict(Path=Path, os=os, stat=stat, digest=digest))

    def fixture(self, root):
        binary = root / 'official/bin' / ('lean.exe' if os.name == 'nt' else 'lean')
        binary.parent.mkdir(parents=True)
        binary.write_bytes(b'finite authenticated compiler-image fixture; never executed')
        binary.chmod(0o755)
        return binary, dict(compiler_path=str(binary), compiler_sha256=digest(binary.read_bytes()), compiler_commit=COMMIT)

    def test_official_directory_precedes_fake_launcher_without_mutating_environment(self):
        import shutil
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp).resolve();binary,official=self.fixture(root)
            fake=root/'earlier-launcher';fake.mkdir();launcher=fake/binary.name
            launcher.write_bytes(b'foreign launcher fixture; never executed');launcher.chmod(0o755)
            original={'PATH':str(fake), 'LEAN_PATH':'pinned-companions', 'LEAN_SRC_PATH':'pinned-sources', 'UNCHANGED':'value'}
            before=dict(original)
            self.assertEqual(Path(shutil.which(binary.name,path=original['PATH'])),launcher)
            self.assertEqual(Path(shutil.which('lean',path=original['PATH'])),launcher)
            changed=self.helper()(original,official)
            self.assertEqual(original,before);self.assertIsNot(changed,original)
            self.assertEqual(changed['PATH'],str(binary.parent)+os.pathsep+str(fake))
            self.assertEqual(Path(shutil.which(binary.name,path=changed['PATH'])),binary)
            self.assertEqual(Path(shutil.which('lean',path=changed['PATH'])),binary)
            self.assertEqual({k:v for k,v in changed.items() if k!='PATH'},{k:v for k,v in before.items() if k!='PATH'})
            for empty in ({},{'PATH':''}):
                self.assertEqual(self.helper()(empty,official)['PATH'],str(binary.parent))

    def test_wrong_stale_missing_nonregular_and_linked_compiler_fail_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp).resolve();binary,official=self.fixture(root);helper=self.helper()
            for key,value in (('compiler_commit','wrong'),('compiler_sha256','0'*64),('compiler_path',str(root/'missing')),
                              ('compiler_path',str(binary.parent)),('compiler_path','relative/lean')):
                altered=dict(official);altered[key]=value
                with self.subTest(key=key,value=value),self.assertRaises((AssertionError,OSError)):
                    helper({'PATH':'unchanged'},altered)
            raw=binary.read_bytes();binary.write_bytes(raw+b'!')
            with self.assertRaisesRegex(AssertionError,'digest drift'):helper({},official)
            binary.write_bytes(raw)
            real=Path.is_symlink
            for linked in (binary,binary.parent):
                # Portable predicate fixture, not a claim that Windows creates
                # or executes genuine Unix aliases.
                with patch.object(Path,'is_symlink',lambda p: p==linked or real(p)):
                    with self.assertRaisesRegex(AssertionError,'link'):helper({},official)
            with patch.object(os,'access',return_value=False):
                with self.assertRaisesRegex(AssertionError,'not executable'):helper({},official)

    def test_existing_query_and_monitor_still_reject_races_foreign_images_and_second_compilers(self):
        checks=OwnedProcessIdentityAndPrefixQuery()
        query,owner,official=checks.rows()
        self.assertTrue(checks.classify(query,owner,official))
        for field,value in (('stable',False),('exe','/foreign/lean'),('exe_sha256','0'*64),('ppid',999),
                            ('session',999),('argv',list(checks.stage_argv))):
            bad=dict(query);bad[field]=value
            self.assertFalse(checks.classify(bad,owner,official),field)
        for options in (dict(child_argv=list(checks.stage_argv)),dict(exe_race=True),dict(reverse_exe_race=True),
                        dict(race=True),dict(disappear=True),dict(unknown=True)):
            with self.subTest(options=options):
                stage,events,failure=checks.exercise(**options)
                self.assertIsInstance(failure,RuntimeError)
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'],2)
                self.assertTrue(stage['owner_reaped']);self.assertEqual(stage['remaining_session_pids'],[])
                self.assertEqual(events,[('kill',100,9),('wait',10)])

    def test_production_environment_is_selected_before_all_owned_bootstrap_and_native_descendants(self):
        owner=next(n for n in TREE.body if isinstance(n,ast.Try))
        calls=[(i,n) for i,n in enumerate(owner.body) if isinstance(n,ast.Assign)
               and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Name) and n.value.func.id=='pinned_compiler_environment']
        self.assertEqual(len(calls),1);index,node=calls[0]
        self.assertEqual(ast.dump(node,include_attributes=False),ast.dump(ast.parse('env = pinned_compiler_environment(env, receipt)').body[0],include_attributes=False))
        self.assertTrue(any(isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
            and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name)
            and n.value.func.value.id=='env' and n.value.func.attr=='update' for n in owner.body[:index]))
        for n in owner.body[:index]:
            self.assertFalse(any(isinstance(k,ast.Name) and k.id in ('bootstrap_visit','serial_compile','compiler_run') for k in ast.walk(n)))
        self.assertIn("if compilers > 1:",function_source('run'))
        self.assertIn("if not process['stable'] or process['errors']",function_source('is_exact_official_prefix_query'))

def cache_view_module():
    """Extract only the genuine production source-view helpers, never its driver."""
    names = {'IO_SHA', 'COMMIT', 'ENV_KEY', 'ORIGINAL', 'REPLACEMENT', 'sha', 'regular_seal',
             'derive_cache_io', 'verify_pinned_cache_source_view', 'prepare_pinned_cache_source_view'}
    nodes = [node for node in TREE.body if
             (isinstance(node, ast.FunctionDef) and node.name in names) or
             (isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id in names for target in node.targets))]
    self_names = {node.name if isinstance(node, ast.FunctionDef) else node.targets[0].id for node in nodes}
    assert self_names == names
    namespace = dict(Path=Path, os=os, stat=stat, hashlib=hashlib)
    execute_nodes(nodes, namespace)
    return types.SimpleNamespace(**namespace)

class AuthenticatedCacheSourceViewControls(unittest.TestCase):
    """Finite source/provenance regressions; no native compilation or SDK credit."""
    PINNED_IO_GZIP_BASE64 = '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'

    def fixture(self, root):
        import base64, gzip
        view = cache_view_module()
        original = gzip.decompress(base64.b64decode(self.PINNED_IO_GZIP_BASE64))
        self.assertEqual(digest(original), view.IO_SHA)
        mathlib, prefix = root / 'mathlib', root / 'observed-official'
        (mathlib / 'Cache').mkdir(parents=True)
        (mathlib / 'Cache/IO.lean').write_bytes(original)
        (mathlib / 'Cache/Main.lean').write_bytes(b'module\npublic import Cache.IO\n')
        (prefix / 'bin').mkdir(parents=True)
        for name in ('lean', 'leantar'):
            path = prefix / 'bin' / name
            path.write_bytes(('FINITE MOCK SDK IMAGE ' + name).encode())
            path.chmod(0o755)
        official = {'compiler_path': str(prefix / 'bin/lean'), 'compiler_sha256': digest((prefix / 'bin/lean').read_bytes()), 'compiler_commit': COMMIT}
        owned = root / 'owned-source-view'
        env, context = view.prepare_pinned_cache_source_view(mathlib, prefix, official, {'PATH': 'finite-fixture'}, owned)
        return view, mathlib, prefix, official, env, context, original

    def test_whole_pinned_inverse_preserves_imports_and_original_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            view, mathlib, prefix, official, env, context, original = self.fixture(Path(temp))
            derived = Path(context['derived']['path']).read_bytes()
            self.assertNotEqual(digest(derived), view.IO_SHA)
            self.assertEqual(derived.replace(view.REPLACEMENT, view.ORIGINAL), original)
            self.assertEqual(original.count(view.ORIGINAL), 1)
            self.assertEqual(derived.count(view.REPLACEMENT), 1)
            self.assertEqual(admission.imports(original), admission.imports(derived))
            self.assertEqual((mathlib / 'Cache/IO.lean').read_bytes(), original)
            self.assertEqual(env[view.ENV_KEY], str(prefix / 'bin/leantar'))
            self.assertIs(view.verify_pinned_cache_source_view(context, env, official), context)
            self.assertIs(context['compiled_source_is_original'], False)
            with self.assertRaises(AssertionError):
                view.derive_cache_io(original + b'\n-- source drift\n')

    def test_every_sealed_input_mutation_and_missing_input_is_rejected(self):
        for name in ('original', 'derived', 'compiler', 'leantar'):
            for mutation in ('bytes', 'missing', 'directory'):
                with self.subTest(input=name, mutation=mutation), tempfile.TemporaryDirectory() as temp:
                    view, mathlib, prefix, official, env, context, original = self.fixture(Path(temp))
                    path = Path(context[name]['path'])
                    if mutation == 'bytes':
                        path.write_bytes(path.read_bytes() + b'MUTATED')
                    else:
                        path.unlink()
                        if mutation == 'directory':
                            path.mkdir()
                    with self.assertRaises((AssertionError, OSError)):
                        view.verify_pinned_cache_source_view(context, env, official)

    def test_environment_and_provenance_labels_fail_closed(self):
        import copy
        with tempfile.TemporaryDirectory() as temp:
            view, mathlib, prefix, official, env, context, original = self.fixture(Path(temp))
            for replacement in (None, '', 'relative/leantar', str(prefix / 'bin/lean')):
                with self.subTest(environment=replacement):
                    changed = dict(env)
                    if replacement is None:
                        del changed[view.ENV_KEY]
                    else:
                        changed[view.ENV_KEY] = replacement
                    with self.assertRaisesRegex(AssertionError, 'controlled environment drift'):
                        view.verify_pinned_cache_source_view(context, changed, official)
            for key, value in [('role', 'MATHEMATICS'), ('mathlib_pin', '0' * 40), ('compiled_source_is_original', True), ('point4', 'COMPLETE'), ('policy_sha256', '0' * 64), ('extra', True)]:
                with self.subTest(field=key):
                    changed = copy.deepcopy(context)
                    changed[key] = value
                    with self.assertRaises(AssertionError):
                        view.verify_pinned_cache_source_view(changed, env, official)

    def test_owned_namespace_reparse_rejection_precedes_any_write(self):
        import types
        view = cache_view_module()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            original_lstat = Path.lstat
            def flagged(path):
                value = original_lstat(path)
                if path == root:
                    return types.SimpleNamespace(**{key: getattr(value, key) for key in ('st_mode', 'st_dev', 'st_ino', 'st_size', 'st_mtime_ns', 'st_ctime_ns')}, st_file_attributes=0x400)
                return value
            with patch.object(Path, 'lstat', flagged):
                with self.assertRaisesRegex(AssertionError, 'output ancestor reparse point'):
                    view.prepare_pinned_cache_source_view(root / 'unused-mathlib', root / 'unused-prefix', {}, {}, root / 'must-not-be-created')
            self.assertFalse((root / 'must-not-be-created').exists())
            self.assertEqual(list(root.iterdir()), [])

    def test_existing_owned_output_and_observed_prefix_drift_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            view, mathlib, prefix, official, env, context, original = self.fixture(Path(temp))
            owned = Path(context['owned_root'])
            before = {str(path): path.read_bytes() for path in owned.rglob('*') if path.is_file()}
            with self.assertRaisesRegex(AssertionError, 'output must be fresh and owned'):
                view.prepare_pinned_cache_source_view(mathlib, prefix, official, env, owned)
            self.assertEqual(before, {str(path): path.read_bytes() for path in owned.rglob('*') if path.is_file()})
            with self.assertRaisesRegex(AssertionError, 'observed prefix drift'):
                view.prepare_pinned_cache_source_view(mathlib, prefix / 'another', official, env, Path(temp) / 'new-owned')
            self.assertFalse((Path(temp) / 'new-owned').exists())

    def test_actual_bootstrap_dfs_forces_derived_io_and_complete_cache_namespace(self):
        with tempfile.TemporaryDirectory() as temp:
            view, mathlib, prefix, official, env, context, original = self.fixture(Path(temp))
            owner = next(node for node in TREE.body if isinstance(node, ast.Try))
            definitions = {node.name: node for node in owner.body if isinstance(node, ast.FunctionDef)}
            namespace = {'Path': Path, 'cache_source_view': context, 'cache_order': [], 'seen': set(), 'active': set(),
                         'source_path': lambda name: mathlib / (name.replace('.', '/') + '.lean'),
                         'artifact_exists': lambda name: True,
                         'verify_dependency_source': lambda source: self.assertEqual(source.read_bytes(), original if source.name == 'IO.lean' else b'module\npublic import Cache.IO\n'),
                         'cache_bootstrap_imports': lambda raw: ['Cache.IO'] if raw == b'module\npublic import Cache.IO\n' else []}
            execute_nodes([definitions['bootstrap_visit']], namespace)
            namespace['bootstrap_visit']('Cache.Main')
            self.assertEqual(namespace['cache_order'], [('Cache.IO', Path(context['derived']['path'])), ('Cache.Main', mathlib / 'Cache/Main.lean')])
            self.assertEqual((mathlib / 'Cache/IO.lean').read_bytes(), original)
            self.assertEqual(namespace['active'], set())
            body = ast.unparse(owner)
            self.assertIn("del env[ENV_KEY]", body)
            self.assertLess(body.index("del env[ENV_KEY]"), body.index("for i, row in enumerate(admission['closure'])"))
            for name in ('owned_process_identity', 'is_exact_official_prefix_query', 'run', 'compiler_run', 'serial_compile'):
                self.assertIn(name, SOURCE)



class OwnedTerminalLifecycleTransitionControls(unittest.TestCase):
    def exercise(self, **kwargs):
        return OwnedProcessIdentityAndPrefixQuery().exercise(**kwargs)

    def process(self, stage):
        return OwnedProcessIdentityAndPrefixQuery().process(stage, 101)

    def test_initial_running_child_requires_two_fresh_matching_terminal_observations(self):
        for reverse in (False, True):
            with self.subTest(reverse_order=reverse):
                stage, events, failure = self.exercise(child_state='R',
                    terminal_transition=True, reverse_order=reverse)
                self.assertIsNone(failure)
                row = self.process(stage)
                self.assertEqual(row['state'], 'R')
                self.assertFalse(row['stable'])
                self.assertNotIn('exe', row); self.assertNotIn('argv', row)
                self.assertEqual(row['errors'][0]['type'], 'FileNotFoundError')
                self.assertEqual(len(row['terminal_samples']), 2)
                for sample in row['terminal_samples']:
                    self.assertEqual(sample['state'], 'Z')
                    self.assertEqual(sample['rss_bytes'], 0)
                    for key in ('pid', 'ppid', 'pgrp', 'session', 'starttime_ticks'):
                        self.assertEqual(sample[key], row[key])
                self.assertTrue(row['verified_terminated_zombie'])
                self.assertEqual(row['terminal_errors'], [])
                self.assertTrue(row['conservative_executable_count'])
                self.assertFalse(row['counted_compiler'])
                self.assertFalse(row['exact_official_prefix_query'])
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 1)
                # Initial live RSS and session cleanup are not weakened.
                self.assertEqual(stage['peak_rss_bytes'], 4*4096)
                self.assertTrue(stage['owner_reaped'])
                self.assertEqual(stage['remaining_session_pids'], [])
                self.assertEqual(events, [('kill',100,9),('wait',10)])

    def test_either_fresh_terminal_sample_rejects_liveness_identity_or_rss_drift(self):
        for fault_read in (2, 3):
            for field in ('pid', 'ppid', 'pgrp', 'session', 'starttime_ticks', 'state', 'rss_bytes'):
                with self.subTest(fresh_sample=fault_read-1, field=field):
                    stage, _, failure = self.exercise(child_state='R',
                        terminal_transition=True, terminal_change=field,
                        terminal_fault_read=fault_read)
                    self.assertIsInstance(failure, RuntimeError)
                    self.assertEqual(str(failure), 'More than one Lean compiler in an owned stage')
                    row = self.process(stage)
                    self.assertEqual(len(row['terminal_samples']), 2)
                    self.assertFalse(row['verified_terminated_zombie'])
                    self.assertTrue(row['terminal_errors'])
                    self.assertTrue(row['conservative_executable_count'])
                    self.assertTrue(row['counted_compiler'])
                    self.assertFalse(row['exact_official_prefix_query'])
                    self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_absent_unreadable_or_malformed_fresh_stat_keeps_unknown_child_counted(self):
        for fault_read in (2, 3):
            for error in (FileNotFoundError, PermissionError, ValueError, IndexError):
                with self.subTest(fresh_sample=fault_read-1, error=error):
                    stage, _, failure = self.exercise(child_state='R',
                        terminal_transition=True, terminal_read_error=error,
                        terminal_fault_read=fault_read)
                    self.assertIsInstance(failure, RuntimeError)
                    row = self.process(stage)
                    self.assertFalse(row['verified_terminated_zombie'])
                    self.assertEqual(len(row['terminal_samples']), fault_read-2)
                    self.assertEqual(row['errors'][0]['type'], 'FileNotFoundError')
                    self.assertEqual(row['terminal_errors'][0]['type'], error.__name__)
                    self.assertTrue(row['counted_compiler'])
                    self.assertFalse(row['exact_official_prefix_query'])
                    self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_live_unknown_or_actual_second_compiler_has_no_terminal_exemption(self):
        for options in (dict(unknown=True), dict(child_argv=['/official/bin/lean','second.lean'])):
            with self.subTest(options=options):
                stage, _, failure = self.exercise(child_state='R', **options)
                self.assertIsInstance(failure, RuntimeError)
                row = self.process(stage)
                self.assertEqual(len(row['terminal_samples']), 2)
                self.assertTrue(all(sample['state']=='R' for sample in row['terminal_samples']))
                self.assertFalse(row['verified_terminated_zombie'])
                self.assertTrue(row['counted_compiler'])
                self.assertEqual(stage['owned_process_snapshot']['counted_compilers'], 2)

    def test_verified_terminal_child_still_cannot_survive_owned_session_cleanup(self):
        stage, _, failure = self.exercise(child_state='R',
            terminal_transition=True, zombie_survivor=True)
        self.assertIsInstance(failure, AssertionError)
        self.assertEqual(str(failure), 'Owned session not drained')
        self.assertTrue(self.process(stage)['verified_terminated_zombie'])
        self.assertEqual(stage['remaining_session_pids'], [101])
        self.assertTrue(stage['owner_reaped'])

# Proposed class to append to the existing chart control script. No tests run.
class CachePhaseSplitControls(unittest.TestCase):
    def api(self):
        import stat
        ns = dict(Path=Path, json=json, re=__import__('re'), os=os, stat=stat,
                  hashlib=hashlib, digest=digest)
        wanted = {'CACHE_SPLIT_PIN', 'CACHE_SPLIT_URLS', 'CACHE_SPLIT_UPSTREAM'}
        nodes = [n for n in TREE.body if (isinstance(n, ast.FunctionDef) and
                    (n.name.startswith('cache_split_') or n.name == 'acquire_pinned_cache_phase_split'))
                 or (isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id in wanted for t in n.targets))]
        execute_nodes(nodes, ns)
        return ns

    def plan(self, root):
        pkg = root / 'repo'; mathlib = pkg / '.lake/packages/mathlib'; cache = root / 'cache'
        a = 'Mathlib.A'; b = 'Batteries.B'
        source_a = str(mathlib / 'Mathlib/A.lean'); source_b = str(pkg / '.lake/packages/batteries/Batteries/B.lean')
        context = str(Path('.lake/packages/mathlib'))
        p = dict(schema='point4-cache-plan-v1', mathlib_pin=PIN, mathlib=str(mathlib), mathlib_context=context,
                 cwd=str(pkg), cache_dir=str(cache), roots=[a], source_search_path=[str(mathlib)],
                 root_hash_archive_spelling='0000000000000000.ltar', root_hash_generation=5,
                 full_hash_inputs=[dict(module=a, source=source_a), dict(module=b, source=source_b)],
                 modules=[dict(module=b, source=source_b, archive='0000000000000001.ltar', dependencies=[], extract=str(cache/'0000000000000001.ltar')),
                          dict(module=a, source=source_a, archive='0000000000000002.ltar', dependencies=[b], extract=dict(file=str(cache/'0000000000000002.ltar'), base=context))],
                 repo='leanprover-community/mathlib4', containers=['master','legacy'], compiler_or_acquisition_spawned=False)
        return p, [a], mathlib, cache, pkg, {source_a: {}, source_b: {}}

    def validate(self, p, *args):
        return self.api()['cache_split_validate_plan'](json.dumps(p).encode(), *args)

    def test_native_planner_generation_schema_and_strict_validator_types(self):
        producer = next(ast.literal_eval(node.value) for node in TREE.body
                        if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name)
                        and target.id == 'CACHE_PLAN_SOURCE' for target in node.targets))
        # These assertions bind the real Lean producer, whose Json.num self-check
        # runs in the already-required native planner before its output is printed.
        conversion = 'let generationJson := toJson rootHashGeneration.toNat'
        checked = 'match generationJson with\n    | .num _ => pure ()\n    | _ => throw <| IO.userError "Cache generation must serialize as a JSON number"'
        self.assertEqual(producer.count(conversion), 1)
        self.assertEqual(producer.count(checked), 1)
        self.assertEqual(producer.count('unless generationJson == toJson (5 : Nat) do'), 1)
        self.assertEqual(producer.count('("root_hash_generation", generationJson),'), 1)
        self.assertNotIn('("root_hash_generation", toJson rootHashGeneration),', producer)
        with tempfile.TemporaryDirectory() as directory:
            plan, *args = self.plan(Path(directory).resolve())
            self.assertEqual(self.validate(plan, *args), plan)
            for malformed in ('5', True, False, 5.0, 4, 6, None, []):
                with self.subTest(generation=malformed, value_type=type(malformed).__name__):
                    changed = dict(plan, root_hash_generation=malformed)
                    with self.assertRaises(AssertionError):
                        self.validate(changed, *args)

    def test_exact_root_closure_and_singleton_extraction_destinations(self):
        with tempfile.TemporaryDirectory() as d:
            p,*args=self.plan(Path(d).resolve()); self.assertEqual(self.validate(p,*args),p)

    def test_missing_admitted_root_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p,*args=self.plan(Path(d).resolve()); p['modules'].pop()
            with self.assertRaises(AssertionError): self.validate(p,*args)

    def test_duplicate_module_and_duplicate_archive_are_rejected(self):
        import copy
        with tempfile.TemporaryDirectory() as d:
            p,*args=self.plan(Path(d).resolve())
            for mutation in ('module','archive'):
                q=copy.deepcopy(p)
                if mutation=='module': q['modules'][1]['module']=q['modules'][0]['module']
                else: q['modules'][1]['archive']=q['modules'][0]['archive']
                with self.assertRaises(AssertionError): self.validate(q,*args)

    def test_extra_module_and_missing_dependency_are_rejected(self):
        import copy
        with tempfile.TemporaryDirectory() as d:
            p,*args=self.plan(Path(d).resolve())
            q=copy.deepcopy(p);q['modules'][1]['dependencies']=[]
            with self.assertRaises(AssertionError): self.validate(q,*args)
            q=copy.deepcopy(p);q['modules'][1]['dependencies']=['Batteries.Missing']
            with self.assertRaises(AssertionError): self.validate(q,*args)

    def test_wrong_extraction_base_and_source_provenance_are_rejected(self):
        import copy
        with tempfile.TemporaryDirectory() as d:
            p,*args=self.plan(Path(d).resolve())
            q=copy.deepcopy(p);q['modules'][1]['extract']['base']='outside'
            with self.assertRaises(AssertionError): self.validate(q,*args)
            q=copy.deepcopy(p);q['modules'][1]['source']=str(Path(d)/'unowned.lean')
            with self.assertRaises(AssertionError): self.validate(q,*args)

    def test_duplicate_json_keys_and_nonfinite_numbers_are_rejected(self):
        parse=self.api()['cache_split_json']
        for raw in ('{"a":1,"a":2}','{"a":NaN}','{"a":Infinity}'):
            with self.assertRaises((AssertionError,ValueError)): parse(raw)

    def transfers(self, codes, container='master', tool_exit=0):
        requested={'/owned/'+str(i)+'.part':'https://official/f/'+str(i) for i in range(len(codes))}
        rows=[dict(filename_effective=p,url_effective=u,http_code=code,exitcode=exitcode)
              for (p,u),(code,exitcode) in zip(requested.items(),codes)]
        raw=b'\n'.join(json.dumps(row).encode() for row in rows)
        return self.api()['cache_split_transfer_results'](raw,requested,container,tool_exit),rows,requested

    def test_every_successful_transfer_is_bound_to_actual_request(self):
        (records,served,misses,failures),_,requested=self.transfers([(200,0),(201,0)])
        self.assertEqual(served,set(requested));self.assertEqual(set(records),set(requested));self.assertFalse(misses or failures)

    def test_404_and_only_legacy_403_are_cache_misses(self):
        (r,s,m,f),_,_=self.transfers([(404,0),(403,0)])
        self.assertEqual(len(m),1);self.assertEqual(len(f),1)
        (r,s,m,f),_,_=self.transfers([(403,0)],'legacy')
        self.assertEqual(len(m),1);self.assertFalse(s or f)

    def test_http_success_with_transport_failure_cannot_promote(self):
        (r,s,m,f),_,_=self.transfers([(200,18)])
        self.assertFalse(s or m);self.assertEqual(len(f),1)

    def test_whole_process_nonzero_remains_hard_failure(self):
        (r,s,m,f),_,_=self.transfers([(200,0)],tool_exit=7)
        self.assertEqual(len(s),1);self.assertIn({'curl_process_exit':7},f)

    def test_missing_duplicate_and_extra_transfer_rows_are_rejected(self):
        _,rows,requested=self.transfers([(200,0),(200,0)])
        parse=self.api()['cache_split_transfer_results']
        for values in (rows[:1],rows+[rows[0]],rows+[dict(rows[0],filename_effective='/extra')]):
            with self.assertRaises(AssertionError): parse(b'\n'.join(json.dumps(r).encode() for r in values),requested,'master',0)

    def test_altered_url_and_malformed_status_are_rejected(self):
        _,rows,requested=self.transfers([(200,0)])
        parse=self.api()['cache_split_transfer_results']
        for key,value in (('url_effective','https://other/f/0'),('http_code',True),('exitcode','0')):
            row=dict(rows[0]);row[key]=value
            with self.assertRaises(AssertionError): parse(json.dumps(row).encode(),requested,'master',0)

    def process(self):
        image=[1,2,3,4,5]; argv=['/official/curl','--disable','--version']
        row=dict(pid=10,session=10,pgrp=10,argv=argv,stable=True,errors=[],exe=argv[0],image_identity=image,
                 recheck=dict(exe=argv[0],image_identity=image))
        tool=dict(path=argv[0],image_identity=image)
        return row,argv,tool

    def test_one_authenticated_noncompiler_owner_is_accepted(self):
        row,argv,tool=self.process();self.api()['cache_split_process_policy']([row],10,argv,tool)

    def test_lean_or_unknown_descendant_is_never_exempted(self):
        row,argv,tool=self.process();fn=self.api()['cache_split_process_policy']
        for child in (dict(pid=11,exe='/official/lean'),dict(pid=11)):
            with self.assertRaises(AssertionError): fn([row,child],10,argv,tool)

    def test_unreadable_live_owner_remains_rejected(self):
        row,argv,tool=self.process();row['stable']=False;row['errors']=[{'type':'FileNotFoundError'}]
        with self.assertRaises(AssertionError): self.api()['cache_split_process_policy']([row],10,argv,tool)

    def test_owner_image_argv_or_kernel_scope_drift_is_rejected(self):
        import copy
        row,argv,tool=self.process();fn=self.api()['cache_split_process_policy']
        for key,value in (('exe','/other/curl'),('argv',argv+['extra']),('session',11),('image_identity',[2,2,3,4,5])):
            changed=copy.deepcopy(row);changed[key]=value
            with self.assertRaises(AssertionError): fn([changed],10,argv,tool)

    def test_inherited_url_container_and_scope_overrides_fail_closed(self):
        fn=self.api()['cache_split_no_overrides'];fn({})
        for key in ('MATHLIB_CACHE_GET_URL','MATHLIB_CACHE_PUT_URL','MATHLIB_CACHE_FROM','MATHLIB_CACHE_REPO_SCOPE'):
            with self.assertRaises(AssertionError): fn({key:'unexpected'})

    def test_new_dependency_source_namespace_is_rejected(self):
        ns=self.api()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d).resolve();dep=root/'dep';dep.mkdir();(dep/'A.lean').write_text('module\n')
            ns['ROOT']=root; inventory={'dep':{'A.lean':('100644','blob','unused')}}
            ns['cache_split_source_namespace'](inventory)
            (dep/'Unexpected.lean').write_text('module\n')
            with self.assertRaises(AssertionError): ns['cache_split_source_namespace'](inventory)

    def stage_case(self, scenario):
        import types
        ns=self.api();events=[];record={'stages':[]};state={'done':False,'waited':False}
        with tempfile.TemporaryDirectory() as d:
            root=Path(d).resolve();procroot=root/'proc';procroot.mkdir()
            image_file=root/'finite-image';image_file.write_bytes(b'finite image, never executed')
            for pid in (70,71):
                q=procroot/str(pid);q.mkdir()
                fields=['S','1','70','70']+['0']*20;fields[19]='123';fields[21]=str(LIMIT//4096+1 if scenario=='rss' else 1)
                (q/'stat').write_text(str(pid)+' (curl) '+' '.join(fields))
            class ProcDir:
                def iterdir(self):
                    return [procroot/'70'] if not state['waited'] else ([procroot/'71'] if scenario=='survivor' else [])
            def path(value):return ProcDir() if str(value)=='/proc' else Path(value)
            argv=['/official/curl','--disable','--version'];image=[1,2,3,4,5]
            tool=dict(path=argv[0],sha256='a'*64,image_identity=image)
            class Proc:
                pid=70;returncode=None
                def poll(self):
                    if scenario=='poll_error':raise OSError('finite poll failure')
                    if state['done']:self.returncode=0;return 0
                    return None
                def wait(self,timeout):
                    events.append(('wait',timeout));state['waited']=True;self.returncode=0
                    if scenario=='wait_error':raise OSError('finite wait failure')
                    return 0
            def popen(actual,**kwargs):
                events.append(('spawn',actual))
                self.assertEqual(actual,argv);self.assertEqual(kwargs['executable'],'/proc/self/fd/'+str(state['fd']))
                self.assertEqual(kwargs['pass_fds'],(state['fd'],));self.assertTrue(kwargs['start_new_session'])
                if scenario!='stdin_close':self.assertEqual(kwargs['stdin'],-3)
                if scenario=='popen_error':raise OSError('finite spawn failure')
                kwargs['stderr'].write(b'x'*131072);kwargs['stdout'].write(b'finite stdout\n')
                return Proc()
            def observe(p,info):
                row=dict(pid=70,session=70,pgrp=70,argv=argv,stable=True,errors=[],exe=argv[0],image_identity=image,
                         recheck=dict(exe=argv[0],image_identity=image))
                if scenario=='unknown':row.update(stable=False,errors=[{'type':'FileNotFoundError'}]);row.pop('exe')
                return row
            probes=[]
            def resources():
                probes.append(1)
                events.append(('resources',len(probes)))
                if scenario=='pre_resource' and len(probes)==1:raise OSError('finite resource PRE failure')
                return {'memory':LIMIT,'affinity':[1] if scenario=='resource' and len(probes)>1 else [0]}
            def post(fd,tool):
                events.append(('tool_POST',))
                self.assertEqual(os.fstat(fd).st_size,len(b'finite image, never executed'))
                if scenario=='tool_post':raise OSError('finite tool POST failure')
            def close(fd):
                events.append(('close',fd))
                os.close(fd)
                if scenario=='fd_close':raise OSError('finite fd close failure')
            def opened(path):
                state['fd']=os.open(image_file,os.O_RDONLY)
                return state['fd'],tool
            class Input:
                def open(self,mode):return self
                def close(self):events.append(('stdin_close',));raise OSError('finite stdin close failure')
            original_path=path
            def path(value):return Input() if str(value)=='finite-input' else original_path(value)
            saves=[]
            def save():
                saves.append(1);events.append(('save',))
                if scenario=='pre_save' and len(saves)==1:raise OSError('finite initial save failure')
            class OutputPathFailure:
                def __truediv__(self,name):raise AssertionError('finite output path failure')
            ns.update(Path=path,LIMIT=LIMIT,PKG=root,EVIDENCE=OutputPathFailure() if scenario=='pre_path' else root,receipt=record,save=save,
                      cache_split_open_tool=opened,cache_split_tool_POST=post,
                      cache_split_resource_seal=resources,owned_process_identity=observe,
                      os=types.SimpleNamespace(name='posix',sysconf=lambda _:4096,close=close,
                         killpg=lambda pid,sig:events.append(('killpg',pid))),
                      signal=types.SimpleNamespace(SIGKILL=9),
                      subprocess=types.SimpleNamespace(Popen=popen,DEVNULL=-3),
                      time=types.SimpleNamespace(monotonic=lambda:101 if scenario=='timeout' and record['stages'] else 10,
                         sleep=lambda delay:state.update(done=True)))
            failure=None;result=None
            try:result=ns['cache_split_tool_stage'](argv,'finite-stage',{},100,'finite-input' if scenario=='stdin_close' else None)
            except BaseException as exc:failure=exc
            fd=state['fd'];self.assertIn(('close',fd),events)
            with self.assertRaises(OSError):os.fstat(fd)
            no_process={'popen_error','pre_resource','pre_save','pre_path'}
            if scenario not in no_process:
                self.assertIn(('killpg',70),events);self.assertIn(('wait',10),events)
            if scenario=='success':
                self.assertIsNone(failure);self.assertEqual(result[0],0);self.assertEqual(len(result[2]),131072)
                self.assertEqual(record['stages'][0]['remaining_session_pids'],[])
                self.assertEqual(record['stages'][0]['resources_PRE'],record['stages'][0]['resources_POST'])
            else:
                expected={
                    'rss':(AssertionError,'original 6GiB RSS bound'),
                    'unknown':(AssertionError,'Unreadable/raced acquisition owner'),
                    'timeout':(TimeoutError,'finite-stage'),
                    'poll_error':(OSError,'finite poll failure'),
                    'popen_error':(OSError,'finite spawn failure'),
                    'survivor':(AssertionError,'Acquisition session not drained'),
                    'resource':(AssertionError,'Acquisition resource PREPOST drift'),
                    'stdin_close':(OSError,'finite stdin close failure'),
                    'tool_post':(OSError,'finite tool POST failure'),
                    'fd_close':(OSError,'finite fd close failure'),
                    'wait_error':(OSError,'finite wait failure'),
                    'pre_resource':(OSError,'finite resource PRE failure'),
                    'pre_save':(OSError,'finite initial save failure'),
                    'pre_path':(AssertionError,'finite output path failure')}[scenario]
                self.assertIsInstance(failure,expected[0]);self.assertIn(expected[1],str(failure))
            self.assertIn(('tool_POST',),events)
            self.assertIn(('resources',2),events)
            self.assertEqual(events[-1],('save',))
            self.assertLess(events.index(('tool_POST',)),events.index(('close',fd)))
            if scenario not in no_process:
                self.assertLess(events.index(('spawn',argv)),events.index(('killpg',70)))
                self.assertLess(events.index(('killpg',70)),events.index(('wait',10)))
                self.assertLess(events.index(('wait',10)),events.index(('tool_POST',)))
            if scenario=='rss':self.assertGreater(record['stages'][0]['peak_rss_bytes'],LIMIT)

    def test_actual_tool_stage_cleanup_rss_timeout_and_large_stderr(self):
        for scenario in ('success','rss','unknown','timeout','poll_error','popen_error','survivor','resource',
                         'stdin_close','tool_post','fd_close','wait_error','pre_resource','pre_save','pre_path'):
            with self.subTest(scenario=scenario):self.stage_case(scenario)

    def test_acquisition_keeps_early_hard_failure_after_later_success(self):
        ns=self.api()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d).resolve();p,*args=self.plan(root);record={};labels=[]
            ns.update(EVIDENCE=root,receipt=record,save=lambda:None,
                      regular_seal=lambda path:(path.read_bytes(),{'sha256':digest(path.read_bytes())}))
            def run(argv,label,env,deadline,stdin_path=None):
                labels.append(label);self.assertNotEqual(label,'cache-extract','Hard failures must precede extraction')
                self.assertEqual(argv[1],'--disable');self.assertEqual(argv[argv.index('--retry')+1],'5')
                config=Path(argv[argv.index('--config')+1]).read_text();lines=config.splitlines();rows=[]
                for i in range(0,len(lines),2):
                    url=json.loads(lines[i].removeprefix('url = '));path=json.loads(lines[i+1].removeprefix('-o '))
                    code=(500 if i==0 else 404) if label=='cache-master' else 200
                    Path(path).write_bytes(b'finite archive')
                    rows.append(dict(filename_effective=path,url_effective=url,http_code=code,exitcode=0))
                return 0,b'\n'.join(json.dumps(row).encode() for row in rows),b''
            ns['cache_split_tool_stage']=run
            with self.assertRaisesRegex(AssertionError,'hard failure'):
                ns['cache_split_acquire'](p,{},'/official/curl','/official/leantar',100)
            self.assertEqual(labels,['cache-master','cache-legacy'])
            self.assertEqual(len(record['cache_acquisition']['archives']),2)
            self.assertEqual(len(record['cache_acquisition']['hard_failures']),1)

    def test_failed_unreaped_or_surviving_planner_cannot_admit_acquisition(self):
        fn=self.api()['cache_split_planner_completed']
        good=dict(exit_code=0,status='SUCCEEDED',owner_reaped=True,remaining_session_pids=[])
        fn(good)
        for key,value in (('exit_code',1),('status','FAILED'),('owner_reaped',False),('remaining_session_pids',[123])):
            changed=dict(good);changed[key]=value;acquired=[]
            with self.assertRaises(AssertionError):
                fn(changed);acquired.append(True)
            self.assertEqual(acquired,[])


if __name__ == '__main__':
    unittest.main(verbosity=2)
