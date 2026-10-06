#!/usr/bin/env python3
"""Ordinary source/control fixtures and explicit real Linux/Git/schema fixtures.

Offline source tests use authenticated parent bytes, never claim a runtime pass.
Real fixtures run only when explicitly selected and require actual current logs.
"""
from __future__ import annotations
import argparse, ast, contextlib, copy, importlib, io, json, os, pathlib
import signal, subprocess, sys, tempfile, time, unittest
import types
from unittest.mock import patch
import point4_smooth_master_composition as comp

OFFLINE=None
REAL=False
SCHEMA=None

def parent_inputs():
    if OFFLINE:
        pins=json.loads((OFFLINE/'PINNED-TREES.json').read_text(encoding='utf8'))
        master={x['path']:(x['mode'],x['sha']) for x in pins['master']['tree'] if x['type']=='blob'}
        support={x['path']:(x['mode'],x['sha']) for x in pins['support']['tree'] if x['type']=='blob'}
        def read(path):
            name='master' if path in master else 'support'
            data=(OFFLINE/'parent-sources'/name/path).read_bytes()
            assert comp.blob_id(data)==(master if name=='master' else support)[path][1]
            return data
    else:
        master,support=comp.parent_tree(comp.MASTER),comp.parent_tree(comp.SUPPORT)
        read=lambda path:comp.original_bytes(path,master,support)
    return master,support,read

class OrdinaryCompositionTests(unittest.TestCase):
    def test_exact_parent_resolution_and_omission_controls(self):
        master,support,_=parent_inputs()
        union=comp.resolve_union(master,support)
        self.assertEqual(len(union),1723)
        for path in comp.SHARED:self.assertEqual(union[path],master[path])
        for p in list(master)[:1]:
            wrong=dict(master);wrong.pop(p)
            with self.assertRaises(AssertionError):comp.resolve_union(wrong,support)
        wrong=dict(support);p=next(p for p in wrong if p not in comp.SHARED and p in master)
        wrong[p]=('100644','0'*40)
        with self.assertRaises(AssertionError):comp.resolve_union(master,wrong)

    def test_every_finite_transform_and_reverse_identity(self):
        master,support,read=parent_inputs()
        helper_sha=comp.sha256((comp.ROOT/comp.HELPER).read_bytes())
        mock=comp.transform(comp.FIXTURE,read(comp.FIXTURE),helper_sha)
        workflow=comp.transform(comp.WORKFLOW,read(comp.WORKFLOW),helper_sha)
        with patch.object(comp,'parent_tree',side_effect=lambda c:master if c==comp.MASTER else support):
            for path in comp.EDITED:
                original=read(path)
                changed=comp.transform(path,original,helper_sha,comp.sha256(mock),comp.sha256(workflow))
                if path==comp.WORKFLOW:
                    self.assertEqual(changed.replace(comp.WF_STEP.encode(),b'',1),original)
                else:
                    hook=comp.bootstrap(path,helper_sha).encode()
                    self.assertEqual(changed.count(hook),1)
                    without=changed.replace(hook,b'',1)
                    if path!=comp.SMOOTH:self.assertEqual(without,original)
                    else:
                        old=original.decode();new=without.decode()
                        a=old.index('FILE_SHA256 = ');b=old.index('\nADDED = ',a)
                        aa=new.index('FILE_SHA256 = ');bb=new.index('\nADDED = ',aa)
                        self.assertEqual(new[:aa]+old[a:b]+new[bb:],old)
                with self.assertRaises(AssertionError):comp.transform(path,changed,helper_sha,comp.sha256(mock),comp.sha256(workflow))
                anchor=comp.WF_ANCHOR if path==comp.WORKFLOW else comp.ENTRY
                for bad in (original.decode().replace(anchor,'',1),original.decode()+anchor):
                    with self.assertRaises(AssertionError):comp.transform(path,bad.encode(),helper_sha,comp.sha256(mock),comp.sha256(workflow))

    def test_tree_records_reject_duplicates_modes_and_truncation(self):
        good=b'100644 blob '+b'a'*40+b'\ta.lean\0'
        self.assertEqual(comp.parse_tree(good),{'a.lean':('100644','a'*40)})
        for bad in (good[:-1],good+good,good.replace(b'100644',b'120000'),good.replace(b'a.lean',b'../a.lean'),good.replace(b'a'*40,b'z'*40)):
            with self.assertRaises(AssertionError):comp.parse_tree(bad)

    def test_callback_failure_nested_ownership_and_restoration(self):
        original=object();namespace={'value':original};other={'value':original}
        try:
            with self.assertRaises(RuntimeError):
                with comp.replacements(namespace,{'value':'outer'}):
                    with self.assertRaises(AssertionError):
                        with comp.replacements(other,{'value':'wrong'}):pass
                    with comp.replacements(namespace,{'value':'inner'}):self.assertEqual(namespace['value'],'inner')
                    self.assertEqual(namespace['value'],'outer')
                    raise RuntimeError('ordinary requested failure')
        finally:
            self.assertIs(namespace['value'],original)
            self.assertEqual(comp._depth,0);self.assertIsNone(comp._owner)

    def test_weighted_leaf_restores_real_callback_slots_on_failure(self):
        before_imports,before_metadata=object(),object()
        helper=types.SimpleNamespace(check_imports=before_imports,check_metadata=before_metadata)
        local=types.SimpleNamespace(legacy_check_imports=object(),legacy_check_metadata=object())
        namespace={'expected_sources':lambda:{},'public_paths':lambda:set(),
            'historical_c2':lambda:helper,'_composition_original_public_paths':lambda:set()}
        before=dict(namespace)
        def failing(schema):
            changed=namespace['historical_c2']()
            self.assertIs(changed.check_imports,local.legacy_check_imports)
            self.assertIs(changed.check_metadata,local.legacy_check_metadata)
            raise RuntimeError('ordinary callback body failure')
        namespace['_composition_original_check_current']=failing
        with patch.object(comp,'verify_current',return_value={}),patch.object(comp.importlib,'import_module',return_value=local):
            with self.assertRaises(RuntimeError):comp.weighted_leaf(namespace)
        for name in before:self.assertIs(namespace[name],before[name])
        self.assertIs(helper.check_imports,before_imports);self.assertIs(helper.check_metadata,before_metadata)
        self.assertEqual(comp._depth,0);self.assertIsNone(comp._owner)

    def test_argument_paths_survive_checkout_changes(self):
        args=['--schema','schema.json','--audit-rc','1','--smooth-audit-json=verdict.json']
        normalized=comp.absolute_arguments(args)
        self.assertEqual(normalized[1],str(pathlib.Path('schema.json').resolve()))
        self.assertEqual(normalized[4],'--smooth-audit-json='+str(pathlib.Path('verdict.json').resolve()))
        self.assertEqual(args[1],'schema.json');self.assertEqual(normalized[2:4],args[2:4])
        with self.assertRaises(AssertionError):comp.absolute_arguments(['--schema'])

    def test_original_parser_unsupported_option_rejection(self):
        for path in ('curvature/scripts/point4_c2_initial_heat_source_test.py',
                     'curvature/scripts/point4_linear_heat_geometry_source_test.py',
                     'curvature/scripts/point4_manifold_heat_release_guard.py',
                     'curvature/scripts/point4_manifold_heat_source_test.py'):
            with contextlib.redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as failure:
                comp.evidence_parser(path).parse_args(['--unsupported-composition-option'])
            self.assertEqual(failure.exception.code,2)

    def test_call_graph_weighted_leaf_cannot_enter_outer_replay(self):
        source=(comp.ROOT/comp.HELPER).read_text(encoding='utf8');tree=ast.parse(source)
        leaf=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='weighted_leaf')
        names={n.func.id for n in ast.walk(leaf) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name)}
        self.assertFalse(names&{'historical','install_smooth','run_support_fixtures','install_weighted'})
        self.assertIn('replacements',names)

    def test_mock_definitions_and_deadlines_are_retained(self):
        _,_,read=parent_inputs();source=read(comp.FIXTURE)
        digest=comp.sha256((comp.ROOT/comp.HELPER).read_bytes())
        transformed=comp.transform(comp.FIXTURE,source,digest)
        self.assertEqual(transformed.replace(comp.bootstrap(comp.FIXTURE,digest).encode(),b'',1),source)
        self.assertEqual(transformed.count(b'timeout=120'),source.count(b'timeout=120'))

    def test_requested_schema_reaches_genuine_root_validation_before_module_import(self):
        # Fail-dispatch control only: no Git or unavailable schema runtime is
        # simulated as passing. The genuine validator is inspected below.
        with patch.object(comp,'verify_current',return_value={}),patch.object(comp,'current_root_schema',side_effect=RuntimeError('requested root-schema control failure')) as check:
            with self.assertRaisesRegex(RuntimeError,'root-schema control failure'):
                comp.current_evidence('curvature/scripts/point4_c2_initial_heat_source_test.py',['--schema','root.schema.json'])
            check.assert_called_once_with(pathlib.Path('root.schema.json'))
        tree=ast.parse((comp.ROOT/comp.HELPER).read_text(encoding='utf8'))
        validator=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='current_root_schema')
        calls=[n for n in ast.walk(validator) if isinstance(n,ast.Call)]
        self.assertTrue(any(isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='jsonschema' and n.func.attr=='validate' for n in calls))
        self.assertTrue(any(isinstance(n.func,ast.Attribute) and n.func.attr=='strict_yaml' for n in calls))
        self.assertTrue(any(isinstance(n,ast.Constant) and n.value=='curvature/formalization.yaml' for n in ast.walk(validator)))
        leaf=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='weighted_leaf')
        self.assertEqual(sum(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='current_root_schema' for n in ast.walk(leaf)),2)

    def test_direct_weighted_projects_current_inherited_evidence_without_weighted_probe_confusion(self):
        args=['--schema','root.schema.json','--axiom-dir','actual-probes','--audit-json','actual-audit.json',
              '--audit-rc','1','--probe-log','weighted-probe.log','--compile-log','weighted-compile.log']
        with patch.object(comp,'current_evidence',side_effect=RuntimeError('current inherited-evidence control failure')) as check:
            with self.assertRaisesRegex(RuntimeError,'inherited-evidence control failure'):
                comp.weighted_current_inherited_evidence({},args)
            check.assert_called_once_with('curvature/scripts/point4_manifold_heat_release_guard.py',
                ['--schema',str(pathlib.Path('root.schema.json').resolve()),'--axiom-dir',str(pathlib.Path('actual-probes').resolve()),
                 '--audit-json',str(pathlib.Path('actual-audit.json').resolve()),'--audit-rc','1'])

    def test_direct_weighted_and_smooth_postcheck_order_is_enforced(self):
        tree=ast.parse((comp.ROOT/comp.HELPER).read_text(encoding='utf8'))
        weighted=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='install_weighted')
        main=next(n for n in weighted.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        checks=[n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='weighted_current_inherited_evidence']
        original=next(n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='original_main')
        self.assertEqual(len(checks),2)
        self.assertLess(checks[0].lineno,original.lineno);self.assertGreater(checks[1].lineno,original.lineno)
        self.assertTrue(all(n.lineno>checks[1].lineno for n in ast.walk(main) if isinstance(n,ast.Return)))
        smooth=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='install_smooth')
        main=next(n for n in smooth.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        historical=next(n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='historical')
        post=next(n for n in ast.walk(main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='current_smooth_evidence')
        self.assertGreater(post.lineno,historical.lineno)

    def test_smooth_postcheck_dispatches_all_original_validators_without_replay(self):
        tree=ast.parse((comp.ROOT/comp.HELPER).read_text(encoding='utf8'))
        leaf=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='current_smooth_evidence')
        calls=[n for n in ast.walk(leaf) if isinstance(n,ast.Call)]
        named={n.func.id for n in calls if isinstance(n.func,ast.Name)}
        self.assertIn('current_evidence',named);self.assertIn('verify_current',named)
        self.assertFalse(named&{'historical','install_smooth','install_weighted','run_support_fixtures'})
        callbacks={n.func.slice.value for n in calls if isinstance(n.func,ast.Subscript) and isinstance(n.func.value,ast.Name) and n.func.value.id=='namespace' and isinstance(n.func.slice,ast.Constant)}
        self.assertTrue({'check_new_metadata','check_support_probe','check_completion_open','check_smooth_audit_open'}<=callbacks)
        self.assertTrue(any(isinstance(n.func,ast.Attribute) and n.func.attr=='validate' for n in calls))

def required_process(path,args):
    assert sys.platform.startswith('linux'), 'Real fixture requires Linux; no substitute runtime'
    argv=[sys.executable,'-B',str(comp.ROOT/path),*args]
    process=subprocess.Popen(argv,cwd=comp.ROOT,env=comp.ENV,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
    try:
        output,_=process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid,signal.SIGTERM)
        try:process.communicate(timeout=3)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL);process.communicate(timeout=3)
        raise
    finally:
        # Drain this fixture's owned descendants even after a successful owner.
        try:
            os.killpg(process.pid,signal.SIGTERM)
            until=time.monotonic()+3
            while time.monotonic()<until:
                try:os.killpg(process.pid,0)
                except ProcessLookupError:break
                time.sleep(.05)
            else:
                os.killpg(process.pid,signal.SIGKILL)
                until=time.monotonic()+3
                while time.monotonic()<until:
                    try:os.killpg(process.pid,0)
                    except ProcessLookupError:break
                    time.sleep(.05)
                else:raise AssertionError('Owned fixture process group failed to drain')
        except ProcessLookupError:pass
    return process.returncode,output

def current_smooth_arguments():
    observed=json.loads((pathlib.Path('/tmp')/'point4-smooth-forward-composition-inputs.log').read_text())
    assert observed['head']==comp.git('rev-parse','HEAD').decode().strip()
    args=observed['validated_current_arguments']
    required={'--schema','--probe-log','--axiom-dir','--audit-json','--audit-rc',
        '--smooth-probe-log','--smooth-completion-log','--smooth-completion-rc','--smooth-audit-json','--smooth-audit-rc'}
    assert required<=set(args), 'Actual complete current evidence is required'
    assert pathlib.Path(args[args.index('--schema')+1]).resolve()==SCHEMA.resolve()
    return args

class RealValidatorTests(unittest.TestCase):
    def test_genuine_weighted_base_route(self):
        code,output=required_process(comp.WEIGHTED,['--schema',str(SCHEMA)])
        self.assertEqual(code,0,output)
        self.assertIn('Source-only integration checks passed',output)
        self.assertIn('OPEN',output)

    def test_complete_original_localization_and_current_semantics(self):
        with tempfile.TemporaryDirectory(prefix='point4-current-localization-evidence-') as directory:
            manifest=pathlib.Path(directory)/'current.json'
            code,output=required_process(comp.LOCAL,['--schema',str(SCHEMA),'--manifest',str(manifest)])
            self.assertEqual(code,0,output)
            self.assertIn('HISTORICAL_VALIDATOR_BEGIN '+comp.LOCALIZATION,output)
            self.assertIn('Frozen five-module localization',output)
            data=json.loads(manifest.read_text());self.assertTrue(data['source_only'])
            historical=manifest.with_name(manifest.name+'.historical-'+comp.LOCALIZATION+'.json')
            self.assertEqual(json.loads(historical.read_text())['candidate'],comp.LOCALIZATION)

    def test_actual_two_parent_consistency_and_current_identity(self):
        code,output=required_process(comp.CONSISTENCY,[])
        self.assertEqual(code,0,output)
        self.assertIn('HISTORICAL_VALIDATOR_BEGIN '+comp.MASTER,output)
        self.assertIn('Exact two-parent union',output)

    def test_original_smooth_scope_and_current_real_evidence(self):
        args=current_smooth_arguments()
        code,output=required_process(comp.SMOOTH,args)
        self.assertEqual(code,0,output)
        self.assertIn('HISTORICAL_VALIDATOR_BEGIN '+comp.SUPPORT,output)
        self.assertIn('SMOOTH',output.upper())

    def test_actual_schema_axiom_completion_and_open_failures_restore(self):
        original_args=current_smooth_arguments()
        weighted=importlib.import_module('point4_weighted_hessian_release_guard')
        smooth=importlib.import_module('point4_smooth_forward_release_guard')
        names=('check_current','historical_gate','expected_sources','public_paths','historical_c2')
        before={name:getattr(weighted,name) for name in names}
        with tempfile.TemporaryDirectory(prefix='point4-current-negative-evidence-') as directory:
            for flag,modify in (
                ('--schema',lambda text:text+'\nincorrect official schema digest\n'),
                ('--smooth-probe-log',lambda text:text.replace('propext','Hidden.unapproved_axiom',1)),
                ('--smooth-completion-log',lambda text:text+'extra ordinary completion diagnostic\n'),
                ('--audit-json',lambda text:text.replace('"build_run": true','"build_run": false',1)),
                ('--smooth-audit-json',lambda text:text.replace('"full_build": true','"full_build": false',1)),
            ):
                index=original_args.index(flag)+1;source=pathlib.Path(original_args[index]).read_text()
                bad=modify(source);self.assertNotEqual(bad,source,flag)
                file=pathlib.Path(directory)/(flag[2:]+'.log');file.write_text(bad)
                args=list(original_args);args[index]=str(file)
                with contextlib.redirect_stdout(io.StringIO()),self.assertRaises((AssertionError,subprocess.CalledProcessError)):
                    smooth.main(args)
                for name in names:self.assertIs(getattr(weighted,name),before[name])
                self.assertEqual(comp._depth,0);self.assertIsNone(comp._owner)
                comp.verify_current()

    def test_current_identity_omissions_map_mode_and_transform_failures(self):
        # These are ordinary current source mutations in this owned fixture;
        # each is restored before the next check and cannot qualify a runtime.
        for path in sorted(comp.EDITED|{comp.MAP}):
            file=comp.ROOT/path;original=file.read_bytes()
            try:
                file.write_bytes(original+b'\nincorrect ordinary source transformation\n')
                with self.assertRaises(AssertionError):comp.verify_current()
            finally:file.write_bytes(original)
        file=comp.ROOT/comp.DOC;mode=file.stat().st_mode
        try:
            file.chmod(mode|0o111)
            with self.assertRaises(AssertionError):comp.verify_current()
        finally:file.chmod(mode)
        for path in sorted(comp.WEIGHTED_MISSING|set(comp.NEW)):
            file=comp.ROOT/path;original=file.read_bytes()
            try:
                file.unlink()
                with self.assertRaises((AssertionError,FileNotFoundError)):comp.verify_current()
            finally:file.write_bytes(original)
        extra=comp.ROOT/'ordinary-unregistered-source.py'
        self.assertFalse(extra.exists())
        try:
            extra.write_text('# ordinary unregistered public source control\n')
            with self.assertRaises(AssertionError):comp.verify_current()
        finally:extra.unlink()
        comp.verify_current()

    def test_real_unsupported_options_fail(self):
        for path in (comp.SMOOTH,comp.LOCAL,comp.CONSISTENCY,comp.WEIGHTED):
            code,output=required_process(path,['--unsupported-composition-option'])
            self.assertNotEqual(code,0,output)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--real-runtime',action='store_true');parser.add_argument('--schema',type=pathlib.Path)
    parser.add_argument('--parent-fixtures',type=pathlib.Path)
    args=parser.parse_args();OFFLINE=args.parent_fixtures;SCHEMA=args.schema;REAL=args.real_runtime
    assert not REAL or (sys.platform.startswith('linux') and SCHEMA and SCHEMA.is_file()), 'Actual Linux/schema input required'
    suite=unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(OrdinaryCompositionTests))
    if REAL:suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(RealValidatorTests))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
