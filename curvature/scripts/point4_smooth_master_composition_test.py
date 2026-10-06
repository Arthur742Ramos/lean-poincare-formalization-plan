#!/usr/bin/env python3
"""Ordinary source/control fixtures and explicit real Linux/Git/schema fixtures.

Offline source tests use authenticated parent bytes, never claim a runtime pass.
Real fixtures run only when explicitly selected and require actual current logs.
"""
from __future__ import annotations
import argparse, ast, contextlib, copy, importlib, io, json, os, pathlib
import signal, subprocess, sys, tempfile, time, unittest
import types, datetime, locale
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
                    self.assertEqual(changed.replace(comp.WF_STEP.encode(),b'',1).replace(comp.STARTUP_ENV.encode(),b'',1),original)
                elif path==comp.LOCALIZATION_WORKFLOW:
                    self.assertEqual(changed.replace(comp.STARTUP_ENV.encode(),b'',1).replace(comp.LOCALIZATION_MOCK_ROUTE_COMMAND.encode(),comp.LOCALIZATION_MOCK_COMMAND.encode(),1),original)
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
                anchor=comp.STARTUP_ANCHOR if path==comp.LOCALIZATION_WORKFLOW else comp.WF_ANCHOR if path==comp.WORKFLOW else comp.ENTRY
                for bad in (original.decode().replace(anchor,'',1),original.decode()+anchor):
                    with self.assertRaises(AssertionError):comp.transform(path,bad.encode(),helper_sha,comp.sha256(mock),comp.sha256(workflow))

    def test_tree_records_reject_duplicates_modes_and_truncation(self):
        good=b'100644 blob '+b'a'*40+b'\ta.lean\0'
        self.assertEqual(comp.parse_tree(good),{'a.lean':('100644','a'*40)})
        for bad in (good[:-1],good+good,good.replace(b'100644',b'120000'),good.replace(b'a.lean',b'../a.lean'),good.replace(b'a'*40,b'z'*40)):
            with self.assertRaises(AssertionError):comp.parse_tree(bad)

    def test_localization_startup_env_is_job_scoped_and_exactly_reversible(self):
        master,_,read=parent_inputs()
        original=read(comp.LOCALIZATION_WORKFLOW)
        self.assertEqual(comp.blob_id(original),master[comp.LOCALIZATION_WORKFLOW][1])
        changed=comp.transform(comp.LOCALIZATION_WORKFLOW,original,'0'*64)
        self.assertEqual(changed.replace(comp.STARTUP_ENV.encode(),b'',1).replace(comp.LOCALIZATION_MOCK_ROUTE_COMMAND.encode(),comp.LOCALIZATION_MOCK_COMMAND.encode(),1),original)
        self.assertEqual(changed.count(comp.STARTUP_ENV.encode()),1)
        self.assertLess(changed.index(comp.STARTUP_ENV.encode()),changed.index(b'    steps:\n'))
        self.assertLess(changed.index(comp.STARTUP_ENV.encode()),changed.index(b'python3 curvature/scripts/'))
        for bad in (original.replace(b'timeout-minutes: 350',b'timeout-minutes: 349'),
                    original.replace(b'    steps:\n',comp.STARTUP_ENV.encode()+b'    steps:\n',1)):
            with self.assertRaises(AssertionError):comp.transform(comp.LOCALIZATION_WORKFLOW,bad,'0'*64)

    def test_actual_python_startup_env_disables_bytecode_before_composition_import(self):
        # Actual ordinary interpreter startup, deliberately without -B. This
        # is not a simulated Git/schema check or a cache admission fixture.
        env=os.environ.copy()
        env['PYTHONDONTWRITEBYTECODE']='1'
        env['PYTHONPATH']=str(comp.ROOT/'curvature/scripts')
        result=subprocess.run([sys.executable,'-c',
            'import sys; assert sys.dont_write_bytecode; import point4_smooth_master_composition; assert sys.dont_write_bytecode'],
            cwd=comp.ROOT,env=env,capture_output=True,text=True,timeout=120)
        self.assertEqual(result.returncode,0,result.stderr)

    def test_localization_mock_route_is_fixed_and_wrapper_flag_is_stripped(self):
        # Deliberate ordinary dispatch failure; never a substitute for genuine
        # current semantic validation or the authenticated 29-test execution.
        namespace={'main':object()};original=namespace['main'];comp.install_localization(namespace)
        events=[]
        def history(commit,path,args):
            self.assertEqual(commit,comp.LOCALIZATION)
            self.assertNotIn(comp.LOCALIZATION_MOCK_FLAG,args)
            events.append(path)
            if path==comp.LOCALIZATION_MOCK:
                self.assertEqual(args,[])
                raise RuntimeError('ordinary fixed mock-route dispatch failure')
            self.assertEqual(path,comp.LOCAL)
            self.assertEqual(args,['--schema',str(pathlib.Path('schema.json').resolve())])
        with (patch.object(comp,'verify_current',side_effect=lambda:events.append('identity')),
              patch.object(comp,'localization_current',side_effect=lambda *args:events.append('current')),
              patch.object(comp,'historical',side_effect=history)):
            with self.assertRaisesRegex(RuntimeError,'fixed mock-route dispatch failure'):
                namespace['main'](['--schema','schema.json',comp.LOCALIZATION_MOCK_FLAG])
        self.assertEqual(events,['identity','current',comp.LOCAL,comp.LOCALIZATION_MOCK,'identity','current'])
        self.assertIs(namespace['_composition_original_main'],original)

    def test_localization_source_failure_runs_postchecks_and_stops_mock(self):
        namespace={'main':object()};comp.install_localization(namespace)
        with (patch.object(comp,'verify_current') as identity,patch.object(comp,'localization_current') as current,
              patch.object(comp,'historical',side_effect=RuntimeError('ordinary original source dispatch failure')) as history):
            with self.assertRaisesRegex(RuntimeError,'original source dispatch failure'):
                namespace['main'](['--schema','schema.json',comp.LOCALIZATION_MOCK_FLAG])
        self.assertEqual(identity.call_count,2);self.assertEqual(current.call_count,2)
        history.assert_called_once_with(comp.LOCALIZATION,comp.LOCAL,['--schema',str(pathlib.Path('schema.json').resolve())])

    def test_localization_prevalidation_failure_cannot_enter_history(self):
        namespace={'main':object()};comp.install_localization(namespace)
        with (patch.object(comp,'verify_current',side_effect=RuntimeError('ordinary current identity dispatch failure')),
              patch.object(comp,'localization_current') as current,patch.object(comp,'historical') as history):
            with self.assertRaisesRegex(RuntimeError,'current identity dispatch failure'):
                namespace['main'](['--schema','schema.json',comp.LOCALIZATION_MOCK_FLAG])
        current.assert_not_called();history.assert_not_called()

    def test_localization_mock_route_rejects_unknown_or_duplicate_wrapper_arguments(self):
        namespace={'main':object()};comp.install_localization(namespace)
        cases=([comp.LOCALIZATION_MOCK_FLAG],
            ['--schema','schema.json','--historical-localization-m'],
            ['--schema','schema.json',comp.LOCALIZATION_MOCK_FLAG+'=other'],
            ['--schema','schema.json','--historical-path','other.py'],
            ['--schema','schema.json','--historical-commit','0'*40],
            ['--schema','schema.json',comp.LOCALIZATION_MOCK_FLAG,comp.LOCALIZATION_MOCK_FLAG])
        for args in cases:
            with (contextlib.redirect_stderr(io.StringIO()),patch.object(comp,'verify_current') as identity,
                  patch.object(comp,'historical') as history,self.assertRaises(SystemExit) as failure):
                namespace['main'](args)
            self.assertEqual(failure.exception.code,2);identity.assert_not_called();history.assert_not_called()

    def test_localization_workflow_mock_command_replacement_is_count_one(self):
        _,_,read=parent_inputs();original=read(comp.LOCALIZATION_WORKFLOW)
        changed=comp.transform(comp.LOCALIZATION_WORKFLOW,original,'0'*64)
        self.assertEqual(changed.count(comp.LOCALIZATION_MOCK_ROUTE_COMMAND.encode()),1)
        self.assertNotIn(comp.LOCALIZATION_MOCK_COMMAND.encode(),changed)
        for bad in (original.replace(comp.LOCALIZATION_MOCK_COMMAND.encode(),b'',1),
                    original+comp.LOCALIZATION_MOCK_COMMAND.encode()):
            with self.assertRaises(AssertionError):comp.transform(comp.LOCALIZATION_WORKFLOW,bad,'0'*64)

    def test_smooth_startup_env_covers_nested_audit_without_changing_commands(self):
        _,_,read=parent_inputs()
        original=read(comp.WORKFLOW)
        changed=comp.transform(comp.WORKFLOW,original,'0'*64)
        self.assertEqual(changed.replace(comp.WF_STEP.encode(),b'',1).replace(comp.STARTUP_ENV.encode(),b'',1),original)
        self.assertEqual(changed.count(comp.STARTUP_ENV.encode()),1)
        self.assertLess(changed.index(comp.STARTUP_ENV.encode()),changed.index(b'    steps:\n'))
        self.assertLess(changed.index(comp.STARTUP_ENV.encode()),changed.index(b'bash scripts/point4_audit.sh'))
        for bad in (original.replace(b'timeout-minutes: 350',b'timeout-minutes: 349'),
                    original.replace(b'    steps:\n',comp.STARTUP_ENV.encode()+b'    steps:\n',1)):
            with self.assertRaises(AssertionError):comp.transform(comp.WORKFLOW,bad,'0'*64)

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

POSITIVE_SECONDS=1200
POSITIVE_RSS_BYTES=6*1024**3
POSITIVE_TERM=15
POSITIVE_KILL=9
POSITIVE_ROUTES={
    'weighted-full':comp.WEIGHTED,
    'localization-manifest-full':comp.LOCAL,
    'smooth-evidence-full':comp.SMOOTH,
    'localization-mocks-full':comp.LOCAL,
}

class PositiveResourceStop(AssertionError):pass

class PositiveInterrupted(AssertionError):pass

class _LinuxPositiveOwner:
    def __init__(self,process,argv):self.process=process;self.argv=argv
    def poll(self):return self.process.poll()
    def alive(self):
        try:os.killpg(self.process.pid,0);return True
        except ProcessLookupError:return False
    def send(self,kind):
        try:os.killpg(self.process.pid,kind);return True
        except ProcessLookupError:return False
    def rss(self):
        total=0;owner_high=0;members=[]
        for folder in pathlib.Path('/proc').iterdir():
            if not folder.name.isdecimal():continue
            try:
                before=(folder/'stat').read_text()
                fields=before[before.rindex(')')+2:].split()
                if int(fields[2])!=self.process.pid:continue
                assert int(fields[3])==self.process.pid, 'Owned group session drift'
                status=(folder/'status').read_text()
                after=(folder/'stat').read_text()
                if before.split(')')[-1].split()[19]!=after.split(')')[-1].split()[19]:continue
            except (FileNotFoundError,ProcessLookupError):continue
            values={line.split(':',1)[0]:line.split(':',1)[1].split()
                for line in status.splitlines() if ':' in line}
            def kb(name):
                value=values.get(name,['0','kB'])
                assert len(value)==2 and value[1]=='kB'
                return int(value[0])*1024
            total+=kb('VmRSS')
            if int(folder.name)==self.process.pid:owner_high=kb('VmHWM')
            members.append([int(folder.name),int(fields[19])])
        return total,owner_high,members

@contextlib.contextmanager
def _positive_signal_mask():
    if sys.platform.startswith('linux'):
        before=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGTERM,signal.SIGINT})
        try:yield
        finally:signal.pthread_sigmask(signal.SIG_SETMASK,before)
    else:yield # Ordinary fake-owner controls only; real launch requires Linux.

def _positive_cleanup(owner,record,monotonic,sleep):
    begin=monotonic()
    record.setdefault('term_requested',False);record.setdefault('kill_requested',False)
    record.setdefault('root_reaped',False);record.setdefault('group_drain_observed',False)
    try:
        with _positive_signal_mask():
            for kind,key in ((POSITIVE_TERM,'term_requested'),(POSITIVE_KILL,'kill_requested')):
                if not owner.alive():break
                record[key]=owner.send(kind)
                until=monotonic()+3
                while owner.alive() and monotonic()<until:
                    owner.poll()
                    sleep(min(.05,max(0,until-monotonic())))
            status=owner.poll()
            record['exit_code']=status
            record['root_reaped']=status is not None
            record['group_drain_observed']=not owner.alive()
            assert record['root_reaped'] and record['group_drain_observed'], 'Owned positive root/group failed to drain'
    finally:
        record['cleanup_elapsed_seconds']=monotonic()-begin
        record['cleanup_completed']=True

def _positive_controller(owner,record,monotonic=time.monotonic,sleep=time.sleep):
    # Injectable observation/clock adapters support finite ordinary controls.
    # Neither adapter nor record supplies a deadline or command selector.
    begin=record.get('monotonic_start',monotonic());primary=None;traceback=None;cleanup_error=None
    record.update(execution_limit_seconds=POSITIVE_SECONDS,cleanup_seconds=[3,3],
        aggregate_rss_stop_bytes=POSITIVE_RSS_BYTES,rss_sampling_seconds=.1,
        maximum_observed_group_rss_bytes=0,maximum_observed_owner_vm_hwm_bytes=0,
        term_requested=False,kill_requested=False,root_reaped=False,group_drain_observed=False,rss_samples=0)
    try:
        while True:
            status=owner.poll()
            if status is not None:record['stop_reason']='owner exit';break
            group_rss,owner_high,members=owner.rss()
            record['rss_samples']+=1
            record['maximum_observed_group_rss_bytes']=max(record['maximum_observed_group_rss_bytes'],group_rss)
            record['maximum_observed_owner_vm_hwm_bytes']=max(record['maximum_observed_owner_vm_hwm_bytes'],owner_high)
            record['last_observed_members']=members
            if group_rss>POSITIVE_RSS_BYTES:
                record['stop_reason']='sampled aggregate RSS exceeded fixed bound'
                raise PositiveResourceStop(record['stop_reason'])
            if monotonic()-begin>=POSITIVE_SECONDS:
                record['stop_reason']='execution timeout'
                raise subprocess.TimeoutExpired(owner.argv,POSITIVE_SECONDS)
            sleep(.1)
    except BaseException as error:
        primary=error;traceback=error.__traceback__
        record['primary_exception']=type(error).__name__
    finally:
        record['execution_elapsed_seconds']=monotonic()-begin
        try:
            _positive_cleanup(owner,record,monotonic,sleep)
        except BaseException as error:
            cleanup_error=error;record['cleanup_exception']=type(error).__name__+': '+str(error)
    if primary is not None:
        if cleanup_error is not None:primary.add_note('Positive cleanup failure: '+str(cleanup_error))
        raise primary.with_traceback(traceback)
    if cleanup_error is not None:raise cleanup_error
    return record['exit_code']

def _positive_finish(record,stdout_path,receipt_path):
    raw=stdout_path.read_bytes()
    record['stdout_stderr_bytes']=len(raw);record['stdout_stderr_sha256']=comp.sha256(raw)
    record['stdout_stderr_path']=str(stdout_path)
    # Exclusive receipt publication preserves failed runs and output bytes.
    with receipt_path.open('x',encoding='utf8') as handle:
        handle.write(json.dumps(record,indent=2)+'\n')
    return raw

def positive_route_process(route,args):
    assert sys.platform.startswith('linux'), 'Real positive fixture requires Linux; no substitute runtime'
    assert route in POSITIVE_ROUTES, 'Unknown positive route'
    path=POSITIVE_ROUTES[route]
    argv=[sys.executable,'-B',str(comp.ROOT/path),*args]
    allowed=sorted(os.sched_getaffinity(0))[:2]
    assert allowed, 'No admitted CPU available'
    # These small read-only identities precede launch; actual gates stay inside.
    head=comp.git('rev-parse','HEAD').decode().strip()
    if os.environ.get('EXPECTED_SHA'):assert head==os.environ['EXPECTED_SHA']
    record={'route':route,'head':head,'tree':comp.git('rev-parse','HEAD^{tree}').decode().strip(),
        'argv':argv,'entry_sha256':comp.sha256((comp.ROOT/path).read_bytes()),
        'test_sha256':comp.sha256((comp.ROOT/comp.TEST).read_bytes()),
        'helper_sha256':comp.sha256((comp.ROOT/comp.HELPER).read_bytes()),
        'toolchain':(comp.ROOT/'curvature/lean-toolchain').read_text().strip(),
        'mathlib':next(p['rev'] for p in json.loads((comp.ROOT/'curvature/lake-manifest.json').read_text())['packages'] if p['name']=='mathlib'),
        'utc_start':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'cpu_affinity':allowed,'rss_scope':'100ms sampled live group RSS and observed owner VmHWM; no exact aggregate peak claim',
        'rss_stop_scope':'sampled threshold, not a cgroup hard limit','pid':None,'pgid':None,
        'execution_limit_seconds':POSITIVE_SECONDS,'cleanup_seconds':[3,3],
        'aggregate_rss_stop_bytes':POSITIVE_RSS_BYTES,
        'qualification':'requires zero exit, original test assertions and observed root/group drain'}
    fd,name=tempfile.mkstemp(prefix='point4-smooth-forward-positive-'+route+'-',suffix='-stdout.log')
    stdout_path=pathlib.Path(name);receipt_path=stdout_path.with_name(stdout_path.name.replace('-stdout.log','-receipt.log'))
    output=None;primary=None;traceback=None;raw=b'';owner=None;saved={}
    record['monotonic_start']=time.monotonic()
    def interrupted(signum,frame):raise PositiveInterrupted('Controller signal '+str(signum))
    def teardown_error(stage,error):
        nonlocal primary,traceback
        record.setdefault('teardown_errors',[]).append({'stage':stage,'type':type(error).__name__,'message':str(error)})
        if primary is None:
            primary=error;traceback=error.__traceback__
            record.setdefault('primary_exception',type(error).__name__)
        else:primary.add_note('Positive '+stage+' failure: '+str(error))
    try:
        output=os.fdopen(fd,'wb')
        for kind in (signal.SIGTERM,signal.SIGINT):
            saved[kind]=signal.signal(kind,interrupted)
        child_mask=signal.pthread_sigmask(signal.SIG_BLOCK,set())
        def child_setup():
            os.sched_setaffinity(0,allowed)
            signal.pthread_sigmask(signal.SIG_SETMASK,child_mask)
        with _positive_signal_mask():
            process=subprocess.Popen(argv,cwd=comp.ROOT,env=comp.ENV,stdout=output,
                stderr=subprocess.STDOUT,start_new_session=True,
                preexec_fn=child_setup)
            owner=_LinuxPositiveOwner(process,argv)
            record.update(pid=process.pid,pgid=process.pid)
        code=_positive_controller(owner,record)
    except BaseException as error:
        # Capture identity/traceback before any output closure or restoration.
        primary=error;traceback=error.__traceback__
        record.setdefault('primary_exception',type(error).__name__)
    finally:
        # Cover interruption after owned launch but before controller entry.
        if owner is not None and not record.get('cleanup_completed'):
            try:_positive_cleanup(owner,record,time.monotonic,time.sleep)
            except BaseException as error:teardown_error('cleanup',error)
        try:
            if output is not None:output.close()
            else:os.close(fd)
        except BaseException as error:teardown_error('output close',error)
        for kind,handler in saved.items():
            try:signal.signal(kind,handler)
            except BaseException as error:teardown_error('signal restoration '+str(kind),error)
        record['utc_end']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        try:
            raw=stdout_path.read_bytes()
            _positive_finish(record,stdout_path,receipt_path)
        except BaseException as error:teardown_error('receipt',error)
    if primary is not None:
        if isinstance(primary,subprocess.TimeoutExpired):primary.output=raw
        raise primary.with_traceback(traceback)
    return code,raw.decode(locale.getpreferredencoding(False))

class PositiveControllerTests(unittest.TestCase):
    class Clock:
        def __init__(self):self.now=0.
        def read(self):return self.now
        def sleep(self,seconds):self.now+=seconds
    class Owner:
        argv=['fixed-positive-entry']
        def __init__(self,clock,exit_at=None,term_drains=False,kill_drains=True,rss=0,error=None):
            self.clock=clock;self.exit_at=exit_at;self.term_drains=term_drains;self.kill_drains=kill_drains
            self.rss_value=rss;self.error=error;self.dead=False;self.root_done=False;self.signals=[];self.polls=0
        def poll(self):
            self.polls+=1
            if self.dead or (self.exit_at is not None and self.clock.now>=self.exit_at):self.root_done=True;return 0
            return None
        def alive(self):return not self.dead
        def send(self,kind):
            self.signals.append((kind,self.clock.now))
            if (kind==POSITIVE_TERM and self.term_drains) or (kind==POSITIVE_KILL and self.kill_drains):self.dead=True
            return True
        def rss(self):
            if self.error is not None:raise self.error
            return self.rss_value,42,[[123,456]]
    def control(self,owner):
        record={}
        result=_positive_controller(owner,record,owner.clock.read,owner.clock.sleep)
        return result,record
    def test_success_reaps_root_and_observes_term_drain(self):
        clock=self.Clock();owner=self.Owner(clock,exit_at=.2,term_drains=True)
        code,record=self.control(owner)
        self.assertEqual(code,0);self.assertTrue(record['root_reaped']);self.assertTrue(record['group_drain_observed'])
        self.assertTrue(record['term_requested']);self.assertFalse(record['kill_requested'])
        self.assertEqual(record['maximum_observed_owner_vm_hwm_bytes'],42)
    def test_success_escalates_after_bounded_term_window(self):
        clock=self.Clock();owner=self.Owner(clock,exit_at=0)
        code,record=self.control(owner)
        self.assertEqual([s[0] for s in owner.signals],[POSITIVE_TERM,POSITIVE_KILL])
        self.assertAlmostEqual(owner.signals[1][1]-owner.signals[0][1],3,places=8)
        self.assertLessEqual(record['cleanup_elapsed_seconds'],6.000001)
        self.assertTrue(record['root_reaped'] and record['group_drain_observed'])
    def test_resource_stop_is_failure_and_retains_observations(self):
        clock=self.Clock();owner=self.Owner(clock,rss=POSITIVE_RSS_BYTES+1,term_drains=True);record={}
        with self.assertRaises(PositiveResourceStop):_positive_controller(owner,record,clock.read,clock.sleep)
        self.assertEqual(record['maximum_observed_group_rss_bytes'],POSITIVE_RSS_BYTES+1)
        self.assertEqual(record['maximum_observed_owner_vm_hwm_bytes'],42)
        self.assertTrue(record['root_reaped'] and record['group_drain_observed'])
    def test_primary_exception_identity_survives_cleanup_failure(self):
        clock=self.Clock();primary=RuntimeError('original observation failure')
        owner=self.Owner(clock,error=primary,kill_drains=False);record={}
        try:_positive_controller(owner,record,clock.read,clock.sleep)
        except RuntimeError as error:self.assertIs(error,primary);self.assertTrue(error.__notes__)
        else:self.fail('Original failure must propagate')
        self.assertFalse(record['group_drain_observed']);self.assertFalse(record['root_reaped'])
        self.assertAlmostEqual(record['cleanup_elapsed_seconds'],6,places=8)
    def test_successful_owner_with_undrained_group_cannot_pass(self):
        clock=self.Clock();owner=self.Owner(clock,exit_at=0,kill_drains=False);record={}
        with self.assertRaisesRegex(AssertionError,'failed to drain'):_positive_controller(owner,record,clock.read,clock.sleep)
        self.assertTrue(record['root_reaped']);self.assertFalse(record['group_drain_observed'])
        self.assertAlmostEqual(record['cleanup_elapsed_seconds'],6,places=8)
    def test_timeout_remains_timeout_and_cleanup_is_single_sequence(self):
        clock=self.Clock();owner=self.Owner(clock,term_drains=True);record={}
        # Advance virtual execution to the immutable budget without waiting.
        def sleep(seconds):clock.now+=1200 if seconds==.1 else seconds
        with self.assertRaises(subprocess.TimeoutExpired) as caught:
            _positive_controller(owner,record,clock.read,sleep)
        self.assertEqual(caught.exception.timeout,1200)
        self.assertEqual(owner.signals,[(POSITIVE_TERM,1200.)])
        self.assertTrue(record['root_reaped'] and record['group_drain_observed'])
    def test_stdout_bytes_and_failed_receipt_are_preserved_exclusively(self):
        with tempfile.TemporaryDirectory() as directory:
            output=pathlib.Path(directory)/'stdout.log';receipt=pathlib.Path(directory)/'receipt.log'
            raw=b'\x00\xff\r\npartial output\n';output.write_bytes(raw)
            record={'primary_exception':'TimeoutExpired','group_drain_observed':False}
            self.assertEqual(_positive_finish(record,output,receipt),raw)
            saved=json.loads(receipt.read_text());self.assertEqual(saved['stdout_stderr_sha256'],comp.sha256(raw))
            self.assertEqual(saved['stdout_stderr_bytes'],len(raw));self.assertFalse(saved['group_drain_observed'])
            with self.assertRaises(FileExistsError):_positive_finish(record,output,receipt)
            self.assertEqual(output.read_bytes(),raw)
    def test_fixed_route_table_and_original_120_helper_remain(self):
        self.assertEqual(set(POSITIVE_ROUTES),{'weighted-full','localization-manifest-full','smooth-evidence-full','localization-mocks-full'})
        self.assertEqual(POSITIVE_ROUTES['weighted-full'],comp.WEIGHTED)
        self.assertEqual(POSITIVE_ROUTES['smooth-evidence-full'],comp.SMOOTH)
        source=(comp.ROOT/comp.TEST).read_text(encoding='utf8');tree=ast.parse(source)
        helper=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='required_process')
        self.assertEqual(comp.sha256(ast.get_source_segment(source,helper).encode()),'b71a8710f1b5d58e850503cff65cc36a7f0a7d9b74d3f0ff4eb57a5317f1193b')
        cls=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='RealValidatorTests')
        calls=[n for n in ast.walk(cls) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='positive_route_process']
        self.assertEqual(len(calls),4);self.assertEqual({n.args[0].value for n in calls},set(POSITIVE_ROUTES))
    def test_launch_interrupt_preserves_primary_and_raw_output(self):
        clock=self.Clock();owner=self.Owner(clock,term_drains=True)
        process=types.SimpleNamespace(pid=123)
        primary=subprocess.TimeoutExpired(['original'],1200)
        raw=b'\x00\xff\r\npartial output\n'
        def launch(*args,**kwargs):kwargs['preexec_fn']();kwargs['stdout'].write(raw);return process
        # File-backed Popen capture is exercised; Linux ownership is a finite
        # adapter control, never presented as an actual Linux execution receipt.
        with tempfile.TemporaryDirectory() as directory:
            output=pathlib.Path(directory)/'control-stdout.log'
            def capture_file(*args,**kwargs):
                return os.open(str(output),os.O_WRONLY|os.O_CREAT|os.O_EXCL),str(output)
            with patch.object(sys,'platform','linux'),patch.object(os,'sched_getaffinity',return_value={0,1,2},create=True),\
                 patch.object(os,'sched_setaffinity',create=True) as affinity,\
                 patch.object(signal,'pthread_sigmask',return_value={2},create=True) as mask,\
                 patch.object(signal,'SIG_BLOCK',0,create=True),patch.object(signal,'SIG_SETMASK',2,create=True),\
                 patch.dict(os.environ,{'EXPECTED_SHA':'a'*40}),patch.object(comp,'git',return_value=b'a'*40+b'\n'),\
                 patch.object(tempfile,'mkstemp',side_effect=capture_file),\
                 patch.dict(globals(),{'_positive_signal_mask':contextlib.nullcontext}),\
                 patch.object(subprocess,'Popen',side_effect=launch),\
                 patch.dict(globals(),{'_LinuxPositiveOwner':lambda *args:owner,'_positive_controller':lambda *args:(_ for _ in ()).throw(primary)}):
                try:positive_route_process('weighted-full',['--schema','unchanged'])
                except subprocess.TimeoutExpired as error:self.assertIs(error,primary);self.assertEqual(error.output,raw)
                else:self.fail('Primary timeout must propagate')
                affinity.assert_called_once_with(0,[0,1])
                self.assertEqual(mask.call_args_list[-1].args,(2,{2}))
            self.assertEqual(output.read_bytes(),raw)
            receipt=json.loads(output.with_name('control-receipt.log').read_text())
            self.assertTrue(receipt['root_reaped'] and receipt['group_drain_observed'])
            self.assertEqual(receipt['stdout_stderr_sha256'],comp.sha256(raw))
        self.assertEqual(owner.signals,[(POSITIVE_TERM,0.)])
    def test_nonzero_exit_is_returned_without_success_conversion(self):
        clock=self.Clock();owner=self.Owner(clock);owner.dead=True;owner.poll=lambda:7
        code,record=self.control(owner)
        self.assertEqual(code,7);self.assertEqual(record['exit_code'],7)
        self.assertFalse(record['term_requested'] or record['kill_requested'])
    def test_positive_step_cap_preserves_job_and_original_commands(self):
        _,_,read=parent_inputs();original=read(comp.WORKFLOW)
        changed=comp.transform(comp.WORKFLOW,original,'0'*64)
        self.assertIn(b'        timeout-minutes: 125\n',changed)
        self.assertEqual(changed.count(b'    timeout-minutes: 350\n'),1)
        self.assertEqual(changed.replace(comp.WF_STEP.encode(),b'',1).replace(comp.STARTUP_ENV.encode(),b'',1),original)
    def teardown_case(self,primary,close_error=None,restore_error=None,receipt_error=None):
        # Inject failures at the real wrapper's teardown boundaries. All OS
        # owner observations are finite adapters; no Linux route is executed.
        clock=self.Clock();owner=self.Owner(clock,term_drains=True)
        raw=b'\x00\xff\r\ncontroller output\n';token=object();restored=[];closed=[];attempts=[]
        fdopen=os.fdopen;finish=_positive_finish
        class Capture:
            def __init__(self,fd):self.file=fdopen(fd,'wb')
            def write(self,value):return self.file.write(value)
            def close(self):
                closed.append(True);self.file.close()
                if close_error is not None:raise close_error
            def __enter__(self):return self
            def __exit__(self,*args):self.close()
        def signals(kind,handler):
            if handler is token:
                restored.append(kind)
                if kind==signal.SIGTERM and restore_error is not None:raise restore_error
            return token
        def controller(*args):
            if primary is not None:raise primary
            return 0
        def publish(*args):
            attempts.append(args[0])
            if receipt_error is not None:raise receipt_error
            return finish(*args)
        def launch(*args,**kwargs):kwargs['stdout'].write(raw);return types.SimpleNamespace(pid=123)
        with tempfile.TemporaryDirectory() as directory:
            output=pathlib.Path(directory)/'repair-stdout.log'
            def capture(*args,**kwargs):return os.open(str(output),os.O_WRONLY|os.O_CREAT|os.O_EXCL),str(output)
            with patch.object(sys,'platform','linux'),patch.object(os,'sched_getaffinity',return_value={0,1},create=True),\
                 patch.object(signal,'pthread_sigmask',return_value=set(),create=True),\
                 patch.object(signal,'SIG_BLOCK',0,create=True),patch.object(signal,'signal',side_effect=signals),\
                 patch.dict(os.environ,{'EXPECTED_SHA':'a'*40}),patch.object(comp,'git',return_value=b'a'*40+b'\n'),\
                 patch.object(tempfile,'mkstemp',side_effect=capture),patch.object(os,'fdopen',side_effect=lambda fd,*args:Capture(fd)),\
                 patch.object(subprocess,'Popen',side_effect=launch),\
                 patch.dict(globals(),{'_positive_signal_mask':contextlib.nullcontext,'_LinuxPositiveOwner':lambda *args:owner,
                    '_positive_controller':controller,'_positive_finish':publish}):
                expected=primary if primary is not None else close_error if close_error is not None else restore_error
                self.assertIsNotNone(expected)
                with self.assertRaises(type(expected)) as caught:positive_route_process('weighted-full',[])
                self.assertIs(caught.exception,expected)
                if isinstance(expected,subprocess.TimeoutExpired):self.assertEqual(expected.output,raw)
            self.assertEqual(output.read_bytes(),raw)
            self.assertEqual(closed,[True]);self.assertEqual(restored,[signal.SIGTERM,signal.SIGINT])
            self.assertEqual(len(attempts),1)
            self.assertTrue(attempts[0]['root_reaped'] and attempts[0]['group_drain_observed'])
            if receipt_error is None:
                saved=json.loads(output.with_name('repair-receipt.log').read_text())
                self.assertEqual(saved['stdout_stderr_sha256'],comp.sha256(raw))
                self.assertEqual(len(saved.get('teardown_errors',[])),int(close_error is not None)+int(restore_error is not None))
            else:self.assertFalse(output.with_name('repair-receipt.log').exists())
    def test_identical_timeout_survives_output_close_failure(self):
        self.teardown_case(subprocess.TimeoutExpired(['original'],1200),close_error=OSError('injected close failure'))
    def test_identical_timeout_survives_signal_restoration_failure(self):
        self.teardown_case(subprocess.TimeoutExpired(['original'],1200),restore_error=OSError('injected restoration failure'))
    def test_identical_timeout_survives_both_teardown_failures(self):
        self.teardown_case(subprocess.TimeoutExpired(['original'],1200),OSError('injected close failure'),OSError('injected restoration failure'))
    def test_close_failure_after_success_blocks_pass(self):
        self.teardown_case(None,close_error=OSError('injected close failure'))
    def test_restoration_failure_after_success_blocks_pass(self):
        self.teardown_case(None,restore_error=OSError('injected restoration failure'))
    def test_identical_timeout_survives_receipt_failure(self):
        self.teardown_case(subprocess.TimeoutExpired(['original'],1200),receipt_error=OSError('injected receipt failure'))

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
    def test_genuine_original_29_localization_mocks_and_current_semantics(self):
        code,output=positive_route_process('localization-mocks-full',['--schema',str(SCHEMA),comp.LOCALIZATION_MOCK_FLAG])
        self.assertEqual(code,0,output)
        self.assertIn('HISTORICAL_VALIDATOR_BEGIN '+comp.LOCALIZATION+' '+comp.LOCALIZATION_MOCK,output)
        self.assertIn('HISTORICAL_VALIDATOR_END '+comp.LOCALIZATION+' '+comp.LOCALIZATION_MOCK,output)
        self.assertIn('Ran 29 tests',output)
        self.assertIn('Frozen five-module localization',output)
        self.assertIn('Closed-contract source invariants passed',output)

    def test_genuine_weighted_base_route(self):
        code,output=positive_route_process('weighted-full',['--schema',str(SCHEMA)])
        self.assertEqual(code,0,output)
        self.assertIn('Source-only integration checks passed',output)
        self.assertIn('OPEN',output)

    def test_complete_original_localization_and_current_semantics(self):
        with tempfile.TemporaryDirectory(prefix='point4-current-localization-evidence-') as directory:
            manifest=pathlib.Path(directory)/'current.json'
            code,output=positive_route_process('localization-manifest-full',['--schema',str(SCHEMA),'--manifest',str(manifest)])
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
        code,output=positive_route_process('smooth-evidence-full',args)
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
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(PositiveControllerTests))
    if REAL:suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(RealValidatorTests))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
