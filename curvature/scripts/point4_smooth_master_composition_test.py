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
HEAT_FIXTURES=None
CONTRACTION_FIXTURES=None
FIXED_FIXTURES=None
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
    def test_heat_weighted_failure_runs_all_postchecks_and_preserves_primary(self):
        _,_,read=parent_inputs()
        helper=types.SimpleNamespace(check_imports=object(),check_metadata=object())
        local=types.SimpleNamespace(legacy_check_imports=object(),legacy_check_metadata=object())
        primary=RuntimeError('actual semantic primary failure')
        namespace={'expected_sources':lambda:{},'public_paths':lambda:set(),
            'historical_c2':lambda:helper,'_composition_original_public_paths':lambda:set(),
            'restored_exact_head_workflow':object(),'UNIT_FILE_SHA256':{},
            '_composition_original_check_current':lambda schema:(_ for _ in ()).throw(primary)}
        before=dict(namespace);slots=helper.check_imports,helper.check_metadata;events=[]
        def identity():
            events.append('identity')
            if len(events)>2:raise RuntimeError('POST identity failure')
            return {}
        def schema(*args):
            events.append('schema')
            if len(events)>2:raise RuntimeError('POST schema failure')
        with patch.object(comp,'verify_current',side_effect=identity),patch.object(comp,'current_root_schema',side_effect=schema),patch.object(comp.importlib,'import_module',return_value=local):
            with self.assertRaises(RuntimeError) as error:comp.weighted_leaf(namespace,pathlib.Path('schema.json'))
        self.assertIs(error.exception,primary)
        self.assertEqual(events,['identity','schema','identity','schema'])
        self.assertEqual(len(primary.__notes__),2)
        for name in before:self.assertIs(namespace[name],before[name])
        self.assertEqual((helper.check_imports,helper.check_metadata),slots)
        self.assertEqual(comp._depth,0);self.assertIsNone(comp._owner)

    def test_heat_default_git_reader_survives_reentrant_mock(self):
        # Exercise the real default path against actual owned Git objects. This
        # cannot be covered by the offline parent-file adapter alone.
        with tempfile.TemporaryDirectory(prefix='point4-heat-reader-',dir=pathlib.Path.cwd()) as directory:
            root=pathlib.Path(directory).resolve()
            self.assertEqual(root.parent,pathlib.Path.cwd().resolve())
            env=dict(comp.ENV,GIT_AUTHOR_NAME='Point4 regression fixture',
                GIT_AUTHOR_EMAIL='fixture@example.invalid',GIT_COMMITTER_NAME='Point4 regression fixture',
                GIT_COMMITTER_EMAIL='fixture@example.invalid')
            def actual_git(*args,data=None):
                return subprocess.check_output(['git','--no-replace-objects','-C',str(root),*args],input=data,env=env)
            actual_git('init','--quiet')
            values=[b'owned authentic parent fixture\n',b'owned authentic source fixture\n']
            commits=[];trees=[];objects=[]
            for index,value in enumerate(values):
                oid=actual_git('hash-object','-w','--stdin',data=value).decode().strip()
                tree=actual_git('mktree',data=('100644 blob '+oid+'\tordinary.txt\n').encode()).decode().strip()
                commit=actual_git('commit-tree',tree,data=('owned regression '+str(index)+'\n').encode()).decode().strip()
                commits.append(commit);trees.append(tree);objects.append(oid)
            case=OrdinaryCompositionTests(methodName='test_heat_current_body_failure_is_propagated')
            with patch.dict(globals(),{'HEAT_FIXTURES':None,'OFFLINE':None,'CONTRACTION_FIXTURES':None}),patch.object(comp,'ROOT',root),\
                 patch.object(comp,'HEAT_PARENT',commits[0]),patch.object(comp,'HEAT_SOURCE',commits[1]),\
                 patch.dict(comp.TREES,dict(zip(commits,trees))):
                base,source,reader=case.heat_inputs()
                self.assertEqual(base,{'ordinary.txt':('100644',objects[0])})
                self.assertEqual(source,{'ordinary.txt':('100644',objects[1])})
                # The side effect reproduces the real controls' reentrant shape.
                # Capturing the unmocked reader must break that recursion while
                # still executing actual Git show, not synthetic file bytes.
                with patch.object(comp,'git',side_effect=lambda command,name:reader(*name.split(':',1))) as mocked:
                    self.assertEqual(comp.git('show',commits[0]+':ordinary.txt'),values[0])
                    self.assertEqual(comp.git('show',commits[1]+':ordinary.txt'),values[1])
                    self.assertEqual(mocked.call_count,2)

    def test_heat_default_reader_calls_captured_original_once_and_restores(self):
        before_git=comp.git;before_owner=comp._owner;before_depth=comp._depth
        data=b'controlled actual default factory\n';events=[]
        def source_git(*args):events.append(args);return data
        snapshot={'ordinary.txt':('100644',comp.blob_id(data))}
        with patch.dict(globals(),{'HEAT_FIXTURES':None,'OFFLINE':None,'CONTRACTION_FIXTURES':None}),\
             patch.object(comp,'parent_tree',return_value=snapshot),patch.object(comp,'git',source_git):
            base,source,reader=self.heat_inputs()
            self.assertEqual(base,snapshot);self.assertEqual(source,snapshot)
            with patch.object(comp,'git',side_effect=lambda command,name:reader(*name.split(':',1))) as mocked:
                self.assertEqual(comp.git('show',comp.HEAT_PARENT+':ordinary.txt'),data)
                mocked.assert_called_once_with('show',comp.HEAT_PARENT+':ordinary.txt')
            self.assertIs(comp.git,source_git)
            self.assertEqual(events,[('show',comp.HEAT_PARENT+':ordinary.txt')])
        self.assertIs(comp.git,before_git);self.assertIs(comp._owner,before_owner);self.assertEqual(comp._depth,before_depth)
    def heat_inputs(self):
        if HEAT_FIXTURES:
            data=json.loads((HEAT_FIXTURES/'sources/master-tree.json').read_text(encoding='utf8'))
            base={r['path']:(r['mode'],r['sha']) for r in data['tree'] if r['type']=='blob'}
            data=json.loads((HEAT_FIXTURES/'sources/pr110-tree.json').read_text(encoding='utf8'))
            source={r['path']:(r['mode'],r['sha']) for r in data['tree'] if r['type']=='blob'}
            def read(commit,path):
                label='master110' if commit==comp.HEAT_PARENT else 'pr110'
                data=(HEAT_FIXTURES/'sources'/label/path).read_bytes()
                self.assertEqual(comp.blob_id(data),(base if label=='master110' else source)[path][1])
                return data
        else:
            base,source=comp.parent_tree(comp.HEAT_PARENT),comp.parent_tree(comp.HEAT_SOURCE)
            git_read=comp.git
            read=lambda commit,path:git_read('show',commit+':'+path)
        return base,source,read

    def test_heat_root_provenance_and_scope_transforms_are_count_one_and_reversible(self):
        base,source,read=self.heat_inputs()
        with patch.object(comp,'git',side_effect=lambda command,object_name:read(*object_name.split(':',1))),patch.object(comp,'parent_tree',side_effect=lambda c:base if c==comp.HEAT_PARENT else source):
            for path in comp.HEAT_ROOTS:
                original=read(comp.HEAT_PARENT,path)
                changed=comp.heat_transform(path,original)
                self.assertEqual(comp.heat_inverse(path,changed),original)
                for bad in (changed+b'\nextra unreviewed root content\n',original):
                    with self.assertRaises(AssertionError):comp.heat_inverse(path,bad)
                with self.assertRaises(AssertionError):comp.heat_transform(path,changed)
                anchor=comp.HEAT_IMPORT_ANCHOR if path==comp.HEAT_ROOT else 'related_formalizations:\n' if path==comp.HEAT_METADATA else comp.HEAT_DOC_ANCHOR
                for bad in (original.replace(anchor.encode(),b'',1),original+anchor.encode()):
                    with self.assertRaises(AssertionError):comp.heat_transform(path,bad)

    def test_heat_current_semantics_run_actual_bodies_after_exact_inverse(self):
        base,source,read=self.heat_inputs();events=[]
        local=types.SimpleNamespace(INTEGRATION_PARENT='semantic-base',blob=lambda commit,path:read(comp.HEAT_PARENT,path),
            legacy_check_imports=lambda raw:events.append(('old-imports',raw)),
            legacy_check_metadata=lambda raw:events.append(('old-metadata',raw)),
            check_imports=lambda *args:events.append(('current-imports',args)),
            check_metadata=lambda *args:events.append(('current-metadata',args)))
        with patch.object(comp,'git',side_effect=lambda command,object_name:read(*object_name.split(':',1))),patch.object(comp,'parent_tree',return_value=base):
            old=read(comp.HEAT_PARENT,comp.HEAT_ROOT);new=comp.heat_transform(comp.HEAT_ROOT,old)
            comp.heat_check_imports(local,new)
            self.assertEqual(events,[('old-imports',old),('current-imports',(new,new,old))])
            events.clear();old=read(comp.HEAT_PARENT,comp.HEAT_METADATA);new=comp.heat_transform(comp.HEAT_METADATA,old)
            comp.heat_check_metadata(local,new.decode())
            self.assertEqual(events,[('old-metadata',old.decode()),('current-metadata',(new,new,old))])
            events.clear()
            with self.assertRaises(AssertionError):comp.heat_check_metadata(local,new.decode()+'\nextra metadata\n')
            self.assertEqual(events,[])

    def test_heat_current_body_failure_is_propagated(self):
        base,_,read=self.heat_inputs();events=[]
        local=types.SimpleNamespace(INTEGRATION_PARENT='semantic-base',blob=lambda commit,path:read(comp.HEAT_PARENT,path),
            legacy_check_imports=lambda raw:events.append('historical-shape'),
            check_imports=lambda *args:(_ for _ in ()).throw(RuntimeError('actual current body failure')))
        with patch.object(comp,'git',side_effect=lambda command,object_name:read(*object_name.split(':',1))),patch.object(comp,'parent_tree',return_value=base):
            raw=comp.heat_transform(comp.HEAT_ROOT,read(comp.HEAT_PARENT,comp.HEAT_ROOT))
            with self.assertRaisesRegex(RuntimeError,'actual current body failure'):comp.heat_check_imports(local,raw)
        self.assertEqual(events,['historical-shape'])

    def test_heat_finite_source_inventory_and_base_drift_rejection(self):
        base,source,read=self.heat_inputs();master,support,parent_read=parent_inputs()
        legacy=comp.resolve_union(master,support);digest=comp.sha256(read(comp.HEAT_PARENT,comp.HELPER))
        def parents(commit):
            return master if commit==comp.MASTER else support if commit==comp.SUPPORT else base if commit==comp.HEAT_PARENT else source
        originals={p:parent_read(p) for p in comp.EDITED}
        with patch.object(comp,'parent_tree',side_effect=parents):
            changes={p:comp.transform(p,originals[p],digest) for p in comp.EDITED-{comp.SMOOTH}}
            changes[comp.SMOOTH]=comp.transform(comp.SMOOTH,originals[comp.SMOOTH],digest,comp.sha256(changes[comp.FIXTURE]),comp.sha256(changes[comp.WORKFLOW]))
            expected=dict(legacy);expected.update({p:('100644',comp.blob_id(b)) for p,b in changes.items()})
            with patch.object(comp,'git',side_effect=lambda command,object_name:read(*object_name.split(':',1))):
                final,_,_=comp.heat_identity(dict(expected),dict(originals),dict(changes))
                self.assertEqual(len(final),1726)
                for path in comp.HEAT_ADDED|{comp.HEAT_DOMAIN}:self.assertEqual(final[path],source[path])
                untouched=set(legacy)-comp.EDITED-comp.HEAT_ROOTS-{comp.HEAT_DOMAIN}
                self.assertTrue(all(final[p]==base[p] for p in untouched))
                bad=dict(base);bad.pop(next(iter(untouched)))
                with patch.object(comp,'parent_tree',side_effect=lambda c:bad if c==comp.HEAT_PARENT else parents(c)),self.assertRaises(AssertionError):
                    comp.heat_identity(dict(expected),dict(originals),dict(changes))
                for mode,blob in [('100755',source[comp.HEAT_MODULE][1]),('100644','0'*40)]:
                    bad=dict(source);bad[comp.HEAT_MODULE]=(mode,blob)
                    with patch.object(comp,'parent_tree',side_effect=lambda c:bad if c==comp.HEAT_SOURCE else parents(c)),self.assertRaises(AssertionError):
                        comp.heat_identity(dict(expected),dict(originals),dict(changes))

    def weighted_mock_namespace(self,events):
        namespace={'main':lambda args:events.append(('main',args)), 'run_inherited':object(),
            'check_current':object(), 'public_paths':object(), 'historical_gate':object(), 'BASE':'ordinary-only'}
        comp.install_weighted(namespace)
        return namespace

    def test_weighted_mock_dispatch_failure_keeps_current_pre_post_and_original_main(self):
        events=[];namespace=self.weighted_mock_namespace(events)
        def history(commit,path,args):
            self.assertEqual((commit,path,args),(comp.WEIGHTED_MOCK_PARENT,comp.WEIGHTED_MOCK,[]))
            events.append(('history',args))
            raise RuntimeError('ordinary authentic weighted mock dispatch failure')
        with (patch.object(comp,'weighted_current_inherited_evidence',side_effect=lambda ns,args:events.append(('schema',args))),
              patch.object(comp,'weighted_execution',side_effect=lambda ns:contextlib.nullcontext()),
              patch.object(comp,'weighted_leaf',side_effect=lambda ns,schema:events.append(('leaf',str(schema)))),
              patch.object(comp,'historical',side_effect=history)):
            with self.assertRaisesRegex(RuntimeError,'authentic weighted mock dispatch failure'):
                namespace['main'](['--schema','schema.json',comp.WEIGHTED_MOCK_FLAG])
        schema=str(pathlib.Path('schema.json').resolve())
        self.assertEqual(events,[('schema',['--schema',schema]),('main',['--schema',schema]),
            ('schema',['--schema',schema]),('history',[]),('leaf',schema),('schema',['--schema',schema])])

    def test_weighted_mock_argument_dispatch_rejects_missing_schema_extra_and_duplicate_flag(self):
        cases=([comp.WEIGHTED_MOCK_FLAG],['--schema','schema.json',comp.WEIGHTED_MOCK_FLAG,comp.WEIGHTED_MOCK_FLAG],
            ['--schema','schema.json',comp.WEIGHTED_MOCK_FLAG,'--commit','arbitrary'],
            ['--schema','schema.json',comp.WEIGHTED_MOCK_FLAG,'--historical-path','arbitrary.py'])
        for args in cases:
            namespace=self.weighted_mock_namespace([])
            with (contextlib.redirect_stderr(io.StringIO()),patch.object(comp,'weighted_current_inherited_evidence') as current,
                  patch.object(comp,'historical') as history,self.assertRaises((AssertionError,SystemExit))):
                namespace['main'](args)
            current.assert_not_called();history.assert_not_called()

    def test_manifold_env_precedes_every_repo_import_and_duplicate_env_rejected(self):
        _,_,read=parent_inputs();original=read(comp.MANIFOLD_WORKFLOW)
        changed=comp.transform(comp.MANIFOLD_WORKFLOW,original,'0'*64)
        self.assertEqual(changed.replace(comp.STARTUP_ENV.encode(),b'',1),original)
        self.assertLess(changed.index(comp.STARTUP_ENV.encode()),changed.index(b'python3 curvature/scripts/'))
        self.assertIn(b'bash scripts/point4_audit.sh',changed)
        with self.assertRaises(AssertionError):comp.transform(comp.MANIFOLD_WORKFLOW,changed,'0'*64)

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
                    self.assertEqual(changed.replace(comp.LOCALIZATION_CONTRACT_BUILD_COMMAND.encode(),b'',1).replace(comp.STARTUP_ENV.encode(),b'',1).replace(comp.LOCALIZATION_MOCK_ROUTE_COMMAND.encode(),comp.LOCALIZATION_MOCK_COMMAND.encode(),1),original)
                elif path==comp.WEIGHTED_WORKFLOW:
                    self.assertEqual(changed.replace(comp.WEIGHTED_MOCK_ROUTE_COMMAND.encode(),comp.WEIGHTED_MOCK_COMMAND.encode(),1),original)
                elif path==comp.MANIFOLD_WORKFLOW:
                    self.assertEqual(changed.replace(comp.STARTUP_ENV.encode(),b'',1),original)
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
                anchor=comp.WEIGHTED_MOCK_COMMAND if path==comp.WEIGHTED_WORKFLOW else comp.STARTUP_ANCHOR if path in (comp.LOCALIZATION_WORKFLOW,comp.MANIFOLD_WORKFLOW) else comp.WF_ANCHOR if path==comp.WORKFLOW else comp.ENTRY
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
        self.assertEqual(changed.replace(comp.LOCALIZATION_CONTRACT_BUILD_COMMAND.encode(),b'',1).replace(comp.STARTUP_ENV.encode(),b'',1).replace(comp.LOCALIZATION_MOCK_ROUTE_COMMAND.encode(),comp.LOCALIZATION_MOCK_COMMAND.encode(),1),original)
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
            'historical_c2':lambda:helper,'_composition_original_public_paths':lambda:set(),
            'restored_exact_head_workflow':object(),'UNIT_FILE_SHA256':{}}
        before=dict(namespace)
        def failing(schema):
            changed=namespace['historical_c2']()
            with patch.object(comp,'fixed_check_imports') as imports,patch.object(comp,'fixed_check_metadata') as metadata:
                changed.check_imports(b'current import bytes')
                changed.check_metadata('current metadata bytes')
                imports.assert_called_once_with(local,b'current import bytes')
                metadata.assert_called_once_with(local,'current metadata bytes')
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
        actual=current_smooth_arguments()
        args=[]
        for flag in ('--schema','--axiom-dir','--audit-json','--audit-rc'):
            args.extend([flag,actual[actual.index(flag)+1]])
        code,output=positive_route_process('weighted-full',args)
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

class ContractionCompositionTests(unittest.TestCase):
    def test_metric_default_reader_calls_captured_original_once_and_restores(self):
        before_git=comp.git;before_owner=comp._owner;before_depth=comp._depth
        data=b'controlled metric default factory\n';events=[]
        def source_git(*args):events.append(args);return data
        snapshot={'ordinary.txt':('100644',comp.blob_id(data))}
        with patch.dict(globals(),{'HEAT_FIXTURES':None,'OFFLINE':None,'CONTRACTION_FIXTURES':None}),\
             patch.object(comp,'parent_tree',return_value=snapshot),patch.object(comp,'git',source_git):
            with self.sources() as (trees,reader):
                self.assertTrue(all(value==snapshot for value in trees.values()))
                with patch.object(comp,'git',side_effect=lambda command,name:reader(*name.split(':',1))) as mocked:
                    self.assertEqual(comp.git('show',comp.CONTRACTION_SOURCE+':ordinary.txt'),data)
                    mocked.assert_called_once_with('show',comp.CONTRACTION_SOURCE+':ordinary.txt')
                self.assertIs(comp.git,source_git)
                self.assertEqual(events,[('show',comp.CONTRACTION_SOURCE+':ordinary.txt')])
        self.assertIs(comp.git,before_git);self.assertIs(comp._owner,before_owner);self.assertEqual(comp._depth,before_depth)

    def test_metric_default_git_reader_survives_reentrant_mock(self):
        with tempfile.TemporaryDirectory(prefix='point4-metric-reader-',dir=pathlib.Path.cwd()) as directory:
            root=pathlib.Path(directory).resolve();self.assertEqual(root.parent,pathlib.Path.cwd().resolve())
            env=dict(comp.ENV,GIT_AUTHOR_NAME='Point4 regression fixture',GIT_AUTHOR_EMAIL='fixture@example.invalid',
                GIT_COMMITTER_NAME='Point4 regression fixture',GIT_COMMITTER_EMAIL='fixture@example.invalid')
            def actual_git(*args,data=None):
                return subprocess.check_output(['git','--no-replace-objects','-C',str(root),*args],input=data,env=env)
            actual_git('init','--quiet');value=b'owned genuine metric Git fixture\n'
            oid=actual_git('hash-object','-w','--stdin',data=value).decode().strip()
            tree=actual_git('mktree',data=('100644 blob '+oid+'\tordinary.txt\n').encode()).decode().strip()
            commit=actual_git('commit-tree',tree,data=b'owned metric regression\n').decode().strip()
            names=('MASTER','SUPPORT','HEAT_PARENT','HEAT_SOURCE','CONTRACTION_PARENT','CONTRACTION_SOURCE','CONTRACTION_BASE')
            with contextlib.ExitStack() as stack:
                stack.enter_context(patch.dict(globals(),{'HEAT_FIXTURES':None,'OFFLINE':None,'CONTRACTION_FIXTURES':None}))
                stack.enter_context(patch.object(comp,'ROOT',root))
                stack.enter_context(patch.dict(comp.TREES,{commit:tree}))
                for name in names:stack.enter_context(patch.object(comp,name,commit))
                with self.sources() as (trees,reader):
                    self.assertEqual(trees,{commit:{'ordinary.txt':('100644',oid)}})
                    with patch.object(comp,'git',side_effect=lambda command,name:reader(*name.split(':',1))) as mocked:
                        self.assertEqual(comp.git('show',commit+':ordinary.txt'),value)
                        mocked.assert_called_once_with('show',commit+':ordinary.txt')

    @contextlib.contextmanager
    def sources(self):
        if CONTRACTION_FIXTURES:
            fixture=json.loads((CONTRACTION_FIXTURES/'SOURCE-FIXTURES.json').read_bytes())
            trees={c:{p:tuple(v) for p,v in rows.items()} for c,rows in fixture['trees'].items()}
            heat=pathlib.Path(fixture['heat_root']);legacy=pathlib.Path(fixture['legacy_root']);design=pathlib.Path(fixture['design_root'])
            def source_bytes(commit,path):
                if FIXED_FIXTURES and commit in {comp.FIXED_PARENT,comp.FIXED_SOURCE,comp.FIXED_BASE,FIXED_SEMANTIC_PARENT}:
                    return fixed_fixture_read(commit,path)
                if commit==comp.CONTRACTION_PARENT:
                    file=heat/'candidate'/path
                    if not file.exists():
                        self.assertIn(path,comp.CONTRACTION_REPLACED)
                        self.assertEqual(trees[commit][path],trees[comp.CONTRACTION_BASE][path])
                        file=CONTRACTION_FIXTURES/'sources/predecessor'/path
                elif commit==comp.CONTRACTION_SOURCE:file=design/'sources/pr115'/path
                elif commit==comp.CONTRACTION_BASE:file=design/'sources/base115'/path
                elif commit==comp.HEAT_PARENT:file=heat/'sources/master110'/path
                elif commit==comp.HEAT_SOURCE:file=heat/'sources/pr110'/path
                else:file=legacy/'parent-sources'/('master' if commit==comp.MASTER else 'support')/path
                data=file.read_bytes();self.assertEqual(comp.blob_id(data),trees[commit][path][1])
                return data
            head=json.loads((CONTRACTION_FIXTURES/'CANDIDATE-RECIPE.json').read_bytes())['identity']
            def git(*args):
                if args==('ls-tree','-rz','HEAD'):
                    return b''.join(mode.encode()+b' blob '+oid.encode()+b'\t'+p.encode()+b'\0' for p,(mode,oid) in sorted(head.items()))
                self.assertEqual(args[0],'show');self.assertEqual(len(args),2)
                return source_bytes(*args[1].split(':',1))
            with patch.object(comp,'parent_tree',side_effect=lambda c:trees[c]),patch.object(comp,'git',side_effect=git):
                yield trees,source_bytes
        else:
            trees={c:comp.parent_tree(c) for c in (comp.MASTER,comp.SUPPORT,comp.HEAT_PARENT,comp.HEAT_SOURCE,comp.CONTRACTION_PARENT,comp.CONTRACTION_SOURCE,comp.CONTRACTION_BASE)}
            source_git=comp.git
            yield trees,lambda commit,path:source_git('show',commit+':'+path)

    def test_full_finite_identity_and_selected_source_bytes(self):
        with self.sources() as (trees,read):
            expected,originals,changes=comp.tensor_identity(*comp.expected_identity())
            self.assertEqual(len(expected),1920)
            for path in comp.CONTRACTION_ADDED|comp.CONTRACTION_REPLACED:
                self.assertEqual(changes[path],read(comp.CONTRACTION_SOURCE,path))
                self.assertEqual(expected[path],trees[comp.CONTRACTION_SOURCE][path])
            for path in comp.CONTRACTION_ROOTS:
                self.assertEqual(comp.contraction_inverse(path,comp.fixed_inverse(path,changes[path])),read(comp.CONTRACTION_PARENT,path))
            unchanged=set(trees[comp.CONTRACTION_PARENT])-comp.EDITED-comp.NEW-comp.CONTRACTION_ROOTS-comp.CONTRACTION_REPLACED-comp.FIXED_ROOTS-comp.TENSOR_PATHS
            self.assertTrue(all(expected[p]==trees[comp.CONTRACTION_PARENT][p] for p in unchanged))
            self.assertEqual(comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()),comp.tensor_map_record(expected,originals,changes))

    def test_exact_inverse_rejects_missing_extra_and_duplicate_transform(self):
        with self.sources() as (_,read):
            for path in comp.CONTRACTION_ROOTS:
                original=read(comp.CONTRACTION_PARENT,path)
                actual=comp.contraction_transform(path,original)
                self.assertEqual(comp.contraction_inverse(path,actual),original)
                for bad in (original,actual+b'\nextra unreviewed content\n'):
                    with self.assertRaises(AssertionError):comp.contraction_inverse(path,bad)
                with self.assertRaises(AssertionError):comp.contraction_transform(path,actual)

    def test_original_semantic_bodies_receive_the_actual_expanded_union(self):
        with self.sources() as (_,read):
            events=[]
            local=types.SimpleNamespace(INTEGRATION_PARENT='semantic-base',blob=lambda commit,path:read(comp.HEAT_PARENT,path),
                legacy_check_imports=lambda raw:events.append(('old-imports',raw)),
                legacy_check_metadata=lambda raw:events.append(('old-metadata',raw)),
                check_imports=lambda *args:events.append(('actual-imports',args)),
                check_metadata=lambda *args:events.append(('actual-metadata',args)))
            for path in (comp.HEAT_ROOT,comp.HEAT_METADATA):
                old=read(comp.HEAT_PARENT,path)
                actual=comp.contraction_transform(path,comp.heat_transform(path,old))
                if path==comp.HEAT_ROOT:
                    comp.contraction_check_imports(local,actual)
                    self.assertEqual(events,[('old-imports',old),('actual-imports',(actual,actual,old))])
                else:
                    comp.contraction_check_metadata(local,actual.decode())
                    self.assertEqual(events,[('old-metadata',old.decode()),('actual-metadata',(actual,actual,old))])
                    self.assertEqual(actual.count(comp.CONTRACTION_METADATA_NOTE.encode()),1)
                    self.assertEqual(actual.count(comp.HEAT_METADATA_NOTE.encode()),1)
                events.clear()

    def test_current_semantic_body_failure_is_not_converted_to_success(self):
        with self.sources() as (_,read):
            primary=RuntimeError('actual expanded current semantic failure');events=[]
            local=types.SimpleNamespace(INTEGRATION_PARENT='semantic-base',blob=lambda commit,path:read(comp.HEAT_PARENT,path),
                legacy_check_imports=lambda raw:events.append(raw),
                check_imports=lambda *args:(_ for _ in ()).throw(primary))
            actual=comp.fixed_inverse(comp.HEAT_ROOT,(comp.ROOT/comp.HEAT_ROOT).read_bytes())
            with self.assertRaises(RuntimeError) as error:comp.contraction_check_imports(local,actual)
            self.assertIs(error.exception,primary)
            self.assertEqual(events,[read(comp.HEAT_PARENT,comp.HEAT_ROOT)])

    def test_bad_inverse_stops_before_both_semantic_bodies(self):
        with self.sources():
            events=[]
            local=types.SimpleNamespace(legacy_check_imports=lambda *a:events.append('legacy'),check_imports=lambda *a:events.append('actual'))
            with self.assertRaises(AssertionError):comp.contraction_check_imports(local,comp.fixed_inverse(comp.HEAT_ROOT,(comp.ROOT/comp.HEAT_ROOT).read_bytes())+b'\nextra\n')
            self.assertEqual(events,[])

    def test_source_omission_mode_blob_and_extra_branch_path_are_rejected(self):
        with self.sources() as (trees,read):
            module=sorted(comp.CONTRACTION_ADDED)[0]
            for mutation in ('omit','mode','blob','extra'):
                bad=dict(trees[comp.CONTRACTION_SOURCE])
                if mutation=='omit':bad.pop(module)
                elif mutation=='mode':bad[module]=('100755',bad[module][1])
                elif mutation=='blob':bad[module]=('100644','0'*40)
                else:bad['unexpected-new-path.lean']=('100644','0'*40)
                with patch.object(comp,'parent_tree',side_effect=lambda c:bad if c==comp.CONTRACTION_SOURCE else trees[c]),self.assertRaises(AssertionError):
                    comp.expected_identity()

    def test_predecessor_drift_is_not_absorbed_into_current_recipe(self):
        with self.sources() as (trees,read):
            for mutation in ('omit','blob','mode'):
                bad=dict(trees[comp.CONTRACTION_PARENT]);path='curvature/lean-toolchain'
                if mutation=='omit':bad.pop(path)
                elif mutation=='blob':bad[path]=('100644','0'*40)
                else:bad[path]=('100755',bad[path][1])
                with patch.object(comp,'parent_tree',side_effect=lambda c:bad if c==comp.CONTRACTION_PARENT else trees[c]),self.assertRaises(AssertionError):
                    comp.expected_identity()

    def test_merge_base_drift_cannot_broaden_the_fixed_seven_path_scope(self):
        with self.sources() as (trees,read):
            bad=dict(trees[comp.CONTRACTION_BASE]);bad['curvature/lean-toolchain']=('100644','0'*40)
            with patch.object(comp,'parent_tree',side_effect=lambda c:bad if c==comp.CONTRACTION_BASE else trees[c]),self.assertRaises(AssertionError):
                comp.expected_identity()

from pathlib import Path
import runpy
ROOT=comp.ROOT
FIXED_PARENT_PIN=comp.FIXED_PARENT
FIXED_SEMANTIC_PARENT='fe921dbc34918d22389e87f30bdffb73ed7ebeb9'

def fixed_fixture_read(commit,path):
    fixture=json.loads((FIXED_FIXTURES/'SOURCE-FIXTURES.json').read_bytes())
    roots={k:pathlib.Path(v) for k,v in fixture['fixed_roots'].items()}
    if commit==FIXED_PARENT_PIN:
        file=roots['fixed_parent']/'candidate'/path
        if not file.exists():
            assert path=='docs/status.md';file=roots['design']/'sources/master79'/path
    elif commit==comp.FIXED_SOURCE:file=roots['preflight']/'sources/pr126'/path
    elif commit==comp.FIXED_BASE:file=roots['preflight']/'sources/base126'/path
    elif commit==FIXED_SEMANTIC_PARENT:file=roots['semantic']/path
    elif commit==comp.CONTRACTION_PARENT:
        file=roots['heat']/'candidate'/path
        if not file.exists():
            assert path in comp.CONTRACTION_REPLACED
            file=roots['repair']/'sources/predecessor'/path
    elif commit==comp.CONTRACTION_SOURCE:file=roots['design']/'sources/pr115'/path
    elif commit==comp.CONTRACTION_BASE:file=roots['design']/'sources/base115'/path
    elif commit==comp.HEAT_PARENT:file=roots['heat']/'sources/master110'/path
    elif commit==comp.HEAT_SOURCE:file=roots['heat']/'sources/pr110'/path
    else:
        assert commit in [comp.MASTER,comp.SUPPORT]
        file=roots['legacy']/'parent-sources'/('master' if commit==comp.MASTER else 'support')/path
    data=file.read_bytes()
    assert comp.blob_id(data)==fixture['trees'][commit][path][1]
    return data

@contextlib.contextmanager
def fixed_sources():
    if FIXED_FIXTURES:
        fixture=json.loads((FIXED_FIXTURES/'SOURCE-FIXTURES.json').read_bytes())
        trees={c:{p:tuple(v) for p,v in rows.items()} for c,rows in fixture['trees'].items()}
        head=json.loads((FIXED_FIXTURES/'CANDIDATE-RECIPE.json').read_bytes())['identity']
        def source_git(*args):
            if args==('ls-tree','-rz','HEAD'):
                return b''.join(mode.encode()+b' blob '+oid.encode()+b'\t'+p.encode()+b'\0' for p,(mode,oid) in sorted(head.items()))
            assert len(args)==2 and args[0]=='show'
            return fixed_fixture_read(*args[1].split(':',1))
        with patch.object(comp,'parent_tree',side_effect=lambda c:trees[c]),patch.object(comp,'git',side_effect=source_git):
            yield trees,fixed_fixture_read
    else:
        names=('MASTER','SUPPORT','HEAT_PARENT','HEAT_SOURCE','CONTRACTION_PARENT','CONTRACTION_SOURCE','CONTRACTION_BASE','FIXED_PARENT','FIXED_SOURCE','FIXED_BASE')
        trees={getattr(comp,name):comp.parent_tree(getattr(comp,name)) for name in names}
        captured_git=comp.git
        reader=lambda commit,path:captured_git('show',commit+':'+path)
        yield trees,reader

def fixed_semantic_blob(commit,path):
    assert commit==FIXED_SEMANTIC_PARENT
    return comp.git('show',commit+':'+path)

def fixed_semantic_local():
    # Compile the original function bodies, constants and strict YAML parser;
    # avoid executing the guard's release/bootstrap entry point in this unit.
    import re,hashlib,yaml
    tree=ast.parse((comp.ROOT/comp.LOCAL).read_bytes())
    namespace={'re':re,'hashlib':hashlib,'yaml':yaml,'blob':fixed_semantic_blob}
    for name in ['PREFIX','MODULES','INTEGRATION_PARENT','PARENT_NOTE_SHA256']:
        node=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets))
        exec(compile(ast.Module(body=[node],type_ignores=[]),'exact_original_semantic_constant','exec'),namespace)
    nodes=[n for n in tree.body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name in
        ['StrictLoader','unique_mapping','strict_yaml','check_imports','entries','check_metadata','legacy_check_imports','legacy_check_metadata']]
    constructor=next(n for n in tree.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
        and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='add_constructor')
    nodes.insert(2,constructor)
    exec(compile(ast.Module(body=nodes,type_ignores=[]),'exact_original_semantic_bodies','exec'),namespace)
    return types.SimpleNamespace(**namespace)

class FixedBackgroundCompositionTests(unittest.TestCase):

    def tearDown(self):
        self.assertEqual(comp.FIXED_PARENT,FIXED_PARENT_PIN)
        self.assertIsNone(comp._owner)
        self.assertEqual(comp._depth, 0)

    def test_missing_and_malformed_pin_fail_before_git_or_parent_reads(self):
        for bad in [None, '', 'f' * 39, 'g' * 40, 'F' * 40, 'f' * 40 + '\n']:
            with patch.object(comp, 'FIXED_PARENT', bad), patch.object(comp, 'git') as git, patch.object(comp, 'parent_tree') as parent, patch.object(comp.subprocess, 'run') as process:
                for function, args in [(comp.verify_current, ()), (comp.fixed_identity, ({}, {}, {})), (comp.fixed_inverse, (comp.HEAT_ROOT, b'candidate'))]:
                    with self.assertRaisesRegex(AssertionError, 'pin|^$'):
                        function(*args)
                git.assert_not_called()
                parent.assert_not_called()
                process.assert_not_called()

    def test_full_controlled_identity_and_unchanged_selected_mathematics(self):
        with fixed_sources() as (trees, reader):
            expected, originals, changes = comp.tensor_identity(*comp.expected_identity())
            expected = comp.curvature_identity(expected,originals,changes)[0]
            self.assertEqual(expected, comp.parse_tree(comp.git('ls-tree','-rz','HEAD')))
            self.assertEqual(len(expected), 2139)
            for path in comp.FIXED_ADDED:
                self.assertEqual(changes[path], reader(comp.FIXED_SOURCE, path))
                self.assertEqual(expected[path], trees[comp.FIXED_SOURCE][path])
            self.assertEqual(comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()), comp.tensor_map_record(expected, originals, changes))
            unchanged = set(trees[FIXED_PARENT_PIN]) - comp.EDITED - comp.NEW - comp.FIXED_ROOTS - comp.TENSOR_PATHS - set(comp.CURVATURE_SELECTED)
            self.assertTrue(all((expected[p] == trees[FIXED_PARENT_PIN][p] for p in unchanged)))

    def test_all_four_exact_transforms_and_inverses(self):
        with fixed_sources() as (_, reader):
            for path in comp.FIXED_ROOTS:
                original = reader(FIXED_PARENT_PIN, path)
                actual = comp.fixed_transform(path, original)
                self.assertEqual(comp.fixed_inverse(path, actual), original)
                self.assertEqual(actual, (comp.ROOT / path).read_bytes())

    def test_missing_extra_and_duplicate_transform_rejected(self):
        with fixed_sources() as (_, reader):
            for path in comp.FIXED_ROOTS:
                original = reader(FIXED_PARENT_PIN, path)
                actual = comp.fixed_transform(path, original)
                for bad in [original, actual + b'\nextra\n']:
                    with self.assertRaises(AssertionError):
                        comp.fixed_inverse(path, bad)
                with self.assertRaises(AssertionError):
                    comp.fixed_transform(path, actual)

    def test_status_is_exactly_bound_instead_of_whitelisted(self):
        with fixed_sources() as (_, reader):
            original = reader(FIXED_PARENT_PIN, comp.FIXED_STATUS)
            actual = comp.fixed_transform(comp.FIXED_STATUS, original)
            for bad in [actual.replace(b'OPEN', b'CLOSED', 1), actual + b'\nunchecked status\n']:
                with self.assertRaises(AssertionError):
                    comp.fixed_inverse(comp.FIXED_STATUS, bad)

    def test_structured_provenance_count_and_method_preservation(self):
        with fixed_sources() as (_, reader):
            actual = comp.fixed_transform(comp.HEAT_METADATA, reader(FIXED_PARENT_PIN, comp.HEAT_METADATA))
            self.assertEqual(actual.count(comp.FIXED_SOURCE.encode()), 1)
            self.assertEqual(actual.count(comp.FIXED_BASE.encode()), 1)
            self.assertEqual(actual.count(comp.FIXED_METADATA_NOTE.encode()), 1)
            self.assertEqual(actual.count(b'    - method: "agent"'), 1)
            self.assertNotIn(b'    - method: "agent-assisted"', actual)
            self.assertEqual(comp.fixed_inverse(comp.HEAT_METADATA, actual), reader(FIXED_PARENT_PIN, comp.HEAT_METADATA))

    def test_source_omission_mode_blob_extra_path_rejected(self):
        with fixed_sources() as (trees, _):
            path = sorted(comp.FIXED_ADDED)[0]
            for mutation in ['omit', 'mode', 'blob', 'extra']:
                bad = dict(trees[comp.FIXED_SOURCE])
                if mutation == 'omit':
                    bad.pop(path)
                elif mutation == 'mode':
                    bad[path] = ('100755', bad[path][1])
                elif mutation == 'blob':
                    bad[path] = ('100644', '0' * 40)
                else:
                    bad['unexpected.lean'] = ('100644', '0' * 40)
                with patch.object(comp, 'parent_tree', side_effect=lambda c: bad if c == comp.FIXED_SOURCE else trees[c]), self.assertRaises(AssertionError):
                    comp.expected_identity()

    def test_complete_predecessor_policy_rejects_drift(self):
        with fixed_sources() as (trees, _):
            path = 'curvature/lean-toolchain'
            for mutation in ['omit', 'mode', 'blob']:
                bad = dict(trees[FIXED_PARENT_PIN])
                if mutation == 'omit':
                    bad.pop(path)
                elif mutation == 'mode':
                    bad[path] = ('100755', bad[path][1])
                else:
                    bad[path] = ('100644', '0' * 40)
                with patch.object(comp, 'parent_tree', side_effect=lambda c: bad if c == FIXED_PARENT_PIN else trees[c]), self.assertRaises(AssertionError):
                    comp.expected_identity()

    def test_merge_base_drift_does_not_expand_nine_path_scope(self):
        with fixed_sources() as (trees, _):
            bad = dict(trees[comp.FIXED_BASE])
            bad['curvature/lean-toolchain'] = ('100644', '0' * 40)
            with patch.object(comp, 'parent_tree', side_effect=lambda c: bad if c == comp.FIXED_BASE else trees[c]), self.assertRaises(AssertionError):
                comp.expected_identity()

    def test_actual_original_import_bodies_accept_actual_expanded_bytes(self):
        with fixed_sources():
            local = fixed_semantic_local()
            calls = []
            for name in ['legacy_check_imports', 'check_imports']:
                original = getattr(local, name)
                setattr(local, name, lambda *args, name=name, original=original: (calls.append((name, args)), original(*args))[1])
            actual = (comp.ROOT / comp.HEAT_ROOT).read_bytes()
            comp.fixed_check_imports(local, actual)
            self.assertEqual([name for name, _ in calls], ['legacy_check_imports', 'check_imports'])
            master = comp.fixed_transform(comp.HEAT_ROOT, comp.contraction_transform(comp.HEAT_ROOT, comp.heat_transform(comp.HEAT_ROOT, fixed_semantic_blob(local.INTEGRATION_PARENT, comp.HEAT_ROOT))))
            self.assertEqual(calls[1][1], (actual, master, fixed_semantic_blob(local.INTEGRATION_PARENT, comp.HEAT_ROOT)))

    def test_actual_original_parsed_metadata_bodies_accept_expanded_bytes(self):
        with fixed_sources():
            comp.fixed_check_metadata(fixed_semantic_local(), (comp.ROOT / comp.HEAT_METADATA).read_bytes().decode())

    def test_metadata_callback_routing_uses_actual_bytes_and_exact_inverse(self):
        with fixed_sources() as (_, reader):
            events = []
            local = types.SimpleNamespace(INTEGRATION_PARENT='controlled-semantic-base', blob=lambda commit, path: reader(comp.HEAT_PARENT, path), legacy_check_metadata=lambda raw: events.append(('legacy', raw)), check_metadata=lambda *args: events.append(('current', args)))
            actual = (comp.ROOT / comp.HEAT_METADATA).read_bytes()
            comp.fixed_check_metadata(local, actual.decode())
            prior = reader(comp.HEAT_PARENT, comp.HEAT_METADATA)
            self.assertEqual(events, [('legacy', prior.decode()), ('current', (actual, actual, prior))])

    def test_original_source_provenance_regression_runs_on_actual_fixture(self):
        runpy.run_path(str(comp.ROOT/'curvature/scripts/point4_fixed_background_heat_source_test.py'), run_name='__main__')

    def test_bad_inverse_prevents_both_import_and_metadata_bodies(self):
        with fixed_sources():
            events = []
            local = types.SimpleNamespace(legacy_check_imports=lambda *a: events.append('old-import'), check_imports=lambda *a: events.append('current-import'), legacy_check_metadata=lambda *a: events.append('old-metadata'), check_metadata=lambda *a: events.append('current-metadata'))
            for path, callback in [(comp.HEAT_ROOT, comp.fixed_check_imports), (comp.HEAT_METADATA, comp.fixed_check_metadata)]:
                with self.assertRaises(AssertionError):
                    callback(local, (comp.ROOT / path).read_bytes() + b'\nextra\n')
            self.assertEqual(events, [])

    def test_current_import_primary_exception_identity_preserved(self):
        with fixed_sources():
            local = fixed_semantic_local()
            primary = RuntimeError('actual current import failure')
            original = local.check_imports
            events = []

            def fail(*args):
                original(*args)
                events.append('actual body passed')
                raise primary
            local.check_imports = fail
            with self.assertRaises(RuntimeError) as error:
                comp.fixed_check_imports(local, (comp.ROOT / comp.HEAT_ROOT).read_bytes())
            self.assertIs(error.exception, primary)
            self.assertEqual(events, ['actual body passed'])

    def test_legacy_failure_stops_current_body(self):
        with fixed_sources():
            primary = RuntimeError('legacy body failure')
            events = []
            local = types.SimpleNamespace(legacy_check_imports=lambda *a: (_ for _ in ()).throw(primary), check_imports=lambda *a: events.append('current'))
            with self.assertRaises(RuntimeError) as error:
                comp.fixed_check_imports(local, (comp.ROOT / comp.HEAT_ROOT).read_bytes())
            self.assertIs(error.exception, primary)
            self.assertEqual(events, [])

    def test_weighted_new_callback_failure_runs_post_and_restores_slots(self):
        with fixed_sources():
            local = fixed_semantic_local()
            primary = RuntimeError('fixed current semantic failure')
            original = local.check_imports

            def fail(*args):
                original(*args)
                raise primary
            local.check_imports = fail
            helper = types.SimpleNamespace(check_imports=object(), check_metadata=object())
            slots = (helper.check_imports, helper.check_metadata)
            events = []
            namespace = {'expected_sources': lambda: {}, 'public_paths': lambda: set(), 'historical_c2': lambda: helper, '_composition_original_public_paths': lambda: set(), 'restored_exact_head_workflow': object(), 'UNIT_FILE_SHA256': {}}

            def current(schema):
                namespace['historical_c2']().check_imports((comp.ROOT / comp.HEAT_ROOT).read_bytes())
            namespace['_composition_original_check_current'] = current
            before = dict(namespace)
            with patch.object(comp, 'verify_current', side_effect=lambda: (events.append('identity'), comp.parse_tree(comp.git('ls-tree','-rz','HEAD')))[1]), patch.object(comp.importlib, 'import_module', return_value=local):
                with self.assertRaises(RuntimeError) as error:
                    comp.weighted_leaf(namespace)
            self.assertIs(error.exception, primary)
            self.assertEqual(events, ['identity', 'identity'])
            self.assertEqual((helper.check_imports, helper.check_metadata), slots)
            for name in before:
                self.assertIs(namespace[name], before[name])

    def test_new_default_factory_captures_original_exactly_once_and_restores(self):
        global FIXED_FIXTURES
        events = []
        data = b'controlled fixed-background default reader\n'
        before = comp.git
        old_fixture = FIXED_FIXTURES
        FIXED_FIXTURES = None

        def original(*args):
            events.append(args)
            return data
        try:
            with patch.object(comp, 'parent_tree', return_value={'reader.txt': ('100644', comp.blob_id(data))}), patch.object(comp, 'git', original):
                with fixed_sources() as (_, reader):
                    with patch.object(comp, 'git', side_effect=lambda cmd, name: reader(*name.split(':', 1))) as forward:
                        self.assertEqual(comp.git('show', comp.FIXED_SOURCE + ':reader.txt'), data)
                        forward.assert_called_once_with('show', comp.FIXED_SOURCE + ':reader.txt')
                self.assertIs(comp.git, original)
            self.assertEqual(events, [('show', comp.FIXED_SOURCE + ':reader.txt')])
            self.assertIs(comp.git, before)
        finally:
            FIXED_FIXTURES = old_fixture

    def test_new_default_factory_uses_owned_genuine_git_with_fixture_flags_cleared(self):
        global FIXED_FIXTURES
        old_fixture = FIXED_FIXTURES
        FIXED_FIXTURES = None
        try:
            with tempfile.TemporaryDirectory(prefix='fixed-reader-', dir=ROOT) as directory:
                actual = Path(directory).resolve()
                self.assertEqual(actual.parent, ROOT.resolve())
                env = dict(comp.ENV, GIT_AUTHOR_NAME='Controlled fixture', GIT_AUTHOR_EMAIL='fixture@example.invalid', GIT_COMMITTER_NAME='Controlled fixture', GIT_COMMITTER_EMAIL='fixture@example.invalid')

                def git(*args, data=None):
                    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(actual), *args], input=data, env=env)
                git('init', '--quiet')
                data = b'actual owned fixed default Git bytes\n'
                oid = git('hash-object', '-w', '--stdin', data=data).decode().strip()
                tree = git('mktree', data=f'100644 blob {oid}\treader.txt\n'.encode()).decode().strip()
                commit = git('commit-tree', tree, data=b'Owned fixture only\n').decode().strip()
                with contextlib.ExitStack() as stack:
                    stack.enter_context(patch.object(comp, 'ROOT', actual))
                    stack.enter_context(patch.dict(comp.TREES, {commit: tree}))
                    for name in ['MASTER', 'SUPPORT', 'HEAT_PARENT', 'HEAT_SOURCE', 'CONTRACTION_PARENT', 'CONTRACTION_SOURCE', 'CONTRACTION_BASE', 'FIXED_PARENT', 'FIXED_SOURCE', 'FIXED_BASE']:
                        stack.enter_context(patch.object(comp, name, commit))
                    stack.enter_context(patch.dict(globals(), {'OFFLINE': None, 'HEAT_FIXTURES': None, 'CONTRACTION_FIXTURES': None}))
                    with fixed_sources() as (trees, reader):
                        self.assertEqual(trees, {commit: {'reader.txt': ('100644', oid)}})
                        with patch.object(comp, 'git', side_effect=lambda cmd, name: reader(*name.split(':', 1))) as forward:
                            self.assertEqual(comp.git('show', commit + ':reader.txt'), data)
                            forward.assert_called_once_with('show', commit + ':reader.txt')
        finally:
            FIXED_FIXTURES = old_fixture

    def test_deliberately_uncaptured_reader_mutation_reproduces_recursion(self):
        data = b'mutation control\n'
        with patch.object(comp, 'git', return_value=data):
            bad = lambda commit, path: comp.git('show', commit + ':' + path)
            with patch.object(comp, 'git', side_effect=lambda cmd, name: bad(*name.split(':', 1))):
                with self.assertRaises(RecursionError):
                    comp.git('show', comp.FIXED_SOURCE + ':reader.txt')

import functools

AXIOM_INVENTORY_FIXTURE = {'master': 'e883681caa862277857ee825a547502e8f3ec036', 'contraction_source': '93aa44010811b9145d6ff79abac3ed506ad51c29', 'jobs': [112650426668, 112681114319], 'sources': {'contraction': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.MetricContractedDeTurckField\n\n#print axioms PoincareCurvature.metricBilinearContraction_eq_sum_inverseGram\n#print axioms PoincareCurvature.metricContractSymbol_ne_ordinaryTraceRaisedSymbol_conformal_two\n#print axioms CovariantDerivative.metricConnectionDifferenceVector_localFrameCoeff\n#print axioms CovariantDerivative.metricConnectionDifferenceVector_eq_zero_of_isLeviCivita\n#print axioms RicciFlow.metricContractedDeTurckVectorField_eq_zero_of_isLeviCivita\n\n#print axioms RicciFlow.metricContractedDeTurckVectorField_eq_standardDeTurckVectorField\n', 'coordinate_connection': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateJetConnectionDerivative\n\n#print axioms PoincareCurvature.hasDerivAt_nonsing_inv_entry_of_det_ne_zero\n#print axioms PoincareCurvature.CoordinateMatrixJet.hasDerivAt_coordinateLine\n#print axioms PoincareCurvature.CoordinateMatrixJet.hasDerivAt_comp_coordinateLine\n#print axioms PoincareCurvature.CoordinateMatrixJet.differentiableAt_inverse_entry\n#print axioms PoincareCurvature.CoordinateMatrixJet.fderiv_inverse_apply\n#print axioms PoincareCurvature.CoordinateMatrixJet.inverseFirst_eq_sum\n#print axioms PoincareCurvature.CoordinateMatrixJet.differentiableAt_christoffel\n#print axioms PoincareCurvature.CoordinateMatrixJet.fderiv_christoffel_apply\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.invMetricOfJet_coordinateJet_eq_inverse\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.derivInvMetricOfJet_coordinateJet_eq_inverseFirst\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.fderiv_invMetricOfJet_coordinateJet_apply\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.christoffelOfJet_coordinateJet_eq_christoffel\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.derivChristoffelOfJet_coordinateJet_eq_christoffelFirst\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.fderiv_christoffelOfJet_coordinateJet_apply\n', 'coordinate_jet': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateJetPrincipalRemainder\n\n#print axioms PoincareCurvature.CoordinateMatrixJet.component_contDiffAt\n#print axioms PoincareCurvature.CoordinateMatrixJet.component_hasFDerivAt\n#print axioms PoincareCurvature.CoordinateMatrixJet.first_eq_matrix_fderiv\n#print axioms PoincareCurvature.CoordinateMatrixJet.component_differential_hasFDerivAt\n#print axioms PoincareCurvature.CoordinateMatrixJet.first_component_hasFDerivAt\n#print axioms PoincareCurvature.CoordinateMatrixJet.fderiv_first_apply\n#print axioms PoincareCurvature.CoordinateMatrixJet.second_derivative_symm\n#print axioms PoincareCurvature.CoordinateMatrixJet.first_tensor_symm\n#print axioms PoincareCurvature.CoordinateMatrixJet.second_tensor_symm\n#print axioms RicciFlow.AnalyticPDE.coordinateJet_deriv2_derivative_symm\n#print axioms RicciFlow.AnalyticPDE.coordinateJet_deriv2_tensor_symm\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRD_coordinateJet_eq_principal_add_lowerOrder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJet_coordinateJet_eq_principal_add_lowerOrder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJet_coordinateJet_eq_frozenPrincipal_add_remainder\n', 'coordinate_operator': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateRicciDeTurckOperator\n\n#print axioms PoincareCurvature.CoordinateMatrixJet.background_component_hasFDerivAt\n#print axioms PoincareCurvature.CoordinateMatrixJet.differentiableAt_deTurck\n#print axioms PoincareCurvature.CoordinateMatrixJet.deTurckFirst_eq_productRule\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.deTurck_eq_coordinateJet\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.deTurckFirst_eq_coordinateJet\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRicci_eq_coordinateJet\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateLie_eq_coordinateJet\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_correctedJet\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_principal_add_lowerOrder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_frozenPrincipal_add_remainder\n', 'principal_remainder': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckPrincipalRemainder\n\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.secondJetLinearReaction_eq_principal\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDOfJet_eq_principal_add_lowerOrder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDOfJet_eq_of_val_deriv1\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDWithBackgroundJetOfJet_eq\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDWithBackgroundJetOfJet_eq_of_val_deriv1\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_principal_add_lowerOrder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.abs_frozenPrincipalError_le\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_zero\n#print axioms RicciFlow.AnalyticPDE.GenuinePhiRD.hasDerivAt_conventionalContraction\n', 'chosen_lc_coordinate': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateChristoffel\n\n#print axioms PoincareCurvature.PreferredCoordinateFrame.frame_eq_inverseChart_derivative\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero\n#print axioms PoincareCurvature.PreferredCoordinateFrame.toModel_coordinateVector\n#print axioms PoincareCurvature.PreferredCoordinateFrame.fderiv_comp_toModel_coordinateVector\n#print axioms CovariantDerivative.koszul_formula_at\n#print axioms RicciFlow.isOpen_chosenLCCoordinateDomain\n#print axioms RicciFlow.chosenLCMetricCoordinates_symm\n#print axioms RicciFlow.contDiffOn_chosenLCMetricCoordinates\n#print axioms RicciFlow.chosenLCMetricCoordinates_det_ne_zero_on_domain\n#print axioms RicciFlow.first_chosenLCMetricCoordinates_eq_mvfderiv\n#print axioms RicciFlow.chosenLC_inner_coordinateFrame_eq_first_metric\n#print axioms RicciFlow.chosenLC_coordinateFrameCoeff_eq_christoffel\n#print axioms RicciFlow.chosenLCConnectionCoordinates_eq_christoffel\n#print axioms RicciFlow.chosenLCConnectionCoordinates_eventuallyEq_christoffel\n#print axioms RicciFlow.differentiableAt_chosenLCConnectionCoordinates\n#print axioms RicciFlow.fderiv_chosenLCConnectionCoordinates_apply\n', 'chosen_lc_curvature': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateCurvature\n\n#print axioms PoincareCurvature.CoordinateMatrixJet.christoffel_lower_symm\n#print axioms PoincareCurvature.CoordinateMatrixJet.christoffel_lower_eventuallyEq\n#print axioms PoincareCurvature.CoordinateMatrixJet.christoffelFirst_lower_symm\n#print axioms PoincareCurvature.CoordinateMatrixJet.coordinateRicci_eq_christoffel_curvature_trace\n#print axioms RicciFlow.contMDiffOn_chosenLCCoordinateFrameDerivative\n#print axioms RicciFlow.contMDiffOn_chosenLCCoordinateFrameDerivativeCoeff\n#print axioms RicciFlow.contDiffOn_scalarReadout_chosenLCCoordinateFrameDerivativeCoeff\n#print axioms RicciFlow.chosenLC_coordinateFrameCoeff_mvfderiv_eq_christoffelFirst\n#print axioms RicciFlow.chosenLC_coordinateFrameCoeff_curvatureTensor_eq\n#print axioms RicciFlow.coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor_transpose\n#print axioms RicciFlow.coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor\n', 'standard_coordinate_operator': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.StandardRicciDeTurckCoordinateOperator\n\n#print axioms RicciFlow.contMDiffOn_actualBackgroundFrameDerivative\n#print axioms RicciFlow.contMDiffOn_actualBackgroundFrameCoeff\n#print axioms RicciFlow.contDiffOn_scalarReadout_actualBackgroundFrameCoeff\n#print axioms RicciFlow.contDiffOn_actualBackgroundCoordinates\n#print axioms RicciFlow.actualBackgroundCoordinates_eq_frameCoeff\n#print axioms RicciFlow.backgroundFirst_actualBackgroundCoordinates_eq_mvfderiv\n#print axioms RicciFlow.chosenLC_coordinateFrame_metricCompatibility\n#print axioms RicciFlow.standardDeTurck_coordinateFrameCoeff_eq_deTurck\n#print axioms RicciFlow.standardDeTurckCoordinates_eq_deTurck\n#print axioms RicciFlow.standardDeTurckCoordinates_eventuallyEq_deTurck\n#print axioms RicciFlow.differentiableAt_standardDeTurckCoordinates\n#print axioms RicciFlow.fderiv_standardDeTurckCoordinates_apply\n#print axioms RicciFlow.contMDiffOn_standardDeTurckFrameCoeff\n#print axioms RicciFlow.contDiffOn_scalarReadout_standardDeTurckFrameCoeff\n#print axioms RicciFlow.standardDeTurck_coordinateFrameCoeff_mvfderiv_eq_deTurckFirst\n#print axioms RicciFlow.standardDeTurck_coordinateFrameCoeff_covariantDerivative_eq\n#print axioms RicciFlow.standardDeTurckCorrection_coordinateFrame_eq_coordinateLie\n#print axioms RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD\n#print axioms RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_correctedJet\n#print axioms RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_principal_add_lowerOrder\n#print axioms RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_frozenPrincipal_add_remainder\n', 'frozen_metric_principal': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ChosenLCFrozenTensorHeat\n\n#print axioms PoincareCurvature.second_fderiv_linear_readout\n#print axioms RicciFlow.AnalyticPDE.localFrameInChart_preferred_eq_basis\n#print axioms RicciFlow.AnalyticPDE.chosenLC_localFrameInverseGramMatrix_eq_inverse\n#print axioms RicciFlow.AnalyticPDE.chosenLCFrozenTensorHeatPrincipalCoefficient_apply\n#print axioms RicciFlow.AnalyticPDE.second_finiteCylinderTensorReadout\n#print axioms RicciFlow.AnalyticPDE.deriv_finiteCylinderTensorReadout\n#print axioms RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL\n#print axioms RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives\n\n-- Full elaborated types expose geometric assumptions and the actual derivatives.\n#check @RicciFlow.AnalyticPDE.chosenLCFrozenTensorHeatPrincipalCoefficient_apply\n#check @RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives\n\nnoncomputable section\nopen scoped Manifold ContDiff BigOperators\nopen RicciFlow.AnalyticPDE PoincareCurvature.PreferredCoordinateFrame\n\nsection GenuineReadout\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]\n  {d : ℕ} {t₀ T α : ℝ}\n\n-- The output reversal is definitional and does not assume tensor symmetry.\nexample (b : Module.Basis (Fin d) ℝ E)\n    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)\n    (s : ℝ) (ξ : Fin d → ℝ) (i j : Fin d) :\n    finiteCylinderTensorReadout b u s ξ i j =\n      FiniteParabolicC2AlphaBanach.value u (s, toModel b ξ) (j, i) := rfl\n\n-- No positive alpha, time nonemptiness, or separately supplied C2 certificate.\nexample (b : Module.Basis (Fin d) ℝ E)\n    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)\n    {s : ℝ} (hs : s ∈ Set.Ioc t₀ T) (ξ : Fin d → ℝ) (a c i j : Fin d) :\n    PoincareCurvature.CoordinateMatrixJet.second (finiteCylinderTensorReadout b u s) ξ a c i j =\n      FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, toModel b ξ)\n        (b a) (b c) (j, i) :=\n  second_finiteCylinderTensorReadout b u hs ξ a c i j\nend GenuineReadout\n\nsection ActualMetric\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n  [FiniteDimensional ℝ E] [CompleteSpace E]\n  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}\n  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]\n  [IsManifold I ∞ M] [I.Boundaryless]\n  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]\n  {d : ℕ} {t₀ T α : ℝ}\n\n-- No ambient Riemannian-bundle instance is supplied: the actual g slice selects it.\nexample (g : RicciFlow.MetricFamily (I := I) (M := M)) (tStar : ℝ)\n    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}\n    (hx₀ : x₀ ∈ (extChartAt I p).source)\n    (Q : E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) (out : Fin d × Fin d) :\n    chosenLCFrozenTensorHeatPrincipalCoefficient g tStar p b x₀ Q out =\n      ∑ a : Fin d, ∑ c : Fin d,\n        PoincareCurvature.CoordinateMatrixJet.inverse (RicciFlow.chosenLCMetricCoordinates g tStar p b)\n          (RicciFlow.chosenLCCoordinatePoint (I := I) p b x₀) a c * Q (b a) (b c) out :=\n  chosenLCFrozenTensorHeatPrincipalCoefficient_apply g tStar p b hx₀ Q out\nend ActualMetric\n', 'weak_laplacian': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatWeakLaplacian\n\n-- Exact elaborated theorem types, including local-domain and regularity premises.\n-- The main type retains ContMDiffVectorBundle 3 for the tangent bundle.\n-- Metric regularity is only IsContMDiffRiemannianBundle I 1.\n-- Tensor C2 is confined to e.baseSet; no induced-three connection class is supplied.\n#check CovariantDerivative.contMDiffOn_localTwoTensorConnectionCoefficient_one\n#check CovariantDerivative.contDiffOn_localTwoTensorConnectionCoefficientInChart_one\n#check RicciFlow.AnalyticPDE.contDiffOn_localTensorCoordinates_of_contMDiffOn_two\n#print RicciFlow.AnalyticPDE.connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_baseC1_and_localC2\n\n#print axioms CovariantDerivative.contMDiffOn_localTwoTensorConnectionCoefficient_one\n#print axioms CovariantDerivative.contDiffOn_localTwoTensorConnectionCoefficientInChart_one\n#print axioms RicciFlow.AnalyticPDE.contDiffOn_localTensorCoordinates_of_contMDiffOn_two\n#print axioms RicciFlow.AnalyticPDE.connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_baseC1_and_localC2\n', 'boundaryless_chart_frames': 'import PoincareCurvature.Analysis.PreferredCoordinateFrame\n\n#print axioms PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target\n#print axioms PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range\n#print axioms PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv\n#print axioms PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback\n#print axioms PoincareCurvature.PreferredCoordinateFrame.frame_eq_inverseChart_derivative\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv\n#print axioms PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero\n#print axioms PoincareCurvature.PreferredCoordinateFrame.toModel_coordinateVector\n#print axioms PoincareCurvature.PreferredCoordinateFrame.fderiv_comp_toModel_coordinateVector\n\n#eval IO.println "BOUNDARYLESS_TYPES_BEGIN"\n#check @PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target\n#check @PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range\n#check @PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv\n#check @PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback\n#check @PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const\n#check @PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv\n#check @PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero\n\n#eval IO.println "BOUNDARYLESS_TYPES_END"\n\nopen Set\nopen scoped Manifold ContDiff\n\n-- Existing callers with a boundaryless model obtain the weaker instance.\nsection ModelBoundarylessRegression\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n    [FiniteDimensional ℝ E] [CompleteSpace E]\n    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}\n    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]\n    [IsManifold I ∞ M] [I.Boundaryless]\n    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]\n\nexample : BoundarylessManifold I M := inferInstance\n\nexample (p : M) : IsOpen (extChartAt I p).target :=\n  PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target p\n\nexample {ι : Type*} (p : M) (b : Module.Basis ι ℝ E) {x : M}\n    (hx : x ∈ (extChartAt I p).source) (i j : ι) :\n    VectorField.mlieBracket I\n      (PoincareCurvature.PreferredCoordinateFrame.frame (I := I) p b i)\n      (PoincareCurvature.PreferredCoordinateFrame.frame (I := I) p b j) x = 0 :=\n  PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero p b hx i j\nend ModelBoundarylessRegression\n', 'c2_heat_trace': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace\n\nset_option pp.proofs false\n\nopen RicciFlow.AnalyticPDE\nopen scoped Topology BigOperators\n\n#print PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous\n#print PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus\n#print abs_heatSemigroupND_sub_self_le_of_local_modulus\n#print norm_heatSemigroupNDbcf_sub_self_le_of_modulus\n#print continuousAt_heatFlowPathBcf_zero_of_uniformContinuous\n#print tendstoUniformlyOn_heatSemigroupND_zero\n#print EuclideanBoundedC2Data.uniformContinuous_value\n#print EuclideanBoundedC2Data.uniformContinuous_first\n#print EuclideanBoundedC2Data.tendstoUniformlyOn_heatGradient_zero\n#print EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_zero\n#print EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero\n#print EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero\n\n#print axioms PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous\n#print axioms PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus\n#print axioms abs_heatSemigroupND_sub_self_le_of_local_modulus\n#print axioms norm_heatSemigroupNDbcf_sub_self_le_of_modulus\n#print axioms continuousAt_heatFlowPathBcf_zero_of_uniformContinuous\n#print axioms tendstoUniformlyOn_heatSemigroupND_zero\n#print axioms EuclideanBoundedC2Data.uniformContinuous_value\n#print axioms EuclideanBoundedC2Data.uniformContinuous_first\n#print axioms EuclideanBoundedC2Data.tendstoUniformlyOn_heatGradient_zero\n#print axioms EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_zero\n#print axioms EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero\n#print axioms EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero\n\n-- Dimension zero is not excluded from the global endpoint trace or generator.\nexample (D : EuclideanBoundedC2Data 0) :\n    ContinuousAt (fun t : ℝ =>\n      (heatFlowPathBcf D.value t,\n        (fun k => heatFlowPathBcf (D.first k) t),\n        (fun j k => heatFlowPathBcf (D.second j k) t))) 0 :=\n  D.continuousAt_heatC2Trace_zero (fun j => Fin.elim0 j)\n\nexample (D : EuclideanBoundedC2Data 0) (x : Fin 0 → ℝ) :\n    HasDerivWithinAt (fun t => heatFlowPathBcf D.value t x)\n      (∑ k : Fin 0, D.second k k x) (Set.Ici 0) 0 :=\n  D.hasDerivWithinAt_heatFlowPathBcf_apply_zero x\n', 'weighted_initial_heat': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatWeightedInitialHolder\n\nset_option pp.proofs false\n\nopen RicciFlow.AnalyticPDE Filter\nopen scoped Topology BigOperators\n\n#print initialHeatHolderConstant\n#print heatEvolvedWeightedC2AlphaData\n#print abs_heatSemigroupNDbcf_spatial_holder_le\n#print heatSemigroupNDbcf_split_initial_error\n#print abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant\n#print initialHeatHolderConstant_weight_identity\n#print tendsto_weighted_initialHeatHolderConstant_zero\n#print heatEvolvedWeightedC2AlphaData_base_eq\n#print heatEvolvedWeightedC2AlphaData_holderConstant_eq\n#print EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero\n#print EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero\n\n#print axioms abs_heatSemigroupNDbcf_spatial_holder_le\n#print axioms heatSemigroupNDbcf_split_initial_error\n#print axioms initialHeatHolderConstant_nonneg\n#print axioms abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant\n#print axioms initialHeatHolderConstant_weight_identity\n#print axioms tendsto_weighted_initialHeatHolderConstant_zero\n#print axioms heatEvolvedWeightedC2AlphaData\n#print axioms heatEvolvedWeightedC2AlphaData_base_eq\n#print axioms heatEvolvedWeightedC2AlphaData_holderConstant_eq\n#print axioms EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero\n#print axioms EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero\n\n-- The producer carries the original actual value, first and Hessian derivatives.\nexample {n : ℕ} (D : EuclideanBoundedC2Data n) {t α : ℝ}\n    (ht : 0 < t) (hα : 0 < α) (hα1 : α < 1) :\n    (heatEvolvedWeightedC2AlphaData D ht hα.le hα1.le).base =\n      heatEvolvedBoundedC2Data D ht := rfl\n\n-- No initial positive-exponent Hölder hypothesis is added to the headline.\nexample {n : ℕ} (D : EuclideanBoundedC2Data n)\n    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))\n    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :\n    Tendsto (fun t : ℝ => t ^ (α / 2) *\n      (if ht : 0 < t then\n        (heatEvolvedWeightedC2AlphaData D ht hα.le hα1.le).hessianHolderConstant\n      else 0)) (𝓝[>] 0) (𝓝 0) :=\n  D.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero hsecond hα hα1.le\n\n-- Dimension zero remains valid, without an added positive-rank assumption.\nexample (D : EuclideanBoundedC2Data 0) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :\n    Tendsto (fun t : ℝ => t ^ (α / 2) *\n      (if ht : 0 < t then\n        (heatEvolvedWeightedC2AlphaData D ht hα.le hα1).hessianHolderConstant\n      else 0)) (𝓝[>] 0) (𝓝 0) :=\n  D.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero (fun j => Fin.elim0 j) hα hα1\n\nexample (D : EuclideanBoundedC2Data 0) (α t : ℝ) :\n    D.initialHessianHolderConstant α t = 0 := by\n  simp [EuclideanBoundedC2Data.initialHessianHolderConstant]\n'}, 'baseline_blobs': {'contraction': 'f411469fcdc46e15964f047c396e15889ad2b83e', 'coordinate_connection': 'd037dd379a7145b0eb17ebe8c92a205ebbbb7e34', 'coordinate_jet': '7b4f202b3e71de35850ea58ed82719abe23a410c', 'coordinate_operator': 'be9d273cbb1799dca288cd88b4297031668cf238', 'principal_remainder': '5350fde6d70299bf212d4c45bc0304b816936e8b', 'chosen_lc_coordinate': '883b4cb4252999f2eb4be9f6c38995827cdb5189', 'chosen_lc_curvature': '4eada83ad5afd298a82909fe02eba704ab76b2a7', 'standard_coordinate_operator': '40e6e86435f601f616c29d514e381277e0d91f33', 'frozen_metric_principal': '759de0f79f1c1fa268306686d8e5683f7b9acea0', 'weak_laplacian': '9b4c3ac99770db4e7b48729760113e118ca53f02', 'boundaryless_chart_frames': '41e0ee8972beb25ad5a0132cb0384749e6cc32f1', 'c2_heat_trace': '9ebe118352ccddb9f47f8191bfe0615f18aa5aee', 'weighted_initial_heat': 'cd6e1dc245bb2fca4a019d09afe4c5b8423fe769'}, 'current_contraction': 'import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.MetricContractedDeTurckJointRegularity\n\n#print axioms PoincareCurvature.metricBilinearContraction_eq_sum_inverseGram\n#print axioms PoincareCurvature.metricContractSymbol_ne_ordinaryTraceRaisedSymbol_conformal_two\n#print axioms CovariantDerivative.metricConnectionDifferenceVector_localFrameCoeff\n#print axioms CovariantDerivative.metricConnectionDifferenceVector_eq_zero_of_isLeviCivita\n#print axioms RicciFlow.metricContractedDeTurckVectorField_eq_zero_of_isLeviCivita\n\n#print axioms RicciFlow.metricContractedDeTurckVectorField_eq_standardDeTurckVectorField\n#print axioms PoincareCurvature.ParametrizedInner.contMDiffOn_timeDependentMetricContraction\n#print axioms PoincareCurvature.ParametrizedInner.contMDiff_paramSection_neg\n#print axioms RicciFlow.metricContractedDeTurckVectorField_eq_sum_inverseGram_correction\n#print axioms RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correction\n#print axioms RicciFlow.contMDiff_metricContractedDeTurckGaugeField_of_joint_correction\n#print axioms RicciFlow.exists_pos_metricContractedDiffeomorph3GaugeFlowOn_of_joint_correction\n#print axioms RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correctionFunctional\n', 'outputs': {'contraction': "'PoincareCurvature.metricBilinearContraction_eq_sum_inverseGram' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.metricContractSymbol_ne_ordinaryTraceRaisedSymbol_conformal_two' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'CovariantDerivative.metricConnectionDifferenceVector_localFrameCoeff' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'CovariantDerivative.metricConnectionDifferenceVector_eq_zero_of_isLeviCivita' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.metricContractedDeTurckVectorField_eq_zero_of_isLeviCivita' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.metricContractedDeTurckVectorField_eq_standardDeTurckVectorField' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.ParametrizedInner.contMDiffOn_timeDependentMetricContraction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.ParametrizedInner.contMDiff_paramSection_neg' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.metricContractedDeTurckVectorField_eq_sum_inverseGram_correction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contMDiff_metricContractedDeTurckGaugeField_of_joint_correction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.exists_pos_metricContractedDiffeomorph3GaugeFlowOn_of_joint_correction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contMDiff_metricContractedDeTurckVectorField_of_joint_correctionFunctional' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'coordinate_connection': "'PoincareCurvature.hasDerivAt_nonsing_inv_entry_of_det_ne_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.hasDerivAt_coordinateLine' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.hasDerivAt_comp_coordinateLine' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.differentiableAt_inverse_entry' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.fderiv_inverse_apply' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.inverseFirst_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.differentiableAt_christoffel' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.fderiv_christoffel_apply' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.invMetricOfJet_coordinateJet_eq_inverse' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.derivInvMetricOfJet_coordinateJet_eq_inverseFirst' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.fderiv_invMetricOfJet_coordinateJet_apply' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.christoffelOfJet_coordinateJet_eq_christoffel' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.derivChristoffelOfJet_coordinateJet_eq_christoffelFirst' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.fderiv_christoffelOfJet_coordinateJet_apply' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'coordinate_jet': "'PoincareCurvature.CoordinateMatrixJet.component_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.component_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.first_eq_matrix_fderiv' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.component_differential_hasFDerivAt' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.first_component_hasFDerivAt' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.fderiv_first_apply' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.second_derivative_symm' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.first_tensor_symm' depends on axioms: [propext, Classical.choice, Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.second_tensor_symm' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.coordinateJet_deriv2_derivative_symm' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.coordinateJet_deriv2_tensor_symm' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRD_coordinateJet_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJet_coordinateJet_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJet_coordinateJet_eq_frozenPrincipal_add_remainder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'coordinate_operator': "'PoincareCurvature.CoordinateMatrixJet.background_component_hasFDerivAt' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.differentiableAt_deTurck' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.deTurckFirst_eq_productRule' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.deTurck_eq_coordinateJet' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.deTurckFirst_eq_coordinateJet' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRicci_eq_coordinateJet' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateLie_eq_coordinateJet' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_correctedJet' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.coordinateRD_eq_frozenPrincipal_add_remainder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'principal_remainder': "'RicciFlow.AnalyticPDE.GenuinePhiRD.secondJetLinearReaction_eq_principal' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDOfJet_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDOfJet_eq_of_val_deriv1' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_sub_backgroundLieTerm' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDWithBackgroundJetOfJet_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.lowerOrderRDWithBackgroundJetOfJet_eq_of_val_deriv1' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.abs_frozenPrincipalError_le' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.phiRDWithBackgroundJetOfJet_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.GenuinePhiRD.hasDerivAt_conventionalContraction' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'chosen_lc_coordinate': "'PoincareCurvature.PreferredCoordinateFrame.frame_eq_inverseChart_derivative' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.toModel_coordinateVector' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.fderiv_comp_toModel_coordinateVector' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'CovariantDerivative.koszul_formula_at' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.isOpen_chosenLCCoordinateDomain' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLCMetricCoordinates_symm' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contDiffOn_chosenLCMetricCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLCMetricCoordinates_det_ne_zero_on_domain' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.first_chosenLCMetricCoordinates_eq_mvfderiv' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLC_inner_coordinateFrame_eq_first_metric' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLC_coordinateFrameCoeff_eq_christoffel' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLCConnectionCoordinates_eq_christoffel' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.chosenLCConnectionCoordinates_eventuallyEq_christoffel' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.differentiableAt_chosenLCConnectionCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.fderiv_chosenLCConnectionCoordinates_apply' depends on axioms: [propext, Classical.choice, Quot.sound]\n", 'chosen_lc_curvature': "'PoincareCurvature.CoordinateMatrixJet.christoffel_lower_symm' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.christoffel_lower_eventuallyEq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.christoffelFirst_lower_symm' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.CoordinateMatrixJet.coordinateRicci_eq_christoffel_curvature_trace' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contMDiffOn_chosenLCCoordinateFrameDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contMDiffOn_chosenLCCoordinateFrameDerivativeCoeff' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contDiffOn_scalarReadout_chosenLCCoordinateFrameDerivativeCoeff' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.chosenLC_coordinateFrameCoeff_mvfderiv_eq_christoffelFirst' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.chosenLC_coordinateFrameCoeff_curvatureTensor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor_transpose' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'standard_coordinate_operator': "'RicciFlow.contMDiffOn_actualBackgroundFrameDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contMDiffOn_actualBackgroundFrameCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contDiffOn_scalarReadout_actualBackgroundFrameCoeff' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.contDiffOn_actualBackgroundCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.actualBackgroundCoordinates_eq_frameCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.backgroundFirst_actualBackgroundCoordinates_eq_mvfderiv' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.chosenLC_coordinateFrame_metricCompatibility' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.standardDeTurck_coordinateFrameCoeff_eq_deTurck' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.standardDeTurckCoordinates_eq_deTurck' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.standardDeTurckCoordinates_eventuallyEq_deTurck' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.differentiableAt_standardDeTurckCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.fderiv_standardDeTurckCoordinates_apply' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contMDiffOn_standardDeTurckFrameCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.contDiffOn_scalarReadout_standardDeTurckFrameCoeff' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardDeTurck_coordinateFrameCoeff_mvfderiv_eq_deTurckFirst' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardDeTurck_coordinateFrameCoeff_covariantDerivative_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardDeTurckCorrection_coordinateFrame_eq_coordinateLie' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_correctedJet' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_principal_add_lowerOrder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.standardRicciDeTurckRHS_coordinateFrame_eq_frozenPrincipal_add_remainder' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'frozen_metric_principal': "'PoincareCurvature.second_fderiv_linear_readout' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.localFrameInChart_preferred_eq_basis' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.chosenLC_localFrameInverseGramMatrix_eq_inverse' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.chosenLCFrozenTensorHeatPrincipalCoefficient_apply' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.second_finiteCylinderTensorReadout' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.deriv_finiteCylinderTensorReadout' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'weak_laplacian': "'CovariantDerivative.contMDiffOn_localTwoTensorConnectionCoefficient_one' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'CovariantDerivative.contDiffOn_localTwoTensorConnectionCoefficientInChart_one' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.contDiffOn_localTensorCoordinates_of_contMDiffOn_two' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_baseC1_and_localC2' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'boundaryless_chart_frames': "'PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.frame_eq_inverseChart_derivative' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.toModel_coordinateVector' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.PreferredCoordinateFrame.fderiv_comp_toModel_coordinateVector' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\nBOUNDARYLESS_TYPES_BEGIN\n@PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]\n  [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2} [inst_4 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M] [inst_6 : ChartedSpace H M]\n  [IsManifold I (↑⊤) M] [BoundarylessManifold I M] (p : M), IsOpen (extChartAt I p).target\n@PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range : ∀ {E : Type u_1}\n  [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2}\n  [inst_4 : TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M]\n  [inst_6 : ChartedSpace H M] [IsManifold I (↑⊤) M] [BoundarylessManifold I M] (p : M),\n  (extChartAt I p).target ⊆ interior (Set.range ↑I)\n@PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv : ∀ {E : Type u_1}\n  [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2}\n  [inst_4 : TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M]\n  [inst_6 : ChartedSpace H M] [IsManifold I (↑⊤) M] [BoundarylessManifold I M] (p : M) {z : E},\n  z ∈ (extChartAt I p).target → mfderiv[Set.range ↑I] ↑(extChartAt I p).symm z = mfderiv% ↑(extChartAt I p).symm z\n@PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback : ∀ {E : Type u_1}\n  [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2}\n  [inst_4 : TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M]\n  [inst_6 : ChartedSpace H M] [IsManifold I (↑⊤) M] [BoundarylessManifold I M] (p : M) (V : (x : M) → TangentSpace I x)\n  {z : E},\n  z ∈ (extChartAt I p).target →\n    VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I (↑(extChartAt I p).symm) V (Set.range ↑I) z =\n      VectorField.mpullback (modelWithCornersSelf ℝ E) I (↑(extChartAt I p).symm) V z\n@PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]\n  [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2} [inst_4 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M] [inst_6 : ChartedSpace H M]\n  [inst_7 : IsManifold I (↑⊤) M] [BoundarylessManifold I M] [ContMDiffVectorBundle 2 E (TangentSpace I) I]\n  {ι : Type u_4} (p : M) (b : Module.Basis ι ℝ E) {z : E},\n  z ∈ (extChartAt I p).target →\n    ∀ (i : ι),\n      VectorField.mpullback (modelWithCornersSelf ℝ E) I (↑(extChartAt I p).symm)\n          (PoincareCurvature.PreferredCoordinateFrame.frame p b i) z =\n        (NormedSpace.fromTangentSpace z).symm (b i)\n@PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]\n  [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2} [inst_4 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M] [inst_6 : ChartedSpace H M]\n  [inst_7 : IsManifold I (↑⊤) M] [BoundarylessManifold I M] [ContMDiffVectorBundle 2 E (TangentSpace I) I]\n  {ι : Type u_4} (p : M) (b : Module.Basis ι ℝ E) {f : M → ℝ} {x : M},\n  x ∈ (extChartAt I p).source →\n    MDiffAt f x →\n      ∀ (i : ι),\n        (d% f x) (PoincareCurvature.PreferredCoordinateFrame.frame p b i x) =\n          (fderiv ℝ (PoincareCurvature.PreferredCoordinateFrame.scalarReadout p f) (↑(extChartAt I p) x)) (b i)\n@PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]\n  [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type u_2} [inst_4 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_5 : TopologicalSpace M] [inst_6 : ChartedSpace H M]\n  [inst_7 : IsManifold I (↑⊤) M] [BoundarylessManifold I M] [ContMDiffVectorBundle 2 E (TangentSpace I) I]\n  {ι : Type u_4} (p : M) (b : Module.Basis ι ℝ E) {x : M},\n  x ∈ (extChartAt I p).source →\n    ∀ (i j : ι),\n      VectorField.mlieBracket I (PoincareCurvature.PreferredCoordinateFrame.frame p b i)\n          (PoincareCurvature.PreferredCoordinateFrame.frame p b j) x =\n        0\nBOUNDARYLESS_TYPES_END\n", 'c2_heat_trace': "'PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.abs_heatSemigroupND_sub_self_le_of_local_modulus' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.norm_heatSemigroupNDbcf_sub_self_le_of_modulus' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.continuousAt_heatFlowPathBcf_zero_of_uniformContinuous' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.tendstoUniformlyOn_heatSemigroupND_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.uniformContinuous_value' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.uniformContinuous_first' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.tendstoUniformlyOn_heatGradient_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", 'weighted_initial_heat': "'RicciFlow.AnalyticPDE.abs_heatSemigroupNDbcf_spatial_holder_le' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.heatSemigroupNDbcf_split_initial_error' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.initialHeatHolderConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.initialHeatHolderConstant_weight_identity' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.tendsto_weighted_initialHeatHolderConstant_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.heatEvolvedWeightedC2AlphaData' depends on axioms: [propext, Classical.choice, Quot.sound]\n'RicciFlow.AnalyticPDE.heatEvolvedWeightedC2AlphaData_base_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.heatEvolvedWeightedC2AlphaData_holderConstant_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"}, 'public_record_scope': 'Exact axiom records and boundaryless type block extracted from current public job logs; source-only regression evidence, no new compiler result'}

class CurrentAxiomInventoryTests(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory(prefix='point4-current-axioms-',dir=pathlib.Path.cwd())
        self.addCleanup(self.directory.cleanup)
        self.root=pathlib.Path(self.directory.name).resolve()
        self.assertEqual(self.root.parent,pathlib.Path.cwd().resolve())
        self.folder=self.root/'logs';self.folder.mkdir()
        self.assertEqual(AXIOM_INVENTORY_FIXTURE['master'],comp.MASTER)
        self.assertEqual(AXIOM_INVENTORY_FIXTURE['contraction_source'],comp.CONTRACTION_SOURCE)
        env=dict(comp.ENV)
        def owned_git(*args,data=None):
            return subprocess.check_output(['git','--no-replace-objects','-C',str(self.root),*args],input=data,env=env)
        owned_git('init','--quiet');self.master={}
        for name,original in AXIOM_INVENTORY_FIXTURE['sources'].items():
            path=f'curvature/scripts/point4_{name}_probe.lean';raw=original.encode()
            oid=owned_git('hash-object','-w','--stdin',data=raw).decode().strip()
            self.assertEqual(oid,AXIOM_INVENTORY_FIXTURE['baseline_blobs'][name])
            self.master[path]=('100644',oid)
            target=self.root/path;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes((AXIOM_INVENTORY_FIXTURE['current_contraction'] if name=='contraction' else original).encode())
            (self.folder/(name+'.log')).write_bytes(AXIOM_INVENTORY_FIXTURE['outputs'][name].encode())
        @functools.lru_cache(maxsize=None)
        def objects(oid):return owned_git('cat-file','blob',oid)
        def original_git(*args):
            self.assertEqual(args[0],'show');self.assertEqual(len(args),2)
            commit,path=args[1].split(':',1);self.assertEqual(commit,comp.MASTER)
            return objects(self.master[path][1])
        self.original_git=original_git
        source=(comp.ROOT/'curvature/scripts/point4_c2_initial_heat_source_test.py').read_bytes()
        tree=ast.parse(source)
        functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'probe_names','check_axiom_output','check_boundaryless_types'}]
        self.assertEqual({n.name for n in functions},{'probe_names','check_axiom_output','check_boundaryless_types'})
        namespace={'re':comp.re}
        exec(compile(ast.Module(body=functions,type_ignores=[]),'immutable original axiom checker bodies','exec'),namespace)
        self.inherited=types.SimpleNamespace(**{n:namespace[n] for n in ('probe_names','check_axiom_output','check_boundaryless_types')},PROBES=comp.INHERITED_AXIOM_PROBES)
        linear=(comp.ROOT/'curvature/scripts/point4_linear_heat_geometry_source_test.py').read_bytes()
        functions=[n for n in ast.parse(linear).body if isinstance(n,ast.FunctionDef) and n.name in {'check_axiom_output','check_boundaryless_types'}]
        self.assertEqual({n.name for n in functions},{'check_axiom_output','check_boundaryless_types'})
        namespace={'re':comp.re}
        exec(compile(ast.Module(body=functions,type_ignores=[]),'immutable original linear axiom checker bodies','exec'),namespace)
        self.linear=types.SimpleNamespace(**{n:namespace[n] for n in ('check_axiom_output','check_boundaryless_types')},PROBES=comp.INHERITED_AXIOM_PROBES[:11])
        self.assertFalse(hasattr(self.linear,'probe_names'))

    @contextlib.contextmanager
    def sources(self):
        with patch.object(comp,'ROOT',self.root),patch.object(comp,'parent_tree',side_effect=lambda c:self.master if c==comp.MASTER else self.fail('unrequested predecessor')), \
             patch.object(comp,'git',side_effect=self.original_git):
            yield

    def actual_route(self,path):
        probes=comp.INHERITED_AXIOM_PROBES if 'c2_initial' in path or 'manifold_heat_release' in path else comp.INHERITED_AXIOM_PROBES[:11]
        inherited=types.SimpleNamespace(**vars(self.inherited if len(probes)==13 else self.linear));inherited.PROBES=probes
        module=types.SimpleNamespace(c2_guard=lambda:inherited) if 'manifold_heat_release' in path else inherited
        with self.sources(),patch.object(comp,'verify_current',return_value={}),patch.object(comp.importlib,'import_module',return_value=module):
            comp.current_evidence(path,['--axiom-dir',str(self.folder)])

    def test_current_public_positive_routes_use_real_checker_and_owned_git(self):
        self.assertEqual(AXIOM_INVENTORY_FIXTURE['jobs'],[112650426668,112681114319])
        for path in ('curvature/scripts/point4_c2_initial_heat_source_test.py','curvature/scripts/point4_manifold_heat_release_guard.py','curvature/scripts/point4_linear_heat_geometry_source_test.py'):
            with self.subTest(path=path):self.actual_route(path)
        with self.sources():
            inventory=comp.current_axiom_inventory('curvature/scripts/point4_c2_initial_heat_source_test.py',self.inherited)
        occurrences=sum((list(v[1]) for v in inventory.values()),[])
        self.assertEqual((len(occurrences),len(set(occurrences))),(157,151))
        self.assertEqual(len(inventory['contraction'][1]),13)
        self.assertEqual(len(occurrences)-len(set(occurrences)),6)

    def test_every_inherited_and_added_missing_record_is_rejected(self):
        for name,output in AXIOM_INVENTORY_FIXTURE['outputs'].items():
            source=(self.root/f'curvature/scripts/point4_{name}_probe.lean').read_text()
            for record in comp.re.finditer(r"'[^']+' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms?)",output):
                for checker in [self.inherited]+([self.linear] if name in self.linear.PROBES else []):
                    with self.subTest(probe=name,record=record.group(),group=len(checker.PROBES)),self.assertRaises(AssertionError):
                        checker.check_axiom_output(source,output[:record.start()]+output[record.end():])

    def test_every_inherited_and_added_duplicate_record_is_rejected(self):
        for name,output in AXIOM_INVENTORY_FIXTURE['outputs'].items():
            source=(self.root/f'curvature/scripts/point4_{name}_probe.lean').read_text()
            for record in comp.re.finditer(r"'[^']+' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms?)",output):
                for checker in [self.inherited]+([self.linear] if name in self.linear.PROBES else []):
                    with self.subTest(probe=name,record=record.group(),group=len(checker.PROBES)),self.assertRaises(AssertionError):
                        checker.check_axiom_output(source,output+'\n'+record.group())

    def test_every_inherited_and_added_forbidden_axiom_is_rejected(self):
        for name,output in AXIOM_INVENTORY_FIXTURE['outputs'].items():
            source=(self.root/f'curvature/scripts/point4_{name}_probe.lean').read_text()
            for record in comp.re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms?)",output):
                bad=output[:record.start()]+"'"+record.group(1)+"' depends on axioms: [PoincareCurvature.UnprovedBridge]"+output[record.end():]
                for checker in [self.inherited]+([self.linear] if name in self.linear.PROBES else []):
                    with self.subTest(probe=name,endpoint=record.group(1),group=len(checker.PROBES)),self.assertRaises(AssertionError):
                        checker.check_axiom_output(source,bad)

    def test_every_inherited_and_added_source_occurrence_is_required(self):
        with self.sources():
            for name in comp.INHERITED_AXIOM_PROBES:
                path=self.root/f'curvature/scripts/point4_{name}_probe.lean';source=path.read_bytes()
                for directive in comp.re.findall(rb'^#print axioms \S+',source,comp.re.M):
                    try:
                        path.write_bytes(source.replace(directive,b'',1))
                        with self.subTest(probe=name,directive=directive),self.assertRaises(AssertionError):
                            comp.current_axiom_inventory('curvature/scripts/point4_c2_initial_heat_source_test.py',self.inherited)
                        if name in self.linear.PROBES:
                            with self.subTest(probe=name,directive=directive,group=11),self.assertRaises(AssertionError):
                                comp.current_axiom_inventory('curvature/scripts/point4_linear_heat_geometry_source_test.py',self.linear)
                    finally:path.write_bytes(source)

    def test_same_count_substitution_duplicate_and_order_drift_are_rejected(self):
        path=self.root/'curvature/scripts/point4_contraction_probe.lean';source=path.read_bytes()
        directives=comp.re.findall(rb'^#print axioms \S+',source,comp.re.M)
        mutations=(source.replace(directives[-1],b'#print axioms RicciFlow.UnapprovedReplacement',1),
                   source+b'\n'+directives[-1]+b'\n',
                   source.replace(directives[0],b'#print axioms TEMPORARY_SWAP',1).replace(directives[1],directives[0],1).replace(b'#print axioms TEMPORARY_SWAP',directives[1],1))
        with self.sources():
            for bad in mutations:
                try:
                    path.write_bytes(bad)
                    with self.assertRaises(AssertionError):comp.current_axiom_inventory('curvature/scripts/point4_c2_initial_heat_source_test.py',self.inherited)
                finally:path.write_bytes(source)

    def test_current_route_rejects_missing_duplicate_forbidden_and_extra_file(self):
        path=self.folder/'contraction.log';output=path.read_text()
        name=comp.CONTRACTION_AXIOM_ADDITIONS[-1]
        record=comp.re.search(r"'"+comp.re.escape(name)+r"' depends on axioms:\s*\[[^]]*\]",output)
        self.assertIsNotNone(record)
        mutations=(output[:record.start()]+output[record.end():],output+'\n'+record.group(),
                   output[:record.start()]+"'"+name+"' depends on axioms: [RicciFlow.UnprovedBridge]"+output[record.end():])
        for bad in mutations:
            try:
                path.write_text(bad)
                for route in ('curvature/scripts/point4_manifold_heat_release_guard.py','curvature/scripts/point4_c2_initial_heat_source_test.py','curvature/scripts/point4_linear_heat_geometry_source_test.py'):
                    with self.subTest(route=route),self.assertRaises(AssertionError):self.actual_route(route)
            finally:path.write_bytes(output.encode())
        extra=self.folder/'unapproved.log';extra.write_bytes(b'')
        try:
            with self.assertRaises(AssertionError):self.actual_route('curvature/scripts/point4_c2_initial_heat_source_test.py')
        finally:extra.unlink()
        path.unlink()
        with self.assertRaises(AssertionError):self.actual_route('curvature/scripts/point4_c2_initial_heat_source_test.py')

    def test_predecessor_blob_and_probe_inventory_drift_are_rejected(self):
        with self.sources(),patch.object(comp,'git',return_value=b'unapproved predecessor bytes'):
            with self.assertRaises(AssertionError):comp.current_axiom_inventory('curvature/scripts/point4_c2_initial_heat_source_test.py',self.inherited)
        with self.sources():
            self.inherited.PROBES=self.inherited.PROBES[:-1]
            with self.assertRaises(AssertionError):comp.current_axiom_inventory('curvature/scripts/point4_c2_initial_heat_source_test.py',self.inherited)

    @contextlib.contextmanager
    def historical_controls(self,output=None,exit_code=0,version_exit=0,version_output=b'Lean (version 4.33.0, fixture)\n'):
        # Source/control fixture only: actual checker bodies and owned Git probe
        # blobs, mocked compiler execution. Hosted argument-bearing positives
        # below are separately required to establish real replay evidence.
        originals={p:self.original_git('show',comp.MASTER+':'+p) for p in self.master}
        source=originals['curvature/scripts/point4_contraction_probe.lean'].decode()
        names=self.inherited.probe_names(source)
        records={m.group(1):m.group() for m in comp.re.finditer(
            r"'([^']+)' (?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms?)",
            AXIOM_INVENTORY_FIXTURE['outputs']['contraction'])}
        self.historical_output=('\n'.join(records[n] for n in names)+'\n').encode()
        chosen=self.historical_output if output is None else output
        module=types.SimpleNamespace(c2_guard=lambda:self.inherited)
        def read(*args):
            self.assertEqual(args[0],'show');commit,path=args[1].split(':',1)
            self.assertIn(commit,(comp.MASTER,comp.SUPPORT))
            return originals[path]
        def run(command,**kwargs):
            self.assertEqual(kwargs['cwd'],self.root/'curvature')
            self.assertEqual(command[:3],['lake','env','lean'])
            if command[-1]=='--version':
                return subprocess.CompletedProcess(command,version_exit,version_output,b'')
            self.assertEqual(pathlib.Path(command[-1]).read_bytes(),source.encode())
            return subprocess.CompletedProcess(command,exit_code,chosen)
        with patch.object(comp,'ROOT',self.root),patch.object(comp,'parent_tree',return_value=self.master),\
             patch.object(comp,'git',side_effect=lambda *a: b'0'*40+b'\n' if a==('rev-parse','HEAD') else read(*a)),\
             patch.object(comp,'verify_current',return_value={}),patch.object(comp.importlib,'import_module',return_value=module),\
             patch.object(comp.subprocess,'run',side_effect=run) as runner:
            yield runner

    def test_historical_argument_route_preserves_complete_current_logs_and_raw_receipt(self):
        before=comp.raw_axiom_files(self.folder)
        for inline in (False,True):
            args=['--axiom-dir='+str(self.folder)] if inline else ['--axiom-dir',str(self.folder)]
            args+=['--audit-rc','1']
            with self.historical_controls() as runner:
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',args) as routed:
                    slot=comp.axiom_argument(routed);view=slot[2]
                    self.assertNotEqual(view,self.folder)
                    self.assertEqual((view/'contraction.log').read_bytes(),self.historical_output)
                    self.assertEqual(len(self.inherited.check_axiom_output(
                        AXIOM_INVENTORY_FIXTURE['sources']['contraction'],self.historical_output.decode())),6)
                    self.assertEqual(routed[-2:],['--audit-rc','1'])
                self.assertEqual(runner.call_count,2)
            self.assertEqual(comp.raw_axiom_files(self.folder),before)
        lines=comp.routing_receipt_path(self.folder).read_text().splitlines()
        receipt=json.loads(next(x.split(' ',1)[1] for x in lines if x.startswith('HISTORICAL_AXIOM_ROUTING_RECEIPT ')))
        self.assertEqual(comp.base64.b64decode(receipt['raw_contraction_base64']),self.historical_output)
        self.assertEqual(receipt['probe_exit'],0)
        self.assertEqual(receipt['current_sha256']['contraction.log'],comp.sha256(before['contraction.log']))

    def test_both_argument_bearing_wrappers_route_separate_historical_inputs(self):
        args=['--axiom-dir',str(self.folder)]
        events=[]
        def gate(path,routed):
            view=comp.axiom_argument(routed)[2]
            self.assertNotEqual(view,self.folder)
            self.assertEqual((view/'contraction.log').read_bytes(),self.historical_output)
            events.append(path)
        namespace={'BASE':comp.MASTER,'_composition_original_historical_gate':gate,
                   'check_current':object(),'historical_gate':object()}
        with self.historical_controls(),comp.weighted_execution(namespace):
            namespace['historical_gate']('curvature/scripts/point4_manifold_heat_release_guard.py',args)
        smooth={'main':lambda actual:events.append(('current',actual))}
        comp.install_smooth(smooth)
        with self.historical_controls(),patch.object(comp,'current_smooth_evidence'),\
             patch.object(comp,'historical',side_effect=lambda commit,path,actual:gate(path,actual)):
            smooth['main'](args)
        self.assertEqual(events[0],'curvature/scripts/point4_manifold_heat_release_guard.py')
        self.assertEqual(events[1],('current',args))
        self.assertEqual(events[2],comp.SMOOTH)

    def test_historical_bad_raw_records_and_compiler_failure_are_rejected(self):
        with self.historical_controls():good=self.historical_output
        records=list(comp.re.finditer(rb"'[^']+' depends on axioms:\s*\[[^]]*\]",good))
        self.assertTrue(records)
        bads=(good[:records[0].start()]+good[records[0].end():],good+b'\n'+records[0].group(),
              good+b"\n'RicciFlow.Extra' depends on axioms: []\n",good.replace(b'propext',b'sorryAx',1),
              AXIOM_INVENTORY_FIXTURE['outputs']['contraction'].encode())
        for output in bads:
            with self.historical_controls(output),self.assertRaises(AssertionError):
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                    ['--axiom-dir',str(self.folder)]):self.fail('Bad historical output reached validator')
        with self.historical_controls(exit_code=1),self.assertRaises(AssertionError):
            with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                ['--axiom-dir',str(self.folder)]):self.fail('Failed compiler reached validator')

    def test_historical_prevalidation_rejects_each_added_forbidden_record(self):
        file=self.folder/'contraction.log';original=file.read_bytes()
        for name in comp.CONTRACTION_AXIOM_ADDITIONS:
            record=comp.re.search(rb"'"+comp.re.escape(name.encode())+rb"' depends on axioms:\s*\[[^]]*\]",original)
            self.assertIsNotNone(record)
            bad=original[:record.start()]+b"'"+name.encode()+b"' depends on axioms: [sorryAx]"+original[record.end():]
            file.write_bytes(bad)
            try:
                with self.historical_controls() as runner,self.assertRaises(AssertionError):
                    with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                        ['--axiom-dir',str(self.folder)]):self.fail('Untrusted current addition reached history')
                runner.assert_not_called()
            finally:file.write_bytes(original)

    def test_historical_probe_provenance_drift_is_rejected_before_lean(self):
        with self.historical_controls() as runner:
            tree=dict(self.master);tree['curvature/scripts/point4_contraction_probe.lean']=('100644','0'*40)
            with patch.object(comp,'parent_tree',return_value=tree),self.assertRaises(AssertionError):
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                    ['--axiom-dir',str(self.folder)]):self.fail('Bad pinned blob reached history')
            runner.assert_not_called()

    def test_historical_compiler_identity_is_exact_and_successful(self):
        for status,output in ((1,b'Lean (version 4.33.0, fixture)\n'),
                              (0,b'Lean (version 4.33.01, fixture)\n'),
                              (0,b'unapproved prefix version 4.33.0\n')):
            with self.historical_controls(version_exit=status,version_output=output) as runner,self.assertRaisesRegex(AssertionError,'compiler identity'):
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                    ['--axiom-dir',str(self.folder)]):self.fail('Wrong compiler reached validator')
            self.assertEqual(runner.call_count,1)

    def test_historical_route_rejects_byte_drift_swapped_dirs_and_mutation(self):
        target=self.root/'curvature/scripts/point4_coordinate_jet_probe.lean';original=target.read_bytes()
        target.write_bytes(original+b'\n-- Unapproved comment drift\n')
        try:
            with self.historical_controls(),self.assertRaisesRegex(AssertionError,'byte drift'):
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                    ['--axiom-dir',str(self.folder)]):self.fail('Drift reached validator')
        finally:target.write_bytes(original)
        for which in ('current','historical'):
            with self.historical_controls(),self.assertRaisesRegex(AssertionError,'input mutation'):
                with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                    ['--axiom-dir',str(self.folder)]) as routed:
                    view=comp.axiom_argument(routed)[2]
                    folder=self.folder if which=='current' else view
                    (folder/'coordinate_jet.log').write_bytes((folder/'coordinate_jet.log').read_bytes()+b'\nchanged\n')
            (self.folder/'coordinate_jet.log').write_bytes(AXIOM_INVENTORY_FIXTURE['outputs']['coordinate_jet'].encode())
        with self.historical_controls():
            with comp.historical_axiom_arguments(comp.MASTER,'curvature/scripts/point4_manifold_heat_release_guard.py',
                ['--axiom-dir',str(self.folder)]) as routed:
                with self.assertRaises(AssertionError):
                    comp.current_evidence('curvature/scripts/point4_manifold_heat_release_guard.py',routed)





class MapConstructionSnapshotTests(unittest.TestCase):
    """Map equivalence and authentication scope against the published route fix."""
    PUBLISHED='19bbceea080c8723b1f802b9b980b01b2ec4ba2a'
    PUBLISHED_TREE='39076b211555c93c16c4952b3372bb6673b67380'

    @classmethod
    def setUpClass(cls):
        assert comp.git('rev-parse',cls.PUBLISHED+'^{tree}').decode().strip()==cls.PUBLISHED_TREE, 'Unbatched reference tree drift'
        subprocess.run(['git','--no-replace-objects','-C',str(comp.ROOT),'merge-base','--is-ancestor',cls.PUBLISHED,'HEAD'],check=True,env=comp.ENV)
        original=comp.git('show',cls.PUBLISHED+':'+comp.HELPER)
        assert comp.blob_id(original)==comp.git('rev-parse',cls.PUBLISHED+':'+comp.HELPER).decode().strip(), 'Unbatched reference blob drift'
        cls.original_ast=ast.parse(original)
        cls.functions={'prior_map_record','map_record'}
        if hasattr(comp,'contraction_map_record'):cls.functions.add('contraction_map_record')
        namespace=dict(comp.__dict__)
        selected=[copy.deepcopy(node) for node in cls.original_ast.body
                  if isinstance(node,ast.FunctionDef) and node.name in cls.functions]
        exec(compile(ast.Module(body=selected,type_ignores=[]),'published-map-reference','exec'),namespace)
        cls.reference_namespace=namespace
        cls.inputs=comp.expected_identity()
        cls.pins=[comp.MASTER,comp.SUPPORT,comp.HEAT_PARENT,comp.HEAT_SOURCE,
                  comp.CONTRACTION_PARENT,comp.CONTRACTION_SOURCE,comp.CONTRACTION_BASE]
        if hasattr(comp,'FIXED_PARENT'):
            cls.pins.extend([comp.FIXED_PARENT,comp.FIXED_SOURCE,comp.FIXED_BASE])
        cls.snapshots={commit:comp.parent_tree(commit) for commit in cls.pins}

    def evaluate(self,reference=False,mutate=None):
        calls=[]
        def read(commit):
            frame=sys._getframe(1)
            if frame.f_code.co_name in ('<dictcomp>','<setcomp>','<listcomp>'):
                frame=frame.f_back
            calls.append((frame.f_code.co_name,commit))
            tree=dict(self.snapshots[commit])
            if mutate:mutate(commit,tree)
            return tree
        previous=self.reference_namespace['parent_tree']
        self.reference_namespace['parent_tree']=read
        try:
            with patch.object(comp,'parent_tree',read):
                function=self.reference_namespace['map_record'] if reference else comp.map_record
                result=function(*self.inputs)
            return result,calls
        finally:self.reference_namespace['parent_tree']=previous

    def test_full_record_matches_published_unbatched_reference(self):
        original,old_calls=self.evaluate(reference=True)
        current,new_calls=self.evaluate()
        self.assertEqual(current,original)
        required={'prior_map_record':{comp.MASTER,comp.SUPPORT,comp.HEAT_PARENT,comp.HEAT_SOURCE},
                  'contraction_map_record' if hasattr(comp,'contraction_map_record') else 'map_record':
                      {comp.CONTRACTION_PARENT,comp.CONTRACTION_SOURCE,comp.CONTRACTION_BASE}}
        if hasattr(comp,'FIXED_PARENT'):
            required['map_record']={comp.FIXED_PARENT,comp.FIXED_SOURCE,comp.FIXED_BASE}
        for name,pins in required.items():
            direct=[commit for caller,commit in new_calls if caller==name]
            self.assertEqual(set(direct),pins)
            self.assertEqual(len(direct),len(pins))
        self.assertGreater(len(old_calls),len(new_calls))

    def test_second_construction_reauthenticates_and_observes_drift(self):
        first,first_calls=self.evaluate()
        def changed(commit,tree):
            if commit==comp.HEAT_SOURCE:
                tree[comp.HEAT_DOMAIN]=('100755','0'*40)
        second,second_calls=self.evaluate(mutate=changed)
        self.assertIn(('prior_map_record',comp.HEAT_SOURCE),first_calls)
        self.assertIn(('prior_map_record',comp.HEAT_SOURCE),second_calls)
        self.assertNotEqual(first,second)
        self.assertEqual(second['heat_invariant_integration']['fixed_source_paths'][comp.HEAT_DOMAIN],
                         ['100755','0'*40])
        def missing(commit,tree):
            if commit==comp.HEAT_SOURCE:tree.pop(comp.HEAT_DOMAIN)
        with self.assertRaises(KeyError):self.evaluate(mutate=missing)
        # Authentication failure must also propagate on a later construction.
        with patch.object(comp,'parent_tree',side_effect=AssertionError('fresh pinned tree drift')):
            with self.assertRaisesRegex(AssertionError,'fresh pinned tree drift'):
                comp.map_record(*self.inputs)

    def test_authentication_rejects_changed_pinned_tree_before_enumeration(self):
        for commit in self.pins:
            with patch.object(comp,'git',return_value=b'0'*40+b'\n') as reader:
                # Use the unchanged actual authenticator, not a tree stub.
                original=[node for node in self.original_ast.body
                          if isinstance(node,ast.FunctionDef) and node.name=='parent_tree'][0]
                namespace=dict(comp.__dict__)
                exec(compile(ast.Module(body=[copy.deepcopy(original)],type_ignores=[]),
                             'published-parent-authenticator','exec'),namespace)
                with self.assertRaises(AssertionError):namespace['parent_tree'](commit)
                reader.assert_called_once_with('rev-parse',commit+'^{tree}')

    def test_all_other_helper_guards_and_module_state_are_unchanged(self):
        current=ast.parse(comp.tensor_helper_inverse((comp.ROOT/comp.HELPER).read_bytes()))
        def guards(module):
            return ast.dump(ast.Module(body=[node for node in module.body
                if not (isinstance(node,ast.FunctionDef) and node.name in self.functions)],
                type_ignores=[]),include_attributes=False)
        self.assertEqual(guards(current),guards(self.original_ast))

# BEGIN authenticated finite tensor tests
class TensorCompositionTests(unittest.TestCase):
    def inputs(self):
        return comp.tensor_identity(*comp.expected_identity())

    def test_entire_predecessor_helper_and_test_are_recovered(self):
        for path,inverse in ((comp.HELPER,comp.tensor_helper_inverse),(comp.TEST,comp.tensor_test_inverse)):
            raw=(comp.ROOT/path).read_bytes()
            self.assertEqual(inverse(raw),comp.git('show',comp.TENSOR_PARENT+':'+path))
            for bad in (raw+b'\nchanged',raw.replace(b'# BEGIN authenticated finite tensor',b'# EXTRA authenticated finite tensor',1)):
                with self.assertRaises(AssertionError):inverse(bad)

    def test_all_237_records_and_selected_sources_are_exact(self):
        expected,originals,changes=self.inputs()
        pins=comp.tensor_pins();delta=comp.tensor_delta(pins)
        self.assertEqual(len(expected),1920)
        self.assertEqual(set(delta),comp.TENSOR_PATHS)
        for p in comp.TENSOR_RETAINED:self.assertEqual(expected[p],pins[comp.TENSOR_PARENT][p])
        for p in comp.TENSOR_PATHS-comp.TENSOR_RETAINED:
            if p==comp.TENSOR_PACKAGE:
                original=comp.git('show',comp.TENSOR_SOURCE+':'+p)
                self.assertEqual(comp.tensor_package_inverse(changes[p]),original)
                self.assertEqual(expected[p],('100644',comp.blob_id(changes[p])))
            elif p==comp.TENSOR_BOUNDARY_WORKFLOW:
                original=comp.git('show',comp.TENSOR_SOURCE+':'+p)
                self.assertEqual(comp.tensor_boundary_inverse(changes[p]),original)
                self.assertEqual(expected[p],('100644',comp.blob_id(changes[p])))
            else:
                self.assertEqual(expected[p],pins[comp.TENSOR_SOURCE][p])
                self.assertEqual(changes[p],comp.git('show',comp.TENSOR_SOURCE+':'+p))
        self.assertEqual(comp.tensor_map_record(expected,originals,changes),comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()))

    def test_missing_extra_modified_mode_and_source_records_are_rejected(self):
        original=comp.tensor_pins()
        example=next(p for p in comp.TENSOR_PATHS if p!=comp.TENSOR_MECHANICAL)
        for action in ('missing','extra','mode','blob'):
            snapshots={c:dict(rows) for c,rows in original.items()}
            rows=snapshots[comp.TENSOR_SOURCE]
            if action=='missing':rows.pop(example)
            elif action=='extra':rows['unreviewed.lean']=('100644','0'*40)
            elif action=='mode':rows[example]=('100755',rows[example][1])
            else:rows[example]=('100644','0'*40)
            with self.assertRaises(AssertionError):
                # Physical immutable bytes and pinned source maps both matter.
                with patch.object(comp,'tensor_pins',return_value=snapshots):comp.tensor_identity(*self.inputs())

    def test_immutable_pin_drift_precedes_affected_tree_enumeration(self):
        actual_git=comp.git;actual_parent=comp.parent_tree
        pins=[comp.TENSOR_PARENT,comp.TENSOR_SOURCE,comp.TENSOR_BASE,comp.TENSOR_DEPENDENCY]
        for i,c in enumerate(pins):
            def read(*args):
                if args==('rev-parse',c+'^{tree}'):return b'0'*40+b'\n'
                return actual_git(*args)
            with patch.object(comp,'git',side_effect=read),patch.object(comp,'parent_tree',wraps=actual_parent) as parent:
                with self.assertRaises(AssertionError):comp.tensor_pins()
                self.assertEqual([call.args[0] for call in parent.call_args_list],pins[:i])

    def test_duplicate_identity_records_rejected(self):
        for raw in (b'{"tensor":1,"tensor":1}',b'{"tensor":{"path":1,"path":1}}'):
            with self.assertRaisesRegex(AssertionError,'Duplicate'):comp.tensor_strict_json(raw)

    def test_predecessor_map_and_mechanical_mutations_rejected(self):
        expected,originals,changes=self.inputs()
        snapshots=comp.tensor_pins()
        for p in {comp.MAP}|comp.TENSOR_RETAINED:
            altered={c:dict(rows) for c,rows in snapshots.items()}
            altered[comp.TENSOR_PARENT][p]=('100644','0'*40)
            with self.assertRaises(AssertionError):comp.tensor_predecessor(expected,originals,changes,altered)
    def test_exact_package_guard_repair_preserves_all_original_checks(self):
        original=comp.git('show',comp.TENSOR_SOURCE+':'+comp.TENSOR_PACKAGE)
        actual=(comp.ROOT/comp.TENSOR_PACKAGE).read_bytes()
        self.assertEqual(comp.tensor_package_inverse(actual),original)
        for bad in (original,actual+b'\nchanged',actual.replace(b'exact qualified-master',b'changed guard',1)):
            with self.assertRaises(AssertionError):comp.tensor_package_inverse(bad)
        with self.assertRaises(AssertionError):comp.tensor_package_transform(actual)

    def test_boundary_workflow_inverse_hooks_deadline_and_compiler_separation(self):
        import yaml
        actual=(comp.ROOT/comp.TENSOR_BOUNDARY_WORKFLOW).read_bytes()
        original=comp.git('show',comp.TENSOR_SOURCE+':'+comp.TENSOR_BOUNDARY_WORKFLOW)
        self.assertEqual(comp.tensor_boundary_inverse(actual),original)
        workflow=yaml.safe_load(actual);baseline=yaml.safe_load(original)
        job=workflow['jobs']['candidate-boundary']
        self.assertEqual(job['timeout-minutes'],90)
        self.assertEqual(workflow['jobs']['current-mechanical']['needs'],'candidate-boundary')
        reusable=dict(workflow['jobs']['current-mechanical']);reusable.pop('needs')
        self.assertEqual(reusable,baseline['jobs']['current-mechanical'])
        self.assertEqual({k:v for k,v in workflow.items() if k!='jobs'},{k:v for k,v in baseline.items() if k!='jobs'})
        commands=[step['run'] for step in job['steps'] if 'run' in step]
        compiler=next(run for run in commands if 'lake exe cache get' in run)
        for required in ('leanprover/lean4:v4.35.0-rc2','065356127b1dc0016f66b7283ce0ce2c4055aa55',
                         'lake build TensorHeatChallenge','python scripts/check-challenge-boundary.py',
                         'lake env lean scripts/check-closed-statement.lean'):
            self.assertIn(required,compiler)
        bindings=[run for run in commands if "git('ls-tree'" in run]
        self.assertEqual(len(bindings),2)
        def source_check(run):
            script=run[run.index('import hashlib,'):run.rindex('\nPY')]
            return ast.dump(ast.parse(script),include_attributes=False)
        self.assertEqual(source_check(bindings[0]),source_check(bindings[1]))
        for token in (b'timeout-minutes: 90',b'needs: candidate-boundary',b'check-challenge-boundary.py',
                      b'check-closed-statement.lean',b'065356127b1dc0016f66b7283ce0ce2c4055aa55',
                      b'persist-credentials: false',b"assert index == entries"):
            with self.assertRaises(AssertionError):comp.tensor_boundary_inverse(actual.replace(token,b'changed',1))
        with self.assertRaises(AssertionError):comp.tensor_boundary_transform(actual)

    def test_genuine_weighted_reconstruction_positive_and_adversarial_records(self):
        import point4_weighted_hessian_release_guard as weighted
        import stat
        self.assertEqual(weighted.ROOT,comp.ROOT)
        expected,originals,changes=comp.curvature_identity(*self.inputs())
        captured=[]
        original=comp.tensor_reconstructed_sources
        physical_stat=pathlib.Path.lstat
        def committed_mode_fixture(physical,*args,**kwargs):
            actual=physical_stat(physical,*args,**kwargs)
            try:relative=physical.relative_to(comp.ROOT).as_posix()
            except ValueError:return actual
            if relative not in expected:return actual
            self.assertTrue(stat.S_ISREG(actual.st_mode))
            self.assertEqual(comp.blob_id(physical.read_bytes()),expected[relative][1])
            fields=list(actual)
            fields[0]=(fields[0]&~0o111)|(0o111 if expected[relative][0]=='100755' else 0)
            return os.stat_result(fields)
        def observe(namespace,inherited,actual):
            captured.append(dict(inherited))
            return original(namespace,inherited,actual)
        # Exercise genuine inherited expected_sources and the genuine original
        # weighted check_current, not a fake successful body. Immutable identity
        # fixtures isolate platform executable-mode checks; hosted PRE/POST runs
        # authenticate actual Linux modes, HEAD, index and all physical bytes.
        schemas=[None]+([SCHEMA] if SCHEMA else [])
        for schema in schemas:
            with patch.object(comp,'verify_current',return_value=expected) as verify, \
                 patch.object(comp,'tensor_reconstructed_sources',side_effect=observe), \
                 patch.object(pathlib.Path,'lstat',committed_mode_fixture if sys.platform=='win32' else physical_stat), \
                 patch.dict(weighted.__dict__,{'raw_git':comp.git} if sys.platform=='win32' else {}):
                report=comp.weighted_leaf(weighted.__dict__,schema)
            self.assertEqual(report['public_paths'],2139)
            self.assertEqual(verify.call_count,2)
        inherited=captured[0]
        self.assertEqual(len(inherited),1686)
        path=next(p for p in inherited if p in comp.TENSOR_PATHS-comp.TENSOR_RETAINED)
        for action in ('missing','extra','predecessor','provenance','final-mode','final-blob','current-bytes'):
            rows=dict(inherited);final=dict(expected)
            if action=='missing':rows.pop(path)
            elif action=='extra':rows['unreviewed.lean']=('unreviewed',b'')
            elif action=='predecessor':rows[path]=(rows[path][0],rows[path][1]+b'changed')
            elif action=='provenance':rows[path]=('unreviewed origin',rows[path][1])
            elif action=='final-mode':final[path]=('100755' if final[path][0]=='100644' else '100644',final[path][1])
            elif action=='final-blob':final[path]=(final[path][0],'0'*40)
            if action=='current-bytes':
                read=pathlib.Path.read_bytes
                def changed(physical):
                    data=read(physical)
                    return data+b'changed' if physical==comp.ROOT/path else data
                with patch.object(pathlib.Path,'read_bytes',changed):
                    with self.assertRaises(AssertionError):original(weighted.__dict__,rows,final)
            else:
                with self.assertRaises(AssertionError):original(weighted.__dict__,rows,final)
        # Verify that a mutation detected after the original body cannot return
        # a success report. This sequence shares the actual positive route above.
        with patch.object(comp,'verify_current',side_effect=[expected,AssertionError('POST input mutation')]), \
             patch.dict(weighted.__dict__,{'_composition_original_check_current':lambda schema: {}}), \
             patch.object(pathlib.Path,'lstat',committed_mode_fixture if sys.platform=='win32' else physical_stat), \
             patch.dict(weighted.__dict__,{'raw_git':comp.git} if sys.platform=='win32' else {}):
            with self.assertRaisesRegex(AssertionError,'POST input mutation'):
                comp.weighted_leaf(weighted.__dict__)

# END authenticated finite tensor tests
# BEGIN authenticated finite curvature tests
class CurvatureCompositionTests(unittest.TestCase):
    def test_actual_current_verifier_owned_namespace_and_exception_unwind(self):
        import point4_weighted_hessian_release_guard as weighted
        import stat
        committed=comp.parse_tree(comp.git('ls-tree','-rz','HEAD'))
        self.assertEqual(len(committed),2139)
        physical_stat=pathlib.Path.lstat
        def committed_modes(physical,*args,**kwargs):
            actual=physical_stat(physical,*args,**kwargs)
            try:relative=physical.relative_to(comp.ROOT).as_posix()
            except ValueError:return actual
            if relative not in committed:return actual
            self.assertTrue(stat.S_ISREG(actual.st_mode))
            self.assertEqual(comp.blob_id(physical.read_bytes()),committed[relative][1])
            fields=list(actual)
            fields[0]=(fields[0]&~0o111)|(0o111 if committed[relative][0]=='100755' else 0)
            return os.stat_result(fields)
        # Actual immutable HEAD/index/ancestry/physical bytes and original full
        # verifier execute; Windows only models committed executable modes and
        # routes the unchanged Git calls to the genuine installed Git binary.
        with patch.object(pathlib.Path,'lstat',committed_modes if sys.platform=='win32' else physical_stat), \
             patch.dict(weighted.__dict__,{'raw_git':comp.git} if sys.platform=='win32' else {}):
            self.assertEqual(comp.verify_current(),committed)
        self.assertFalse(comp._curvature_verification_active)
        self.assertIsNone(comp._owner)
        self.assertEqual(comp._depth,0)
        primary=RuntimeError('genuine verifier failure')
        with patch.object(comp,'_curvature_original_verify_current',side_effect=primary):
            with self.assertRaises(RuntimeError) as observed:comp.verify_current()
        self.assertIs(observed.exception,primary)
        self.assertFalse(comp._curvature_verification_active)
        with patch.object(comp,'_curvature_verification_active',True),patch.object(comp,'git') as read:
            with self.assertRaisesRegex(AssertionError,'Recursive'):comp.verify_current()
            read.assert_not_called()
        with patch.object(pathlib.Path,'lstat',committed_modes if sys.platform=='win32' else physical_stat), \
             patch.dict(weighted.__dict__,{'raw_git':comp.git} if sys.platform=='win32' else {}):
            self.assertEqual(comp.verify_current(),committed)
        self.assertFalse(comp._curvature_verification_active)
        self.assertIsNone(comp._owner)
        self.assertEqual(comp._depth,0)

    def test_full_legacy_recovery_and_exact_2139_current_input_namespace(self):
        legacy,originals,changes=comp.tensor_identity(*comp.expected_identity())
        self.assertEqual(len(legacy),1920)
        snapshots=comp.curvature_pins()
        self.assertEqual(comp.curvature_predecessor(legacy,originals,changes,snapshots),snapshots[comp.CURVATURE_PARENT])
        complete,_,_=comp.curvature_identity(legacy,originals,changes)
        self.assertEqual(len(complete),2139)
        self.assertEqual(set(complete)-set(legacy),set(comp.CURVATURE_SELECTED)-{'curvature/lakefile.toml'})
        self.assertEqual(comp.tensor_map_record(complete,originals,changes),comp.tensor_strict_json((comp.ROOT/comp.MAP).read_bytes()))
        for path,marker in ((comp.HELPER,'extension'),(comp.TEST,'tests')):
            raw=(comp.ROOT/path).read_bytes()
            self.assertEqual(comp.curvature_section_inverse(raw,path,marker),comp.git('show',comp.CURVATURE_PARENT+':'+path))
            with self.assertRaises(AssertionError):comp.curvature_section_inverse(raw+b'changed',path,marker)

    def test_finite_origin_source_identity_and_current_input_mutation_reject(self):
        selected=json.loads(json.dumps(comp.CURVATURE_SELECTED))
        path=next(iter(selected))
        for mutation in ('missing','extra','origin','blob'):
            modified=json.loads(json.dumps(selected))
            if mutation=='missing':modified.pop(path)
            elif mutation=='extra':modified['invented.lean']=modified[path]
            elif mutation=='origin':modified[path]['origins'][0]['head']=comp.CURVATURE_PARENT
            else:modified[path]['mode_blob'][1]='0'*40
            with patch.object(comp,'CURVATURE_SELECTED',modified):
                with self.assertRaises(AssertionError):comp.curvature_pins()
        raw=(comp.ROOT/path).read_bytes()
        try:
            (comp.ROOT/path).write_bytes(raw+b'current source mutation')
            with self.assertRaises(AssertionError):comp.curvature_identity(*comp.tensor_identity(*comp.expected_identity()))
        finally:(comp.ROOT/path).write_bytes(raw)
        comp.curvature_identity(*comp.tensor_identity(*comp.expected_identity()))
class CurvatureProductionNamespaceTests(unittest.TestCase):
    """Actual-current startup/source controls; no original-main/native claims."""
    @classmethod
    def setUpClass(cls):
        cls.model=comp.parse_tree(comp.git('ls-tree','-rz','HEAD'))
        assert len(cls.model)==2139
        cls.modules={}
        cls.physical_stat=pathlib.Path.lstat
        cls.units={132:'point4_two_sided_heat_source_guard',
            134:'point4_c2_c0_metric_velocity_source_guard',111:'point4_hamilton_native_source_guard',
            136:'point4_c2_resonance_guard',138:'chart_port_candidate_check'}

    @staticmethod
    def committed_modes(physical,*args,**kwargs):
        import stat
        actual=CurvatureProductionNamespaceTests.physical_stat(physical,*args,**kwargs)
        try:relative=physical.relative_to(comp.ROOT).as_posix()
        except ValueError:return actual
        model=CurvatureProductionNamespaceTests.model
        if relative not in model:return actual
        assert stat.S_ISREG(actual.st_mode) and comp.blob_id(physical.read_bytes())==model[relative][1]
        fields=list(actual);fields[0]=(fields[0]&~0o111)|(0o111 if model[relative][0]=='100755' else 0)
        return os.stat_result(fields)

    def modes(self):
        import point4_weighted_hessian_release_guard as weighted
        import contextlib
        stack=contextlib.ExitStack()
        if sys.platform=='win32':
            stack.enter_context(patch.object(pathlib.Path,'lstat',self.committed_modes))
            stack.enter_context(patch.dict(weighted.__dict__,{'raw_git':comp.git}))
        return stack

    def registered(self):
        import importlib
        for number,name in self.units.items():
            if number not in self.modules:
                self.modules[number]=importlib.import_module(name)
            module=self.modules[number]
            self.assertEqual(pathlib.Path(module.__file__).resolve(),comp.ROOT/('curvature/scripts/'+name+'.py'))
            self.assertIs(module._curvature_comp,comp)
            self.check_namespace(number,module.__dict__)
        return self.modules

    def check_namespace(self,number,namespace):
        if number in (132,134,111):comp.curvature_leaf_namespace_binding(namespace,number)
        elif number==136:comp.curvature_scalar_namespace_binding(namespace)
        else:comp.curvature_chart_namespace_binding(namespace)

    def test_genuine_current_five_namespace_hooks_and_original_entry_bodies(self):
        with self.modes():
            self.assertEqual(comp.verify_current(),self.model)
            modules=self.registered()
            for number,module in modules.items():
                path='curvature/scripts/'+self.units[number]+'.py'
                head=next(row['head'] for row in comp.CURVATURE_SELECTED[path]['origins'])
                raw=comp.git('show',head+':'+path)
                reference={'__file__':str(comp.ROOT/path),'__name__':'immutable_entry_body_reference_only'}
                exec(compile(raw,str(comp.ROOT/path),'exec',dont_inherit=True),reference)
                name='admit' if number==138 else 'main'
                self.assertEqual(getattr(module,name).__wrapped__.__code__,reference[name].__code__)
            self.assertEqual(comp.verify_current(),self.model)

    def test_each_current_namespace_policy_body_and_bootstrap_mutation_rejected(self):
        with self.modes():
            modules=self.registered()
            for number,module in modules.items():
                namespace=module.__dict__
                for key,replacement in (('BASE','0'*40),('_curvature_helper',pathlib.Path('foreign-helper'))):
                    old=namespace[key]
                    try:
                        namespace[key]=replacement
                        with self.assertRaises(AssertionError):self.check_namespace(number,namespace)
                    finally:namespace[key]=old
                name='admit' if number==138 else 'main'
                original=namespace[name].__wrapped__;old=original.__code__
                try:
                    original.__code__=(lambda *args,**kwargs:True).__code__
                    with self.assertRaises(AssertionError):self.check_namespace(number,namespace)
                finally:original.__code__=old
                self.check_namespace(number,namespace)
            self.assertEqual(comp.verify_current(),self.model)

    def test_failed_current_five_startups_restore_hooks_and_registry(self):
        with self.modes():
            self.registered()
            for number,name in self.units.items():
                path='curvature/scripts/'+name+'.py'
                namespace={'__file__':str(comp.ROOT/path),'__name__':'actual_current_startup_failure_control'}
                library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (132,134,111) else 'curvature_auxiliary_binding')
                before=set(library._BINDINGS);primary=RuntimeError('current startup verification failure')
                with patch.object(comp,'verify_current',side_effect=primary):
                    with self.assertRaises(RuntimeError) as caught:
                        exec(compile((comp.ROOT/path).read_bytes(),str(comp.ROOT/path),'exec',dont_inherit=True),namespace)
                self.assertIs(caught.exception,primary)
                self.assertEqual(set(library._BINDINGS),before)
                entry=namespace['admit' if number==138 else 'main']
                self.assertFalse(hasattr(entry,'__wrapped__'))
            self.assertEqual(comp.verify_current(),self.model)

    def test_embedded_runtime_code_policy_and_foreign_keys_rejected(self):
        with self.modes():
            self.registered()
            execution=comp.curvature_embedded_module('curvature_leaf_execution')
            original=execution.run_leaf.__code__
            try:
                execution.run_leaf.__code__=(lambda *args,**kwargs:True).__code__
                with self.assertRaisesRegex(AssertionError,'runtime code/policy drift'):
                    comp.curvature_embedded_module('curvature_leaf_execution')
            finally:execution.run_leaf.__code__=original
            records=comp.curvature_embedded_module('curvature_incoming_source_records')
            original=records.RULES[134]['paths']
            try:
                records.RULES[134]['paths']=original+1
                with self.assertRaisesRegex(AssertionError,'runtime code/policy drift'):
                    comp.curvature_embedded_module('curvature_leaf_execution')
            finally:records.RULES[134]['paths']=original
            execution.foreign_runtime_key=True
            try:
                with self.assertRaisesRegex(AssertionError,'runtime namespace keys drift'):
                    comp.curvature_embedded_module('curvature_leaf_execution')
            finally:del execution.foreign_runtime_key
            comp.curvature_embedded_module('curvature_leaf_execution')
            self.assertEqual(comp.verify_current(),self.model)

    def test_all_five_registry_entries_and_coordinated_hook_rewrites_rejected(self):
        import functools,types
        with self.modes():
            modules=self.registered()
            for number,module in modules.items():
                library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (111,132,134) else 'curvature_auxiliary_binding')
                namespace=module.__dict__;identifier=id(namespace);record=library._BINDINGS[identifier]
                self.assertIs(type(record),types.MappingProxyType)
                self.assertIs(type(record['bindings']),types.MappingProxyType)
                self.assertIs(type(record['originals']),types.MappingProxyType)
                with self.assertRaises(TypeError):record['number']=0
                with self.assertRaises(TypeError):record['bindings']['BASE']=('data','forged')
                with self.assertRaises(TypeError):record['originals'][next(iter(record['originals']))]=lambda:True
                name='admit' if number==138 else 'main';hook=namespace[name];executed=[]
                @functools.wraps(hook.__wrapped__)
                def foreign(*args,**kwargs):executed.append('foreign target executed');return True
                for kind in ('add','delete','replace','number','coordinated'):
                    try:
                        replacement=dict(record)
                        if kind=='add':library._BINDINGS[identifier+1]=record
                        elif kind=='delete':library._BINDINGS.pop(identifier)
                        elif kind=='number':
                            replacement['number']=0;library._BINDINGS[identifier]=types.MappingProxyType(replacement)
                        elif kind=='coordinated':
                            namespace[name]=foreign
                            replacement['bindings']=types.MappingProxyType({key:library.snapshot(value,key) for key,value in namespace.items()})
                            originals=dict(record['originals']);originals[name]=foreign.__wrapped__
                            replacement['originals']=types.MappingProxyType(originals)
                            library._BINDINGS[identifier]=types.MappingProxyType(replacement)
                        else:library._BINDINGS[identifier]=types.MappingProxyType(replacement)
                        with self.assertRaises(AssertionError):self.check_namespace(number,namespace)
                        self.assertEqual(executed,[])
                    finally:
                        library._BINDINGS.pop(identifier+1,None)
                        library._BINDINGS[identifier]=record;namespace[name]=hook
                    self.check_namespace(number,namespace)
            self.assertEqual(comp.verify_current(),self.model)

    def test_auxiliary_direct_saved_function_closure_cells_reject_changed_targets(self):
        import functools
        with self.modes():
            modules=self.registered()
            for number,name,variable in ((136,'main','original_main'),(138,'check_probe','original_probe')):
                namespace=modules[number].__dict__;hook=namespace[name]
                cells=dict(zip(hook.__code__.co_freevars,hook.__closure__))
                self.assertIn(variable,cells);self.assertNotIn('saved',cells)
                cell=cells[variable];original=cell.cell_contents;executed=[]
                @functools.wraps(original)
                def foreign(*args,**kwargs):executed.append('foreign closure executed');return True
                try:
                    cell.cell_contents=foreign
                    with self.assertRaises(AssertionError):self.check_namespace(number,namespace)
                    self.assertEqual(executed,[])
                finally:cell.cell_contents=original
                self.check_namespace(number,namespace)
            self.assertEqual(comp.verify_current(),self.model)

    def test_failed_all_five_startups_restore_seals_and_allow_same_namespace_registration(self):
        with self.modes():
            self.registered()
            for number,name in self.units.items():
                path='curvature/scripts/'+name+'.py';source=(comp.ROOT/path).read_bytes()
                namespace={'__file__':str(comp.ROOT/path),'__name__':'actual_current_registration_retry_control'}
                library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (111,132,134) else 'curvature_auxiliary_binding')
                before=comp._curvature_registration_seals;primary=RuntimeError('owned registration retry failure')
                with patch.object(comp,'verify_current',side_effect=primary):
                    with self.assertRaises(RuntimeError) as caught:
                        exec(compile(source,str(comp.ROOT/path),'exec',dont_inherit=True),namespace)
                self.assertIs(caught.exception,primary)
                self.assertEqual(comp._curvature_registration_seals,before)
                self.assertNotIn(id(namespace),library._BINDINGS)
                try:
                    exec(compile(source,str(comp.ROOT/path),'exec',dont_inherit=True),namespace)
                    self.check_namespace(number,namespace)
                finally:
                    # Restore only this test-owned successful extra namespace;
                    # production add/rollback APIs remain transaction-restricted.
                    library._BINDINGS.pop(id(namespace),None)
                    comp._curvature_registration_seals=before
                comp.curvature_registration_check(library.__name__,library._BINDINGS)
                self.assertEqual(comp._curvature_registration_seals,before)
            self.assertEqual(comp.verify_current(),self.model)

    def test_forged_fresh_registration_and_foreign_rollback_entry_points_rejected(self):
        import types
        with self.modes():
            modules=self.registered()
            for number,module in modules.items():
                library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (111,132,134) else 'curvature_auxiliary_binding')
                record=library._BINDINGS[id(module.__dict__)];foreign=dict(module.__dict__)
                replacement=dict(record);replacement['namespace']=foreign
                forged=types.MappingProxyType(replacement);before=comp._curvature_registration_seals
                keys=set(library._BINDINGS)
                with self.assertRaisesRegex(AssertionError,'Foreign registration transaction'):
                    comp.curvature_registration_add(library.__name__,library._BINDINGS,forged)
                with self.assertRaisesRegex(AssertionError,'Foreign registry rollback transaction'):
                    comp.curvature_registration_rollback(library.__name__,library._BINDINGS,dict(before)[library.__name__])
                self.assertEqual(set(library._BINDINGS),keys)
                self.assertEqual(comp._curvature_registration_seals,before)
                self.assertIsNone(comp._curvature_install_owner)
                self.check_namespace(number,module.__dict__)
            self.assertEqual(comp.verify_current(),self.model)

    def test_genuine_module_and_dictionary_startups_preserve_all_five_bindings(self):
        import builtins
        with self.modes():
            for binding in (builtins,builtins.__dict__):
                for number,name in self.units.items():
                    path='curvature/scripts/'+name+'.py'
                    namespace={'__file__':str(comp.ROOT/path),'__name__':'genuine_builtins_startup_control',
                               '__builtins__':binding}
                    library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (111,132,134) else 'curvature_auxiliary_binding')
                    before=comp._curvature_registration_seals
                    try:
                        exec(compile((comp.ROOT/path).read_bytes(),str(comp.ROOT/path),'exec',dont_inherit=True),namespace)
                        self.assertIs(namespace['__builtins__'],binding)
                        self.check_namespace(number,namespace)
                        entry=namespace['admit' if number==138 else 'main'].__wrapped__
                        self.assertIs(entry.__builtins__,builtins.__dict__)
                        self.assertEqual(comp.verify_current(),self.model)
                    finally:
                        library._BINDINGS.pop(id(namespace),None)
                        comp._curvature_registration_seals=before
                    comp.curvature_registration_check(library.__name__,library._BINDINGS)

    def test_foreign_builtin_objects_rejected_before_any_five_registration(self):
        import builtins,types
        fake=types.ModuleType('builtins');fake.__dict__.update(builtins.__dict__)
        with self.modes():
            for binding in (dict(builtins.__dict__),fake):
                for number,name in self.units.items():
                    path='curvature/scripts/'+name+'.py'
                    namespace={'__file__':str(comp.ROOT/path),'__name__':'foreign_builtins_startup_control',
                               '__builtins__':binding}
                    library=comp.curvature_embedded_module('curvature_leaf_binding' if number in (111,132,134) else 'curvature_auxiliary_binding')
                    before=comp._curvature_registration_seals;keys=set(library._BINDINGS)
                    with self.assertRaisesRegex(AssertionError,'genuine builtins identity drift'):
                        exec(compile((comp.ROOT/path).read_bytes(),str(comp.ROOT/path),'exec',dont_inherit=True),namespace)
                    self.assertIs(namespace['__builtins__'],binding)
                    self.assertEqual(comp._curvature_registration_seals,before)
                    self.assertEqual(set(library._BINDINGS),keys)
                    self.assertIsNone(comp._curvature_install_owner)
            # A foreign sys.modules alias must not authenticate itself through
            # a property exposing the genuine dictionary.
            canonical=builtins
            class Proxy:
                @property
                def __dict__(self):return canonical.__dict__
            class ModuleSubclass(types.ModuleType):
                @property
                def __dict__(self):return canonical.__dict__
            library=comp.curvature_embedded_module('curvature_leaf_binding')
            reference={'__builtins__':canonical.__dict__}
            namespace={'__builtins__':canonical.__dict__}
            code=compile('def sample(): return len(())\n','canonical_function_before_foreign_alias','exec')
            exec(code,reference);exec(code,namespace)
            before=comp._curvature_registration_seals;keys=set(library._BINDINGS)
            for foreign in (Proxy(),ModuleSubclass('builtins')):
                namespace['__builtins__']=foreign
                self.assertIs(namespace['sample'].__builtins__,canonical.__dict__)
                try:
                    sys.modules['builtins']=foreign
                    with self.assertRaisesRegex(AssertionError,'builtins identity drift'):
                        library.authenticate_builtins(foreign,canonical.__dict__)
                finally:sys.modules['builtins']=canonical
                self.assertIs(namespace['__builtins__'],foreign)
                self.assertEqual(comp._curvature_registration_seals,before)
                self.assertEqual(set(library._BINDINGS),keys)
                self.assertIsNone(comp._curvature_install_owner)
            # The canonical module anchor must remain authoritative even if
            # both import aliases and the mutable metatype attribute change.
            native_module_type=types.ModuleType
            for foreign in (Proxy(),ModuleSubclass('builtins')):
                namespace['__builtins__']=foreign
                self.assertIs(namespace['sample'].__builtins__,canonical.__dict__)
                try:
                    types.ModuleType=type(foreign)
                    sys.modules['builtins']=foreign
                    with self.assertRaisesRegex(AssertionError,'genuine builtins identity drift'):
                        library.authenticate_builtins(foreign,canonical.__dict__)
                    for genuine in (canonical,canonical.__dict__):
                        library.authenticate_builtins(genuine,canonical.__dict__)
                finally:
                    sys.modules['builtins']=canonical
                    types.ModuleType=native_module_type
                self.assertIs(namespace['__builtins__'],foreign)
                self.assertEqual(comp._curvature_registration_seals,before)
                self.assertEqual(set(library._BINDINGS),keys)
                self.assertIsNone(comp._curvature_install_owner)
            self.assertEqual(comp.verify_current(),self.model)

    def test_cached_foreign_function_builtins_and_registered_form_switch_rejected(self):
        import builtins
        library=comp.curvature_embedded_module('curvature_leaf_binding')
        code=compile('def sample(): return len(())\n','genuine_function_builtin_control','exec')
        reference={'__builtins__':builtins.__dict__};exec(code,reference)
        namespace={'__builtins__':dict(builtins.__dict__)};exec(code,namespace)
        cached=namespace['sample'].__builtins__
        namespace['__builtins__']=builtins.__dict__
        self.assertIsNot(cached,builtins.__dict__)
        with self.assertRaisesRegex(AssertionError,'function builtins identity drift'):
            library.initial_chain(namespace['sample'],reference['sample'],namespace,reference)
        with self.modes():
            for number,module in self.registered().items():
                namespace=module.__dict__;original=namespace['__builtins__']
                replacements=(builtins if original is builtins.__dict__ else builtins.__dict__,dict(builtins.__dict__))
                for replacement in replacements:
                    try:
                        namespace['__builtins__']=replacement
                        with self.assertRaisesRegex(AssertionError,'namespace identity drift: __builtins__'):
                            self.check_namespace(number,namespace)
                    finally:namespace['__builtins__']=original
                    self.check_namespace(number,namespace)
            self.assertEqual(comp.verify_current(),self.model)

    def test_genuine_direct_interpreter_and_runpy_builtin_forms(self):
        import tempfile
        raw=comp.CURVATURE_EMBEDDED_SOURCES['curvature_leaf_binding']
        node=next(node for node in ast.parse(raw).body if isinstance(node,ast.FunctionDef) and node.name=='authenticate_builtins')
        source=ast.get_source_segment(raw,node)
        program='import types\n'+source+'''\nimport builtins,runpy
authenticate_builtins(__builtins__,builtins.__dict__)
if __name__=='__main__':
    assert __builtins__ is builtins
    result=runpy.run_path(__file__,run_name='genuine_runpy_builtin_control')
    assert result['__builtins__'] is builtins.__dict__
    print('GENUINE_DIRECT_MODULE_AND_RUNPY_DICTIONARY_PASS')
else:
    assert __builtins__ is builtins.__dict__
'''
        with tempfile.TemporaryDirectory(prefix='point4-genuine-builtins-') as directory:
            path=pathlib.Path(directory)/'actual_builtin_entry.py';path.write_bytes(program.encode())
            result=subprocess.run([sys.executable,'-B','-X','utf8',str(path)],
                                  stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False,timeout=30)
            self.assertEqual(result.returncode,0,result.stderr.decode())
            self.assertEqual(result.stdout.decode().splitlines(),['GENUINE_DIRECT_MODULE_AND_RUNPY_DICTIONARY_PASS'])
            self.assertEqual(path.read_bytes(),program.encode())

# END authenticated finite curvature tests
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--real-runtime',action='store_true');parser.add_argument('--schema',type=pathlib.Path)
    parser.add_argument('--parent-fixtures',type=pathlib.Path)
    parser.add_argument('--support110-fixtures',type=pathlib.Path)
    parser.add_argument('--support115-fixtures',type=pathlib.Path)
    parser.add_argument('--support126-fixtures',type=pathlib.Path)
    args=parser.parse_args();FIXED_FIXTURES=args.support126_fixtures;CONTRACTION_FIXTURES=args.support115_fixtures;OFFLINE=args.parent_fixtures;HEAT_FIXTURES=args.support110_fixtures;SCHEMA=args.schema;REAL=args.real_runtime
    assert not REAL or (sys.platform.startswith('linux') and SCHEMA and SCHEMA.is_file()), 'Actual Linux/schema input required'
    suite=unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(OrdinaryCompositionTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(PositiveControllerTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(ContractionCompositionTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(FixedBackgroundCompositionTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(CurrentAxiomInventoryTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(MapConstructionSnapshotTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(TensorCompositionTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(CurvatureCompositionTests))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(CurvatureProductionNamespaceTests))
    if REAL:suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(RealValidatorTests))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
