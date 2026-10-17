"""Focused tests of reuse boundaries; these do not execute Lean, Git or evidence."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import time
import os
import subprocess
import multiprocessing

import command_broker as broker
from identity import canonical, digest, require, strict_json, OutputBudget, LEDGER_LIMIT
import runner


def _reserve_fixture_worker(root,name,start,results):
    budget=OutputBudget(Path(root),maximum=LEDGER_LIMIT+10,entries=10)
    start.wait()
    try:
        with budget.file(Path(root)/name,maximum=10)as handle:handle.write(b'123456')
        results.put('PASS')
    except RuntimeError:results.put('BOUNDED_REJECT')


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self._budget_tmp=tempfile.TemporaryDirectory()
        OutputBudget(Path(self._budget_tmp.name),initialize=True)
        self._env=mock.patch.dict(os.environ,{'P4_CI_BUDGET_ROOT':self._budget_tmp.name})
        self._env.start()

    def tearDown(self):
        self._env.stop();self._budget_tmp.cleanup()

    def test_audit_only_destination_is_normalized(self):
        a, destination = broker.audit_arguments(['scripts/point4_audit.sh', '--json', '/tmp/point4-a.json'])
        b, _ = broker.audit_arguments(['scripts/point4_audit.sh', '--json', '/tmp/point4-b.json'])
        self.assertEqual(a, b)
        self.assertEqual(destination, Path('/tmp/point4-a.json'))
        for flags in (['--no-build'], ['--json', '../x'], ['--json', '/tmp/x.json'],
                      ['--json', '/tmp/point4-a.json', '--json', '/tmp/point4-b.json']):
            with self.assertRaises(RuntimeError):
                broker.audit_arguments(['scripts/point4_audit.sh', *flags])

    def test_broker_scope_does_not_capture_builds_or_other_epochs(self):
        root = Path('/candidate')
        plan = dict(audit_script='scripts/point4_audit.sh', probe_argv_allowlist=[['env', 'lean', 'scripts/point4_x_probe.lean']],enable_probe_reuse=True)
        self.assertIsNone(broker.classify('lake', ['build'], root/'curvature', root, plan))
        self.assertIsNone(broker.classify('lake', ['env', 'lean', 'scripts/point4_x_probe.lean'], Path('/historical/curvature'), root, plan))
        self.assertIsNone(broker.classify('lake', ['env', 'lean', '-Dpp.all=true', 'scripts/point4_x_probe.lean'], root/'curvature', root, plan))
        self.assertEqual(broker.classify('lake', ['env', 'lean', 'scripts/point4_x_probe.lean'], root/'curvature', root, plan)['kind'], 'probe')

    def test_strict_json_rejects_duplicate_and_nonfinite(self):
        for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}'):
            with self.assertRaises(RuntimeError):
                strict_json(raw)

    def test_replayed_stream_events_preserve_exact_complete_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            (p/'stdout.bin').write_bytes(b'ABC')
            (p/'stderr.bin').write_bytes(b'XY')
            saved = dict(exit_code=1, events=[[0,0,1],[1,0,2],[0,1,2]],
                         streams=[dict(bytes=3,sha256=digest(b'ABC')),dict(bytes=2,sha256=digest(b'XY'))])
            self.assertEqual(broker.validate_payload(p,saved),[b'ABC',b'XY'])
            for events in ([[0,0,3]], [[0,1,2],[1,0,2]], [[0,0,4],[1,0,2]]):
                bad=copy.deepcopy(saved); bad['events']=events
                with self.assertRaises(RuntimeError):broker.validate_payload(p,bad)
            (p/'stdout.bin').write_bytes(b'ABD')
            with self.assertRaises(RuntimeError):broker.validate_payload(p,saved)

    def test_open_exit_is_not_coerced_to_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp); raw=b'{"build_run":true,"verdict":"OPEN"}'
            (p/'audit.json').write_bytes(raw)
            saved=dict(audit_json=dict(bytes=len(raw),sha256=digest(raw)))
            broker.copy_audit_json(p,None,dict(audit_json=None))
            with self.assertRaises(RuntimeError):broker.copy_audit_json(p,None,saved)
            # The broker's returned exit_code stays1. Only original caller
            # parsers may accept the honest OPEN result, never a cache flag.
            (p/'stdout.bin').write_bytes(b'OPEN')
            (p/'stderr.bin').write_bytes(b'')
            actual=dict(exit_code=1,events=[[0,0,4]],streams=[dict(bytes=4,sha256=digest(b'OPEN')),dict(bytes=0,sha256=digest(b''))])
            broker.validate_payload(p,actual)
            self.assertEqual(actual['exit_code'],1)

    def test_only_known_source_expressions(self):
        self.assertEqual(runner.expand('${{ github.event.pull_request.head.sha || github.sha }}','a','b','/tmp','workflow_dispatch'),'a')
        with self.assertRaises(RuntimeError):runner.expand('${{ arbitrary.expression }}','a','b','/tmp','workflow_dispatch')

    def test_source_plan_is_exhaustive_and_preserves_literal_bodies(self):
        p=Path(__file__).with_name('plan.json'); plan=strict_json(p.read_bytes())
        self.assertEqual(len(plan['workflows']),33)
        self.assertEqual(sum(len(w['jobs'])for w in plan['workflows']),35)
        steps=[s for w in plan['workflows']for j in w['jobs']for s in j['steps']if 'run'in s]
        self.assertEqual(len(steps),216)
        for step in steps:self.assertEqual(step['run_sha256'],digest(step['run'].encode()))
        self.assertNotIn('point4_joint_metric_defect_c1_probe.lean',p.read_text())
        kinds={s['uses']for w in plan['workflows']for j in w['jobs']for s in j['steps']if 'uses'in s}
        self.assertEqual(kinds,set(plan['setup_actions'].values()))

    def test_plan_matches_actual_all33_legacy_yaml_sources(self):
        import yaml
        root=Path(__file__).resolve().parents[2]
        plan=strict_json(Path(__file__).with_name('plan.json').read_bytes())
        for workflow in plan['workflows']:
            raw=(root/workflow['path']).read_bytes()
            self.assertEqual(digest(raw),workflow['sha256'])
            source=yaml.safe_load(raw)
            self.assertEqual(list(source['jobs']),[j['id']for j in workflow['jobs']])
            self.assertEqual(source.get('defaults',{}),workflow['defaults'])
            self.assertEqual(source.get('env',{}),workflow['env'])
            for job in workflow['jobs']:
                original=source['jobs'][job['id']]
                self.assertEqual(original.get('env',{}),job['env'])
                self.assertEqual(original.get('defaults',{}),job['defaults'])
                self.assertEqual(original.get('timeout-minutes',360),job['timeout_minutes'])
                self.assertEqual(len(original['steps']),len(job['steps']))
                for before,after in zip(original['steps'],job['steps']):
                    self.assertEqual(before,{k:v for k,v in after.items()if k not in ('ordinal','run_sha256')})

    def test_step_budget_uses125step_not350job(self):
        state=dict(active_seconds=60.0)
        with mock.patch.object(runner.time,'monotonic',return_value=100):
            self.assertEqual(runner.step_budget({'timeout-minutes':125},{'timeout_minutes':350},state,{'deadline':30000}),7500)
            self.assertEqual(runner.step_budget({'timeout-minutes':125},{'timeout_minutes':350},state,{'deadline':110}),10)

    def test_default_probe_reuse_disabled_and_no_json_audit_native(self):
        root=Path('/candidate')
        plan=dict(audit_script='scripts/point4_audit.sh',probe_argv_allowlist=[['env','lean','x.lean']],enable_probe_reuse=False)
        self.assertIsNone(broker.classify('lake',['env','lean','x.lean'],root/'curvature',root,plan))
        self.assertIsNone(broker.classify('bash',['scripts/point4_audit.sh'],root/'curvature',root,plan))

    def test_stream_seal_detects_mutable_compiled_plugin(self):
        from identity import stream_seal
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'plugin.so';path.write_bytes(b'first')
            first=stream_seal(path)
            path.write_bytes(b'other')
            self.assertNotEqual(first,stream_seal(path))
            with self.assertRaises(RuntimeError):stream_seal(path,maximum=2)

    def test_chart_case_has_real_path_and_projected_workspace(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'cases').mkdir()
            context=dict(evidence=p,env={'PATH':'/broker:/real','GITHUB_WORKSPACE':'/execution'},real_path='/real',
                         expansion=dict(sha='a',tree='b',runner_temp='/tmp',event='workflow_dispatch'))
            state=runner.prepare_case({'path':'.github/workflows/point4-local-chart-connection.yml'}, {'id':'chart_connection'},context)
            self.assertEqual(state['env']['PATH'],'/real')
            self.assertEqual(state['env']['GITHUB_WORKSPACE'],'/execution')

    def test_owned_unit_rejects_foreign_cwd_and_invocation(self):
        spec=dict(unit='chart-port-123-1.service',root='/execution',argv=['/usr/bin/python3','driver.py'],executable='/usr/bin/python3')
        values=dict(Id=spec['unit'],LoadState='loaded',ActiveState='active',User=str(os.getuid()),
                    WorkingDirectory='/execution',InvocationID='b'*32,MainPID='123',ControlGroup='/system.slice/'+spec['unit'])
        owner=dict(pid=123,cgroup=values['ControlGroup'],cgroup_dev=0,cgroup_ino=0)
        result=mock.Mock(returncode=0,stdout='\n'.join(k+'='+v for k,v in values.items()).encode(),stderr=b'')
        with mock.patch.object(runner.subprocess,'run',return_value=result),mock.patch.object(runner,'process_owner',return_value=owner):
            self.assertEqual(runner.owned_unit_snapshot(spec)['owner'],owner)
        wrong=dict(values,WorkingDirectory='/foreign')
        with mock.patch.object(runner.subprocess,'run',return_value=mock.Mock(returncode=0,stdout='\n'.join(k+'='+v for k,v in wrong.items()).encode(),stderr=b'')):
            with self.assertRaises(RuntimeError):runner.owned_unit_snapshot(spec)
        observed=dict(values,owner=owner)
        with mock.patch.object(runner,'owned_unit_snapshot',return_value=dict(observed,InvocationID='c'*32)),mock.patch.object(runner,'_group_empty',return_value=False):
            with self.assertRaises(RuntimeError):runner.cleanup_owned_unit(spec,observed)

    def test_proc_owner_matches_whole_argv_not_substrings(self):
        spec=dict(root='/execution',executable='/usr/bin/python3.12',
                  argv=['/usr/bin/python3','curvature/scripts/chart_port_ci.py','--expected-sha','a'*40,
                        '--expected-tree','b'*40,'--evidence','/tmp/exact-evidence'])
        group='/system.slice/chart-port-123-1.service'
        stat_raw=b'123 (python3) S '+b'0 '*18+b'42 0 0'
        def run(actual_argv):
            def read(path,maximum):
                if path.name=='stat':return stat_raw
                if path.name=='cmdline':return b'\0'.join(x.encode()for x in actual_argv)+b'\0'
                if path.name=='status':return ('Uid: '+(' '.join([str(os.getuid())]*4))).encode()
                if path.name=='cgroup':return b'0::'+group.encode()+b'\n'
                raise AssertionError(path)
            def resolve(path,*args,**kwargs):
                return Path(spec['executable']if path.name=='exe'else spec['root'])
            with mock.patch.object(runner,'_bounded_proc',side_effect=read), \
                 mock.patch.object(Path,'resolve',autospec=True,side_effect=resolve), \
                 mock.patch.object(Path,'stat',return_value=mock.Mock(st_dev=1,st_ino=2)):
                return runner.process_owner(123,spec,group)
        self.assertEqual(run(spec['argv'])['argv'],spec['argv'])
        for index in (3,5,7):
            changed=list(spec['argv']);changed[index]+='-suffix'
            with self.assertRaises(RuntimeError):run(changed)

    def test_stop_timeout_still_forcekills_and_proves_empty(self):
        spec=dict(unit='chart-port-123-1.service')
        values=dict(InvocationID='b'*32,ControlGroup='/system.slice/'+spec['unit'],ActiveState='active',SubState='running',Job='0',
                    owner=dict(cgroup='/system.slice/'+spec['unit'],cgroup_dev=0,cgroup_ino=0))
        state=dict(killed=False)
        def snapshot(*args,**kwargs):
            return dict(values,ActiveState='inactive',SubState='dead')if state['killed']else values
        def execute(argv,**kwargs):
            if 'kill'in argv:state['killed']=True;return mock.Mock(returncode=0)
            raise subprocess.TimeoutExpired('stop',5)
        with mock.patch.object(runner,'owned_unit_snapshot',side_effect=snapshot), \
             mock.patch.object(runner,'_group_empty',side_effect=lambda group:state['killed']), \
             mock.patch.object(runner.subprocess,'run',side_effect=execute)as calls:
            result=runner.cleanup_owned_unit(spec,values)
        self.assertTrue(result['confirmed_empty']);self.assertTrue(result['confirmed_terminal']);self.assertTrue(result['force_kill'])
        self.assertEqual(calls.call_args_list[-1].args[0],['sudo','-n','systemctl','kill','--signal=SIGKILL','--kill-who=all','--',spec['unit']])

    def test_startup_observation_refreshes_live_owner_with_same_invocation(self):
        spec=dict(unit='chart-port-123-1.service')
        observed=dict(InvocationID='b'*32,ControlGroup='',MainPID='0',owner=None,ActiveState='activating',SubState='start',Job='12')
        live=dict(observed,MainPID='123',ControlGroup='/system.slice/'+spec['unit'],ActiveState='active',SubState='running',Job='0',
                  owner=dict(cgroup='/system.slice/'+spec['unit'],cgroup_dev=0,cgroup_ino=0))
        terminal=dict(live,ActiveState='inactive',SubState='dead',MainPID='0')
        with mock.patch.object(runner,'owned_unit_snapshot',side_effect=[dict(live,owner=None),live,terminal,terminal])as inspect, \
             mock.patch.object(runner,'_group_empty',return_value=True),mock.patch.object(runner.subprocess,'run',return_value=mock.Mock(returncode=0)):
            result=runner.cleanup_owned_unit(spec,observed)
        self.assertTrue(result['stop_requested']);self.assertTrue(result['confirmed_terminal'])
        self.assertEqual(inspect.call_args_list[1].kwargs,{})

    def test_queued_empty_unit_is_canceled_not_assumed_finished(self):
        spec=dict(unit='chart-port-123-1.service')
        queued=dict(InvocationID='b'*32,ControlGroup='',MainPID='0',owner=None,ActiveState='activating',SubState='start',Job='12')
        terminal=dict(queued,ActiveState='inactive',SubState='dead',Job='0')
        with mock.patch.object(runner,'owned_unit_snapshot',side_effect=[queued,queued,terminal,terminal]), \
             mock.patch.object(runner,'queued_unit_config',return_value=dict(argv=['exact']))as config, \
             mock.patch.object(runner.subprocess,'run',return_value=mock.Mock(returncode=0))as stop:
            result=runner.cleanup_owned_unit(spec,queued)
        self.assertEqual(config.call_count,1);self.assertEqual(stop.call_count,1)
        self.assertTrue(result['stop_requested']);self.assertTrue(result['confirmed_terminal'])

    def test_queued_unit_becomes_live_during_retry_timeout_then_is_killed(self):
        spec=dict(unit='chart-port-123-1.service')
        queued=dict(InvocationID='b'*32,ControlGroup='',MainPID='0',owner=None,
                    ActiveState='activating',SubState='start',Job='12')
        group='/system.slice/'+spec['unit']
        owner=dict(cgroup=group,cgroup_dev=0,cgroup_ino=0)
        live=dict(queued,ControlGroup=group,MainPID='123',ActiveState='active',SubState='running',Job='0',owner=owner)
        terminal=dict(queued,ActiveState='inactive',SubState='dead',Job='0')
        state=dict(stops=0,live=False,killed=False,vanish=False)
        def snapshot(spec,inspect_process=True):
            if state['killed']:return terminal # manager clears group; retained group must still be checked
            if state['live']:
                if inspect_process and not state['vanish']:
                    state['vanish']=True;raise FileNotFoundError('PID exited during /proc refresh')
                return live if inspect_process else dict(live,owner=None)
            return queued
        def execute(argv,**kwargs):
            if 'stop'in argv:
                state['stops']+=1
                if state['stops']==2:state['live']=True
                raise subprocess.TimeoutExpired('stop',5)
            self.assertEqual(argv,['sudo','-n','systemctl','kill','--signal=SIGKILL','--kill-who=all','--',spec['unit']])
            state['killed']=True;return mock.Mock(returncode=0)
        checked=[]
        def empty(actual):checked.append(actual);return state['killed']
        with mock.patch.object(runner,'owned_unit_snapshot',side_effect=snapshot), \
             mock.patch.object(runner,'queued_unit_config',return_value=dict(argv=['exact']))as config, \
             mock.patch.object(runner,'_group_empty',side_effect=empty), \
             mock.patch.object(runner.subprocess,'run',side_effect=execute)as calls, \
             mock.patch.object(runner.time,'sleep'):
            result=runner.cleanup_owned_unit(spec,queued)
        self.assertEqual(state['stops'],2);self.assertTrue(state['vanish']);self.assertTrue(state['killed'])
        self.assertTrue(result['force_kill']);self.assertTrue(result['confirmed_terminal']);self.assertTrue(result['confirmed_empty'])
        self.assertGreaterEqual(config.call_count,2);self.assertIn(group,checked)
        self.assertEqual(sum('kill'in row.args[0]for row in calls.call_args_list),1)

    def test_structured_queued_config_rejects_multiple_or_extra_argv(self):
        spec=dict(unit='chart-port-123-1.service',executable=str(Path('/usr/bin/python3').resolve()),
                  argv=['/usr/bin/python3','driver.py','--expected-sha','a'*40])
        row=[spec['argv'][0],spec['argv'],False,0,0,0,0,0,0,0]
        def read(value):
            with mock.patch.object(runner.subprocess,'run',return_value=mock.Mock(returncode=0,stdout=canonical(value),stderr=b'')):
                return runner.queued_unit_config(spec)
        self.assertEqual(read(dict(type='a(sasbttttuii)',data=[row]))['argv'],spec['argv'])
        for value in [dict(type='unknown',data=[row]),dict(type='a(sasbttttuii)',data=[row,row]),
                      dict(type='a(sasbttttuii)',data=[[row[0],row[1]+['extra'],*row[2:]]])]:
            with self.assertRaises(RuntimeError):read(value)

    def test_source_prephase_does_not_reach_lean_action_or_native_seed(self):
        plan=dict(setup_actions=dict(lean='lean-action',upload='upload'))
        job=dict(id='job',name='job',timeout_minutes=350,steps=[
            dict(ordinal=1,run='echo guard',run_sha256=digest(b'echo guard')),
            dict(ordinal=2,uses='lean-action'),dict(ordinal=3,run='native',run_sha256=digest(b'native'))])
        workflow=dict(path='.github/workflows/source.yml',name='source')
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'cases').mkdir()
            context=dict(evidence=p,env={},execution=p,tooling=p,real_path='/real',plan=plan,real_bash='/usr/bin/bash',
                         deadline=time.monotonic()+1000,expansion=dict(sha='a',tree='b',runner_temp='/tmp',event='workflow_dispatch'))
            state=runner.prepare_case(workflow,job,context)
            result=dict(exit_code=0,timed_out=False,leaked_group_killed=False,elapsed_seconds=1)
            with mock.patch.object(runner,'run_process',return_value=result) as execute, mock.patch.object(runner,'evidence_usage'):
                self.assertIsNone(runner.execute_job(workflow,job,context,state,preflight_only=True))
                self.assertEqual(execute.call_count,1)
                self.assertEqual(state['next_step'],1)
                self.assertGreaterEqual(state['active_seconds'],0)

    def test_audit_g2_failure_is_never_reusable(self):
        passed=dict(build_run=True,gates=dict(G2_build_green=dict(status='PASS')))
        self.assertTrue(broker.audit_native_eligible(1,passed))
        self.assertFalse(broker.audit_native_eligible(2,passed))
        self.assertFalse(broker.audit_native_eligible(1,dict(passed,build_run=False)))
        self.assertFalse(broker.audit_native_eligible(1,dict(build_run=True,gates=dict(G2_build_green=dict(status='FAIL')))))

    def test_audit_build_side_effect_whole_byte_seal(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);raw=b'Build completed successfully (3957 jobs).\n'
            (p/'build.log').write_bytes(raw)
            row=dict(bytes=len(raw),sha256=digest(raw))
            self.assertEqual(broker.validate_side_effect(p,row),raw)
            (p/'build.log').write_bytes(raw.replace(b'3957',b'0000'))
            with self.assertRaises(RuntimeError):broker.validate_side_effect(p,row)

    def test_failed_source_prefix_only_runs_always_diagnostics(self):
        workflow=dict(path='.github/workflows/failure.yml',name='failure')
        job=dict(id='job',name='job',timeout_minutes=350,steps=[
            dict(ordinal=1,run='bad guard',run_sha256=digest(b'bad guard')),
            dict(ordinal=2,uses='lean-action'),
            dict(ordinal=3,run='native',run_sha256=digest(b'native')),
            dict(ordinal=4,run='post guard',run_sha256=digest(b'post guard'),**{'if':'always()'})])
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'cases').mkdir()
            context=dict(evidence=p,env={},execution=p,tooling=p,real_path='/real',
                         plan=dict(setup_actions=dict(lean='lean-action',upload='upload')),real_bash='/usr/bin/bash',
                         deadline=time.monotonic()+1000,expansion=dict(sha='a',tree='b',runner_temp='/tmp',event='workflow_dispatch'))
            state=runner.prepare_case(workflow,job,context)
            bad=dict(exit_code=1,timed_out=False,leaked_group_killed=False)
            good=dict(exit_code=0,timed_out=False,leaked_group_killed=False)
            with mock.patch.object(runner,'run_process',side_effect=[bad,good]) as execute, mock.patch.object(runner,'evidence_usage'):
                result=runner.execute_job(workflow,job,context,state,preflight_only=True)
            self.assertEqual(result['status'],'FAIL')
            self.assertEqual(execute.call_count,2)
            self.assertEqual([s['status']for s in result['steps']],['FAIL','SKIPPED_AFTER_FAILURE','SKIPPED_AFTER_FAILURE','PASS'])

    def test_nested_weighted_audit_original_argv_is_native(self):
        plan=dict(audit_script='scripts/point4_audit.sh',probe_argv_allowlist=[],enable_probe_reuse=False)
        root=Path('/candidate')
        self.assertIsNone(broker.classify('bash',['scripts/point4_audit.sh','--json','/tmp/point4-weighted-hessian-evidence/audit.json'],root/'curvature',root,plan))

    def test_parent_burst_is_rejected_before_log_write(self):
        with tempfile.TemporaryDirectory()as tmp:
            log=Path(tmp)/'burst.log'
            with mock.patch.object(runner,'MAX_LOG',16):
                with self.assertRaises(RuntimeError):
                    runner.run_process(['/usr/bin/python3','-c','import sys;sys.stdout.buffer.write(b"x"*100000)'],Path(tmp),dict(os.environ),log,5)
            self.assertLessEqual(log.stat().st_size,16)

    def test_two_writers_cannot_oversubscribe_reserved_bytes(self):
        with tempfile.TemporaryDirectory()as tmp:
            root=Path(tmp);OutputBudget(root,initialize=True,maximum=LEDGER_LIMIT+10,entries=10)
            ctx=multiprocessing.get_context('fork');start=ctx.Event();results=ctx.Queue()
            children=[ctx.Process(target=_reserve_fixture_worker,args=(tmp,name,start,results))for name in('a','b')]
            for child in children:child.start()
            start.set();verdicts=[results.get(timeout=10)for _ in children]
            for child in children:child.join(10);self.assertFalse(child.is_alive());self.assertEqual(child.exitcode,0)
            self.assertEqual(sorted(verdicts),['BOUNDED_REJECT','PASS'])
            self.assertEqual(sum((root/name).stat().st_size for name in('a','b')),6)
            results.close();results.join_thread()

    def test_identity_changes_for_command_source_env_and_candidate(self):
        value=dict(candidate='a',source='b',env='c',argv=['lake','env','lean','probe.lean'])
        key=digest(canonical(value))
        for name in value:
            other=copy.deepcopy(value);other[name]='changed'
            self.assertNotEqual(key,digest(canonical(other)))


if __name__=='__main__':
    unittest.main()
