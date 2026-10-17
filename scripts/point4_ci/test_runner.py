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
import shutil

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


class EffectiveSearchTests(unittest.TestCase):
    """Exercise the real compiled inventory against finite Lake environment fixtures."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / 'candidate'
        self.package = self.root / 'curvature'
        self.prefix = Path(self.tmp.name) / 'toolchain'
        self.build = self.package / '.lake/build/lib/lean'
        self.dependency = self.package / '.lake/packages/dependency'
        self.depbuild = self.dependency / '.lake/build/lib/lean'
        for path in (self.build, self.depbuild, self.prefix / 'lib/lean', self.prefix / 'src',
                     Path(self.tmp.name) / 'outside'):
            path.mkdir(parents=True)
        (self.package / 'lake-manifest.json').write_text(json.dumps({
            'packages': [{'type': 'git', 'name': 'dependency'}]}))
        (self.build / 'Fixture.olean').write_bytes(b'compiled fixture')
        (self.package / 'Fixture.lean').write_text('-- Source fixture\n')
        (self.depbuild / 'Dependency.olean').write_bytes(b'dependency fixture')
        (self.dependency / 'Dependency.lean').write_text('-- dependency fixture\n')
        self.search = {'LEAN_PATH': '.lake/build/lib/lean:.lake/packages/dependency/.lake/build/lib/lean',
                       'LEAN_SRC_PATH': '.:.lake/packages/dependency:' + str(self.prefix / 'src')}

    def tearDown(self):
        self.tmp.cleanup()

    def inventory(self):
        import identity
        def lake(argv, cwd):
            self.assertEqual(cwd, self.package)
            if argv == ['/pinned/lake', 'env', 'lean', '--print-prefix']:
                return str(self.prefix).encode()
            self.assertEqual(argv[:4], ['/pinned/lake', 'env', 'python3', '-c'])
            return canonical(self.search)
        with mock.patch.object(identity, 'command', side_effect=lake), \
             mock.patch.object(identity, 'reject_untracked_modules'):
            return identity.compiled_identity(self.root, '/pinned/lake', {})

    def test_real_inventory_resolves_relative_roots_in_queried_package(self):
        actual = self.inventory()
        self.assertEqual(actual['search'], self.search)
        self.assertEqual(actual['search_resolution']['package_cwd'], str(self.package))
        self.assertEqual(actual['search_resolution']['paths']['LEAN_PATH'], [
            {'raw': '.lake/build/lib/lean', 'resolved': str(self.build)},
            {'raw': '.lake/packages/dependency/.lake/build/lib/lean', 'resolved': str(self.depbuild)}])
        self.assertEqual(actual['files'], 2)

    def test_process_cwd_does_not_change_relative_search_identity(self):
        before = self.inventory()
        previous = Path.cwd()
        try:
            os.chdir(Path(self.tmp.name) / 'outside')
            self.assertEqual(self.inventory(), before)
        finally:
            os.chdir(previous)

    def test_absolute_core_roots_and_duplicate_order_remain_bound(self):
        core = str(self.prefix / 'lib/lean')
        self.search['LEAN_PATH'] += ':' + core + ':.lake/build/lib/lean'
        actual = self.inventory()
        self.assertEqual([row['raw'] for row in actual['search_resolution']['paths']['LEAN_PATH']],
                         self.search['LEAN_PATH'].split(':'))
        self.search['LEAN_PATH'] = core + ':' + self.search['LEAN_PATH']
        self.assertNotEqual(self.inventory(), actual)

    def test_unknown_missing_file_and_escaping_alias_are_rejected(self):
        outside = Path(self.tmp.name) / 'outside'
        (self.package / 'escape').symlink_to(outside, target_is_directory=True)
        for raw in ('missing', '../outside', str(outside), 'Fixture.lean', 'escape'):
            with self.subTest(raw=raw):
                self.search['LEAN_PATH'] = raw
                with self.assertRaises(RuntimeError):
                    self.inventory()

    def test_complete_compiled_bytes_are_still_hashed_on_every_call(self):
        before = self.inventory()
        (self.depbuild / 'Dependency.olean').write_bytes(b'dependency changed')
        after = self.inventory()
        self.assertNotEqual(before['inventory_sha256'], after['inventory_sha256'])

    def unbuild_dependency(self):
        shutil.rmtree(self.dependency / '.lake')

    def test_manifest_dependency_absent_slot_is_bound_without_materialization(self):
        self.unbuild_dependency()
        before = self.inventory()
        row = before['search_resolution']['paths']['LEAN_PATH'][1]
        parent = self.dependency.stat()
        self.assertEqual(row, dict(raw='.lake/packages/dependency/.lake/build/lib/lean',
                                   resolved=str(self.depbuild), state='absent',
                                   missing_from=str(self.dependency / '.lake'),
                                   absent_parent=dict(path=str(self.dependency), device=parent.st_dev,
                                                      inode=parent.st_ino, mode=parent.st_mode)))
        self.assertFalse((self.dependency / '.lake').exists())
        self.assertEqual(self.inventory(), before)
        self.assertEqual(before['files'], 1)
        self.search['LEAN_PATH'] = str(self.depbuild) + ':' + self.search['LEAN_PATH']
        after = self.inventory()
        self.assertEqual([r['state'] for r in after['search_resolution']['paths']['LEAN_PATH']
                          if 'state' in r], ['absent', 'absent'])
        self.assertNotEqual(before, after)

    def test_missing_slot_frontier_and_absence_transitions_change_identity(self):
        self.unbuild_dependency()
        absent = self.inventory()
        (self.dependency / '.lake/build').mkdir(parents=True)
        frontier = self.inventory()
        self.assertNotEqual(absent, frontier)
        self.depbuild.mkdir(parents=True)
        empty = self.inventory()
        self.assertNotEqual(frontier, empty)
        (self.depbuild / 'Dependency.olean').write_bytes(b'compiled')
        present = self.inventory()
        self.assertNotEqual(empty, present)
        self.unbuild_dependency()
        self.assertEqual(absent, self.inventory())

    def test_absent_marker_binds_nearest_existing_ancestor_identity(self):
        self.unbuild_dependency()
        before = self.inventory()
        self.dependency.rename(self.dependency.with_name('old-dependency'))
        self.dependency.mkdir()
        (self.dependency / 'Dependency.lean').write_text('-- dependency fixture\n')
        after = self.inventory()
        self.assertNotEqual(before, after)
        a = before['search_resolution']['paths']['LEAN_PATH'][1]
        b = after['search_resolution']['paths']['LEAN_PATH'][1]
        self.assertEqual(a['missing_from'], b['missing_from'])
        self.assertNotEqual(a['absent_parent'], b['absent_parent'])

    def test_absent_slots_reject_unknown_descendants_core_and_source_paths(self):
        self.unbuild_dependency()
        for name, raw in [('LEAN_PATH', str(self.depbuild / 'unknown')),
                          ('LEAN_PATH', str(self.depbuild.parent)),
                          ('LEAN_PATH', '.lake/packages/unknown/.lake/build/lib/lean'),
                          ('LEAN_PATH', str(self.prefix / 'lib/missing')),
                          ('LEAN_SRC_PATH', str(self.depbuild)),
                          ('LEAN_PATH', str(self.depbuild / '../lean'))]:
            with self.subTest(name=name, raw=raw):
                old = self.search[name]
                self.search[name] = raw
                try:
                    with self.assertRaises(RuntimeError):
                        self.inventory()
                finally:
                    self.search[name] = old

    def test_absent_slots_reject_live_and_dangling_ancestor_aliases(self):
        self.unbuild_dependency()
        target = Path(self.tmp.name) / 'outside'
        for destination in (target, target / 'missing'):
            with self.subTest(destination=destination):
                alias = self.dependency / '.lake'
                alias.symlink_to(destination, target_is_directory=True)
                try:
                    with self.assertRaises(RuntimeError):
                        self.inventory()
                finally:
                    alias.unlink()
        self.depbuild.parent.mkdir(parents=True)
        self.depbuild.symlink_to(target / 'missing', target_is_directory=True)
        with self.assertRaises(RuntimeError):
            self.inventory()

    def test_absent_slot_existing_file_is_rejected(self):
        self.unbuild_dependency()
        self.depbuild.parent.mkdir(parents=True)
        self.depbuild.write_bytes(b'not a directory')
        with self.assertRaises(RuntimeError):
            self.inventory()

    def test_absent_frontier_does_not_hide_permission_errors(self):
        import identity
        self.unbuild_dependency()
        original = Path.lstat
        denied = self.dependency / '.lake'
        def lstat(path):
            if path == denied:
                raise PermissionError('fixture denial')
            return original(path)
        with mock.patch.object(Path, 'lstat', lstat):
            with self.assertRaises(PermissionError):
                identity.absent_search_frontier(self.depbuild)

    def test_absent_slot_appearance_during_inventory_is_rejected(self):
        import identity
        self.unbuild_dependency()
        original = identity.stream_seal
        def seal(path, *args):
            self.depbuild.mkdir(parents=True, exist_ok=True)
            return original(path, *args)
        with mock.patch.object(identity, 'stream_seal', side_effect=seal):
            with self.assertRaises(RuntimeError):
                self.inventory()


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self._budget_tmp=tempfile.TemporaryDirectory()
        OutputBudget(Path(self._budget_tmp.name),initialize=True)
        self._env=mock.patch.dict(os.environ,{'P4_CI_BUDGET_ROOT':self._budget_tmp.name})
        self._env.start()

    def tearDown(self):
        self._env.stop();self._budget_tmp.cleanup()

    def test_five_stage_partition_is_exact_and_preserves_all_cases(self):
        plan=json.loads(Path(__file__).with_name('plan.json').read_text())
        assignments=[runner.stage_partition(plan,stage)for stage in runner.STAGES]
        self.assertEqual([(row['assigned_workflow_count'],row['assigned_job_count'],row['assigned_run_count'])
                          for row in assignments],[(11,11,69),(2,3,25),(6,7,30),(6,6,41),(8,8,51)])
        self.assertEqual(sum(row['assigned_run_count']for row in assignments),216)
        self.assertEqual(len({row['partition_sha256']for row in assignments}),1)
        self.assertEqual(plan['stages']['first'][:7],[row['path']for row in plan['workflows'][:7]])
        all_cases={(w['path'],j['id'])for w in plan['workflows']for j in w['jobs']}
        selected=[{(w['path'],j['id'])for w in row['workflows']for j in w['jobs']}for row in assignments]
        for i,group in enumerate(selected):
            for other in selected[i+1:]:self.assertFalse(group&other)
        self.assertEqual(set().union(*selected),all_cases)

    def test_stage_partition_rejects_dropped_workflow(self):
        plan=json.loads(Path(__file__).with_name('plan.json').read_text());plan['stages']['first'].pop()
        with self.assertRaises(RuntimeError):runner.stage_partition(plan,'first')

    def test_stage_partition_rejects_overlap_and_reassignment(self):
        original=json.loads(Path(__file__).with_name('plan.json').read_text())
        overlap=copy.deepcopy(original);overlap['stages']['first'].append(overlap['stages']['second'][0])
        with self.assertRaises(RuntimeError):runner.stage_partition(overlap,'first')
        shifted=copy.deepcopy(original)
        shifted['stages']['first'][0],shifted['stages']['second'][0]=shifted['stages']['second'][0],shifted['stages']['first'][0]
        with self.assertRaises(RuntimeError):runner.stage_partition(shifted,'second')

    def test_stage_partition_rejects_unknown_stage(self):
        plan=json.loads(Path(__file__).with_name('plan.json').read_text())
        for stage in ('all','sixth','',None):
            with self.assertRaises(RuntimeError):runner.stage_partition(plan,stage)

    def test_sequential_stages_keep_one_cache_writer_and_original_timeouts(self):
        import yaml
        path=Path(__file__).resolve().parents[2]/'.github/workflows/point4-consolidated.yml'
        workflow=yaml.safe_load(path.read_text());jobs=workflow['jobs']
        self.assertEqual(tuple(jobs),runner.STAGES)
        self.assertFalse(workflow['concurrency']['cancel-in-progress'])
        writer_stages=[]
        for index,stage in enumerate(runner.STAGES):
            job=jobs[stage];self.assertEqual(job['timeout-minutes'],360)
            self.assertEqual(job.get('needs'),None if index==0 else runner.STAGES[index-1])
            self.assertEqual(job['env']['P4_CI_STAGE'],stage)
            native=[step for step in job['steps']if step.get('id')=='native']
            self.assertEqual(len(native),1);self.assertIn('--budget-seconds 19800',native[0]['run'])
            saves=[step for step in job['steps']if step.get('with',{}).get('phase')=='save']
            self.assertEqual(len(saves),1)
            self.assertEqual(saves[0]['if'],"success() && env.P4_CI_STAGE == 'first'")
            if stage=='first':writer_stages.append(stage)
        self.assertEqual(writer_stages,['first'])

    def test_stage_outcome_never_claims_pair_success_or_partial_completion(self):
        plan=json.loads(Path(__file__).with_name('plan.json').read_text())
        assignment=runner.stage_partition(plan,'second')
        rows=[dict(workflow=w['path'],job=j['id'],status='PASS')for w in assignment['workflows']for j in w['jobs']]
        complete=runner.stage_outcome(assignment,rows,False)
        self.assertTrue(complete['stage_passed']);self.assertFalse(complete['all_cases_passed'])
        self.assertTrue(complete['pair_join_required']);self.assertEqual(complete['coverage_scope'],'ASSIGNED_STAGE_ONLY')
        for partial in ([],rows[:-1],[dict(rows[0],status='FAIL')]):
            self.assertFalse(runner.stage_outcome(assignment,partial,False)['stage_passed'])
        self.assertFalse(runner.stage_outcome(assignment,rows,True)['stage_passed'])
        for invalid in (rows+[rows[0]],rows+[dict(workflow='foreign',job='x',status='PASS')]):
            with self.assertRaises(RuntimeError):runner.stage_outcome(assignment,invalid,False)

    def test_all_consumer_stages_require_hit_and_exact_identity(self):
        proof=dict(head='a'*40,tree='b'*40);toolchain=dict(version='official version',compiler_sha256='c'*64)
        provider={name:'actual-'+name for name in ('GITHUB_REPOSITORY','GITHUB_REF','GITHUB_WORKFLOW_REF','GITHUB_WORKFLOW_SHA')}
        identity=dict(schema='point4-exact-candidate-cache-v1',head=proof['head'],tree=proof['tree'],
                      compiler_version=toolchain['version'],compiler_binary_sha256=toolchain['compiler_sha256'],
                      targets=['PoincareCurvature'],provider_scope=provider)
        key='point4-candidate-v1-'+digest(json.dumps(identity,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode())
        state=dict(restore_complete=True,cache_hit=True,restored_bytes=1,identity=identity,key=key)
        for stage in runner.STAGES[1:]:
            actual=runner.compiled_cache_provenance(canonical(state),stage,proof,toolchain,provider)
            self.assertFalse(actual['cache_writer_allowed']);self.assertEqual(actual['proof_credit'],0)
            self.assertTrue(actual['consumer_stage_read_only_enforced_by_coordinator'])
            for changes in (dict(cache_hit=False,restored_bytes=0),dict(restored_bytes=0),dict(restore_complete=False),dict(key='wrong')):
                with self.assertRaises(RuntimeError):
                    runner.compiled_cache_provenance(canonical(dict(state,**changes)),stage,proof,toolchain,provider)
            for changed_proof in (dict(proof,head='d'*40),dict(proof,tree='d'*40)):
                with self.assertRaises(RuntimeError):runner.compiled_cache_provenance(canonical(state),stage,changed_proof,toolchain,provider)
            with self.assertRaises(RuntimeError):runner.compiled_cache_provenance(canonical(state),stage,proof,dict(toolchain,compiler_sha256='wrong'),provider)
            with self.assertRaises(RuntimeError):runner.compiled_cache_provenance(canonical(state),stage,proof,toolchain,dict(provider,GITHUB_WORKFLOW_SHA='other'))
        miss=dict(state,cache_hit=False,restored_bytes=0)
        first=runner.compiled_cache_provenance(canonical(miss),'first',proof,toolchain,provider)
        self.assertTrue(first['cache_writer_allowed']);self.assertFalse(first['cache_hit'])

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



class CompactProjectionTests(unittest.TestCase):
    """Synthetic saved-byte transport fixtures; no Lean/Git/native qualification."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.evidence=self.root/'evidence';self.evidence.mkdir()
        self.output=self.root/'review';self.plan=json.loads(Path(__file__).with_name('plan.json').read_bytes())
        self.assignment=runner.stage_partition(self.plan,'fifth')
        self.expansion=dict(sha='f'*40,tree='e'*40,runner_temp='/fixture-temp',event='workflow_dispatch')
        self.binding=dict(tooling={'head':'f'*40,'tree':'e'*40},proof={'head':'f'*40,'tree':'e'*40},chart={'head':'f'*40,'tree':'e'*40},broker_path='/fixed/broker.py',source_post_valid=True,cache_final_valid=True)
        self.coverage=dict(schema='point4-consolidated-stage-coverage-v2',stage='fifth',stage_passed=True,all_cases_passed=False,
            required_stages=list(runner.STAGES),
            partition_sha256=self.assignment['partition_sha256'],full_partition=self.assignment['partition'],stopped_after_first_failure=False,
            tooling_source=self.binding['tooling'],executed_proof_source=self.binding['proof'],chart_proof_source=self.binding['chart'],jobs=[],provider_context={'run_id':'fixture'})
        self.write('output-budget.json',b'{}');self.write('output-budget.lock',b'')
        self.write('compiled-cache-provenance.json',b'{}')
        self.coverage['compiled_cache_provenance']={'state_sha256':digest(b'{}'),'state_bytes':2}
        self.coverage['native_initial_full_build']=self.process('native-full-build.log',b'complete seed\n')
        for workflow in self.assignment['workflows']:
            for job in workflow['jobs']:
                case=workflow['path'].split('/')[-1][:-4]+'--'+job['id'];steps=[]
                for step in job['steps']:
                    row=dict(ordinal=step['ordinal'],name=step.get('name'),source_run_sha256=step.get('run_sha256'))
                    if 'run'in step:
                        self.write(f'cases/{case}/step-{step["ordinal"]}.sh',step['run'].encode())
                        row.update(status='PASS',**self.process(f'cases/{case}/step-{step["ordinal"]}.log',b'entire observed output\n'))
                    elif step['uses']==self.plan['setup_actions']['upload']:
                        policy=self.plan['review_projection']['producers'][case];files=[]
                        if step['ordinal']==policy['upload_ordinal']:
                            names=list(policy['required'])
                            if policy['dynamic']:
                                names.extend('point4-smooth-forward-positive-'+route+'-token-'+kind+'.log'for route in policy['dynamic']['exact_routes']for kind in('stdout','receipt'))
                            if 'opaque_roots'in policy:names.append('local-rebuild/lib/lean/Fixture.olean')
                            for name in names:
                                raw=b'opaque-object\xff\x00'if name.endswith('.olean')else b'entire selected text\n'
                                stored=f'{len(files):06d}.bin';self.write(f'cases/{case}/artifact-{step["ordinal"]}/{stored}',raw)
                                root=runner.expand(policy['root'],**self.expansion)
                                files.append(dict(original_path=root+'/'+name,stored_path=stored,bytes=len(raw),sha256=digest(raw)))
                        metadata=dict(schema='point4-original-upload-selection-v1',original_upload=step,files=files,scope='synthetic')
                        self.write_json(f'cases/{case}/artifact-{step["ordinal"]}/members.json',metadata)
                        row.update(status='PRESERVED_SOURCE_ALLOWLIST',files=len(files),bytes=sum(x['bytes']for x in files))
                    else:row.update(status='COORDINATOR_SETUP_REUSE',action=step['uses'])
                    steps.append(row)
                result=dict(schema='point4-consolidated-case-v1',workflow=workflow['path'],job=job['id'],status='PASS',steps=steps)
                self.coverage['jobs'].append(result);self.write_json(f'cases/{case}/receipt.json',result)
        self.save_coverage()

    def write(self,name,data):
        p=self.evidence/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return p

    def write_json(self,name,value):return self.write(name,canonical(value)+b'\n')
    def save_coverage(self):self.write_json('coverage.json',self.coverage)
    def process(self,name,data):
        self.write(name,data);return dict(exit_code=0,reaped=True,timed_out=False,leaked_group_killed=False,owned_systemd_cleanup=None,bytes=len(data),sha256=digest(data))
    def project(self,**kwargs):
        return runner.project_review_evidence(self.plan,'fifth',self.evidence,self.output,self.expansion,{},time.monotonic()+120,self.binding,**kwargs)
    def artifact(self):return next(self.evidence.glob('cases/point4-weighted-duhamel*/artifact-*/members.json'))

    def test_compact_complete_projection_retains_all_text_and_only_inventories_objects(self):
        value=self.project();self.assertTrue(value['projection_complete']);self.assertTrue(value['stage_execution_passed']);self.assertFalse(value['all_cases_passed'])
        self.assertTrue(value['all_projected_output_hashes_verified']);self.assertFalse(value['original_full_ZIP_locally_hashed'])
        chunks=[row for c in value['inventory_chunks']for row in json.loads((self.output/c['path']).read_bytes())]
        opaque=[r for r in chunks if r['role']=='OPAQUE_ORIGINAL_OBJECT'];self.assertEqual(len(opaque),1)
        self.assertNotIn(opaque[0]['path'],{r['source']for r in value['selected_files']})
        self.assertEqual(len(chunks),value['preserved_inputs']);self.assertTrue((self.output/'review-index.json').is_file())

    def test_compact_missing_payload_is_rejected(self):
        meta=json.loads(self.artifact().read_bytes());(self.artifact().parent/meta['files'][0]['stored_path']).unlink()
        with self.assertRaisesRegex(RuntimeError,'missing payload'):self.project()
        self.assertFalse((self.output/'review-index.json').exists())

    def test_compact_wrong_upload_source_is_rejected(self):
        p=self.artifact();m=json.loads(p.read_bytes());m['original_upload']['with']['path']='/unreviewed/*';p.write_bytes(canonical(m))
        with self.assertRaisesRegex(RuntimeError,'Source join'):self.project()

    def test_compact_unknown_original_member_is_rejected(self):
        p=self.artifact();m=json.loads(p.read_bytes());m['files'][0]['original_path']='/tmp/point4-weighted-hessian-evidence/unreviewed.log';p.write_bytes(canonical(m))
        with self.assertRaisesRegex(RuntimeError,'outside Source upload'):self.project()

    def test_compact_per_producer_size_cap_is_not_replaced_by_bundle_cap(self):
        p=self.artifact();m=json.loads(p.read_bytes());m['files'][0]['bytes']=4*1024**2+1;p.write_bytes(canonical(m))
        with self.assertRaisesRegex(RuntimeError,'per-file cap'):self.project()

    def test_compact_unknown_empty_directory_is_rejected(self):
        (self.evidence/'unreviewed').mkdir()
        with self.assertRaisesRegex(RuntimeError,'Unknown evidence directory'):self.project()

    def test_compact_alias_and_symlink_are_rejected(self):
        self.write('Coverage.json',b'{}')
        with self.assertRaisesRegex(RuntimeError,'case alias'):self.project()
        (self.evidence/'Coverage.json').unlink();(self.evidence/'foreign').symlink_to(self.evidence/'coverage.json')
        with self.assertRaisesRegex(RuntimeError,'Unexpected input symlink'):self.project()

    def test_compact_changed_full_run_script_rejected(self):
        p=next(self.evidence.glob('cases/*/step-*.sh'));p.write_bytes(p.read_bytes()+b'\nfalse\n')
        with self.assertRaisesRegex(RuntimeError,'Source script differs'):self.project()

    def test_compact_changed_raw_log_hash_rejected_without_truncation(self):
        p=next(self.evidence.glob('cases/*/step-*.log'));p.write_bytes(b'mutated actual output\n')
        with self.assertRaisesRegex(RuntimeError,'Runtime log/native receipt'):self.project()
        self.assertFalse((self.output/'review-index.json').exists())

    def test_compact_oversized_runtime_text_fails_before_output(self):
        p=next(self.evidence.glob('cases/*/step-*.log'))
        with p.open('wb')as stream:stream.truncate(16*1024**2+1)
        with self.assertRaisesRegex(RuntimeError,'Oversized selected text'):self.project()
        self.assertFalse(self.output.exists())

    def test_compact_count_bound_fails_before_payload_copy(self):
        folder=self.evidence/'command-receipts';folder.mkdir()
        for i in range(10000):self.write(f'command-receipts/{i}-1.json',b'{}')
        with self.assertRaisesRegex(RuntimeError,'Compact count/raw aggregate'):self.project()
        self.assertFalse(self.output.exists())

    def test_compact_partial_stage_is_diagnostic_not_pair_or_stage_pass(self):
        self.coverage['stage_passed']=False;self.coverage['stopped_after_first_failure']=True;self.coverage['jobs']=self.coverage['jobs'][:1];self.save_coverage()
        value=self.project();self.assertTrue(value['projection_complete']);self.assertFalse(value['stage_execution_passed']);self.assertFalse(value['all_cases_passed'])

    def test_compact_missing_campaign_stage_list_is_rejected(self):
        self.coverage['required_stages'].pop();self.save_coverage()
        with self.assertRaisesRegex(RuntimeError,'Coverage stage/partition join'):self.project()
        self.assertFalse(self.output.exists())

    def test_compact_unclosed_process_or_missing_sourcepost_cannot_pass(self):
        self.coverage['native_initial_full_build']['reaped']=False;self.save_coverage()
        with self.assertRaisesRegex(RuntimeError,'Seed owner'):self.project()
        self.coverage['native_initial_full_build']['reaped']=True;self.save_coverage();self.binding['source_post_valid']=False
        with self.assertRaisesRegex(RuntimeError,'SourcePOST/cache'):self.project()

    def test_compact_deadline_is_global_not_per_file(self):
        with self.assertRaisesRegex(RuntimeError,'deadline'):
            runner.project_review_evidence(self.plan,'fifth',self.evidence,self.output,self.expansion,{},time.monotonic()-1,self.binding)
        self.assertFalse(self.output.exists())

    def test_compact_stream_detects_mutation_and_preserves_binary_bytes(self):
        p=self.root/'raw.bin';p.write_bytes(b'\xff\0whole raw command bytes');seen=[]
        class Capture:
            def write(inner,data):seen.append(data)
        value,_=runner.review_stream(p,time.monotonic()+5,1024,Capture());self.assertEqual(b''.join(seen),p.read_bytes());self.assertEqual(value['sha256'],digest(p.read_bytes()))
        class Mutate:
            def write(inner,data):p.write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError,'changed|grew'):runner.review_stream(p,time.monotonic()+5,1024,Mutate())

    def test_compact_output_nested_under_input_is_rejected(self):
        self.output=self.evidence/'review'
        with self.assertRaisesRegex(RuntimeError,'fresh/separate'):self.project()

    def test_compact_rejects_incomplete_main_dynamic_journal_pairs(self):
        policy=next(p for p in self.plan['review_projection']['producers'].values()if p['dynamic'])
        names=policy['required']+['point4-smooth-forward-positive-'+route+'-token-stdout.log'for route in policy['dynamic']['exact_routes']]
        with self.assertRaisesRegex(RuntimeError,'Incomplete dynamic'):runner.review_producer_names(policy,names,True)

    def test_compact_source_match_does_not_cross_path_components(self):
        self.assertTrue(runner.review_source_match('/tmp/a.log','/tmp/*.log'))
        self.assertFalse(runner.review_source_match('/tmp/foreign/a.log','/tmp/*.log'))
        for bad in('../foreign','/absolute','a\\b','a\0b','a:b'):
            with self.assertRaises(RuntimeError):runner.review_safe_name(bad)

    def test_compact_stale_baseline_proof_identity_is_rejected(self):
        self.binding['proof']=dict(self.binding['proof'],head=self.plan['baseline_master'])
        with self.assertRaisesRegex(RuntimeError,'exact current proof/tooling'):self.project()

    def test_compact_output_inside_source_is_rejected(self):
        self.binding['source_roots']=[str(self.root)]
        with self.assertRaisesRegex(RuntimeError,'outside Source'):self.project()

    def test_compact_full_source_check_failure_cannot_publish_complete_index(self):
        def bad():raise RuntimeError('fresh Source changed')
        with self.assertRaisesRegex(RuntimeError,'fresh Source'):self.project(final_check=bad)
        self.assertFalse((self.output/'review-index.json').exists())

class CurrentHeadIntegrationTests(unittest.TestCase):
    """Current Source identity and exact transport controls; no Git/Lean execution."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.plan=json.loads(Path(__file__).with_name('plan.json').read_bytes())
        self.tool=self.root/'tool';self.execution=self.root/'execution';self.chart=self.root/'chart'
        self.head='a'*40;self.tree='b'*40;self.identity=dict(head=self.head,tree=self.tree,files=2196,catalogue_sha256='c'*64)
        source=Path(__file__).parents[2]
        for workflow in self.plan['workflows']:
            path=self.execution/workflow['path'];path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((source/workflow['path']).read_bytes())
        path='.github/workflows/point4-hamilton-release-audit.yml';(self.execution/path).write_bytes((source/path).read_bytes())

    def test_current_plan_preserves_all_original_workflow_sources_and_full_inverse(self):
        runner.validate_plan(self.plan,self.execution)
        p=self.execution/self.plan['workflows'][0]['path'];p.write_bytes(p.read_bytes()+b'\n# extra Source edit\n')
        with self.assertRaisesRegex(RuntimeError,'Original workflow Source changed'):runner.validate_plan(self.plan,self.execution)

    def test_hamilton_extra_edit_is_not_admitted_by_transport_exception(self):
        path=self.execution/'.github/workflows/point4-hamilton-release-audit.yml';path.write_bytes(path.read_bytes()+b'\n# extra\n')
        with self.assertRaisesRegex(RuntimeError,'Hamilton current Source differs'):runner.validate_current_head_policy(self.plan,self.execution)

    def test_hamilton_wrong_inverse_cannot_be_admitted_by_after_hash_only(self):
        self.plan['current_head_execution']['hamilton_transport']['ordered_single_occurrence_ports'][0]['before']='  not_the_original_dispatch:\n'
        with self.assertRaisesRegex(RuntimeError,'Hamilton full Source inverse differs'):runner.validate_current_head_policy(self.plan,self.execution)

    def test_coordinator_and_bridge_cannot_recurse_into_legacy_job_plan(self):
        self.plan['workflows'][0]['path']='.github/workflows/point4-consolidated.yml'
        with self.assertRaisesRegex(RuntimeError,'recursion'):runner.validate_current_head_policy(self.plan,self.execution)

    def test_current_sources_run_original_current_gate_on_both_real_proof_roots(self):
        with mock.patch.object(runner,'source_identity',return_value=self.identity)as identity,mock.patch.object(runner,'source_guard')as gate:
            actual=runner.current_execution_sources(self.tool,self.execution,self.chart,self.head,self.tree)
        self.assertEqual(actual,(self.identity,self.identity,self.identity))
        self.assertEqual(identity.call_args_list,[mock.call(root,self.head,self.tree)for root in(self.tool,self.execution,self.chart)])
        self.assertEqual(gate.call_args_list,[mock.call(root,'verify_current')for root in(self.execution,self.chart)])

    def test_wrong_proof_head_tree_or_catalogue_is_rejected(self):
        for change in(dict(head='d'*40),dict(tree='e'*40),dict(catalogue_sha256='f'*64)):
            bad=dict(self.identity,**change)
            with mock.patch.object(runner,'source_identity',side_effect=[self.identity,bad,self.identity]),mock.patch.object(runner,'source_guard')as gate:
                with self.assertRaisesRegex(RuntimeError,'catalogue differs'):runner.current_execution_sources(self.tool,self.execution,self.chart,self.head,self.tree)
                gate.assert_not_called()

    def test_external_current_identity_and_separate_roots_are_mandatory(self):
        with self.assertRaisesRegex(RuntimeError,'External current Source identity'):runner.current_execution_sources(self.tool,self.execution,self.chart,'baseline','b'*40)
        with self.assertRaisesRegex(RuntimeError,'Distinct'):runner.current_execution_sources(self.tool,self.tool,self.chart,self.head,self.tree)

    def test_current_source_gate_failure_cannot_be_replaced_by_identity_hashes(self):
        with mock.patch.object(runner,'source_identity',return_value=self.identity),mock.patch.object(runner,'source_guard',side_effect=RuntimeError('original current guard rejects')):
            with self.assertRaisesRegex(RuntimeError,'original current guard rejects'):runner.current_execution_sources(self.tool,self.execution,self.chart,self.head,self.tree)

    def test_stale_baseline_overlay_post_cannot_qualify_current_projection(self):
        policy=self.plan['current_head_execution']
        post=dict(tooling_head=self.head,tooling_tree=self.tree,execution_head=self.head,execution_tree=self.tree,
                  proof_base_head=policy['proof_base_head'],proof_base_tree=policy['proof_base_tree'],
                  all_lean_sources_unchanged=True,legacy_epoch_complete_current_identity_verified=True,index_and_physical_prepost=True)
        self.assertTrue(runner.projection_source_post(post,self.head,self.tree,self.plan))
        for change in(dict(execution_head=policy['proof_base_head']),dict(execution_tree=policy['proof_base_tree']),
                      dict(legacy_epoch_complete_current_identity_verified=False),dict(all_lean_sources_unchanged=False)):
            self.assertFalse(runner.projection_source_post(dict(post,**change),self.head,self.tree,self.plan))


class CanonicalSourceGuardTests(unittest.TestCase):
    """Tiny Source fixtures exercise real canonical imports, never real H/Git."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.oldpath=list(runner.sys.path)
        self.helper_name='point4_smooth_master_composition'
        self.weighted_name='point4_weighted_hessian_release_guard'

    def fixture(self, name, fail=False):
        root=self.root/name;directory=root/'curvature/scripts';directory.mkdir(parents=True)
        helper="import sys\nfrom pathlib import Path\nROOT=Path(__file__).parents[2]\ndef verify_current():\n import point4_smooth_master_composition as own\n import point4_weighted_hessian_release_guard as weighted\n assert own is sys.modules[__name__] and weighted.owner is own\n"
        helper += " raise RuntimeError('fixture current verifier failure')\n" if fail else " return str(ROOT)\n"
        (directory/'point4_smooth_master_composition.py').write_text(helper)
        (directory/'point4_weighted_hessian_release_guard.py').write_text('import point4_smooth_master_composition as owner\n')
        return root

    def assert_clean(self):
        self.assertNotIn(self.helper_name,runner.sys.modules);self.assertNotIn(self.weighted_name,runner.sys.modules)
        self.assertEqual(runner.sys.path,self.oldpath)

    def test_canonical_self_and_weighted_import_share_exact_owned_module(self):
        root=self.fixture('one')
        self.assertEqual(runner.source_guard(root,'verify_current'),str(root));self.assert_clean()

    def test_two_execution_roots_do_not_reuse_previous_guard_or_leaf_globals(self):
        for name in('shared','chart','tooling'):
            root=self.fixture(name)
            self.assertEqual(runner.source_guard(root,'verify_current'),str(root));self.assert_clean()

    def test_failed_current_guard_cleans_canonical_and_owned_companions(self):
        root=self.fixture('failing',fail=True)
        with self.assertRaisesRegex(RuntimeError,'fixture current verifier failure'):runner.source_guard(root,'verify_current')
        self.assert_clean()

    def test_preloaded_canonical_guard_rejected_without_mutating_foreign_owner(self):
        root=self.fixture('foreign');foreign=runner.types.ModuleType(self.helper_name)
        with mock.patch.dict(runner.sys.modules,{self.helper_name:foreign}):
            with self.assertRaisesRegex(RuntimeError,'Foreign/preloaded'):runner.source_guard(root,'verify_current')
            self.assertIs(runner.sys.modules[self.helper_name],foreign)
        self.assert_clean()

    def test_preexisting_unrelated_module_binding_and_path_survive(self):
        root=self.fixture('preserve');name='point4_unrelated_fixture_sentinel';sentinel=runner.types.ModuleType(name)
        sentinel.__file__=str(root/'preexisting.py')
        with mock.patch.dict(runner.sys.modules,{name:sentinel}):
            self.assertEqual(runner.source_guard(root,'verify_current'),str(root));self.assert_clean()
            self.assertIs(runner.sys.modules[name],sentinel)


if __name__=='__main__':
    unittest.main()
