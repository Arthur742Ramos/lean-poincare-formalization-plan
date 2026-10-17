#!/usr/bin/env python3
"""Run Source-frozen legacy Point-4 cases serially with a shared native build.

This is a new consolidated protocol. It does not create historical workflow
statuses, qualify new mathematical statements, or infer success from cache hits.
"""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import glob
import importlib.util
import json
import os
import pwd
from pathlib import Path
import re
import shutil
import signal
import selectors
import stat
import subprocess
import sys
import time
import types

from identity import canonical, digest, regular, require, source_identity, strict_json, toolchain_identity, OutputBudget, output_budget

MAX_LOG = 512 * 1024 * 1024
MAX_ARCHIVE_FILE = 1024 * 1024 * 1024
MAX_ARCHIVE_TOTAL = 16 * 1024 * 1024 * 1024
MAX_ARCHIVE_FILES = 100000
MAX_EVIDENCE_BYTES = 24 * 1024 * 1024 * 1024
MAX_EVIDENCE_ENTRIES = 300000


def write_json(path, value):
    with output_budget().file(path) as handle:
        handle.write(canonical(value) + b'\n')


def expand(value, sha, tree, runner_temp, event):
    """No eval or generic expression engine: known Source expressions only."""
    if not isinstance(value, str):
        return str(value)
    literals = {
        '${{ github.event.pull_request.head.sha || github.sha }}': sha,
        '${{ github.event.pull_request.head.sha || inputs.candidate_sha }}': sha,
        '${{ inputs.expected_tree }}': tree,
        '${{ github.event_name }}': event,
        '${{ runner.temp }}': runner_temp,
        '${{ github.run_attempt }}': os.environ.get('GITHUB_RUN_ATTEMPT', '1'),
    }
    for before, after in literals.items():
        value = value.replace(before, after)
    require('${{' not in value, 'Unsupported Source expression')
    return value


def _bounded_proc(path,maximum):
    with Path(path).open('rb') as handle:
        raw=handle.read(maximum+1)
    require(len(raw)<=maximum,'Owned process metadata exceeded')
    return raw


def _group_empty(group):
    path=Path('/sys/fs/cgroup')/group.lstrip('/')
    if not path.exists():return True
    require(path.is_dir() and not path.is_symlink(),'Owned cgroup alias')
    raw=_bounded_proc(path/'cgroup.events',2048)
    return b'populated 0' in raw.splitlines()


def process_owner(pid,spec,group):
    require(type(pid)is int and pid>0,'Invalid owned MainPID')
    base=Path('/proc')/str(pid)
    before=_bounded_proc(base/'stat',65536)
    start=before.rsplit(b')',1)[1].split()[19]
    argv=_bounded_proc(base/'cmdline',65536).split(b'\0')
    require(argv[-1]==b'','Incomplete owned argv');argv=argv[:-1]
    require(argv==[value.encode()for value in spec['argv']],'Owned process full argv differs')
    require(str((base/'exe').resolve(strict=True))==spec['executable'],'Owned executable differs')
    require(str((base/'cwd').resolve(strict=True))==spec['root'],'Owned process cwd differs')
    status=_bounded_proc(base/'status',65536)
    uid_lines=[line for line in status.splitlines()if line.startswith(b'Uid:')]
    require(len(uid_lines)==1 and all(int(x)==os.getuid()for x in uid_lines[0].split()[1:]),'Owned process UID differs')
    cgroup=_bounded_proc(base/'cgroup',65536)
    require(cgroup.splitlines()==[b'0::'+group.encode()],'Owned process cgroup differs')
    after=_bounded_proc(base/'stat',65536)
    require(after.rsplit(b')',1)[1].split()[19]==start,'Owned PID identity changed')
    cg=Path('/sys/fs/cgroup')/group.lstrip('/')
    st=cg.stat()
    return dict(pid=pid,start_ticks=start.decode(),argv=spec['argv'],executable=spec['executable'],
                uid=os.getuid(),cwd=spec['root'],cgroup=group,cgroup_dev=st.st_dev,cgroup_ino=st.st_ino)


def owned_unit_snapshot(spec,inspect_process=True):
    unit=spec['unit']
    require(re.fullmatch(r'chart-port-[0-9]+-[0-9]+\.service',unit),'Unexpected owned unit')
    properties=['Id','LoadState','ActiveState','SubState','Job','User','WorkingDirectory','InvocationID','MainPID','ControlGroup']
    result=subprocess.run(['systemctl','show',unit,'--property='+','.join(properties)],
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
    require(len(result.stdout)<=16384 and len(result.stderr)<=16384,'Owned unit metadata bound exceeded')
    values=dict(line.split('=',1)for line in result.stdout.decode().splitlines()if '='in line)
    if values.get('LoadState')=='not-found':return None
    require(result.returncode==0 and values.get('Id')==unit,'Cannot authenticate exact owned unit')
    require(values.get('WorkingDirectory')==spec['root'],'Owned unit cwd differs')
    require(values.get('User')in(str(os.getuid()),pwd.getpwuid(os.getuid()).pw_name),'Owned unit uid differs')
    require(re.fullmatch(r'[0-9a-f]{32}',values.get('InvocationID','')),'Owned invocation missing')
    group=values.get('ControlGroup','')
    require(group in ('','/system.slice/'+unit),'Unexpected owned cgroup identity')
    pid=int(values.get('MainPID','0'))
    values['owner']=process_owner(pid,spec,group)if pid and inspect_process else None
    return values


def terminal_unit(values):
    return (values is None or (values.get('ActiveState')in('inactive','failed') and
            values.get('SubState')in('dead','failed') and values.get('Job')in('','0','0 /')))


def queued_unit_config(spec):
    """Exact typed D-Bus argv, including a service not yet visible in /proc."""
    label=''.join(ch if ch.isascii()and ch.isalnum() else '_'+format(ord(ch),'02x')for ch in spec['unit'])
    result=subprocess.run(['busctl','--json=short','get-property','org.freedesktop.systemd1',
        '/org/freedesktop/systemd1/unit/'+label,'org.freedesktop.systemd1.Service','ExecStart'],
        stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
    require(result.returncode==0 and len(result.stdout)<=16384 and len(result.stderr)<=16384,'Cannot read bounded owned ExecStart')
    value=strict_json(result.stdout)
    require(type(value)is dict and set(value)=={'type','data'} and value['type']=='a(sasbttttuii)', 'Unknown ExecStart schema')
    rows=value['data']
    require(type(rows)is list and len(rows)==1 and type(rows[0])is list and len(rows[0])==10,'Unexpected ExecStart command inventory')
    row=rows[0]
    require(type(row[0])is str and type(row[1])is list and all(type(x)is str for x in row[1])
            and row[2]is False and all(type(x)is int and x>=0 for x in row[3:8])
            and all(type(x)is int for x in row[8:]),'Malformed ExecStart fields')
    require(row[0]==spec['argv'][0] and str(Path(row[0]).resolve())==spec['executable']
            and row[1]==spec['argv'],'Queued owned executable/full argv differs')
    return dict(executable=spec['executable'],argv=spec['argv'],config_sha256=digest(canonical(value)))


def cleanup_owned_unit(spec,observed):
    """Refresh ownership through cancellation and prove every owned group empty."""
    state=dict(binding=observed,owner=(observed or {}).get('owner'),groups={})
    queued=None
    def refresh():
        nonlocal queued
        values=owned_unit_snapshot(spec,inspect_process=False)
        binding=state['binding']
        if binding is not None and values is not None:
            require(values['InvocationID']==binding['InvocationID'],'Owned invocation changed during teardown')
        if values is not None:
            if binding is None:state['binding']=values
            observed_group=values.get('ControlGroup','')
            if observed_group:state['groups'].setdefault(observed_group,None)
            if values.get('MainPID','0')!='0':
                try:
                    fresh=owned_unit_snapshot(spec)
                except FileNotFoundError:
                    # The exact observed PID may exit between manager and /proc.
                    # Authenticate the still-owned service config, then reread it.
                    queued=queued_unit_config(spec)
                    fresh=owned_unit_snapshot(spec,inspect_process=False)
                require(fresh is None or fresh['InvocationID']==values['InvocationID'],
                        'Owned invocation changed during owner refresh')
                values=fresh
                if values is not None and values.get('owner')is not None:
                    state['owner']=values['owner']
            group=(values or {}).get('ControlGroup','')
            if group:state['groups'].setdefault(group,None)
        owner=state['owner']
        if owner is not None:
            group=owner['cgroup'];identity=(owner['cgroup_dev'],owner['cgroup_ino'])
            previous=state['groups'].get(group)
            require(previous is None or previous==identity,'Owned cgroup inode changed')
            state['groups'][group]=identity
        for group,identity in state['groups'].items():
            cg=Path('/sys/fs/cgroup')/group.lstrip('/')
            if identity is not None and cg.exists():
                st=cg.stat();require((st.st_dev,st.st_ino)==identity,'Owned cgroup inode replaced')
        return values
    def empty():
        return all(_group_empty(group)for group in state['groups'])
    # Preserve a previously seen group even if the manager later clears it.
    old_group=(observed or {}).get('ControlGroup','')
    if old_group:state['groups'][old_group]=None
    values=refresh()
    if terminal_unit(values)and empty():
        return dict(unit=spec['unit'],confirmed_empty=True,confirmed_terminal=True,stop_requested=False,force_kill=False)
    binding=state['binding']
    require(binding is not None,'Missing owned unit identity')
    if state['owner']is None:
        require(values is not None,'Cannot authenticate absent nonempty owned unit')
        queued=queued_unit_config(spec)
        values=refresh()
        require(values is not None,'Queued owned unit disappeared before cancellation')
    failures=[];forced=False
    try:
        result=subprocess.run(['sudo','-n','systemctl','stop','--',spec['unit']],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
        if result.returncode:failures.append('stop_exit_'+str(result.returncode))
    except Exception as error:
        failures.append('stop_'+type(error).__name__)
    finally:
        current=refresh()
        if current is not None and not terminal_unit(current):
            try:
                retry=subprocess.run(['sudo','-n','systemctl','stop','--',spec['unit']],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
                if retry.returncode:failures.append('cancel_exit_'+str(retry.returncode))
            except Exception as error:failures.append('cancel_'+type(error).__name__)
        deadline=time.monotonic()+10
        # Refresh AFTER the retry and on every poll: a queued service can become
        # live during either stop. Never use a stale empty cgroup for teardown.
        while True:
            final=refresh()
            if terminal_unit(final)and empty():break
            populated=not empty()
            if populated:
                require(final is not None,'Cannot authenticate exact unit before force kill')
                if state['owner']is None:queued=queued_unit_config(spec)
                # A final manager refresh binds every unit-addressed kill to the
                # same invocation/config, retaining all previously seen groups.
                final=refresh()
                require(final is not None and final['InvocationID']==binding['InvocationID'],
                        'Owned invocation changed before force kill')
                forced=True
                try:
                    killed=subprocess.run(['sudo','-n','systemctl','kill','--signal=SIGKILL','--kill-who=all','--',spec['unit']],
                                          stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=5)
                    if killed.returncode:failures.append('kill_exit_'+str(killed.returncode))
                except Exception as error:failures.append('kill_'+type(error).__name__)
            require(time.monotonic()<deadline,
                    'Owned unit not terminal/unqueued/empty after bounded teardown: '+','.join(failures))
            time.sleep(.1)
    return dict(unit=spec['unit'],invocation_id=binding['InvocationID'],confirmed_empty=True,confirmed_terminal=True,
                stop_requested=True,force_kill=forced,queued_config=queued,teardown_diagnostics=failures)


def run_process(argv,cwd,env,log,timeout,owned_systemd=None):
    """PIPE output is reserved before each bounded write; teardown is finally."""
    require(timeout>0,'Original job time budget exhausted')
    started=time.monotonic();unit_seen=None;last_unit_poll=0;child=None
    timed_out=False;leaked=False;unit_cleanup=None;failure=None;code=None;total=0
    if owned_systemd is not None:
        require(owned_unit_snapshot(owned_systemd)is None,'Owned unit already exists before launch')
    interrupted={}
    def stop(signum,frame):raise InterruptedError('Consolidated runner interrupted')
    for signum in(signal.SIGTERM,signal.SIGINT):
        interrupted[signum]=signal.getsignal(signum);signal.signal(signum,stop)
    try:
        with output_budget().file(log,MAX_LOG)as handle:
            child=subprocess.Popen(argv,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
            with selectors.DefaultSelector()as poll:
                poll.register(child.stdout,selectors.EVENT_READ)
                while poll.get_map()or child.poll()is None:
                    now=time.monotonic()
                    if owned_systemd is not None and (unit_seen is None or unit_seen.get('owner')is None)and now-last_unit_poll>=.5:
                        candidate=owned_unit_snapshot(owned_systemd)
                        if candidate is not None:unit_seen=candidate
                        last_unit_poll=now
                    if now-started>=timeout:
                        timed_out=True;raise TimeoutError('Original step/job/global deadline reached')
                    for key,_ in poll.select(timeout=.1):
                        data=os.read(key.fileobj.fileno(),65536)
                        if not data:poll.unregister(key.fileobj);key.fileobj.close();continue
                        require(total+len(data)<=MAX_LOG,'Source step log bound exceeded')
                        handle.write(data);total+=len(data)
            code=child.wait(timeout=5)
    except BaseException as error:
        failure=error
    finally:
        # Even wait/stop/output/timeout exceptions cannot bypass owned teardown.
        if child is not None:
            try:
                os.killpg(child.pid,0);leaked=child.poll()is not None
                os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            try:
                code=child.wait(timeout=10)
            except Exception as error:
                failure=failure or error
            if child.stdout is not None and not child.stdout.closed:child.stdout.close()
            if owned_systemd is not None:
                try:unit_cleanup=cleanup_owned_unit(owned_systemd,unit_seen)
                except Exception as error:failure=failure or error
        for signum,handler in interrupted.items():signal.signal(signum,handler)
    if failure is not None:
        raise RuntimeError(json.dumps(dict(error=type(failure).__name__,message=str(failure),
                          timed_out=timed_out,reaped=child is None or child.poll()is not None,
                          owned_unit_cleanup=unit_cleanup),sort_keys=True))from failure
    raw=regular(log,MAX_LOG)
    return dict(exit_code=code,timed_out=timed_out,reaped=child.poll()is not None,
                leaked_group_killed=leaked,owned_systemd_cleanup=unit_cleanup,
                elapsed_seconds=time.monotonic()-started,bytes=len(raw),sha256=digest(raw),log=log.name)


def validate_current_head_policy(plan, execution):
    """Only the reviewed current tooling commit may execute original validators."""
    policy=plan.get('current_head_execution')
    require(type(policy)is dict and policy.get('schema')=='point4-exact-current-toolhead-execution-v1'
            and policy.get('expected_identity')=='external-tooling-head-and-tree-only'
            and policy.get('proof_base_head')=='5d1b3e2c123a8bdfd036a0e4d8495586c4a6d1b9'
            and policy.get('proof_base_tree')=='8081325e22bc0314d6106a311f92606e7e03f9d3'
            and plan['baseline_master']==policy['proof_base_head'],'Current HEAD execution policy differs')
    require(policy.get('excluded_from_legacy_jobs')==['.github/workflows/point4-consolidated.yml','.github/workflows/point4-hamilton-release-audit.yml']
            and not set(policy['excluded_from_legacy_jobs'])&{w['path']for w in plan['workflows']},'Coordinator/transport recursion into original jobs')
    transport=policy['hamilton_transport'];path='.github/workflows/point4-hamilton-release-audit.yml'
    require(transport['path']==path and transport['before']==dict(bytes=14836,sha256='1d8849f98be74899334bedc94ed68c46b1270c420e9454f66a27d28e791d4c2d')
            and transport['after']==dict(bytes=15305,sha256='6f8bd895146f718953e1d47b089d4d6e11aaf9d424bee9e727f3a54972162311'),'Hamilton exact Source epoch differs')
    raw=regular(execution/path);require(len(raw)==transport['after']['bytes']and digest(raw)==transport['after']['sha256'],'Hamilton current Source differs')
    append=transport['append_exact'].encode();require(append and raw.endswith(append),'Hamilton exact caller suffix differs');restored=raw[:-len(append)]
    ports=transport['ordered_single_occurrence_ports'];require(len(ports)==2 and all(port['occurrences']==1 for port in ports),'Hamilton finite ports differ')
    for port in reversed(ports):
        after=port['after'].encode();require(after and restored.count(after)==1,'Hamilton inverse port ambiguity');restored=restored.replace(after,port['before'].encode(),1)
    require(len(restored)==transport['before']['bytes']and digest(restored)==transport['before']['sha256'],'Hamilton full Source inverse differs')
    review=plan['review_projection']
    require(review.get('execution_identity')==policy['expected_identity']and review.get('proof_reference_head')==policy['proof_base_head']
            and review.get('proof_reference_tree')==policy['proof_base_tree'],'Projection execution policy differs')
    return policy


def current_execution_sources(tooling, execution, chart, expected_sha, expected_tree):
    require(re.fullmatch('[0-9a-f]{40}',expected_sha or'')and re.fullmatch('[0-9a-f]{40}',expected_tree or''),'External current Source identity required')
    require(len({str(root)for root in(tooling,execution,chart)})==3,'Distinct actual current Source roots required')
    tool=source_identity(tooling,expected_sha,expected_tree)
    proof=source_identity(execution,expected_sha,expected_tree);chart_source=source_identity(chart,expected_sha,expected_tree)
    require(tool==proof==chart_source,'Current proof/tooling Source catalogue differs')
    source_guard(execution,'verify_current');source_guard(chart,'verify_current')
    return tool,proof,chart_source


def projection_source_post(post, expected_sha, expected_tree, plan):
    policy=plan['current_head_execution']
    return(post.get('tooling_head')==expected_sha and post.get('tooling_tree')==expected_tree
           and post.get('execution_head')==expected_sha and post.get('execution_tree')==expected_tree
           and post.get('proof_base_head')==policy['proof_base_head']and post.get('proof_base_tree')==policy['proof_base_tree']
           and post.get('all_lean_sources_unchanged')is True and post.get('legacy_epoch_complete_current_identity_verified')is True
           and post.get('index_and_physical_prepost')is True)


def validate_plan(plan, execution):
    require(plan['schema'] == 'point4-consolidated-source-plan-v1', 'Wrong plan schema')
    require(len(plan['workflows']) == plan['workflow_count'] == 33, '33 workflow coverage differs')
    workflows, jobs, runs = set(), set(), 0
    for workflow in plan['workflows']:
        path = workflow['path']
        require(path not in workflows and path.startswith('.github/workflows/') and path.endswith('.yml'), 'Workflow identity differs')
        workflows.add(path)
        require(digest(regular(execution / path)) == workflow['sha256'], 'Original workflow Source changed; new review required')
        for job in workflow['jobs']:
            key = (path, job['id'])
            require(key not in jobs, 'Duplicate job')
            jobs.add(key)
            for ordinal, step in enumerate(job['steps'], 1):
                require(step['ordinal'] == ordinal, 'Source step ordering differs')
                require(('run' in step) != ('uses' in step), 'Malformed Source step')
                if 'run' in step:
                    runs += 1
                    require(digest(step['run'].encode()) == step['run_sha256'], 'Literal Run body differs')
                    require(step.get('if', 'success()') in ('success()', 'always()'), 'Unsupported Source conditional')
                else:
                    require(step['uses'] in plan['setup_actions'].values(), 'Action outside explicit setup contract')
    require(len(jobs) == plan['job_count'] == 35 and runs == plan['run_step_count'] == 216, 'Complete job/Run coverage differs')
    stage_partition(plan, 'first')
    stage_partition(plan, 'second')
    validate_current_head_policy(plan, execution)


def stage_partition(plan, stage):
    require(stage in ('first','second'), 'Unknown execution stage')
    expected_second={'.github/workflows/point4-'+name+'.yml'for name in (
        'weighted-duhamel-hessian','c2-resonance','smooth-forward-support','local-chart-connection')}
    partition=plan.get('stages')
    require(type(partition)is dict and set(partition)=={'schema','first','second'}
            and partition['schema']=='point4-two-stage-partition-v1','Wrong finite stage partition')
    full=[workflow['path']for workflow in plan['workflows']]
    require(len(full)==33 and len(set(full))==33,'Full workflow partition differs')
    for name in ('first','second'):
        rows=partition[name]
        require(type(rows)is list and all(type(row)is str for row in rows)
                and len(rows)==len(set(rows)), 'Duplicate or malformed stage rows')
        expected=[path for path in full if (path in expected_second)==(name=='second')]
        require(rows==expected,'Stage must preserve exact complete workflow assignment')
    require(set(partition['first']).isdisjoint(partition['second'])
            and set(partition['first'])|set(partition['second'])==set(full), 'Stage partition is not disjoint and complete')
    counts={name:sum(len(w['jobs'])for w in plan['workflows']if w['path']in partition[name])for name in ('first','second')}
    require(counts=={'first':30,'second':5}, 'Stage job partition differs')
    assigned=[w for w in plan['workflows']if w['path']in partition[stage]]
    return dict(stage=stage,partition=partition,partition_sha256=digest(canonical(partition)),
                assigned_workflow_count=len(assigned),assigned_job_count=counts[stage],
                assigned_run_count=sum('run'in step for w in assigned for job in w['jobs']for step in job['steps']),
                workflows=assigned)


def stage_outcome(assignment,results,stopped):
    expected=[(w['path'],j['id'])for w in assignment['workflows']for j in w['jobs']]
    actual=[(row['workflow'],row['job'])for row in results]
    require(len(actual)==len(set(actual)) and all(key in expected for key in actual),
            'Stage result contains duplicate or foreign cases')
    # A preflight failure may be the only receipt and occur after earlier
    # unfinished prefixes; successful completion must match every assigned case.
    passed=not stopped and actual==expected and all(row['status']=='PASS'for row in results)
    return dict(stage=assignment['stage'],partition_sha256=assignment['partition_sha256'],
                stage_passed=passed,all_cases_passed=False,
                pair_join_required=True,coverage_scope='ASSIGNED_STAGE_ONLY',
                assigned_workflow_count=assignment['assigned_workflow_count'],
                assigned_job_count=assignment['assigned_job_count'],
                assigned_run_count=assignment['assigned_run_count'])


def compiled_cache_provenance(raw,stage,proof,toolchain,provider):
    require(stage in ('first','second'), 'Unknown cache consumer stage')
    state=strict_json(raw)
    require(type(state)is dict and state.get('restore_complete')is True
            and type(state.get('cache_hit'))is bool and type(state.get('restored_bytes'))is int
            and 0<=state['restored_bytes']<=8*1024**3,'Incomplete cache restore provenance')
    identity=state.get('identity')
    require(type(identity)is dict and identity.get('schema')=='point4-exact-candidate-cache-v1'
            and identity.get('head')==proof['head'] and identity.get('tree')==proof['tree']
            and identity.get('compiler_version')==toolchain['version']
            and identity.get('compiler_binary_sha256')==toolchain['compiler_sha256']
            and identity.get('targets')==['PoincareCurvature'],'Cache candidate/compiler/targets differ')
    expected_provider={name:provider.get(name,'')for name in (
        'GITHUB_REPOSITORY','GITHUB_REF','GITHUB_WORKFLOW_REF','GITHUB_WORKFLOW_SHA')}
    require(all(expected_provider.values())and identity.get('provider_scope')==expected_provider,
            'Cache tooling provider provenance differs')
    expected_key='point4-candidate-v1-'+digest(json.dumps(identity,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode())
    require(state.get('key')==expected_key,'Cache exact identity key differs')
    require(state['cache_hit']or state['restored_bytes']==0,'Cache miss reports restored bytes')
    require(stage!='second'or(state['cache_hit']and state['restored_bytes']>0),
            'Second stage requires verified exact cache hit; cold fallback forbidden')
    return dict(state_sha256=digest(raw),state_bytes=len(raw),key=expected_key,
                restore_complete=True,cache_hit=state['cache_hit'],restored_bytes=state['restored_bytes'],
                stage=stage,cache_writer_allowed=stage=='first',
                second_stage_read_only_enforced_by_coordinator=stage=='second',
                identity=identity,proof_credit=0)


def source_guard(root, function, *args):
    """Fresh canonical H ownership, including its exact imported companions."""
    path = root / ('scripts/point4_tooling_overlay.py' if function == 'verify_tooling_overlay'
                   else 'curvature/scripts/point4_smooth_master_composition.py')
    name = 'point4_tooling_overlay' if function == 'verify_tooling_overlay' else 'point4_smooth_master_composition'
    require(name not in sys.modules, 'Foreign/preloaded canonical Source guard')
    raw = regular(path, 8 * 1024 * 1024)
    previous_path, previous_modules = list(sys.path), dict(sys.modules)
    module = types.ModuleType(name)
    module.__file__, module.__package__ = str(path), None
    sys.path.insert(0, str(path.parent))
    sys.modules[name] = module
    try:
        # Execute the same sealed physical bytes, never a bytecode cache. H and
        # weighted/leaf bootstraps must resolve their own canonical module.
        exec(compile(raw, str(path), 'exec', dont_inherit=True), module.__dict__)
        result = getattr(module, function)(*args)
        require(sys.modules.get(name) is module and regular(path, 8 * 1024 * 1024) == raw,
                'Source guard module/physical POST drift')
        return result
    finally:
        sys.path[:] = previous_path
        for imported_name in tuple(set(sys.modules) - set(previous_modules)):
            imported = sys.modules.get(imported_name)
            location = getattr(imported, '__file__', None)
            if imported_name == name or (type(location) is str and Path(location).is_absolute()
                                        and Path(location).is_relative_to(root)):
                del sys.modules[imported_name]
        # Preserve all preexisting modules exactly; never leave a candidate's
        # replacement or deletion installed after an exception.
        for imported_name, original in previous_modules.items():
            sys.modules[imported_name] = original


def preserve_artifacts(step, context, directory, counters):
    """Retain original upload allowlists; no object/proof-credit inference."""
    paths = step.get('with', {}).get('path', '')
    matches, rows = set(), []
    for pattern in paths.splitlines():
        require(time.monotonic() < context['deadline'], 'Overall deadline reached during artifact preservation')
        pattern = expand(pattern, **context['expansion'])
        if not pattern:
            continue
        full = Path(pattern) if Path(pattern).is_absolute() else context['execution'] / pattern
        # glob expansion is explicitly bounded by the original source allowlists;
        # cap names during traversal, rather than materializing recursive glob.
        for name in glob.iglob(str(full), recursive=True):
            require(time.monotonic() < context['deadline'], 'Artifact traversal deadline reached')
            require(len(matches) < MAX_ARCHIVE_FILES, 'Artifact namespace count exceeded')
            path = Path(name)
            if path.is_dir() and not path.is_symlink():
                for parent, dirs, files in os.walk(path, followlinks=False):
                    counters['namespace_entries'] += len(dirs) + len(files)
                    require(counters['namespace_entries'] <= 2 * MAX_ARCHIVE_FILES, 'Artifact traversal bound exceeded')
                    for item in dirs:
                        require(not (Path(parent) / item).is_symlink(), 'Artifact directory symlink')
                    for item in files:
                        require(len(matches) < MAX_ARCHIVE_FILES, 'Artifact namespace count exceeded')
                        matches.add(str(Path(parent) / item))
            else:
                matches.add(str(path))
    if not matches:
        require(step.get('with', {}).get('if-no-files-found', 'warn') != 'error', 'Required artifact allowlist empty')
    output_budget().mkdir(directory)
    for index, name in enumerate(sorted(matches)):
        require(time.monotonic() < context['deadline'], 'Artifact copy deadline reached')
        path = Path(name).absolute()
        raw = regular(path, MAX_ARCHIVE_FILE)
        counters['bytes'] += len(raw)
        counters['files'] += 1
        require(counters['bytes'] <= MAX_ARCHIVE_TOTAL and counters['files'] <= MAX_ARCHIVE_FILES, 'Whole evidence bound exceeded')
        target = directory / f'{index:06d}.bin'
        with output_budget().file(target,MAX_ARCHIVE_FILE) as handle:
            handle.write(raw)
        rows.append(dict(original_path=str(path), stored_path=target.name, bytes=len(raw), sha256=digest(raw)))
    write_json(directory / 'members.json', dict(schema='point4-original-upload-selection-v1',
               original_upload=step, files=rows, scope='Source-selected artifact files; opaque preservation, not semantic validation'))
    return dict(files=len(rows), bytes=sum(r['bytes'] for r in rows))


def evidence_usage(context):
    total, count = 0, 0
    root = context['evidence']
    for parent, dirs, files in os.walk(root, followlinks=False):
        require(time.monotonic() < context['deadline'], 'Overall evidence deadline reached')
        count += len(dirs) + len(files)
        require(count <= MAX_EVIDENCE_ENTRIES, 'Total evidence namespace exceeded')
        for name in dirs:
            require(not (Path(parent) / name).is_symlink(), 'Evidence directory alias')
        for name in files:
            path = Path(parent) / name
            if path.is_symlink():
                require(path.parent == root / 'bin' and name in ('bash', 'lake') and
                        path.resolve() == context['tooling'] / 'scripts/point4_ci/command_broker.py', 'Unexpected evidence alias')
                continue
            st = path.lstat()
            require(stat.S_ISREG(st.st_mode), 'Nonregular evidence output')
            total += st.st_size
            require(total <= MAX_EVIDENCE_BYTES, 'Total evidence byte bound exceeded')
    return dict(entries=count, bytes=total)


def step_budget(step, job, state, context):
    limit = step.get('timeout-minutes', job['timeout_minutes'])
    require(type(limit) is int and 0 < limit <= 360, 'Unsupported Source step budget')
    return min(limit * 60, job['timeout_minutes'] * 60 - state['active_seconds'],
               context['deadline'] - time.monotonic())


def prepare_case(workflow, job, context):
    case = workflow['path'].removeprefix('.github/workflows/').removesuffix('.yml') + '--' + job['id']
    directory = context['evidence'] / 'cases' / case
    output_budget().mkdir(directory)
    env = dict(context['env'])
    for mapping in (workflow.get('env', {}), job.get('env', {})):
        env.update({k: expand(v, **context['expansion']) for k, v in mapping.items()})
    env['P4_CI_CASE'] = case
    if workflow['path'] == '.github/workflows/point4-local-chart-connection.yml':
        # systemd forwards PATH but deliberately not the P4 broker context.
        # Every mandatory chart/bootstrap stage therefore uses only real tools.
        env['PATH'] = context['real_path']
    return dict(case=case, directory=directory, env=env, next_step=0, failed=False,
                active_seconds=0.0, records=[], complete=False)


def execute_job(workflow, job, context, state, preflight_only=False):
    defaults = {**workflow.get('defaults', {}).get('run', {}), **job.get('defaults', {}).get('run', {})}
    while state['next_step'] < len(job['steps']):
        step = job['steps'][state['next_step']]
        if preflight_only and step.get('uses') == context['plan']['setup_actions']['lean']:
            break
        state['next_step'] += 1
        number = step['ordinal']
        entry = dict(ordinal=number, name=step.get('name'), source_run_sha256=step.get('run_sha256'),
                     phase='SOURCE_PREFLIGHT' if preflight_only else 'NATIVE_AND_GUARDS')
        always = step.get('if') == 'always()'
        if state['failed'] and not always:
            entry['status'] = 'SKIPPED_AFTER_FAILURE'; state['records'].append(entry); continue
        evidence_usage(context)
        active_start = time.monotonic()
        if 'uses' in step:
            action = step['uses']
            if action == context['plan']['setup_actions']['upload']:
                try:
                    require(step_budget(step, job, state, context) > 0, 'Artifact budget exhausted')
                    artifact_context = dict(context)
                    artifact_context['deadline'] = min(context['deadline'], time.monotonic() + step_budget(step, job, state, context))
                    result = preserve_artifacts(step, artifact_context, state['directory'] / f'artifact-{number}', context['counters'])
                    entry.update(status='PRESERVED_SOURCE_ALLOWLIST', **result)
                except Exception as error:
                    entry.update(status='FAIL', error=str(error)); state['failed'] = True
            else:
                entry.update(status='COORDINATOR_SETUP_REUSE', action=action)
            state['active_seconds'] += time.monotonic() - active_start
            state['records'].append(entry); continue
        step_env = dict(state['env'])
        step_env.update({k: expand(v, **context['expansion']) for k, v in step.get('env', {}).items()})
        step_env['P4_CI_STEP'] = str(number)
        shell = step.get('shell', defaults.get('shell'))
        require(shell in (None, 'bash'), 'Unsupported Source shell')
        cwd = context['execution'] / step.get('working-directory', defaults.get('working-directory', '.'))
        require(cwd.resolve().is_relative_to(context['execution']), 'Source cwd escapes execution view')
        script = state['directory'] / f'step-{number}.sh'
        with output_budget().file(script,16*1024*1024) as handle:
            handle.write(step['run'].encode())
        argv = [context['real_bash']]
        argv += ['--noprofile', '--norc', '-e', '-o', 'pipefail'] if shell == 'bash' else ['-e']
        argv.append(str(script))
        owned = None
        if workflow['path'] == '.github/workflows/point4-local-chart-connection.yml' and 'sudo systemd-run' in step['run']:
            run_id, attempt = step_env.get('GITHUB_RUN_ID', ''), step_env.get('GITHUB_RUN_ATTEMPT', '')
            require(re.fullmatch('[0-9]{1,20}', run_id) and re.fullmatch('[0-9]{1,6}', attempt), 'Owned unit provider identity missing')
            owned = dict(unit=f'chart-port-{run_id}-{attempt}.service', root=str(context['execution']),
                         executable=str(Path('/usr/bin/python3').resolve()),
                         argv=['/usr/bin/python3','curvature/scripts/chart_port_ci.py',
                               '--expected-sha',context['expansion']['sha'],'--expected-tree',context['expansion']['tree'],
                               '--evidence',str(Path(step_env['RUNNER_TEMP'])/('local-chart-connection-'+context['expansion']['sha']))])
        try:
            result = run_process(argv, cwd, step_env, state['directory'] / f'step-{number}.log',
                                 step_budget(step, job, state, context), owned_systemd=owned)
            entry.update(status='PASS' if result['exit_code'] == 0 and not result['timed_out']
                         and not result['leaked_group_killed'] else 'FAIL', **result)
        except Exception as error:
            entry.update(status='FAIL', error=str(error))
        state['active_seconds'] += time.monotonic() - active_start
        if entry['status'] == 'FAIL':
            state['failed'] = True
        state['records'].append(entry)
        if state['failed'] and preflight_only:
            break
    if preflight_only and not state['failed']:
        return None
    # On the first definite failure, retain only this case's original always()
    # diagnostics/artifacts; no later native command or workflow is dispatched.
    if state['failed'] and state['next_step'] < len(job['steps']):
        return execute_job(workflow, job, context, state, preflight_only=False)
    state['complete'] = True
    receipt = dict(schema='point4-consolidated-case-v1', workflow=workflow['path'], workflow_name=workflow['name'],
                   job=job['id'], display_name=job['name'], native_hosted_workflow_claimed=False,
                   status='FAIL' if state['failed'] else 'PASS', steps=state['records'],
                   execution_root=str(context['execution']),
                   accumulated_active_seconds=state['active_seconds'], original_job_budget_minutes=job['timeout_minutes'])
    write_json(state['directory'] / 'receipt.json', receipt)
    return receipt



def review_safe_name(value):
    require(type(value)is str and 0<len(value.encode())<=1024 and not value.startswith('/')
            and '\\'not in value and ':'not in value
            and all(part not in ('','.','..')for part in value.split('/'))
            and all(ord(ch)>=32 and ord(ch)!=127 for ch in value), 'Unsafe review path')
    return value


def review_identity(info):
    return (info.st_dev,info.st_ino,info.st_mode,info.st_nlink,info.st_size,info.st_mtime_ns,info.st_ctime_ns)


def review_stream(path,deadline,maximum,writer=None):
    """One bounded hash/copy pass; no object importer, decoder, or second hash."""
    path=Path(path)
    for parent in path.parents:
        require(stat.S_ISDIR(parent.lstat().st_mode),'Review input ancestor alias')
    pre=path.lstat()
    require(stat.S_ISREG(pre.st_mode)and pre.st_nlink==1 and not pre.st_mode&0o7000
            and 0<=pre.st_size<=maximum,'Review input kind/size/alias')
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC)
    hasher=hashlib.sha256();total=0
    try:
        require(review_identity(os.fstat(fd))==review_identity(pre),'Review input changed at open')
        while True:
            require(time.monotonic()<deadline,'Review projection deadline')
            block=os.read(fd,65536)
            if not block:break
            total+=len(block);require(total<=maximum and total<=pre.st_size,'Review input grew')
            hasher.update(block)
            if writer is not None:writer.write(block)
        require(total==pre.st_size and review_identity(os.fstat(fd))==review_identity(pre)
                ==review_identity(path.lstat()),'Review input changed during stream')
    finally:os.close(fd)
    return dict(bytes=total,sha256=hasher.hexdigest()),review_identity(pre)


def review_source_match(path,pattern):
    """Source glob components; '*' cannot silently consume a path separator."""
    parts=Path(path).parts;wanted=Path(pattern).parts;memo={}
    def match(i,j):
        if(i,j)in memo:return memo[i,j]
        if j==len(wanted):result=i==len(parts)
        elif wanted[j]=='**':result=match(i,j+1)or(i<len(parts)and match(i+1,j))
        else:result=i<len(parts)and fnmatch.fnmatchcase(parts[i],wanted[j])and match(i+1,j+1)
        memo[i,j]=result;return result
    if not any(ch in pattern for ch in '*?['):
        return path==pattern or path.startswith(pattern.rstrip('/')+'/')
    return match(0,0)


def review_producer_names(policy,names,complete):
    require(len(names)==len(set(names)),'Duplicate producer logical name')
    required=set(policy['required']);actual=set(names)
    optional=set(policy.get('optional_text',[]))
    dynamic=policy.get('dynamic');matched=set()
    if dynamic:
        routes={route:[]for route in dynamic['exact_routes']}
        for name in actual-required:
            match=re.fullmatch(dynamic['regex'],name)
            require(match is not None and match.group(1)in routes,'Unknown dynamic producer name')
            routes[match.group(1)].append((match.group(2),match.group(3)));matched.add(name)
        for values in routes.values():
            if complete:require(len(values)==2 and len({v[0]for v in values})==1
                                and {v[1]for v in values}=={'stdout','receipt'},'Incomplete dynamic journal pair')
    unknown=actual-required-optional-matched
    require(not unknown,'Unknown original text classification')
    if complete:
        require(required<=actual,'Missing original selected text')
        require(len(actual-optional)==policy['count'],'Original selected text cardinality')
        for pair in policy.get('paired_optional',[]):
            require(not(actual&set(pair))or set(pair)<=actual,'Partial optional producer pair')


def review_artifact_members(plan,case,step,members,expansion,complete):
    policy=plan['review_projection']['producers'].get(case)
    require(policy is not None,'Artifact producer absent from Source policy')
    require(members.get('schema')=='point4-original-upload-selection-v1'
            and members.get('original_upload')==step and type(members.get('files'))is list,
            'Original upload/manifest Source join')
    ordinal=step['ordinal'];main_upload=ordinal==policy['upload_ordinal']
    require(main_upload or ordinal==policy.get('optional_failure_upload_ordinal'),'Unknown Source artifact ordinal')
    root=expand(policy['root'],**expansion);require(Path(root).is_absolute(),'Producer root must be absolute')
    patterns=[expand(p,**expansion)for p in step['with']['path'].splitlines()if p]
    logical=[];mapping={};folded=set();total=0
    for index,row in enumerate(members['files']):
        require(type(row)is dict and set(row)=={'original_path','stored_path','bytes','sha256'}
                and row['stored_path']==f'{index:06d}.bin'and type(row['bytes'])is int
                and 0<=row['bytes']<=MAX_ARCHIVE_FILE and re.fullmatch('[0-9a-f]{64}',row['sha256']or''),
                'Invalid original member inventory')
        original=row['original_path'];require(type(original)is str and Path(original).is_absolute()
                and all(ord(c)>=32 and ord(c)!=127 for c in original)
                and any(review_source_match(original,p)for p in patterns),'Original member outside Source upload')
        require(original.startswith(root.rstrip('/')+'/'),'Original member root mismatch')
        name=review_safe_name(original[len(root.rstrip('/'))+1:]);require(name.casefold()not in folded,'Original member case alias');folded.add(name.casefold())
        opaque=any(name.startswith(p+'/')for p in policy.get('opaque_roots',[]))and any(name.endswith(s)for s in policy.get('opaque_suffixes',[]))
        if not opaque:
            require(row['bytes']<=policy['original_per_file_limit'],'Original text per-file cap')
            logical.append(name);total+=row['bytes']
        mapping[row['stored_path']]=dict(original_path=original,logical_name=name,expected=row,
                                         role='OPAQUE_ORIGINAL_OBJECT'if opaque else'ORIGINAL_SELECTED_TEXT')
    require(total<=policy['original_aggregate_limit'],'Original text aggregate cap')
    if main_upload:review_producer_names(policy,logical,complete)
    else:require(set(logical)<={'first-compiler-failure.json','first-compiler-failure.sha256'}and all(v['role']!='OPAQUE_ORIGINAL_OBJECT'for v in mapping.values()),'Unknown first failure evidence')
    return mapping,total


def review_validate_cases(plan,coverage,stage,evidence):
    assignment=stage_partition(plan,stage);passed=coverage is not None and coverage.get('stage_passed')is True
    if coverage is None:return assignment,False
    require(coverage.get('schema')=='point4-consolidated-stage-coverage-v2'
            and coverage.get('stage')==stage and coverage.get('partition_sha256')==assignment['partition_sha256']
            and coverage.get('full_partition')==assignment['partition']and coverage.get('all_cases_passed')is False,
            'Coverage stage/partition join')
    rows=coverage.get('jobs');require(type(rows)is list,'Missing case rows')
    expected=[(w['path'],j['id'])for w in assignment['workflows']for j in w['jobs']]
    actual=[(row['workflow'],row['job'])for row in rows]
    require(len(actual)==len(set(actual))and all(key in expected for key in actual),'Foreign or repeated case result')
    if passed:require(actual==expected and coverage.get('stopped_after_first_failure')is False,'Partial stage cannot pass')
    source={(w['path'],j['id']):j for w in assignment['workflows']for j in w['jobs']}
    for row in rows:
        job=source[row['workflow'],row['job']];steps=row.get('steps');require(type(steps)is list,'Missing Source step rows')
        if passed:require(row.get('status')=='PASS'and len(steps)==len(job['steps']),'Missing complete job steps')
        require(len({s['ordinal']for s in steps})==len(steps),'Duplicate Source step')
        for value in steps:
            matches=[s for s in job['steps']if s['ordinal']==value['ordinal']];require(len(matches)==1,'Unknown step ordinal');step=matches[0]
            require(value.get('source_run_sha256')==step.get('run_sha256'),'Source Run hash differs')
            if passed and 'run'in step:
                require(value.get('status')=='PASS'and value.get('exit_code')==0
                        and value.get('reaped')is True and value.get('timed_out')is False
                        and value.get('leaked_group_killed')is False,'Unclosed or failed Source Run')
                cleanup=value.get('owned_systemd_cleanup')
                require(cleanup is None or(cleanup.get('confirmed_empty')is True and cleanup.get('confirmed_terminal')is True),'Owned unit not terminal/empty')
            elif passed:
                expected_status='PRESERVED_SOURCE_ALLOWLIST'if step['uses']==plan['setup_actions']['upload']else'COORDINATOR_SETUP_REUSE'
                require(value.get('status')==expected_status,'Source action disposition differs')
        if passed:
            require([s['ordinal']for s in steps]==[s['ordinal']for s in job['steps']],'Source step order differs')
    if passed:
        seed=coverage.get('native_initial_full_build')
        require(type(seed)is dict and seed.get('exit_code')==0 and seed.get('reaped')is True
                and seed.get('timed_out')is False and seed.get('leaked_group_killed')is False,'Seed owner not successfully reaped')
    return assignment,passed


def project_review_evidence(plan,stage,evidence,destination,expansion,external,deadline,source_binding,final_check=None):
    """Transport exact saved outputs. No proof objects or original ZIP are parsed."""
    policy=plan['review_projection'];require(policy['schema']=='point4-compact-review-Source-policy-v1','Unknown review Source policy')
    require(source_binding['tooling']==source_binding['proof']==source_binding['chart'],'Projection must bind exact current proof/tooling Source')
    require(policy['maximum_raw_bytes']==256*1024**2 and policy['maximum_file_bytes']==16*1024**2
            and policy['maximum_files']==10000 and policy['deadline_seconds']==120,'Review bounds changed')
    evidence=Path(evidence);destination=Path(destination)
    require(evidence.is_absolute()and evidence==evidence.resolve()and stat.S_ISDIR(evidence.lstat().st_mode),'Invalid evidence root')
    require(destination.is_absolute()and destination==destination.resolve(strict=False)
            and not destination.exists()and not destination.is_symlink()
            and not destination.is_relative_to(evidence)and not evidence.is_relative_to(destination),'Review output is not fresh/separate')
    for parent in destination.parents:require(stat.S_ISDIR(parent.lstat().st_mode),'Review output parent alias')
    require(not any(destination.is_relative_to(Path(root))for root in source_binding.get('source_roots',[])),'Review output must stay outside Source')
    require(time.monotonic()<deadline,'Review projection deadline')
    coverage_path=evidence/'coverage.json';parsed_expected={}
    coverage_raw=regular(coverage_path,16*1024**2)if coverage_path.exists()else None
    coverage=strict_json(coverage_raw)if coverage_raw is not None else None
    if coverage_raw is not None:parsed_expected['coverage.json']={'bytes':len(coverage_raw),'sha256':digest(coverage_raw)}
    assignment,passed=review_validate_cases(plan,coverage,stage,evidence)
    if passed:
        require(source_binding['source_post_valid']is True and source_binding['cache_final_valid']is True,'Missing SourcePOST/cache seal')
        require(coverage['tooling_source']==source_binding['tooling']and coverage['executed_proof_source']==source_binding['proof']
                and coverage['chart_proof_source']==source_binding['chart'],'Current Source differs from native Source')
    # Enumerate and classify the complete physical namespace before copying payloads.
    cases={w['path'].split('/')[-1][:-4]+'--'+j['id']:(w,j)for w in assignment['workflows']for j in w['jobs']}
    names={};input_pre={};directories=[];folded=set();symlinks=[]
    for parent,dirs,files in os.walk(evidence,followlinks=False):
        require(time.monotonic()<deadline,'Review enumeration deadline')
        for name in dirs+files:
            path=Path(parent)/name;rel=review_safe_name(path.relative_to(evidence).as_posix());require(rel.casefold()not in folded,'Review namespace case alias');folded.add(rel.casefold())
            require(len(folded)<=2*policy['maximum_input_files'],'Review input namespace count')
            info=path.lstat()
            if stat.S_ISLNK(info.st_mode):
                require(rel in('bin/bash','bin/lake')and os.readlink(path)==source_binding['broker_path'],'Unexpected input symlink')
                symlinks.append(dict(path=rel,target=os.readlink(path),identity=review_identity(info)));continue
            if stat.S_ISDIR(info.st_mode):
                parts=rel.split('/')
                allowed=rel in('cases','bin','command-receipts','same-run-cache')
                allowed=allowed or(len(parts)==2 and parts[0]=='cases'and parts[1]in cases)
                allowed=allowed or(len(parts)==3 and parts[0]=='cases'and parts[1]in cases
                    and any(parts[2]=='artifact-'+str(step['ordinal'])and step.get('uses')==plan['setup_actions']['upload']for step in cases[parts[1]][1]['steps']))
                allowed=allowed or(len(parts)==2 and parts[0]=='same-run-cache'and re.fullmatch('[0-9a-f]{64}',parts[1])is not None)
                require(allowed,'Unknown evidence directory')
                directories.append((rel,review_identity(info)));continue
            require(stat.S_ISREG(info.st_mode)and info.st_nlink==1 and not info.st_mode&0o7000,'Unsafe physical review input')
            require(len(names)<policy['maximum_input_files'],'Review input file count');names[rel]=path;input_pre[rel]=review_identity(info)
    def parsed_input(name):
        raw=regular(names[name],16*1024**2)
        require(review_identity(names[name].lstat())==input_pre[name],'Parsed metadata changed since namespace PRE')
        row={'bytes':len(raw),'sha256':digest(raw)}
        require(name not in parsed_expected or parsed_expected[name]==row,'Parsed metadata bytes changed')
        parsed_expected[name]=row
        return strict_json(raw)
    original={};main_total=0;original_text_bytes=0;original_text_count=0
    for case,(workflow,job)in cases.items():
        for step in job['steps']:
            if step.get('uses')!=plan['setup_actions']['upload']:continue
            rel=f'cases/{case}/artifact-{step["ordinal"]}/members.json'
            if rel not in names:
                if passed:raise RuntimeError('Missing original upload selection receipt')
                continue
            metadata=parsed_input(rel);mapping,total=review_artifact_members(plan,case,step,metadata,expansion,passed)
            original_text_bytes+=total;original_text_count+=sum(row['role']!='OPAQUE_ORIGINAL_OBJECT'for row in mapping.values())
            if workflow['path']=='.github/workflows/point4-smooth-forward-support.yml':main_total+=total
            for name,row in mapping.items():original[f'cases/{case}/artifact-{step["ordinal"]}/{name}']=row
    require(main_total<=32*1024**2,'MAIN52+ordinary3 shared raw cap')
    require(original_text_count<=1000 and original_text_bytes<=128*1024**2,'Global original selected-text bound')
    def classify(rel):
        if rel in original:return original[rel]['role']
        if rel in('coverage.json','compiled-cache-provenance.json','native-full-build.log','output-budget.json','output-budget.lock'):return'RUNTIME_TEXT'
        parts=rel.split('/')
        if len(parts)>=3 and parts[0]=='cases'and parts[1]in cases:
            job=cases[parts[1]][1]
            if len(parts)==3 and parts[2]=='receipt.json':return'RUNTIME_TEXT'
            if len(parts)==3:
                m=re.fullmatch(r'step-([0-9]+)\.(sh|log)',parts[2])
                if m and any(s['ordinal']==int(m.group(1))and'run'in s for s in job['steps']):return'RUNTIME_TEXT'
            if len(parts)==4 and parts[2].startswith('artifact-')and parts[3]=='members.json':
                if any(parts[2]=='artifact-'+str(s['ordinal'])and s.get('uses')==plan['setup_actions']['upload']for s in job['steps']):return'RUNTIME_TEXT'
        if len(parts)==2 and parts[0]=='command-receipts'and re.fullmatch(r'[0-9]{1,20}-[0-9]{1,20}\.json',parts[1]):return'RUNTIME_TEXT'
        if len(parts)==3 and parts[0]=='same-run-cache'and re.fullmatch('[0-9a-f]{64}',parts[1])and parts[2]in('receipt.json','audit.json','build.log','stdout.bin','stderr.bin'):return'RAW_COMMAND_STREAM_OR_RECEIPT'
        raise RuntimeError('Unknown evidence classification: '+rel)
    roles={name:classify(name)for name in names}
    require(sum(role!='OPAQUE_ORIGINAL_OBJECT'for role in roles.values())+len(external)+10<=policy['maximum_files'],'Compact count/raw aggregate')
    require(all(name in names for name in original),'Original manifest points to missing payload')
    runtime_expected=parsed_expected
    if coverage:
        seed=coverage.get('native_initial_full_build')
        if type(seed)is dict and 'sha256'in seed:runtime_expected['native-full-build.log']=seed
        restored=coverage.get('compiled_cache_provenance')
        if type(restored)is dict:runtime_expected['compiled-cache-provenance.json']={'sha256':restored['state_sha256'],'bytes':restored['state_bytes']}
        for case,(workflow,job)in cases.items():
            found=[row for row in coverage['jobs']if row['workflow']==workflow['path']and row['job']==job['id']]
            if found:
                for step in found[0]['steps']:
                    if 'sha256'in step:runtime_expected[f'cases/{case}/step-{step["ordinal"]}.log']=step
    cache_keys={name.split('/')[1]for name in names if name.startswith('same-run-cache/')}
    owners={}
    for key in cache_keys:
        prefix='same-run-cache/'+key+'/'
        required_cache={'receipt.json','audit.json','build.log','stdout.bin','stderr.bin'}
        present={name[len(prefix):]for name in names if name.startswith(prefix)}
        if passed:require(present==required_cache,'Incomplete command owner payload')
        if 'receipt.json'not in present:continue
        saved=parsed_input(prefix+'receipt.json');saved_raw=regular(names[prefix+'receipt.json'],16*1024**2);require(digest(saved_raw)==parsed_expected[prefix+'receipt.json']['sha256'],'Owner metadata drift')
        require(saved.get('schema')=='point4-same-run-command-v1'and saved.get('key')==key
                and digest(canonical(saved['identity']))==key,'Command owner identity/key mismatch')
        require(saved['identity']['source']==coverage['executed_proof_source']
                and saved['identity']['tooling_source']==coverage['tooling_source']
                and saved['identity']['plan_sha256']==digest(canonical(plan)),'Command owner Source/plan mismatch')
        owners[key]=(saved,digest(saved_raw));streams=saved['streams']
        require(type(streams)is list and len(streams)==2,'Command streams missing')
        for part,row in zip(('stdout.bin','stderr.bin'),streams):runtime_expected[prefix+part]=row
        for part,keyname in [('audit.json','audit_json'),('build.log','build_log')]:
            if type(saved.get(keyname))is dict:runtime_expected[prefix+part]=saved[keyname]
    native_counts={key:0 for key in owners}
    for name in names:
        if not name.startswith('command-receipts/'):continue
        value=parsed_input(name);key=value.get('key')
        require(key in owners,'Consumer lacks command owner');owner,owner_sha=owners[key]
        require(value.get('schema')=='point4-command-consumer-v1'and value.get('native_receipt_sha256')==owner_sha
                and value.get('owner')==owner['owner']and value.get('streams')==owner['streams']
                and value.get('exit_code')==owner['exit_code'],'Consumer/owner output join mismatch')
        consumer=value.get('consumer');require(type(consumer)is dict and consumer.get('case')in cases
                and any(step['ordinal']==int(consumer['step'])for step in cases[consumer['case']][1]['steps']),'Consumer outside assigned Source cases')
        if value.get('mode')=='NATIVE':
            require(consumer==owner['owner'],'Native command owner attribution differs');native_counts[key]+=1
        else:require(value.get('mode')=='SAME_RUN_REUSE'and owner.get('reusable')is True,'Ineligible replay')
    if passed:require(all(count==1 for count in native_counts.values()),'Command needs exactly one native producer')
    if passed:
        require(all(name in names for name in('coverage.json','compiled-cache-provenance.json','native-full-build.log','output-budget.json','output-budget.lock')),'Missing runtime evidence')
        for case,(workflow,job)in cases.items():
            require(f'cases/{case}/receipt.json'in names,'Missing case receipt')
            row=next(row for row in coverage['jobs']if row['workflow']==workflow['path']and row['job']==job['id'])
            require(parsed_input(f'cases/{case}/receipt.json')==row,'Case receipt/coverage mismatch')
            for step in job['steps']:
                if'run'in step:
                    for suffix in('sh','log'):require(f'cases/{case}/step-{step["ordinal"]}.{suffix}'in names,'Missing full Source Run input/output')
                    require(regular(names[f'cases/{case}/step-{step["ordinal"]}.sh'],16*1024**2)==step['run'].encode(),'Saved full Source script differs')
    # Selected text limits are checked from metadata before first copy.
    selected=[name for name in sorted(names)if roles[name]!='OPAQUE_ORIGINAL_OBJECT']
    sizes=[names[name].lstat().st_size for name in selected]
    require(all(n<=policy['maximum_file_bytes']for n in sizes),'Oversized selected text; truncation forbidden')
    require(len(selected)+len(external)+10<=policy['maximum_files']and sum(sizes)<=policy['maximum_raw_bytes'],'Compact count/raw aggregate')
    destination.mkdir();budget=OutputBudget(destination,initialize=True,maximum=policy['maximum_raw_bytes'],entries=policy['maximum_files'])
    budget.mkdir(destination/'files');budget.mkdir(destination/'inventory')
    copied=[];inventory=[];seals={};copied_bytes=0
    for number,name in enumerate(sorted(names)):
        require(time.monotonic()<deadline,'Review hash/copy deadline');target=None
        if roles[name]!='OPAQUE_ORIGINAL_OBJECT':target=destination/'files'/f'{number:06d}.bin'
        if target is None:row,identity=review_stream(names[name],deadline,MAX_ARCHIVE_FILE)
        else:
            with budget.file(target,policy['maximum_file_bytes'])as writer:row,identity=review_stream(names[name],deadline,policy['maximum_file_bytes'],writer)
            copied_bytes+=row['bytes'];copied.append(dict(source=name,stored=target.relative_to(destination).as_posix(),role=roles[name],**row))
        require(identity==input_pre[name],'Input changed after namespace PRE')
        seals[name]=identity
        if name in runtime_expected:require(row['bytes']==runtime_expected[name]['bytes']and row['sha256']==runtime_expected[name]['sha256'],'Runtime log/native receipt hash mismatch')
        if name in original:require(row['bytes']==original[name]['expected']['bytes']and row['sha256']==original[name]['expected']['sha256'],'Original copied payload/inventory hash mismatch')
        inventory.append(dict(path=name,role=roles[name],identity=list(identity),**row))
    for label,path in sorted(external.items()):
        review_safe_name(label);target=destination/'files'/('external-'+label)
        with budget.file(target,policy['maximum_file_bytes'])as writer:row,identity=review_stream(path,deadline,policy['maximum_file_bytes'],writer)
        if label in source_binding.get('external_expected',{}):require(row==source_binding['external_expected'][label],'External parsed Source/cache seal changed')
        copied_bytes+=row['bytes'];copied.append(dict(source='EXTERNAL/'+label,stored=target.relative_to(destination).as_posix(),role='CACHE_OR_SOURCE_SEAL',**row));seals['EXTERNAL/'+label]=(path,identity)
    require(copied_bytes<=policy['maximum_raw_bytes'],'Review copied raw cap')
    chunks=[];pending=[];length=2
    def flush():
        nonlocal pending,length
        if not pending:return
        raw=canonical(pending)+b'\n';require(len(raw)<=policy['inventory_chunk_bytes'],'Opaque inventory chunk cap')
        path=destination/'inventory'/f'{len(chunks):05d}.json'
        with budget.file(path,policy['inventory_chunk_bytes'])as out:out.write(raw)
        chunks.append(dict(path=path.relative_to(destination).as_posix(),rows=len(pending),bytes=len(raw),sha256=digest(raw)));pending=[];length=2
    for row in inventory:
        size=len(canonical(row))+1
        if length+size>policy['inventory_chunk_bytes']-2:flush()
        pending.append(row);length+=size
    flush()
    # A complete second namespace/stat pass, not a second multi-GiB payload hash.
    observed=[]
    for parent,dirs,files in os.walk(evidence,followlinks=False):
        require(time.monotonic()<deadline,'Review final namespace deadline')
        for name in dirs+files:observed.append((Path(parent)/name).relative_to(evidence).as_posix())
    require(set(observed)==set(names)|{x[0]for x in directories}|{x['path']for x in symlinks},'Evidence namespace changed')
    for name,identity in seals.items():
        path,expected=identity if name.startswith('EXTERNAL/')else(names[name],identity)
        require(time.monotonic()<deadline and review_identity(Path(path).lstat())==expected,'Evidence input POST differs')
    for name,identity in directories:require(review_identity((evidence/name).lstat())==identity,'Evidence directory POST differs')
    for row in symlinks:require(review_identity((evidence/row['path']).lstat())==row['identity']and os.readlink(evidence/row['path'])==row['target'],'Broker shim POST differs')
    # Rehash only bounded projected text, never multi-GiB opaque inputs again.
    expected_outputs={row['stored']:{'bytes':row['bytes'],'sha256':row['sha256']}for row in copied}
    expected_outputs.update({row['path']:{'bytes':row['bytes'],'sha256':row['sha256']}for row in chunks})
    actual_outputs=set()
    for parent,dirs,files in os.walk(destination,followlinks=False):
        require(time.monotonic()<deadline and len(actual_outputs)+len(files)<=policy['maximum_files'],'Review output namespace deadline/count')
        for name in dirs:
            path=Path(parent)/name
            require(stat.S_ISDIR(path.lstat().st_mode)and path.relative_to(destination).as_posix()in('files','inventory'),'Unexpected review output directory')
        for name in files:
            path=Path(parent)/name;rel=path.relative_to(destination).as_posix();actual_outputs.add(rel)
            require(rel in expected_outputs or rel in('output-budget.json','output-budget.lock'),'Unexpected review output file')
            actual,_=review_stream(path,deadline,policy['maximum_file_bytes'])
            if rel in expected_outputs:require(actual==expected_outputs[rel],'Projected output hash/size mismatch')
    require(actual_outputs==set(expected_outputs)|{'output-budget.json','output-budget.lock'},'Missing review output')
    if final_check is not None:final_check()
    index=dict(schema='point4-compact-review-projection-v1',projection_complete=True,stage=stage,
               stage_execution_passed=passed,all_cases_passed=False,pair_join_required=True,
               tooling_source=source_binding['tooling'],proof_source=source_binding['proof'],chart_source=source_binding['chart'],
               full_partition=assignment['partition'],partition_sha256=assignment['partition_sha256'],
               review_policy_sha256=digest(canonical(policy)),plan_sha256=digest(canonical(plan)),
               provider_context=coverage.get('provider_context')if coverage else None,
               preserved_inputs=len(inventory),preserved_input_bytes=sum(row['bytes']for row in inventory),
               inventory_chunks=chunks,inventory_rows_sha256=digest(canonical(inventory)),
               selected_files=copied,selected_raw_bytes=copied_bytes,known_shim_links=symlinks,
               all_input_FD_and_metadata_PREPOST=True,all_projected_output_hashes_verified=True,original_objects_read_only_as_opaque_streams=True,
               original_object_semantic_imports=0,original_full_ZIP_locally_hashed=False,
               original_full_artifact_retained_separately=True,archive_transport='NEW_COMPACT_ARTIFACT_ONLY',
               index_self_hash_scope='index/output-budget.json/output-budget.lock excluded from self inventory; canonical new artifact and external descriptor bind them',
               limits=dict(raw=policy['maximum_raw_bytes'],file=policy['maximum_file_bytes'],files=policy['maximum_files'],deadline_seconds=120),
               scope=policy['scope'],qualification_credit=0)
    encoded=canonical(index)+b'\n';require(len(encoded)<=policy['maximum_file_bytes'],'Review index cap')
    require(time.monotonic()<deadline,'Review final write deadline')
    index_path=destination/'review-index.json'
    with budget.file(index_path,policy['maximum_file_bytes'])as out:out.write(encoded)
    try:
        checked,_=review_stream(index_path,deadline,policy['maximum_file_bytes'])
        require(checked==dict(bytes=len(encoded),sha256=digest(encoded)),'Final review index corruption')
        final_names=set()
        for parent,dirs,files in os.walk(destination,followlinks=False):
            require(time.monotonic()<deadline and len(final_names)+len(files)<=policy['maximum_files'],'Final review output deadline/count')
            for name in dirs:
                path=Path(parent)/name
                require(stat.S_ISDIR(path.lstat().st_mode)and path.relative_to(destination).as_posix()in('files','inventory'),'Final review output directory differs')
            for name in files:
                path=Path(parent)/name;info=path.lstat()
                require(stat.S_ISREG(info.st_mode)and info.st_nlink==1 and not info.st_mode&0o7000,'Final review output alias/type')
                final_names.add(path.relative_to(destination).as_posix())
        require(final_names==set(expected_outputs)|{'output-budget.json','output-budget.lock','review-index.json'},'Final review output namespace differs')
    except BaseException:
        index_path.unlink(missing_ok=True)
        raise
    return index


def project_review(args):
    started=time.monotonic();deadline=started+120
    require(args.review_directory is not None and args.source_pre is not None and args.source_post is not None,'Projection paths required')
    tooling=args.tooling_root;execution=args.execution_root;chart=args.chart_execution_root
    plan=strict_json(regular(tooling/'scripts/point4_ci/plan.json'));validate_plan(plan,execution)
    policy=plan['review_projection']
    tool,proof,chart_source=current_execution_sources(tooling,execution,chart,args.expected_sha,args.expected_tree)
    external={};external_raw={};post_valid=False;cache_valid=False
    for label,path in [('source-pre.json',args.source_pre),('source-post.json',args.source_post),('cache-final-state.json',args.compiled_cache_provenance),('cache-action.log',Path('/tmp/point4-consolidated-cache.log'))]:
        if path.exists():external[label]=path;external_raw[label]=regular(path,16*1024**2)
    if args.source_post.exists():
        post=strict_json(external_raw['source-post.json']);post_valid=projection_source_post(post,args.expected_sha,args.expected_tree,plan)
    manifest=args.compiled_cache_provenance.parent/'snapshot/inventory.json'
    if args.compiled_cache_provenance.exists()and manifest.exists():
        state_raw=external_raw['cache-final-state.json'];state=strict_json(state_raw);compiled_cache_provenance(state_raw,args.stage,proof,toolchain_identity(execution,shutil.which('lake'),plan),os.environ)
        manifest_raw=regular(manifest,16*1024**2);value=strict_json(manifest_raw)
        cache_valid=value.get('identity')==state.get('identity')and value.get('key')==state.get('key')
        if args.stage=='first':cache_valid=cache_valid and state.get('inventory_sha256')==digest(manifest_raw)and state.get('save_action_step_outcome')in('success','skipped')
        external['cache-inventory.json']=manifest;external_raw['cache-inventory.json']=manifest_raw
    cache_valid=cache_valid and all(label in external for label in('source-pre.json','source-post.json','cache-final-state.json','cache-action.log','cache-inventory.json'))
    binding=dict(tooling=tool,proof=proof,chart=chart_source,source_roots=[str(tooling),str(execution),str(chart)],broker_path=str(tooling/'scripts/point4_ci/command_broker.py'),source_post_valid=post_valid,cache_final_valid=cache_valid,external_expected={label:dict(bytes=len(raw),sha256=digest(raw))for label,raw in external_raw.items()})
    expansion=dict(sha=args.expected_sha,tree=args.expected_tree,runner_temp=os.environ['RUNNER_TEMP'],event='workflow_dispatch')
    def final_source_check():
        require(current_execution_sources(tooling,execution,chart,args.expected_sha,args.expected_tree)==(tool,proof,chart_source),'Projection Source POST differs')
    index=project_review_evidence(plan,args.stage,args.evidence_dir,args.review_directory,expansion,external,deadline,binding,final_source_check)
    require(time.monotonic()<deadline,'Projection overall deadline')
    print(json.dumps(dict(projection_complete=True,stage=args.stage,stage_execution_passed=index['stage_execution_passed'],
                         selected_raw_bytes=index['selected_raw_bytes'],elapsed_seconds=time.monotonic()-started)))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tooling-root', required=True, type=Path)
    parser.add_argument('--execution-root', required=True, type=Path)
    parser.add_argument('--chart-execution-root', required=True, type=Path)
    parser.add_argument('--expected-sha', required=True)
    parser.add_argument('--expected-tree', required=True)
    parser.add_argument('--evidence-dir', required=True, type=Path)
    parser.add_argument('--stage', required=True, choices=('first','second'))
    parser.add_argument('--compiled-cache-provenance', required=True, type=Path)
    parser.add_argument('--budget-seconds', type=int, default=19800)
    parser.add_argument('--project-review', action='store_true')
    parser.add_argument('--review-directory', type=Path)
    parser.add_argument('--source-pre', type=Path)
    parser.add_argument('--source-post', type=Path)
    args = parser.parse_args()
    if args.project_review:
        return project_review(args)
    require(300 <= args.budget_seconds <= 21000, 'Finite overall budget must be300..21000seconds')
    deadline = time.monotonic() + args.budget_seconds
    tooling, execution, chart_execution, evidence = args.tooling_root, args.execution_root, args.chart_execution_root, args.evidence_dir
    for root in (tooling, execution, chart_execution, evidence.parent):
        require(root.is_absolute() and root == root.resolve(), 'Canonical absolute directories required')
    require(not evidence.exists() and not evidence.is_symlink(), 'Evidence directory must be fresh')
    require(not evidence.is_relative_to(tooling) and not evidence.is_relative_to(execution) and not evidence.is_relative_to(chart_execution), 'Evidence must stay outside both Source views')
    evidence.mkdir()
    budget = OutputBudget(evidence,initialize=True)
    os.environ['P4_CI_BUDGET_ROOT']=str(evidence)
    budget.mkdir(evidence / 'cases')
    plan = strict_json(regular(tooling / 'scripts/point4_ci/plan.json'))
    validate_plan(plan, execution)
    assignment = stage_partition(plan, args.stage)
    execution_head, execution_tree = args.expected_sha, args.expected_tree
    tooling_pre, execution_pre, chart_pre = current_execution_sources(tooling, execution, chart_execution, execution_head, execution_tree)
    projection = source_guard(tooling, 'verify_tooling_overlay', args.expected_sha)
    require(projection_source_post(projection,execution_head,execution_tree,plan),'Current tooling overlay did not establish current execution gate')
    require(chart_execution != execution and (chart_execution/'.git').is_dir()
            and not (chart_execution/'curvature/.lake').exists(), 'Chart Source must be a distinct pristine normal checkout')
    source_guard(execution, 'verify_current')
    real_lake, real_bash = shutil.which('lake'), '/usr/bin/bash'
    require(real_lake and Path(real_lake).is_absolute(), 'Pinned Lake must already be installed by coordinator')
    toolchain = toolchain_identity(execution, real_lake, plan)
    cache_raw = regular(args.compiled_cache_provenance,32*1024*1024)
    cache_provenance = compiled_cache_provenance(cache_raw,args.stage,execution_pre,toolchain,os.environ)
    with budget.file(evidence / 'compiled-cache-provenance.json',32*1024*1024) as handle:
        handle.write(cache_raw)
    go = subprocess.check_output(['go', 'version'], timeout=30).decode().strip()
    require(re.fullmatch(r'go version go1\.24\.0 [^\n]+', go), 'Coordinator must install exact Go1.24.0')
    shims = evidence / 'bin'; budget.mkdir(shims)
    broker = tooling / 'scripts/point4_ci/command_broker.py'
    require(bool(broker.stat().st_mode & stat.S_IXUSR), 'Broker Source must be executable')
    for name in ('bash', 'lake'):
        budget.reserve(shims/name,kind='symlink')
        (shims / name).symlink_to(broker)
    env = dict(os.environ)
    provider_workspace = env.get('GITHUB_WORKSPACE', '')
    real_path = env['PATH']
    env.update(GITHUB_WORKSPACE=str(execution), P4_CI_PROVIDER_GITHUB_WORKSPACE=provider_workspace, P4_CI_ROOT=str(execution), P4_CI_TOOLING_ROOT=str(tooling),
               P4_CI_TOOLING_SHA=args.expected_sha, P4_CI_TOOLING_TREE=args.expected_tree,
               P4_CI_EXPECTED_SHA=execution_head, P4_CI_EXPECTED_TREE=execution_tree,
               P4_CI_EVIDENCE=str(evidence), P4_CI_REAL_LAKE=real_lake, P4_CI_REAL_BASH=real_bash,
               EXPECTED_SHA=execution_head, PYTHONDONTWRITEBYTECODE='1')
    env['PATH'] = str(shims) + os.pathsep + env['PATH']
    context = dict(tooling=tooling, execution=execution, evidence=evidence, plan=plan,
                   real_bash=real_bash, real_path=real_path, env=env, counters=dict(bytes=0, files=0, namespace_entries=0), deadline=deadline,
                   expansion=dict(sha=execution_head, tree=execution_tree,
                                  runner_temp=os.environ['RUNNER_TEMP'], event='workflow_dispatch'))
    chart_context = dict(context,execution=chart_execution,env=dict(context['env']))
    chart_context['env'].update(GITHUB_WORKSPACE=str(chart_execution),P4_CI_ROOT=str(chart_execution))
    states = [(workflow,job,chart_context if workflow['path']=='.github/workflows/point4-local-chart-connection.yml' else context)
              for workflow in assignment['workflows'] for job in workflow['jobs']]
    states = [(workflow,job,case_context,prepare_case(workflow,job,case_context)) for workflow,job,case_context in states]
    results, stopped = [], False
    # Original Source/provenance/mock prefixes run before any cold build. The
    # time spent in each case accumulates across phases; waiting for other cases
    # does not reset an execution budget or create another hosted job.
    for workflow, job, case_context, state in states:
        result = execute_job(workflow, job, case_context, state, preflight_only=True)
        if result is not None and result['status'] == 'FAIL':
            results.append(result); stopped = True; break
    seed = None
    if not stopped:
        seed = run_process([real_lake, 'build'], execution / 'curvature', env,
                           evidence / 'native-full-build.log', min(210 * 60, deadline - time.monotonic()))
        stopped = not (seed['exit_code'] == 0 and not seed['timed_out'] and not seed['leaked_group_killed'])
    if not stopped:
        for workflow, job, case_context, state in states:
            result = execute_job(workflow, job, case_context, state)
            results.append(result)
            print(json.dumps(dict(workflow=workflow['path'], job=job['id'], status=result['status'])), flush=True)
            if result['status'] == 'FAIL':
                stopped = True; break
    source_guard(execution, 'verify_current')
    source_guard(chart_execution, 'verify_current')
    source_guard(tooling, 'verify_tooling_overlay', args.expected_sha)
    require(source_identity(tooling, args.expected_sha, args.expected_tree) == tooling_pre, 'Tooling Source POST differs')
    require(source_identity(execution, execution_head, execution_tree) == execution_pre, 'Execution Source POST differs')
    require(source_identity(chart_execution, execution_head, execution_tree) == chart_pre, 'Chart Source POST differs')
    require(regular(args.compiled_cache_provenance,32*1024*1024)==cache_raw, 'Cache restore provenance changed during stage')
    output_inventory = evidence_usage(context)
    outcome = stage_outcome(assignment, results, stopped)
    passed = outcome['stage_passed']
    write_json(evidence / 'coverage.json', dict(schema='point4-consolidated-stage-coverage-v2',
               **outcome, full_partition=assignment['partition'],
               tooling_source=tooling_pre, executed_proof_source=execution_pre, chart_proof_source=chart_pre,
               chart_execution_root=str(chart_execution), shared_execution_root=str(execution),
               scope='Actual current ToolHEAD with finite legacy Source admission; unchanged baseline Lean reference only; no new mathematical proof credit',
               proof_base_head=plan['current_head_execution']['proof_base_head'], proof_base_tree=plan['current_head_execution']['proof_base_tree'],
               current_legacy_execution_gate=True,
               projection_witness=projection, toolchain=toolchain, compiled_cache_provenance=cache_provenance, native_initial_full_build=seed,
               provider_context=dict(actual_tooling_GITHUB_SHA=os.environ.get('GITHUB_SHA'),
                                     run_id=os.environ.get('GITHUB_RUN_ID'),attempt=os.environ.get('GITHUB_RUN_ATTEMPT'),
                                     actual_tooling_GITHUB_WORKSPACE=provider_workspace,
                                     executed_GITHUB_WORKSPACE=str(execution)),
               stopped_after_first_failure=stopped, completed_case_count=len(results),
               original_workflows=33, original_jobs=35, global_budget_seconds=args.budget_seconds,
               legacy_hosted_statuses_created=False, jobs=results, artifact_totals=context['counters'],
               output_inventory=output_inventory))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
