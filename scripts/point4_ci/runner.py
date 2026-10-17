#!/usr/bin/env python3
"""Run Source-frozen legacy Point-4 cases serially with a shared native build.

This is a new consolidated protocol. It does not create historical workflow
statuses, qualify new mathematical statements, or infer success from cache hits.
"""
from __future__ import annotations

import argparse
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
    path = root / ('scripts/point4_tooling_overlay.py' if function == 'verify_tooling_overlay'
                   else 'curvature/scripts/point4_smooth_master_composition.py')
    spec = importlib.util.spec_from_file_location('point4_consolidated_source_' + function, path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(path.parent))
    try:
        spec.loader.exec_module(module)
        return getattr(module, function)(*args)
    finally:
        sys.path.pop(0)


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
    args = parser.parse_args()
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
    tooling_pre = source_identity(tooling, args.expected_sha, args.expected_tree)
    projection = source_guard(tooling, 'verify_tooling_overlay', args.expected_sha)
    execution_head = plan['baseline_master']
    execution_tree = subprocess.check_output(['git', '--no-replace-objects', '-C', str(execution), 'rev-parse', 'HEAD^{tree}']).decode().strip()
    execution_pre = source_identity(execution, execution_head, execution_tree)
    chart_pre = source_identity(chart_execution, execution_head, execution_tree)
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
               scope='Master proof Sources with independently admitted finite tooling overlay; no PR146 new-proof credit',
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
