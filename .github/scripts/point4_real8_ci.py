#!/usr/bin/env python3
"""Exact PR146 current guard and original eight real-runtime routes.

Historical audit/probe inputs retain their original attribution. Cache retrieval
provides compiler inputs; it supplies no proof or runtime PASS result.
"""
from __future__ import annotations

import argparse
import ctypes
import hashlib
import importlib.metadata
import importlib.util
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import time
import urllib.request
import zipfile

PROOF_SHA = '589f451ab90f0e258318dd07d2624dec7c399402'
PROOF_TREE = 'ea54a41a423c93dc379a310aebf9579fa3259c3f'
LEAN_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
MATHLIB_SHA = 'db584cd6d46c92f209a44c0f1c829460d327499d'
OFFICIAL_COMPILER_FILES = {
    'bin/lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'bin/lake': '60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3',
    'lib/lean/libleanshared.so': 'f2a36d5e56b936afc07bdbea18542de0bce6a9977ebc325915272c300d992d42',
}
LOG_LIMIT = 16 * 1024**2
EVIDENCE_LIMIT = 128 * 1024**2
RSS_LIMIT = 6 * 1024**3
CONTEXT = Path('/tmp/point4-smooth-forward-composition-inputs.log')
SIGNALS = (signal.SIGINT, signal.SIGTERM)
EXECUTION_DEADLINE = None


def require(value, message):
    if not value:
        raise ValueError(message)


def pin(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def read_regular(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode), 'Nonregular input: ' + str(path))
        chunks = []
        while chunk := os.read(fd, 1024 * 1024):
            chunks.append(chunk)
        after = os.fstat(fd)
        require(all(getattr(before, key) == getattr(after, key) for key in
                    ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')),
                'Input changed during read: ' + str(path))
        return b''.join(chunks)
    finally:
        os.close(fd)


def identity(path):
    return pin(read_regular(path))


def evidence_size(root):
    total = 0
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'Evidence symlink')
        if p.is_file():
            total += p.stat().st_size
    return total


def write_json(path, value):
    raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    previous = path.stat().st_size if path.exists() else 0
    require(evidence_size(path.parent) - previous + len(raw) <= EVIDENCE_LIMIT,
            'Evidence metadata bound exceeded')
    require(not path.is_symlink(), 'Receipt symlink')
    path.write_bytes(raw)


def git(root, *args):
    return subprocess.check_output(['git', '--no-replace-objects', '-c', 'core.fsmonitor=false',
        '-C', str(root), *args], timeout=20, env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).decode().strip()


def snapshot(root):
    require(not git(root, 'status', '--porcelain', '--untracked-files=normal'), 'Dirty source tree')
    rows = subprocess.check_output(['git', '-C', str(root), 'ls-files', '--stage', '-z'], timeout=20)
    files = {}
    for row in rows.split(b'\0'):
        if not row:
            continue
        meta, name = row.decode().split('\t', 1)
        mode, blob, stage = meta.split()
        require(stage == '0' and mode in ('100644', '100755', '120000'), 'Unsupported source index entry')
        p = root / name
        require(not any(parent.is_symlink() for parent in p.parents), 'Source symlink parent')
        if mode == '120000':
            require(p.is_symlink(), 'Expected literal source symlink')
            raw = os.fsencode(os.readlink(p))
            actual_mode = '120000'
        else:
            raw = read_regular(p)
            actual_mode = '100755' if p.stat().st_mode & 0o111 else '100644'
        actual_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(mode == actual_mode and blob == actual_blob, 'Physical source/index mismatch: ' + name)
        files[name] = {'mode': mode, 'blob': blob, **pin(raw)}
    return {'head': git(root, 'rev-parse', 'HEAD'), 'tree': git(root, 'rev-parse', 'HEAD^{tree}'),
            'index_tree': git(root, 'write-tree'), 'files': files}


def proc_table():
    rows = {}
    for p in Path('/proc').iterdir():
        if not p.name.isdecimal():
            continue
        try:
            fields = (p / 'stat').read_text().rsplit(')', 1)[1].split()
            rows[int(p.name)] = {'state': fields[0], 'ppid': int(fields[1]),
                'pgrp': int(fields[2]), 'start_ticks': int(fields[19]),
                'rss': int(fields[21]) * os.sysconf('SC_PAGE_SIZE')}
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError as exc:
            raise ValueError('Unreadable ownership metadata') from exc
    return rows


def owned_processes():
    rows = proc_table()
    owners = {os.getpid()}
    while True:
        additions = {pid for pid, row in rows.items() if row['ppid'] in owners}
        if additions <= owners:
            break
        owners |= additions
    return {pid: rows[pid] for pid in owners - {os.getpid()}}


def signal_owned(sig):
    rows = owned_processes()
    groups = {r['pgrp'] for r in rows.values() if r['state'] not in ('Z', 'X')}
    for group in groups:
        require(group > 0 and group != os.getpgrp(), 'Unsafe owned process group')
        try:
            os.killpg(group, sig)
        except ProcessLookupError:
            pass
    return sorted(groups)


def cleanup(child):
    record = {'TERM_groups': signal_owned(signal.SIGTERM), 'adopted_reaped': []}
    deadline = time.monotonic() + 3
    while time.monotonic() < deadline:
        child.poll()
        if not any(r['state'] not in ('Z', 'X') for r in owned_processes().values()):
            break
        time.sleep(0.025)
    record['KILL_groups'] = signal_owned(signal.SIGKILL)
    child.wait(timeout=3)
    deadline = time.monotonic() + 3
    while True:
        while True:
            try:
                pid, status_value = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                break
            if not pid:
                break
            record['adopted_reaped'].append({'pid': pid, 'wait_status': status_value})
        if not owned_processes():
            break
        require(time.monotonic() < deadline, 'Owned descendants remain after cleanup')
        signal_owned(signal.SIGKILL)
        time.sleep(0.025)
    record.update(leader_reaped=True, no_live_owned_descendants=True,
                  ownership='Linux subreaper and complete PPID closure, including nested sessions')
    return record


def run_process(argv, cwd, evidence, label, timeout, env=None):
    """Signal-safe publication of child ownership; all descendants are reaped."""
    require(not owned_processes(), 'Earlier owned descendants remain')
    require(ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) == 0, 'Subreaper unavailable')
    started = time.monotonic()
    if EXECUTION_DEADLINE is not None:
        timeout = min(timeout, EXECUTION_DEADLINE - started)
        require(timeout > 0, 'Cumulative execution deadline exhausted before ' + label)
    row = {'argv': list(map(str, argv)), 'cwd': str(cwd), 'timeout_seconds': timeout,
           'once_attempt_count': 1, 'peak_sampled_owned_RSS_bytes': 0}
    child, failure, closure = None, None, None
    selector = selectors.DefaultSelector()
    logpath = evidence / (label + '.log')
    fd = os.open(logpath, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    handlers = {s: signal.getsignal(s) for s in SIGNALS}
    initial_mask = signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)

    def stopped(number, _frame):
        # selectors treats InterruptedError as an ordinary interrupted syscall.
        # Use a distinct exception so termination cannot be silently retried.
        raise ValueError('Supervisor signal ' + str(number))

    def child_setup():
        signal.pthread_sigmask(signal.SIG_SETMASK, initial_mask)
        # Only validators generate additional ordinary log files. Applying this
        # limit to cache retrieval or compilation would truncate valid oleans.
        if label in ('current-guard-producer', 'original-eight-real-runtime'):
            resource.setrlimit(resource.RLIMIT_FSIZE, (LOG_LIMIT, LOG_LIMIT))

    try:
        for sig in SIGNALS:
            signal.signal(sig, stopped)
        try:
            child = subprocess.Popen(row['argv'], cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
                preexec_fn=child_setup)
            row['pid'] = child.pid
            selector.register(child.stdout, selectors.EVENT_READ)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, initial_mask)
        while True:
            for key, _ in selector.select(timeout=0.025):
                data = os.read(key.fileobj.fileno(), 65536)
                if not data:
                    selector.unregister(key.fileobj)
                    continue
                require(os.fstat(fd).st_size + len(data) <= LOG_LIMIT, 'Stage log exceeded 16MiB')
                require(evidence_size(evidence) + len(data) <= EVIDENCE_LIMIT - 8 * 1024**2,
                        'Evidence reserve reached')
                view = memoryview(data)
                while view:
                    view = view[os.write(fd, view):]
            owned = owned_processes()
            rss = proc_table()[os.getpid()]['rss'] + sum(r['rss'] for r in owned.values())
            row['peak_sampled_owned_RSS_bytes'] = max(row['peak_sampled_owned_RSS_bytes'], rss)
            require(rss <= RSS_LIMIT, 'Sampled aggregate owned RSS exceeded 6GiB')
            require(os.fstat(fd).st_size <= LOG_LIMIT, 'Stage log exceeded 16MiB')
            require(evidence_size(evidence) <= EVIDENCE_LIMIT - 8 * 1024**2, 'Evidence reserve reached')
            code = child.poll()
            if code is not None:
                require(code == 0, label + ' exited ' + str(code))
                require(not any(r['state'] not in ('Z', 'X') for r in owned_processes().values()),
                        'Successful leader left live descendants')
                if not selector.get_map():
                    break
            require(time.monotonic() - started < timeout, label + ' exceeded execution wall bound')
    except BaseException as exc:
        failure = exc
    finally:
        signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
        try:
            if child is not None:
                closure = cleanup(child)
        except BaseException as exc:
            row['cleanup_error'] = str(exc)
            failure = failure or exc
        finally:
            selector.close()
            if child is not None and child.stdout is not None:
                child.stdout.close()
            os.close(fd)
            row.update(exit_code=child.returncode if child else None,
                       elapsed_seconds=time.monotonic() - started, closure=closure,
                       log=identity(logpath), error=None if failure is None else str(failure))
            try:
                write_json(evidence / (label + '.json'), row)
            finally:
                for sig, handler in handlers.items():
                    signal.signal(sig, handler)
                signal.pthread_sigmask(signal.SIG_SETMASK, initial_mask)
    if failure:
        raise failure
    return read_regular(logpath)


def focused_order(proof, description):
    spec = importlib.util.spec_from_file_location('real8_source_scanner', proof / 'curvature/scripts/point4_scan.py')
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    visited, order, roots = set(), [], set()

    def visit(name):
        if name.startswith('Mathlib.'):
            roots.add(name)
            return
        if name in {'Init', 'Lean', 'Std'} or name.startswith(('Init.', 'Lean.', 'Std.')):
            return
        if name in visited:
            return
        require(name in description['project_modules'], 'Unadmitted import: ' + name)
        visited.add(name)
        source = proof / description['project_modules'][name]['path']
        code = '\n'.join(scanner.strip_comments(source.read_text()))
        imports = [v for group in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', code, re.M)
                   for v in group.split()]
        require(imports == description['project_modules'][name]['imports'], 'Import descriptor drift')
        for dep in imports:
            visit(dep)
        order.append(name)

    visit(description['historical_probe']['native_import'])
    require(len(visited) == 21 and visited == set(description['project_modules']) and
            sorted(roots) == description['Mathlib_roots'] and len(roots) == 38, 'Native closure drift')
    return order


def recover_inputs(description, work, evidence):
    """One supported public artifact transfer; signed redirect locations are not recorded."""
    url = ('https://api.github.com/repos/Arthur742Ramos/lean-poincare-formalization-plan/'
           'actions/artifacts/12001365510/zip')
    request = urllib.request.Request(url, headers={'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'point4-current-guard-verification'})
    with urllib.request.urlopen(request, timeout=60) as response:
        raw = response.read(description['archive']['bytes'] + 1)
    require(pin(raw) == description['archive'], 'Canonical artifact whole-byte mismatch')
    members = description['archive_members']
    root = work / 'preserved-inputs'
    root.mkdir(mode=0o700)
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        infos = archive.infolist()
        require(len(infos) == len(members) == 52 and {i.filename for i in infos} == set(members),
                'Artifact namespace or duplicate mismatch')
        selected = {}
        for info in infos:
            name, expected = info.filename, members[info.filename]
            path = PurePosixPath(name)
            require(not path.is_absolute() and '..' not in path.parts and not info.is_dir(), 'Unsafe ZIP member')
            require(info.file_size == expected['bytes'] and info.CRC == expected['CRC32'], 'ZIP metadata drift')
            data = archive.read(info)
            require(pin(data) == {k: expected[k] for k in ('bytes', 'sha256')}, 'Artifact member hash drift')
            if expected['selected_for_preserved_guard_inputs']:
                data.decode('utf-8', errors='strict')
                dest = root / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
                selected[name] = identity(dest)
    require(len(selected) == 19 and sum(v['bytes'] for v in selected.values()) == 85420, 'Input selection drift')
    write_json(evidence / 'historical-input-provenance.json', {
        'origin': description['historical_input_origin'], 'archive': description['archive'],
        'all_52_namespace_sizes_hashes_CRC_verified': True, 'selected_19': selected,
        'fresh_audit_or_historical_execution_claimed': False, 'raw_historical_inputs_uploaded': False})
    return root, selected


def input_snapshot(root, names):
    return {name: {'identity': identity(root / name),
                  'stat': {key: getattr((root / name).stat(), key) for key in
                           ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')}}
            for name in names}


def compiled_snapshot(pkg):
    roots = [pkg / '.lake/build', *(pkg / '.lake/packages').glob('*/.lake/build')]
    result = {}
    for root in roots:
        if not root.exists():
            continue
        for path in sorted(root.rglob('*')):
            require(not path.is_symlink(), 'Compiled namespace symlink')
            if path.is_file():
                result[str(path.relative_to(pkg))] = identity(path)
    # Lake package configurations live outside build/. Their compiled bytes are
    # also part of the executable readset used by every genuine `lake env`.
    for lake in [pkg / '.lake', *(pkg / '.lake/packages').glob('*/.lake')]:
        if lake.exists():
            for path in sorted(lake.iterdir()):
                if path.is_file():
                    result[str(path.relative_to(pkg))] = identity(path)
    require(result, 'Empty compiled readset')
    return result


def python_command(proof, script, arguments):
    program = ('import runpy,sys;sys.path.insert(0,sys.argv[1]);'
               'p=sys.argv[2];sys.argv=[p]+sys.argv[3:];runpy.run_path(p,run_name="__main__")')
    return [sys.executable, '-I', '-B', '-c', program, str(proof / 'curvature/scripts'),
            str(proof / 'curvature/scripts' / script), *arguments]


def guard_arguments(root):
    values = [('--schema', root / 'point4-manifold-heat-official-schema.json'),
        ('--probe-log', root / 'point4-manifold-heat-probe.log'),
        ('--axiom-dir', root / 'point4-manifold-heat-inherited-probes'),
        ('--audit-json', root / 'point4-manifold-heat-full-audit.json'), ('--audit-rc', '1'),
        ('--smooth-probe-log', root / 'point4-smooth-forward-support-probe.log'),
        ('--smooth-completion-log', root / 'point4-smooth-forward-completion.log'),
        ('--smooth-completion-rc', '1'),
        ('--smooth-audit-json', root / 'point4-smooth-forward-audit/verdict.json'), ('--smooth-audit-rc', '1')]
    return [str(v) for pair in values for v in pair]


def check_real8_output(raw, names):
    text = raw.decode('utf-8', errors='strict')
    observed = re.findall(r'^(test_\w+) \(__main__\.RealValidatorTests\.\1\) \.\.\. ok$', text, re.M)
    require(observed == sorted(names), 'Missing, skipped, repeated or unsuccessful original real route')
    require(re.search(r'\nRan 8 tests in [0-9.]+s\n\nOK\s*$', text), 'Missing complete eight-test success footer')


def preflight(args):
    proof, control, evidence = args.candidate_root.resolve(), args.control_root.resolve(), args.evidence.resolve()
    require(proof != control and proof not in evidence.parents and control not in evidence.parents, 'Overlapping workspaces')
    evidence.mkdir(parents=True, exist_ok=True)
    require(args.candidate_sha == PROOF_SHA and args.expected_tree == PROOF_TREE, 'Unreviewed candidate')
    require(re.fullmatch('[0-9a-f]{40}', args.caller_sha), 'Invalid caller SHA')
    require(git(proof, 'rev-parse', 'HEAD') == PROOF_SHA and git(proof, 'rev-parse', 'HEAD^{tree}') == PROOF_TREE,
            'Candidate identity drift')
    require(git(control, 'rev-parse', 'HEAD') == args.caller_sha, 'Caller identity drift')
    description = json.loads(read_regular(Path(__file__).with_name('point4_real8_sources.json')))
    require(description['candidate_commit'] == PROOF_SHA and description['candidate_tree'] == PROOF_TREE, 'Descriptor identity drift')
    for item in [*description['project_modules'].values(), *[
            dict(path=path, **value) for path, value in description['current_control_sources'].items()]]:
        require(identity(proof / item['path']) == {k: item[k] for k in ('bytes', 'sha256')}, 'Source pin drift: ' + item['path'])
    probe = description['historical_probe']
    raw = subprocess.check_output(['git', '-C', str(proof), 'show', probe['commit'] + ':' + probe['path']], timeout=20)
    require(pin(raw) == {k: probe[k] for k in ('bytes', 'sha256')}, 'Historical six-entry probe drift')
    require((proof / 'curvature/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0', 'Toolchain pin drift')
    focused_order(proof, description)
    return proof, control, evidence, description


def main(args):
    proof, control, evidence, description = preflight(args)
    if args.phase == 'preflight':
        require(not (evidence / 'preflight.json').exists(), 'Preflight already exists')
        write_json(evidence / 'preflight.json', {'proof': snapshot(proof), 'control': snapshot(control)})
        return
    before = json.loads(read_regular(evidence / 'preflight.json'))
    require(before == {'proof': snapshot(proof), 'control': snapshot(control)}, 'Source changed after preflight')
    require(tempfile.gettempdir() == '/tmp' and not CONTEXT.exists() and not CONTEXT.is_symlink(), 'Context must be newly produced at original /tmp path')
    require(not list(Path('/tmp').glob('point4-smooth-forward-positive-*')), 'Pre-existing positive-route output')
    require(sys.flags.optimize == 0 and sys.version_info >= (3, 12), 'Assertions and Python3.12 required')
    require(importlib.metadata.version('PyYAML') == '6.0.2' and importlib.metadata.version('jsonschema') == '4.23.0', 'Python package drift')
    require(not any(os.environ.get(k) for k in ('MATHLIB_CACHE_GET_URL', 'MATHLIB_CACHE_FROM',
        'MATHLIB_CACHE_REPO_SCOPE', 'MATHLIB_CACHE_SAS', 'MATHLIB_CACHE_AZURE_BEARER_TOKEN')), 'Cache override forbidden')
    work = args.work.resolve()
    require(not work.exists() and work != evidence and evidence not in work.parents and work not in evidence.parents,
            'Fresh separate nonpublished workdir required')
    work.mkdir(mode=0o700, parents=True)
    global EXECUTION_DEADLINE
    # The outer kernel service has 15000 seconds. Execution ends by 14500,
    # reserving 500 seconds for reaping, complete readback and final receipts.
    EXECUTION_DEADLINE = time.monotonic() + 14500
    state = {'candidate': PROOF_SHA, 'tree': PROOF_TREE, 'caller': args.caller_sha, 'Point4': 'OPEN',
             'status': 'RUNNING_UNVERIFIED', 'ordinary_controls_replaced': False, 'historical_audits_refreshed': False}
    dependencies, compiled_pre, inputs_pre, inputs = [], None, None, None
    pkg = proof / 'curvature'
    try:
        state['python'] = {'version': sys.version, 'executable': str(Path(sys.executable)),
            'resolved_executable': identity(Path(sys.executable).resolve()), 'PyYAML': '6.0.2', 'jsonschema': '4.23.0'}
        root, selected = recover_inputs(description, work, evidence)
        inputs = root
        inputs_pre = input_snapshot(root, selected)
        version = run_process(['lean', '--version'], pkg, evidence, 'lean-version', 30).decode()
        require('version 4.33.0,' in version and LEAN_COMMIT in version, 'Wrong official compiler')
        prefix = Path(run_process(['lean', '--print-prefix'], pkg, evidence, 'lean-prefix', 30).decode().strip())
        state['compiler'] = {name: identity(prefix / name) for name in OFFICIAL_COMPILER_FILES}
        require(all(state['compiler'][name]['sha256'] == sha for name, sha in OFFICIAL_COMPILER_FILES.items()), 'Official compiler byte drift')
        manifest = json.loads(read_regular(pkg / 'lake-manifest.json'))
        for entry in manifest['packages']:
            if entry['type'] != 'git':
                continue
            require(re.fullmatch('[0-9a-f]{40}', entry['rev']) and re.fullmatch('[A-Za-z0-9_-]+', entry['name']), 'Invalid manifest revision/name')
            require(entry['url'].startswith(('https://github.com/leanprover-community/', 'https://github.com/leanprover/')), 'Unadmitted registry')
            dest = pkg / '.lake/packages' / entry['name']
            require(not dest.exists(), 'Pre-existing dependency')
            dest.mkdir(parents=True)
            name = entry['name']
            for suffix, argv, limit in [
                ('init', ['git', 'init', '--quiet'], 10),
                ('origin', ['git', 'remote', 'add', 'origin', entry['url']], 10),
                ('fetch', ['git', 'fetch', '--no-tags', '--depth=1', 'origin', entry['rev']], 90),
                ('checkout', ['git', 'checkout', '--detach', 'FETCH_HEAD'], 20)]:
                run_process(argv, dest, evidence, 'dependency-' + name + '-' + suffix, limit)
            require(git(dest, 'rev-parse', 'HEAD') == entry['rev'], 'Dependency HEAD mismatch')
            dependencies.append({'name': name, 'root': str(dest), 'rev': entry['rev'], 'source': snapshot(dest)})
        require(len(dependencies) == 9 and next(x['rev'] for x in dependencies if x['name'] == 'mathlib') == MATHLIB_SHA, 'Dependency set drift')
        write_json(evidence / 'dependency-sources.json', dependencies)
        run_process(['lake', 'exe', 'cache', 'get', '--repo=leanprover-community/mathlib4',
            '--cache-from=master,legacy', *description['Mathlib_roots']], pkg, evidence, 'official-cache', 600)
        order = focused_order(proof, description)
        write_json(evidence / 'compile-order.json', order)
        for i, name in enumerate(order):
            output = pkg / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            require(not output.exists(), 'Pre-existing project output')
            source = Path(description['project_modules'][name]['path']).relative_to('curvature')
            run_process(['lake', 'env', 'lean', '-j1', '-M5632', '-o', str(output), str(source)], pkg,
                evidence, f'compile-{i:02d}', 720 if name.endswith('.RiemannianSection') else 480)
            require(output.is_file() and output.stat().st_size, 'Missing compiled module')
        compiled_pre = compiled_snapshot(pkg)
        write_json(evidence / 'compiled-PRE.json', compiled_pre)
        arguments = guard_arguments(root)
        run_process(python_command(proof, 'point4_smooth_forward_release_guard.py', arguments),
                    proof, evidence, 'current-guard-producer', 1200)
        context_raw = read_regular(CONTEXT)
        context = json.loads(context_raw)
        require(context == {'head': PROOF_SHA, 'source_only': True, 'validated_current_arguments': arguments},
                'Genuine producer context drift')
        write_json(evidence / 'new-current-context.json', {'context': context, 'raw_identity': pin(context_raw),
            'origin': 'Unmodified current guard after both real routes; original /tmp file consumed by original tests'})
        raw = run_process(python_command(proof, 'point4_smooth_master_composition_test.py',
            ['--real-runtime', '--real-only', '--schema', str(root / 'point4-manifold-heat-official-schema.json')]),
            proof, evidence, 'original-eight-real-runtime', 7500)
        check_real8_output(raw, description['real8_exact_ids'])
        require(read_regular(CONTEXT) == context_raw, 'Current context changed during real8')
        state['status'] = 'CURRENT_GUARD_AND_ORIGINAL_REAL8_PASS_ACTUAL_REVIEW_PENDING'
    except BaseException as exc:
        state.update(status='FAIL_UNVERIFIED', error=str(exc))
        raise
    finally:
        try:
            require(before == {'proof': snapshot(proof), 'control': snapshot(control)}, 'Source PRE/POST mismatch')
            for dep in dependencies:
                require(snapshot(Path(dep['root'])) == dep['source'], 'Dependency source PRE/POST drift')
            state['source_PRE_POST_equal'] = True
            if compiled_pre is not None:
                compiled_post = compiled_snapshot(pkg)
                write_json(evidence / 'compiled-POST.json', compiled_post)
                require(compiled_post == compiled_pre, 'Compiled readset PRE/POST drift')
                state['compiled_PRE_POST_equal'] = True
            if inputs_pre is not None:
                require(input_snapshot(inputs, inputs_pre) == inputs_pre, 'Preserved19 input identity/content drift')
                state['preserved19_PRE_POST_equal'] = True
            routing = [] if inputs is None else list(inputs.glob('*-historical-routing.log'))
            for path in routing:
                raw = read_regular(path)
                require(len(raw) <= LOG_LIMIT and evidence_size(evidence) + len(raw) < EVIDENCE_LIMIT - 1024**2,
                        'Routing receipt aggregate overflow')
                (evidence / path.name).write_bytes(raw)
            for path in Path('/tmp').glob('point4-smooth-forward-positive-*'):
                if path.is_file():
                    raw = read_regular(path)
                    require(len(raw) <= LOG_LIMIT and evidence_size(evidence) + len(raw) < EVIDENCE_LIMIT - 1024**2,
                            'Positive receipt aggregate limit')
                    (evidence / path.name).write_bytes(raw)
            require(not owned_processes(), 'Final owned descendants remain')
            state['no_live_owned_descendants'] = True
        except BaseException as exc:
            state.update(status='FAIL_POST_VERIFICATION', post_error=str(exc))
            raise
        finally:
            write_json(evidence / 'outcome.json', state)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('preflight', 'verify'), required=True)
    for flag in ('candidate-root', 'control-root', 'evidence', 'work'):
        parser.add_argument('--' + flag, type=Path, required=True)
    for flag in ('candidate-sha', 'expected-tree', 'caller-sha'):
        parser.add_argument('--' + flag, required=True)
    main(parser.parse_args())
