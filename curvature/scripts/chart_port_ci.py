"""Rebuild the admitted chart closure serially; never substitute old receipts."""
from pathlib import Path
import argparse, hashlib, json, os, re, signal, subprocess, sys, time
from chart_port_candidate_check import admit, check_probe, check_ricci_extension_probe, digest, imports, tree_entries, package_root_relationships
from chart_port_artifacts import artifact_status, required_import_files

LIMIT = 6 * 1024 ** 3
ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / 'curvature'
ap = argparse.ArgumentParser()
ap.add_argument('--expected-sha', required=True)
ap.add_argument('--expected-tree', required=True)
ap.add_argument('--evidence', type=Path, required=True)
ap.add_argument('--setup-only', action='store_true',
                help='Check pinned environment setup only; full qualification remains required')
args = ap.parse_args()
args.evidence.mkdir(parents=True, exist_ok=False)
EVIDENCE = args.evidence.resolve()
receipt = dict(owner_pid=os.getpid(), candidate_sha=args.expected_sha, candidate_tree=args.expected_tree,
               source_admission='PENDING', build='RUNNING', point4='OPEN', general_targets='OPEN', stages=[],
               mode='SETUP_ONLY' if args.setup_only else 'FULL_QUALIFICATION',
               environment_setup='PENDING', full_candidate_qualification='NOT_RUN')

class _SetupOnlyComplete(Exception):
    pass

def save():
    (EVIDENCE / 'run.json').write_text(json.dumps(receipt, indent=2) + '\n')

def owned_process_identity(p, initial_stat):
    # Diagnostic reads precede cleanup. A failed/raced read never earns an exemption.
    row = dict(pid=int(p.name), observed_at=time.time(), state=initial_stat[0],
        ppid=int(initial_stat[1]), pgrp=int(initial_stat[2]), session=int(initial_stat[3]),
        starttime_ticks=int(initial_stat[19]), rss_bytes=int(initial_stat[21]) * os.sysconf('SC_PAGE_SIZE'),
        stable=False, errors=[], verified_terminated_zombie=False)
    try:
        row['exe'] = os.readlink(p / 'exe')
        image = (p / 'exe').stat()
        row['image_identity'] = [image.st_dev, image.st_ino, image.st_size, image.st_mtime_ns, image.st_ctime_ns]
        raw = (p / 'cmdline').read_bytes()
        row['cmdline_hex'] = raw.hex()
        if not raw or not raw.endswith(b'\0'):
            raise ValueError('Empty or unterminated process argv')
        row['argv'] = [arg.decode('utf8') for arg in raw[:-1].split(b'\0')]
        if Path(row['exe']).name == 'lean':
            row['exe_sha256'] = digest((p / 'exe').read_bytes())
        again = (p / 'stat').read_text().rsplit(')', 1)[1].split()
        row['recheck'] = dict(state=again[0], ppid=int(again[1]), pgrp=int(again[2]),
            session=int(again[3]), starttime_ticks=int(again[19]))
        # Retain each observed field before attempting the next fallible read.
        row['recheck']['exe'] = os.readlink(p / 'exe')
        row['recheck']['cmdline_hex'] = (p / 'cmdline').read_bytes().hex()
        image = (p / 'exe').stat()
        row['recheck']['image_identity'] = [image.st_dev, image.st_ino, image.st_size, image.st_mtime_ns, image.st_ctime_ns]
        keys = ('ppid', 'pgrp', 'session', 'starttime_ticks', 'exe', 'cmdline_hex', 'image_identity')
        row['stable'] = all(row[k] == row['recheck'][k] for k in keys)
        if not row['stable']:
            row['errors'].append(dict(type='IdentityRace', message='Process identity changed during observation'))
    except (OSError, ValueError, UnicodeError, IndexError) as exc:
        row['errors'].append(dict(type=type(exc).__name__, message=str(exc)))
    if row['state'] == 'Z':
        # A terminal state is not an executable/query exemption. Verify the
        # same kernel identity remains Z after all fallible image reads.
        row['terminal_errors'] = []
        try:
            raw_stat = (p / 'stat').read_text()
            terminal = raw_stat.rsplit(')', 1)[1].split()
            row['terminal_recheck'] = dict(pid=int(raw_stat.split(' ', 1)[0]),
                state=terminal[0], ppid=int(terminal[1]), pgrp=int(terminal[2]),
                session=int(terminal[3]), starttime_ticks=int(terminal[19]),
                rss_bytes=int(terminal[21]) * os.sysconf('SC_PAGE_SIZE'))
            check = row['terminal_recheck']
            keys = ('pid', 'ppid', 'pgrp', 'session', 'starttime_ticks')
            row['verified_terminated_zombie'] = (check['state'] == 'Z'
                and row['rss_bytes'] == check['rss_bytes'] == 0
                and row['pgrp'] == row['session']
                and all(row[key] == check[key] for key in keys))
            if not row['verified_terminated_zombie']:
                row['terminal_errors'].append(dict(type='TerminalIdentityMismatch',
                    message='Terminal state or kernel process identity changed'))
        except (OSError, ValueError, UnicodeError, IndexError) as exc:
            row['terminal_errors'].append(dict(type=type(exc).__name__, message=str(exc)))
    row['rechecked_at'] = time.time()
    return row

def pinned_cache_query_context(mathlib, roots):
    # These exact pinned sources execute Cache.IO's leantar prefix initializer.
    source, initializer = mathlib / 'Cache/Main.lean', mathlib / 'Cache/IO.lean'
    assert digest(source.read_bytes()) == 'dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044', 'Pinned Cache.Main source changed'
    assert digest(initializer.read_bytes()) == '8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82', 'Pinned Cache.IO initializer changed'
    assert isinstance(roots, list) and roots and all(isinstance(name, str)
        and name.startswith('Mathlib.') and all(part.isidentifier() for part in name.split('.')) for name in roots)
    return dict(mathlib_pin='db584cd6d46c92f209a44c0f1c829460d327499d',
        package_root=str(mathlib), source=str(source), source_sha256='dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044',
        initializer=str(initializer), initializer_sha256='8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82', admitted_roots=list(roots))

def is_exact_official_prefix_query(row, owner, stage_argv, official, cache_context=None):
    # Independently reviewable predicate: setting this to False retains diagnostics
    # and the original strict compiler count. No grace period or pre-exec exclusion.
    try:
        if official['compiler_commit'] != 'd8b18978322de05a8f3dba51ef03cf5461676c17':
            return False
        path, identity = official['compiler_path'], official['compiler_sha256']
        compile_owner = (stage_argv[0] == path
            and all(flag in stage_argv for flag in ('-j1', '-M5632', '-o', '-c'))
            and stage_argv[-1].endswith('.lean'))
        cache_owner = False
        if cache_context is not None:
            context = cache_context
            root, roots = context['package_root'], context['admitted_roots']
            cache_owner = (context['mathlib_pin'] == 'db584cd6d46c92f209a44c0f1c829460d327499d'
                and context['source'] == root + '/Cache/Main.lean'
                and context['source_sha256'] == 'dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044'
                and context['initializer'] == root + '/Cache/IO.lean'
                and context['initializer_sha256'] == '8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82'
                and isinstance(roots, list) and bool(roots) and all(isinstance(name, str)
                    and name.startswith('Mathlib.') and all(part.isidentifier() for part in name.split('.')) for name in roots)
                and list(stage_argv) == [path, '-j1', '-M5632', '-R', root, '--run', context['source'], 'get', *roots])
        if not (compile_owner or cache_owner):
            return False
        for process in (row, owner):
            if not process['stable'] or process['errors'] or process['state'] not in ('R', 'S', 'D', 'I'):
                return False
            if process['recheck']['state'] not in ('R', 'S', 'D', 'I'):
                return False
            if process['exe'] != path or process['exe_sha256'] != identity:
                return False
        return (row['pid'] != owner['pid'] and row['ppid'] == owner['pid']
            and row['session'] == row['pgrp'] == owner['session'] == owner['pgrp'] == owner['pid']
            and row['starttime_ticks'] >= owner['starttime_ticks']
            and row['image_identity'] == owner['image_identity']
            and owner['argv'] == list(stage_argv)
            and row['argv'] in (['lean', '--print-prefix'], [path, '--print-prefix']))
    except (KeyError, TypeError, IndexError):
        return False

def run(argv, label, cwd=PKG, env=None, timeout=600, cache_query_context=None):
    stage = dict(argv=argv, cwd=str(cwd), timeout_seconds=timeout, started=time.time(), status='STARTING', peak_rss_bytes=0)
    if cache_query_context is not None:
        stage['cache_query_context'] = cache_query_context
    receipt['stages'].append(stage)
    save()
    start = time.monotonic()
    proc = None
    try:
        with (EVIDENCE / (label + '.stdout')).open('wb') as stdout, (EVIDENCE / (label + '.stderr')).open('wb') as stderr:
            proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
            stage.update(pid=proc.pid, status='RUNNING')
            save()
            while proc.poll() is None:
                rss, compilers, identities = 0, 0, []
                for p in Path('/proc').iterdir():
                    if not p.name.isdigit():
                        continue
                    try:
                        stat = (p / 'stat').read_text().rsplit(')', 1)[1].split()
                        if int(stat[3]) != proc.pid:  # session ID, not command text
                            continue
                        rss += int(stat[21]) * os.sysconf('SC_PAGE_SIZE')
                        identities.append(owned_process_identity(p, stat))
                    except (FileNotFoundError, ProcessLookupError, PermissionError):
                        continue  # No owned identity was observed by this stat read.
                owner = next((row for row in identities if row['pid'] == proc.pid), {})
                for row in identities:
                    # An unreadable executable is conservatively counted. Once a
                    # Lean image was observed, disappearance/race still counts it.
                    counted = 'exe' not in row or any(Path(exe).name == 'lean'
                        for exe in (row.get('exe'), row.get('recheck', {}).get('exe')) if exe is not None)
                    query = counted and is_exact_official_prefix_query(row, owner, argv, receipt, cache_query_context)
                    terminal = row.get('verified_terminated_zombie') is True
                    row.update(counted_compiler=bool(counted and not query and not terminal),
                        exact_official_prefix_query=bool(query),
                        conservative_executable_count=bool(counted))
                    compilers += row['counted_compiler']
                stage['owned_process_snapshot'] = dict(observed_at=time.time(),
                    owner_pid=proc.pid, counted_compilers=compilers, processes=identities)
                stage['peak_rss_bytes'] = max(stage['peak_rss_bytes'], rss)
                if compilers > 1:
                    raise RuntimeError('More than one Lean compiler in an owned stage')
                if identities and not owner:
                    raise RuntimeError('Owned process identities observed without compiler owner identity')
                if rss > LIMIT:
                    raise RuntimeError('Owned process tree exceeds 6 GiB RSS')
                if time.monotonic() - start > timeout:
                    raise TimeoutError(label)
                time.sleep(0.05)
            stage.update(exit_code=proc.returncode, status='SUCCEEDED' if proc.returncode == 0 else 'FAILED')
    except BaseException as exc:
        stage.update(status='FAILED', exception_type=type(exc).__name__, error=str(exc))
        raise
    finally:
        if proc is not None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=10)
            stage['exit_code'] = proc.returncode
            stage['owner_reaped'] = True
            # Reject surviving members of the owned session, including zombies.
            survivors = []
            for p in Path('/proc').iterdir():
                if not p.name.isdigit():
                    continue
                try:
                    stat = (p / 'stat').read_text().rsplit(')', 1)[1].split()
                    if int(stat[3]) == proc.pid:
                        survivors.append(int(p.name))
                except (FileNotFoundError, ProcessLookupError):
                    continue
            stage['remaining_session_pids'] = survivors
        stage['elapsed_seconds'] = time.monotonic() - start
        for suffix in ('.stdout', '.stderr'):
            p = EVIDENCE / (label + suffix)
            stage[suffix[1:] + '_sha256'] = digest(p.read_bytes())
        save()
    assert stage['exit_code'] == 0, label + ' failed; raw logs retained'
    assert not stage['remaining_session_pids'], 'Owned session not drained'
    return (EVIDENCE / (label + '.stdout')).read_bytes()

def compiler_log_identity(path):
    h = hashlib.sha256(); size = 0
    try:
        with path.open('rb') as stream:
            while data := stream.read(65536):
                h.update(data); size += len(data)
    except OSError as exc:
        return dict(path=str(path), available=False, exception_type=type(exc).__name__, error=str(exc))
    return dict(path=str(path), available=True, bytes=size, sha256=h.hexdigest())

def record_first_compiler_failure(label, argv, source_identity, stage, failure):
    summary = EVIDENCE / 'first-compiler-failure.json'
    if summary.exists():
        return  # Keep the original first failure and its independently bound bytes.
    logs = {suffix: compiler_log_identity(EVIDENCE / (label + '.' + suffix)) for suffix in ('stdout', 'stderr')}
    payload = dict(schema_version=1, candidate_sha=receipt['candidate_sha'], candidate_tree=receipt['candidate_tree'],
        stage=label, argv=list(argv), source_identity=source_identity,
        failure_exception=dict(type=type(failure).__name__, message=str(failure)),
        owned_stage_receipt=dict(stage), logs=logs,
        driver_resource_receipt={k:receipt[k] for k in ('owner_pid', 'memory_limit_bytes', 'cpu_affinity', 'cgroup') if k in receipt},
        point4='OPEN', full_candidate_qualification='NOT_RUN')
    data = (json.dumps(payload, indent=2, ensure_ascii=True) + '\n').encode('utf8')
    try:
        with summary.open('xb') as stream:
            stream.write(data)
        identity = digest(data)
        with (EVIDENCE / 'first-compiler-failure.sha256').open('x', encoding='ascii') as stream:
            stream.write(identity + '  first-compiler-failure.json\n')
        receipt['first_compiler_failure'] = dict(stage=label, summary=str(summary), summary_sha256=identity)
        save()
    finally:
        # Stream both complete retained logs to the job output. No diagnostic
        # text is truncated, decoded, filtered or rewritten; raw files stay put.
        for suffix in ('stdout', 'stderr'):
            sys.stdout.buffer.write(('\n=== first failed compiler stage ' + label + ': ' + suffix + ' ===\n').encode())
            try:
                with (EVIDENCE / (label + '.' + suffix)).open('rb') as stream:
                    while chunk := stream.read(65536):
                        sys.stdout.buffer.write(chunk)
            except OSError as exc:
                sys.stdout.buffer.write(('\nRaw log unavailable: ' + type(exc).__name__ + ': ' + str(exc) + '\n').encode())
            sys.stdout.buffer.flush()

def compiler_run(argv, label, source, module, env=None):
    source_identity = dict(path=str(source), module=module, observed_before_owned_stage=True)
    try:
        data = source.read_bytes()
        source_identity.update(bytes=len(data), sha256=digest(data),
            git_blob_sha=hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest())
    except OSError as exc:
        source_identity.update(identity_read_exception=type(exc).__name__, identity_read_error=str(exc))
    try:
        return run(argv, label, env=env)
    except BaseException as exc:
        stage = receipt['stages'][-1] if receipt['stages'] and receipt['stages'][-1].get('argv') == argv else {}
        try:
            record_first_compiler_failure(label, argv, source_identity, stage, exc)
        except BaseException as reporting_error:
            receipt['first_compiler_failure_reporting_error'] = dict(type=type(reporting_error).__name__, message=str(reporting_error))
            try:
                print('First compiler failure reporting error: ' + repr(reporting_error), flush=True)
            except BaseException:
                pass  # Best-effort output must preserve the original compiler exception.
        raise

def serial_compile(name, source, output_root, lean, env, label, strict=True):
    output = output_root / (name.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    assert not output.exists(), 'Fresh output required'
    argv = [lean, '-j1', '-M5632']
    if strict:
        argv += ['-DautoImplicit=false', '-DmaxSynthPendingDepth=3']
    package_root = source.parents[len(name.split('.')) - 1]
    argv += ['-R', str(package_root)]
    # Emitting C also emits IR used by interpreted Cache code and metaprograms.
    argv += ['-o', str(output), '-c', str(output.with_suffix('.c')), str(source)]
    compiler_run(argv, label, source, name, env=env)
    status = artifact_status(name, [output_root], source.read_bytes())
    assert status['ready'], ('Compiler did not emit required Lean 4.33 import companions', status)
    receipt['stages'][-1].update(source=str(source), source_sha256=digest(source.read_bytes()),
                                  output=str(output), output_sha256=digest(output.read_bytes()))
    receipt['stages'][-1]['import_artifacts'] = [dict(path=str(p), sha256=digest(p.read_bytes())) for p in required_import_files(output, source.read_bytes())]
    save()

try:
    # Hard cgroup limits are applied by the workflow, before this script starts.
    group = next(x.split(':', 2)[2] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup') / group.lstrip('/')
    assert (cgroup / 'memory.max').read_text().strip() == str(LIMIT)
    quota, period = map(int, (cgroup / 'cpu.max').read_text().split())
    assert quota <= 2 * period
    cpus = sorted(os.sched_getaffinity(0))[:2]
    assert cpus
    os.sched_setaffinity(0, cpus)
    receipt.update(cpu_affinity=cpus, memory_limit_bytes=LIMIT, cgroup=str(cgroup))
    admission = admit(ROOT, args.expected_sha, args.expected_tree)
    (EVIDENCE / 'admission.json').write_text(json.dumps(admission, indent=2) + '\n')
    receipt['source_admission'] = 'PASSED'
    save()
    assert (PKG / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0'
    version = run(['lean', '--version'], 'compiler-version').decode()
    compiler_commit = run(['lean', '--githash'], 'compiler-commit').decode().strip()
    assert 'version 4.33.0,' in version
    assert compiler_commit == 'd8b18978322de05a8f3dba51ef03cf5461676c17'
    compiler_prefix = Path(run(['lean', '--print-prefix'], 'compiler-prefix').decode().strip())
    lean = str(compiler_prefix / 'bin/lean')
    receipt.update(compiler_path=lean, compiler_sha256=digest(Path(lean).read_bytes()), compiler_commit=compiler_commit)
    # lake env loads the exact TOML/path dependency configuration and pinned manifest.
    env = os.environ.copy()
    env['MATHLIB_CACHE_DIR'] = str(EVIDENCE / 'ordinary-mathlib-downloads')
    env_raw = run(['lake', 'env', 'python3', '-c', 'import json,os;print(json.dumps({k:os.environ.get(k, "") for k in ("LEAN_PATH", "LEAN_SRC_PATH")}))'], 'lake-environment', env=env)
    env.update(json.loads(env_raw))
    mathlib = PKG / '.lake/packages/mathlib'
    actual_pin = subprocess.check_output(['git', '--no-replace-objects', '-C', str(mathlib), 'rev-parse', 'HEAD']).decode().strip()
    assert actual_pin == 'db584cd6d46c92f209a44c0f1c829460d327499d'
    assert not subprocess.check_output(['git', '--no-replace-objects', '-C', str(mathlib), 'status', '--porcelain', '--untracked-files=no'])
    manifest = json.loads((PKG / 'lake-manifest.json').read_text())
    # Observe actual roots before any dependency link/admission failure. This
    # receipt is diagnostic and does not permit symlinked package roots.
    root_receipt = package_root_relationships(ROOT, PKG, manifest, env)
    root_receipt_path = EVIDENCE / 'package-root-relationships.json'
    root_receipt_path.write_text(json.dumps(root_receipt, indent=2) + '\n')
    receipt['package_root_relationships_sha256'] = digest(root_receipt_path.read_bytes())
    save()
    dependency_roots = []
    dependency_inventory = {}
    for package in manifest['packages']:
        if package['type'] == 'git':
            dep = PKG / manifest['packagesDir'] / package['name']
            assert subprocess.check_output(['git', '--no-replace-objects', '-C', str(dep), 'rev-parse', 'HEAD']).decode().strip() == package['rev']
            assert not subprocess.check_output(['git', '--no-replace-objects', '-C', str(dep), 'status', '--porcelain', '--untracked-files=no'])
            dependency_roots.append(dep.resolve())
            dependency_inventory[dep.relative_to(ROOT).as_posix()] = tree_entries(dep, 'HEAD')
    configured_admission = admit(ROOT, args.expected_sha, args.expected_tree, dependency_inventory)
    (EVIDENCE / 'configured-admission.json').write_text(json.dumps(configured_admission, indent=2) + '\n')
    receipt['environment_setup'] = 'PASSED'
    save()
    if args.setup_only:
        receipt.update(build='SETUP_ONLY_PASSED', fresh_local_modules=0, fresh_probe=0,
                       cgroup_peak_memory_bytes=int((cgroup / 'memory.peak').read_text()),
                       owner_completion='all setup child stages reaped and drained')
        raise _SetupOnlyComplete
    # All fallback outputs and cache downloads stay under this owned evidence root.
    bootstrap, support, local = [EVIDENCE / p / 'lib/lean' for p in ('cache-bootstrap', 'pinned-support', 'local-rebuild')]
    for p in (bootstrap, support, local):
        p.mkdir(parents=True, exist_ok=False)
    old_path = env.get('LEAN_PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(map(str, (local, support, bootstrap))) + os.pathsep + old_path
    env['MATHLIB_CACHE_DIR'] = str(EVIDENCE / 'ordinary-mathlib-downloads')
    # Parse only pinned source imports for a bounded serial Cache bootstrap.
    source_dirs = [Path(p) for p in env['LEAN_SRC_PATH'].split(os.pathsep) if p]
    source_dirs = [p if p.is_absolute() else PKG / p for p in source_dirs]
    artifact_dirs = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep) if p]
    artifact_dirs = [p if p.is_absolute() else PKG / p for p in artifact_dirs]
    prefix = Path(run([lean, '--print-libdir'], 'compiler-libdir', env=env).decode().strip())
    artifact_dirs.append(prefix)
    source_dirs += [compiler_prefix / 'src/lean', compiler_prefix / 'src/lean/lake']
    def source_path(name):
        options = [p / (name.replace('.', '/') + '.lean') for p in source_dirs]
        return next(p.resolve() for p in options if p.is_file())
    def artifact_exists(name):
        status = artifact_status(name, artifact_dirs, source_path(name).read_bytes())
        if not status['ready']:
            receipt.setdefault('missing_import_companions', {})[name] = status
            save()
        return status['ready']
    def verify_dependency_source(source):
        dep = next(p for p in dependency_roots if source.is_relative_to(p))
        rel = source.relative_to(dep).as_posix()
        blob = subprocess.check_output(['git', '--no-replace-objects', '-C', str(dep), 'rev-parse', 'HEAD:' + rel]).decode().strip()
        data = source.read_bytes()
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
    cache_order, seen, active = [], set(), set()
    def bootstrap_visit(name):
        if name in seen or artifact_exists(name):
            return
        assert name not in active
        assert name.startswith(('Cache.', 'Batteries.', 'Cli.')), 'Unexpected cache bootstrap source ' + name
        active.add(name)
        source = source_path(name)
        verify_dependency_source(source)
        for dep in cache_bootstrap_imports(source.read_bytes()):
            bootstrap_visit(dep)
        active.remove(name)
        seen.add(name)
        cache_order.append((name, source))
        assert len(cache_order) <= 200, 'Cache bootstrap exceeded finite source bound'
    def cache_bootstrap_imports(data):
        # Normalize only a canonical combined header for the unchanged parser.
        # Dependency source authentication and compilation retain original bytes.
        normalized = re.sub(rb'(?m)^([ \t]*)public[ \t]+meta[ \t]+import(?=[ \t])',
                            rb'\1meta import', data)
        return imports(normalized)

    # The selected pinned Mathlib closure needs Batteries.Logic even when
    # Cache.Main's own import closure does not. Keep its output under this
    # owned bootstrap root and use the existing serial, bounded traversal.
    logic_source = source_path('Batteries.Logic')
    assert logic_source == (PKG / '.lake/packages/batteries/Batteries/Logic.lean').resolve(), 'Pinned Batteries.Logic source root drift'
    verify_dependency_source(logic_source)
    assert digest(logic_source.read_bytes()) == 'dcfc3dd1580feebc8a29b6f9d65e32a0eadbce486fd02c5b1ce03c43fcf872ce', 'Pinned Batteries.Logic source drift'
    bootstrap_visit('Batteries.Logic')
    bootstrap_visit('Cache.Main')
    for i, (name, source) in enumerate(cache_order):
        serial_compile(name, source, bootstrap, lean, env, 'cache-bootstrap-' + str(i), name.startswith('Cache.'))
    # The real pinned cache CLI runs interpreted, so Lake cannot spawn a parallel build.
    cache_query_context = pinned_cache_query_context(mathlib, admission['external_mathlib_roots'])
    run([lean, '-j1', '-M5632', '-R', str(mathlib), '--run', str(mathlib / 'Cache/Main.lean'), 'get', *admission['external_mathlib_roots']],
        'ordinary-pinned-cache-read', env=env, timeout=1800, cache_query_context=cache_query_context)
    prov = json.loads((PKG / 'third-party/differential-geometry/SOURCE-PROVENANCE.json').read_text())
    allowed = {r['module']: r for r in prov['mathlib_support_sources']}
    missing_order, seen, active = [], set(), set()
    def support_visit(name):
        if name in seen or artifact_exists(name):
            return
        assert name in allowed, 'Missing artifact outside the bounded 31-module fallback: ' + name
        assert name not in active
        active.add(name)
        source = mathlib / allowed[name]['path']
        verify_dependency_source(source.resolve())
        assert digest(source.read_bytes()) == allowed[name]['sha256'], name
        for dep in imports(source.read_bytes()):
            support_visit(dep)
        active.remove(name)
        seen.add(name)
        missing_order.append((name, source))
    for name in admission['external_mathlib_roots']:
        support_visit(name)
    for i, (name, source) in enumerate(missing_order):
        serial_compile(name, source, support, lean, env, 'pinned-support-' + str(i), True)
    # No restored project artifacts are admitted: rebuild all 13+55+2 sources.
    for i, row in enumerate(admission['closure']):
        source = ROOT / row['path']
        assert digest(source.read_bytes()) == row['sha256']
        if row['module'] == 'ChartPort.ChartIdentityEvidence':
            probe = compiler_run([lean, '-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3', str(source)],
                        'full-type-proof-axiom-probe', source, row['module'], env=env)
            result = check_probe(probe)
            (EVIDENCE / 'probe-verdict.json').write_text(json.dumps(result, indent=2) + '\n')
        else:
            serial_compile(row['module'], source, local, lean, env, 'local-' + str(i), True)
    receipt.update(legacy_geometric_gate='PASSED', fresh_local_modules=70, fresh_probe=1,
                   ricci_extension_gate='RUNNING', fresh_extension_modules=0, fresh_extension_probes=0)
    save()
    contracts = {row['module']: row for row in admission['extension_probe_contracts']}
    extension_emits, extension_probes = 0, 0
    for i, row in enumerate(admission['extension_closure']):
        source = ROOT / row['path']
        assert digest(source.read_bytes()) == row['sha256']
        if row['role'] == 'probe':
            probe = compiler_run([lean, '-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3', str(source)],
                                 'ricci-extension-probe-' + str(i), source, row['module'], env=env)
            result = check_ricci_extension_probe(probe, contracts[row['module']])
            (EVIDENCE / ('ricci-extension-probe-' + str(i) + '-verdict.json')).write_text(json.dumps(result, indent=2) + '\n')
            extension_probes += 1
        else:
            serial_compile(row['module'], source, local, lean, env, 'ricci-extension-local-' + str(i), True)
            extension_emits += 1
        receipt.update(fresh_extension_modules=extension_emits, fresh_extension_probes=extension_probes)
        save()
    assert extension_emits == 13 and extension_probes == 10
    receipt['ricci_extension_gate'] = 'PASSED'
    save()
    final = admit(ROOT, args.expected_sha, args.expected_tree, dependency_inventory)
    assert {k:v for k,v in final.items() if k != 'physical_inventory'} == {k:v for k,v in admission.items() if k != 'physical_inventory'}
    (EVIDENCE / 'final-physical-admission.json').write_text(json.dumps(final, indent=2) + '\n')
    assert not subprocess.check_output(['git', '--no-replace-objects', '-C', str(mathlib), 'status', '--porcelain', '--untracked-files=no'])
    receipt.update(build='PASSED', full_candidate_qualification='PASSED', fresh_local_modules=70, fresh_probe=1, fallback_mathlib_modules=len(missing_order),
                   fresh_combined_modules=83, fresh_combined_probes=11,
                   admitted_local_modules=94,
                   ordinary_dependency_artifacts='pinned cache imports; not a full dependency rebuild',
                   cgroup_peak_memory_bytes=int((cgroup / 'memory.peak').read_text()), owner_completion='all child stages reaped and drained')
except _SetupOnlyComplete:
    pass
except BaseException as exc:
    receipt.update(build='FAILED', exception_type=type(exc).__name__, error=str(exc))
    raise
finally:
    receipt['completed'] = time.time()
    save()
