"""Rebuild the admitted chart closure serially; never substitute old receipts."""
from pathlib import Path
import argparse, hashlib, json, os, re, signal, subprocess, sys, time
from chart_port_candidate_check import admit, check_probe, digest, imports, tree_entries
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

def run(argv, label, cwd=PKG, env=None, timeout=600):
    stage = dict(argv=argv, cwd=str(cwd), timeout_seconds=timeout, started=time.time(), status='STARTING', peak_rss_bytes=0)
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
                rss, compilers = 0, 0
                for p in Path('/proc').iterdir():
                    if not p.name.isdigit():
                        continue
                    try:
                        stat = (p / 'stat').read_text().rsplit(')', 1)[1].split()
                        if int(stat[3]) != proc.pid:  # session ID, not command text
                            continue
                        rss += int(stat[21]) * os.sysconf('SC_PAGE_SIZE')
                        exe = os.readlink(p / 'exe')
                        compilers += Path(exe).name == 'lean'
                    except (FileNotFoundError, ProcessLookupError, PermissionError):
                        continue
                stage['peak_rss_bytes'] = max(stage['peak_rss_bytes'], rss)
                if compilers > 1:
                    raise RuntimeError('More than one Lean compiler in an owned stage')
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
    run(argv, label, env=env)
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
        for dep in imports(source.read_bytes()):
            bootstrap_visit(dep)
        active.remove(name)
        seen.add(name)
        cache_order.append((name, source))
        assert len(cache_order) <= 200, 'Cache bootstrap exceeded finite source bound'
    bootstrap_visit('Cache.Main')
    for i, (name, source) in enumerate(cache_order):
        serial_compile(name, source, bootstrap, lean, env, 'cache-bootstrap-' + str(i), name.startswith('Cache.'))
    # The real pinned cache CLI runs interpreted, so Lake cannot spawn a parallel build.
    run([lean, '-j1', '-M5632', '-R', str(mathlib), '--run', str(mathlib / 'Cache/Main.lean'), 'get', *admission['external_mathlib_roots']],
        'ordinary-pinned-cache-read', env=env, timeout=1800)
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
            probe = run([lean, '-j1', '-M5632', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3', str(source)],
                        'full-type-proof-axiom-probe', env=env)
            result = check_probe(probe)
            (EVIDENCE / 'probe-verdict.json').write_text(json.dumps(result, indent=2) + '\n')
        else:
            serial_compile(row['module'], source, local, lean, env, 'local-' + str(i), True)
    final = admit(ROOT, args.expected_sha, args.expected_tree, dependency_inventory)
    assert {k:v for k,v in final.items() if k != 'physical_inventory'} == {k:v for k,v in admission.items() if k != 'physical_inventory'}
    (EVIDENCE / 'final-physical-admission.json').write_text(json.dumps(final, indent=2) + '\n')
    assert not subprocess.check_output(['git', '--no-replace-objects', '-C', str(mathlib), 'status', '--porcelain', '--untracked-files=no'])
    receipt.update(build='PASSED', full_candidate_qualification='PASSED', fresh_local_modules=70, fresh_probe=1, fallback_mathlib_modules=len(missing_order),
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
