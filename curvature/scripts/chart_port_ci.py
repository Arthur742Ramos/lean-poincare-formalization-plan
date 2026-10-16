"""Rebuild the admitted chart closure serially; never substitute old receipts."""
from pathlib import Path
import argparse, hashlib, json, os, re, signal, subprocess, sys, time
from chart_port_candidate_check import admit, check_probe, check_ricci_extension_probe, digest, imports, tree_entries, package_root_relationships
from chart_port_artifacts import artifact_status, required_import_files, materialize_pinned_mathlib_cache
"""Authenticated bootstrap-only Cache.IO view; original Mathlib stays immutable."""
from pathlib import Path
import hashlib
import os
import stat

IO_SHA = '8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82'
COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
ENV_KEY = 'POINT4_AUTHENTICATED_CACHE_LEANTAR'
ORIGINAL = '''private initialize leantarSysrootBin : String ← do
  let out ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
  if out.exitCode == 0 then
    let path : FilePath := out.stdout.trimAscii.toString / "bin" / s!"leantar{EXE}"
    if ← path.pathExists then return path.toString
  throw <| IO.userError "leantar not found in Lean sysroot. This toolchain may predate nightly-2026-03-09."
'''.encode()
REPLACEMENT = '''private initialize leantarSysrootBin : String ← do
  let some value ← IO.getEnv "POINT4_AUTHENTICATED_CACHE_LEANTAR"
    | throw <| IO.userError "Missing authenticated bootstrap leantar path"
  let path : FilePath := value
  unless path.isAbsolute && path.fileName == some s!"leantar{EXE}" do
    throw <| IO.userError "Malformed authenticated bootstrap leantar path"
  unless ← path.pathExists do
    throw <| IO.userError "Authenticated bootstrap leantar path disappeared"
  return value
'''.encode()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def regular_seal(path, *, executable=False):
    path = Path(path)
    assert path.is_absolute() and path.resolve(strict=True) == path, 'Cache view path must be canonical'
    def ancestors():
        for parent in path.parents:
            info = parent.lstat()
            assert stat.S_ISDIR(info.st_mode) and not parent.is_symlink(), 'Cache view ancestor kind/link drift'
            assert not getattr(info, 'st_file_attributes', 0) & 0x400, 'Cache view ancestor reparse point'
    def identity(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    ancestors()
    before = path.lstat()
    assert stat.S_ISREG(before.st_mode) and not path.is_symlink(), 'Cache view input must be a regular file'
    assert not getattr(before, 'st_file_attributes', 0) & 0x400, 'Cache view input reparse point'
    if executable:
        assert os.access(path, os.X_OK), 'Cache view SDK tool is not executable'
    with path.open('rb') as stream:
        opened = os.fstat(stream.fileno())
        if os.name == 'nt':
            # Windows fstat may omit file identity fields. Cross-bind the two
            # open handles with the native volume/file ID, then seal each stat.
            import ctypes
            import msvcrt
            class Info(ctypes.Structure):
                _fields_ = [('attributes', ctypes.c_uint32), ('creation', ctypes.c_uint32 * 2),
                            ('access', ctypes.c_uint32 * 2), ('write', ctypes.c_uint32 * 2),
                            ('volume', ctypes.c_uint32), ('size_high', ctypes.c_uint32),
                            ('size_low', ctypes.c_uint32), ('links', ctypes.c_uint32),
                            ('index_high', ctypes.c_uint32), ('index_low', ctypes.c_uint32)]
            def native(fd):
                value = Info()
                api = ctypes.WinDLL('kernel32', use_last_error=True).GetFileInformationByHandle
                api.argtypes = [ctypes.c_void_p, ctypes.POINTER(Info)]
                api.restype = ctypes.c_int
                assert api(msvcrt.get_osfhandle(fd), ctypes.byref(value)), 'Cache view native file identity failed'
                assert ctypes.sizeof(Info) == 52, 'Cache view native identity layout drift'
                return (value.attributes, tuple(value.creation), tuple(value.write), value.volume,
                        value.size_high, value.size_low, value.links, value.index_high, value.index_low)
            native_before = native(stream.fileno())
            with path.open('rb') as path_stream:
                assert native(path_stream.fileno()) == native_before, 'Cache view open path identity drift'
        else:
            assert identity(opened) == identity(before), 'Cache view open identity drift'
        data = stream.read()
        assert identity(os.fstat(stream.fileno())) == identity(opened), 'Cache view read identity drift'
        if os.name == 'nt':
            assert native(stream.fileno()) == native_before, 'Cache view native read identity drift'
            with path.open('rb') as path_stream:
                assert native(path_stream.fileno()) == native_before, 'Cache view native POST path identity drift'
    assert identity(path.lstat()) == identity(before), 'Cache view path POST identity drift'
    ancestors()
    return data, {'path': str(path), 'identity': list(identity(before)), 'sha256': sha(data)}

def derive_cache_io(original):
    assert sha(original) == IO_SHA, 'Pinned Cache.IO whole source drift'
    assert original.count(ORIGINAL) == 1, 'Pinned Cache.IO initializer occurrence drift'
    derived = original.replace(ORIGINAL, REPLACEMENT)
    assert derived.count(REPLACEMENT) == 1 and derived.replace(REPLACEMENT, ORIGINAL) == original, 'Cache.IO inverse drift'
    return derived

def verify_pinned_cache_source_view(context, env, official):
    assert set(context) == {'role', 'mathlib_pin', 'mathlib', 'compiler_prefix', 'owned_root',
                            'original', 'derived', 'compiler', 'leantar', 'policy_sha256',
                            'compiled_source_is_original', 'point4'}, 'Cache view receipt schema drift'
    assert context['role'] == 'BOOTSTRAP_CACHE_ONLY_AUTHENTICATED_SOURCE_VIEW', 'Cache view role drift'
    assert context['mathlib_pin'] == 'db584cd6d46c92f209a44c0f1c829460d327499d', 'Cache view Mathlib pin drift'
    assert context['compiled_source_is_original'] is False and context['point4'] == 'OPEN', 'Cache view provenance label drift'
    assert official['compiler_commit'] == COMMIT, 'Cache view compiler commit drift'
    compiler = Path(official['compiler_path'])
    prefix = Path(context['compiler_prefix'])
    assert compiler == prefix / 'bin/lean', 'Cache view observed compiler prefix drift'
    leantar = prefix / 'bin/leantar'
    assert env.get(ENV_KEY) == str(leantar), 'Cache view controlled environment drift'
    original_path = Path(context['mathlib']) / 'Cache/IO.lean'
    derived_path = Path(context['owned_root']) / 'Cache/IO.lean'
    assert context['original']['path'] == str(original_path), 'Cache view original path drift'
    assert context['derived']['path'] == str(derived_path), 'Cache view derived path drift'
    original, original_seal = regular_seal(original_path)
    derived, derived_seal = regular_seal(derived_path)
    compiler_data, compiler_seal = regular_seal(compiler, executable=True)
    _, leantar_seal = regular_seal(leantar, executable=True)
    assert sha(compiler_data) == official['compiler_sha256'], 'Cache view official compiler image drift'
    for name, actual in [('original', original_seal), ('derived', derived_seal), ('compiler', compiler_seal), ('leantar', leantar_seal)]:
        assert context[name] == actual, 'Cache view sealed input drift: ' + name
    assert derived == derive_cache_io(original), 'Cache view derived source/inverse drift'
    assert context['policy_sha256'] == sha(ORIGINAL + b'\0' + REPLACEMENT), 'Cache view policy drift'
    return context

def prepare_pinned_cache_source_view(mathlib, compiler_prefix, official, env, owned_root):
    mathlib, compiler_prefix, owned_root = map(Path, (mathlib, compiler_prefix, owned_root))
    assert owned_root.is_absolute() and not owned_root.exists() and not owned_root.is_symlink(), 'Cache view output must be fresh and owned'
    def owned_namespace(directory):
        assert directory.resolve(strict=False) == directory, 'Cache view output namespace must be canonical'
        for parent in (directory, *directory.parents):
            if parent.exists() or parent.is_symlink():
                info = parent.lstat()
                assert stat.S_ISDIR(info.st_mode) and not parent.is_symlink(), 'Cache view output ancestor kind/link drift'
                assert not getattr(info, 'st_file_attributes', 0) & 0x400, 'Cache view output ancestor reparse point'
    owned_namespace(owned_root)
    assert compiler_prefix.is_absolute() and Path(official['compiler_path']) == compiler_prefix / 'bin/lean', 'Cache view observed prefix drift'
    assert official['compiler_commit'] == COMMIT, 'Cache view compiler commit drift'
    original, original_seal = regular_seal(mathlib / 'Cache/IO.lean')
    derived = derive_cache_io(original)
    compiler_data, compiler_seal = regular_seal(compiler_prefix / 'bin/lean', executable=True)
    assert sha(compiler_data) == official['compiler_sha256'], 'Cache view official compiler image drift'
    _, leantar_seal = regular_seal(compiler_prefix / 'bin/leantar', executable=True)
    owned_namespace(owned_root)
    owned_root.mkdir()
    owned_namespace(owned_root)
    (owned_root / 'Cache').mkdir()
    owned_namespace(owned_root / 'Cache')
    derived_path = owned_root / 'Cache/IO.lean'
    with derived_path.open('xb') as stream:
        stream.write(derived)
    _, derived_seal = regular_seal(derived_path)
    context = {'role': 'BOOTSTRAP_CACHE_ONLY_AUTHENTICATED_SOURCE_VIEW',
               'mathlib_pin': 'db584cd6d46c92f209a44c0f1c829460d327499d',
               'mathlib': str(mathlib), 'compiler_prefix': str(compiler_prefix), 'owned_root': str(owned_root),
               'original': original_seal, 'derived': derived_seal, 'compiler': compiler_seal, 'leantar': leantar_seal,
               'policy_sha256': sha(ORIGINAL + b'\0' + REPLACEMENT),
               'compiled_source_is_original': False, 'point4': 'OPEN'}
    controlled = dict(env)
    controlled[ENV_KEY] = str(compiler_prefix / 'bin/leantar')
    verify_pinned_cache_source_view(context, controlled, official)
    return controlled, context


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
    # Image-read failure does not establish termination. Obtain two fresh,
    # consecutive terminal observations of the same initially owned identity.
    # No retry, wait, absent-PID inference or live/query exemption is introduced.
    row['terminal_samples'] = []
    row['terminal_errors'] = []
    try:
        for _ in range(2):
            raw_stat = (p / 'stat').read_text()
            terminal = raw_stat.rsplit(')', 1)[1].split()
            check = dict(pid=int(raw_stat.split(' ', 1)[0]),
                state=terminal[0], ppid=int(terminal[1]), pgrp=int(terminal[2]),
                session=int(terminal[3]), starttime_ticks=int(terminal[19]),
                rss_bytes=int(terminal[21]) * os.sysconf('SC_PAGE_SIZE'),
                observed_at=time.time())
            row['terminal_samples'].append(check)
            row['terminal_recheck'] = check
        keys = ('pid', 'ppid', 'pgrp', 'session', 'starttime_ticks')
        row['verified_terminated_zombie'] = (
            row['pgrp'] == row['session']
            and (row['state'] != 'Z' or row['rss_bytes'] == 0)
            and all(check['state'] == 'Z' and check['rss_bytes'] == 0
                and all(row[key] == check[key] for key in keys)
                for check in row['terminal_samples']))
        if not row['verified_terminated_zombie']:
            row['terminal_errors'].append(dict(type='TerminalIdentityMismatch',
                message='Both fresh terminal states and kernel identities must match'))
    except (OSError, ValueError, UnicodeError, IndexError) as exc:
        row['terminal_errors'].append(dict(type=type(exc).__name__, message=str(exc)))
    row['rechecked_at'] = time.time()
    return row

def pinned_compiler_environment(env, official):
    # Nested Cache initializers invoke bare `lean --print-prefix`. Select the
    # authenticated official image without relaxing owned-process predicates.
    import stat
    assert type(env) is dict and all(type(k) is str and type(v) is str for k, v in env.items())
    assert official['compiler_commit'] == 'd8b18978322de05a8f3dba51ef03cf5461676c17', 'Official compiler commit drift'
    path = Path(official['compiler_path'])
    assert path.is_absolute() and path.resolve(strict=True) == path, 'Official compiler path must be resolved'
    def authenticate_ancestors():
        for parent in path.parents:
            assert not parent.is_symlink() and stat.S_ISDIR(parent.lstat().st_mode), 'Official compiler directory link/kind drift'
    authenticate_ancestors()
    before = path.lstat()
    assert not path.is_symlink() and stat.S_ISREG(before.st_mode), 'Official compiler must be a regular nonlink file'
    assert os.access(path, os.X_OK), 'Official compiler is not executable'
    def identity(value):
        return (value.st_dev, value.st_ino, value.st_mode, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
    def same_object(value):
        # Path and handle stat APIs can represent Windows execute bits and
        # creation/change time differently. Cross-bind the real inode/image;
        # retain full mode and change-time seals independently within each API.
        return (value.st_dev, value.st_ino, stat.S_IFMT(value.st_mode), value.st_size, value.st_mtime_ns)
    with path.open('rb') as stream:
        opened = os.fstat(stream.fileno())
        assert same_object(opened) == same_object(before), 'Official compiler open identity drift'
        data = stream.read()
        assert identity(os.fstat(stream.fileno())) == identity(opened), 'Official compiler read identity drift'
    assert digest(data) == official['compiler_sha256'], 'Official compiler image digest drift'
    assert identity(path.lstat()) == identity(before) and not path.is_symlink(), 'Official compiler identity POST drift'
    authenticate_ancestors()
    result = dict(env)
    previous = result.get('PATH', '')
    result['PATH'] = str(path.parent) + (os.pathsep + previous if previous else '')
    return result


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

CACHE_PLAN_SOURCE = '/- Bootstrap-only plan producer. Never downloads, extracts, or starts a child. -/\nimport Cache.Requests\n\nopen Lean System Cache IO Hashing Requests\n\nprivate def strings (xs : Array String) : Json := toJson xs\n\nprivate def moduleRow (memo : HashMemo) (mod : Name) (h : UInt64) : CacheM Json := do\n  let ctx ← read\n  let some deps := memo.depsMap[mod]? | throw <| IO.userError s!"Missing dependency row: {mod}"\n  let source ← IO.FS.realPath (← Lean.findLean ctx.srcSearchPath mod)\n  let singleton : ModuleHashMap := (∅ : ModuleHashMap).insert mod h\n  let config ← mkLeanTarConfig singleton\n  unless config.size == 1 do throw <| IO.userError "Singleton extraction plan drift"\n  pure <| Json.mkObj [\n    ("module", toJson mod.toString), ("archive", toJson h.asLTar),\n    ("source", toJson source.toString),\n    ("dependencies", strings (deps.map Name.toString)), ("extract", config[0]!)]\n\ndef main (args : List String) : IO Unit := do\n  let some boundText ← IO.getEnv "POINT4_CACHE_PLAN_SOURCE_BOUND"\n    | throw <| IO.userError "Missing authenticated source-inventory bound"\n  let some sourceBound := boundText.toNat? | throw <| IO.userError "Malformed source bound"\n  unless !args.isEmpty && args.length ≤ sourceBound && args.eraseDups.length == args.length do\n    throw <| IO.userError "Expected distinct, bounded admitted roots"\n  CacheM.run do\n    let ctx ← read\n    let mathlib ← IO.FS.realPath ctx.mathlibDepPath\n    unless !(← isMathlibRoot) do throw <| IO.userError "Expected downstream package context"\n    checkForToolchainMismatch\n    checkForManifestMismatch\n    let roots ← parseArgs ("get" :: args)\n    unless roots.size == args.length do throw <| IO.userError "Root parsing changed cardinality"\n    let names := args.map String.toName\n    unless names.all (fun n => roots.contains n) do throw <| IO.userError "Root parsing changed names"\n    -- The pinned function hashes Mathlib plus these roots, then we filter.\n    let memo ← getHashMemo roots\n    unless names.all (fun n => memo.hashMap.contains n && memo.depsMap.contains n) do\n      throw <| IO.userError "An admitted root has no genuine cache hash"\n    let selected ← memo.filterByRootModules names\n    unless selected.size > 0 && selected.size ≤ sourceBound && memo.hashMap.size ≤ sourceBound do\n      throw <| IO.userError "Finite cache plan bound exceeded"\n    let selectedRows := selected.toArray.qsort (fun a b => a.1.toString < b.1.toString)\n    let mut rows := #[]\n    for (mod, h) in selectedRows do\n      let some deps := memo.depsMap[mod]? | throw <| IO.userError "Missing selected dependency row"\n      unless deps.all selected.contains do throw <| IO.userError s!"Incomplete selected closure: {mod}"\n      rows := rows.push (← moduleRow memo mod h)\n    let inputRows := memo.hashMap.toArray.qsort (fun a b => a.1.toString < b.1.toString)\n    let mut inputSources := #[]\n    for (mod, _) in inputRows do\n      inputSources := inputSources.push (Json.mkObj [\n        ("module", toJson mod.toString),\n        ("source", toJson (← IO.FS.realPath (← Lean.findLean ctx.srcSearchPath mod)).toString)])\n    -- Exercise the actual pinned Lean serializer before emitting the schema field.\n    let generationJson := toJson rootHashGeneration.toNat\n    match generationJson with\n    | .num _ => pure ()\n    | _ => throw <| IO.userError "Cache generation must serialize as a JSON number"\n    unless generationJson == toJson (5 : Nat) do\n      throw <| IO.userError "Pinned cache generation changed"\n    let plan := Json.mkObj [\n      ("schema", toJson "point4-cache-plan-v1"),\n      ("mathlib_pin", toJson "db584cd6d46c92f209a44c0f1c829460d327499d"),\n      ("mathlib", toJson mathlib.toString), ("cwd", toJson (← IO.currentDir).toString),\n      ("mathlib_context", toJson ctx.mathlibDepPath.toString),\n      ("cache_dir", toJson CACHEDIR.toString), ("roots", toJson args),\n      ("source_search_path", strings (ctx.srcSearchPath.toArray.map FilePath.toString)),\n      ("root_hash_archive_spelling", toJson memo.rootHash.asLTar),\n      ("root_hash_generation", generationJson),\n      ("full_hash_inputs", Json.arr inputSources), ("modules", Json.arr rows),\n      ("repo", toJson "leanprover-community/mathlib4"),\n      ("containers", strings #["master", "legacy"]),\n      ("compiler_or_acquisition_spawned", toJson false)]\n    IO.println plan.compress\n'

"""Proposed driver definitions; embed before the existing driver try block.

No MAIN here. The existing Lean-stage run, resource limit and process classifier
are not changed. This fragment is not an independently executable actor.
"""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import time

CACHE_SPLIT_PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'
CACHE_SPLIT_UPSTREAM = {
    'Cache/IO.lean': '8457b0e2b404ae2a7c7e02d9e264f9d8c1e72935178e7dda1fae95424b022c82',
    'Cache/Requests.lean': 'f9b3f03a938146b08f106bffff8e87405b3535f4a2a2b9b690c359b49cbe8464',
    'Cache/Hashing.lean': 'd38ae8d111ce0407b36d1a633f4fac5fd4b0fa065cf7dc8bfe9a69ad416398eb',
    'Cache/Main.lean': 'dccffca32f05fa9d2e8880a928c170e5cae52376a5c94966cef770e1fc5f5044',
    'Cache/Lean.lean': 'c89aa848e695a7cad04ae66f517f5c1ccc6f1035062efa376115ce1b8eb46e8d',
    'Cache/Infra.lean': 'c3c6bb06dd0c7fd6b472d1830ab2d07ca8164e9faf89e5076ee4f736d712fd98',
}
CACHE_SPLIT_URLS = (
    ('master', 'https://lakecache.blob.core.windows.net/mathlib4-master'),
    ('legacy', 'https://lakecache.blob.core.windows.net/mathlib4'))


def cache_split_json(raw):
    def object_pairs(pairs):
        out = {}
        for key, value in pairs:
            assert key not in out, 'Duplicate JSON key'
            out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=object_pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def cache_split_no_overrides(env):
    for key in ('MATHLIB_CACHE_GET_URL', 'MATHLIB_CACHE_PUT_URL',
                'MATHLIB_CACHE_FROM', 'MATHLIB_CACHE_REPO_SCOPE'):
        assert not env.get(key), 'Unsupported inherited cache override: ' + key


def cache_split_validate_plan(raw, roots, mathlib, cache_dir, cwd, source_catalog):
    assert len(raw) <= 32 * 1024**2, 'Bounded plan exceeded'
    p = cache_split_json(raw)
    assert set(p) == {'schema', 'mathlib_pin', 'mathlib', 'mathlib_context', 'cwd', 'cache_dir', 'roots',
                      'source_search_path', 'root_hash_archive_spelling', 'full_hash_inputs',
                      'root_hash_generation', 'modules', 'repo', 'containers', 'compiler_or_acquisition_spawned'}
    assert p['schema'] == 'point4-cache-plan-v1' and p['mathlib_pin'] == CACHE_SPLIT_PIN
    assert p['repo'] == 'leanprover-community/mathlib4' and p['containers'] == ['master', 'legacy']
    assert p['compiler_or_acquisition_spawned'] is False
    assert p['roots'] == roots and roots and len(set(roots)) == len(roots) <= len(source_catalog)
    assert all(type(n) is str and re.fullmatch(r'Mathlib(?:\.[A-Za-z_]\w*)+', n) for n in roots)
    assert p['mathlib'] == str(mathlib) and p['cache_dir'] == str(cache_dir) and p['cwd'] == str(cwd)
    assert (cwd / p['mathlib_context']).resolve() == mathlib
    assert type(p['root_hash_generation']) is int and p['root_hash_generation'] == 5
    assert re.fullmatch('[0-9a-f]{16}\\.ltar', p['root_hash_archive_spelling'])
    assert type(p['source_search_path']) is list and p['source_search_path']
    full = p['full_hash_inputs']; rows = p['modules']
    assert type(full) is list and type(rows) is list and 0 < len(rows) <= len(full) <= len(source_catalog)
    full_names = {}; full_paths = set()
    for row in full:
        assert set(row) == {'module', 'source'} and type(row['module']) is str
        assert row['module'] not in full_names and row['source'] in source_catalog
        assert Path(row['source']).as_posix().endswith('/' + row['module'].replace('.', '/') + '.lean')
        assert row['source'] not in full_paths, 'Two module names for one hash input source'
        full_names[row['module']] = row['source']; full_paths.add(row['source'])
    modules = {}; archives = set()
    for row in rows:
        assert set(row) == {'module', 'archive', 'source', 'dependencies', 'extract'}
        name = row['module']; archive = row['archive']
        assert type(name) is str and name not in modules and name in full_names
        assert row['source'] == full_names[name] and row['source'] in source_catalog
        assert type(archive) is str and re.fullmatch('[0-9a-f]{16}\\.ltar', archive)
        # Refuse an ambiguous hash-to-many-module plan; do not overwrite a destination.
        assert archive not in archives, 'Ambiguous archive alias'
        deps = row['dependencies']; assert type(deps) is list
        assert all(type(dep) is str for dep in deps)
        expected = {'file': str(cache_dir / archive), 'base': p['mathlib_context']} if name == 'Mathlib' or name.startswith('Mathlib.') else str(cache_dir / archive)
        assert row['extract'] == expected, 'Pinned singleton mkLeanTarConfig destination drift'
        modules[name] = row; archives.add(archive)
    assert set(roots) <= set(modules)
    seen = set(); active = set()
    def visit(name):
        assert name in modules and name not in active, 'Missing/cyclic dependency evidence'
        if name in seen: return
        active.add(name)
        for dep in modules[name]['dependencies']: visit(dep)
        active.remove(name); seen.add(name)
    for root in roots: visit(root)
    assert seen == set(modules), 'Extra module outside admitted root closure'
    assert list(modules) == sorted(modules), 'Canonical plan order required'
    return p


def cache_split_transfer_results(raw, requested, container, tool_exit):
    assert container in ('master', 'legacy') and len(raw) <= 64 * 1024**2
    records = {}; served = set(); misses = set(); failures = []
    for line in raw.splitlines():
        assert line, 'Empty transfer record'
        row = cache_split_json(line)
        assert type(row) is dict and {'filename_effective', 'url_effective', 'http_code', 'exitcode'} <= set(row)
        path = row['filename_effective']; assert type(path) is str and path in requested
        assert path not in records, 'Duplicate transfer response'
        assert row['url_effective'] == requested[path], 'Transfer URL drift'
        code = row['http_code']; exitcode = row['exitcode']
        assert type(code) is int and type(exitcode) is int and 0 <= code <= 599 and 0 <= exitcode <= 255
        records[path] = row
        if code in (200, 201) and exitcode == 0: served.add(path)
        elif (code == 404 or (container == 'legacy' and code == 403)) and exitcode == 0: misses.add(path)
        else: failures.append({'path': path, 'http_code': code, 'exitcode': exitcode})
    assert set(records) == set(requested), 'Missing/extra transfer evidence'
    if tool_exit != 0: failures.append({'curl_process_exit': tool_exit})
    return records, served, misses, failures


def cache_split_terminal_owner(row, owner_pid, argv, tool, launch, exit_code):
    """Accept only a recomputed, already-exited direct authenticated tool owner."""
    assert row.get('verified_terminated_zombie') is True and row.get('terminal_errors') == [], 'Unreadable/raced acquisition owner'
    assert type(launch) is dict and type(exit_code) is int, 'Terminal owner lacks launch/exit proof'
    assert type(launch['pid']) is int and type(launch['parent_pid']) is int
    assert launch['pid'] == owner_pid and launch['parent_pid'] == os.getpid()
    assert launch['argv'] == argv and launch['start_new_session'] is True
    fd = launch['fd']; assert type(fd) is int and fd >= 0
    assert launch['executable'] == '/proc/self/fd/' + str(fd) and launch['pass_fds'] == [fd]
    assert launch['tool_sha256'] == tool['sha256'] and re.fullmatch('[0-9a-f]{64}', tool['sha256'])
    assert type(tool['identity']) is list and len(tool['identity']) == 6 and all(type(value) is int for value in tool['identity'])
    assert type(tool['image_identity']) is list and len(tool['image_identity']) == 5 and all(type(value) is int for value in tool['image_identity'])
    assert launch['tool_identity'] == tool['identity'] == cache_split_file_identity(os.fstat(fd)), 'Terminal owner current image descriptor drift'
    assert tool['image_identity'] == [tool['identity'][i] for i in (0, 1, 3, 4, 5)]
    assert Path(tool['path']).name in ('curl', 'leantar') and argv[0] == tool['path']
    keys = ('pid', 'ppid', 'pgrp', 'session', 'starttime_ticks')
    assert all(type(row[key]) is int for key in keys)
    assert row['pid'] == row['pgrp'] == row['session'] == owner_pid
    assert row['ppid'] == launch['parent_pid'] and row['starttime_ticks'] > 0
    assert row['state'] == 'Z' and type(row['rss_bytes']) is int and row['rss_bytes'] == 0
    samples = row['terminal_samples']; assert type(samples) is list and len(samples) == 2
    for sample in samples:
        assert all(type(sample[key]) is int and sample[key] == row[key] for key in keys)
        assert sample['state'] == 'Z' and type(sample['rss_bytes']) is int and sample['rss_bytes'] == 0
    assert row['terminal_recheck'] == samples[-1]
    times = [launch['started_at'], launch['returned_at'], row['observed_at'],
             samples[0]['observed_at'], samples[1]['observed_at'], row['rechecked_at'], time.time()]
    assert all(type(value) in (int, float) and 0 < value < float('inf') for value in times)
    assert all(a <= b for a, b in zip(times, times[1:])), 'Terminal owner observation order drift'
    # Missing image fields are explained only by the complete terminal proof.
    # Every field actually observed must still agree with the admitted image.
    expected_hex = (b'\0'.join(arg.encode('utf8') for arg in argv) + b'\0').hex()
    for observed in (row, row.get('recheck', {})):
        assert type(observed) is dict
        if 'exe' in observed: assert observed['exe'] == tool['path'] and Path(observed['exe']).name != 'lean'
        if 'argv' in observed: assert observed['argv'] == argv
        if 'cmdline_hex' in observed: assert observed['cmdline_hex'] == expected_hex
        if 'image_identity' in observed:
            image = observed['image_identity']
            assert type(image) is list and all(type(value) is int for value in image) and image == tool['image_identity']
        if 'state' in observed: assert observed['state'] == 'Z'
        if 'rss_bytes' in observed: assert type(observed['rss_bytes']) is int and observed['rss_bytes'] == 0
        for key in keys:
            if key in observed: assert type(observed[key]) is int and observed[key] == row[key]
    return dict(classification='PROVEN_TERMINAL_DIRECT_TOOL_OWNER', exit_code=exit_code,
                kernel_identity={key: row[key] for key in keys}, terminal_samples=samples)


def cache_split_process_policy(rows, owner_pid, argv, tool, *, launch=None, exit_code=None):
    """Stricter than the unchanged Lean-stage classifier: no descendants at all."""
    assert len(rows) == 1 and rows[0]['pid'] == owner_pid, 'Unexpected/absent acquisition process'
    row = rows[0]
    if not (row['stable'] and not row['errors']):
        return cache_split_terminal_owner(row, owner_pid, argv, tool, launch, exit_code)
    assert row['session'] == row['pgrp'] == owner_pid and row['argv'] == argv
    assert row['exe'] == tool['path'] and row['recheck']['exe'] == tool['path']
    assert row['image_identity'] == row['recheck']['image_identity'] == tool['image_identity']
    assert Path(row['exe']).name != 'lean', 'Lean is forbidden during acquisition'


def cache_split_waitable_exit(owner_pid):
    """Observe only this direct child's exit, without reaping or waiting."""
    assert type(owner_pid) is int and owner_pid > 0
    options = os.WEXITED | os.WNOHANG | os.WNOWAIT
    before = time.time()
    event = os.waitid(os.P_PID, owner_pid, options)
    after = time.time()
    assert all(type(value) in (int, float) and 0 < value < float('inf')
               for value in (before, after)) and before <= after, 'Child exit clock drift'
    observation = dict(owner_pid=owner_pid, idtype=os.P_PID, options=options,
                       before=before, after=after, waitable=False)
    if event is None:
        return observation
    fields = {key: getattr(event, key) for key in
              ('si_pid', 'si_uid', 'si_signo', 'si_code', 'si_status')}
    assert all(type(value) is int for value in fields.values()), 'Malformed child exit observation'
    assert fields['si_pid'] == owner_pid and fields['si_uid'] == os.getuid(), 'Child exit identity drift'
    assert fields['si_signo'] == signal.SIGCHLD, 'Child exit signal drift'
    code, status = fields['si_code'], fields['si_status']
    if code == os.CLD_EXITED:
        assert 0 <= status <= 255, 'Child exit status drift'
        exit_code = status
    else:
        assert code in (os.CLD_KILLED, os.CLD_DUMPED), 'Child is not terminated'
        assert 0 < status < signal.NSIG, 'Child termination signal drift'
        exit_code = -status
    observation.update(waitable=True, event=fields, exit_code=exit_code)
    return observation


def cache_split_resource_seal():
    group = next(x.split(':', 2)[2] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    cg = Path('/sys/fs/cgroup') / group.lstrip('/')
    memory = (cg / 'memory.max').read_text().strip()
    quota, period = map(int, (cg / 'cpu.max').read_text().split())
    affinity = sorted(os.sched_getaffinity(0))
    assert memory == str(LIMIT) and quota <= 2 * period and 0 < len(affinity) <= 2
    return {'cgroup': str(cg), 'memory_max': memory, 'cpu_max': [quota, period], 'affinity': affinity}


def cache_split_file_identity(info):
    return [info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns]


def cache_split_open_tool(path):
    path = Path(path).resolve(strict=True)
    assert path.is_absolute() and path.name in ('curl', 'leantar')
    for ancestor in path.parents:
        assert stat.S_ISDIR(ancestor.lstat().st_mode) and not ancestor.is_symlink()
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd); assert stat.S_ISREG(before.st_mode) and before.st_mode & 0o111
        assert cache_split_file_identity(before) == cache_split_file_identity(path.lstat())
        with os.fdopen(os.dup(fd), 'rb') as stream: raw = stream.read()
        os.lseek(fd, 0, os.SEEK_SET)
        assert cache_split_file_identity(before) == cache_split_file_identity(os.fstat(fd))
        return fd, {'path': str(path), 'sha256': digest(raw), 'identity': cache_split_file_identity(before),
                    'image_identity': [before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns]}
    except BaseException:
        os.close(fd); raise


def cache_split_tool_POST(fd, tool):
    os.lseek(fd, 0, os.SEEK_SET)
    with os.fdopen(os.dup(fd), 'rb') as stream: raw = stream.read()
    assert digest(raw) == tool['sha256']
    assert cache_split_file_identity(os.fstat(fd)) == tool['identity']
    assert cache_split_file_identity(Path(tool['path']).lstat()) == tool['identity']


def cache_split_tool_stage(argv, label, env, deadline, stdin_path=None):
    assert os.name == 'posix' and deadline > time.monotonic()
    start = time.monotonic(); proc = None; fd = None; tool = None; pre = None; terminal_exit = None
    stage = dict(argv=argv, label=label, status='STARTING',
                 zero_Lean_required=True, peak_rss_bytes=0)
    receipt['stages'].append(stage)
    out = None; err = None; input_stream = None; primary_error = None
    try:
        # Cleanup ownership begins before opening the image. Every later PRE
        # assertion, resource query, receipt save and path operation is covered.
        fd, tool = cache_split_open_tool(argv[0])
        assert tool['path'] == argv[0]
        stage['authenticated_tool'] = tool
        pre = cache_split_resource_seal(); stage['resources_PRE'] = pre
        save()
        out = EVIDENCE / (label + '.stdout'); err = EVIDENCE / (label + '.stderr')
        if stdin_path is not None: input_stream = Path(stdin_path).open('rb')
        with out.open('xb') as stdout, err.open('xb') as stderr:
            # Execute the already authenticated open image; pathname replacement
            # cannot select another executable between PRE and kernel exec.
            launch_started = time.time()
            proc = subprocess.Popen(argv, executable='/proc/self/fd/' + str(fd), pass_fds=(fd,),
                cwd=PKG, env=env, stdin=input_stream if input_stream is not None else subprocess.DEVNULL,
                stdout=stdout, stderr=stderr, start_new_session=True)
            launch = dict(pid=proc.pid, parent_pid=os.getpid(), argv=list(argv), fd=fd,
                executable='/proc/self/fd/' + str(fd), pass_fds=[fd], start_new_session=True,
                tool_identity=tool['identity'], tool_sha256=tool['sha256'],
                started_at=launch_started, returned_at=time.time())
            stage.update(pid=proc.pid, status='RUNNING', authenticated_launch=launch); save()
            while True:
                if time.monotonic() >= deadline: raise TimeoutError(label)
                # poll() reaps a completed child and destroys the /proc identity
                # needed by the terminal proof. Observe first, retaining it.
                observed = cache_split_waitable_exit(proc.pid)
                stage['waitid_observation'] = observed
                rows = []; rss = 0
                for path in Path('/proc').iterdir():
                    if not path.name.isdigit(): continue
                    try: info = (path / 'stat').read_text().rsplit(')', 1)[1].split()
                    except (FileNotFoundError, ProcessLookupError, PermissionError): continue
                    if int(info[3]) != proc.pid: continue
                    rss += int(info[21]) * os.sysconf('SC_PAGE_SIZE')
                    rows.append(owned_process_identity(path, info))
                stage['owned_process_snapshot'] = rows
                stage['peak_rss_bytes'] = max(stage['peak_rss_bytes'], rss)
                assert rss <= LIMIT, 'Acquisition exceeds original 6GiB RSS bound'
                if observed['waitable']:
                    assert len(rows) == 1 and rows[0]['pid'] == proc.pid, 'Unexpected/absent acquisition process'
                    assert launch['returned_at'] <= observed['before'] <= observed['after'] <= rows[0]['observed_at'], 'Child exit observation order drift'
                    # Always use the complete terminal predicate here, including
                    # when an earlier image observation happened to be stable.
                    terminal_exit = observed['exit_code']
                    proof = cache_split_terminal_owner(rows[0], proc.pid, argv, tool,
                        launch, terminal_exit)
                    stage['terminal_owner_proof'] = proof
                    break
                # No waitable event gives no exemption for unreadable live
                # owners, missing owners, descendants or contradictory fields.
                cache_split_process_policy(rows, proc.pid, argv, tool,
                    launch=launch, exit_code=None)
                time.sleep(0.05)
            stage.update(exit_code=terminal_exit, status='RETURNED')
    except BaseException as exc:
        primary_error = exc
        stage.update(status='FAILED', error={'type': type(exc).__name__, 'message': str(exc)})
        raise
    finally:
        errors = []
        stage['cleanup_errors'] = []
        def attempt(where, action):
            try: return action()
            except BaseException as exc:
                errors.append(exc)
                stage['cleanup_errors'].append({'where': where, 'type': type(exc).__name__, 'message': str(exc)})
        if input_stream is not None: attempt('stdin_close', input_stream.close)
        if proc is not None:
            def kill():
                try: os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError: pass
            attempt('kill_owned_session', kill)
            def reap():
                proc.wait(timeout=10)
                stage.update(exit_code=proc.returncode, owner_reaped=True)
                if terminal_exit is not None:
                    assert proc.returncode == terminal_exit, 'Reaped child status differs from waitid'
            attempt('reap_owner', reap)
            def scan():
                survivors = []
                for path in Path('/proc').iterdir():
                    if not path.name.isdigit(): continue
                    try: info = (path / 'stat').read_text().rsplit(')', 1)[1].split()
                    except (FileNotFoundError, ProcessLookupError): continue
                    if int(info[3]) == proc.pid: survivors.append(int(path.name))
                stage['remaining_session_pids'] = survivors
                assert not survivors, 'Acquisition session not drained'
            attempt('session_scan', scan)
        if fd is not None: attempt('tool_POST', lambda: cache_split_tool_POST(fd, tool))
        def resource_POST():
            stage['resources_POST'] = cache_split_resource_seal()
            if pre is not None:
                assert stage['resources_POST'] == pre, 'Acquisition resource PREPOST drift'
            else:
                stage['resource_PRE_unavailable'] = True
        attempt('resource_POST', resource_POST)
        if fd is not None: attempt('image_descriptor_close', lambda: os.close(fd))
        attempt('elapsed', lambda: stage.update(elapsed_seconds=time.monotonic()-start))
        for suffix, path in [('stdout', out), ('stderr', err)]:
            def log_POST(path=path, suffix=suffix):
                if path is not None and path.exists(): stage[suffix + '_sha256'] = digest(path.read_bytes())
            attempt(suffix + '_POST', log_POST)
        if errors: stage['status'] = 'FAILED_POST'
        attempt('save', save)
        # Retain the original primary failure and every independent cleanup
        # error. Cleanup cannot convert either category to a successful result.
        if primary_error is not None: raise primary_error
        if errors: raise errors[0]
    assert proc is not None and stage['status'] == 'RETURNED'
    assert time.monotonic() <= deadline, 'Original aggregate cache deadline exceeded'
    return stage['exit_code'], out.read_bytes(), err.read_bytes()


def cache_split_acquire(plan, env, curl, leantar, deadline):
    cache_split_no_overrides(env)
    cache_dir = Path(plan['cache_dir']); assert cache_dir.is_absolute()
    cache_dir.mkdir(exist_ok=False)
    remaining = {row['archive']: row for row in plan['modules']}
    served_all = {}; cumulative_failures = []; rounds = []
    for container, base in CACHE_SPLIT_URLS:
        if not remaining: break
        requested = {str(cache_dir / (name + '.part')): base + '/f/' + name for name in sorted(remaining)}
        config = ''.join('url = ' + json.dumps(url) + '\n-o ' + json.dumps(path) + '\n'
                         for path, url in requested.items())
        config_path = EVIDENCE / ('cache-' + container + '.cfg')
        with config_path.open('x', encoding='utf8', newline='\n') as stream: stream.write(config)
        argv = [curl, '--disable', '--request', 'GET', '--parallel', '--silent', '--retry', '5',
                '--write-out', '%{json}\n', '--config', str(config_path)]
        code, output, stderr = cache_split_tool_stage(argv, 'cache-' + container, env, deadline)
        records, served, misses, failures = cache_split_transfer_results(output, requested, container, code)
        for part in sorted(requested):
            path = Path(part)
            if part in served:
                data, seal = regular_seal(path)
                target = cache_dir / path.name.removesuffix('.part'); assert not target.exists()
                path.rename(target)
                after, after_seal = regular_seal(target); assert after == data
                name = target.name; served_all[name] = {'bytes': len(after), 'sha256': digest(after),
                    'container': container, 'url': requested[part], 'transfer': records[part],
                    'archive_authentication': 'Original pinned upstream origin/hash-name policy; SHA256 is an observed byte seal'}
                del remaining[name]
            elif path.exists():
                regular_seal(path); path.unlink()
        cumulative_failures.extend(failures)
        rounds.append({'container': container, 'served': sorted(served), 'misses': sorted(misses), 'failures': failures})
    result = {'archives': served_all, 'missing': sorted(remaining), 'rounds': rounds,
              'hard_failures': cumulative_failures, 'fresh_mathematical_compilations': 0}
    receipt['cache_acquisition'] = result; save()
    assert not cumulative_failures, 'Cache transfer hard failure; all evidence retained'
    config = [row['extract'] for row in plan['modules'] if row['archive'] in served_all]
    if config:
        path = EVIDENCE / 'cache-extraction.json'
        with path.open('x', encoding='utf8') as stream: json.dump(config, stream, separators=(',', ':'))
        before = {name: digest((cache_dir / name).read_bytes()) for name in served_all}
        code, output, stderr = cache_split_tool_stage(
            [leantar, '-x', '--delete-corrupted', '-j', '-'], 'cache-extract', env, deadline, path)
        result['extraction_exit_code'] = code; save()
        assert code == 0, 'Pinned leantar extraction failed'
        assert {name: digest((cache_dir / name).read_bytes()) for name in served_all} == before
    # Misses are not fresh proof credit. Existing finite source fallback and
    # complete companion/materialization checks remain mandatory after return.
    return result


def cache_split_planner_completed(stage):
    assert stage['exit_code'] == 0 and stage['status'] == 'SUCCEEDED', 'Planner did not succeed'
    assert stage['owner_reaped'] is True and stage['remaining_session_pids'] == [], 'Planner not completely reaped'


def cache_split_source_seals(dependency_inventory):
    result = {}
    for prefix, entries in dependency_inventory.items():
        dep = ROOT / prefix
        for relative, record in entries.items():
            if not (relative.endswith('.lean') or Path(relative).name in ('lean-toolchain', 'lake-manifest.json')):
                continue
            assert record[1] == 'blob' and record[0] in ('100644', '100755')
            path = dep / relative
            raw, seal = regular_seal(path)
            assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == record[2]
            assert str(path) not in result
            result[str(path)] = seal
    for path in (PKG / 'lean-toolchain', PKG / 'lake-manifest.json'):
        _, result[str(path)] = regular_seal(path)
    assert result, 'Empty dependency Source provenance'
    return result


def cache_split_seals_POST(seals):
    for path, before in seals.items():
        _, after = regular_seal(Path(path)); assert after == before, 'Cache input POST drift: ' + path


def cache_split_source_namespace(dependency_inventory):
    for prefix, entries in dependency_inventory.items():
        root = ROOT / prefix
        expected = {str(root / p) for p in entries if p.endswith('.lean')}
        actual = set()
        for directory, dirs, files in os.walk(root, followlinks=False):
            if Path(directory) == root and '.git' in dirs: dirs.remove('.git')
            for name in dirs:
                path = Path(directory) / name; info = path.lstat()
                assert stat.S_ISDIR(info.st_mode) and not path.is_symlink() and not getattr(info, 'st_file_attributes', 0) & 0x400
            for name in files:
                if name.endswith('.lean'):
                    path = Path(directory) / name
                    assert stat.S_ISREG(path.lstat().st_mode) and not path.is_symlink()
                    actual.add(str(path))
        assert actual == expected, 'Dependency Source path namespace drift: ' + prefix


def cache_split_context_search(env, cwd, compiler_prefix):
    # Exact Lean.Util.Path.getSrcSearchPath then Cache.IO.SearchPath.relativize.
    # Root's source paths are normalized in the planner; compare resolved
    # physical order, retaining the original lexical list in the receipt.
    roots = [Path(p) for p in env.get('LEAN_SRC_PATH', '').split(os.pathsep) if p]
    roots += [compiler_prefix / 'bin/../src/lean/lake', compiler_prefix / 'bin/../src/lean']
    return [str((cwd / path).resolve()) for path in roots]


def acquire_pinned_cache_phase_split(mathlib, lean, env, compiler_prefix, cache_source_view,
                                    roots, dependency_inventory, bootstrap):
    import shutil
    cache_split_no_overrides(env)
    deadline = time.monotonic() + 1800  # Same aggregate cache-stage bound.
    mathlib = mathlib.resolve(); cache_dir = Path(env['MATHLIB_CACHE_DIR'])
    assert cache_dir.is_absolute() and not cache_dir.exists()
    for relative, h in CACHE_SPLIT_UPSTREAM.items():
        raw, _ = regular_seal(mathlib / relative); assert digest(raw) == h
    # Authenticate the checkout's actual remote before selecting canonical
    # master -> legacy policy; no fork/scope/URL fallback is silently assumed.
    remote = run(['git', '--no-replace-objects', '-C', str(mathlib), 'remote', 'get-url', 'origin'],
                 'cache-canonical-repository', env=env, timeout=max(0.001, deadline-time.monotonic())).decode().strip()
    assert remote in ('https://github.com/leanprover-community/mathlib4',
                      'https://github.com/leanprover-community/mathlib4.git'), 'Unsupported cache repository'
    cache_split_source_namespace(dependency_inventory)
    seals = cache_split_source_seals(dependency_inventory)
    lean_sources = {path: seal for path, seal in seals.items() if path.endswith('.lean')}
    for path in bootstrap.rglob('*'):
        if path.is_file():
            _, seals[str(path)] = regular_seal(path)
    for key in ('derived', 'compiler', 'leantar'):
        path = Path(cache_source_view[key]['path']); _, seals[str(path)] = regular_seal(path)
    planner = EVIDENCE / 'cache-source-view/CachePlan.lean'
    assert not planner.exists()
    with planner.open('xb') as stream: stream.write(CACHE_PLAN_SOURCE.encode('utf8'))
    _, seals[str(planner)] = regular_seal(planner)
    plan_env = dict(env, POINT4_CACHE_PLAN_SOURCE_BOUND=str(len(lean_sources)))
    failure = None
    try:
        raw = run([lean, '-j1', '-M5632', '-R', str(planner.parent), '--run', str(planner), *roots],
                  'cache-hash-plan', env=plan_env, timeout=max(0.001, deadline-time.monotonic()))
        stage = receipt['stages'][-1]
        cache_split_planner_completed(stage)
        plan = cache_split_validate_plan(raw, roots, mathlib, cache_dir, PKG, lean_sources)
        actual_search = [str((PKG / Path(p)).resolve()) for p in plan['source_search_path']]
        assert actual_search == cache_split_context_search(env, PKG, compiler_prefix), 'Hash source search order drift'
        cache_split_seals_POST(seals)
        cache_split_source_namespace(dependency_inventory)
        path = EVIDENCE / 'cache-hash-plan.json'
        with path.open('xb') as stream: stream.write(raw)
        _, seals[str(path)] = regular_seal(path)
        curl = shutil.which('curl', path=env.get('PATH', '')); assert curl, 'Missing curl'
        curl = str(Path(curl).resolve(strict=True)); leantar = str((compiler_prefix / 'bin/leantar').resolve(strict=True))
        code, version, _ = cache_split_tool_stage([curl, '--disable', '--version'], 'cache-curl-version', env, deadline)
        match = re.match(rb'curl (\d+)\.(\d+)\.(\d+)\b', version)
        assert code == 0 and match and tuple(map(int, match.groups())) >= (7, 81, 0), 'Pinned JSON protocol needs supported curl'
        outcome = cache_split_acquire(plan, env, curl, leantar, deadline)
        receipt['cache_phase_split'] = dict(planner=str(planner), planner_sha256=seals[str(planner)]['sha256'],
            plan=str(path), plan_sha256=seals[str(path)]['sha256'], selected_modules=len(plan['modules']),
            full_hash_inputs=len(plan['full_hash_inputs']), source_inventory_bound=len(lean_sources),
            planner_reaped_before_acquisition=True, acquisition_zero_Lean=True,
            repo=remote, containers=['master', 'legacy'], missing=outcome['missing'],
            physical_Source_POST='PENDING', Point4='OPEN')
    except BaseException as exc:
        failure = exc
        receipt.setdefault('cache_phase_split', {}).update(status='FAILED', error={'type': type(exc).__name__, 'message': str(exc)})
        raise
    finally:
        try:
            cache_split_seals_POST(seals)
            cache_split_source_namespace(dependency_inventory)
            verify_pinned_cache_source_view(cache_source_view, env, receipt)
            receipt.setdefault('cache_phase_split', {})['physical_Source_POST'] = 'UNCHANGED'
        except BaseException as post_error:
            receipt.setdefault('cache_phase_split', {})['Source_POST_error'] = repr(post_error)
            if failure is None: raise
        finally: save()

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
    env = pinned_compiler_environment(env, receipt)
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
    env, cache_source_view = prepare_pinned_cache_source_view(mathlib, compiler_prefix, receipt, env, EVIDENCE / 'cache-source-view')
    receipt['cache_source_view'] = cache_source_view
    save()
    cache_order, seen, active = [], set(), set()
    def bootstrap_visit(name):
        if name in seen or (not name.startswith('Cache.') and artifact_exists(name)):
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
        if name == 'Cache.IO':
            assert str(source) == cache_source_view['original']['path'], 'Cache.IO source namespace drift'
            source = Path(cache_source_view['derived']['path'])
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
    # The selected cached Mathlib roots also import this pinned support module.
    # Compile its genuine source and companions through the same bounded DFS.
    library_note_source = source_path('Batteries.Util.LibraryNote')
    assert library_note_source == (PKG / '.lake/packages/batteries/Batteries/Util/LibraryNote.lean').resolve(), 'Pinned Batteries.Util.LibraryNote source root drift'
    verify_dependency_source(library_note_source)
    assert digest(library_note_source.read_bytes()) == 'ecc6ebe4c32eb3c90bb94d0f4ef9eb8d530d95469ba48c0b1995f7c2172c93d8', 'Pinned Batteries.Util.LibraryNote source drift'
    bootstrap_visit('Batteries.Util.LibraryNote')
    bootstrap_visit('Cache.IO')
    bootstrap_visit('Cache.Main')
    for i, (name, source) in enumerate(cache_order):
        verify_pinned_cache_source_view(cache_source_view, env, receipt)
        try:
            serial_compile(name, source, bootstrap, lean, env, 'cache-bootstrap-' + str(i), name.startswith('Cache.'))
        finally:
            verify_pinned_cache_source_view(cache_source_view, env, receipt)
    # Pinned Lean hashing exits and is reaped before any curl/leantar acquisition.
    # The existing Lean-stage run()/compiler classifier remains unchanged.
    acquire_pinned_cache_phase_split(mathlib, lean, env, compiler_prefix, cache_source_view,
        admission['external_mathlib_roots'], dependency_inventory, bootstrap)
    # Bootstrap packages serve Cache.get only. Lean resolves an entire package
    # at its first search root, so partial bootstrap roots must not shadow the
    # genuine cached dependency packages during the source/probe compilation.
    env['LEAN_PATH'] = os.pathsep.join(map(str, (local, support))) + os.pathsep + old_path
    del env[ENV_KEY]
    receipt['cache_source_view_removed_before_mathematics'] = True
    save()
    artifact_dirs = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep) if p]
    artifact_dirs = [p if p.is_absolute() else PKG / p for p in artifact_dirs]
    artifact_dirs.append(prefix)
    materialized = materialize_pinned_mathlib_cache(mathlib / '.lake/build/lib/lean', support,
        mathlib, dependency_inventory[mathlib.relative_to(ROOT).as_posix()])
    materialized_path = EVIDENCE / 'coherent-pinned-Mathlib-cache.json'
    materialized_path.write_text(json.dumps(materialized, indent=2) + '\n')
    receipt['coherent_pinned_cache_sha256'] = digest(materialized_path.read_bytes())
    save()
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
