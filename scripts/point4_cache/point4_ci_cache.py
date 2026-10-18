"""Exact-candidate GitHub cache pilot. Caches accelerate mandatory builds; they prove nothing.

Only curvature/.lake/build is transported. Dependency sources/.git directories are
never cached; the pinned lean-action continues to retrieve the official Mathlib cache.
Origin trust is the GitHub cache service's repository/ref scope and the reviewed writer
workflow. The inventory checks integrity, not independent producer authenticity.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import time
import tomllib

SCHEMA = 'point4-exact-candidate-cache-v1'
CACHE_ACTION = 'caa296126883cff596d87d8935842f9db880ef25'
COMPILER_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
MATHLIB = 'db584cd6d46c92f209a44c0f1c829460d327499d'
MAX_FILES = 100_000
MAX_BYTES = 8 * 1024**3
MANIFEST = 'inventory.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def regular(path):
    for item in (path, *path.parents):
        mode = item.lstat().st_mode
        require(not stat.S_ISLNK(mode), f'Symlink rejected: {item}')
        require(stat.S_ISREG(mode) if item == path else stat.S_ISDIR(mode), f'Invalid path: {item}')


def safe_directories(path):
    """Check existing ancestors before creating or replacing generated directories."""
    for item in (path, *path.parents):
        if item.exists() or item.is_symlink():
            mode = item.lstat().st_mode
            require(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode), f'Unsafe directory ancestor: {item}')


def make_directories(path):
    safe_directories(path)
    path.mkdir(parents=True, exist_ok=True)
    safe_directories(path)


def file_digest(path):
    regular(path)
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024**2), b''):
            value.update(block)
    return value.hexdigest()


def strict_json(path):
    regular(path)
    require(path.stat().st_size <= 32 * 1024**2, 'JSON inventory too large')
    def pairs(rows):
        result = {}
        for key, value in rows:
            require(key not in result, f'Duplicate JSON key: {key}')
            result[key] = value
        return result
    def invalid(value):
        raise ValueError(f'Nonfinite JSON: {value}')
    def finite(value):
        number = float(value)
        require(math.isfinite(number), 'Nonfinite JSON number')
        return number
    return json.loads(path.read_bytes(), object_pairs_hook=pairs, parse_constant=invalid, parse_float=finite)


def command(cwd, *args):
    return subprocess.check_output(args, cwd=cwd, timeout=60, env={**os.environ, 'GIT_NO_LAZY_FETCH': '1'}).decode().strip()


def git(root, *args):
    return command(root, 'git', '--no-replace-objects', '-c', 'core.fsmonitor=false', '-c', 'core.fileMode=true', *args)


def clean(root):
    git(root, 'diff', '--no-ext-diff', '--no-textconv', '--exit-code', 'HEAD', '--', '.')
    git(root, 'diff', '--cached', '--no-ext-diff', '--no-textconv', '--exit-code', 'HEAD', '--', '.')


def relative_path(value):
    require(isinstance(value, str) and value and len(value) <= 1024, 'Invalid relative path')
    require(not value.startswith('/') and '\\' not in value and ':' not in value, 'Absolute/aliased path')
    require(all(part not in ('', '.', '..') for part in value.split('/')), 'Path traversal or empty component')
    require(all(ord(c) >= 32 and ord(c) != 127 for c in value), 'Control character in path')
    return Path(value)


def tracked_source(root, directory):
    """Bind local path dependencies to actual committed bytes, not a path name."""
    prefix = directory.relative_to(root).as_posix()
    rows = git(root, 'ls-tree', '-rz', 'HEAD', '--', prefix).split('\0')
    result = {}
    for row in rows:
        if not row:
            continue
        descriptor, name = row.split('\t', 1)
        mode, kind, oid = descriptor.split()
        require(kind == 'blob' and mode in ('100644', '100755'), 'Unsupported tracked source kind')
        path = root / relative_path(name)
        regular(path)
        raw = path.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(actual == oid and bool(path.stat().st_mode & 0o111) == (mode == '100755'), f'Dirty source: {name}')
        result[name] = [mode, oid, digest(raw)]
    require(result, f'Untracked/empty path dependency: {prefix}')
    return digest(canonical(result))


def parse_targets(raw):
    targets = json.loads(raw)
    require(isinstance(targets, list) and targets, 'Empty/invalid target set')
    require(all(isinstance(t, str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', t) for t in targets), 'Nonliteral Lean target')
    require(len(targets) == len(set(targets)), 'Duplicate target set')
    return targets


def validate_compiler(version):
    require(re.fullmatch(r'Lean \(version 4\.33\.0, [^,\n]+, commit ' + COMPILER_COMMIT + r', Release\)', version) is not None,
            'Compiler is not the pinned official Lean 4.33.0 commit')


def cache_key(identity):
    require(identity['schema'] == SCHEMA, 'Unknown cache schema')
    return 'point4-candidate-v1-' + digest(canonical(identity))


def identity(root, package, targets, build_args):
    root = root.resolve()
    relative_path(package)
    package_dir = root / package
    require(package == 'curvature', 'Pilot supports only the curvature package')
    require(isinstance(build_args, list) and all(isinstance(x, str) for x in build_args), 'Invalid build arguments')
    # Unknown Lean/Lake environment overrides can introduce external source roots
    # or plugins. This bounded pilot supports the workflow's default environment.
    require(not any(value and name.startswith(('LEAN_', 'LAKE_')) for name, value in os.environ.items()),
            'Lean/Lake environment overrides are unsupported by this pilot')
    clean(root)
    head, tree = git(root, 'rev-parse', 'HEAD'), git(root, 'rev-parse', 'HEAD^{tree}')
    require(not os.environ.get('EXPECTED_SHA') or os.environ['EXPECTED_SHA'] == head, 'Checked-out HEAD differs from expected candidate')
    toolchain = package_dir / 'lean-toolchain'
    regular(toolchain)
    require(toolchain.read_bytes() == b'leanprover/lean4:v4.33.0\n', 'Wrong package toolchain')
    manifest_path = package_dir / 'lake-manifest.json'
    manifest = strict_json(manifest_path)
    require(manifest['packagesDir'] == '.lake/packages', 'Unsupported package directory')
    config = package_dir / 'lakefile.toml'
    regular(config)
    options = tomllib.loads(config.read_text())
    require(options['name'] == 'PoincareCurvature', 'Wrong package identity')
    dependencies = []
    for entry in manifest['packages']:
        name = entry['name']
        require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*', name) is not None, 'Unsafe dependency name')
        if entry['type'] == 'git':
            revision = entry['rev']
            require(re.fullmatch('[0-9a-f]{40}', revision) is not None, 'Unpinned Git dependency')
            path = package_dir / '.lake/packages' / name
            safe_directories(path)
            require(Path(git(path, 'rev-parse', '--show-toplevel')).resolve() == path.resolve(), 'Dependency is not its own checkout')
            clean(path)
            require(git(path, 'rev-parse', 'HEAD') == revision, f'Dependency revision mismatch: {name}')
            dependencies.append(dict(kind='git', name=name, manifest=entry, head=revision,
                                     tree=git(path, 'rev-parse', 'HEAD^{tree}')))
        elif entry['type'] == 'path':
            path = (package_dir / entry['dir']).resolve()
            require(path.is_relative_to(root) and path != root, 'Path dependency escapes repository')
            dependencies.append(dict(kind='path', name=name, manifest=entry,
                                     directory=path.relative_to(root).as_posix(), source=tracked_source(root, path)))
        else:
            raise ValueError('Unsupported dependency kind')
    mathlib = [d for d in dependencies if d['name'] == 'mathlib']
    require(len(mathlib) == 1 and mathlib[0]['head'] == MATHLIB, 'Wrong Mathlib pin')
    version = command(package_dir, 'lake', 'env', 'lean', '--version')
    validate_compiler(version)
    compiler_prefix = Path(command(package_dir, 'lake', 'env', 'lean', '--print-prefix'))
    compiler = compiler_prefix / 'bin/lean'
    provider = {name: os.environ.get(name, '') for name in ('GITHUB_REPOSITORY', 'GITHUB_REF', 'GITHUB_WORKFLOW_REF', 'GITHUB_WORKFLOW_SHA')}
    require(all(provider.values()), 'GitHub repository/ref/workflow provenance required')
    # Option values are hashed to avoid putting environment values in cache evidence.
    option_env = {name: digest(value.encode()) for name, value in os.environ.items()
                  if name.startswith(('LEAN_', 'LAKE_')) or name in ('ELAN_TOOLCHAIN', 'CC', 'CXX', 'CFLAGS', 'CXXFLAGS', 'LDFLAGS')}
    return dict(schema=SCHEMA, cache_action=CACHE_ACTION, package=package, package_name=options['name'],
                head=head, tree=tree, toolchain_sha256=file_digest(toolchain), manifest_sha256=file_digest(manifest_path),
                config_sha256=file_digest(config), effective_package_options=options, option_environment_sha256=option_env,
                compiler_version=version, compiler_binary_sha256=file_digest(compiler), dependencies=dependencies,
                package_source=tracked_source(root, package_dir), targets=targets, build_arguments=build_args,
                platform=dict(os=platform.system(), machine=platform.machine(), runner_os=os.environ.get('RUNNER_OS', ''),
                              runner_arch=os.environ.get('RUNNER_ARCH', ''), image_os=os.environ.get('ImageOS', ''),
                              image_version=os.environ.get('ImageVersion', '')), provider_scope=provider,
                source_repository=os.environ.get('P4_SOURCE_REPOSITORY', provider['GITHUB_REPOSITORY']),
                output_root='curvature/.lake/build')


def inventory(directory):
    """Closed regular-file inventory; no symlink, special file, or case alias."""
    safe_directories(directory)
    require(directory.is_dir() and not directory.is_symlink(), 'Missing/symlink output directory')
    records, folded, total, namespace_entries = {}, set(), 0, 0
    for parent, dirs, files in os.walk(directory, followlinks=False):
        base = Path(parent)
        namespace_entries += len(dirs) + len(files)
        require(namespace_entries <= 2 * MAX_FILES, 'Cache namespace resource bound exceeded')
        for name in dirs + files:
            relative = (base / name).relative_to(directory).as_posix()
            relative_path(relative)
            require(relative.casefold() not in folded, 'Case alias in cache namespace')
            folded.add(relative.casefold())
        for name in dirs:
            mode = (base / name).lstat().st_mode
            require(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode), 'Non-directory/symlink in cache')
        for name in files:
            path = base / name
            relative = path.relative_to(directory).as_posix()
            relative_path(relative)
            regular(path)
            info = path.stat()
            require(not info.st_mode & 0o7000, 'Special permission bits in cache file')
            total += info.st_size
            require(len(records) < MAX_FILES and total <= MAX_BYTES, 'Cache inventory resource bound exceeded')
            records[relative] = dict(bytes=info.st_size, mode=stat.S_IMODE(info.st_mode), sha256=file_digest(path))
    return records


def validate_snapshot(snapshot, expected_identity):
    """Validate every byte before any cached file reaches active Lake outputs."""
    require(snapshot.is_dir() and not snapshot.is_symlink(), 'Missing snapshot')
    require({p.name for p in snapshot.iterdir()} == {MANIFEST, 'payload'}, 'Incomplete/extra snapshot roots')
    saved = strict_json(snapshot / MANIFEST)
    require(saved['schema'] == SCHEMA and saved['identity'] == expected_identity, 'Cache identity mismatch')
    require(saved['key'] == cache_key(expected_identity), 'Cache key mismatch')
    require(saved['provider_scope'] == expected_identity['provider_scope'], 'Cache provider/ref provenance mismatch')
    require(isinstance(saved['inventory'], dict) and saved['inventory'], 'Empty inventory')
    for path, row in saved['inventory'].items():
        relative_path(path)
        require(set(row) == {'bytes', 'mode', 'sha256'} and type(row['bytes']) is int and row['bytes'] >= 0, 'Bad inventory record')
        require(type(row['mode']) is int and 0 <= row['mode'] <= 0o777 and re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None, 'Bad inventory mode/hash')
    actual = inventory(snapshot / 'payload')
    require(actual == saved['inventory'], 'Corrupt/incomplete/extra cache payload')
    require(saved['bytes'] == sum(row['bytes'] for row in actual.values()), 'Cache byte count mismatch')
    return saved


def copy_regular_tree(source, destination):
    require(not destination.exists() and not destination.is_symlink(), 'Destination already exists')
    make_directories(destination)
    for path in inventory(source):
        src, dst = source / path, destination / path
        make_directories(dst.parent)
        shutil.copyfile(src, dst)
        os.chmod(dst, stat.S_IMODE(src.stat().st_mode))


def replace_outputs(root, snapshot, expected_identity):
    saved = validate_snapshot(snapshot, expected_identity)
    target = root / relative_path(expected_identity['output_root'])
    require(expected_identity['output_root'] == 'curvature/.lake/build', 'Unsupported output root')
    # Generated output parents must be directories; never follow a source symlink.
    make_directories(target.parent)
    staged = target.with_name('point4-cache-build-staged')
    require(not staged.exists() and not staged.is_symlink(), 'Stale staged output')
    copy_regular_tree(snapshot / 'payload', staged)
    require(inventory(staged) == saved['inventory'], 'Staged-copy corruption')
    backup = target.with_name('point4-cache-build-backup')
    require(not backup.exists() and not backup.is_symlink(), 'Stale output backup')
    had_target = target.exists() or target.is_symlink()
    if had_target:
        inventory(target)  # Reject links/special files before moving generated files.
        target.rename(backup)
    try:
        staged.rename(target)
        require(inventory(target) == saved['inventory'], 'Injected-output corruption')
    except BaseException:
        if target.exists() and not target.is_symlink():
            shutil.rmtree(target)
        if had_target:
            backup.rename(target)
        raise
    if had_target:
        shutil.rmtree(backup)
    return saved['bytes']


def write_json(path, value):
    make_directories(path.parent)
    if path.exists() or path.is_symlink():
        regular(path)
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def emit(outputs):
    output_path = os.environ.get('GITHUB_OUTPUT')
    if output_path:
        with open(output_path, 'a') as stream:
            for name, value in outputs.items():
                require(re.fullmatch('[A-Za-z0-9_-]+', name) is not None and '\n' not in str(value), 'Invalid action output')
                stream.write(f'{name}={value}\n')
    print(json.dumps(outputs, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('identity', 'restore', 'snapshot', 'report'))
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--state-dir', type=Path, required=True)
    parser.add_argument('--package', default='curvature')
    parser.add_argument('--targets-json', required=True)
    parser.add_argument('--build-arguments-json', default='[]')
    parser.add_argument('--cache-hit', default='')
    parser.add_argument('--matched-key', default='')
    parser.add_argument('--manual-success', default='false')
    parser.add_argument('--save-step-outcome', default='not-requested')
    args = parser.parse_args()
    started = time.monotonic()
    require(args.root.is_absolute() and args.state_dir.is_absolute(), 'Absolute root/state directory required')
    require(args.root == args.root.resolve() and args.state_dir == args.state_dir.resolve(), 'Root/state aliases rejected')
    require(not args.state_dir.is_relative_to(args.root), 'Cache transport state must stay outside source tree')
    targets = parse_targets(args.targets_json)
    current = identity(args.root, args.package, targets, json.loads(args.build_arguments_json))
    key = cache_key(current)
    state_path, snapshot = args.state_dir / 'state.json', args.state_dir / 'snapshot'
    if args.phase == 'identity':
        require(not args.state_dir.exists(), 'Cache state already initialized')
        state = dict(identity=current, key=key, started=started, identity_seconds=time.monotonic() - started,
                     restore_complete=False, cache_hit=False)
        write_json(state_path, state)
        emit(dict(key=key, identity_seconds=time.monotonic() - started))
        return
    state = strict_json(state_path)
    require(state['identity'] == current and state['key'] == key, 'Source/pins/options/provider changed after identity')
    if args.phase == 'restore':
        require(not state['restore_complete'], 'Restore already completed')
        require(args.cache_hit in ('', 'false', 'true'), 'Invalid cache-hit state')
        hit = args.cache_hit == 'true'
        if hit:
            require(args.matched_key == key, 'Only an exact cache key may be restored')
            restored = replace_outputs(args.root, snapshot, current)
        else:
            require(not args.matched_key, 'Unexpected partial cache match')
            require(not snapshot.is_symlink(), 'Symlink snapshot rejected')
            require(not snapshot.exists() or not any(snapshot.iterdir()), 'Incomplete cache restore; fail before builds')
            restored = 0
        state.update(cache_hit=hit, restored_bytes=restored, restore_complete=True,
                     restore_seconds=time.monotonic() - state['started'], validation_seconds=time.monotonic() - started)
        write_json(state_path, state)
        emit(dict(key=key, cache_hit=str(hit).lower(), restored_bytes=restored,
                  restore_seconds=state['restore_seconds'], validation_seconds=state['validation_seconds'], proof_credit=0))
    elif args.phase == 'snapshot':
        require(args.manual_success == 'true' and state['restore_complete'], 'Save requires successful manual gates after restore')
        output = args.root / current['output_root']
        records = inventory(output)
        require(records, 'Successful candidate build produced no cacheable outputs')
        state.update(post_build_files=len(records), post_build_bytes=sum(r['bytes'] for r in records.values()),
                     snapshot_seconds=time.monotonic() - started, save_requested=not state['cache_hit'])
        if not state['cache_hit']:
            require(not snapshot.is_symlink(), 'Symlink snapshot rejected')
            require(not snapshot.exists() or not any(snapshot.iterdir()), 'Snapshot transport directory is not empty')
            make_directories(snapshot)
            copy_regular_tree(output, snapshot / 'payload')
            manifest = dict(schema=SCHEMA, identity=current, key=key, provider_scope=current['provider_scope'],
                            producer_run_id=os.environ.get('GITHUB_RUN_ID'), producer_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'),
                            inventory=records, bytes=state['post_build_bytes'])
            write_json(snapshot / MANIFEST, manifest)
            validate_snapshot(snapshot, current)
        state['inventory_sha256'] = file_digest(snapshot / MANIFEST)
        state['snapshot_seconds'] = time.monotonic() - started
        state['snapshot_finished_monotonic'] = time.monotonic()
        write_json(state_path, state)
        emit(dict(key=key, can_save=str(state['save_requested']).lower(), output_files=len(records),
                  output_bytes=state['post_build_bytes'], snapshot_seconds=state['snapshot_seconds'], proof_credit=0))
    else:
        state.update(save_action_step_outcome=args.save_step_outcome,
                     save_action_wall_seconds=started - state['snapshot_finished_monotonic'],
                     report_validation_seconds=time.monotonic() - started,
                     elapsed_since_identity_seconds=time.monotonic() - state['started'])
        write_json(state_path, state)
        emit(dict(key=key, cache_hit=str(state['cache_hit']).lower(), restored_bytes=state['restored_bytes'],
                  save_action_step_outcome=args.save_step_outcome, proof_credit=0))
        # A successful cache action step is not evidence that the provider stored an entry.
        summary = os.environ.get('GITHUB_STEP_SUMMARY')
        if summary:
            with open(summary, 'a') as stream:
                stream.write('### Point-4 exact-candidate cache pilot\n\n```json\n' + json.dumps({k: v for k, v in state.items() if k != 'identity'}, indent=2) + '\n```\n')


if __name__ == '__main__':
    main()
