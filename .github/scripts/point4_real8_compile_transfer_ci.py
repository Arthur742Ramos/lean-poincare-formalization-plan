#!/usr/bin/env python3
"""Compile public inputs only; export a bounded complete build-file readset.

This does not fetch historical artifact inputs or run the guard/real8. The
recipient must authenticate the whole payload and regenerate Lake configuration
at its own paths before a separately reviewed actual runtime invocation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import sys
import time
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import point4_real8_ci as ci

FILE_COUNT_LIMIT = 50000
FILE_BYTES_LIMIT = 512 * 1024**2
UNCOMPRESSED_LIMIT = 8 * 1024**3
ARCHIVE_LIMIT = 2 * 1024**3
EXECUTION_SECONDS = 4500


def path_dependency_state(proof):
    root = proof / 'hamilton-ivey-reaction'
    lake = root / '.lake'
    ci.require(root.is_dir() and not root.is_symlink() and not lake.is_symlink(), 'Path dependency alias')
    directories = []
    if lake.exists():
        ci.require(lake.is_dir(), 'Non-directory path dependency build root')
        for path in lake.rglob('*'):
            ci.require(path.is_dir() and not path.is_symlink(),
                       'Unmodelled path-dependency compiled file; export must be reviewed')
            directories.append(str(path.relative_to(lake)))
    return {'source_root': 'hamilton-ivey-reaction',
            'source_configuration': {name: ci.identity(root / name) for name in
                ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')},
            'lake_directory_exists': lake.exists(), 'empty_directories_only': sorted(directories),
            'compiled_files_absent': True,
            'native_21_module_import_closure_uses_this_namespace': False}


class BoundedArchive:
    def __init__(self, stream, deadline):
        self.stream, self.deadline = stream, deadline

    def write(self, data):
        ci.require(time.monotonic() < self.deadline, 'Archive write deadline')
        ci.require(self.stream.tell() + len(data) <= ARCHIVE_LIMIT, 'Compressed payload limit before write')
        return self.stream.write(data)

    def __getattr__(self, name):
        return getattr(self.stream, name)


def payload_files(pkg):
    # Retain *all* generated build files, including private/server/IR companions,
    # native libraries and utilities. There is no guessed 21-olean-only subset.
    roots = [pkg / '.lake/build', *(pkg / '.lake/packages').glob('*/.lake/build')]
    files = {}
    for root in roots:
        if not root.exists():
            continue
        for path in sorted(root.rglob('*')):
            ci.require(not path.is_symlink(), 'Build namespace symlink')
            if path.is_file():
                files[str(path.relative_to(pkg))] = path
    # Hosted configuration objects are retained as provenance data. The local
    # recipient must NOT install these path-dependent configuration objects.
    for lake in [pkg / '.lake', *(pkg / '.lake/packages').glob('*/.lake')]:
        if lake.exists():
            for path in lake.iterdir():
                if path.is_file():
                    ci.require(not path.is_symlink(), 'Lake configuration symlink')
                    files[str(path.relative_to(pkg))] = path
    ci.require(0 < len(files) <= FILE_COUNT_LIMIT, 'Payload file-count bound')
    return dict(sorted(files.items()))


def build_payload(pkg, output, deadline):
    ci.require(not output.exists(), 'Export directory must be fresh')
    output.mkdir(mode=0o700, parents=True)
    ci.require(shutil.disk_usage(output).free >= ARCHIVE_LIMIT + 512 * 1024**2,
               'Insufficient bounded archive disk reserve')
    files, rows, total = payload_files(pkg), {}, 0
    partial = output / 'compiled-closure.zip.partial'
    final = output / 'compiled-closure.zip'
    with partial.open('xb') as stream, zipfile.ZipFile(BoundedArchive(stream, deadline), 'w',
            compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
        for name, path in files.items():
            ci.require(time.monotonic() < deadline, 'Cumulative compilation/packing deadline')
            st = path.lstat()
            ci.require(stat.S_ISREG(st.st_mode) and 0 <= st.st_size <= FILE_BYTES_LIMIT,
                       'Nonregular or oversized compiled payload member')
            total += st.st_size
            ci.require(total <= UNCOMPRESSED_LIMIT, 'Uncompressed payload limit')
            before = ci.identity(path)
            archive.write(path, arcname=name)
            ci.require(ci.identity(path) == before, 'Payload changed while packing')
            ci.require(partial.stat().st_size <= ARCHIVE_LIMIT, 'Compressed payload limit')
            info = archive.getinfo(name)
            rows[name] = dict(before, CRC32=info.CRC, mode=stat.S_IMODE(st.st_mode),
                role='compiled-build' if '/build/' in name else 'hosted-config-provenance-only-do-not-install')
    ci.require(partial.stat().st_size <= ARCHIVE_LIMIT, 'Final archive limit')
    partial.rename(final)
    # Hash the archive in bounded memory: the archive has its own finite cap,
    # separate from the small receipt-directory cap.
    digest = hashlib.sha256()
    with final.open('rb') as stream:
        while chunk := stream.read(1024 * 1024):
            ci.require(time.monotonic() < deadline, 'Archive identity deadline')
            digest.update(chunk)
    record = {'archive': {'bytes': final.stat().st_size, 'sha256': digest.hexdigest()},
        'files': rows, 'member_count': len(rows), 'uncompressed_bytes': total,
        'limits': {'member_count': FILE_COUNT_LIMIT, 'individual_file_bytes': FILE_BYTES_LIMIT,
                   'uncompressed_bytes': UNCOMPRESSED_LIMIT, 'archive_bytes': ARCHIVE_LIMIT},
        'historical_inputs_or_private_review_records_included': False,
        'scope': 'Complete public-source generated build files; no guard/real8 PASS',
        'hosted_configs_must_be_regenerated_locally': True}
    # Small bounded manifest; the large ZIP is never charged to the 128MiB
    # receipt allowance or silently uploaded through that allowance.
    raw = (json.dumps(record, indent=2, sort_keys=True) + '\n').encode()
    ci.require(len(raw) <= 32 * 1024**2, 'Payload manifest limit')
    (output / 'compiled-closure-manifest.json').write_bytes(raw)
    return {'archive': record['archive'], 'manifest': ci.identity(output / 'compiled-closure-manifest.json'),
            'member_count': len(rows), 'uncompressed_bytes': total}


def main(args):
    proof, control, evidence, description = ci.preflight(args)
    before = json.loads(ci.read_regular(evidence / 'preflight.json'))
    ci.require(before == {'proof': ci.snapshot(proof), 'control': ci.snapshot(control)}, 'Source drift after preflight')
    ci.require(not any(os.environ.get(k) for k in ('MATHLIB_CACHE_GET_URL', 'MATHLIB_CACHE_FROM',
        'MATHLIB_CACHE_REPO_SCOPE', 'MATHLIB_CACHE_SAS', 'MATHLIB_CACHE_AZURE_BEARER_TOKEN')), 'Cache override forbidden')
    work = args.work.resolve()
    ci.require(not work.exists() and work != evidence and evidence not in work.parents and
               work not in evidence.parents and proof not in work.parents and control not in work.parents,
               'Fresh separate public-output workdir required')
    work.mkdir(mode=0o700, parents=True)
    started = time.monotonic()
    deadline = started + EXECUTION_SECONDS
    ci.EXECUTION_DEADLINE = deadline
    pkg, dependencies, compiled_pre = proof / 'curvature', [], None
    state = {'candidate': ci.PROOF_SHA, 'tree': ci.PROOF_TREE, 'caller': args.caller_sha,
        'status': 'RUNNING_PUBLIC_COMPILE_ONLY_UNVERIFIED', 'Point4': 'OPEN',
        'historical_input_download_attempted': False, 'guard_or_real8_executed': False,
        'platform': {'system': platform.system(), 'machine': platform.machine(),
                     'libc': list(platform.libc_ver()), 'python': sys.version}}
    try:
        ci.require(platform.system() == 'Linux' and platform.machine() == 'x86_64', 'Unsupported producer platform')
        version = ci.run_process(['lean', '--version'], pkg, evidence, 'lean-version', 30).decode()
        ci.require('version 4.33.0,' in version and ci.LEAN_COMMIT in version, 'Wrong compiler')
        prefix = Path(ci.run_process(['lean', '--print-prefix'], pkg, evidence, 'lean-prefix', 30).decode().strip())
        state['compiler'] = {name: ci.identity(prefix / name) for name in ci.OFFICIAL_COMPILER_FILES}
        ci.require(all(state['compiler'][name]['sha256'] == sha for name, sha in ci.OFFICIAL_COMPILER_FILES.items()),
                   'Official compiler bytes drift')
        manifest = json.loads(ci.read_regular(pkg / 'lake-manifest.json'))
        for entry in manifest['packages']:
            if entry['type'] != 'git':
                continue
            ci.require(re.fullmatch('[0-9a-f]{40}', entry['rev']) and re.fullmatch('[A-Za-z0-9_-]+', entry['name']), 'Invalid dependency pin')
            ci.require(entry['url'].startswith(('https://github.com/leanprover-community/', 'https://github.com/leanprover/')), 'Unadmitted source registry')
            dest = pkg / '.lake/packages' / entry['name']
            ci.require(not dest.exists(), 'Pre-existing dependency source/cache')
            dest.mkdir(parents=True)
            name = entry['name']
            for suffix, argv, limit in [
                ('init', ['git', 'init', '--quiet'], 10),
                ('origin', ['git', 'remote', 'add', 'origin', entry['url']], 10),
                ('fetch', ['git', 'fetch', '--no-tags', '--depth=1', 'origin', entry['rev']], 90),
                ('checkout', ['git', 'checkout', '--detach', 'FETCH_HEAD'], 20)]:
                ci.run_process(argv, dest, evidence, 'dependency-' + name + '-' + suffix, limit)
            ci.require(ci.git(dest, 'rev-parse', 'HEAD') == entry['rev'], 'Dependency HEAD mismatch')
            dependencies.append({'name': name, 'root': str(dest), 'rev': entry['rev'], 'source': ci.snapshot(dest)})
        ci.require(len(dependencies) == 9 and next(x['rev'] for x in dependencies if x['name'] == 'mathlib') == ci.MATHLIB_SHA,
                   'Dependency set drift')
        ci.write_json(evidence / 'dependency-sources.json', dependencies)
        ci.run_process(['lake', 'exe', 'cache', 'get', '--repo=leanprover-community/mathlib4',
            '--cache-from=master,legacy', *description['Mathlib_roots']], pkg, evidence, 'official-cache', 600)
        order = ci.focused_order(proof, description)
        ci.write_json(evidence / 'compile-order.json', order)
        for i, name in enumerate(order):
            output = pkg / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            ci.require(not output.exists(), 'Pre-existing project output')
            source = Path(description['project_modules'][name]['path']).relative_to('curvature')
            ci.run_process(['lake', 'env', 'lean', '-j1', '-M5632', '-o', str(output), str(source)], pkg,
                evidence, f'compile-{i:02d}', 720 if name.endswith('.RiemannianSection') else 480)
            ci.require(output.is_file() and output.stat().st_size, 'Compiled project output missing')
        compiled_pre = ci.compiled_snapshot(pkg)
        ci.write_json(evidence / 'compiled-PRE.json', compiled_pre)
        state['path_dependency'] = path_dependency_state(proof)
        state['public_compiled_transfer'] = build_payload(pkg, work / 'export', deadline)
        ci.require(path_dependency_state(proof) == state['path_dependency'], 'Path dependency state drift')
        state['status'] = 'PUBLIC_COMPILED_CLOSURE_READY_ACTUAL_TRANSFER_REVIEW_PENDING_NO_REAL8'
    except BaseException as exc:
        state.update(status='FAIL_COMPILE_TRANSFER_UNVERIFIED', error=str(exc))
        raise
    finally:
        try:
            ci.require(before == {'proof': ci.snapshot(proof), 'control': ci.snapshot(control)}, 'Source PRE/POST mismatch')
            for dep in dependencies:
                ci.require(ci.snapshot(Path(dep['root'])) == dep['source'], 'Dependency source PRE/POST mismatch')
            state['source_PRE_POST_equal'] = True
            if compiled_pre is not None:
                compiled_post = ci.compiled_snapshot(pkg)
                ci.write_json(evidence / 'compiled-POST.json', compiled_post)
                ci.require(compiled_post == compiled_pre, 'Complete compiled PRE/POST mismatch')
                state['compiled_PRE_POST_equal'] = True
            ci.require(not ci.owned_processes(), 'Owned descendants remain')
            state['no_live_owned_descendants'] = True
        except BaseException as exc:
            state.update(status='FAIL_POST_UNVERIFIED', post_error=str(exc))
            raise
        finally:
            state['total_elapsed_seconds'] = time.monotonic() - started
            ci.write_json(evidence / 'outcome.json', state)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('candidate-root', 'control-root', 'evidence', 'work'):
        parser.add_argument('--' + flag, type=Path, required=True)
    for flag in ('candidate-sha', 'expected-tree', 'caller-sha'):
        parser.add_argument('--' + flag, required=True)
    main(parser.parse_args())
