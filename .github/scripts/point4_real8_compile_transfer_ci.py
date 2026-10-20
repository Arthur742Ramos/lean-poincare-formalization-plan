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
PART_BYTES_LIMIT = 400 * 1024**2
PART_COUNT_LIMIT = 6
FIRST_SUCCESSFUL_COMPILED_CATALOGUE_SHA256 = 'a52ead712b2425342ff33c759a882299194a27447c0ba0c02ef93280e26f381f'


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
    ci.require(shutil.disk_usage(output).free >= 2 * ARCHIVE_LIMIT + 1024**3,
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


def require_first_compiled_catalogue(compiled):
    raw = json.dumps(compiled, sort_keys=True, separators=(',', ':')).encode('utf-8')
    observed = hashlib.sha256(raw).hexdigest()
    ci.require(observed == FIRST_SUCCESSFUL_COMPILED_CATALOGUE_SHA256,
        'Compiled file namespace/content differs from first successful run39348618514; no normalization or waiver')
    return {'sha256': observed, 'canonical_JSON_bytes': len(raw), 'first_run': 39348618514,
            'file_count': len(compiled), 'all_file_bytes': sum(row['bytes'] for row in compiled.values())}


def split_public_payload(export, output, record, catalogue, deadline):
    """Separate artifacts keep each normal connector transfer below512MiB."""
    ci.require(not output.exists(), 'Fresh chunk namespace required')
    output.mkdir(parents=True, mode=0o700)
    source = export / 'compiled-closure.zip'; before = source.stat()
    ci.require(stat.S_ISREG(source.lstat().st_mode) and before.st_size == record['archive']['bytes'] and
               0 < before.st_size <= ARCHIVE_LIMIT, 'Inner archive identity/size drift before splitting')
    whole, parts = hashlib.sha256(), {}
    with source.open('rb') as stream:
        for index in range(PART_COUNT_LIMIT):
            ci.require(time.monotonic() < deadline, 'Payload splitting cumulative deadline')
            if stream.tell() == before.st_size: break
            directory = output / f'part-{index:02d}'; directory.mkdir(mode=0o700)
            path = directory / f'compiled-closure.zip.part-{index:02d}'
            count, part = 0, hashlib.sha256()
            with path.open('xb') as destination:
                while count < PART_BYTES_LIMIT:
                    ci.require(time.monotonic() < deadline, 'Payload chunk write deadline')
                    chunk = stream.read(min(1024**2, PART_BYTES_LIMIT - count))
                    if not chunk: break
                    ci.require(count + len(chunk) <= PART_BYTES_LIMIT, 'Part byte ceiling before write')
                    destination.write(chunk); count += len(chunk); part.update(chunk); whole.update(chunk)
            ci.require(count > 0 and ci.identity(path) == {'bytes': count, 'sha256': part.hexdigest()},
                       'Whole written chunk identity/readback failed')
            parts[path.name] = {'bytes': count, 'sha256': part.hexdigest(), 'index': index,
                                'artifact_suffix': f'part-{index:02d}'}
        ci.require(stream.tell() == before.st_size and not stream.read(1), 'Chunk count ceiling')
    after = source.stat()
    ci.require(all(getattr(before, key) == getattr(after, key) for key in
               ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')) and
               whole.hexdigest() == record['archive']['sha256'], 'Whole split archive SHA/identity mismatch')
    small = output / 'manifest'; small.mkdir(mode=0o700)
    shutil.copyfile(export / 'compiled-closure-manifest.json', small / 'compiled-closure-manifest.json')
    ci.require(ci.identity(small / 'compiled-closure-manifest.json') == record['manifest'], 'Manifest copy mismatch')
    descriptor = {'schema': 'public-compiled-payload-parts-v1', 'archive': record['archive'],
        'manifest': record['manifest'], 'parts': parts, 'part_count': len(parts),
        'part_bytes_limit': PART_BYTES_LIMIT, 'part_count_limit': PART_COUNT_LIMIT,
        'canonical_first_compiled_catalogue': catalogue,
        'old_unavailable_container_identity_claim': False,
        'all_compiled_file_bytes_equal_first_successful_run': True,
        'historical_inputs_or_private_review_records_included': False,
        'scope': 'Public build-file bytes only; no hosted nested config/guard/real8 credit'}
    raw = (json.dumps(descriptor, sort_keys=True, indent=2) + '\n').encode()
    ci.require(len(raw) <= 1024**2, 'Chunk descriptor bound')
    path = small / 'compiled-closure-parts.json'; path.write_bytes(raw)
    return {'descriptor': ci.identity(path), 'parts': parts, 'part_count': len(parts),
            'part_bytes_limit': PART_BYTES_LIMIT, 'canonical_first_compiled_catalogue': catalogue}


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
        state['first_successful_compiled_catalogue'] = require_first_compiled_catalogue(compiled_pre)
        state['path_dependency'] = path_dependency_state(proof)
        state['public_compiled_transfer'] = build_payload(pkg, work / 'export', deadline)
        state['public_compiled_parts_transfer'] = split_public_payload(work / 'export', work / 'transfer',
            state['public_compiled_transfer'], state['first_successful_compiled_catalogue'], deadline)
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
