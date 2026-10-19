#!/usr/bin/env python3
"""Focused PR148 verification; independent of the frozen legacy campaign gates."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import sys
import time

PROOF_SHA = '78019d610d82460480141d9e3a53c69589c66da6'
PROOF_TREE = '27b4a9ba12c48573b6ea4132a6f893915b0ae807'
LEAN_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
MATHLIB_SHA = 'db584cd6d46c92f209a44c0f1c829460d327499d'
TARGET = 'PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointBackgroundFrameC1'
PROBE = 'scripts/point4_fixed_background_frame_c1_probe.lean'
MARKERS = ('FIXED_BACKGROUND_FRAME_C1_TYPES_BEGIN', 'FIXED_BACKGROUND_FRAME_C1_TYPES_END')
AXIOM_NAMES = (
    'fixedBackgroundFrameC1FullSignatureAssignment',
    'fixedIVPMetricDefectC1FullSignatureAssignment',
    'PoincareCurvature.GaugeFlowAssembly.contMDiffOn_const_background_localFrame',
    'PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_fixed_background',
    'RicciFlow.InitialValueProblem.contMDiffOn_joint_metricDefect_component_fixedLeviCivitaBackground',
    'fixedBackgroundFin0EndomorphismZero',
    'fixedBackgroundFin0MetricDefectZero',
)
TYPE_NAMES = (
    'ExpectedFixedBackgroundFrameC1', AXIOM_NAMES[0],
    'ExpectedFixedIVPMetricDefectC1', AXIOM_NAMES[1], *AXIOM_NAMES[2:],
)
LOG_LIMIT = 16 * 1024**2
EVIDENCE_LIMIT = 64 * 1024**2
LOG_BUDGET = EVIDENCE_LIMIT - 8 * 1024**2  # reserve fixed metadata/failure-receipt capacity
OFFICIAL_COMPILER_FILES = {
    'bin/lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'bin/lake': '60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3',
    'lib/lean/libleanshared.so': 'f2a36d5e56b936afc07bdbea18542de0bce6a9977ebc325915272c300d992d42',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write_json(path, value):
    data = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    total = sum(p.stat().st_size for p in path.parent.iterdir() if p.is_file())
    previous = path.stat().st_size if path.exists() else 0
    require(total - previous + len(data) <= EVIDENCE_LIMIT, 'Metadata exceeds total evidence bound')
    path.write_bytes(data)


def identity(path):
    require(path.is_file() and not path.is_symlink(), f'Not a regular file: {path}')
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], timeout=20).decode().strip()


def snapshot(root):
    require(not git(root, 'status', '--porcelain', '--untracked-files=normal'), 'Dirty source tree')
    names = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z'], timeout=20).decode().split('\0')
    return {name: identity(root / name) for name in names if name}


def guard_output(raw):
    require(0 < len(raw) <= LOG_LIMIT, 'Empty or oversized probe output')
    text = raw.decode('utf-8', errors='strict')
    require(not re.search(r'\bsorryAx\b|(?:^|\n).*\berror:', text), 'Probe error or forbidden axiom')
    lines = text.splitlines()
    begin, end = MARKERS
    require(lines.count(begin) == lines.count(end) == 1, 'Missing or repeated type marker')
    first, last = lines.index(begin), lines.index(end)
    require(first < last, 'Reordered type markers')
    body = '\n'.join(lines[first + 1:last])
    require(body.strip(), 'Empty whole-type group')
    header = re.compile(r'^(?:(?:@\[[^\n]+\]|protected|noncomputable)\s+)*(?:def|abbrev|theorem)\s+'
                        r'([A-Za-z_][A-Za-z0-9_.]*[A-Za-z0-9_])(?=\.\{|\s|:)', re.M)
    require(tuple(header.findall(body)) == TYPE_NAMES, 'Missing, extra or reordered printed declarations')
    require(len(re.findall(r'depends on axioms:|does not depend on any axioms', text)) == 7,
            'Unexpected number of axiom records')
    tail = '\n'.join(lines[last + 1:]).strip()
    pattern = re.compile(r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)\s*$", re.M)
    records = list(pattern.finditer(tail))
    require(tuple(m.group(1) for m in records) == AXIOM_NAMES, 'Missing, extra or reordered axiom records')
    atom = re.compile(r'(propext|Classical\.choice|Quot\.sound)(?:\.\{[A-Za-z0-9_ .()+\s]{1,256}\})?')
    cursor, evidence = 0, []
    for match in records:
        require(not tail[cursor:match.start()].strip(), 'Unexpected text between axiom records')
        cursor = match.end()
        raw_list = match.group(2)
        items = [] if raw_list is None or not raw_list.strip() else [x.strip() for x in raw_list.split(',')]
        matches = [atom.fullmatch(x) for x in items]
        require(all(matches), 'Malformed or nonstandard axiom')
        bases = [m.group(1) for m in matches]
        require(len(bases) == len(set(bases)), 'Repeated axiom base')
        evidence.append({'name': match.group(1), 'raw_record': match.group(0), 'standard_bases': bases})
    require(not tail[cursor:].strip(), 'Unexpected trailing probe output')
    return {'printed_declarations': list(TYPE_NAMES), 'axiom_records': evidence, 'Point4': 'OPEN'}


def group_members(pgid):
    rows = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            # comm may contain spaces or parentheses; fields start after its final ')'.
            fields = (path / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) == pgid and fields[0] != 'Z':
                rows.append(int(path.name))
        except (FileNotFoundError, ProcessLookupError):
            pass
        except PermissionError as exc:
            raise ValueError('Unreadable process metadata; stage quiescence is unverified') from exc
    return rows


def stop_group(proc):
    if group_members(proc.pid):
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + 2
        while group_members(proc.pid) and time.monotonic() < deadline:
            time.sleep(0.05)
        if group_members(proc.pid):
            os.killpg(proc.pid, signal.SIGKILL)
    proc.wait(timeout=5)
    deadline = time.monotonic() + 2
    while group_members(proc.pid) and time.monotonic() < deadline:
        time.sleep(0.05)
    require(not group_members(proc.pid), 'Live stage descendants remain')


def run_process(argv, cwd, evidence, label, timeout, env=None):
    """Capture bounded output; reap leader AND terminate any remaining stage group."""
    started = time.monotonic()
    row = {'argv': list(map(str, argv)), 'cwd': str(cwd), 'timeout_seconds': timeout}
    proc = subprocess.Popen(row['argv'], cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, start_new_session=True)
    row['pid'] = proc.pid
    selector = selectors.DefaultSelector()
    selector.register(proc.stdout, selectors.EVENT_READ)
    size, failure = 0, None
    try:
        with (evidence / (label + '.log')).open('wb') as log:
            while selector.get_map():
                if time.monotonic() - started > timeout:
                    raise TimeoutError(f'{label} exceeded its wall bound')
                for key, _ in selector.select(timeout=0.2):
                    data = os.read(key.fileobj.fileno(), 65536)
                    if not data:
                        selector.unregister(key.fileobj)
                        continue
                    require(size + len(data) <= LOG_LIMIT, f'{label} exceeded log bound')
                    log.flush()
                    total = sum(p.stat().st_size for p in evidence.iterdir() if p.is_file())
                    require(total + len(data) <= LOG_BUDGET, 'Focused logs exhausted their reserved budget')
                    log.write(data)
                    size += len(data)
            proc.wait(timeout=max(0.1, timeout - (time.monotonic() - started)))
            require(proc.returncode == 0, f'{label} exited {proc.returncode}')
    except BaseException as exc:
        failure = exc
    finally:
        selector.close()
        proc.stdout.close()
        try:
            stop_group(proc)
            row['no_live_stage_descendants'] = True
        except BaseException as cleanup:
            row['cleanup_error'] = str(cleanup)
            failure = failure or cleanup
        row.update(exit_code=proc.returncode, elapsed_seconds=time.monotonic() - started,
                   leader_reaped=proc.returncode is not None, log=identity(evidence / (label + '.log')))
        if failure:
            row['error'] = str(failure)
        write_json(evidence / (label + '.json'), row)
    if failure:
        raise failure
    return (evidence / (label + '.log')).read_bytes()


def preflight(args):
    proof, control, evidence = args.candidate_root.resolve(), args.control_root.resolve(), args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    require(args.candidate_sha == PROOF_SHA and args.expected_tree == PROOF_TREE, 'Unreviewed proof pin')
    require(re.fullmatch(r'[0-9a-f]{40}', args.caller_sha), 'Malformed caller SHA')
    require(git(proof, 'rev-parse', 'HEAD') == PROOF_SHA, 'Proof HEAD drift')
    require(git(proof, 'rev-parse', 'HEAD^{tree}') == PROOF_TREE, 'Proof tree drift')
    require(git(control, 'rev-parse', 'HEAD') == args.caller_sha, 'Workflow caller HEAD drift')
    description = json.loads((Path(__file__).with_name('point4_fixed_background_sources.json')).read_text())
    require(description['candidate_commit'] == PROOF_SHA and description['candidate_tree'] == PROOF_TREE,
            'Descriptor proof pin drift')
    for item in [*description['project_modules'].values(), description['probe']]:
        require(identity(proof / item['path']) == {k: item[k] for k in ('bytes', 'sha256')},
                f"Focused source changed: {item['path']}")
    require((proof / 'curvature/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.0',
            'Toolchain pin drift')
    return proof, control, evidence, description


def focused_order(proof, description):
    spec = importlib.util.spec_from_file_location('fixed_background_source_scanner', proof / 'curvature/scripts/point4_scan.py')
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
        require(name in description['project_modules'], f'Unadmitted local import {name}')
        visited.add(name)
        source = proof / description['project_modules'][name]['path']
        code = '\n'.join(scanner.strip_comments(source.read_text()))
        for imports in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', code, re.M):
            for dep in imports.split():
                visit(dep)
        order.append(name)

    visit(TARGET)
    require(visited == set(description['project_modules']) and sorted(roots) == description['Mathlib_roots'],
            'Focused project/import/cache-root closure drift')
    return order


def main(args):
    proof, control, evidence, description = preflight(args)
    state = {'proof_commit': PROOF_SHA, 'proof_tree': PROOF_TREE, 'caller_commit': args.caller_sha,
             'caller_tree': git(control, 'rev-parse', 'HEAD^{tree}'), 'Point4': 'OPEN',
             'status': 'PREFLIGHT_ONLY' if args.phase == 'preflight' else 'RUNNING_UNVERIFIED'}
    if args.phase == 'preflight':
        state['proof_sources'] = snapshot(proof)
        state['control_sources'] = snapshot(control)
        write_json(evidence / 'preflight.json', state)
        return
    before = json.loads((evidence / 'preflight.json').read_text())
    require(before['proof_sources'] == snapshot(proof) and before['control_sources'] == snapshot(control),
            'Sources changed after preflight')
    state['started_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    dependencies = []
    try:
        require(not any(os.environ.get(k) for k in ('MATHLIB_CACHE_GET_URL', 'MATHLIB_CACHE_FROM',
                    'MATHLIB_CACHE_REPO_SCOPE', 'MATHLIB_CACHE_SAS', 'MATHLIB_CACHE_AZURE_BEARER_TOKEN')),
                'Cache endpoint/scope/auth override is not admitted')
        pkg = proof / 'curvature'
        lean_version = run_process(['lean', '--version'], pkg, evidence, 'lean-version', 30).decode()
        require('version 4.33.0,' in lean_version and LEAN_COMMIT in lean_version, 'Wrong official compiler')
        state['compiler_version'] = lean_version.strip()
        prefix = Path(run_process(['lean', '--print-prefix'], pkg, evidence, 'compiler-prefix', 30).decode().strip())
        require(prefix.is_absolute(), 'Compiler prefix is not absolute')
        state['compiler_files'] = {name: identity(prefix / name) for name in OFFICIAL_COMPILER_FILES}
        require(all(state['compiler_files'][name]['sha256'] == sha for name, sha in OFFICIAL_COMPILER_FILES.items()),
                'Compiler bytes differ from the hash-verified official Linux4.33 archive')
        order = focused_order(proof, description)
        write_json(evidence / 'focused-order.json', order)
        manifest = json.loads((pkg / 'lake-manifest.json').read_text())
        for entry in manifest['packages']:
            if entry['type'] != 'git':
                continue
            require(re.fullmatch(r'[0-9a-f]{40}', entry['rev']), 'Invalid manifest Git revision')
            require(entry['url'].startswith(('https://github.com/leanprover-community/',
                                             'https://github.com/leanprover/')), 'Unadmitted source registry')
            dest = pkg / '.lake/packages' / entry['name']
            require(not dest.exists(), 'Unexpected pre-existing dependency source/cache')
            dest.mkdir(parents=True)
            name = entry['name']
            run_process(['git', 'init', '--quiet'], dest, evidence, 'source-init-' + name, 10)
            run_process(['git', 'remote', 'add', 'origin', entry['url']], dest, evidence, 'source-origin-' + name, 10)
            run_process(['git', 'fetch', '--no-tags', '--depth=1', 'origin', entry['rev']], dest,
                        evidence, 'source-fetch-' + name, 90)
            run_process(['git', 'checkout', '--detach', 'FETCH_HEAD'], dest, evidence, 'source-checkout-' + name, 20)
            require(git(dest, 'rev-parse', 'HEAD') == entry['rev'], 'Dependency revision mismatch')
            dependencies.append({'name': name, 'url': entry['url'], 'rev': entry['rev'], 'root': str(dest)})
        require(len(dependencies) == 9 and next(x['rev'] for x in dependencies if x['name'] == 'mathlib') == MATHLIB_SHA,
                'Unexpected dependency set')
        write_json(evidence / 'dependencies.json', dependencies)
        run_process(['lake', 'exe', 'cache', 'get', '--repo=leanprover-community/mathlib4',
                     '--cache-from=master,legacy', *description['Mathlib_roots']], pkg, evidence, 'official-cache', 600)
        # Direct Lean invocations cannot silently build a missing Mathlib dependency.
        # Only this reviewed 28-module project closure is compiled, sequentially.
        compiled = []
        for i, name in enumerate(order):
            output = pkg / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            require(not output.exists(), 'Unexpected pre-existing project output')
            source = Path(description['project_modules'][name]['path']).relative_to('curvature')
            run_process(['lake', 'env', 'lean', '-j1', '-M5632', '-o', str(output), str(source)],
                        pkg, evidence, f'compile-{i:02d}', 480)
            require(output.is_file() and output.stat().st_size, 'Compiler output missing')
            compiled.append({'module': name, 'source': description['project_modules'][name],
                             'outputs': {p.name: identity(p) for p in output.parent.glob(output.name + '*')}})
            write_json(evidence / 'compiled-project-modules.json', compiled)
        raw = run_process(['lake', 'env', 'lean', '-j1', '-M5632', PROBE], pkg, evidence, 'probe', 240)
        write_json(evidence / 'probe-guard.json', guard_output(raw))
        state['status'] = 'FOCUSED_COMPILE_AND_PROBE_PASS_ACTUAL_REVIEW_PENDING'
    except BaseException as exc:
        state['status'] = 'FAIL_UNVERIFIED'
        state['error'] = str(exc)
        raise
    finally:
        try:
            require(before['proof_sources'] == snapshot(proof) and before['control_sources'] == snapshot(control),
                    'Source PRE/POST mismatch')
            for dep in dependencies:
                require(git(Path(dep['root']), 'rev-parse', 'HEAD') == dep['rev'], 'Dependency HEAD changed')
                require(not git(Path(dep['root']), 'status', '--porcelain', '--untracked-files=no'),
                        'Dependency tracked source changed')
            state['source_PRE_POST_equal'] = True
        except BaseException as exc:
            state['status'] = 'FAIL_SOURCE_POST'
            state['post_error'] = str(exc)
            raise
        finally:
            write_json(evidence / 'outcome.json', state)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase', choices=('preflight', 'verify'), required=True)
    for flag in ('candidate-root', 'control-root', 'evidence'):
        parser.add_argument('--' + flag, type=Path, required=True)
    for flag in ('candidate-sha', 'expected-tree', 'caller-sha'):
        parser.add_argument('--' + flag, required=True)
    main(parser.parse_args())
