#!/usr/bin/env python3
"""Explicit same-run command reuse; never caches builds or fabricates audit PASS."""
from __future__ import annotations

import json
import os
from pathlib import Path
import selectors
import stat
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from identity import canonical, digest, execution_identity, regular, require, strict_json, output_budget

MAX_OUTPUT = 32 * 1024 * 1024
MAX_EVENTS = 100000


def audit_arguments(argv):
    """Only known audit flags; output path alone may differ between consumers."""
    require(argv and argv[0] == "scripts/point4_audit.sh", "Not the audit command")
    normalized, destination = [argv[0]], None
    i = 1
    while i < len(argv):
        if argv[i] == "--json":
            require(destination is None and i + 1 < len(argv), "Duplicate/missing audit JSON argument")
            destination = Path(argv[i + 1])
            require(destination.is_absolute() and destination.parent == Path('/tmp')
                    and destination.name.startswith('point4-') and destination.suffix == '.json',
                    "Audit JSON destination is not an authorized flat /tmp evidence path")
            normalized.extend(['--json', '<consumer-json>'])
            i += 2
        elif argv[i] == '--quiet':
            require('--quiet' not in normalized, "Duplicate audit flag")
            normalized.append(argv[i]); i += 1
        else:
            # In particular --no-build cannot acquire a full-audit reuse receipt.
            raise RuntimeError("Audit option outside reuse contract")
    return normalized, destination


def classify(name, argv, cwd, root, plan):
    if Path(cwd).resolve() != root / 'curvature':
        return None
    if name == 'bash' and argv and argv[0] == plan['audit_script']:
        try:
            normalized, destination = audit_arguments(argv)
        except RuntimeError:
            # Original nested Hessian destination is intentionally native.
            return None
        if destination is None:
            return None
        return dict(kind='full-audit', argv=normalized, destination=destination)
    if name == 'lake' and plan.get('enable_probe_reuse') is True and argv in plan['probe_argv_allowlist']:
        return dict(kind='probe', argv=argv, destination=None)
    return None


def emit_receipt(directory, value):
    output_budget().mkdir(directory,exist_ok=True)
    name = f"{time.time_ns()}-{os.getpid()}.json"
    with output_budget().file(directory/name,MAX_OUTPUT) as handle:
        handle.write(canonical(value) + b'\n')


def write_all(fd, data):
    while data:
        written = os.write(fd, data)
        require(written > 0, 'Output stream closed')
        data = data[written:]


def capture(argv, cwd, directory):
    """Preserve stdout/stderr event ordering, stream live, bound retained bytes."""
    paths = [directory / 'stdout.bin', directory / 'stderr.bin']
    events, total, offsets = [], 0, [0, 0]
    with output_budget().file(paths[0],MAX_OUTPUT) as out, output_budget().file(paths[1],MAX_OUTPUT) as err:
        handles = [out, err]
        child = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            with selectors.DefaultSelector() as poll:
                poll.register(child.stdout, selectors.EVENT_READ, 0)
                poll.register(child.stderr, selectors.EVENT_READ, 1)
                while poll.get_map():
                    for key, _ in poll.select(timeout=1):
                        stream = key.data
                        data = os.read(key.fileobj.fileno(), 65536)
                        if not data:
                            poll.unregister(key.fileobj)
                            key.fileobj.close()
                            continue
                        total += len(data)
                        require(total <= MAX_OUTPUT and len(events) < MAX_EVENTS, 'Native output bound exceeded')
                        handles[stream].write(data)
                        write_all(stream + 1, data)
                        events.append([stream, offsets[stream], len(data)])
                        offsets[stream] += len(data)
            code = child.wait()
        except BaseException:
            child.kill(); child.wait()
            raise
        finally:
            for stream in (child.stdout,child.stderr):
                if not stream.closed:stream.close()
    return dict(exit_code=code, events=events,
                streams=[dict(bytes=p.stat().st_size, sha256=digest(regular(p, MAX_OUTPUT))) for p in paths])


def validate_payload(directory, saved):
    data = [regular(directory / n, MAX_OUTPUT) for n in ('stdout.bin', 'stderr.bin')]
    require(sum(map(len, data)) <= MAX_OUTPUT, 'Cached output aggregate exceeded')
    require(saved['streams'] == [dict(bytes=len(x), sha256=digest(x)) for x in data], 'Cached stream corrupted')
    require(type(saved['exit_code']) is int and 0 <= saved['exit_code'] <= 255, 'Invalid cached exit code')
    offsets = [0, 0]
    require(type(saved['events']) is list and len(saved['events']) <= MAX_EVENTS, 'Cached event bound exceeded')
    for row in saved['events']:
        require(type(row) is list and len(row) == 3 and all(type(x) is int for x in row), 'Malformed cached event')
        stream, offset, size = row
        require(stream in (0, 1) and offset == offsets[stream] and size > 0, 'Cached event order differs')
        require(offset + size <= len(data[stream]), 'Cached event outside stream')
        offsets[stream] += size
    require(offsets == list(map(len, data)), 'Cached event coverage incomplete')
    return data


def copy_audit_json(directory, destination, saved, native=False):
    if destination is None:
        require(saved['audit_json'] is None, 'Unexpected audit JSON')
        return
    raw = regular(directory / 'audit.json', MAX_OUTPUT)
    require(saved['audit_json'] == dict(bytes=len(raw), sha256=digest(raw)), 'Audit JSON corrupted')
    strict_json(raw)
    if not native:
        for parent in destination.parents:
            require(stat.S_ISDIR(parent.lstat().st_mode), 'Audit output parent is a symlink')
        if destination.exists() or destination.is_symlink():
            require(stat.S_ISREG(destination.lstat().st_mode), 'Audit output is not regular')
        # Legacy commands intentionally replace their flat /tmp output. Atomic
        # same-directory replacement prevents following an existing symlink.
        temporary = destination.with_name(destination.name + f'.point4-{os.getpid()}')
        with output_budget().file(temporary,MAX_OUTPUT) as handle:
            handle.write(raw)
        os.replace(temporary, destination)


def audit_native_eligible(code, parsed):
    return (code in (0, 1) and parsed.get('build_run') is True and
            parsed.get('gates', {}).get('G2_build_green', {}).get('status') == 'PASS')


def validate_side_effect(directory, row):
    raw = regular(directory / 'build.log', MAX_OUTPUT)
    require(row == dict(bytes=len(raw), sha256=digest(raw)), 'Audit build side effect corrupted')
    return raw


def main():
    name = Path(sys.argv[0]).name
    require(name in ('bash', 'lake'), 'Broker must be invoked through its explicit shim')
    argv = sys.argv[1:]
    root = Path(os.environ['P4_CI_ROOT'])
    plan = strict_json(regular(Path(os.environ['P4_CI_TOOLING_ROOT']) / 'scripts/point4_ci/plan.json'))
    real = os.environ['P4_CI_REAL_BASH' if name == 'bash' else 'P4_CI_REAL_LAKE']
    cwd = Path.cwd()
    selection = classify(name, argv, cwd, root, plan)
    # Unknown import/plugin/loader overrides retain real execution, never reuse.
    overrides = any(value and (key.startswith(('LEAN_', 'LAKE_', 'LD_', 'DYLD_')))
                    for key, value in os.environ.items())
    if overrides:
        selection = None
    if selection is None:
        os.execv(real, [real, *argv])
    evidence = Path(os.environ['P4_CI_EVIDENCE'])
    identity = execution_identity(root, os.environ['P4_CI_REAL_LAKE'], plan, [name, *selection['argv']], cwd, dict(os.environ))
    key = digest(canonical(identity))
    directory = evidence / 'same-run-cache' / key
    output_budget().mkdir(directory.parent,exist_ok=True)
    native = not directory.exists()
    if native:
        output_budget().mkdir(directory)
        output = capture([real, *argv], cwd, directory)
        # A failed probe is preserved but cannot become a reusable successful check.
        reusable = output['exit_code'] == 0 if selection['kind'] == 'probe' else output['exit_code'] in (0, 1)
        audit, build_log = None, None
        if selection['destination'] is not None:
            raw = regular(selection['destination'], MAX_OUTPUT)
            parsed = strict_json(raw)
            require(parsed.get('build_run') is True, 'Native audit did not run its full G2 build')
            with output_budget().file(directory/'audit.json',MAX_OUTPUT) as handle:
                handle.write(raw)
            audit = dict(bytes=len(raw), sha256=digest(raw))
            reusable = audit_native_eligible(output['exit_code'], parsed)
            build_raw = regular(Path('/tmp/point4_build.log'), MAX_OUTPUT)
            with output_budget().file(directory/'build.log',MAX_OUTPUT) as handle:
                handle.write(build_raw)
            build_log = dict(bytes=len(build_raw), sha256=digest(build_raw))
        post = execution_identity(root, os.environ['P4_CI_REAL_LAKE'], plan, [name, *selection['argv']], cwd, dict(os.environ))
        require(post == identity, 'Command changed its Source/toolchain/input identity')
        saved = dict(schema='point4-same-run-command-v1', identity=identity, key=key,
                     owner=dict(case=os.environ['P4_CI_CASE'], step=os.environ['P4_CI_STEP']),
                     kind=selection['kind'], reusable=reusable, audit_json=audit, build_log=build_log, **output)
        with output_budget().file(directory/'receipt.json',MAX_OUTPUT) as handle:
            handle.write(canonical(saved) + b'\n')
    else:
        saved = strict_json(regular(directory / 'receipt.json', MAX_OUTPUT))
        require(saved['schema'] == 'point4-same-run-command-v1' and saved['key'] == key
                and saved['identity'] == identity and saved['kind'] == selection['kind']
                and saved['reusable'] is True, 'Same-run reuse identity/eligibility differs')
    data = validate_payload(directory, saved)
    build_raw = validate_side_effect(directory, saved['build_log']) if saved['build_log'] is not None else None
    copy_audit_json(directory, selection['destination'], saved, native=native)
    if build_raw is not None:
        if not native:
            target = Path('/tmp/point4_build.log')
            require(not target.is_symlink() and (not target.exists() or target.is_file()), 'Invalid audit build output')
            temporary = target.with_name(target.name + f'.point4-{os.getpid()}')
            with output_budget().file(temporary,MAX_OUTPUT) as handle:
                handle.write(build_raw)
            os.replace(temporary, target)
    if not native:
        for stream, offset, length in saved['events']:
            write_all(stream + 1, data[stream][offset:offset + length])
    emit_receipt(evidence / 'command-receipts', dict(schema='point4-command-consumer-v1',
                 consumer=dict(case=os.environ['P4_CI_CASE'], step=os.environ['P4_CI_STEP']),
                 mode='NATIVE' if native else 'SAME_RUN_REUSE', owner=saved['owner'], key=key,
                 native_receipt_sha256=digest(regular(directory / 'receipt.json', MAX_OUTPUT)),
                 exit_code=saved['exit_code'], streams=saved['streams']))
    return saved['exit_code']


if __name__ == '__main__':
    try:
        code = main()
    except Exception as error:
        print('POINT4_BROKER_INFRASTRUCTURE_FAILURE: ' + str(error), file=sys.stderr)
        code = 70  # Distinct from the honest full-audit OPEN exit1.
    raise SystemExit(code)
