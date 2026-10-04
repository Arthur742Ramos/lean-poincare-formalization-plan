#!/usr/bin/env python3
"""Observe real Lean compiler exits without changing Lake's compilation arguments.

Linux-only, audit-local launcher. It never certifies an existing object, changes
source/setup/options, or substitutes a compiler result. Unexpected invocations
fail closed; the ordinary pinned toolchain remains untouched.
"""
from __future__ import annotations

import fcntl
import hashlib
import gzip
import json
import os
import pathlib
import shutil
import subprocess
import sys
import time

GIB = 1024 ** 3
INFO_QUERIES = {"--githash", "--version", "--print-prefix"}


def digest(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def atomic_json(path, value):
    path = pathlib.Path(path)
    temporary = path.with_suffix(f".tmp-{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def memory_available():
    path = pathlib.Path("/proc/meminfo")
    if not path.is_file():
        return 0
    return next(int(line.split()[1]) * 1024 for line in path.read_text().splitlines()
                if line.startswith("MemAvailable:"))


def inspect_invocation(control, args, cwd):
    """Only the exact configured project compiler command is observable here."""
    root = pathlib.Path(control["root"]).resolve()
    assert pathlib.Path(cwd).resolve() == root, "Unexpected compiler working directory"
    sources = [a for a in args if a.endswith(".lean")]
    assert len(sources) == 1, "Expected exactly one project source"
    source = (root / sources[0]).resolve()
    relative = source.relative_to(root).as_posix()
    module = relative[:-5].replace("/", ".")
    assert module in control["allowed_modules"], "Unexpected project/dependency compilation"
    expected = control["modules"][module]
    assert digest(source) == expected["source_sha256"], "Source changed before compilation"
    stem = module.replace(".", "/")
    outputs = {"-o": root / f".lake/build/lib/lean/{stem}.olean",
               "-i": root / f".lake/build/lib/lean/{stem}.ilean",
               "-c": root / f".lake/build/ir/{stem}.c",
               "--setup": root / f".lake/build/ir/{stem}.setup.json"}
    # The immutable TOML declares no additional Lean arguments or LLVM backend.
    assert len(args) == 10 and args[0] == sources[0] and args[-1] == "--json", args
    for offset, (flag, path) in zip((1, 3, 5, 7), outputs.items()):
        assert args[offset] == flag and (root / args[offset + 1]).resolve() == path, args
    setup = outputs["--setup"]
    assert json.loads(setup.read_text())["name"] == module, "Lake setup/module mismatch"
    assert not outputs["-o"].exists(), "Existing project object at compiler launch"
    records = pathlib.Path(control["evidence"]) / "compiler-records"
    for dependency in expected["project_imports"]:
        position = control["modules"][dependency]["position"]
        result = json.loads((records / f"{position:04d}.json").read_text())
        assert result.get("status") == "finished" and result.get("exit_code") == 0, (
            "Project import lacks a successful real compiler exit", dependency)
    return module, source, outputs


def take_slot(control, *, available=memory_available, disk_free=None, pause=time.sleep):
    """Hold a kernel file lock through the actual compiler's lifetime."""
    assert control["jobs"] in (1, 2), "Unsupported compiler worker bound"
    evidence = pathlib.Path(control["evidence"])
    disk_free = disk_free or (lambda: shutil.disk_usage(control["root"]).free)
    while True:
        with (evidence / "compiler-slots.lock").open("a") as mutex:
            fcntl.flock(mutex, fcntl.LOCK_EX)
            assert not (evidence / "compiler-stop.json").exists(), "Previous audit compiler failure"
            assert disk_free() >= GIB, "Less than 1 GiB free at compiler launch"
            leases = []
            for index in range(control["jobs"]):
                stream = (evidence / f"compiler-slot-{index}.lock").open("a")
                try:
                    fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    leases.append(stream)
                except BlockingIOError:
                    stream.close()
            active = control["jobs"] - len(leases)
            if leases and (not active or available() >= 8 * GIB):
                chosen = leases.pop(0)
                for stream in leases:
                    stream.close()
                return chosen
            for stream in leases:
                stream.close()
        pause(0.1)


def observe(control, args, *, run=subprocess.run, cwd=None, acquire=take_slot):
    evidence = pathlib.Path(control["evidence"])
    record_path = None
    record = {"argv": args, "status": "rejected"}
    lease = None
    reserved = False
    try:
        module, source, outputs = inspect_invocation(control, args, cwd or pathlib.Path.cwd())
        position = control["modules"][module]["position"]
        record_path = evidence / "compiler-records" / f"{position:04d}.json"
        # Atomic exclusive reservation prevents duplicates even across processes.
        with record_path.with_suffix(".reserved").open("x"):
            pass
        reserved = True
        record.update(module=module, source_sha256=digest(source), status="waiting",
                      setup_sha256=digest(outputs["--setup"]), compiler=control["compiler"],
                      compiler_sha256=control["compiler_sha256"],
                      lean_path=os.environ.get("LEAN_PATH", ""))
        setup_bytes = outputs["--setup"].read_bytes()
        setup_value = json.loads(setup_bytes)
        record["lake_setup_options"] = setup_value.get("options", {})
        setup_copy = evidence / "module-setups" / f"{position:04d}.json.gz"
        setup_copy.write_bytes(gzip.compress(setup_bytes, mtime=0))
        atomic_json(record_path, record)
        assert digest(control["compiler"]) == control["compiler_sha256"], "Compiler changed"
        lease = acquire(control)
        record["status"] = "running"
        atomic_json(record_path, record)
        started = time.monotonic()
        env = os.environ.copy()
        # Restore the real installation for Lean itself; preserve Lake's LEAN_PATH
        # and all compilation arguments and the untouched setup file.
        env.update(LEAN_SYSROOT=control["sysroot"], LEAN=control["compiler"])
        result = run([control["compiler"], *args], cwd=control["root"], env=env,
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        log = evidence / "module-build-logs" / f"{position:04d}"
        log.with_suffix(".stdout.log").write_bytes(result.stdout)
        log.with_suffix(".stderr.log").write_bytes(result.stderr)
        sys.stdout.buffer.write(result.stdout)
        sys.stderr.buffer.write(result.stderr)
        record.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - started,
                      status="finished", stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
                      stderr_sha256=hashlib.sha256(result.stderr).hexdigest())
        assert digest(source) == record["source_sha256"], "Source changed during compilation"
        assert digest(outputs["--setup"]) == record["setup_sha256"], "Lake setup changed"
        if result.returncode == 0:
            assert outputs["-o"].is_file(), "Successful compiler produced no project object"
            record["olean_sha256"] = digest(outputs["-o"])
        else:
            atomic_json(evidence / "compiler-stop.json", record)
        atomic_json(record_path, record)
        return result.returncode
    except BaseException as error:
        record.update(status="inconclusive", observer_error=f"{type(error).__name__}: {error}")
        atomic_json(evidence / "compiler-stop.json", record)
        if reserved:
            atomic_json(record_path, record)
        raise
    finally:
        if lease is not None:
            lease.close()


def main():
    control = json.loads(pathlib.Path(os.environ["HAMILTON_COMPILER_CONTROL"]).read_text())
    args = sys.argv[1:]
    if len(args) == 1 and args[0] in INFO_QUERIES:
        # Metadata comes only from the actual pinned compiler, including prefix.
        assert digest(control["compiler"]) == control["compiler_sha256"], "Compiler changed"
        env = os.environ.copy()
        env.update(LEAN_SYSROOT=control["sysroot"], LEAN=control["compiler"])
        os.execve(control["compiler"], [control["compiler"], *args], env)
    sys.exit(observe(control, args))


if __name__ == "__main__":
    main()
