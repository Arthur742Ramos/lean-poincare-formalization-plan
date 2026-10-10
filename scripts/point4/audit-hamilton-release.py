#!/usr/bin/env python3
"""Rebuild the exact upstream Ricci-flow endpoint closure, then audit axioms.

This script does not vendor upstream proofs or certify a bridge to Point 4.
The immutable source must already be checked out in a separate directory.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import heapq
import hashlib
import gzip
import importlib.util
import json
import pathlib
import os
import shlex
import signal
import re
import shutil
import subprocess
import sys
import time
import tomllib

SOURCE_SHA = "8bd406e35c33a200e9b88895cf11ee8429194e15"
MATHLIB_SHA = "8a178386ffc0f5fef0b77738bb5449d50efeea95"
TARGETS = {
    "DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence":
        "DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Construction":
        "DifferentialGeometry.PDE.RicciFlow.ricci_flow_forward_unique",
}
LAKE_API_SHA = "98dc76e3c0a9b856c9b98726b713fb04fab16740"
DRIVER_IMPORTS = ("Lake", "Lake.CLI.Build", "Lake.Load.Workspace")
BOOTSTRAP_ENV_KEYS = ("LEAN_SYSROOT", "LEAN_PATH", "LEAN")
SDK_IDENTITY_ROOTS = ("bin", "include", "lib", "share", "src")
SDK_ARCHIVE_SHA256 = "089f7e513ed3e9436d191f4986330c0b53809c86b5997f5eb7f25550c374fa48"
SDK_ARCHIVE_URL = "https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux.tar.zst"
# Filled from source-only hashing of the checksum-verified official archive's
# selected tree. Relative paths make the identity independent of install path.
SDK_TREE_SHA256 = "58073c8f2300c6a95fca7635b6c8421087737206fd1d62680ef21872c7f46035"


def dependency_ready_build(order, graph, build, completed, *, jobs=2,
                           can_launch=lambda active: True):
    """Compile each source exactly once, only after its project imports finish.

    A failure stops new submissions; already running independent jobs finish
    and retain their evidence. This never accepts an upstream object cache.
    """
    assert jobs in (1, 2)
    positions = {module: i for i, module in enumerate(order)}
    assert len(positions) == len(order)
    dependencies = {m: set(graph[m]) & positions.keys() for m in order}
    children = {m: [] for m in order}
    for module, deps in dependencies.items():
        for parent in deps:
            children[parent].append(module)
    ready = [(positions[m], m) for m in order if not dependencies[m]]
    heapq.heapify(ready)
    succeeded = set()
    failure = None
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        running = {}
        while running or (ready and failure is None):
            while ready and failure is None and len(running) < jobs:
                if not can_launch(len(running)):
                    break
                _, module = heapq.heappop(ready)
                assert dependencies[module] <= succeeded
                running[executor.submit(build, module)] = module
            if not running:
                raise RuntimeError("Resource guard prevented the next source build")
            finished, _ = concurrent.futures.wait(
                running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in sorted(finished, key=lambda f: positions[running[f]]):
                module = running.pop(future)
                result = future.result()
                completed(module, result)
                if result[0] != 0:
                    if failure is None:
                        failure = (module, result[0])
                    continue
                succeeded.add(module)
                for child in children[module]:
                    dependencies[child].discard(module)
                    if not dependencies[child]:
                        heapq.heappush(ready, (positions[child], child))
    if failure is None:
        assert succeeded == set(order), "Incomplete or cyclic source graph"
    return failure


def chain_batches(order, graph, jobs):
    """Partition into explicit direct-import chains, with width at most jobs.

    Off-batch project imports must be in earlier batches. No Lake concurrency
    flag is assumed: at most jobs chains can have a project compiler ready.
    """
    assert jobs in (1, 2)
    assert len(order) == len(set(order))
    known = set(order)
    assert set(graph) == known
    assert all(set(graph[m]) <= known for m in order)
    built, batches = set(), []
    while built != known:
        batch, selected, chains = [], set(), []
        for module in order:
            if module in built or not set(graph[module]) <= built | selected:
                continue
            candidates = [i for i, chain in enumerate(chains) if chain[-1] in graph[module]]
            if candidates:
                chains[candidates[0]].append(module)
            elif len(chains) < jobs:
                chains.append([module])
            else:
                continue
            batch.append(module)
            selected.add(module)
        assert batch, "Incomplete or cyclic source graph"
        batches.append({"modules": batch, "chains": chains})
        built.update(selected)
    return batches


def assert_no_project_objects(root):
    """The root project is source-only; dependency Mathlib objects are allowed."""
    root = pathlib.Path(root)
    found = []
    for base in (root / "DifferentialGeometry", root / ".lake/build"):
        if base.exists():
            found.extend(str(path.relative_to(root)) for path in base.rglob("*.olean*"))
    found.extend(str(path.relative_to(root)) for path in root.glob("*.olean*"))
    assert not found, "Precompiled project objects before source build: " + ", ".join(found[:10])
    return found


def make_compiler_shim(output, sysroot, observer, control_path):
    """Create audit-local links; never edit the official toolchain installation."""
    shim = output / "observed-toolchain"
    shim.mkdir()
    (shim / "bin").mkdir()
    for entry in sysroot.iterdir():
        if entry.name != "bin":
            (shim / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    for entry in (sysroot / "bin").iterdir():
        if entry.name != "lean":
            (shim / "bin" / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    launcher = shim / "bin/lean"
    launcher.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + " " +
                        shlex.quote(str(observer)) + ' "$@"\n')
    launcher.chmod(0o755)
    env = os.environ.copy()
    # Ignore caller-supplied library/trust/cache overrides. Lake calculates the
    # original workspace paths itself; the observer receives those exact paths.
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_GITHASH", "LAKE_CACHE_KEY",
                "LD_PRELOAD", "LD_AUDIT", "LD_LIBRARY_PATH"):
        env.pop(key, None)
    env.update(LEAN_SYSROOT=str(shim), LAKE_OVERRIDE_LEAN="true",
               LAKE_ARTIFACT_CACHE="false", LAKE_CACHE_DIR="",
               HAMILTON_COMPILER_CONTROL=str(control_path))
    return env


def compiler_records(output, modules, *, required=False):
    records = {}
    for path in sorted((output / "compiler-records").glob("*.json")):
        value = json.loads(path.read_text())
        module = value.get("module")
        assert module in modules, ("Unexpected compiler record", path, module)
        assert path.name == f"{modules[module]['position']:04d}.json", path
        assert module not in records, ("Duplicate compiler record", module)
        assert value["source_sha256"] == modules[module]["source_sha256"], module
        records[module] = value
    if required:
        assert set(records) == set(modules), "Missing actual source compiler records"
        assert all(v.get("status") == "finished" and v.get("exit_code") == 0
                   and v.get("olean_sha256") for v in records.values()), (
                       "Incomplete, interrupted, or unsuccessful actual source compilation")
        assert not (output / "compiler-stop.json").exists(), "Compiler observer failed"
        for module, value in records.items():
            position = modules[module]["position"]
            for stream in ("stdout", "stderr"):
                assert file_digest(output / "module-build-logs" / f"{position:04d}.{stream}.log") == value[f"{stream}_sha256"], "Compiler log hash mismatch"
            setup_bytes = gzip.decompress((output / "module-setups" / f"{position:04d}.json.gz").read_bytes())
            assert hashlib.sha256(setup_bytes).hexdigest() == value["setup_sha256"], "Lake setup evidence mismatch"
    return records


def batch_records(output, batches, *, required=False):
    """The persistent official-Lake frontend cannot certify a partial plan."""
    records = {}
    for path in sorted((output / "batch-results").glob("*.json")):
        value = json.loads(path.read_text())
        index = value["batch"]
        assert type(index) is int and 1 <= index <= len(batches), "Unexpected batch index"
        assert path.name == f"{index:04d}.json" and index not in records, "Duplicate/misindexed batch"
        expected = ["+" + chain[-1] + ":olean" for chain in batches[index - 1]["chains"]]
        assert value["targets"] == expected, "Lake batch targets changed"
        assert value["status"] in ("running", "finished"), "Unexpected batch state"
        records[index] = value
    if required:
        assert set(records) == set(range(1, len(batches) + 1)), "Incomplete official Lake batch plan"
        assert all(v["status"] == "finished" and v.get("lake_job_success") is True
                   for v in records.values()), "Failed or interrupted official Lake batch"
    return [records[i] for i in sorted(records)]


def resource_summary(records, jobs):
    """Summarize real child accounting and enforced launch floors, not caps."""
    assert jobs in (1, 2)
    second = []
    peak_workers, total_user, total_system, peak_rss = 0, 0.0, 0.0, 0
    for value in records.values():
        launch, measured = value["launch_resources"], value["resources"]
        active = launch["active_compiler_leases_before"]
        assert type(active) is int and 0 <= active < jobs, "Invalid compiler lease evidence"
        assert launch["free_disk_bytes"] >= 1024 ** 3, "Compiler launch violated disk floor"
        if active:
            assert launch["available_memory_bytes"] >= 8 * 1024 ** 3, "Second compiler violated memory launch floor"
            second.append(launch["available_memory_bytes"])
        peak_workers = max(peak_workers, active + 1)
        user, system, rss = (measured["child_user_cpu_seconds"],
                             measured["child_system_cpu_seconds"], measured["child_maximum_rss_bytes"])
        assert user >= 0 and system >= 0 and rss >= 0, "Invalid measured compiler resources"
        total_user += user
        total_system += system
        peak_rss = max(peak_rss, rss)
    return {"measured_compilers": len(records), "recorded_peak_compiler_leases_at_launch": peak_workers,
            "minimum_second_compiler_available_memory_bytes": min(second) if second else None,
            "total_child_user_cpu_seconds": total_user,
            "total_child_system_cpu_seconds": total_system,
            "largest_child_maximum_rss_bytes": peak_rss,
            "hard_cpu_or_memory_cap": False}


def endpoint_output(stdout, code):
    assert code == 0, "Endpoint signature/axiom probe failed"
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", stdout)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", stdout)
    names = [name for name, _ in entries] + clean
    assert len(names) == len(TARGETS) and set(names) == set(TARGETS.values()), names
    for theorem in TARGETS.values():
        assert len(re.findall(r"(?m)^@" + re.escape(theorem) + r"\s*:", stdout)) == 1, (
            "Missing or duplicate actual endpoint signature", theorem)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    actual = {name: sorted({a.strip() for a in axioms.split(",") if a.strip()})
              for name, axioms in entries}
    actual.update({name: [] for name in clean})
    assert all(set(axioms) <= allowed for axioms in actual.values()), actual
    return actual


class AuditInterrupted(RuntimeError):
    """An external cancellation is an inconclusive audit, never a compiler exit."""


@contextlib.contextmanager
def audit_execution(report, save):
    """Translate SIGTERM only within source execution; restore the old handler."""
    previous = signal.getsignal(signal.SIGTERM)

    def terminate(signum, frame):
        raise AuditInterrupted("Audit received SIGTERM")

    signal.signal(signal.SIGTERM, terminate)
    try:
        yield
    except BaseException:
        if report["kernel_audit_status"].startswith("RUNNING"):
            report["kernel_audit_status"] = "INCONCLUSIVE: interrupted, resource, or evidence failure"
        save()
        raise
    finally:
        signal.signal(signal.SIGTERM, previous)


def drain_process_group(process, *, grace_seconds=30, kill_seconds=5):
    """Bound cancellation of the detached Lake group, including its compilers."""
    previous = signal.getsignal(signal.SIGTERM)
    # Repeated cancellation must not interrupt the cleanup itself.
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    try:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=grace_seconds)
        except subprocess.TimeoutExpired:
            pass
        # Even if Lake exits promptly, descendants may ignore SIGTERM. Kill the
        # entire remaining group before the final bounded parent reap.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=kill_seconds)
    finally:
        signal.signal(signal.SIGTERM, previous)


def run_batch(command, *, root, env, stream, refresh, sample=lambda process: None, poll_seconds=2,
              grace_seconds=30, kill_seconds=5, maximum_seconds=None):
    """Run unchanged Lake arguments with signal-safe, bounded group cleanup."""
    # Close the spawn/assignment race without passing a blocked signal mask to
    # the child: defer SIGTERM until the process handle and finally block exist.
    previous = signal.getsignal(signal.SIGTERM)
    pending = []
    signal.signal(signal.SIGTERM, lambda signum, frame: pending.append(signum))
    process = None
    try:
        process = subprocess.Popen(command, cwd=root, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        signal.signal(signal.SIGTERM, previous)
        if pending:
            raise AuditInterrupted("Audit received SIGTERM while spawning Lake")
        started = time.monotonic()
        sample(process)
        while process.poll() is None:
            if maximum_seconds is not None and time.monotonic() - started >= maximum_seconds:
                raise TimeoutError("Bounded audit-owned bootstrap/preflight exceeded its time limit")
            time.sleep(poll_seconds)
            sample(process)
            refresh()
        # Capture the actual Lake exit before cleanup. Once Lake exits, no
        # valid compiler work should remain in its owned process group.
        return process.returncode
    finally:
        try:
            if process is not None:
                drain_process_group(process, grace_seconds=grace_seconds,
                                    kill_seconds=kill_seconds)
                # Retain records written during bounded cancellation cleanup.
                refresh()
        finally:
            signal.signal(signal.SIGTERM, previous)


def file_digest(path):
    value = hashlib.sha256()
    with pathlib.Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def sdk_environment(sysroot):
    """Use the official SDK directly, with no observer or caller C override."""
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_GITHASH", "LEAN_CC",
                "LEAN_AR", "LEAN_OPTS", "LEANC_OPTS", "LD_PRELOAD", "LD_AUDIT",
                "LD_LIBRARY_PATH", "HAMILTON_COMPILER_CONTROL"):
        env.pop(key, None)
    env.update(LEAN_SYSROOT=str(sysroot), LEAN_PATH=str(sysroot / "lib/lean"),
               LEAN=str(sysroot / "bin/lean"))
    return env


def lean_source_imports(text):
    """Read SDK import headers without executing any configuration or Lean."""
    clean, index, depth, quoted = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        if not depth and text[index] == '"':
            quoted = not quoted
            clean.append(" ")
            index += 1
        elif quoted and text[index] == "\\":
            clean.extend("  ")
            index += 2
        elif quoted:
            clean.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        else:
            clean.append(text[index] if not depth or text[index] == "\n" else " ")
            index += 1
    assert depth == 0, "Unclosed SDK source comment"
    text = "".join(clean)
    imports = [] if re.search(r"(?m)^\s*prelude\s*$", text) else ["Init"]
    for match in re.finditer(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)", text):
        for name in match.group(1).split():
            assert all(part and all(c.isalnum() or c in "_'" for c in part)
                       for part in name.split(".")), ("Unsupported SDK import", name)
            if name not in imports:
                imports.append(name)
    return imports


def sdk_import_closure(driver, sysroot):
    """Retain the full explicit transitive initialization/import source graph."""
    direct = lean_source_imports(driver.read_text())
    assert direct == ["Init", *DRIVER_IMPORTS], "Audit driver import roots changed"
    modules = {}

    def visit(name):
        if name in modules:
            return
        relative = pathlib.Path(name.replace(".", "/") + ".lean")
        source = sysroot / "src/lean" / relative
        if name == "Lake" or name.startswith("Lake."):
            source = sysroot / "src/lean/lake" / relative
        assert source.is_file(), ("SDK import source missing", name)
        imports = lean_source_imports(source.read_text())
        object_path = sysroot / "lib/lean" / relative.with_suffix(".olean")
        assert object_path.is_file(), ("SDK import object missing", name)
        ir_path = object_path.with_suffix(".ir")
        assert ir_path.is_file(), ("SDK interpreter IR missing", name)
        artifacts = {str(path): file_digest(path) for path in
                     (object_path, object_path.with_suffix(".olean.private"),
                      object_path.with_suffix(".olean.server"), ir_path) if path.is_file()}
        modules[name] = {"source": str(source), "source_sha256": file_digest(source),
                         "imports": imports, "object_sha256": artifacts}
        for imported in imports:
            visit(imported)

    for name in direct:
        visit(name)
    return {"driver_imports": direct, "modules": modules,
            "initialization": "compiler-generated main calls initialize_HamiltonAuditDriver(1); generated module initializers recursively propagate builtin to their imports"}


def generated_main_contract(path):
    """Fail closed if the compiler did not emit the reviewed native entry path."""
    text = path.read_text()
    assert text.count("int main(int argc, char ** argv)") == 1, "Missing/duplicate generated native main"
    main = text[text.index("int main(int argc, char ** argv)"):]
    initializer = "res = initialize_HamiltonAuditDriver(1 /* builtin */);"
    assert initializer in main, "Missing builtin initialization of complete driver import closure"
    assert main.index("lean_initialize();") < main.index(initializer) < main.index("lean_io_mark_end_initialization();") < main.index("lean_init_task_manager();"), "Native initialization order changed"
    module = text[text.index("LEAN_EXPORT lean_object* initialize_HamiltonAuditDriver(uint8_t builtin) {"):text.index("int main(int argc, char ** argv)")]
    for symbol in ("Init", "Lake", "Lake_CLI_Build", "Lake_Load_Workspace"):
        assert f"res = initialize_{symbol}(builtin);" in module, ("Generated driver import initializer missing", symbol)


def sdk_identity_manifest(sysroot):
    """Hash every selected official SDK input, with contained symlink targets.

    Includes all bin/include/lib files plus shipped share/source support files.
    Traversal never accepts a link outside this SDK or a cyclic directory link.
    The stable digest excludes machine-local absolute paths.
    """
    sysroot = pathlib.Path(sysroot).resolve()
    entries = {}

    def visit(path, ancestors):
        resolved = path.resolve(strict=True)
        assert resolved.is_relative_to(sysroot), ("SDK symlink escapes selected installation", path)
        relative = path.relative_to(sysroot).as_posix()
        if path.is_symlink():
            entry = {"kind": "symlink", "target": os.readlink(path),
                     "resolved_target": resolved.relative_to(sysroot).as_posix()}
            if resolved.is_file():
                entry.update(target_sha256=file_digest(resolved), bytes=resolved.stat().st_size,
                             executable=bool(resolved.stat().st_mode & 0o111))
            else:
                assert resolved.is_dir(), ("Unexpected SDK symlink target", path)
            entries[relative] = entry
        elif path.is_file():
            entries[relative] = {"kind": "file", "sha256": file_digest(path),
                                 "bytes": path.stat().st_size, "executable": bool(path.stat().st_mode & 0o111)}
        else:
            assert path.is_dir(), ("Unsupported SDK filesystem input", path)
            entries[relative] = {"kind": "directory"}
        if resolved.is_dir():
            assert resolved not in ancestors, ("Cyclic SDK directory symlink", path)
            for child in sorted(path.iterdir()):
                visit(child, ancestors | {resolved})

    for name in SDK_IDENTITY_ROOTS:
        path = sysroot / name
        assert path.is_dir(), ("Official SDK input root missing", name)
        visit(path, set())
    encoded = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode()
    return {"roots": list(SDK_IDENTITY_ROOTS), "entries": entries,
            "tree_sha256": hashlib.sha256(encoded).hexdigest(),
            "official_release": {"version": "4.29.0", "commit": LAKE_API_SHA,
                                 "archive_url": SDK_ARCHIVE_URL, "archive_sha256": SDK_ARCHIVE_SHA256}}


def bootstrap_native_driver(driver, sysroot, output, *, root, run=run_batch):
    """Compile only the audit-owned orchestration source; never project source.

    Exact compile/link commands, SDK identities, generated C and lossless logs
    are retained. This function is an explicit workflow gate, not an on-demand
    fallback to an interpreted frontend.
    """
    directory = output / "native-bootstrap"
    directory.mkdir()  # Existing bootstrap output is never silently reused.
    copied = directory / "HamiltonAuditDriver.lean"
    copied.write_bytes(driver.read_bytes())
    c_file, object_file = directory / "HamiltonAuditDriver.c", directory / "HamiltonAuditDriver.o"
    executable = directory / "hamilton-lake-driver"
    sdk_inputs = [sysroot / "bin" / name for name in ("lean", "leanc", "clang", "ld.lld")]
    sdk_inputs += sorted((sysroot / "lib/lean").glob("lib*.a"))
    plugin = sysroot / "lib/lean/libLake_shared.so"
    sdk_inputs.append(plugin)
    assert all(path.is_file() for path in sdk_inputs), "Official native SDK input missing"
    assert (sysroot / "lib/lean/libLake.a").is_file(), "Official static Lake library missing"
    closure_path = directory / "import-closure.json"
    closure_path.write_text(json.dumps(sdk_import_closure(copied, sysroot), indent=2) + "\n")
    sdk_identity = sdk_identity_manifest(sysroot)
    assert sdk_identity["tree_sha256"] == SDK_TREE_SHA256, "Selected SDK differs from checksum-verified official release tree"
    sdk_identity_path = directory / "sdk-identity.json"
    sdk_identity_path.write_text(json.dumps(sdk_identity, indent=2) + "\n")
    env = sdk_environment(sysroot)
    manifest = {"status": "running", "source": str(driver),
                "source_sha256": file_digest(driver), "compiler_reference_sha": LAKE_API_SHA,
                "bootstrap_environment": {key: env[key] for key in BOOTSTRAP_ENV_KEYS},
                "sdk_input_sha256": {str(path): file_digest(path) for path in sdk_inputs},
                "sdk_identity": str(sdk_identity_path), "sdk_identity_sha256": file_digest(sdk_identity_path),
                "sdk_tree_sha256": sdk_identity["tree_sha256"],
                "import_closure": str(closure_path), "import_closure_sha256": file_digest(closure_path),
                "steps": [], "artifacts": {}}
    manifest_path = directory / "bootstrap.json"

    def save():
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")

    def step(name, command):
        record = {"name": name, "command": command, "status": "running"}
        manifest["steps"].append(record)
        save()
        log = directory / (name + ".log")
        started = time.monotonic()
        with log.open("wb") as stream:
            code = run(command, root=root, env=env, stream=stream, refresh=save,
                       maximum_seconds=600)
        record.update(status="finished", exit_code=code, elapsed_seconds=time.monotonic() - started,
                      log=str(log), log_sha256=file_digest(log))
        save()
        assert code == 0, ("Native driver bootstrap failed", name, code)
        return log.read_text().strip()

    try:
        version = step("version", [str(sysroot / "bin/lean"), "--version"])
        assert re.search(r"Lean \(version 4\.29\.0(?:,|\))", version), version
        assert step("githash", [str(sysroot / "bin/lean"), "--githash"]) == LAKE_API_SHA, "Wrong native bootstrap SDK revision"
        step("leanc-cflags", [str(sysroot / "bin/leanc"), "--print-cflags"])
        step("leanc-ldflags", [str(sysroot / "bin/leanc"), "--print-ldflags"])
        step("emit-c", [str(sysroot / "bin/lean"), "--plugin", str(plugin), "-R", str(directory),
                        "-o", str(directory / "HamiltonAuditDriver.olean"),
                        "-i", str(directory / "HamiltonAuditDriver.ilean"),
                        "-c", str(c_file), str(copied)])
        generated_main_contract(c_file)
        step("compile-c", [str(sysroot / "bin/leanc"), "-v", "-c", "-O3", "-DNDEBUG",
                           "-DLEAN_EXPORTING", "-o", str(object_file), str(c_file)])
        # -rdynamic is Lake's documented supportInterpreter link mode on Linux.
        # Static official Lake symbols are initialized via the generated main;
        # no runtime plugin alias or manually called private initializer is used.
        step("link", [str(sysroot / "bin/leanc"), "-v", "-rdynamic", "-o", str(executable),
                      str(object_file), str(sysroot / "lib/lean/libLake.a")])
        assert executable.is_file() and os.access(executable, os.X_OK), "Native executable not produced"
        manifest["artifacts"] = {str(path): file_digest(path) for path in directory.iterdir()
                                 if path.is_file() and path != manifest_path}
        manifest.update(status="verified-bootstrap", executable=str(executable),
                        executable_sha256=file_digest(executable))
        save()
        verify_native_bootstrap(driver, sysroot, output)
        return manifest
    except BaseException as error:
        manifest.update(status="inconclusive", error=f"{type(error).__name__}: {error}")
        save()
        raise


def verify_native_bootstrap(driver, sysroot, output):
    directory = output / "native-bootstrap"
    manifest = json.loads((directory / "bootstrap.json").read_text())
    assert manifest["status"] == "verified-bootstrap", "Native bootstrap incomplete"
    assert manifest["source_sha256"] == file_digest(driver), "Native driver source changed"
    assert manifest["compiler_reference_sha"] == LAKE_API_SHA, "Wrong native bootstrap revision"
    assert manifest["bootstrap_environment"] == {"LEAN_SYSROOT": str(sysroot), "LEAN_PATH": str(sysroot / "lib/lean"), "LEAN": str(sysroot / "bin/lean")}, "Native bootstrap SDK selection changed"
    assert manifest["executable"] == str(directory / "hamilton-lake-driver"), "Unexpected native executable path"
    assert file_digest(directory / "HamiltonAuditDriver.lean") == manifest["source_sha256"], "Compiled source copy differs from reviewed driver"
    required_inputs = {str(sysroot / "bin" / name) for name in ("lean", "leanc", "clang", "ld.lld")}
    required_inputs.update(str(path) for path in (sysroot / "lib/lean").glob("lib*.a"))
    required_inputs.add(str(sysroot / "lib/lean/libLake_shared.so"))
    assert set(manifest["sdk_input_sha256"]) == required_inputs, "Native SDK identity set changed"
    required_artifacts = {str(directory / ("HamiltonAuditDriver" + extension)) for extension in (".lean", ".c", ".o", ".olean", ".ilean")}
    required_artifacts.update((str(directory / "hamilton-lake-driver"), str(directory / "import-closure.json")))
    required_artifacts.add(str(directory / "sdk-identity.json"))
    assert required_artifacts <= manifest["artifacts"].keys(), "Missing bootstrap output evidence"
    for path, digest in {**manifest["sdk_input_sha256"], **manifest["artifacts"]}.items():
        assert file_digest(path) == digest, ("Native bootstrap identity changed", path)
    assert all(step["status"] == "finished" and step["exit_code"] == 0
               and file_digest(step["log"]) == step["log_sha256"] for step in manifest["steps"]), "Native compile/link evidence incomplete or changed"
    assert [step["name"] for step in manifest["steps"]] == ["version", "githash", "leanc-cflags", "leanc-ldflags", "emit-c", "compile-c", "link"], "Native bootstrap step set changed"
    assert file_digest(manifest["executable"]) == manifest["executable_sha256"], "Native executable changed"
    assert file_digest(manifest["import_closure"]) == manifest["import_closure_sha256"], "SDK import closure evidence changed"
    assert manifest["sdk_tree_sha256"] == SDK_TREE_SHA256, "Unexpected official SDK identity anchor"
    assert manifest["sdk_identity"] == str(directory / "sdk-identity.json"), "Unexpected SDK native-input manifest path"
    assert file_digest(manifest["sdk_identity"]) == manifest["sdk_identity_sha256"], "SDK native-input identity evidence changed"
    recorded_identity = json.loads(pathlib.Path(manifest["sdk_identity"]).read_text())
    assert recorded_identity["tree_sha256"] == SDK_TREE_SHA256, "SDK catalog differs from official archive identity anchor"
    current_identity = sdk_identity_manifest(sysroot)
    assert current_identity["tree_sha256"] == SDK_TREE_SHA256 and current_identity == recorded_identity, "Shipped SDK native/header/support input changed"
    closure = json.loads(pathlib.Path(manifest["import_closure"]).read_text())
    for module in closure["modules"].values():
        assert file_digest(module["source"]) == module["source_sha256"], "SDK import source changed"
        for path, digest in module["object_sha256"].items():
            assert file_digest(path) == digest, ("SDK import object changed", path)
    generated_main_contract(output / "native-bootstrap/HamiltonAuditDriver.c")
    return manifest


def verify_selected_install(output, executable, shim):
    value = json.loads((output / "lake-install.json").read_text())
    expected = {"application": str(executable), "lean_sysroot": str(shim),
                "lean_executable": str(shim / "bin/lean"), "lean_githash": LAKE_API_SHA,
                "lake_home": str(shim), "lake_library_directory": str(shim / "lib/lean"),
                "lake_shared_library": str(shim / "lib/lean/libLake_shared.so")}
    assert value == expected, "Native driver did not select the observed official installation"
    return value


def native_driver_preflight(driver, sysroot, output, observer, *, run=run_batch):
    """One fresh project compiler after two separate local Lean config loads.

    This bounded test uses the same executable, observer and evidence gates as
    the campaign but never imports campaign/upstream/Mathlib source or objects.
    """
    bootstrap = verify_native_bootstrap(driver, sysroot, output)
    directory = output / "native-preflight"
    directory.mkdir()
    root, evidence = directory / "workspace", directory / "evidence"
    root.mkdir()
    evidence.mkdir()
    for name in ("module-build-logs", "compiler-records", "module-setups", "batch-results", "frontend-build-logs"):
        (evidence / name).mkdir()
    package_names = ("audit_dep_a", "audit_dep_b")
    config = 'name = "DifferentialGeometry"\nversion = "0.0.0"\n[[lean_lib]]\nname = "DifferentialGeometry"\n'
    packages = []
    for index, name in enumerate(package_names):
        dependency = root / name
        dependency.mkdir()
        # Different headers force two distinct import-cache misses, not merely
        # two files sharing one already-loaded Lake header environment.
        header = "import Lake\n" + ("import Lake.CLI.Build\n" if index else "")
        (dependency / "lakefile.lean").write_text(header + f"open Lake DSL\npackage {name}\n")
        (dependency / "lake-manifest.json").write_text(json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "name": name, "lakeDir": ".lake"}) + "\n")
        config += f'[[require]]\nname = "{name}"\npath = "{name}"\n'
        packages.append({"type": "path", "name": name, "dir": name,
                         "manifestFile": "lake-manifest.json", "configFile": "lakefile.lean", "inherited": False})
    (root / "lakefile.toml").write_text(config)
    (root / "lake-manifest.json").write_text(json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages", "packages": packages, "name": "DifferentialGeometry", "lakeDir": ".lake"}) + "\n")
    module = "DifferentialGeometry.NativePreflight"
    source = root / "DifferentialGeometry/NativePreflight.lean"
    source.parent.mkdir()
    source.write_text("theorem native_preflight : True := True.intro\n")
    source_inputs = {str(path): file_digest(path) for path in root.rglob("*") if path.is_file()}
    modules = {module: {"position": 1, "source_sha256": file_digest(source), "project_imports": []}}
    batches = [{"modules": [module], "chains": [[module]]}]
    plan = evidence / "lake-batch-plan.json"
    plan.write_text(json.dumps({"batches": batches}) + "\n")
    compiler = sysroot / "bin/lean"
    control = {"root": str(root), "evidence": str(evidence), "sysroot": str(sysroot),
               "compiler": str(compiler), "compiler_sha256": file_digest(compiler),
               "jobs": 1, "modules": modules, "allowed_modules": [module],
               "active_batch_path": str(evidence / "active-batch.json")}
    control_path = evidence / "compiler-control.json"
    control_path.write_text(json.dumps(control, indent=2) + "\n")
    env = make_compiler_shim(evidence, sysroot, observer, control_path)
    shim = evidence / "observed-toolchain"
    executable = pathlib.Path(bootstrap["executable"])
    command = [str(executable), str(plan), str(evidence)]
    log = evidence / "frontend-build-logs/lake.log"
    receipt = {"status": "running", "command": command, "bootstrap_executable_sha256": bootstrap["executable_sha256"],
               "observer_sha256": file_digest(observer), "source_inputs_sha256": source_inputs,
               "plan_sha256": file_digest(plan), "control_sha256": file_digest(control_path),
               "environment": {key: env[key] for key in ("LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN", "LAKE_ARTIFACT_CACHE", "LAKE_CACHE_DIR", "HAMILTON_COMPILER_CONTROL")}}
    receipt_path = directory / "preflight.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    try:
        assert_no_project_objects(root)
        save()
        started = time.monotonic()
        with log.open("wb") as stream:
            code = run(command, root=root, env=env, stream=stream, refresh=save, maximum_seconds=180)
        receipt.update(exit_code=code, elapsed_seconds=time.monotonic() - started, log_sha256=file_digest(log))
        save()
        assert code == 0, ("Native driver preflight failed", code)
        batch_records(evidence, batches, required=True)
        records = compiler_records(evidence, modules, required=True)
        receipt["compiler_resources"] = resource_summary(records, 1)
        receipt["selected_installation"] = verify_selected_install(evidence, executable, shim)
        for path, digest in source_inputs.items():
            assert file_digest(path) == digest, "Native preflight source/config changed"
        assert file_digest(plan) == receipt["plan_sha256"] and file_digest(control_path) == receipt["control_sha256"], "Native preflight plan/control changed"
        assert file_digest(observer) == receipt["observer_sha256"], "Native preflight observer changed"
        object_path = root / ".lake/build/lib/lean/DifferentialGeometry/NativePreflight.olean"
        assert file_digest(object_path) == records[module]["olean_sha256"], "Native preflight object changed"
        verify_native_bootstrap(driver, sysroot, output)
        receipt.update(status="passed", compiler_records=records,
                       batch_records=batch_records(evidence, batches, required=True))
        save()
        return receipt
    except BaseException as error:
        receipt.update(status="inconclusive", error=f"{type(error).__name__}: {error}")
        save()
        raise
    finally:
        # The isolated preflight's view must not be followed by artifact upload.
        # Only audit-created links are removed, never the official SDK targets.
        shutil.rmtree(shim)


def verify_native_preflight(output, bootstrap, observer):
    receipt = json.loads((output / "native-preflight/preflight.json").read_text())
    assert receipt["status"] == "passed" and receipt["exit_code"] == 0, "Native runtime preflight did not pass"
    assert receipt["bootstrap_executable_sha256"] == bootstrap["executable_sha256"], "Preflight used another executable"
    assert receipt["observer_sha256"] == file_digest(observer), "Preflight used another observer"
    evidence = output / "native-preflight/evidence"
    assert receipt["plan_sha256"] == file_digest(evidence / "lake-batch-plan.json"), "Preflight plan changed"
    assert receipt["control_sha256"] == file_digest(evidence / "compiler-control.json"), "Preflight control changed"
    for path, digest in receipt["source_inputs_sha256"].items():
        assert file_digest(path) == digest, "Native preflight fixture changed"
    assert receipt["log_sha256"] == file_digest(evidence / "frontend-build-logs/lake.log"), "Preflight log changed"
    assert verify_selected_install(evidence, pathlib.Path(bootstrap["executable"]), evidence / "observed-toolchain") == receipt["selected_installation"], "Preflight selected-installation evidence changed"
    control = json.loads((evidence / "compiler-control.json").read_text())
    plan = json.loads((evidence / "lake-batch-plan.json").read_text())
    records = compiler_records(evidence, control["modules"], required=True)
    assert records == receipt["compiler_records"], "Preflight compiler evidence changed"
    assert batch_records(evidence, plan["batches"], required=True) == receipt["batch_records"], "Preflight batch evidence changed"
    resource_summary(records, 1)
    for module, record in records.items():
        path = pathlib.Path(control["root"]) / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        assert file_digest(path) == record["olean_sha256"], "Preflight object changed"
    return receipt


class ProcessGroupSamples:
    """Sample Linux process-group RSS/CPU; these are observations, not caps.

    Short-lived processes can be missed. Per-module compiler CPU and maximum
    RSS come separately from the observer's reaped-child resource accounting.
    """
    def __init__(self):
        self.value = {"samples": 0, "sampled_peak_group_rss_bytes": 0,
                      "sampled_peak_group_processes": 0,
                      "sampled_peak_frontend_rss_bytes": 0,
                      "sampled_peak_frontend_threads": 0,
                      "sampled_frontend_cpu_seconds": 0.0,
                      "measurement": "Linux /proc snapshots; RSS is a sum with shared pages counted per process; not a hard memory or CPU limit"}

    def __call__(self, process):
        ticks, page = os.sysconf("SC_CLK_TCK"), os.sysconf("SC_PAGE_SIZE")
        group_rss, count = 0, 0
        for path in pathlib.Path("/proc").glob("[0-9]*/stat"):
            try:
                fields = path.read_text().rpartition(")")[2].split()
                if int(fields[2]) != process.pid or fields[0] == "Z":
                    continue
                rss = max(0, int(fields[21])) * page
                group_rss += rss
                count += 1
                if path.parent.name == str(process.pid):
                    status = (path.parent / "status").read_text()
                    threads = next(int(line.split()[1]) for line in status.splitlines()
                                   if line.startswith("Threads:"))
                    self.value["sampled_peak_frontend_threads"] = max(
                        self.value["sampled_peak_frontend_threads"], threads)
                    self.value["sampled_peak_frontend_rss_bytes"] = max(
                        self.value["sampled_peak_frontend_rss_bytes"], rss)
                    self.value["sampled_frontend_cpu_seconds"] = max(
                        self.value["sampled_frontend_cpu_seconds"],
                        (int(fields[11]) + int(fields[12])) / ticks)
            except (OSError, ValueError, IndexError, StopIteration):
                # Races with real process exit are expected; absent observations
                # are never substituted for compiler exits or resource bounds.
                continue
        self.value["samples"] += 1
        self.value["sampled_peak_group_rss_bytes"] = max(
            self.value["sampled_peak_group_rss_bytes"], group_rss)
        self.value["sampled_peak_group_processes"] = max(
            self.value["sampled_peak_group_processes"], count)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=pathlib.Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--plan-only", action="store_true")
    mode.add_argument("--bootstrap-only", action="store_true")
    mode.add_argument("--native-preflight-only", action="store_true")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    root = args.source.resolve()
    here = pathlib.Path(__file__).resolve().parents[2]
    spec = importlib.util.spec_from_file_location(
        "point4_scan", here / "curvature/scripts/point4_scan.py")
    assert spec and spec.loader
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)

    def git(*arguments: str) -> str:
        return subprocess.check_output(["git", *arguments], cwd=root,
                                       text=True).strip()

    assert git("rev-parse", "HEAD") == SOURCE_SHA, "Wrong upstream source SHA"
    assert git("status", "--porcelain") == "", "Upstream checkout is modified"
    assert_no_project_objects(root)
    assert (root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.29.0"
    config = tomllib.loads((root / "lakefile.toml").read_text())
    assert set(config) == {"name", "version", "keywords", "defaultTargets", "leanOptions", "require", "lean_lib"}
    assert config["name"] == "DifferentialGeometry"
    assert config["lean_lib"] == [{"name": "DifferentialGeometry"}], "Unexpected library options"
    requirements = config["require"]
    assert len(requirements) == 1 and requirements[0] == {
        "name": "mathlib", "scope": "leanprover-community", "rev": "v4.29.0"
    }, "Unexpected upstream dependency configuration"

    visiting: set[str] = set()
    seen: set[str] = set()
    order: list[str] = []
    graph: dict[str, list[str]] = {}
    findings: list[str] = []
    execution_findings: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        assert module not in visiting, f"Cyclic import: {module}"
        visiting.add(module)
        path = root / (module.replace(".", "/") + ".lean")
        assert path.is_file(), f"Missing source: {module}"
        text = "\n".join(scanner.strip_comments(path.read_text()))
        imports: list[str] = []
        for match in re.finditer(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", text):
            for name in match.group(1).split():
                # Lean module names can contain Unicode letters (for example
                # Γ in the immutable release), so never truncate to ASCII.
                assert all(part and all(c.isalnum() or c in "_'" for c in part)
                           for part in name.split(".")), (
                               module, "Unexpected import syntax", name)
                if name.startswith("DifferentialGeometry.") or name == "DifferentialGeometry":
                    imports.append(name)
        graph[module] = imports
        for match in re.finditer(r"\b(?:sorry|admit|sorryAx|axiom|native_decide)\b|\bdecide!", text):
            line = text.count("\n", 0, match.start()) + 1
            findings.append(f"{module}:{line}: {match.group()}")
        for match in re.finditer(
                r"\b(?:unsafe|implemented_by|run_tac|run_cmd|initialize|builtin_initialize)\b"
                r"|#eval\b|\bIO\.(?:Process|FS)\b|\bdebug\.skipKernelTC\b|@\[extern\b", text):
            line = text.count("\n", 0, match.start()) + 1
            execution_findings.append(f"{module}:{line}: {match.group()}")
        for dependency in imports:
            visit(dependency)
        visiting.remove(module)
        seen.add(module)
        order.append(module)

    for module in TARGETS:
        visit(module)
    assert len(order) == 2270, "Unexpected immutable source closure size"
    assert sum((root / (m.replace('.', '/') + '.lean')).stat().st_size for m in order) == 64667615, "Unexpected immutable source closure bytes"
    output = root.parent / "hamilton-release-audit"
    output.mkdir(exist_ok=True)
    report = {
        "source_sha": SOURCE_SHA,
        "audit_commit_sha": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=here, text=True).strip(),
        "audit_script_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        "observer_script_sha256": hashlib.sha256(pathlib.Path(__file__).with_name("observe-hamilton-compiler.py").read_bytes()).hexdigest(),
        "lake_driver_sha256": file_digest(pathlib.Path(__file__).with_name("build-hamilton-batches.lean")),
        "lake_api_reference_sha": LAKE_API_SHA,
        "mathlib_sha": MATHLIB_SHA,
        "targets": TARGETS,
        "source_closure_modules": len(order),
        "source_closure_bytes": sum((root / (m.replace('.', '/') + '.lean')).stat().st_size for m in order),
        "source_findings": findings,
        "execution_or_trust_findings": execution_findings,
        "graph": graph,
        "build_order": order,
        "built": [],
        "project_objects_before_build": [],
        "source_sha256": {m: hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest() for m in order},
        "lakefile_sha256": hashlib.sha256((root / "lakefile.toml").read_bytes()).hexdigest(),
        "kernel_audit_status": "NOT RUN",
        "point4_status": "OPEN: no semantic bridge constructed",
    }
    report_path = output / "report.json"

    def save() -> None:
        temporary = report_path.with_suffix(".tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(report_path)

    save()
    print(f"Focused upstream source closure: {len(order)} modules", flush=True)
    assert not findings, "Proof-placeholder/axiom findings: " + "; ".join(findings)
    assert not execution_findings, "Manual execution/trust review required: " + "; ".join(execution_findings)
    if args.plan_only:
        return
    # The immutable release intentionally does not track a Lake manifest.
    # Check its tagged configuration before setup and the actual resolved
    # immutable revision after setup has generated the local manifest.
    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == MATHLIB_SHA, "Wrong resolved Mathlib pin"
    resolved = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/mathlib", text=True).strip()
    assert resolved == MATHLIB_SHA, "Resolved Mathlib checkout disagrees with manifest"

    # Ask only for the required SDK path, never dump the caller environment.
    sysroot = pathlib.Path(subprocess.check_output(
        ["lake", "env", "lean", "--print-prefix"], cwd=root, text=True).strip()).resolve()
    compiler = sysroot / "bin/lean"
    driver = pathlib.Path(__file__).with_name("build-hamilton-batches.lean")
    observer = pathlib.Path(__file__).with_name("observe-hamilton-compiler.py")
    if args.bootstrap_only or args.native_preflight_only:
        report["kernel_audit_status"] = "RUNNING: audit-owned native bootstrap/preflight only"
        save()
        with audit_execution(report, save):
            if args.bootstrap_only:
                report["native_bootstrap"] = bootstrap_native_driver(driver, sysroot, output, root=root)
            else:
                report["native_preflight"] = native_driver_preflight(driver, sysroot, output, observer)
        report["kernel_audit_status"] = "NOT RUN: audit-owned native bootstrap/preflight passed; upstream closure unchecked"
        save()
        return
    bootstrap = verify_native_bootstrap(driver, sysroot, output)
    preflight = verify_native_preflight(output, bootstrap, observer)
    report.update(native_bootstrap=bootstrap, native_preflight=preflight,
                  native_bootstrap_manifest_sha256=file_digest(output / "native-bootstrap/bootstrap.json"),
                  native_preflight_receipt_sha256=file_digest(output / "native-preflight/preflight.json"))

    # One persistent official Lake FetchM store, fetching and awaiting only
    # one bounded direct-import-chain batch at a time. Compiler evidence remains
    # independent of Lake job status and the aggregate frontend process exit.
    memory = {}
    if pathlib.Path("/proc/meminfo").is_file():
        memory = {line.split(':')[0]: int(line.split()[1]) * 1024
                  for line in pathlib.Path("/proc/meminfo").read_text().splitlines()
                  if line.startswith(("MemTotal:", "MemAvailable:"))}
    jobs = args.jobs if memory.get("MemTotal", 0) >= 14 * 1024 ** 3 else 1
    batches = chain_batches(order, graph, jobs)
    positions = {module: i + 1 for i, module in enumerate(order)}
    report.update(kernel_audit_status="RUNNING: source closure incomplete",
                  source_compile_workers=jobs, initial_memory_bytes=memory,
                  build_mode="persistent official Lake FetchM store; bounded-chain batches; quiet frontend; real compiler observation",
                  compiler_results={}, batch_plan=batches, batch_results=[],
                  project_artifact_cache_enabled=False,
                  resource_bounds={"maximum_real_compiler_workers": jobs,
                                   "second_compiler_available_memory_floor_bytes": 8 * 1024 ** 3,
                                   "free_disk_launch_floor_bytes": 1024 ** 3,
                                   "persistent_lake_frontends": 1,
                                   "hard_cpu_or_memory_cap": False})
    for name in ("module-build-logs", "compiler-records", "module-setups", "frontend-build-logs", "batch-results"):
        directory = output / name
        directory.mkdir(exist_ok=True)
        assert not list(directory.iterdir()), "Audit evidence directory is not fresh: " + name
    # Resolve the real compiler through the original pinned Lake environment.
    # Metadata queries are forwarded to this exact binary by the shim.
    version = subprocess.check_output([str(compiler), "--version"], cwd=root, text=True).strip()
    assert re.search(r"Lean \(version 4\.29\.0(?:,|\))", version), version
    report.update(compiler_version=version, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                  original_lean_sysroot=str(sysroot))
    modules = {m: {"position": positions[m], "source_sha256": report["source_sha256"][m],
                   "project_imports": graph[m]} for m in order}
    control = {"root": str(root), "evidence": str(output), "sysroot": str(sysroot),
               "compiler": str(compiler), "compiler_sha256": report["compiler_sha256"],
               "jobs": jobs, "modules": modules, "allowed_modules": order,
               "active_batch_path": str(output / "active-batch.json")}
    assert not pathlib.Path(control["active_batch_path"]).exists(), "Active batch evidence is not fresh"
    control_path = output / "compiler-control.json"
    control_path.write_text(json.dumps(control, indent=2) + "\n")
    env = make_compiler_shim(output, sysroot, observer, control_path)
    # This second assertion is immediately before the first compilation, after
    # official dependency-cache retrieval and all audit plumbing setup.
    assert_no_project_objects(root)
    save()

    record_mtimes = {}
    sampler = ProcessGroupSamples()
    report["frontend_resource_samples"] = sampler.value

    def refresh():
        current_batches = batch_records(output, batches)
        changed = current_batches != report["batch_results"]
        previous_batches = {value["batch"]: value for value in report["batch_results"]}
        report["batch_results"] = current_batches
        for path in (output / "compiler-records").glob("*.json"):
            mtime = path.stat().st_mtime_ns
            if record_mtimes.get(path) != mtime:
                record_mtimes[path] = mtime
                value = json.loads(path.read_text())
                m = value.get("module")
                assert m in modules and path.name == f"{positions[m]:04d}.json", "Unexpected compiler record"
                assert value["source_sha256"] == modules[m]["source_sha256"], "Source evidence mismatch"
                report["compiler_results"][m] = value
                changed = True
        if not changed:
            return
        report["built"] = [m for m in order if report["compiler_results"].get(m, {}).get("status") == "finished"
                           and report["compiler_results"][m].get("exit_code") == 0
                           and report["compiler_results"][m].get("olean_sha256")]
        report["failed_modules"] = [m for m, v in report["compiler_results"].items()
                                    if v.get("status") == "finished" and v.get("exit_code") != 0]
        for value in current_batches:
            if value["status"] == "finished" and value.get("lake_job_success") is True:
                index = value["batch"]
                assert all(m in report["built"] for m in batches[index - 1]["modules"]), "Lake job success without every real compiler success"
                assert all(report["compiler_results"][m].get("batch") == index
                           for m in batches[index - 1]["modules"]), "Compiler evidence belongs to another batch"
                if previous_batches.get(index, {}).get("status") != "finished":
                    print(f"BATCH {index}/{len(batches)} complete; {len(report['built'])}/{len(order)} actual source compiler successes", flush=True)
        save()

    plan_path = output / "lake-batch-plan.json"
    plan_path.write_text(json.dumps({"batches": batches}, indent=2) + "\n")
    report["lake_batch_plan_sha256"] = file_digest(plan_path)
    executable = pathlib.Path(bootstrap["executable"])
    command = [str(executable), str(plan_path), str(output)]
    report["lake_frontend_executable_sha256"] = bootstrap["executable_sha256"]
    report["bootstrap_plugin_sha256"] = file_digest(sysroot / "lib/lean/libLake_shared.so")
    report["lake_frontend_command"] = command
    save()

    with audit_execution(report, save):
        started = time.monotonic()
        path = output / "frontend-build-logs" / "lake.log"
        with path.open("wb") as stream:
            code = run_batch(command, root=root, env=env, stream=stream,
                             refresh=refresh, sample=sampler)
        refresh()
        report["lake_frontend_result"] = {"command": command, "exit_code": code,
                                          "elapsed_seconds": time.monotonic() - started,
                                          "log_sha256": file_digest(path)}
        print(f"Lake frontend EXIT {code}; {len(report['built'])}/{len(order)} actual source compiler successes", flush=True)
        if code != 0:
            report["kernel_audit_status"] = "BUILD FAILED: official Lake frontend or real compiler/observer failure"
            save()
            raise SystemExit(code if code > 0 else 1)
        verify_native_bootstrap(driver, sysroot, output)
        verify_native_preflight(output, bootstrap, observer)
        assert file_digest(output / "native-bootstrap/bootstrap.json") == report["native_bootstrap_manifest_sha256"], "Native bootstrap manifest changed"
        assert file_digest(output / "native-preflight/preflight.json") == report["native_preflight_receipt_sha256"], "Native preflight receipt changed"
        report["selected_lake_installation"] = verify_selected_install(output, executable, output / "observed-toolchain")
        assert file_digest(driver) == report["lake_driver_sha256"], "Audit driver changed during execution"
        batch_records(output, batches, required=True)
        records = compiler_records(output, modules, required=True)
        report["compiler_resource_summary"] = resource_summary(records, jobs)
        assert file_digest(plan_path) == report["lake_batch_plan_sha256"], "Lake batch plan changed"
        assert report["built"] == order, "Incomplete source closure"
        for m in order:
            assert hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest() == report["source_sha256"][m]
            result = report["compiler_results"][m]
            assert hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest() == result["source_sha256"]
            assert hashlib.sha256((root / (".lake/build/lib/lean/" + m.replace('.', '/') + '.olean')).read_bytes()).hexdigest() == result["olean_sha256"]

    report["kernel_audit_status"] = "RUNNING: source closure complete, endpoint audit pending"
    save()
    probe = output / "endpoint-probe.lean"
    probe.write_text("\n".join(
        ["import " + m for m in TARGETS] +
        [command + theorem for theorem in TARGETS.values()
         for command in ("#check @", "#print axioms ")] + [""]))
    try:
        with audit_execution(report, save):
            command = ["lake", "env", "lean", str(probe)]
            path = output / "endpoint-probe.log"
            endpoint_samples = ProcessGroupSamples()
            report["endpoint_resource_samples"] = endpoint_samples.value
            with path.open("wb") as stream:
                code = run_batch(command, root=root, env=os.environ.copy(), stream=stream,
                                 refresh=lambda: None, sample=endpoint_samples)
            stdout = path.read_text()
            print(stdout, flush=True)
            report["endpoint_probe_result"] = {"command": command, "exit_code": code,
                                                "log_sha256": file_digest(path)}
            report["endpoint_axioms"] = endpoint_output(stdout, code)
    except BaseException:
        report["kernel_audit_status"] = "INCONCLUSIVE: endpoint signature/axiom audit failed or interrupted"
        save()
        raise
    assert git("status", "--porcelain") == "", "Build modified upstream tracked sources"
    report["kernel_audit_status"] = "PASS: exact focused source closure and endpoint axioms"
    save()
    print(report["kernel_audit_status"], flush=True)
    print(report["point4_status"], flush=True)


if __name__ == "__main__":
    main()
