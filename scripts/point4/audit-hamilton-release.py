#!/usr/bin/env python3
"""Rebuild the exact upstream Ricci-flow endpoint closure, then audit axioms.

This script does not vendor upstream proofs or certify a bridge to Point 4.
The immutable source must already be checked out in a separate directory.
"""
from __future__ import annotations

import argparse
import concurrent.futures
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
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_GITHASH", "LAKE_CACHE_KEY"):
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
                assert hashlib.sha256((output / "module-build-logs" / f"{position:04d}.{stream}.log").read_bytes()).hexdigest() == value[f"{stream}_sha256"], "Compiler log hash mismatch"
            setup_bytes = gzip.decompress((output / "module-setups" / f"{position:04d}.json.gz").read_bytes())
            assert hashlib.sha256(setup_bytes).hexdigest() == value["setup_sha256"], "Lake setup evidence mismatch"
    return records


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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--plan-only", action="store_true")
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

    # One official Lake plan per bounded direct-import-chain batch. The audit
    # observer retains actual compiler exits and performs resource checks at
    # every compiler launch, rather than deriving exits from a batch result.
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
                  build_mode="official Lake bounded-chain batches with real compiler observation",
                  compiler_results={}, batch_plan=batches, batch_results=[],
                  project_artifact_cache_enabled=False)
    for name in ("module-build-logs", "compiler-records", "module-setups", "batch-build-logs"):
        directory = output / name
        directory.mkdir(exist_ok=True)
        assert not list(directory.iterdir()), "Audit evidence directory is not fresh: " + name
    # Resolve the real compiler through the original pinned Lake environment.
    # Metadata queries are forwarded to this exact binary by the shim.
    environment = subprocess.check_output(["lake", "env"], cwd=root, text=True)
    original_env = dict(line.split("=", 1) for line in environment.splitlines() if "=" in line)
    sysroot = pathlib.Path(original_env["LEAN_SYSROOT"]).resolve()
    compiler = sysroot / "bin/lean"
    version = subprocess.check_output([str(compiler), "--version"], cwd=root, text=True).strip()
    assert re.search(r"Lean \(version 4\.29\.0(?:,|\))", version), version
    report.update(compiler_version=version, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                  original_lean_sysroot=str(sysroot))
    modules = {m: {"position": positions[m], "source_sha256": report["source_sha256"][m],
                   "project_imports": graph[m]} for m in order}
    control = {"root": str(root), "evidence": str(output), "sysroot": str(sysroot),
               "compiler": str(compiler), "compiler_sha256": report["compiler_sha256"],
               "jobs": jobs, "modules": modules, "allowed_modules": []}
    control_path = output / "compiler-control.json"
    control_path.write_text(json.dumps(control, indent=2) + "\n")
    observer = pathlib.Path(__file__).with_name("observe-hamilton-compiler.py")
    env = make_compiler_shim(output, sysroot, observer, control_path)
    # This second assertion is immediately before the first compilation, after
    # official dependency-cache retrieval and all audit plumbing setup.
    assert_no_project_objects(root)
    save()

    record_mtimes = {}

    def refresh():
        changed = False
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
        save()

    try:
        for index, batch in enumerate(batches, 1):
            assert all(set(graph[m]) <= set(report["built"]) | set(batch["modules"])
                       for m in batch["modules"])
            control["allowed_modules"] = batch["modules"]
            control_path.write_text(json.dumps(control, indent=2) + "\n")
            command = ["lake", "--no-cache", "--no-ansi", "--verbose", "build",
                       *["+" + m + ":olean" for m in batch["modules"]]]
            started = time.monotonic()
            print(f"BATCH {index}/{len(batches)} START ({len(batch['modules'])} source modules)", flush=True)
            path = output / "batch-build-logs" / f"{index:04d}.log"
            with path.open("w") as stream:
                process = subprocess.Popen(command, cwd=root, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    while process.poll() is None:
                        time.sleep(2)
                        refresh()
                finally:
                    if process.poll() is None:
                        # Evidence/resource exceptions must not leave detached
                        # Lake or real compiler processes consuming the runner.
                        os.killpg(process.pid, signal.SIGTERM)
                        try:
                            process.wait(timeout=30)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait()
            code = process.returncode
            refresh()
            report["batch_results"].append({"batch": index, "command": command, "exit_code": code,
                                            "elapsed_seconds": time.monotonic() - started})
            print(path.read_text(), end="", flush=True)
            print(f"BATCH {index}/{len(batches)} EXIT {code}; {len(report['built'])}/{len(order)} actual source compiler successes", flush=True)
            if code != 0:
                report["kernel_audit_status"] = "BUILD FAILED: batch or real compiler/observer failure"
                save()
                raise SystemExit(code if code > 0 else 1)
            assert all(m in report["built"] for m in batch["modules"]), "Batch success without every real compiler success"
            assert not (output / "compiler-stop.json").exists(), "Compiler observer failed"
            save()
        compiler_records(output, modules, required=True)
        assert report["built"] == order, "Incomplete source closure"
        for m in order:
            assert hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest() == report["source_sha256"][m]
            result = report["compiler_results"][m]
            assert hashlib.sha256((root / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest() == result["source_sha256"]
            assert hashlib.sha256((root / (".lake/build/lib/lean/" + m.replace('.', '/') + '.olean')).read_bytes()).hexdigest() == result["olean_sha256"]
    except BaseException:
        if report["kernel_audit_status"].startswith("RUNNING"):
            report["kernel_audit_status"] = "INCONCLUSIVE: interrupted, resource, or evidence failure"
        save()
        raise

    report["kernel_audit_status"] = "RUNNING: source closure complete, endpoint audit pending"
    save()
    probe = output / "endpoint-probe.lean"
    probe.write_text("\n".join(
        ["import " + m for m in TARGETS] +
        [command + theorem for theorem in TARGETS.values()
         for command in ("#check @", "#print axioms ")] + [""]))
    try:
        command = ["lake", "env", "lean", str(probe)]
        result = subprocess.run(command, cwd=root,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / "endpoint-probe.log").write_text(result.stdout)
        print(result.stdout, flush=True)
        report["endpoint_probe_result"] = {"command": command, "exit_code": result.returncode,
                                            "log_sha256": hashlib.sha256(result.stdout.encode()).hexdigest()}
        report["endpoint_axioms"] = endpoint_output(result.stdout, result.returncode)
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
