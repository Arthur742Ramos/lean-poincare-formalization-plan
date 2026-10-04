#!/usr/bin/env python3
"""Rebuild the exact upstream Ricci-flow endpoint closure, then audit axioms.

This script does not vendor upstream proofs or certify a bridge to Point 4.
The immutable source must already be checked out in a separate directory.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tomllib

SOURCE_SHA = "8bd406e35c33a200e9b88895cf11ee8429194e15"
MATHLIB_SHA = "8a178386ffc0f5fef0b77738bb5449d50efeea95"
TARGETS = {
    "DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence":
        "DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence",
    "DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Construction":
        "DifferentialGeometry.PDE.RicciFlow.ricci_flow_forward_unique",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--plan-only", action="store_true")
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
    assert (root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.29.0"
    config = tomllib.loads((root / "lakefile.toml").read_text())
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
    output = root.parent / "hamilton-release-audit"
    output.mkdir(exist_ok=True)
    report = {
        "source_sha": SOURCE_SHA,
        "mathlib_sha": MATHLIB_SHA,
        "targets": TARGETS,
        "source_closure_modules": len(order),
        "source_closure_bytes": sum((root / (m.replace('.', '/') + '.lean')).stat().st_size for m in order),
        "source_findings": findings,
        "execution_or_trust_findings": execution_findings,
        "graph": graph,
        "build_order": order,
        "built": [],
        "kernel_audit_status": "NOT RUN",
        "point4_status": "OPEN: no semantic bridge constructed",
    }
    report_path = output / "report.json"

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + "\n")

    save()
    print(f"Focused upstream source closure: {len(order)} modules", flush=True)
    assert not findings, "Proof-placeholder/axiom findings: " + "; ".join(findings)
    assert not execution_findings, "Manual execution/trust review required: " + "; ".join(execution_findings)
    if args.plan_only:
        return
    # The immutable release intentionally does not track a Lake manifest.
    # Check its tagged configuration before setup and the actual resolved
    # immutable revision after Lean action has generated the local manifest.
    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == MATHLIB_SHA, "Wrong resolved Mathlib pin"
    resolved = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/mathlib", text=True).strip()
    assert resolved == MATHLIB_SHA, "Resolved Mathlib checkout disagrees with manifest"

    # Build the import DAG in topological order to avoid launching the entire
    # large upstream project concurrently on a standard hosted runner. Only
    # Mathlib uses its official cache; all upstream modules compile from source.
    for position, module in enumerate(order, 1):
        free = shutil.disk_usage(root).free
        if free < 1024 ** 3:
            report["kernel_audit_status"] = "BLOCKED: less than 1 GiB free on hosted runner"
            save()
            raise SystemExit(report["kernel_audit_status"])
        print(f"[{position}/{len(order)}] {module}", flush=True)
        result = subprocess.run(["lake", "--no-cache", "build", module + ":olean"], cwd=root)
        if result.returncode:
            report["kernel_audit_status"] = "BUILD FAILED"
            report["failed_module"] = module
            save()
            raise SystemExit(result.returncode)
        report["built"].append(module)
        save()

    probe = output / "endpoint-probe.lean"
    probe.write_text("\n".join(
        ["import " + m for m in TARGETS] +
        [command + theorem for theorem in TARGETS.values()
         for command in ("#check @", "#print axioms ")] + [""]))
    result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "endpoint-probe.log").write_text(result.stdout)
    print(result.stdout, flush=True)
    assert result.returncode == 0, "Endpoint signature/axiom probe failed"
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", result.stdout)
    assert {name for name, _ in entries} | set(clean) == set(TARGETS.values()), entries
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, axioms in entries:
        actual = {a.strip() for a in axioms.split(",") if a.strip()}
        assert actual <= allowed, (name, actual)
    assert git("status", "--porcelain") == "", "Build modified upstream tracked sources"
    report["kernel_audit_status"] = "PASS: exact focused source closure and endpoint axioms"
    save()
    print(report["kernel_audit_status"], flush=True)
    print(report["point4_status"], flush=True)


if __name__ == "__main__":
    main()
