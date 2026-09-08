"""Audit the compiler's complete candidate constant inventory, not a regex sample.

All implementation modules are imported, including modules not needed by the
selected theorem. Lean assigns declarations to their defining modules and
collects each transitive axiom closure. Private/generated constants present
in the imported environment are included. Actual Lean negative controls test
proof holes, custom axioms, native reduction, and missing declarations.
"""

import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FIXTURE = "LichnerowiczObata.AxiomFixture"


def without_comments(source):
    # Nested Lean block comments, plus line comments; preserve newlines.
    result, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif depth:
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                result.append(" ")
                i += 1
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed Lean comment")
    return "".join(result)


def audit_command(selected):
    names = ", ".join(json.dumps(name) for name in sorted(selected))
    return r'''
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let mod := moduleNames[idx.toNat]!
        mod.toString.startsWith "LichnerowiczObata." || mod == `LichnerowiczObataSolution
          || mod == `AlmostSchur || mod.toString.startsWith "AlmostSchur."
          || mod.toString.startsWith "RellichKondrachov."
      | none => name.toString.startsWith "LichnerowiczObata."
    if owned then some name else none
  let selected : List String := [SELECTED_NAMES]
  for name in selected do
    unless candidates.contains name.toName do
      throwError "missing selected declaration: {name}"
  if candidates.isEmpty then throwError "empty candidate inventory"
  for name in candidates do
    let axioms ← Lean.collectAxioms name
    let report := Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"AXIOM_REPORT {report.compress}"
'''.replace("SELECTED_NAMES", names)


def validate(output, selected):
    reports = {}
    for line in output.splitlines():
        if "AXIOM_REPORT " not in line:
            continue
        report = json.loads(line.split("AXIOM_REPORT ", 1)[1])
        name = report["name"]
        if name in reports:
            raise ValueError("duplicate constant report: " + name)
        axioms = set(report["axioms"])
        if not axioms <= ALLOWED:
            raise ValueError("unapproved transitive axioms for " + name + ": " + str(sorted(axioms)))
        reports[name] = axioms
    if not reports or not selected <= set(reports):
        raise ValueError("missing selected declarations or empty audit")
    return len(reports)


def run_lean(source, temp, name):
    path = Path(temp) / (name + ".lean")
    path.write_text(source, encoding="utf-8")
    return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    files = sorted((ROOT / "LichnerowiczObata").rglob("*.lean"))
    vendor_root = ROOT / "vendor/almost-schur"
    vendor_files = sorted(vendor_root.rglob("*.lean"))
    if not files:
        raise SystemExit("no implementation sources")
    for path in [*files, *vendor_files, ROOT / "LichnerowiczObataSolution.lean"]:
        if re.search(r"\b(sorry|admit|axiom)\b", without_comments(path.read_text())):
            raise SystemExit("proof-hole token outside comments in " + str(path))
    modules = [".".join(path.relative_to(ROOT).with_suffix("").parts) for path in files]
    modules += [".".join(path.relative_to(vendor_root).with_suffix("").parts)
                for path in vendor_files]
    config = json.loads((ROOT / "comparator.json").read_text())
    selected = set(config["theorem_names"]) | set(config["definition_names"])
    with tempfile.TemporaryDirectory(prefix="lichnerowicz-full-axioms-") as temp:
        source = "\n".join("import " + module for module in modules)
        source += "\nimport LichnerowiczObataSolution\n" + audit_command(selected)
        run = run_lean(source, temp, "AllCandidateAxioms")
        if run.returncode:
            raise SystemExit(run.stdout)
        count = validate(run.stdout, selected)
        controls = {
            "Hole": "theorem " + FIXTURE + " : True := by sorry\n",
            "Custom": "axiom " + FIXTURE + " : True\n",
            "Native": "theorem " + FIXTURE + " : True := by native_decide\n",
            "Missing": "",
        }
        for name, fixture in controls.items():
            result = run_lean("import Mathlib\n" + fixture + audit_command({FIXTURE}), temp, name)
            if result.returncode:
                if name != "Missing" or "missing selected declaration" not in result.stdout:
                    raise SystemExit("negative control failed to execute: " + name + "\n" + result.stdout)
                continue
            try:
                validate(result.stdout, {FIXTURE})
            except ValueError:
                continue
            raise SystemExit("negative control was incorrectly accepted: " + name)
    print(f"Checked {count} compiler-inventoried constants from {len(modules)} implementation modules "
          "plus the Solution; all ten Comparator selections covered; four actual Lean negative "
          "controls rejected.")


if __name__ == "__main__":
    main()
