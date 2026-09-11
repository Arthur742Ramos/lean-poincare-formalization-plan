"""Audit every active project declaration through Lean's transitive axiom collector."""

from pathlib import Path
import json
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SELECTED = {
    "BonnetMyersEntry.completeStatement",
    "BonnetMyersEntry.bonnetMyers_metric_conclusion",
    "BonnetMyersEntry.completeStatement_proved",
    "BonnetMyersEntry.bonnet_myers",
}
FIXTURE = "BonnetMyersEntry.AxiomFixture"


def audit_command(selected: set[str]) -> str:
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
        mod == `Solution || mod == `BonnetMyers || mod.toString.startsWith "BonnetMyers."
          || mod.toString.startsWith "PoincareCurvature."
      | none => name.toString.startsWith "BonnetMyersEntry."
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


def selected_audit_command(selected: set[str]) -> str:
    """Audit named fixtures without rescanning Mathlib's complete environment."""
    names = ", ".join(json.dumps(name) for name in sorted(selected))
    return r'''
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let selected : List String := [SELECTED_NAMES]
  for name in selected do
    unless env.constants.contains name.toName do
      throwError "missing selected declaration: {name}"
    let axioms ← Lean.collectAxioms name.toName
    let report := Json.mkObj [
      ("name", toJson name),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"AXIOM_REPORT {report.compress}"
'''.replace("SELECTED_NAMES", names)


def parse_reports(output: str) -> dict[str, set[str]]:
    reports = {}
    for line in output.splitlines():
        if "AXIOM_REPORT " not in line:
            continue
        report = json.loads(line.split("AXIOM_REPORT ", 1)[1])
        name = report["name"]
        if name in reports:
            raise ValueError("duplicate declaration report: " + name)
        reports[name] = set(report["axioms"])
    return reports


def validate(output: str, selected: set[str]) -> int:
    reports = parse_reports(output)
    for name, axioms in reports.items():
        if not axioms <= ALLOWED:
            raise ValueError("unapproved axioms for " + name + ": " + str(sorted(axioms)))
    if not reports or not selected <= set(reports):
        raise ValueError("missing selected declarations or empty compiler inventory")
    return len(reports)


def run_lean(source: str, directory: str, name: str) -> subprocess.CompletedProcess[str]:
    path = Path(directory) / (name + ".lean")
    path.write_text(source, encoding="utf-8")
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )


def main() -> None:
    modules = [".".join(path.relative_to(ROOT).with_suffix("").parts)
               for path in sorted((ROOT / "BonnetMyers").rglob("*.lean"))]
    modules += [".".join(path.relative_to(ROOT / "vendor/curvature").with_suffix("").parts)
                for path in sorted((ROOT / "vendor/curvature/PoincareCurvature").rglob("*.lean"))]
    with tempfile.TemporaryDirectory(prefix="bonnet-myers-axioms-") as directory:
        source = "\n".join("import " + module for module in modules)
        source += "\nimport Solution\n" + audit_command(SELECTED)
        result = run_lean(source, directory, "AllCandidateAxioms")
        if result.returncode:
            raise SystemExit(result.stdout)
        count = validate(result.stdout, SELECTED)

        controls = {
            FIXTURE + "Hole": "theorem " + FIXTURE + "Hole : True := by sorry\n",
            FIXTURE + "Custom": "axiom " + FIXTURE + "Custom : True\n",
            FIXTURE + "Native":
                "theorem " + FIXTURE + "Native : True := by native_decide\n",
        }
        control = run_lean(
            "import Mathlib.Tactic\n" + "".join(controls.values())
            + selected_audit_command(set(controls)), directory, "RejectedAxioms"
        )
        if control.returncode:
            raise SystemExit("axiom negative controls failed to execute:\n" + control.stdout)
        control_reports = parse_reports(control.stdout)
        if set(control_reports) != set(controls):
            raise SystemExit("axiom negative controls did not report every fixture")
        for name, axioms in control_reports.items():
            if axioms <= ALLOWED:
                raise SystemExit("negative control was incorrectly accepted: " + name)

        missing = FIXTURE + "Missing"
        missing_control = run_lean(
            "import Lean\n" + selected_audit_command({missing}), directory, "Missing"
        )
        if (missing_control.returncode == 0
                or "missing selected declaration" not in missing_control.stdout):
            raise SystemExit("missing-declaration negative control failed:\n" + missing_control.stdout)
    print(f"Checked {count} compiler-inventoried active declarations; selected results covered; four Lean negative controls rejected.")


if __name__ == "__main__":
    main()
