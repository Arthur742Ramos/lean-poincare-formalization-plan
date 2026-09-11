"""Check proof holes and the exact transitive axiom surface of selected results."""

from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECLARATIONS = [
    "EinsteinComparisonEntry.einsteinScalarComparisonAndSharpLifespan",
    "RicciScalarComparison.scalarCurvature_eq_quadraticScalarBarrier",
    "RicciScalarComparison.maximalEinsteinHomotheticIntrinsicSolution_timeSet",
    "RicciScalarComparison.no_riemannian_metric_agrees_at_extinction",
]


def reports(output: str) -> dict[str, set[str]]:
    pattern = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.DOTALL)
    return {
        name: {item.strip() for item in body.replace("\n", " ").split(",") if item.strip()}
        for name, body in pattern.findall(output)
    }


def run(source: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", "--stdin"], cwd=ROOT, input=source,
        text=True, capture_output=True,
    )


def main() -> None:
    source = "import Solution\n" + "\n".join(
        f"#print axioms {name}" for name in DECLARATIONS
    ) + "\n"
    result = run(source)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    found = reports(result.stdout + result.stderr)
    if set(found) != set(DECLARATIONS):
        raise SystemExit("axiom audit did not report every selected declaration")
    for name, axioms in found.items():
        if axioms != ALLOWED:
            raise SystemExit(f"unexpected axiom surface for {name}: {sorted(axioms)}")

    control = run(
        "axiom RicciScalarForbidden : False\n"
        "theorem RicciScalarNegativeControl : True := False.elim RicciScalarForbidden\n"
        "#print axioms RicciScalarNegativeControl\n"
    )
    control_found = reports(control.stdout + control.stderr)
    if control.returncode or control_found.get("RicciScalarNegativeControl") != {"RicciScalarForbidden"}:
        raise SystemExit("axiom negative control failed:\n" + control.stdout + control.stderr)
    print("Selected theorem and three principal results use exactly the permitted axioms; negative control passed.")


if __name__ == "__main__":
    main()
