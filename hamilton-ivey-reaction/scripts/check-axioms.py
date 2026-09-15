"""Check the selected theorem's transitive axiom surface."""

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
THEOREM = "HamiltonIveyChallenge.hamiltonIveyODEPinching"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(source: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT,
        input=source,
        text=True,
        capture_output=True,
    )


def reported(output: str, name: str) -> set[str]:
    match = re.search(
        rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]",
        output,
        re.DOTALL,
    )
    if not match:
        raise SystemExit("axiom report missing for " + name + "\n" + output)
    return {
        item.strip()
        for item in match.group(1).replace("\n", " ").split(",")
        if item.strip()
    }


def main() -> None:
    result = run(f"import Solution\n#print axioms {THEOREM}\n")
    output = result.stdout + result.stderr
    if result.returncode or reported(output, THEOREM) != ALLOWED:
        raise SystemExit("unexpected selected-theorem axiom surface:\n" + output)

    control_name = "HamiltonIveyForbiddenControl"
    control = run(
        "axiom HamiltonIveyForbidden : False\n"
        f"theorem {control_name} : True := False.elim HamiltonIveyForbidden\n"
        f"#print axioms {control_name}\n"
    )
    control_output = control.stdout + control.stderr
    if control.returncode or reported(control_output, control_name) != {"HamiltonIveyForbidden"}:
        raise SystemExit("axiom negative control failed:\n" + control_output)
    print("Selected theorem uses exactly the permitted axioms; negative control passed.")


if __name__ == "__main__":
    main()
