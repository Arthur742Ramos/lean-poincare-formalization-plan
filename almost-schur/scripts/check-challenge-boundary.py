"""Compile Challenge with the pinned dependency closure only."""

import os
from pathlib import Path
import subprocess
import tempfile


PROJECT = Path(__file__).resolve().parents[1]


def main():
    lean = subprocess.check_output(
        ["lake", "env", "which", "lean"], cwd=PROJECT, text=True
    ).strip()
    dependency_paths = sorted(
        (PROJECT / ".lake/packages").glob("*/.lake/build/lib/lean")
    )
    if not dependency_paths:
        raise SystemExit("dependency libraries missing; run lake exe cache get first")
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(
        str(path.resolve()) for path in dependency_paths
    )
    with tempfile.TemporaryDirectory(prefix="almost-schur-boundary-") as scratch:
        probe = subprocess.run(
            [lean, "--stdin"],
            cwd=scratch,
            env=environment,
            text=True,
            capture_output=True,
            input="import AlmostSchur.AlmostSchurAlgebra\n",
        )
        if probe.returncode == 0 or "unknown module prefix 'AlmostSchur'" not in (
            probe.stdout + probe.stderr
        ):
            raise SystemExit(
                "boundary negative control failed: " + probe.stdout + probe.stderr
            )
        subprocess.run(
            [lean, "-o", str(Path(scratch) / "Challenge.olean"), str(PROJECT / "Challenge.lean")],
            cwd=PROJECT,
            env=environment,
            check=True,
        )
    print("Challenge compiles with dependency libraries only; local import negative control passed.")


if __name__ == "__main__":
    main()
