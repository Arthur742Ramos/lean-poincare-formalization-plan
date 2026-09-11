"""Compile Challenge from dependencies only and reject candidate-local imports."""

import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    lean = subprocess.check_output(
        ["lake", "env", "which", "lean"], cwd=ROOT, text=True
    ).strip()
    paths = sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not paths:
        raise SystemExit("dependency libraries missing; run lake exe cache get first")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path.resolve()) for path in paths)
    with tempfile.TemporaryDirectory(prefix="ricci-scalar-boundary-") as scratch:
        probe = subprocess.run(
            [lean, "--stdin"], cwd=scratch, env=env, text=True,
            capture_output=True,
            input=("import PoincareCurvature.Geometry.Manifold.RicciFlow."
                   "LocalExistence.Einstein\n"),
        )
        combined = probe.stdout + probe.stderr
        if probe.returncode == 0 or "unknown module prefix 'PoincareCurvature'" not in combined:
            raise SystemExit("boundary negative control failed: " + combined)
        subprocess.run(
            [lean, "-o", str(Path(scratch) / "Challenge.olean"),
             str(ROOT / "Challenge.lean")],
            cwd=ROOT, env=env, check=True,
        )
    print("Challenge compiles from the pinned dependency closure only; local-import negative control passed.")


if __name__ == "__main__":
    main()
