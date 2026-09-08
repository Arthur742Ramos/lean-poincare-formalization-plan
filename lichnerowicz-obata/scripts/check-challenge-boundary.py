"""Compile the Challenge with Mathlib dependencies only; reject local imports.

Adapts the boundary check from almost-schur at
3faf25aefc27842a77c37ca178e8a40a20bb20c7, adding both dependency and candidate
negative controls and compiling the exact source in an isolated directory.
"""

import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT, text=True).strip()
    paths = sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not paths:
        raise SystemExit("Mathlib dependency libraries missing; fetch the pinned cache first")
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(str(path.resolve()) for path in paths)
    with tempfile.TemporaryDirectory(prefix="lichnerowicz-challenge-boundary-") as temp:
        scratch = Path(temp)
        for module in ("AlmostSchur.AlmostSchurAlgebra", "LichnerowiczObata.LichnerowiczObata"):
            run = subprocess.run([lean, "--stdin"], cwd=scratch, env=environment,
                                 input="import " + module + "\n", text=True, capture_output=True)
            prefix = module.split(".")[0]
            if run.returncode == 0 or "unknown module prefix '" + prefix + "'" not in (
                    run.stdout + run.stderr):
                raise SystemExit("import negative control failed: " + run.stdout + run.stderr)
        source = (ROOT / "LichnerowiczObataChallenge.lean").read_bytes()
        candidate = scratch / "LichnerowiczObataChallenge.lean"
        candidate.write_bytes(source)
        subprocess.run([lean, "-o", str(scratch / "LichnerowiczObataChallenge.olean"), str(candidate)],
                       cwd=scratch, env=environment, check=True)
        if candidate.read_bytes() != source:
            raise SystemExit("independent source changed during verification")
    print("Mathlib-only Challenge passed; candidate and inherited-library imports both rejected.")


if __name__ == "__main__":
    main()
