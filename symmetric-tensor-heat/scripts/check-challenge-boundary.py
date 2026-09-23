"""Compile the Challenge from dependency artifacts only."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    # Windows Lake may report a Cygwin path that CreateProcess cannot open.
    lean = (shutil.which("lean") if os.name == "nt" else
            subprocess.check_output(
                ["lake", "env", "which", "lean"], cwd=ROOT, text=True
            ).strip())
    if not lean:
        raise SystemExit("Lean executable not found")
    paths = sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not paths:
        raise SystemExit("dependency libraries missing; run lake exe cache get")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path.resolve()) for path in paths)
    env["ELAN_TOOLCHAIN"] = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    with tempfile.TemporaryDirectory(prefix="tensor-heat-boundary-") as scratch:
        negative = subprocess.run(
            [lean, "--stdin"], cwd=scratch, env=env, text=True,
            capture_output=True,
            input=("import PoincareCurvature.Geometry.Manifold.RicciFlow."
                   "AnalyticPDE.TensorHeatAtlasSymmetricWellPosedness\n"),
        )
        combined = negative.stdout + negative.stderr
        if negative.returncode == 0 or "unknown module prefix 'PoincareCurvature'" not in combined:
            raise SystemExit("local-import negative control failed:\n" + combined)
        subprocess.run(
            [lean, "-o", str(Path(scratch) / "TensorHeatChallenge.olean"),
             str(ROOT / "TensorHeatChallenge.lean")],
            cwd=ROOT, env=env, check=True,
        )
    print("Challenge compiles from pinned dependencies only; negative control passed.")


if __name__ == "__main__":
    main()
