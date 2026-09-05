"""Compile Challenge with dependency libraries only, excluding candidate build products."""
import os
from pathlib import Path
import subprocess
import tempfile

project = Path(__file__).resolve().parents[1]
lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=project, text=True).strip()
paths = sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean"))
if not paths:
    raise SystemExit("Dependency libraries missing: run lake exe cache get first")
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in paths)
with tempfile.TemporaryDirectory(prefix="contracted-bianchi-boundary-") as scratch:
    # Negative control: the proof-only local library must be inaccessible.
    probe = subprocess.run(
        [lean, "--stdin"], cwd=scratch, env=env, text=True, capture_output=True,
        input="import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along\n",
    )
    if probe.returncode == 0 or "unknown module prefix 'PoincareCurvature'" not in probe.stdout + probe.stderr:
        raise SystemExit("Boundary negative control failed: " + probe.stdout + probe.stderr)
    subprocess.run(
        [lean, "-o", str(Path(scratch) / "Challenge.olean"), str(project / "Challenge.lean")],
        cwd=project, env=env, check=True,
    )
print("Challenge compiles with dependency libraries only; local import negative control passed.")
