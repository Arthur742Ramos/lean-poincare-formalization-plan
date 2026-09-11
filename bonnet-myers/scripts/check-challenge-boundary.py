"""Compile Challenge with dependency libraries only, excluding local proofs."""

import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    lean = subprocess.check_output(
        ["lake", "env", "which", "lean"], cwd=ROOT, text=True
    ).strip()
    dependency_paths = sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    if not dependency_paths:
        raise SystemExit("dependency libraries missing; run lake exe cache get first")
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(str(path.resolve()) for path in dependency_paths)
    with tempfile.TemporaryDirectory(prefix="bonnet-myers-boundary-") as scratch:
        probe = subprocess.run(
            [lean, "--stdin"], cwd=scratch, env=environment, text=True,
            capture_output=True, input="import BonnetMyers.Statement\n"
        )
        combined = probe.stdout + probe.stderr
        if probe.returncode == 0 or "unknown module prefix 'BonnetMyers'" not in combined:
            raise SystemExit("boundary negative control failed: " + combined)
        subprocess.run(
            [lean, "-o", str(Path(scratch) / "Challenge.olean"), str(ROOT / "Challenge.lean")],
            cwd=ROOT, env=environment, check=True
        )
    print("Challenge compiles from the pinned dependency closure only; local-import negative control passed.")


if __name__ == "__main__":
    main()
