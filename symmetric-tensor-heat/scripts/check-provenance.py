"""Verify the immutable same-repository source reused by this entry."""

from pathlib import Path
import hashlib
import subprocess


PACKAGE = Path(__file__).resolve().parents[1]
REPO = PACKAGE.parent
BASE = "13fa15d6a8352ed08bf71b3533b1c2e922c21388"
TREE = "255c32fa869ec955e7c09b21fb74914b9ce13ec7"
SOURCE = Path("curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/") / \
    "TensorHeatAtlasSymmetricWellPosedness.lean"
SOURCE_SHA256 = "beadeb28c37b72ffc0700756ba506e213f97c351fb1ee3125de41667314012a7"
VENDOR = PACKAGE / "vendor/curvature"
VENDORED_PATHS = (
    "PoincareCurvature",
    "PoincareCurvature.lean",
    "README.md",
    "AGENT-CONTRIBUTION.md",
    "AGENT-CONTRIBUTION-02.md",
    "AGENT-CONTRIBUTION-03.md",
    "AGENT-CONTRIBUTION-04.md",
    "AGENT-CONTRIBUTION-05.md",
    "lake-manifest.json",
    "lean-toolchain",
)


def run(*args: str) -> str:
    return subprocess.check_output(args, cwd=REPO, text=True).strip()


def git_bytes(object_name: str) -> bytes:
    return subprocess.check_output(["git", "show", object_name], cwd=REPO)


def main() -> None:
    if run("git", "rev-parse", f"{BASE}:curvature") != TREE:
        raise SystemExit("recorded baseline curvature tree is incorrect")
    # The main curvature subproject continues to evolve. This entry vendors an
    # immutable snapshot, so validate against that commit rather than HEAD.
    digest = hashlib.sha256(git_bytes(f"{BASE}:{SOURCE.as_posix()}")).hexdigest()
    if digest != SOURCE_SHA256:
        raise SystemExit("selected inherited theorem source hash changed")
    expected = set(run(
        "git", "ls-tree", "-r", "--name-only", f"{BASE}:curvature", "--",
        *VENDORED_PATHS,
    ).splitlines())
    actual = {
        path.relative_to(VENDOR).as_posix()
        for path in VENDOR.rglob("*")
        if path.is_file() and ".lake" not in path.relative_to(VENDOR).parts
    }
    generated = {"LICENSE"}
    if actual != expected | generated:
        missing = sorted((expected | generated) - actual)
        extra = sorted(actual - (expected | generated))
        raise SystemExit(f"vendored inventory mismatch; missing={missing}, extra={extra}")
    # Compare committed blobs. Git may materialize CRLF worktree files on
    # Windows even when the immutable source and vendor blobs are identical.
    subprocess.check_call(
        ["git", "diff", "--quiet", "HEAD", "--", "symmetric-tensor-heat/vendor/curvature"],
        cwd=REPO,
    )
    for relative in sorted(expected):
        if git_bytes(f"HEAD:symmetric-tensor-heat/vendor/curvature/{relative}") != \
                git_bytes(f"{BASE}:curvature/{relative}"):
            raise SystemExit("vendored file differs from disclosed source: " + relative)
    if git_bytes("HEAD:symmetric-tensor-heat/vendor/curvature/LICENSE") != \
            git_bytes(f"{BASE}:LICENSE"):
        raise SystemExit("vendored repository license differs from disclosed source")
    metadata = (PACKAGE / "formalization.yaml").read_text(encoding="utf-8")
    for required in (BASE, SOURCE.as_posix(), "vendor/curvature", "relationship: \"builds-on\""):
        if required not in metadata:
            raise SystemExit("structured provenance is incomplete: " + required)
    print("Immutable source, exact vendored snapshot, notices, and structured provenance passed.")


if __name__ == "__main__":
    main()
