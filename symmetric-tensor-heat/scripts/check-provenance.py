"""Verify the immutable same-repository source reused by this entry."""

from pathlib import Path
import hashlib
import subprocess


PACKAGE = Path(__file__).resolve().parents[1]
REPO = PACKAGE.parent
BASE = "d6ef7f253bb95fa44d1fe61c9b1a52e061ca0951"
TREE = "a448a1d7d62c04a5ab85ba0d943b67db293e77c2"
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
    if subprocess.run(
        ["git", "diff", "--quiet", BASE, "--", "curvature"], cwd=REPO
    ).returncode:
        raise SystemExit("current curvature tree differs from the disclosed baseline")
    digest = hashlib.sha256((REPO / SOURCE).read_bytes()).hexdigest()
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
    for relative in sorted(expected):
        if (VENDOR / relative).read_bytes() != git_bytes(f"{BASE}:curvature/{relative}"):
            raise SystemExit("vendored file differs from disclosed source: " + relative)
    if (VENDOR / "LICENSE").read_bytes() != git_bytes(f"{BASE}:LICENSE"):
        raise SystemExit("vendored repository license differs from disclosed source")
    metadata = (PACKAGE / "formalization.yaml").read_text(encoding="utf-8")
    for required in (BASE, str(SOURCE), "vendor/curvature", "relationship: \"builds-on\""):
        if required not in metadata:
            raise SystemExit("structured provenance is incomplete: " + required)
    print("Immutable source, exact vendored snapshot, notices, and structured provenance passed.")


if __name__ == "__main__":
    main()
