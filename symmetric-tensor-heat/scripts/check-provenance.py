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
    return subprocess.check_output(["git", "cat-file", "blob", object_name], cwd=REPO)


def tree_blobs(tree: str) -> dict[str, str]:
    result = {}
    for line in run("git", "ls-tree", "-r", tree).splitlines():
        header, path = line.split("\t", 1)
        _, kind, object_id = header.split()
        if kind != "blob":
            raise SystemExit("non-blob source in disclosed tree: " + path)
        result[path] = object_id
    return result


def main() -> None:
    if run("git", "rev-parse", f"{BASE}:curvature") != TREE:
        raise SystemExit("recorded baseline curvature tree is incorrect")
    source_blobs = tree_blobs(f"{BASE}:curvature")
    vendor_blobs = tree_blobs("HEAD:symmetric-tensor-heat/vendor/curvature")
    # The main curvature subproject continues to evolve. This entry vendors an
    # immutable snapshot, so validate against that commit rather than HEAD.
    source_relative = SOURCE.relative_to("curvature").as_posix()
    digest = hashlib.sha256(git_bytes(source_blobs[source_relative])).hexdigest()
    if digest != SOURCE_SHA256:
        raise SystemExit("selected inherited theorem source hash changed")
    expected = {
        path for path in source_blobs
        if any(path == item or path.startswith(item + "/") for item in VENDORED_PATHS)
    }
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
        if vendor_blobs.get(relative) != source_blobs[relative]:
            raise SystemExit("vendored file differs from disclosed source: " + relative)
    if vendor_blobs.get("LICENSE") != run("git", "rev-parse", f"{BASE}:LICENSE"):
        raise SystemExit("vendored repository license differs from disclosed source")
    metadata = git_bytes("HEAD:symmetric-tensor-heat/formalization.yaml").decode("utf-8")
    for required in (BASE, SOURCE.as_posix(), "vendor/curvature", "relationship: \"builds-on\""):
        if required not in metadata:
            raise SystemExit("structured provenance is incomplete: " + required)
    print("Immutable source, exact vendored snapshot, notices, and structured provenance passed.")


if __name__ == "__main__":
    main()
