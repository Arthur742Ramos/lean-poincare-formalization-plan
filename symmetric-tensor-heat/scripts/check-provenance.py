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
ADAPTED_SHA256 = {
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/HeatKernel1D.lean":
        "824990b4aad942a6f28214d8bc7fd6acb8db85d7921b7a6f861218344ec15246",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/CompactCoefficientExtension.lean":
        "8e42658d1e53ce7c43afca1f667bc9b34a1685b343d4cd50f674bc8330fa9c92",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/NormalizedCutoff.lean":
        "8bdc17251cd27da4f63c357947a65b88b4c27f1c2c5f62ea7c669be7f5e40283",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean":
        "7390d0367bd2b62c849ad473158111ca863828dcb7925e212b9a015b68c0d1d2",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatEuclidean.lean":
        "d3e8684dbfc312d9dfc30b4f47a289589cc12e8fee3e049515f569a14551e637",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean":
        "21d6c184331d870d9fdf7666961258a833080ba9b89d645622be47c1f70a912a",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianChart.lean":
        "3db9f52f16ff40d4262534777f0efc197e03761e5f4ccf82259cabd1fb000033",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/ConnectionLaplacianCoordinate.lean":
        "55446fd439b84183d8f7190edc6fba6b42c2bb430cffcc53650fd3dca7345ac9",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean":
        "626c9efc0ce0563ef8a6576ec0e3a332eb42c1e2d12614272f54fc7f558510ea",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/EndomorphismTrace.lean":
        "647ae886731f58c6c3d3bb6f6806db7c4b8c6defe8167c11b9e8508a950ce434",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean":
        "f7f1477993f745a5901f23340c0602ec659240c7c4a8beabec8ff16db6b6e936",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/FiniteCylinderInterpolation.lean":
        "7f86ecba272aae7e510e66c7101c8a7357a642e749cb6faa85d6cdeba3aee9a7",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/BanachSpace.lean":
        "425d1d2e93476279bfe4ebea9f65ca30d19c7301aa08b53e3e58820b81e0337d",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean":
        "39d79d7bbeb76e6a67510c2698bcb620160e9b283337302e1d8476ff0b0a8d5a",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TensorDivergence.lean":
        "29a4de07240b29e134f3a96570f7bf8ee442c329980a56304fb333f8dbefb3a8",
}
ADDED_ADAPTATION_SHA256 = {
    "PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSectionCore.lean":
        "b03b85f2d006bcea39026c301d9559c242c2aa5718175e1b1b2c9e24be621ed0",
}


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
    added_adaptations = set(ADDED_ADAPTATION_SHA256)
    if actual != expected | generated | added_adaptations:
        missing = sorted((expected | generated | added_adaptations) - actual)
        extra = sorted(actual - (expected | generated | added_adaptations))
        raise SystemExit(f"vendored inventory mismatch; missing={missing}, extra={extra}")
    # Compare committed blobs. Git may materialize CRLF worktree files on
    # Windows even when the immutable source and vendor blobs are identical.
    subprocess.check_call(
        ["git", "diff", "--quiet", "HEAD", "--", "symmetric-tensor-heat/vendor/curvature"],
        cwd=REPO,
    )
    if not set(ADAPTED_SHA256) <= expected:
        raise SystemExit("adapted file is absent from the disclosed source inventory")
    if set(ADDED_ADAPTATION_SHA256) & expected:
        raise SystemExit("added adaptation unexpectedly exists in the source inventory")
    for relative in sorted(expected):
        vendor_oid = vendor_blobs.get(relative)
        if relative in ADAPTED_SHA256:
            if vendor_oid == source_blobs[relative]:
                raise SystemExit("stale adaptation entry: " + relative)
            digest = hashlib.sha256(git_bytes(vendor_oid)).hexdigest()
            if digest != ADAPTED_SHA256[relative]:
                raise SystemExit("adapted vendored file hash changed: " + relative)
        elif vendor_oid != source_blobs[relative]:
            raise SystemExit("vendored file differs from disclosed source: " + relative)
    for relative, expected_hash in ADDED_ADAPTATION_SHA256.items():
        vendor_oid = vendor_blobs.get(relative)
        if vendor_oid is None:
            raise SystemExit("missing added source-derived adaptation: " + relative)
        digest = hashlib.sha256(git_bytes(vendor_oid)).hexdigest()
        if digest != expected_hash:
            raise SystemExit("added adaptation hash changed: " + relative)
        source_section = git_bytes(source_blobs[
            "PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean"
        ]).decode("utf-8")
        core_section = git_bytes(vendor_oid).decode("utf-8")
        for declaration in (
            "instNormedAddCommGroupTangentSpace",
            "instNormedSpaceTangentSpace",
            "instIsTopologicalAddGroupTangentSpace",
            "instT2SpaceTangentSpace",
            "ContMDiffRiemannianMetric.ext",
            "BilinearFormBundle",
            "trivializationAt_bilinearFormBundle_apply_eq",
        ):
            if declaration not in source_section or declaration not in core_section:
                raise SystemExit("source-derived core declaration missing: " + declaration)
    if vendor_blobs.get("LICENSE") != run("git", "rev-parse", f"{BASE}:LICENSE"):
        raise SystemExit("vendored repository license differs from disclosed source")
    metadata = git_bytes("HEAD:symmetric-tensor-heat/formalization.yaml").decode("utf-8")
    for required in (BASE, SOURCE.as_posix(), "vendor/curvature", "relationship: \"builds-on\""):
        if required not in metadata:
            raise SystemExit("structured provenance is incomplete: " + required)
    if "RiemannianSectionCore.lean" not in metadata:
        raise SystemExit("structured provenance omits the proof-support module split")
    banach_space = git_bytes(vendor_blobs[
        "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/BanachSpace.lean"
    ]).decode("utf-8")
    if "import Mathlib.Analysis.Normed.Group.SeparationQuotient" in banach_space:
        raise SystemExit("unused BanachSpace separation-quotient import was restored")
    print("Immutable source, exact baseline/adapted vendor inventory, notices, and structured provenance passed.")


if __name__ == "__main__":
    main()
