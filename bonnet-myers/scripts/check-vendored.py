"""Verify the exact immutable source inventory vendored from curvature/."""

from pathlib import Path
import hashlib
import subprocess


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parent
SOURCE_REVISION = "5db025e6d20d8aad714c3d116714545d1823fd8e"
PREFIX = "curvature/"
EXPECTED = {
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceContinuousDeriv.lean",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurck.lean",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Along.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Bianchi.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Contractions.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Raw.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Sectional.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/DowngradeNormFree.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Existence.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/HomBundleComp.lean",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean",
}


def git(*arguments: str) -> bytes:
    return subprocess.check_output(["git", *arguments], cwd=REPOSITORY)


def blob_hash(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    source = git("ls-tree", "-r", "-z", SOURCE_REVISION, "--", PREFIX)
    source_blobs = {}
    for record in source.split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, kind, digest = metadata.decode().split()
        relative = raw_path.decode().removeprefix(PREFIX)
        if relative in EXPECTED:
            if mode != "100644" or kind != "blob":
                raise SystemExit("unexpected source object: " + relative)
            source_blobs[relative] = digest
    if set(source_blobs) != EXPECTED:
        raise SystemExit("immutable source snapshot is missing an expected file")

    vendor = ROOT / "vendor/curvature"
    actual = {
        str(path.relative_to(vendor)): path
        for path in vendor.rglob("*.lean")
        if path.is_file() or path.is_symlink()
    }
    if set(actual) != EXPECTED:
        missing = sorted(EXPECTED - set(actual))
        extra = sorted(set(actual) - EXPECTED)
        raise SystemExit(f"vendored inventory mismatch; missing={missing}, extra={extra}")
    for relative, path in actual.items():
        if path.is_symlink():
            raise SystemExit("vendored source is a symlink: " + relative)
        digest = blob_hash(path.read_bytes())
        if digest != source_blobs[relative]:
            raise SystemExit("vendored source differs from immutable snapshot: " + relative)

    source_license = git("show", SOURCE_REVISION + ":LICENSE")
    for path in (ROOT / "LICENSE", vendor / "LICENSE"):
        if not path.is_file() or path.is_symlink() or path.read_bytes() != source_license:
            raise SystemExit("Apache-2.0 licence copy differs: " + str(path))
    print(f"All {len(EXPECTED)} vendored Lean files and both licence copies match {SOURCE_REVISION}.")


if __name__ == "__main__":
    main()
