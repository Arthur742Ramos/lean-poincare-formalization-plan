"""Verify immutable vendored files and the two reviewed compatibility adaptations."""

from pathlib import Path
import hashlib
import subprocess


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parent
REVISION = "0cc7c31bf6e2dac5c0359a432f3d99803f563017"
PREFIX = "curvature/"

UNCHANGED = {
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean": "f51be67d184f62539a2eb048b6d0473f46de8e9b",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceContinuousDeriv.lean": "b8da09f25c38ce0da2587aeb886fade977788259",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurck.lean": "415fbf897d53cecd35a75cc8ef2a73e8d2928730",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean": "4b3105634f0cdd1bb29a51e3815f70af36582401",
    "PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence.lean": "3d430cddf9790bd71375727570118e3aed74e183",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/ContinuousSection.lean": "5d8a958fbaeb2613f1bfe2e6e6eb020f01adbe00",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Along.lean": "2cb0c3d13e7d871936b06934ab0524bc4b729fcb",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Bianchi.lean": "8a485f4e3d713afd12016d09201f9d57981421a4",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Contractions.lean": "bdd0708ef3bd896028b000907c5c7e801f1f6834",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Raw.lean": "a9bbfe8933a38543c3568f185d219a7917032e26",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Sectional.lean": "a92f67c5b271d398532722c13cb6b5a345a80fe1",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Tensor.lean": "4b887b01c3d90ef1a2b645610f281829c12808a9",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/DowngradeNormFree.lean": "cb6e05ec51e2933cc563cde4efc6bb1f90b880ac",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Existence.lean": "6678aacea7247af23f8c24c7bbd2d631bc68d220",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean": "31a79f8cc30b8dbed94396a2575274effbd83f54",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean": "61c3753bed4bae6d19225c6a46cc1ad7864443b7",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean": "23d11ea8d2b19bafc1c758ce3107a908486ff1a2",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/HomBundleComp.lean": "bfdbd06290f24aae86a50b3e7e8d9dff01b4addd",
    "PoincareCurvature/Geometry/Manifold/VectorBundle/RiemannianSection.lean": "f250764aa6e576e55a1183e71ca8eafc3f3cfc8c",
}

ADAPTED = {
    "PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence/EinsteinAux.lean":
        ("a3cc9e8d6cdbb3892f9e580b7bec6ff7d3bd6713", "448c02120d88d67c1378bc157fb2dbc8a05810a1"),
    "PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence/Einstein.lean":
        ("7d26eba94ed9b2d8af809732d72cc4e1770313d9", "5f0345914aef49ec1b01e970f1279e8f245304e0"),
}


def git(*arguments: str) -> bytes:
    return subprocess.check_output(["git", *arguments], cwd=REPOSITORY)


def blob_hash(data: bytes) -> str:
    header = b"blob " + str(len(data)).encode() + b"\0"
    return hashlib.sha1(header + data).hexdigest()


def main() -> None:
    expected = set(UNCHANGED) | set(ADAPTED)
    vendor = ROOT / "vendor/curvature"
    actual = {
        str(path.relative_to(vendor)): path
        for path in vendor.rglob("*.lean") if path.is_file() or path.is_symlink()
    }
    if set(actual) != expected:
        raise SystemExit(
            f"vendored inventory mismatch; missing={sorted(expected - set(actual))}, "
            f"extra={sorted(set(actual) - expected)}"
        )
    for relative, expected_blob in UNCHANGED.items():
        source_blob = git("rev-parse", f"{REVISION}:{PREFIX}{relative}").decode().strip()
        if source_blob != expected_blob:
            raise SystemExit("recorded source blob changed: " + relative)
        path = actual[relative]
        if path.is_symlink() or blob_hash(path.read_bytes()) != expected_blob:
            raise SystemExit("vendored source differs from immutable snapshot: " + relative)
    for relative, (source_expected, adapted_expected) in ADAPTED.items():
        source_blob = git("rev-parse", f"{REVISION}:{PREFIX}{relative}").decode().strip()
        if source_blob != source_expected:
            raise SystemExit("adaptation base blob changed: " + relative)
        path = actual[relative]
        if path.is_symlink() or blob_hash(path.read_bytes()) != adapted_expected:
            raise SystemExit("reviewed adaptation hash changed: " + relative)
    source_license = git("show", REVISION + ":LICENSE")
    for path in (ROOT / "LICENSE", vendor / "LICENSE"):
        if not path.is_file() or path.is_symlink() or path.read_bytes() != source_license:
            raise SystemExit("Apache-2.0 licence copy differs: " + str(path))
    print("Verified 19 immutable vendored files, 2 reviewed adaptations, and both licence copies.")


if __name__ == "__main__":
    main()
