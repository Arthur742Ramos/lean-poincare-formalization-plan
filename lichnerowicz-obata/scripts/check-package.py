"""Fail-closed metadata, selection, source-pin, and inherited-provenance checks.

Run with PyYAML 6.0.2 and jsonschema 4.25.1. The metadata schema is fetched
from the immutable upstream revision below, not from a moving branch.
"""

import json
import hashlib
from pathlib import Path
import re
import subprocess
import tomllib
import urllib.request

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parent
BASE = "3faf25aefc27842a77c37ca178e8a40a20bb20c7"
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
SCHEMA_REV = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
SCHEMA_URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    + SCHEMA_REV + "/schema/v0.4.schema.json"
)
PREFIX = "LichnerowiczObataEntry.Geometry."
DEFINITIONS = [
    "extensionBump", "extension", "curvature", "ricci", "gradient",
    "laplacian", "isFirstPositiveEigenvalue", "isRoundSphere", "geometricStatement",
]
RELATED = {
    "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/"
    + BASE + "/almost-schur",
    "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/"
    "12cebb809524d0cd185c6cd7bcb5b73d3562bce1/contracted-bianchi",
    "https://github.com/abenenson/rellich-kondrachov/tree/"
    "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23",
    "https://github.com/leanprover-community/mathlib4/tree/" + MATHLIB,
}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPOSITORY)


def check_dependency_layout(manifest, lakefile):
    require(all(p["type"] == "git" and not p.get("subDir")
                for p in manifest["packages"]),
            "registry workaround requires root-level Git dependencies only")
    require(not any(p["name"] == "AlmostSchur" for p in manifest["packages"]),
            "AlmostSchur must compile as a local library, not a dependency")
    require(lakefile["require"] == [{"name": "mathlib", "scope": "leanprover-community",
                                    "rev": MATHLIB}], "only pinned Mathlib may be required")
    libraries = {lib["name"]: lib for lib in lakefile["lean_lib"]}
    for name in ("AlmostSchur", "RellichKondrachov"):
        require(libraries[name].get("srcDir") == "vendor/almost-schur",
                "inherited sources must build in the root package")
        require(not any(key in libraries[name] for key in ("buildDir", "leanLibDir")),
                "inherited build outputs must stay in the root .lake/build")


def check_flat_vendor():
    prefix = "almost-schur/"
    paths = [prefix + part for part in (
        "AlmostSchur", "AlmostSchur.lean", "RellichKondrachov",
        "LICENSE", "PROVENANCE.md", "dependencies")]
    expected = {}
    for record in git("ls-tree", "-r", "-z", BASE, "--", *paths).split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, kind, digest = metadata.decode().split()
        require(kind == "blob" and mode == "100644", "unexpected vendor source mode")
        expected[raw_path.decode().removeprefix(prefix)] = digest
    vendor = ROOT / "vendor/almost-schur"
    actual = {str(path.relative_to(vendor)): path for path in vendor.rglob("*")
              if path.is_file() or path.is_symlink()}
    require(set(actual) == set(expected), "vendor inventory differs from immutable source")
    for name, path in actual.items():
        require(not path.is_symlink(), "vendor symlink: " + name)
        data = path.read_bytes()
        digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(digest == expected[name], "vendor differs from immutable source: " + name)
    print(f"All {len(expected)} vendored files match the immutable AlmostSchur source byte-for-byte.")


def main():
    required = ["LichnerowiczObataChallenge.lean", "LichnerowiczObataSolution.lean",
                "comparator.json", "formalization.yaml", "PROVENANCE.md", "LICENSE"]
    for name in required:
        path = ROOT / name
        require(path.is_file() and not path.is_symlink(), "missing regular file: " + name)
    challenge = (ROOT / required[0]).read_text(encoding="utf-8")
    solution = (ROOT / required[1]).read_text(encoding="utf-8")
    implementation = (ROOT / "LichnerowiczObata/GeometryStatements.lean").read_text(encoding="utf-8")
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            "Challenge exceeds the independent size limit")
    require(challenge.startswith(implementation), "independent definition copies have diverged")
    require(re.findall(r"^(?:public )?import (.+)$", challenge, re.M) == ["Mathlib"],
            "Challenge imports more than Mathlib")
    require(len(re.findall(r"\bsorry\b", challenge)) == 1, "Challenge must have exactly one hole")
    require(len(re.findall(r"^theorem ", challenge, re.M)) == 1, "unexpected Challenge theorem surface")
    require(not re.search(r"\b(sorry|admit|axiom)\b", solution), "Solution contains a proof hole")
    require("import LichnerowiczObata.GeometryComparison" in solution,
            "Solution does not close the independent geometry")
    for path in (ROOT / "LichnerowiczObata").glob("*.lean"):
        require(not re.search(r"^(?:public )?import .*Challenge", path.read_text(), re.M),
                "implementation imports a Challenge: " + path.name)
    config = json.loads((ROOT / "comparator.json").read_text())
    expected = {
        "challenge_module": "LichnerowiczObataChallenge",
        "solution_module": "LichnerowiczObataSolution",
        "theorem_names": [PREFIX + "lichnerowiczObata"],
        "definition_names": [PREFIX + name for name in DEFINITIONS],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    require(config == expected, "Comparator selection or trust boundary changed")
    metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text())
    with urllib.request.urlopen(SCHEMA_URL, timeout=30) as response:
        schema = json.load(response)
    jsonschema.Draft7Validator.check_schema(schema)
    jsonschema.Draft7Validator(schema).validate(metadata)
    require(metadata["version"] == "v0.4", "wrong metadata version")
    require(metadata["project"]["license"] == "Apache-2.0", "wrong license")
    require(metadata["repository"]["role"] == "substantive-development", "wrong repository role")
    require({entry["id"] for entry in metadata["related_formalizations"]} == RELATED,
            "structured inherited provenance is incomplete or changed")
    expected_results = {
        PREFIX + "lichnerowiczObata": "LichnerowiczObataSolution.lean",
        "LichnerowiczObata.lichnerowicz_obata": "LichnerowiczObata/LichnerowiczObata.lean",
        "LichnerowiczObata.obata_round_metric_diffeomorph": "LichnerowiczObata/ObataRoundDiffeomorph.lean",
        "LichnerowiczObata.round_metric_diffeomorph_exists_extremal_eigenfunction":
            "LichnerowiczObata/RoundSphereConverse.lean",
    }
    results = {entry["declaration"]: entry["file"] for entry in metadata["status"]["main_results"]}
    require(results == expected_results, "main-result declarations or source locations changed")
    for entry in metadata["status"]["main_results"]:
        path = ROOT / entry["file"]
        require(path.is_file() and not path.is_symlink(), "missing main-result source")
        require(entry["sorry_count"] == 0 and set(entry["axioms"]) ==
                {"propext", "Classical.choice", "Quot.sound"}, "incorrect main-result trust metadata")
    require(metadata["status"]["sorry_count"] == metadata["status"]["sorry_in_definitions"] == 0,
            "implementation status must be zero-hole")
    require(set(metadata["status"]["axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
            "unexpected advertised axiom set")
    require(metadata["review"]["status"] == "self-assessed", "external review must not be invented")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    check_dependency_layout(manifest, tomllib.loads((ROOT / "lakefile.toml").read_text()))
    check_flat_vendor()
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    require(mathlib["rev"] == MATHLIB, "Mathlib revision changed")
    require(not git("diff", BASE, "--", "almost-schur"), "inherited almost-schur sources changed")
    require(not git("ls-files", "--others", "--exclude-standard", "--", "almost-schur"),
            "untracked files in inherited source require a provenance audit")
    for name in ("LICENSE", "scripts/verify-comparator.sh", "scripts/landrun-wrapper.sh",
                 "scripts/fake-landrun.sh"):
        require((ROOT / name).read_bytes() == git("show", BASE + ":almost-schur/" + name),
                "copied source differs from its attributed pin: " + name)
    print("Metadata schema, all nine definitions, exact source pins, and inherited provenance passed.")


if __name__ == "__main__":
    main()
