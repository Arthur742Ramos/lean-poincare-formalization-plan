"""Fail-closed package, metadata, source-boundary, and proof-hole checks."""

from pathlib import Path
import json
import re
import subprocess
import tomllib
import urllib.request

import jsonschema
import yaml


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json"
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
THEOREM = "EinsteinComparisonEntry.einsteinScalarComparisonAndSharpLifespan"
DEFINITIONS = [
    "EinsteinComparisonEntry.completeStatement",
]
ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def without_comments(source: str) -> str:
    result: list[str] = []
    depth = 0
    index = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            result.append("  ")
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            result.append("  ")
            index += 2
        elif depth:
            result.append("\n" if source[index] == "\n" else " ")
            index += 1
        elif source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                result.append(" ")
                index += 1
        else:
            result.append(source[index])
            index += 1
    require(depth == 0, "unclosed Lean block comment")
    return "".join(result)


def main() -> None:
    required = [
        "Challenge.lean", "Solution.lean", "RicciScalarComparison.lean",
        "RicciScalarComparison/EinsteinScalar.lean", "comparator.json",
        "formalization.yaml", "lakefile.toml", "lake-manifest.json",
        "lean-toolchain", "LICENSE", "README.md", "PROVENANCE.md",
        "RESEARCH_INTEREST.md", "AGENT-CONTRIBUTION.md", "VERIFICATION.md",
        "VENDORED-SOURCES.md", "scripts/check-closed-statement.lean",
    ]
    for relative in required:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), "missing regular file: " + relative)

    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    solution = (ROOT / "Solution.lean").read_text(encoding="utf-8")
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            "Challenge exceeds Palomar's hard size limit")
    challenge_code = without_comments(challenge)
    imports = re.findall(r"^(?:public )?import\s+(.+)$", challenge_code, re.MULTILINE)
    require(imports and all(item.startswith("Mathlib.") or item == "Mathlib" for item in imports),
            "Challenge imports candidate-specific source")
    require(len(re.findall(r"\bsorry\b", challenge_code)) == 1,
            "Challenge must contain exactly one intentional hole")
    require(len(re.findall(r"^theorem\s+", challenge_code, re.MULTILINE)) == 1,
            "Challenge must expose exactly one theorem")
    require(THEOREM.rsplit(".", 1)[1] in challenge,
            "selected Challenge theorem is missing")
    require("import RicciScalarComparison" in solution and
            "import PoincareCurvature" in solution,
            "Solution does not import the local proof development")

    active = [ROOT / "Solution.lean", ROOT / "RicciScalarComparison.lean"]
    active += sorted((ROOT / "RicciScalarComparison").rglob("*.lean"))
    active += sorted((ROOT / "vendor/curvature/PoincareCurvature").rglob("*.lean"))
    for path in active:
        code = without_comments(path.read_text(encoding="utf-8"))
        require(not re.search(r"\b(sorry|admit|axiom)\b", code),
                "proof-hole token in active source: " + str(path.relative_to(ROOT)))
        require("DifferentialGeometry" not in code,
                "prohibited external formalization import: " + str(path.relative_to(ROOT)))

    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    expected = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [THEOREM],
        "definition_names": DEFINITIONS,
        "permitted_axioms": ALLOWED_AXIOMS,
        "enable_nanoda": True,
    }
    require(comparator == expected, "Comparator selection or trust boundary changed")

    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require(lakefile["require"] == [{
        "name": "mathlib",
        "git": "https://github.com/leanprover-community/mathlib4.git",
        "rev": MATHLIB,
    }], "only the pinned canonical Mathlib dependency is allowed")
    libraries = {entry["name"]: entry for entry in lakefile["lean_lib"]}
    require(libraries["PoincareCurvature"].get("srcDir") == "vendor/curvature",
            "proof infrastructure must remain project-local")
    require(libraries["Challenge"].get("roots") == ["Challenge"] and
            libraries["Solution"].get("roots") == ["Solution"],
            "Challenge/Solution Lake roots changed")
    require(set(lakefile["defaultTargets"]) ==
            {"PoincareCurvature", "RicciScalarComparison", "Challenge", "Solution"},
            "default target coverage changed")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    require(all(package["type"] == "git" and not package.get("subDir")
                for package in manifest["packages"]),
            "manifest contains a non-Git or subdirectory dependency")
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    require(mathlib["url"] == "https://github.com/leanprover-community/mathlib4.git" and
            mathlib["rev"] == MATHLIB, "Mathlib manifest pin changed")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0",
            "unsupported Lean toolchain")

    metadata_text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    require(len(metadata_text.encode()) <= 256 * 1024, "formalization.yaml exceeds size limit")
    metadata = yaml.safe_load(metadata_text)
    with urllib.request.urlopen(SCHEMA, timeout=30) as response:
        schema = json.load(response)
    jsonschema.Draft7Validator.check_schema(schema)
    jsonschema.Draft7Validator(schema).validate(metadata)
    require(metadata["version"] == "v0.4", "metadata version changed")
    require(metadata["project"]["license"] == "Apache-2.0", "metadata licence mismatch")
    require(metadata["project"]["authors"] == [
        "Arthur Freitas Ramos", "David Barros Hulak", "Ruy J. G. B. de Queiroz"
    ] and metadata["project"]["responsible_maintainers"] == ["Arthur Freitas Ramos"],
            "human authorship or maintenance metadata changed")
    related = {entry["id"] for entry in metadata["related_formalizations"]}
    require(any("0cc7c31bf6e2dac5c0359a432f3d99803f563017/curvature" in item
                for item in related), "same-repository source provenance is missing")
    require(any("qinz1yang/differential-geometry" in item for item in related),
            "known overlapping formalization is missing")
    results = {entry["declaration"]: entry["file"]
               for entry in metadata["status"]["main_results"]}
    expected_results = {
        THEOREM,
        "RicciScalarComparison.scalarCurvature_eq_quadraticScalarBarrier",
        "RicciScalarComparison.scalarCurvature_eq_reciprocalTimeToExtinction",
        "RicciScalarComparison.scalarCurvature_tendsto_at_extinction",
        "RicciScalarComparison.extinctionTime_sub_initialTime_eq_dim_div_two_initialScalar",
        "RicciScalarComparison.maximalEinsteinHomotheticIntrinsicSolution_timeSet",
        "RicciScalarComparison.no_riemannian_metric_agrees_at_extinction",
    }
    require(set(results) == expected_results and
            results[THEOREM] == "Solution.lean" and
            all(results[name] == "RicciScalarComparison/EinsteinScalar.lean"
                for name in expected_results - {THEOREM}),
            "main-result metadata changed")
    require(metadata["status"]["sorry_count"] == 0 and
            metadata["status"]["sorry_in_definitions"] == 0 and
            set(metadata["status"]["axioms"]) == set(ALLOWED_AXIOMS),
            "proof-status metadata changed")

    for path in ROOT.rglob("*"):
        if ".lake" in path.parts or ".cache" in path.parts:
            continue
        require(not path.is_symlink(), "source tree contains symlink: " + str(path.relative_to(ROOT)))
        if path.is_file():
            require(path.suffix not in {
                ".olean", ".ilean", ".a", ".bc", ".o", ".so", ".dylib", ".trace", ".pyc"
            }, "compiled artifact outside .lake: " + str(path.relative_to(ROOT)))

    subprocess.run(["python3", "scripts/check-vendored.py"], cwd=ROOT, check=True)
    print("Package shape, metadata schema, dependency pins, proof policy, and source boundary passed.")


if __name__ == "__main__":
    main()
