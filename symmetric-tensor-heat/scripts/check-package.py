# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "jsonschema==4.26.0",
#   "PyYAML==6.0.3",
# ]
# ///
"""Fail-closed package, metadata, source-boundary, and proof-hole checks.

Run directly in an environment with the two dependencies above, or use
`uv run scripts/check-package.py` to resolve the embedded pinned environment.
"""

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
THEOREM = "SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed"
DEFINITIONS = [
    "SymmetricTensorHeatEntry.IsInducedTwoTensorConnection",
    "SymmetricTensorHeatEntry.IsInducedThreeTensorConnection",
    "SymmetricTensorHeatEntry.connectionLaplacianApply",
    "SymmetricTensorHeatEntry.IsSymmetricSection",
    "SymmetricTensorHeatEntry.HasInitialTrace",
    "SymmetricTensorHeatEntry.HasTimeDerivative",
    "SymmetricTensorHeatEntry.SolvesTensorHeat",
    "SymmetricTensorHeatEntry.IsMetricCompatibleTangent",
    "SymmetricTensorHeatEntry.IsLeviCivita",
    "SymmetricTensorHeatEntry.completeStatement",
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
            depth += 1; result.append("  "); index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1; result.append("  "); index += 2
        elif depth:
            result.append("\n" if source[index] == "\n" else " "); index += 1
        elif source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                result.append(" "); index += 1
        else:
            result.append(source[index]); index += 1
    require(depth == 0, "unclosed Lean block comment")
    return "".join(result)


def statement_block(source: str) -> str:
    start = source.index("def completeStatement : Prop :=")
    end_markers = ["\ntheorem symmetricTensorHeatShortTimeWellPosed", "\n\nprivate theorem canonicalTwo_apply_eq"]
    ends = [source.find(marker, start) for marker in end_markers]
    return source[start:min(end for end in ends if end >= 0)].strip()


def instance_block(source: str) -> str:
    start = source.index("@[reducible] local instance challengeTwoModelNormedAddCommGroup")
    end = source.index("/-- A connection on covariant two-tensors", start)
    return source[start:end].strip()


def main() -> None:
    required = [
        "TensorHeatChallenge.lean", "TensorHeatSolution.lean", "comparator.json",
        "formalization.yaml", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "LICENSE", "README.md", "PROVENANCE.md", "RESEARCH_INTEREST.md",
        "AGENT-CONTRIBUTION.md", "VERIFICATION.md",
        "scripts/check-closed-statement.lean", "scripts/check-provenance.py",
        "scripts/check-challenge-boundary.py", "scripts/check-axioms.py",
        "scripts/verify-comparator.sh",
        "vendor/curvature/PoincareCurvature.lean",
        "vendor/curvature/lakefile.toml",
        "vendor/curvature/lake-manifest.json",
        "vendor/curvature/lean-toolchain",
        "vendor/curvature/LICENSE",
    ]
    for relative in required:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), "missing regular file: " + relative)

    challenge = (ROOT / "TensorHeatChallenge.lean").read_text(encoding="utf-8")
    solution = (ROOT / "TensorHeatSolution.lean").read_text(encoding="utf-8")
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            "Challenge exceeds Palomar hard size limits")
    challenge_code = without_comments(challenge)
    imports = re.findall(r"^(?:public )?import\s+(.+)$", challenge_code, re.MULTILINE)
    require(imports and all(item.startswith("Mathlib.") or item == "Mathlib" for item in imports),
            "Challenge imports candidate-specific source")
    require(len(re.findall(r"\bsorry\b", challenge_code)) == 1,
            "Challenge must contain exactly one intentional hole")
    require(len(re.findall(r"^theorem\s+", challenge_code, re.MULTILINE)) == 1,
            "Challenge must expose exactly one theorem")
    require(THEOREM.rsplit(".", 1)[1] in challenge, "selected Challenge theorem missing")
    solution_code = without_comments(solution)
    require("import TensorHeatChallenge" not in solution_code,
            "Solution imports the Challenge and could reuse its hole")
    require("import PoincareCurvature." in solution_code,
            "Solution does not import the inherited proof development")
    require(not re.search(r"\b(sorry|admit|axiom)\b", solution_code),
            "proof-hole token in Solution")
    require(statement_block(challenge) == statement_block(solution),
            "Challenge and Solution completeStatement source differs")
    require(instance_block(challenge) == instance_block(solution),
            "Challenge and Solution structural instance blocks differ")
    for inherited_source in (ROOT / "vendor/curvature").rglob("*.lean"):
        inherited_code = without_comments(inherited_source.read_text(encoding="utf-8"))
        require(not re.search(r"\b(sorry|admit|axiom)\b", inherited_code),
                "proof-hole token in vendored source: " +
                str(inherited_source.relative_to(ROOT)))

    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    expected = {
        "challenge_module": "TensorHeatChallenge",
        "solution_module": "TensorHeatSolution",
        "theorem_names": [THEOREM],
        "definition_names": DEFINITIONS,
        "permitted_axioms": ALLOWED_AXIOMS,
        "enable_nanoda": True,
    }
    require(comparator == expected, "Comparator selection or trust boundary changed")

    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require(lakefile["require"] == [{
        "name": "PoincareCurvature", "path": "vendor/curvature"
    }], "Lake dependency must be the disclosed contained curvature snapshot")
    libraries = {entry["name"]: entry for entry in lakefile["lean_lib"]}
    require(libraries["TensorHeatChallenge"].get("roots") == ["TensorHeatChallenge"] and
            libraries["TensorHeatSolution"].get("roots") == ["TensorHeatSolution"],
            "Challenge/Solution Lake roots changed")
    require(set(lakefile["defaultTargets"]) == {"TensorHeatChallenge", "TensorHeatSolution"},
            "default target coverage changed")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    path_deps = [p for p in manifest["packages"] if p["type"] == "path"]
    require(path_deps == [{
        "type": "path", "scope": "", "name": "PoincareCurvature",
        "manifestFile": "lake-manifest.json", "inherited": False,
        "dir": "vendor/curvature", "configFile": "lakefile.toml",
    }], "manifest path dependency changed")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    require(mathlib["type"] == "git" and
            mathlib["url"] == "https://github.com/leanprover-community/mathlib4" and
            mathlib["rev"] == MATHLIB, "Mathlib manifest pin changed")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0",
            "unsupported Lean toolchain")

    metadata_text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    require(len(metadata_text.encode()) <= 256 * 1024, "formalization.yaml too large")
    metadata = yaml.safe_load(metadata_text)
    with urllib.request.urlopen(SCHEMA, timeout=30) as response:
        schema = json.load(response)
    jsonschema.Draft7Validator.check_schema(schema)
    jsonschema.Draft7Validator(schema).validate(metadata)
    require(metadata["version"] == "v0.4", "metadata version changed")
    require(metadata["project"]["license"] == "Apache-2.0", "licence mismatch")
    require(metadata["project"]["authors"] == [
        "Arthur Freitas Ramos", "David Barros Hulak", "Ruy J. G. B. de Queiroz"
    ], "human authorship metadata changed")
    related = {entry["id"] for entry in metadata["related_formalizations"]}
    require(any("d6ef7f253bb95fa44d1fe61c9b1a52e061ca0951/curvature" in item
                for item in related), "same-repository provenance missing")
    require(any(MATHLIB in item for item in related), "Mathlib provenance missing")
    result = metadata["status"]["main_results"]
    require(len(result) == 1 and result[0]["declaration"] == THEOREM and
            result[0]["file"] == "TensorHeatSolution.lean", "main result metadata changed")
    require(metadata["status"]["sorry_count"] == 0 and
            metadata["status"]["sorry_in_definitions"] == 0 and
            set(metadata["status"]["axioms"]) == set(ALLOWED_AXIOMS),
            "proof-status metadata changed")

    for path in ROOT.rglob("*"):
        if ".lake" in path.parts or ".cache" in path.parts:
            continue
        require(not path.is_symlink(), "source tree contains symlink: " + str(path.relative_to(ROOT)))
        if path.is_file():
            require(path.suffix not in {".olean", ".ilean", ".a", ".bc", ".o", ".so", ".dylib", ".pyc"},
                    "compiled artifact outside build/cache: " + str(path.relative_to(ROOT)))

    subprocess.run(["python3", "scripts/check-provenance.py"], cwd=ROOT, check=True)
    print("Package shape, schema, pins, proof policy, and source boundary passed.")


if __name__ == "__main__":
    main()
