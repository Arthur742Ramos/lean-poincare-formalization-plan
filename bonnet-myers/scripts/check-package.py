"""Fail-closed structural, metadata, source-boundary, and package checks."""

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
ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
THEOREM = "BonnetMyersEntry.bonnet_myers"
DEFINITION = "BonnetMyersEntry.completeStatement"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def without_comments(source: str) -> str:
    result = []
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
        "Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "LICENSE",
        "README.md", "PROVENANCE.md", "RESEARCH_INTEREST.md", "AGENT-CONTRIBUTION.md",
    ]
    for relative in required:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), "missing regular file: " + relative)

    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    solution = (ROOT / "Solution.lean").read_text(encoding="utf-8")
    statement = (ROOT / "BonnetMyers/Statement.lean").read_text(encoding="utf-8")
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            "Challenge exceeds Palomar's hard size limit")
    require(challenge.startswith(statement), "Challenge and canonical statement have diverged")
    challenge_code = without_comments(challenge)
    imports = re.findall(r"^(?:public )?import\s+(.+)$", challenge_code, re.MULTILINE)
    require(imports and all(item.startswith("Mathlib.") or item == "Mathlib" for item in imports),
            "Challenge imports project-specific source")
    require(len(re.findall(r"\bsorry\b", challenge_code)) == 1,
            "Challenge must contain exactly one intentional hole")
    require(len(re.findall(r"^theorem\s+", challenge_code, re.MULTILINE)) == 1,
            "Challenge must expose exactly one theorem")
    require(not re.search(r"\b(sorry|admit|axiom)\b", without_comments(solution)),
            "Solution contains a proof-hole token")
    require("import BonnetMyers.Complete" in solution,
            "Solution does not import the completed proof")

    active_files = sorted((ROOT / "BonnetMyers").rglob("*.lean"))
    active_files += sorted((ROOT / "vendor/curvature/PoincareCurvature").rglob("*.lean"))
    active_files.append(ROOT / "Solution.lean")
    for path in active_files:
        code = without_comments(path.read_text(encoding="utf-8"))
        require(not re.search(r"\b(sorry|admit|axiom)\b", code),
                "proof-hole token in active source: " + str(path.relative_to(ROOT)))
        require("DifferentialGeometry" not in code,
                "prohibited external implementation import: " + str(path.relative_to(ROOT)))

    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    expected_comparator = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [THEOREM],
        "definition_names": [DEFINITION],
        "permitted_axioms": ALLOWED_AXIOMS,
        "enable_nanoda": True,
    }
    require(comparator == expected_comparator, "Comparator selection or trust boundary changed")

    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require(lakefile["require"] == [{"name": "mathlib", "git":
            "https://github.com/leanprover-community/mathlib4.git", "rev": MATHLIB}],
            "only the pinned canonical Mathlib dependency is allowed")
    libraries = {entry["name"]: entry for entry in lakefile["lean_lib"]}
    require(libraries["PoincareCurvature"].get("srcDir") == "vendor/curvature",
            "proof infrastructure must be project-local")
    require(libraries["Challenge"].get("roots") == ["Challenge"] and
            libraries["Solution"].get("roots") == ["Solution"],
            "Challenge/Solution Lake roots changed")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    require(all(package["type"] == "git" and not package.get("subDir")
                for package in manifest["packages"]),
            "manifest contains a non-Git or subdirectory dependency")
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    require(mathlib["url"] == "https://github.com/leanprover-community/mathlib4.git" and
            mathlib["rev"] == MATHLIB, "Mathlib manifest pin changed")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0",
            "unsupported or unreviewed Lean toolchain")

    metadata_text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    require(len(metadata_text.encode()) <= 256 * 1024, "formalization.yaml exceeds size limit")
    metadata = yaml.safe_load(metadata_text)
    with urllib.request.urlopen(SCHEMA, timeout=30) as response:
        schema = json.load(response)
    jsonschema.Draft7Validator.check_schema(schema)
    jsonschema.Draft7Validator(schema).validate(metadata)
    require(metadata["version"] == "v0.4", "metadata version is not v0.4")
    require("repository" not in metadata, "ordinary substantive project must omit repository mapping")
    require(metadata["project"]["license"] == "Apache-2.0", "metadata licence mismatch")
    require(metadata["project"]["authors"] == ["Arthur Freitas Ramos"] and
            metadata["project"]["responsible_maintainers"] == ["Arthur Freitas Ramos"],
            "human authorship or maintenance metadata changed")
    require(any(source.get("relationship") == "independently-proves"
                for source in metadata["sources"]), "source-based origin is missing")
    related = {entry["id"] for entry in metadata["related_formalizations"]}
    require(any("5db025e6d20d8aad714c3d116714545d1823fd8e/curvature" in item
                for item in related), "same-repository infrastructure provenance is missing")
    require(any("qinz1yang/differential-geometry" in item for item in related),
            "known independent implementation provenance is missing")
    results = {entry["declaration"]: entry["file"]
               for entry in metadata["status"]["main_results"]}
    require(results.get(THEOREM) == "Solution.lean" and
            results.get("BonnetMyersEntry.completeStatement_proved") ==
            "BonnetMyers/Complete.lean", "main-result metadata changed")
    require(metadata["status"]["sorry_count"] == 0 and
            metadata["status"]["sorry_in_definitions"] == 0 and
            set(metadata["status"]["axioms"]) == set(ALLOWED_AXIOMS),
            "proof-status metadata changed")

    for path in ROOT.rglob("*"):
        if ".lake" in path.parts or ".cache" in path.parts:
            continue
        require(not path.is_symlink(), "source tree contains symlink: " + str(path.relative_to(ROOT)))
        if path.is_file():
            require(path.suffix not in {".olean", ".ilean", ".a", ".bc", ".o", ".so", ".dylib", ".trace", ".pyc"},
                    "compiled artifact outside .lake: " + str(path.relative_to(ROOT)))
    subprocess.run(["python3", "scripts/check-vendored.py"], cwd=ROOT, check=True)
    print("Package shape, exact statement surface, metadata schema, dependency pins, and source policy passed.")


if __name__ == "__main__":
    main()
