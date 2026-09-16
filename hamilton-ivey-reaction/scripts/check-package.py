"""Fail-closed checks for the Hamilton--Ivey reaction package."""

from pathlib import Path
import json
import re
import tomllib
import yaml


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
THEOREM = "HamiltonIveyChallenge.hamiltonIveyODEPinching"


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
        "Challenge.lean",
        "Solution.lean",
        "HamiltonIveyReaction.lean",
        "HamiltonIveyReaction/Reaction.lean",
        "comparator.json",
        "formalization.yaml",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "README.md",
        "PROVENANCE.md",
        "RESEARCH_INTEREST.md",
        "VERIFICATION.md",
        "scripts/check-closed-statement.lean",
    ]
    for relative in required:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), "missing regular file: " + relative)

    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    challenge_code = without_comments(challenge)
    imports = re.findall(r"^(?:public )?import\s+(.+)$", challenge_code, re.MULTILINE)
    require(imports and all(item.startswith("Mathlib.") or item == "Mathlib" for item in imports),
            "Challenge imports candidate-specific source")
    require(len(re.findall(r"\bsorry\b", challenge_code)) == 1,
            "Challenge must contain exactly one intentional hole")
    require(len(challenge.encode()) <= 100 * 1024,
            "Challenge exceeds Palomar's hard size limit")

    active = [ROOT / "Solution.lean", ROOT / "HamiltonIveyReaction.lean"]
    active += sorted((ROOT / "HamiltonIveyReaction").rglob("*.lean"))
    for path in active:
        code = without_comments(path.read_text(encoding="utf-8"))
        require(not re.search(r"\b(sorry|admit|axiom)\b", code),
                "proof-hole token in active source: " + str(path.relative_to(ROOT)))
        require("DifferentialGeometry" not in code and "qinz1yang" not in code,
                "external Ricci-flow formalization reference in active source")

    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    require(comparator == {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [THEOREM],
        "definition_names": ["HamiltonIveyChallenge.completeStatement"],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }, "Comparator selection or trust boundary changed")

    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require(lakefile["require"] == [{
        "name": "mathlib",
        "scope": "leanprover-community",
        "rev": MATHLIB,
    }], "only pinned canonical Mathlib is allowed")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0",
            "unexpected Lean toolchain")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    require(mathlib["rev"] == MATHLIB, "Mathlib manifest pin changed")
    require(all(package["name"] != "differential-geometry" for package in manifest["packages"]),
            "external Ricci-flow formalization dependency present")

    metadata_text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    metadata = yaml.safe_load(metadata_text)
    require(metadata["version"] == "v0.4", "metadata version changed")
    require(metadata["project"]["license"] == "Apache-2.0", "metadata license changed")
    related = metadata["related_formalizations"]
    require(len(related) == 1 and "mathlib4/tree/" + MATHLIB in related[0]["id"],
            "formal dependency provenance must contain pinned Mathlib only")
    require("does not prove curvature evolution" in metadata["status"]["scope"],
            "metadata must preserve the geometric scope boundary")
    results = {item["declaration"] for item in metadata["status"]["main_results"]}
    require(THEOREM in results, "selected theorem missing from metadata")

    print("Package boundary, proof-hole policy, pins, metadata, and selection passed.")


if __name__ == "__main__":
    main()
