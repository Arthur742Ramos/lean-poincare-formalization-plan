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
import sys
import tomllib
import urllib.request

import jsonschema
import yaml


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json"
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
CURVATURE_BASE = "13fa15d6a8352ed08bf71b3533b1c2e922c21388"
THEOREM = "SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed"
DEFINITIONS = ["SymmetricTensorHeatEntry.completeStatement"]
ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PALOMAR = "a013555a88a0fc9ec910a09ea833dc9cc338db35"
COMPARATOR = "575674928e239f5bc452aab72d1dd7b0f1326494"
NANODA = "68d5ca9db226849b41a6fff59d796ff19d0a8840"
LANDRUN = "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
CACHE_ACTION = "0400d5f644dc74513175e3cd8d07132dd4860809"
CURRENT_PALOMAR = "1703d7babd984ccc3831cdf89c28221abe34808f"


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


def vendored_import_closure() -> set[str]:
    """Return the vendored modules reachable from the candidate entry points.

    Lake does not infer same-library source modules when a library has an
    explicit ``roots`` list, so keep that list fail-closed and derive the
    expected closure from the actual public and private imports.  The parser
    deliberately accepts ``public import`` as well as ordinary imports.
    """
    vendor = ROOT / "vendor/curvature"
    modules = {
        ".".join(path.relative_to(vendor).with_suffix("").parts): path
        for path in vendor.rglob("*.lean")
    }
    import_pattern = re.compile(r"^(?:public )?import\s+([A-Za-z0-9_.]+)$",
                                re.MULTILINE)
    queue: list[str] = []
    for entry in (ROOT / "TensorHeatSolution.lean",
                  ROOT / "TensorHeatGeometricSymmetry.lean"):
        source = without_comments(entry.read_text(encoding="utf-8"))
        queue.extend(module for module in import_pattern.findall(source)
                     if module in modules)
    closure: set[str] = set()
    while queue:
        module = queue.pop()
        if module in closure:
            continue
        closure.add(module)
        source = without_comments(modules[module].read_text(encoding="utf-8"))
        queue.extend(imported for imported in import_pattern.findall(source)
                     if imported in modules and imported not in closure)
    return closure


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
        "scripts/check-nonvacuity.lean",
        "scripts/verify-comparator.sh",
        "vendor/curvature/PoincareCurvature.lean",
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
    statement = statement_block(challenge)
    for semantic_guard in (
        "(∀ x, ∑ᶠ i, atlasWeight i x = 1)",
        "atlasWeight i x ≠ 0 → ∀ v,",
        "initialTensor D x = ∑ᶠ i, initialLocalTensor D i x",
        "sourceTensor f t x = ∑ᶠ i, sourceLocalTensor f i t x",
        "∑ᶠ i, solutionLocalTensor q i t x a b",
        "∑ᶠ i, solutionLocalTimeDerivative q i t x a b",
        "initialLocalTensor D i x (atlasFrame i p x)",
        "sourceLocalTensor f i t x (atlasFrame i p x)",
        "solutionLocalTensor q i t x (atlasFrame i p x)",
        "solutionLocalTimeDerivative q i t x",
        "Function.Injective (fun D =>",
        "Function.Injective sourceValue",
        "Function.Injective (fun q =>",
        "∀ c : Index →",
        "∃ D, ∀ i x",
        "∃ f, ∀ i z",
        "∃ q, ∀ i z",
        "let hasSpatialC2 :=",
        "let hasParabolicC0 :=",
        "let hasParabolicC0First :=",
        "let hasParabolicC0Second :=",
        "let hasParabolicC2 :=",
    ):
        require(semantic_guard in statement,
                "anti-vacuity statement guard missing: " + semantic_guard)
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
        "name": "mathlib", "scope": "leanprover-community", "rev": MATHLIB,
    }], "Lake must depend directly on the pinned Mathlib revision")
    libraries = {entry["name"]: entry for entry in lakefile["lean_lib"]}
    curvature = libraries["PoincareCurvature"]
    require(curvature.get("srcDir") == "vendor/curvature" and
            set(curvature) == {"name", "srcDir", "roots"},
            "vendored curvature must be a rooted library, not a nested Lake package")
    require(set(curvature["roots"]) == vendored_import_closure(),
            "vendored curvature roots do not match the candidate import closure")
    require(libraries["TensorHeatChallenge"].get("roots") == ["TensorHeatChallenge"] and
            libraries["TensorHeatSolution"].get("roots") == ["TensorHeatSolution"],
            "Challenge/Solution Lake roots changed")
    require(set(lakefile["defaultTargets"]) == {
        "TensorHeatChallenge", "TensorHeatSolution", "TensorHeatGeometricSymmetry"},
            "default target coverage changed")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    path_deps = [p for p in manifest["packages"] if p["type"] == "path"]
    require(path_deps == [],
            "manifest must have no path packages (Palomar grants one writable build root)")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    require(mathlib["type"] == "git" and
            mathlib["url"] == "https://github.com/leanprover-community/mathlib4" and
            mathlib["rev"] == MATHLIB and not mathlib["inherited"],
            "direct Mathlib manifest pin changed")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2",
            "unsupported Lean toolchain")

    workflows = {
        "mechanical": ROOT.parent / ".github/workflows/symmetric-tensor-heat-palomar-mechanical.yml",
        "renderer": ROOT.parent / ".github/workflows/symmetric-tensor-heat-palomar-render.yml",
        "current-mechanical": ROOT.parent / ".github/workflows/symmetric-tensor-heat-palomar-current.yml",
        "current-renderer": ROOT.parent / ".github/workflows/symmetric-tensor-heat-palomar-current-render.yml",
    }
    for name, path in workflows.items():
        require(path.is_file() and not path.is_symlink(), f"missing regular {name} workflow")
        require("  push:" not in path.read_text(encoding="utf-8"),
                f"duplicate push trigger in {name} workflow")
    mechanical = workflows["mechanical"].read_text(encoding="utf-8")
    require("  pull_request:" not in mechanical and "  workflow_dispatch:" in mechanical,
            "historical mechanical replay must be manual only")
    for required_text in (
        PALOMAR, COMPARATOR, NANODA, LANDRUN, CACHE_ACTION,
        "verify_submission.py prepare", "verify_submission.py execute",
        "candidate-preflight:", "needs: candidate-preflight",
        "fetch-depth: 0",
        "python scripts/check-package.py", "python scripts/check-provenance.py",
        "lake build TensorHeatChallenge",
        "lake env lean scripts/check-nonvacuity.lean",
        '"project_path": "symmetric-tensor-heat"',
        '"comparator_config_path": "symmetric-tensor-heat/comparator.json"',
        '"formalization_metadata_path": "symmetric-tensor-heat/formalization.yaml"',
    ):
        require(required_text in mechanical,
                "complete hosted Palomar verifier workflow changed: " + required_text)
    renderer = workflows["renderer"].read_text(encoding="utf-8")
    require("  pull_request:" in renderer, "pinned renderer must run on pull requests")
    for required_text in (PALOMAR, LANDRUN, "render_challenge prepare", "render_challenge execute"):
        require(required_text in renderer,
                "hosted Palomar renderer workflow changed: " + required_text)
    current_mechanical = workflows["current-mechanical"].read_text(encoding="utf-8")
    require("  pull_request:" in current_mechanical,
            "current mechanical preflight must run on pull requests")
    for required_text in (CURRENT_PALOMAR, "mode: full",
                          "execution_profile: palomar-standard-v1",
                          "commit: ${{ github.event.pull_request.head.sha || github.sha }}"):
        require(required_text in current_mechanical,
                "current Palomar mechanical workflow changed: " + required_text)
    current_renderer = workflows["current-renderer"].read_text(encoding="utf-8")
    require("  pull_request:" in current_renderer,
            "current renderer must run on pull requests")
    for required_text in (CURRENT_PALOMAR, "render_challenge prepare", "render_challenge execute", "--bwrap"):
        require(required_text in current_renderer,
                "current Palomar renderer workflow changed: " + required_text)

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
    require(any(f"{CURVATURE_BASE}/curvature" in item
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

    subprocess.run([sys.executable, "scripts/check-provenance.py"], cwd=ROOT, check=True)
    print("Package shape, schema, pins, proof policy, and source boundary passed.")


if __name__ == "__main__":
    main()
