"""Fail-closed structural checks for the Almost-Schur package."""

from pathlib import Path
import json
import re

import yaml


ROOT = Path(__file__).resolve().parents[1]


def main():
    challenge = ROOT / "Challenge.lean"
    solution = ROOT / "Solution.lean"
    comparator_path = ROOT / "comparator.json"
    metadata_path = ROOT / "formalization.yaml"
    for path in (challenge, solution, comparator_path, metadata_path, ROOT / "LICENSE"):
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"missing or non-regular required file: {path}")
    if len(challenge.read_text(encoding="utf-8").splitlines()) > 1000:
        raise SystemExit("Challenge.lean exceeds the 1000-line limit")
    if challenge.stat().st_size > 100 * 1024:
        raise SystemExit("Challenge.lean exceeds the 100 KiB limit")

    comparator = json.loads(comparator_path.read_text(encoding="utf-8"))
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if set(comparator) - required - {"definition_names", "enable_nanoda"}:
        raise SystemExit("Comparator has unsupported keys")
    if comparator.get("challenge_module") != "Challenge":
        raise SystemExit("Comparator challenge module must be Challenge")
    if comparator.get("solution_module") != "Solution":
        raise SystemExit("Comparator solution module must be Solution")
    expected_theorems = [
        "AlmostSchurEntry.Geometry.almostSchur",
    ]
    if comparator.get("theorem_names") != expected_theorems:
        raise SystemExit("Comparator theorem surface changed unexpectedly")
    expected_definitions = [
        "AlmostSchurEntry.Geometry." + name for name in (
            "extensionBump", "extension", "curvature", "ricci", "scalar",
            "traceFreeRicciSq", "isRiemannianVolume", "average", "geometricStatement",
        )
    ]
    if comparator.get("definition_names") != expected_definitions:
        raise SystemExit("Comparator must compare every geometric statement definition")
    if comparator.get("permitted_axioms") != ["propext", "Quot.sound", "Classical.choice"]:
        raise SystemExit("Comparator permitted axioms are not the standard three")
    if comparator.get("enable_nanoda") is not True:
        raise SystemExit("NanoDa must be enabled")

    challenge_text = challenge.read_text(encoding="utf-8")
    if len(re.findall(r"\btheorem\s+", challenge_text)) != 1:
        raise SystemExit("Challenge must select the complete geometric theorem")
    if len(re.findall(r"\bsorry\b", challenge_text)) != 1:
        raise SystemExit("Challenge must contain exactly one intentional hole")
    solution_text = solution.read_text(encoding="utf-8")
    if re.search(r"\b(sorry|admit|axiom)\b", solution_text):
        raise SystemExit("Solution contains a proof-hole token")
    if "import AlmostSchur" not in solution_text:
        raise SystemExit("Solution must import the completed implementation")

    metadata = yaml.safe_load(metadata_path.read_text(encoding="utf-8"))
    if metadata.get("version") != "v0.4":
        raise SystemExit("formalization.yaml must declare v0.4")
    project = metadata.get("project", {})
    if not project.get("name") or project.get("license") != "Apache-2.0":
        raise SystemExit("project name/license metadata is incomplete")
    if project.get("responsible_maintainers") != ["Arthur Freitas Ramos"]:
        raise SystemExit("responsible maintainer metadata is incomplete")
    if metadata.get("repository", {}).get("role") != "substantive-development":
        raise SystemExit("repository must be declared as substantive-development")
    sources = metadata.get("sources", [])
    if not sources or not any(s.get("relationship") == "formalizes" for s in sources):
        raise SystemExit("the source-based formalization relationship is missing")
    source = next((s for s in sources if s.get("id") == "10.1007/s00526-011-0413-z"), {})
    if source.get("authors") != ["Camillo De Lellis", "Peter M. Topping"]:
        raise SystemExit("the verified bibliographic source authors are missing or incorrect")
    results = {r.get("declaration") for r in metadata.get("status", {}).get("main_results", [])}
    if not set(expected_theorems) <= results:
        raise SystemExit("Comparator-selected geometry must be recorded among the main results")
    related = metadata.get("related_formalizations", [])
    if not any("contracted-bianchi" in s.get("id", "") for s in related):
        raise SystemExit("contracted-bianchi provenance is missing")
    if not any("rellich-kondrachov" in s.get("id", "") for s in related):
        raise SystemExit("Rellich-Kondrachov provenance is missing")
    print("Almost-Schur package metadata and surface checks passed.")


if __name__ == "__main__":
    main()
