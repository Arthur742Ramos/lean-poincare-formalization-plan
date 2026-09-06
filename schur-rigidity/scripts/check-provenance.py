"""Regression guard for the immutable inherited formalization disclosure."""
from pathlib import Path
import copy
import yaml

SOURCE = (
    "https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/"
    "90d215d81d30a5f67922dce00dfa160b4878e1c5/contracted-bianchi"
)

def validate(metadata):
    matches = [item for item in metadata.get("related_formalizations", [])
               if item.get("id") == SOURCE]
    if len(matches) != 1:
        raise ValueError("Missing or duplicate immutable contracted-bianchi provenance")
    entry = matches[0]
    if entry.get("relationship") != "builds-on":
        raise ValueError("The copied curvature library must be recorded as builds-on")
    note = entry.get("note", "")
    for required in ("contracted-bianchi/PoincareCurvature/", "copied unchanged",
                     "not a newly selected result", "Schur", "Ricci/scalar"):
        if required not in note:
            raise ValueError("Incomplete inherited/new-result distinction: " + required)

metadata = yaml.safe_load((Path(__file__).resolve().parents[1] / "formalization.yaml").read_text())
validate(metadata)
for mutation in ([], [{"id": SOURCE, "relationship": "independent"}],
                 [{"id": SOURCE, "relationship": "builds-on", "note": "Reused code"}]):
    broken = copy.deepcopy(metadata)
    broken["related_formalizations"] = mutation
    try:
        validate(broken)
    except ValueError:
        continue
    raise AssertionError("Provenance negative control was accepted")
print("Structured provenance passed; all three negative controls rejected.")
