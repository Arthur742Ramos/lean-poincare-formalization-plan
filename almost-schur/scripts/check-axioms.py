"""Fail closed on missing declarations or unapproved transitive Lean axioms."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def validate(output, expected):
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        if name in found:
            raise ValueError("duplicate axiom report: " + name)
        found[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    if set(found) != expected:
        raise ValueError("axiom-report coverage mismatch")
    if any(not axioms <= ALLOWED for axioms in found.values()):
        raise ValueError("unapproved axiom in proof closure")


expected = set()
for path in (ROOT / "AlmostSchur").rglob("*.lean"):
    source = path.read_text()
    if re.search(r"\b(sorry|admit|axiom)\b", source):
        raise ValueError("proof-hole token in " + str(path))
    expected.update("AlmostSchur." + name for name in
                    re.findall(r"^(?:def|theorem) (\w+)", source, re.MULTILINE))
run = subprocess.run(["lake", "env", "lean", "CheckAxioms.lean"], cwd=ROOT,
                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if run.returncode:
    raise SystemExit(run.stdout)
validate(run.stdout, expected)
for bad in ("", "'fixture' depends on axioms: [sorryAx]",
            "'fixture' depends on axioms: [Lean.ofReduceBool]",
            "'fixture' depends on axioms: [Custom.assumption]"):
    try:
        validate(bad, {"fixture"})
    except ValueError:
        continue
    raise AssertionError("negative control accepted")
print(f"Checked all {len(expected)} public declarations; four negative controls rejected.")
