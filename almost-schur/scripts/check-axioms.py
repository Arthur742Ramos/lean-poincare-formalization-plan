"""Fail closed on missing declarations or unapproved transitive Lean axioms."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
VENDORED_ENDPOINTS = {
    "RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1",
    "RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2",
    "RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2_codRestrict_range_extendByZero",
    "RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h1",
    "RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.isCompactOperator_h1ToL2_of_summands",
    "MeasureTheory.Lp.extendByZeroRangeEquivOfRestrictChangeMeasureEquiv",
}


def validate(output, expected):
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        if name in found:
            raise ValueError("duplicate axiom report: " + name)
        found[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        if name in found:
            raise ValueError("duplicate axiom report: " + name)
        found[name] = set()
    if set(found) != expected:
        raise ValueError("axiom-report coverage mismatch")
    if any(not axioms <= ALLOWED for axioms in found.values()):
        raise ValueError("unapproved axiom in proof closure")


def declaration_names(source):
    """Resolve every externally nameable project declaration.

    Private and local declarations cannot be referenced from the generated audit
    module.  They are still protected by the proof-hole-token check below and,
    when used, occur in the transitive axiom closure of a public declaration.
    """
    def strip_comments(text):
        """Remove Lean line/block comments while preserving line boundaries."""
        chars = []
        block_depth = 0
        i = 0
        while i < len(text):
            if block_depth:
                if text.startswith("/-", i):
                    block_depth += 1
                    chars.extend("  ")
                    i += 2
                elif text.startswith("-/", i):
                    block_depth -= 1
                    chars.extend("  ")
                    i += 2
                else:
                    chars.append("\n" if text[i] == "\n" else " ")
                    i += 1
            elif text.startswith("--", i):
                while i < len(text) and text[i] != "\n":
                    chars.append(" ")
                    i += 1
            elif text.startswith("/-", i):
                block_depth = 1
                chars.extend("  ")
                i += 2
            else:
                chars.append(text[i])
                i += 1
        return "".join(chars)

    scopes = []
    names = set()
    for line in strip_comments(source).splitlines():
        opened = re.match(r"^namespace ([\w.]+)\s*$", line)
        section = re.match(r"^section(?: ([\w.]+))?\s*$", line)
        closed = re.match(r"^end(?: ([\w.]+))?\s*$", line)
        declaration = re.match(
            r"^(?!private\b|local\b)"
            r"(?:(?:public|protected|noncomputable|unsafe)\s+)*"
            r"(?:def|theorem|lemma|structure|class|abbrev|opaque|inductive|instance)\s+"
            r"([\w.]+)",
            line,
        )
        if opened:
            scopes.append(("namespace", opened[1]))
        elif section:
            scopes.append(("section", section[1]))
        elif closed:
            if not scopes:
                raise ValueError("unmatched end in declaration inventory")
            label = closed[1]
            kind, scope = scopes[-1]
            if label is not None and scope != label:
                raise ValueError("mismatched end in declaration inventory")
            scopes.pop()
        elif declaration:
            name = declaration[1]
            if name.startswith("_root_."):
                names.add(name.removeprefix("_root_."))
            elif not any(kind == "namespace" for kind, _ in scopes):
                raise ValueError("declaration outside an explicit namespace")
            else:
                namespace_names = [scope for kind, scope in scopes if kind == "namespace"]
                names.add(".".join([*namespace_names, name]))
    if scopes:
        raise ValueError("unclosed namespace in declaration inventory")
    return names


assert declaration_names(
    "namespace AlmostSchur\nnamespace Local\ntheorem a : True := by trivial\n"
    "lemma b : True := by trivial\nstructure S where x : Nat\n"
    "private lemma hidden : True := by trivial\nlocal instance : Inhabited Nat := inferInstance\n"
    "end Local\ndef c := 1\nend AlmostSchur\n"
) == {"AlmostSchur.Local.a", "AlmostSchur.Local.b", "AlmostSchur.Local.S",
      "AlmostSchur.c"}
assert declaration_names(
    "namespace AlmostSchur.Local\nabbrev c := Nat\n"
    "lemma _root_.External.d : True := by trivial\nend AlmostSchur.Local\n"
) == {"AlmostSchur.Local.c", "External.d"}
assert declaration_names(
    "namespace AlmostSchur\nsection Local\ntheorem a : True := by trivial\n"
    "end Local\nend AlmostSchur\n"
) == {"AlmostSchur.a"}
assert declaration_names(
    "namespace AlmostSchur\n/-- a section-looking comment\n"
    "section version of a proof -/\ntheorem a : True := by trivial\n"
    "end AlmostSchur\n"
) == {"AlmostSchur.a"}

expected = set()
for path in (ROOT / "AlmostSchur").rglob("*.lean"):
    source = path.read_text()
    if re.search(r"\b(sorry|admit|axiom)\b", source):
        raise ValueError("proof-hole token in " + str(path))
    expected.update(declaration_names(source))
own_count = len(expected)
expected |= VENDORED_ENDPOINTS
with tempfile.TemporaryDirectory(prefix="almost-schur-axioms-") as temp_dir:
    audit_path = Path(temp_dir) / "CheckAllProjectAxioms.lean"
    audit_path.write_text(
        "import AlmostSchur\n" +
        "\n".join(f"#print axioms {name}" for name in sorted(expected)) +
        "\n"
    )
    run = subprocess.run(["lake", "env", "lean", str(audit_path)], cwd=ROOT,
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
print(f"Checked all {own_count} public project declarations and "
      f"{len(VENDORED_ENDPOINTS)} vendored endpoints; four negative controls rejected.")
