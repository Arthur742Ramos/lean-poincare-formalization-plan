#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_file in \
  lean-toolchain lake-manifest.json lakefile.toml formalization.yaml \
  Challenge.lean Solution.lean comparator.json; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

python3 - "$repository_root" <<'PY'
import json
import hashlib
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
repo_root = pathlib.Path(
    subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], cwd=root, text=True
    ).strip()
)
lakefiles = [
    name for name in ("lakefile.toml", "lakefile.lean")
    if (root / name).exists()
]
if lakefiles != ["lakefile.toml"]:
    raise SystemExit(f"error: expected exactly lakefile.toml, found {lakefiles}")

license_pattern = re.compile(
    r"^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$", re.I
)
licenses = [
    path for path in repo_root.iterdir()
    if path.is_file() and not path.is_symlink() and license_pattern.fullmatch(path.name)
]
if len(licenses) != 1:
    raise SystemExit(f"error: expected exactly one root license, found {licenses}")
expected_license_sha256 = "5f3751276afe718ffa78ec1fc61490d4185712554bcb6a90059416dc424ce9a6"
actual_license_sha256 = hashlib.sha256(licenses[0].read_bytes()).hexdigest()
if actual_license_sha256 != expected_license_sha256:
    raise SystemExit(
        "error: root LICENSE is not the canonical Apache-2.0 text with the "
        "project copyright notice"
    )

expected_mathlib_revision = "db584cd6d46c92f209a44c0f1c829460d327499d"
manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
mathlib = next(
    (package for package in manifest.get("packages", [])
     if package.get("name") == "mathlib"),
    None,
)
if mathlib is None or any(
    mathlib.get(field) != expected_mathlib_revision
    for field in ("rev", "inputRev")
):
    raise SystemExit(
        "error: Mathlib must be pinned to canonical master ancestor "
        f"{expected_mathlib_revision}"
    )

artifact_suffixes = {
    ".a", ".bc", ".dll", ".dylib", ".ilean", ".ir", ".o", ".obj",
    ".olean", ".so", ".trace",
}
snapshot_bytes = 0
for path in repo_root.rglob("*"):
    relative = path.relative_to(repo_root)
    if any(part in {".cache", ".git", ".lake"} for part in relative.parts):
        continue
    if path.is_symlink():
        raise SystemExit(f"error: Palomar snapshot contains a symlink: {relative}")
    if path.is_file():
        if path.suffix in artifact_suffixes or path.name.endswith(
            (".olean.private", ".olean.server")
        ):
            raise SystemExit(f"error: compiled artifact is in the snapshot: {relative}")
        snapshot_bytes += path.stat().st_size
if snapshot_bytes > 500 * 1024 * 1024:
    raise SystemExit(
        f"error: Palomar snapshot is {snapshot_bytes} bytes, above the 500 MiB limit"
    )

challenge = root / "Challenge.lean"
challenge_text = challenge.read_text(encoding="utf-8")
if challenge.stat().st_size > 100 * 1024 or len(challenge_text.splitlines()) > 1000:
    raise SystemExit("error: Challenge.lean exceeds the 100 KiB or 1,000-line cap")
imports = [
    line.split()[1]
    for line in challenge_text.splitlines()
    if line.startswith("import ")
]
if not imports or any(not module.startswith("Mathlib.") for module in imports):
    raise SystemExit(f"error: Challenge.lean imports outside Mathlib: {imports}")
challenge_holes = len(re.findall(r"^\s*sorry\s*$", challenge_text, re.MULTILINE))
if challenge_holes != 7:
    raise SystemExit(
        f"error: expected seven deliberate Challenge theorem holes, found {challenge_holes}"
    )

try:
    comparator = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    raise SystemExit(f"error: comparator.json is invalid: {error}")
expected_theorems = [
    "PoincareCurvature.Palomar.parabolicDistance_dilation",
    "PoincareCurvature.Palomar.parabolicClosedBall_zero_mapsTo_dilation",
    "PoincareCurvature.Palomar.parabolicBall_exists_finset_cover_closedBall_subset_open_of_isCompact",
    "PoincareCurvature.Palomar.parabolicC0AlphaWith_comp_parabolicDistanceLe",
    "PoincareCurvature.Palomar.parabolicC0AlphaWith_inv_sub_inv",
    "PoincareCurvature.Palomar.parabolicC0AlphaOn_of_finset_parabolicBall_cover_closedBall",
    "PoincareCurvature.Palomar.parabolicC0AlphaOn_inverse_difference_of_finset_parabolicBall_cover_closedBall",
]
expected_definitions = [
    "RicciFlow.AnalyticPDE.parabolicDistance",
    "RicciFlow.AnalyticPDE.parabolicBall",
    "RicciFlow.AnalyticPDE.parabolicClosedBall",
    "RicciFlow.AnalyticPDE.ParabolicHolderWith",
    "RicciFlow.AnalyticPDE.ParabolicBoundedWith",
    "RicciFlow.AnalyticPDE.ParabolicC0AlphaWith",
    "RicciFlow.AnalyticPDE.ParabolicC0AlphaOn",
    "RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.invSubBoundConst",
    "RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.invSubHolderConst",
]
if comparator.get("challenge_module") != "Challenge":
    raise SystemExit("error: comparator challenge_module must be Challenge")
if comparator.get("solution_module") != "Solution":
    raise SystemExit("error: comparator solution_module must be Solution")
if comparator.get("theorem_names") != expected_theorems:
    raise SystemExit("error: comparator theorem surface does not match corrected Submission 04")
if comparator.get("definition_names") != expected_definitions:
    raise SystemExit("error: auditable definition surface does not match corrected Submission 04")
if comparator.get("enable_nanoda") is not True:
    raise SystemExit("error: comparator.json must enable NanoDa")
if not set(comparator.get("permitted_axioms", [])) <= {
    "propext", "Quot.sound", "Classical.choice"
}:
    raise SystemExit("error: comparator.json contains an unsupported axiom")

solution = (root / "Solution.lean").read_text(encoding="utf-8")
if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)", solution):
    raise SystemExit("error: Solution.lean contains a proof placeholder")
if re.search(r"^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: Solution.lean declares an axiom or unsafe definition")

source_root = root / "PoincareCurvature"
for path in sorted(source_root.rglob("*.lean")):
    source = path.read_text(encoding="utf-8")
    if re.search(r"^\s*(axiom|unsafe)\b", source, re.MULTILINE):
        raise SystemExit(
            f"error: axiom or unsafe declaration found in {path.relative_to(root)}"
        )
    if re.search(r"\bsorryAx\b", source):
        raise SystemExit(f"error: sorryAx found in {path.relative_to(root)}")

dependencies = subprocess.check_output(
    ["lake", "env", "lean", "--src-deps", "Challenge.lean"],
    cwd=root,
    text=True,
).splitlines()
for dependency in dependencies:
    if "/src/lean/" not in dependency and "/.lake/packages/mathlib/" not in dependency:
        raise SystemExit(
            f"error: Challenge import closure contains a non-Mathlib source: {dependency}"
        )

solution_dependencies = subprocess.check_output(
    ["lake", "env", "lean", "--src-deps", "Solution.lean"],
    cwd=root,
    text=True,
).splitlines()
for dependency in solution_dependencies:
    if all(
        marker not in dependency
        for marker in ("/src/lean/", "/.lake/packages/mathlib/", "/PoincareCurvature/")
    ):
        raise SystemExit(
            f"error: Solution import closure contains an unexpected source: {dependency}"
        )

print(
    f"Palomar package shape passed: {snapshot_bytes} snapshot bytes; "
    f"Challenge {challenge.stat().st_size} bytes"
)
PY

ruby -ryaml - "$repository_root/formalization.yaml" <<'RUBY'
path = ARGV.fetch(0)
data = YAML.safe_load(File.read(path), aliases: false)
abort "error: formalization.yaml must be a mapping" unless data.is_a?(Hash)
abort "error: metadata version must be v0.4" unless data["version"] == "v0.4"
project = data["project"]
abort "error: project metadata is incomplete" unless project.is_a?(Hash)
abort "error: project.name is missing" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "error: project.description is missing" unless project["description"].is_a?(String) && !project["description"].strip.empty?
abort "error: project.authors is empty" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "error: project.responsible_maintainers is empty" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "error: project.license must be Apache-2.0" unless project["license"] == "Apache-2.0"
classification = data["classification"]
abort "error: classification is incomplete" unless classification.is_a?(Hash) && classification["arxiv"].is_a?(Array) && classification["msc2020"].is_a?(Array)
abort "error: sources must be nonempty" unless data["sources"].is_a?(Array) && !data["sources"].empty?
status = data["status"]
abort "error: status is incomplete" unless status.is_a?(Hash) && status["scope"].is_a?(String) && status["sorry_count"].is_a?(Integer)
automation = data["automation"]
abort "error: automation metadata is incomplete" unless automation.is_a?(Hash) && automation["methods"].is_a?(Array) && !automation["methods"].empty?
review = data["review"]
abort "error: review metadata is incomplete" unless review.is_a?(Hash) && review["status"].is_a?(String)
puts "formalization.yaml shape passed."
RUBY

lake build
lake build Challenge Solution
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean --src-deps Solution.lean
lake env lean /dev/stdin <<'EOF'
import Solution
#print axioms PoincareCurvature.Palomar.parabolicDistance_dilation
#print axioms PoincareCurvature.Palomar.parabolicClosedBall_zero_mapsTo_dilation
#print axioms PoincareCurvature.Palomar.parabolicBall_exists_finset_cover_closedBall_subset_open_of_isCompact
#print axioms PoincareCurvature.Palomar.parabolicC0AlphaWith_comp_parabolicDistanceLe
#print axioms PoincareCurvature.Palomar.parabolicC0AlphaWith_inv_sub_inv
#print axioms PoincareCurvature.Palomar.parabolicC0AlphaOn_of_finset_parabolicBall_cover_closedBall
#print axioms PoincareCurvature.Palomar.parabolicC0AlphaOn_inverse_difference_of_finset_parabolicBall_cover_closedBall
EOF

git diff --check
echo "Submission 04 local checks passed."
