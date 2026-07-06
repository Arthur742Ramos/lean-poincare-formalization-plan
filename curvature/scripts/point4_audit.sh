#!/usr/bin/env bash
# =============================================================================
# Point 4 completion audit — the SOLE authoritative check for declaring
# roadmap point 4 ("Ricci-flow local existence & uniqueness") closed.
#
# A worker MUST NOT claim point 4 is done unless this script prints
# `VERDICT: POINT 4 CLOSED` and exits 0 (run WITHOUT --no-build).
#
# Five hard gates (all must pass):
#   G1  sorry-free      no sorry/admit/sorryAx/native_decide/decide!/axiom/opaque
#                       in the library source (comment- & string-stripped scan,
#                       immune to "sorry-free" prose false positives)
#   G2  build green     `lake build` succeeds
#   G3  unconditional   a hypothesis-free target theorem concluding in
#                       IntrinsicLocalExistenceUniquenessFamily exists, with NO
#                       restricting instance and NO assumed chart/closure data
#   G4  axiom-clean     `#print axioms <target>` ⊆ {propext,Classical.choice,
#                       Quot.sound} and contains no sorryAx
#   G5  faithful type   the target's elaborated type is the real point-4
#                       package and carries none of the forbidden binders
#
# Usage:
#   scripts/point4_audit.sh [--no-build] [--quiet] [--json PATH]
#     --no-build   skip G2 (fast; for status pulses that must not contend with
#                  the worker's build). Verdict is then "GATED (build not run)".
#     --json PATH  also write a machine-readable summary to PATH.
#
# The canonical target theorem base-name is read from
# scripts/point4_target.txt (default below). The worker may retarget by editing
# that file; the audit derives the fully-qualified name and module from source.
# =============================================================================
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_DIR" || { echo "cannot cd to repo dir"; exit 2; }

LIB="PoincareCurvature"
SCAN="python3 $SCRIPT_DIR/point4_scan.py"
TARGET_FILE="$SCRIPT_DIR/point4_target.txt"
DEFAULT_TARGET="intrinsicLocalExistenceUniquenessFamily_pointFour"
ALLOWED_AXIOMS=("propext" "Classical.choice" "Quot.sound")
FORBIDDEN='IsEmpty|Subsingleton|Module\.finrank|finrank|TimeDependentGeometricRicciDeTurckBanachChart|RicciDeTurckChartClosureData|ChartClosureData'

DO_BUILD=1
QUIET=0
JSON=""
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) DO_BUILD=0 ;;
    --quiet)    QUIET=1 ;;
    --json)     JSON="$2"; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
  shift
done

TARGET_BASE="$DEFAULT_TARGET"
[ -f "$TARGET_FILE" ] && TARGET_BASE="$(tr -d '[:space:]' < "$TARGET_FILE")"

say() { [ "$QUIET" -eq 1 ] || echo "$@"; }
hr()  { say "-------------------------------------------------------------------"; }

# gate result holders
g1="FAIL"; g2="SKIP"; g3="FAIL"; g4="FAIL"; g5="FAIL"
g1_note=""; g2_note=""; g3_note=""; g4_note=""; g5_note=""
SORRY_COUNT="?"

say "Point 4 completion audit  ($(date '+%Y-%m-%d %H:%M:%S %Z'))"
say "repo: $REPO_DIR"
say "target base-name: $TARGET_BASE"
hr

# --- G1: sorry / cheat free ------------------------------------------------
CHEATS_OUT="$($SCAN cheats "$LIB")"
SORRY_COUNT="$(printf '%s\n' "$CHEATS_OUT" | sed -n 's/^TOTAL //p')"
if [ "$SORRY_COUNT" = "0" ]; then
  g1="PASS"; g1_note="no sorry/admit/axiom/opaque/native_decide/decide! in $LIB/"
else
  g1="FAIL"; g1_note="$SORRY_COUNT real cheat token(s) found"
  say "G1 offending lines:"; printf '%s\n' "$CHEATS_OUT" | grep -v '^TOTAL' | sed 's/^/    /'
fi
say "G1 sorry-free    : $g1  ($g1_note)"

# --- G2: build green -------------------------------------------------------
if [ "$DO_BUILD" -eq 1 ]; then
  say "G2 building (lake build) ..."
  if lake build >/tmp/point4_build.log 2>&1; then
    g2="PASS"; g2_note="lake build succeeded"
  else
    g2="FAIL"; g2_note="lake build failed (see /tmp/point4_build.log)"
    say "    $(tail -5 /tmp/point4_build.log | sed 's/^/    /')"
  fi
else
  g2="SKIP"; g2_note="build not run (--no-build)"
fi
say "G2 build green   : $g2  ($g2_note)"

# --- locate the target -----------------------------------------------------
LOC="$($SCAN locate "$TARGET_BASE" "$LIB" 2>/dev/null)"
LOC_RC=$?
FQN=""; MODULE=""; SIG=""
if [ $LOC_RC -eq 0 ]; then
  FQN="$(printf '%s\n' "$LOC" | head -1 | cut -f1)"
  MODULE="$(printf '%s\n' "$LOC" | head -1 | cut -f2)"
  SIG="$(printf '%s\n' "$LOC" | sed -n '/^---SIG---$/,$p' | tail -n +2)"
fi

# --- G3: unconditional target exists & is not gated ------------------------
if [ $LOC_RC -ne 0 ]; then
  g3="FAIL"; g3_note="target theorem '$TARGET_BASE' not found in source (point 4 not yet constructed)"
else
  if ! printf '%s\n' "$SIG" | grep -q 'IntrinsicLocalExistenceUniquenessFamily'; then
    g3="FAIL"; g3_note="target does not conclude in IntrinsicLocalExistenceUniquenessFamily"
  elif printf '%s\n' "$SIG" | grep -Eq "$FORBIDDEN"; then
    g3="FAIL"; g3_note="target signature carries a forbidden restricting/assumed binder: $(printf '%s\n' "$SIG" | grep -Eo "$FORBIDDEN" | sort -u | tr '\n' ' ')"
  else
    g3="PASS"; g3_note="$FQN (hypothesis-free family, no restricting binder)"
  fi
fi
say "G3 unconditional : $g3  ($g3_note)"

# --- G4 & G5: axiom-clean + faithful type (Lean probe) ---------------------
if [ $LOC_RC -eq 0 ]; then
  PROBE="$REPO_DIR/_point4_audit_probe.lean"
  cat > "$PROBE" <<EOF
import $MODULE
#print axioms $FQN
set_option pp.all false in
#check @$FQN
EOF
  PROBE_OUT="$(lake env lean "$PROBE" 2>&1)"
  rm -f "$PROBE"

  if printf '%s\n' "$PROBE_OUT" | grep -qi 'unknownIdentifier\|unknown constant\|unknown identifier'; then
    g4="FAIL"; g4_note="target does not elaborate (unknown constant)"
    g5="FAIL"; g5_note="target does not elaborate"
  else
    # G4: axioms
    if printf '%s\n' "$PROBE_OUT" | grep -q 'sorryAx'; then
      g4="FAIL"; g4_note="depends on sorryAx (contains sorry)"
    else
      # isolate just the `#print axioms` block (axioms line through its `]`),
      # so the trailing `#check` type output can't contaminate the parse.
      AXBLOCK="$(printf '%s\n' "$PROBE_OUT" | sed -n '/depends on axioms:/,/]/p')"
      AX="$(printf '%s\n' "$AXBLOCK" | tr '\n' ' ' | sed -n 's/.*axioms:[^[]*\[\([^]]*\)\].*/\1/p')"
      if printf '%s\n' "$PROBE_OUT" | grep -qi 'does not depend on any axiom'; then
        g4="PASS"; g4_note="depends on no axioms"
      elif [ -n "$AX" ]; then
        bad=""
        IFS=',' read -ra AXARR <<< "$AX"
        for a in "${AXARR[@]}"; do
          a="$(echo "$a" | tr -d '[:space:]')"
          [ -z "$a" ] && continue
          ok=0; for allow in "${ALLOWED_AXIOMS[@]}"; do [ "$a" = "$allow" ] && ok=1; done
          [ $ok -eq 0 ] && bad="$bad $a"
        done
        if [ -z "$bad" ]; then g4="PASS"; g4_note="axioms: $AX"
        else g4="FAIL"; g4_note="disallowed axiom(s):$bad"; fi
      else
        g4="FAIL"; g4_note="could not parse axiom list from probe"
      fi
    fi
    # G5: faithful elaborated type
    TYPE="$(printf '%s\n' "$PROBE_OUT" | sed -n "/^@$(printf '%s' "$FQN" | sed 's/[.[\*^$]/\\&/g')/,\$p")"
    [ -z "$TYPE" ] && TYPE="$PROBE_OUT"
    if ! printf '%s\n' "$TYPE" | grep -q 'IntrinsicLocalExistenceUniquenessFamily'; then
      g5="FAIL"; g5_note="elaborated type is not the point-4 package"
    elif printf '%s\n' "$TYPE" | grep -Eq "$FORBIDDEN"; then
      g5="FAIL"; g5_note="elaborated type carries forbidden binder: $(printf '%s\n' "$TYPE" | grep -Eo "$FORBIDDEN" | sort -u | tr '\n' ' ')"
    else
      g5="PASS"; g5_note="type is the real family, no forbidden binder"
    fi
  fi
else
  g4_note="target missing"; g5_note="target missing"
fi
say "G4 axiom-clean   : $g4  ($g4_note)"
say "G5 faithful type : $g5  ($g5_note)"

hr

# --- verdict ---------------------------------------------------------------
CLOSED=1
[ "$g1" = "PASS" ] || CLOSED=0
[ "$g3" = "PASS" ] || CLOSED=0
[ "$g4" = "PASS" ] || CLOSED=0
[ "$g5" = "PASS" ] || CLOSED=0
if [ "$DO_BUILD" -eq 1 ]; then [ "$g2" = "PASS" ] || CLOSED=0; fi

if [ "$JSON" != "" ]; then
  cat > "$JSON" <<EOF
{
  "timestamp": "$(date '+%Y-%m-%dT%H:%M:%S%z')",
  "target_base": "$TARGET_BASE",
  "fqn": "$FQN",
  "sorry_count": "$SORRY_COUNT",
  "gates": {
    "G1_sorry_free":   {"status": "$g1", "note": "$g1_note"},
    "G2_build_green":  {"status": "$g2", "note": "$g2_note"},
    "G3_unconditional":{"status": "$g3", "note": "$g3_note"},
    "G4_axiom_clean":  {"status": "$g4", "note": "$g4_note"},
    "G5_faithful_type":{"status": "$g5", "note": "$g5_note"}
  },
  "verdict": "$([ $CLOSED -eq 1 ] && echo CLOSED || echo OPEN)",
  "build_run": $([ "$DO_BUILD" -eq 1 ] && echo true || echo false)
}
EOF
fi

if [ $CLOSED -eq 1 ] && [ "$DO_BUILD" -eq 1 ]; then
  say "VERDICT: POINT 4 CLOSED  ✅  (all five gates pass)"
  exit 0
elif [ $CLOSED -eq 1 ] && [ "$DO_BUILD" -eq 0 ]; then
  say "VERDICT: GATED — G1/G3/G4/G5 pass, but build not run (rerun without --no-build to certify)"
  exit 0
else
  say "VERDICT: POINT 4 OPEN  ❌  (see failing gates above)"
  exit 1
fi
