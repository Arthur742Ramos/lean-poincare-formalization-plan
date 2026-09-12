import Challenge

/-! Audit the compiled definition body rather than relying on textual names.
Every mathematical datum in the Comparator-selected statement must come from
Mathlib. Only proposition-valued proof helpers generated while elaborating the
closed definition may remain in the candidate module. -/

open Lean Elab Command

private def candidateModule (name : Name) : Bool :=
  ["Challenge", "RicciScalarComparison", "PoincareCurvature"].any
    (fun modulePrefix => name.toString.startsWith modulePrefix)

run_elab do
  let env ← getEnv
  let root := `EinsteinComparisonEntry.completeStatement
  let some (.defnInfo info) := env.find? root
    | throwError "missing independently compared definition"
  unless info.type == .sort .zero do
    throwError "selected definition must have the closed type Prop"
  let mut proofs : Nat := 0
  for name in info.value.getUsedConstants do
    let some idx := env.getModuleIdxFor? name
      | throwError "missing defining module for {name}"
    let mod := env.header.moduleNames[idx]!
    if candidateModule mod then
      unless mod == `Challenge &&
          name.toString.contains "._proof_" do
        throwError "unchecked candidate data reference: {name} from {mod}"
      let some (.thmInfo _) := env.find? name
        | throwError "candidate helper is not a proof: {name}"
      proofs := proofs + 1
  logInfo m!"Closed statement boundary passed: {info.value.getUsedConstants.size} body constants, {proofs} generated proofs, no unchecked candidate data."
