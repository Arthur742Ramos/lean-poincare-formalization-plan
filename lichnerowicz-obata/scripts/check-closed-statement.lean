import LichnerowiczObata.ClosedStatement

/-! Check the compiled body, not just textual names. All mathematical data must
come from Mathlib; only proposition-valued compiler-generated local proof
helpers may remain. Comparator uses proof irrelevance for those proofs, while
comparing the complete definition body and every hypothesis. -/

open Lean Elab Command

private def candidateModule (name : Name) : Bool :=
  ["LichnerowiczObata", "AlmostSchur", "RellichKondrachov"].any
    (fun prefix => name.toString.startsWith prefix)

run_elab do
  let env ← getEnv
  let root := `LichnerowiczObataEntry.Geometry.completeStatement
  let some (.defnInfo info) := env.find? root
    | throwError "missing independently compared definition"
  unless info.type == .sort .zero do
    throwError "selected definition must have the closed type Prop"
  let mut proofs := 0
  for name in info.value.getUsedConstants do
    let some idx := env.getModuleIdxFor? name
      | throwError "missing defining module for {name}"
    let mod := env.header.moduleNames[idx]!
    if candidateModule mod then
      unless mod == `LichnerowiczObata.ClosedStatement &&
          name.toString.startsWith (root.toString ++ "._proof_") do
        throwError "unchecked candidate data reference: {name} from {mod}"
      let some (.thmInfo _) := env.find? name
        | throwError "candidate helper is not a proof: {name}"
      proofs := proofs + 1
  logInfo m!"Closed statement boundary passed: {info.value.getUsedConstants.size} body constants, {proofs} generated proofs, no unchecked candidate data."
