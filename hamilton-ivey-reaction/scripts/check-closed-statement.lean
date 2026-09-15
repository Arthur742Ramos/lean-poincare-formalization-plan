import Challenge

/-! Audit that the selected closed proposition contains no reachable
candidate-defined mathematical data. -/

open Lean Elab Command

run_elab do
  let env ← getEnv
  let root := `HamiltonIveyChallenge.completeStatement
  let some (.defnInfo info) := env.find? root
    | throwError "missing independently compared completeStatement"
  unless info.type == .sort .zero do
    throwError "selected definition must have the closed type Prop"
  let mut generatedProofs : Nat := 0
  for name in info.value.getUsedConstants do
    let some idx := env.getModuleIdxFor? name
      | throwError "missing defining module for {name}"
    let mod := env.header.moduleNames[idx]!
    if mod == `Challenge then
      if name.toString.contains "._proof_" then
        let some (.thmInfo _) := env.find? name
          | throwError "generated helper is not a proof: {name}"
        generatedProofs := generatedProofs + 1
      else
        throwError "candidate-defined mathematical data in compiled statement: {name}"
  logInfo m!"Closed statement audit passed: {info.value.getUsedConstants.size} constants, {generatedProofs} generated proofs, no candidate-defined mathematical data."
