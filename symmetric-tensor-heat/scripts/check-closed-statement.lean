import TensorHeatChallenge

/-! Audit the compiled statement closure. Every mathematical body must be
inside `completeStatement`; the only reachable Challenge declarations allowed
are compiler-generated proposition proofs. -/

open Lean Elab Command

run_elab do
  let env ← getEnv
  let root := `SymmetricTensorHeatEntry.completeStatement
  let some (.defnInfo info) := env.find? root
    | throwError "missing independently compared completeStatement"
  unless info.type == .sort .zero do
    throwError "selected definition must have the closed type Prop"
  let mut generatedProofs : Nat := 0
  let mut unexpected : Array Name := #[]
  for name in info.value.getUsedConstants do
    let some idx := env.getModuleIdxFor? name
      | throwError "missing defining module for {name}"
    let mod := env.header.moduleNames[idx]!
    if mod.toString.startsWith "PoincareCurvature" then
      throwError "proof-development reference in Challenge statement: {name}"
    if mod == `TensorHeatChallenge then
      if name.toString.contains "._proof_" then
        let some (.thmInfo _) := env.find? name
          | throwError "generated helper is not a proof: {name}"
        generatedProofs := generatedProofs + 1
      else
        unexpected := unexpected.push name
  unless unexpected.isEmpty do
    throwError "candidate-defined data in compiled statement: {unexpected}"
  logInfo m!"Closed statement audit passed: {info.value.getUsedConstants.size} constants, {generatedProofs} generated proofs, no candidate-defined data or proof-development references."
