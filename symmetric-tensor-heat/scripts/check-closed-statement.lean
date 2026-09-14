import TensorHeatChallenge

/-! Audit the compiled statement closure. Candidate-local constants are limited
to the enumerated Mathlib-facing statement helpers, canonical structural
instances needed for iterated continuous-linear-map bundles, and generated
proofs. No proof-development constant may be reachable. -/

open Lean Elab Command

private def semanticHelpers : Array Name := #[
  `SymmetricTensorHeatEntry.IsInducedTwoTensorConnection,
  `SymmetricTensorHeatEntry.IsInducedThreeTensorConnection,
  `SymmetricTensorHeatEntry.connectionLaplacianApply,
  `SymmetricTensorHeatEntry.IsSymmetricSection,
  `SymmetricTensorHeatEntry.HasInitialTrace,
  `SymmetricTensorHeatEntry.HasTimeDerivative,
  `SymmetricTensorHeatEntry.SolvesTensorHeat,
  `SymmetricTensorHeatEntry.IsMetricCompatibleTangent,
  `SymmetricTensorHeatEntry.IsLeviCivita,
  `SymmetricTensorHeatEntry.parabolicDistance,
  `SymmetricTensorHeatEntry.HasParabolicC0AlphaNormLe,
  `SymmetricTensorHeatEntry.HasSpatialC2AlphaNormLe,
  `SymmetricTensorHeatEntry.HasParabolicC2AlphaNormLe
]

private def structuralHelpers : Array Name := #[
  `SymmetricTensorHeatEntry.challengeTwoModelNormedAddCommGroup,
  `SymmetricTensorHeatEntry.challengeTwoModelNormedSpace,
  `SymmetricTensorHeatEntry.challengeTwoFiberNormedAddCommGroup,
  `SymmetricTensorHeatEntry.challengeTwoFiberNormedSpace,
  `SymmetricTensorHeatEntry.challengeTwoTotalSpaceTopology,
  `SymmetricTensorHeatEntry.challengeTwoFiberBundle,
  `SymmetricTensorHeatEntry.challengeTwoVectorBundle,
  `SymmetricTensorHeatEntry.challengeThreeModelNormedAddCommGroup,
  `SymmetricTensorHeatEntry.challengeThreeModelNormedSpace,
  `SymmetricTensorHeatEntry.challengeThreeFiberNormedAddCommGroup,
  `SymmetricTensorHeatEntry.challengeThreeFiberNormedSpace,
  `SymmetricTensorHeatEntry.challengeThreeTotalSpaceTopology,
  `SymmetricTensorHeatEntry.challengeThreeFiberBundle,
  `SymmetricTensorHeatEntry.challengeThreeVectorBundle
]

run_elab do
  let env ← getEnv
  let root := `SymmetricTensorHeatEntry.completeStatement
  let some (.defnInfo info) := env.find? root
    | throwError "missing independently compared completeStatement"
  unless info.type == .sort .zero do
    throwError "selected definition must have the closed type Prop"
  let mut generatedProofs : Nat := 0
  let mut structural : Nat := 0
  let mut semantic : Nat := 0
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
      else if semanticHelpers.contains name then
        semantic := semantic + 1
      else if structuralHelpers.contains name then
        structural := structural + 1
      else
        throwError "unlisted candidate dependency in compiled statement: {name}"
  logInfo m!"Closed statement audit passed: {info.value.getUsedConstants.size} constants, {semantic} semantic helpers, {structural} canonical structures, {generatedProofs} generated proofs, no proof-development references."
