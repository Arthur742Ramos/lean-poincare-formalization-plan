module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOneDeTurck

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Rank-one Levi-Civita-background and gauge-reduced Ricci-DeTurck theorem packages

This thin extension module mirrors the empty-manifold and subsingleton-tangent constructors in
`GaugeReduction.lean` (`leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty`
and `gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent`) for the
rank-one tangent-fiber case. The mathematical input is
`intrinsicLocalExistenceUniqueness_of_finrank_le_one` from `LocalExistence.lean` together with
the existing intrinsic-to-Levi-Civita-background and intrinsic-to-gauge-reduced conversions
from `GaugeReduction.lean`.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

section Compact

variable [CompactSpace M]

/-- Smooth Levi-Civita-background DeTurck theorem package on compact manifolds whose tangent
fibers all have real dimension at most one. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_finrank_le_one (I := I) (M := M) hfin ivp)
    |>.toLeviCivitaBackgroundIntrinsicDeTurck

/-- The theorem-family version of
`leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
      (I := I) (M := M) hfin ivp

/-- Model-space version of
`leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

/-- The theorem-family version of
`leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one`. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)] :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
      (I := I) (M := M) ivp

/-- Gauge-reduced intrinsic Ricci-flow theorem package on compact manifolds whose tangent
fibers all have real dimension at most one, obtained through the identity `C³` gauge from the
direct rank-one stationary-Ricci-flat existence proof. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_finrank_le_one (I := I) (M := M) hfin ivp)
    |>.toGaugeReduced_viaIdentityGauge

/-- The theorem-family version of
`gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
      (I := I) (M := M) hfin ivp

/-- Model-space version of
`gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

/-- The theorem-family version of
`gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one`. -/
noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)] :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_finrank_model_le_one
      (I := I) (M := M) ivp

end Compact

end RicciFlow
