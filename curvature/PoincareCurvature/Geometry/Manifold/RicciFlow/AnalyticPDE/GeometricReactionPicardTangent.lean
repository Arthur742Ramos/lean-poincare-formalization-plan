module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionCoordBounds
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SectionSpacePicard

/-!
# Tangent-bundle DeTurck reaction: section-space Picard coordinate bounds and `IsPicardLindelof`

This module assembles the section-space Picard `hlip`/`hcenter` coordinate obligations for the concrete
**tangent-bundle** DeTurck reaction operator `deTurckReactionSectionMap` (fiber-norm-free, hence
formable at `W := TangentSpace I`), by connecting its model-fibre readout size bounds
(`GeometricReactionCoordBounds`) to the `coord` language of the section-space Picard bridge through a
**fiber-norm-free** coordinate-readout bridge.

The existing coordinate-readout bridge `bilinearFormBundle_coord_eq_trivializationAt_readout` demands
`[∀ x, SeminormedAddCommGroup (W x)]` (the Π-fibre-seminorm) as an explicit binder, which triggers the
derived-module-vs-norm-module diamond at `W := TangentSpace I`.  The bridge
`deTurckReactionSectionMap_coord_eq_readout` below reproves the identity **directly at the tangent
bundle**, where the section-space seminorm `SeminormedAddCommGroup (BilW x)` is supplied per-`x` by the
canonical tangent norm (a global instance) rather than a Π-binder, and the identity itself goes through
the fiber-norm-free `coord_apply` and the `LocalCoordinatePositivity` trivialization lemmas.
-/

@[expose] public noncomputable section

open Bundle RicciFlow
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := TM))

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

/-- **The tangent-bundle DeTurck reaction operator's coordinate readout equals its `trivializationAt`
fibre readout.**  For the concrete operator `deTurckReactionSectionMap … σ` (fiber-norm-free, formable
at `W := TangentSpace I`), the continuous-section-space coordinate
`(coord (deTurckReactionSectionMap … σ)).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the raw
fibre readout `(trivializationAt BilF BilW (x0 i) ⟨x, deTurckReactionSectionMap … σ x⟩).2`.  Proved at
`W := TangentSpace I` without any `[∀ x, SeminormedAddCommGroup (W x)]` Π-binder (which would trigger
the derived-module-vs-norm-module diamond): it combines the fiber-norm-free `coord_apply` with the
on-baseSet trivialization identity `continuousLinearMapAt = (e ⟨x, ·⟩).2` (`coe_linearMapAt_of_mem`),
the bilinear-form trivialization's linearity supplied by the fiber-norm-free
`trivializationAt_bilinearFormBundle_isLinear`.  This turns the operator's model-fibre readout size
bounds (`GeometricReactionCoordBounds`) into section-space Picard coordinate bounds. -/
theorem deTurckReactionSectionMap_coord_eq_readout
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP σ)).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1
            (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover hP σ x.1))).2 := by
  have hx : (x : M) ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i x.2
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  simp [equivCompatibleCoordFamilySubmodule, toSubtype,
    continuousSectionEquivCompatibleCoordFamilySubmodule,
    continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
    compatibleCoordFamilyOfSection, coordFamilyOfSection, coordContinuousMap,
    _root_.Bundle.Trivialization.linearMapAt_apply, hx,
    _root_.Bundle.Trivialization.continuousLinearMapAt_apply,
    _root_.Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
