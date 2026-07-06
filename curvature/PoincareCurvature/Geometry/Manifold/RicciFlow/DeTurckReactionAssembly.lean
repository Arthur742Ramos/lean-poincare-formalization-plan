module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity
public import PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection

/-!
# Assembling the intrinsic DeTurck reaction operator on the section space

The intrinsic Ricci–DeTurck reaction term is the two-sided derivation
`intrinsicDeTurckCorrection g background t x u v = (g t).inner x (∇W u) v + (g t).inner x u (∇W v)`,
where `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` is the
covariant derivative of the intrinsic DeTurck vector field.  The frozen-coefficient section-space
representative of this operator is the bounded operator
`ContinuousSectionSpace.bilinearDerivationField` (built in `VectorBundle/RiemannianSection.lean`),
whose fiberwise action on a section `s` is `x ↦ s(P·, ·) + s(·, P·)` for a continuous
tangent-endomorphism section `P` (its defining identity is `bilinearDerivationField_apply_apply`).

This module supplies the **assembly identity** connecting the two at the fiber-value level: with the
frozen coefficient `P := ∇W`, the fiberwise two-sided derivation of any `ContinuousSectionSpace`
element `sMetric` that agrees pointwise with the metric `(g t).inner` reproduces exactly the geometric
`intrinsicDeTurckCorrectionSection`.  Composed with `bilinearDerivationField_apply_apply` this is the
DeTurck half of the chart operator `A`'s `geometric` identification field: the abstract bounded
reaction operator and the concrete geometric DeTurck term coincide on the metric section.

The result is stated at the fiber-value level (the two-sided derivation applied to `sMetric`) rather
than through a formed `bilinearDerivationField` instance, because instantiating that operator at the
tangent bundle `W := TangentSpace I` triggers an instance diamond: the operator-norm size datum
`‖P x‖` needs `Norm (TangentSpace I x →L[ℝ] TangentSpace I x)`, which is only reachable through the
definitional equality `TangentSpace I x = E`, and it must moreover be mutually consistent with the
`FiberBundle`/`VectorBundle` tangent structure that the same operator demands.  The fiber-value form
here is exactly what such a formed operator evaluates to, so it is directly consumable by the chart
assembly once that instance datum is supplied at the construction site.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology
open PoincareCurvature.Bundle.Trivialization

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **The frozen-coefficient DeTurck reaction of the metric section is the geometric DeTurck
correction.**  Let `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` be
the covariant derivative of the intrinsic DeTurck vector field (the frozen endomorphism coefficient).
For any `ContinuousSectionSpace` element `sMetric` agreeing pointwise with the metric `(g t).inner`,
the fiberwise two-sided derivation
`x ↦ sMetric x (∇W x u) v + sMetric x u (∇W x v)` equals, at every base point and tangent pair,
the geometric `intrinsicDeTurckCorrectionSection g background t`.

This is the fiber-value content of applying the section-space reaction operator
`ContinuousSectionSpace.bilinearDerivationField` (whose fiberwise action is exactly this two-sided
derivation, `bilinearDerivationField_apply_apply`) with frozen coefficient `P := ∇W` to `sMetric`:
the abstract bounded reaction operator reproduces the concrete geometric Ricci–DeTurck reaction term
on the metric section, i.e. the DeTurck half of the chart operator `A`'s `geometric` field. -/
theorem metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (sMetric : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover)
    (hsMetric : ∀ (x : M) (u v : TM x), sMetric x u v = (g t).inner x u v)
    (x : M) (u v : TM x) :
    sMetric x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
      + sMetric x u
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)
      = intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x u v := by
  rw [hsMetric, hsMetric, intrinsicDeTurckCorrectionSection_apply,
    intrinsicDeTurckCorrection_apply]

end RicciFlow
