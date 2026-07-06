module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckReactionAssembly

/-!
# Fiber-norm-free readout algebra for the tangent-bundle DeTurck reaction operator

The concrete tangent-bundle DeTurck reaction operator `deTurckReactionSectionMap` (fiber value
`(u, v) ↦ s (P u) v + s (P v) u`, shape `(s x).comp (P x) + ((s x).comp (P x)).flip`) acts on the
`BilinearFormBundle` continuous section space at `W := TangentSpace I`.  Its section-space Picard
coordinate bounds are ultimately controlled by the operator norm of the *model-fibre* trivialization
readout of its fibre value.

The existing readout estimates in `VectorBundle/RiemannianSection.lean` are phrased via
`ContinuousLinearMap.bilinearComp`, which demands `[SeminormedAddCommGroup]` on its argument spaces.
This module reproves the underlying readout algebra **fiber-norm-free**, phrasing the reaction through
the fibre-norm-free `ContinuousLinearMap.comp`/`ContinuousLinearMap.flip` (exactly what
`deTurckReactionSectionMap` uses).  The key structural facts are:

* the trivialization readout is additive/subtractive in the fibre value (`readout_add_nf`,
  `readout_sub_nf`), and
* it carries a fibre first-slot composition `B.comp Q` to the *model-fibre* composition of `readout B`
  with the endomorphism coordinate readout `inCoordinates F W F W x₀ x x₀ x Q` (`comp_readout_eq_nf`).

All are proved with only `AddCommGroup`/`Module`/`TopologicalSpace` fibre binders — the binders of the
`LocalCoordinatePositivity` section hosting `trivializationAt_bilinearFormBundle_apply_eq` — so at the
tangent bundle they use the canonical derived module and dodge the seminorm-derived-module diamond.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology NNReal

namespace Bundle

section NormFreeReadout

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

local instance bilFNormedAddCommGroupNf : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance bilFNormedSpaceNf : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **Norm-free port of `trivializationAt_bilinearFormBundle_readout_add`.** -/
theorem readout_add_nf
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) (b c : BilW x) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (b + c))).2
      = (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x b)).2
        + (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x c)).2 := by
  ext u v
  simp only [ContinuousLinearMap.add_apply]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (b + c) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx b u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx c u v]
  simp [ContinuousLinearMap.add_apply]

/-- **Norm-free port of `trivializationAt_bilinearFormBundle_readout_sub`.** -/
theorem readout_sub_nf
    (x₀ x : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) (b c : BilW x) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (b - c))).2
      = (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x b)).2
        - (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x c)).2 := by
  ext u v
  simp only [ContinuousLinearMap.sub_apply]
  rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (b - c) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx b u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx c u v]
  simp [ContinuousLinearMap.sub_apply]

/-- **The trivialization readout carries a fibre first-slot composition to a model-fibre
composition.**  For a bilinear-form fibre value `B : BilW x` composed on its first slot with a fibre
endomorphism `Q : W x →L[ℝ] W x` (`B.comp Q`, fibre value `(u, v) ↦ B (Q u) v`), the coordinate
readout is the model-fibre composition of `readout B` with the endomorphism coordinate readout
`inCoordinates F W F W x₀ x x₀ x Q`.  Fiber-norm-free (uses only
`trivializationAt_bilinearFormBundle_apply_eq` and `ContinuousLinearMap.inCoordinates_eq`), so it
elaborates at `W := TangentSpace I` through the canonical derived module. -/
theorem comp_readout_eq_nf
    {x : M} (B : BilW x) (Q : W x →L[ℝ] W x)
    (x₀ : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x (B.comp Q))).2
      = ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2).comp
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q) := by
  have keyQ : ∀ u : F,
      ((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q u)
        = Q (((trivializationAt F W x₀).continuousLinearEquivAt ℝ x hx).symm u) := by
    intro u
    rw [ContinuousLinearMap.inCoordinates_eq hx hx]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  ext u v
  rw [ContinuousLinearMap.comp_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx B
      (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q u) v,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx (B.comp Q) u v,
    ContinuousLinearMap.comp_apply, keyQ u]

end NormFreeReadout

end Bundle
