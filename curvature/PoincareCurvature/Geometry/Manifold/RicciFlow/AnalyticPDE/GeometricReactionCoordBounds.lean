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

section SeminormReadout

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, SeminormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

local instance bilFNormedAddCommGroupSn : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance bilFNormedSpaceSn : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **The trivialization readout carries a fibre slot-flip to a model-fibre slot-flip.**  The
coordinate readout of `B.flip` (fibre value `(u, v) ↦ B v u`) is `(readout B).flip` on the model
fibre.  Uses only `trivializationAt_bilinearFormBundle_apply_eq`.  (Requires
`SeminormedAddCommGroup (W x)`, since `ContinuousLinearMap.flip` on the raw fibre is defined via its
operator norm; at `W := TangentSpace I` this is supplied by `instNormedAddCommGroupTangentSpace`.) -/
theorem flip_readout_eq_sn
    {x : M} (B : BilW x) (x₀ : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    (trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B.flip)).2
      = ((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2).flip := by
  ext u v
  rw [ContinuousLinearMap.flip_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx B v u,
    trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W) x₀ x hx B.flip u v,
    ContinuousLinearMap.flip_apply]

/-- **Readout size bound for the frozen-coefficient DeTurck reaction fibre value.**  The operator
norm of the model-fibre readout of `B.comp Q + (B.comp Q).flip` — the fibre value of the symmetrized
frozen-coefficient DeTurck derivation `(u, v) ↦ B (Q u) v + B (Q v) u` — is bounded by
`2 · ‖readout B‖ · ‖inCoordinates F W F W x₀ x x₀ x Q‖`.  Everything lands in the clean model fibre
(`.comp` size via `opNorm_comp_le`, `.flip` size via `norm_flip`), through the fiber-norm-free readout
identities `readout_add_nf`/`comp_readout_eq_nf` and the readout slot-flip `flip_readout_eq_sn`.  This
is the fibre content of the section-space Picard coordinate bound for `deTurckReactionSectionMap`. -/
theorem norm_deTurckReaction_readout_le_sn
    {x : M} (B : BilW x) (Q : W x →L[ℝ] W x)
    (x₀ : M) (hx : x ∈ (trivializationAt F W x₀).baseSet) :
    ‖(trivializationAt BilF BilW x₀
        (TotalSpace.mk' BilF x (B.comp Q + (B.comp Q).flip))).2‖
      ≤ 2 * ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q‖ := by
  rw [readout_add_nf (F := F) (W := W) x₀ x hx (B.comp Q) (B.comp Q).flip]
  refine (norm_add_le _ _).trans ?_
  rw [comp_readout_eq_nf (F := F) (W := W) B Q x₀ hx,
    flip_readout_eq_sn (F := F) (W := W) (B.comp Q) x₀ hx,
    comp_readout_eq_nf (F := F) (W := W) B Q x₀ hx, ContinuousLinearMap.opNorm_flip]
  have hb : ‖((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2).comp
        (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q)‖
      ≤ ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc ‖((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2).comp
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q)‖
        + ‖((trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2).comp
          (ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q)‖
      ≤ (‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q‖)
        + (‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2‖
            * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q‖) := add_le_add hb hb
    _ = 2 * ‖(trivializationAt BilF BilW x₀ (TotalSpace.mk' BilF x B)).2‖
          * ‖ContinuousLinearMap.inCoordinates F W F W x₀ x x₀ x Q‖ := by ring

end SeminormReadout

end Bundle

namespace RicciFlow

open Bundle
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization

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
set_option maxHeartbeats 1000000

/-- **The tangent-bundle DeTurck reaction operator's trivialization readout splits.**  At every base
point `x` in a trivializing set, the coordinate readout of the concrete operator value
`deTurckReactionSectionMap … σ x = (σ x).comp (P x) + ((σ x).comp (P x)).flip` equals the sum of the
readouts of its two summands.  This is the first connection of the *concrete* `deTurckReactionSectionMap`
operator (acting on the tangent-bundle `BilinearFormBundle` section space) to the fiber-norm-free
readout algebra, discharged through `Bundle.readout_add_nf` (which uses only the derived module, dodging
the seminorm-derived-module diamond that blocks the coordinate machinery at `TM`); the residual
`operator value = comp + flip` is definitional (`Pi.add_apply`). -/
theorem deTurckReactionSectionMap_readout_split
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M) (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x0 x : M) (hx : x ∈ (trivializationAt E TM x0).baseSet) :
    (trivializationAt BilF BilW x0
        (TotalSpace.mk' BilF x
          (deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover hP σ x))).2
      = (trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2
        + (trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (((σ x).comp (P x)).flip))).2 := by
  rw [← Bundle.readout_add_nf (F := E) (W := TM) x0 x hx
    ((σ x).comp (P x)) (((σ x).comp (P x)).flip)]
  rfl

/-- **The tangent-bundle DeTurck reaction operator's readout is bounded by twice the composition
readout.**  `‖readout (deTurckReactionSectionMap … σ x)‖ ≤ 2 · ‖readout ((σ x).comp (P x))‖`.  The
reaction's slot-flip summand has the *same* model-fibre readout norm as the composition summand
(`readout B.flip = (readout B).flip`, an operator-norm isometry `opNorm_flip`), and the two combine by
the triangle inequality.  The flip-readout identity is discharged fiber-norm-free at `TM` by pushing the
readout through `trivializationAt_bilinearFormBundle_apply_eq` on both sides and closing the residual
slot-swap by definitional `flip_apply` (`rfl`) — sidestepping the `ContinuousLinearMap.flip` instance
diamond that blocks a direct `rw`.  This reduces the concrete reaction operator's readout size to the
readout size of `(σ x).comp (P x)` alone. -/
theorem deTurckReactionSectionMap_readout_norm_le_two_comp
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M) (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x0 x : M) (hx : x ∈ (trivializationAt E TM x0).baseSet) :
    ‖(trivializationAt BilF BilW x0
        (TotalSpace.mk' BilF x
          (deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover hP σ x))).2‖
      ≤ 2 * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2‖ := by
  have hflip : (trivializationAt BilF BilW x0
        (TotalSpace.mk' BilF x (((σ x).comp (P x)).flip))).2
      = ((trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2).flip := by
    ext u v
    show (trivializationAt BilF BilW x0
          (TotalSpace.mk' BilF x (((σ x).comp (P x)).flip))).2 u v
        = (trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2 v u
    rw [Bundle.trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx
        (((σ x).comp (P x)).flip) u v,
      Bundle.trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx
        ((σ x).comp (P x)) v u]
    rfl
  rw [deTurckReactionSectionMap_readout_split et Kc hKc Ko hKo hKoEq hcover hP σ x0 x hx]
  refine (norm_add_le
    ((trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2)
    ((trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (((σ x).comp (P x)).flip))).2)).trans ?_
  rw [hflip, ContinuousLinearMap.opNorm_flip]
  linarith [norm_nonneg ((trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2)]

/-- **The reaction operator readout obeys the section-space Picard coordinate size bound, given a
composition-readout bound.**  If the composition readout is controlled by
`‖readout ((σ x).comp (P x))‖ ≤ Kp · ‖readout (σ x)‖` (the fibre content supplied by the frozen
endomorphism coefficient `P`'s coordinate size), then the concrete `deTurckReactionSectionMap` operator
readout obeys `‖readout (deTurckReactionSectionMap … σ x)‖ ≤ 2 · Kp · ‖readout (σ x)‖` — the
`K = 2·Kp` shape of the section-space Picard `hlip`/`hcenter` fibre content, phrased so the
composition-readout bound (which references the endomorphism coordinate readout) is provided by the
caller at a site where those coordinates elaborate. -/
theorem deTurckReactionSectionMap_readout_norm_le_of_comp_bound
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M) (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover)
    (x0 x : M) (hx : x ∈ (trivializationAt E TM x0).baseSet)
    (Kp : ℝ) (hKp : 0 ≤ Kp)
    (hcomp : ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2‖
        ≤ Kp * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (σ x))).2‖) :
    ‖(trivializationAt BilF BilW x0
        (TotalSpace.mk' BilF x
          (deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover hP σ x))).2‖
      ≤ 2 * Kp * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (σ x))).2‖ := by
  refine (deTurckReactionSectionMap_readout_norm_le_two_comp
    et Kc hKc Ko hKo hKoEq hcover hP σ x0 x hx).trans ?_
  calc 2 * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x ((σ x).comp (P x)))).2‖
      ≤ 2 * (Kp * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (σ x))).2‖) := by
        exact mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = 2 * Kp * ‖(trivializationAt BilF BilW x0 (TotalSpace.mk' BilF x (σ x))).2‖ := by ring

end RicciFlow
