import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroup

/-!
# Hölder composition lemmas (Point 4 PDE milestone)

This file proves the abstract analytic core needed for any nonlinearity in the
Duhamel formulation: **composition with a Lipschitz scalar function preserves
Hölder regularity with an explicit constant**.

## Mathematical content

The Ricci–DeTurck nonlinearity (in a chart, after the second-order part is
absorbed into the heat propagator) is a smooth local function of the solution
and its derivatives. The estimates proved here are the soft analytic bridge:

1. `isHolderConst_comp_of_lipschitz`: If `F : ℝ → ℝ` is `L`-Lipschitz and `f`
   is `α`-Hölder with constant `H`, then `F ∘ f` is `α`-Hölder with constant
   `L * H`. This is the pointwise estimate underlying all composition results.

2. `holderBCF_comp`: Composition with a Lipschitz `F` defines a map
   `HolderBCF α n → HolderBCF α n`.

## Status and honest limitations

These lemmas are **genuine** (proved, no sorry) and form the analytic foundation
for a nonlinearity of the form `N(u) = F ∘ u`.

They do **not** by themselves give the genuine Ricci–DeTurck nonlinearity,
because:
- (a) The genuine nonlinearity is **tensorial** (acts on metric tensors, not
  scalar functions) and **second-order** (loses derivatives; does not preserve
  `C^α`). The Duhamel formulation absorbs the second-order part into the heat
  propagator `S`, leaving a first-order/quadratic remainder — but that remainder
  is still matrix-valued.
- (b) The `DuhamelData` instance is on the **little-Hölder** space
  (`LittleHolder n α`), and preserving the `IsGoodHolder` property under
  nonlinear composition requires a heat-semigroup commutator estimate
  (`‖S(t)(F∘f) - F∘f‖ → 0`) that is not proved here.
- (c) Global Lipschitz of `f ↦ F ∘ f` in the full Hölder norm needs
  `F ∈ C^{1,1}` (bounded second derivative); only the Hölder-constant
  preservation is proved here.

What these lemmas **do** provide: the exact pointwise Hölder estimate and the
well-definedness of composition on `HolderBCF`, which are the first two steps
of the nonlinearity analysis. The remaining steps (little-Hölder preservation,
`C^{1,1}` seminorm Lipschitz, tensorial extension) are future milestones.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Pointwise Hölder estimate for composition -/

/-- **Composition with a Lipschitz function preserves the Hölder estimate.**

If `F : ℝ → ℝ` is `LipschitzWith L F` and `f` satisfies the `α`-Hölder estimate
with constant `H`, then `F ∘ f` (as a bounded continuous function via
`BoundedContinuousFunction.comp`) satisfies the `α`-Hölder estimate with
constant `L * H`.

Proof: `|F(f a) - F(f b)| ≤ L * |f a - f b| ≤ L * (H * ∑ |(a-b) j|^α)`. -/
theorem isHolderConst_comp_of_lipschitz
    {f : BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {F : ℝ → ℝ} {L : ℝ≥0} {H : ℝ}
    (hF : LipschitzWith L F)
    (hf : IsHolderConst α f H) :
    IsHolderConst α (f.comp F hF) (L * H) := by
  -- Unpack the Hölder hypothesis
  obtain ⟨hH_nonneg, hH⟩ := hf
  -- The Lipschitz constant as a real is nonnegative
  have hL_nonneg : (0 : ℝ) ≤ L := L.coe_nonneg
  refine ⟨mul_nonneg hL_nonneg hH_nonneg, fun a b => ?_⟩
  -- Pointwise estimate
  have h1 : |f.comp F hF a - f.comp F hF b| ≤ L * |f a - f b| := by
    rw [BoundedContinuousFunction.comp_apply, BoundedContinuousFunction.comp_apply]
    -- `LipschitzWith.dist_le_mul`: `dist (F x) (F y) ≤ ↑L * dist x y` in ℝ.
    have hLip := hF.dist_le_mul (f a) (f b)
    -- For ℝ, `dist x y = |x - y|`.
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs] at hLip
    -- `hLip : |F (f a) - F (f b)| ≤ ↑L * |f a - f b|`; `↑L = (L : ℝ)`.
    have hLr : ((L : ℝ≥0) : ℝ) = L := rfl
    rw [hLr] at hLip
    exact hLip
  have h2 := hH a b
  -- Chain: |F(f a) - F(f b)| ≤ L * |f a - f b| ≤ L * (H * ∑ ...)
  calc |f.comp F hF a - f.comp F hF b|
      ≤ L * |f a - f b| := h1
    _ ≤ L * (H * ∑ j : Fin n, |(a - b) j| ^ α) := by
        apply mul_le_mul_of_nonneg_left h2 hL_nonneg
    _ = (L * H) * ∑ j : Fin n, |(a - b) j| ^ α := by ring

/-! ## 2. Composition as a map on Hölder space -/

/-- **Composition with a Lipschitz function maps `HolderBCF` to `HolderBCF`.**

Given `F : ℝ → ℝ` Lipschitz, the map `f ↦ F ∘ f` is well-defined on the Hölder
space. The Hölder constant of the composition is controlled by the Lipschitz
constant times the original Hölder constant. -/
noncomputable def holderBCF_comp
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    HolderBCF α n → HolderBCF α n :=
  fun f =>
    ⟨f.val.comp F hF,
     ⟨(L : ℝ) * (Classical.choose f.property),
      isHolderConst_comp_of_lipschitz (f := f.val) hF
        (Classical.choose_spec f.property)⟩⟩

/-- **Bridge lemma: the composed function inherits an explicit Hölder constant.**

For `F` `L`-Lipschitz and `f` Hölder with constant `H`, the underlying bounded
continuous function `(holderBCF_comp hF f).toBCF` satisfies `IsHolderConst`
with constant `L * H`.

This avoids definitional-unfolding issues: `isHolderConst_comp_of_lipschitz`
applied to `f.val` directly gives the result, since `(holderBCF_comp hF f).toBCF`
is definitionally `f.val.comp F hF`. -/
theorem isHolderConst_holderBCF_comp_toBCF
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (f : HolderBCF α n) {H : ℝ} (hH : IsHolderConst α f.toBCF H) :
    IsHolderConst α (holderBCF_comp hF f).toBCF ((L : ℝ) * H) :=
  isHolderConst_comp_of_lipschitz (f := f.val) hF hH

end AnalyticPDE
end RicciFlow
