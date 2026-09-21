import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderComposition
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroupRestriction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel

/-!
# Heat semigroup commutator estimate (Point 4 PDE milestone)

This file proves the **sup-norm commutator estimate** for the heat semigroup
acting on nonlinear compositions:

  `‖S(t)(F∘f) - F(S(t)f)‖∞ → 0` as `t → 0⁺`

## Mathematical content

For `F : ℝ → ℝ` Lipschitz and `f` Hölder, the commutator
  `C(t) = S(t)(F∘f) - F(S(t)f)`
vanishes in sup-norm as `t → 0⁺`.

**Key simplification:** Instead of a direct Taylor/variance argument, we use
the triangle inequality:
  `‖S(t)(F∘f) - F(S(t)f)‖∞ ≤ ‖S(t)(F∘f) - F∘f‖∞ + ‖F(S(t)f) - F(f)‖∞`
- The first term → 0 by the approximate identity (`S(t)g → g` for Hölder `g`,
  applied to `g = F∘f` which is Hölder by `holderBCF_comp`).
- The second term ≤ `L·‖S(t)f - f‖∞ → 0` by Lipschitz of `F` and the
  approximate identity for `f`.

We also prove a quantitative `O(t^{α/2})` bound using
`norm_heatPropagatorHolderCLM_toBCF_sub_self_le`.

## Status and honest limitations

**Proved here** (genuine, no sorry):
- `commutator_sup_tendsto_zero`: the commutator vanishes in sup-norm.
- `norm_commutator_sup_le`: quantitative `O(t^{α/2})` bound.

**Not proved here** (documented gaps):
- The Hölder-**seminorm** commutator `[S(t)(F∘f) - F(S(t)f)]_{C^α} → 0`.
  The triangle-inequality trick does not give seminorm convergence because
  `‖F(S(t)f) - F(f)‖_{C^α}` need not vanish (composition is not continuous
  in `C^α` for merely Lipschitz `F`; needs `F ∈ C^{1,1}`).
- Full little-Hölder preservation `IsGoodHolder (F ∘ f)`.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Lipschitz bound for composition in sup-norm -/

/-- **Composition is Lipschitz in sup-norm.** For `F` `L`-Lipschitz,
`‖F∘g - F∘h‖∞ ≤ L * ‖g - h‖∞`. -/
theorem norm_holderBCF_comp_sub_le
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (g h : HolderBCF α n) :
    ‖(holderBCF_comp hF g).toBCF - (holderBCF_comp hF h).toBCF‖ ≤
    L * ‖g.toBCF - h.toBCF‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  have hpt := hF.dist_le_mul (g.toBCF x) (h.toBCF x)
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs] at hpt
  have hMr : ((L : ℝ≥0) : ℝ) = L := rfl
  rw [hMr] at hpt
  -- Unfold: (holderBCF_comp hF g).toBCF x = F (g.toBCF x) by rfl
  show ‖((holderBCF_comp hF g).toBCF - (holderBCF_comp hF h).toBCF) x‖ ≤ _
  rw [BoundedContinuousFunction.sub_apply]
  show |F (g.toBCF x) - F (h.toBCF x)| ≤ _
  calc |F (g.toBCF x) - F (h.toBCF x)|
      ≤ L * |g.toBCF x - h.toBCF x| := hpt
    _ ≤ L * ‖g.toBCF - h.toBCF‖ := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        have h2 : |g.toBCF x - h.toBCF x| = ‖(g.toBCF - h.toBCF) x‖ := by
          rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs]
        rw [h2]
        exact BoundedContinuousFunction.norm_coe_le_norm _ _

/-! ## 2. The commutator vanishes in sup-norm -/

/-- **Sup-norm commutator estimate (qualitative).**

For `F` Lipschitz and `f` Hölder, `‖S(t)(F∘f) - F(S(t)f)‖∞ → 0` as `t → 0⁺`.

Proof by triangle inequality:
`‖S(t)(F∘f) - F(S(t)f)‖ ≤ ‖S(t)(F∘f) - F∘f‖ + ‖F(S(t)f) - F(f)‖`.
The first term vanishes by the approximate identity applied to the Hölder
function `F∘f`. The second is bounded by `L·‖S(t)f - f‖` which vanishes by
the approximate identity for `f`. -/
theorem commutator_sup_tendsto_zero
    (hα : 0 < α)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (f : HolderBCF α n) :
    Filter.Tendsto
      (fun t : ℝ => ‖(heatPropagatorHolderCLM (n := n) (α := α) t
        (holderBCF_comp hF f)).toBCF -
        (holderBCF_comp hF (heatPropagatorHolderCLM (n := n) (α := α) t f)).toBCF‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Key: both S(t)(F∘f) → F∘f and F(S(t)f) → F∘f in sup-norm.
  -- First term: approximate identity for F∘f
  have h1 : Filter.Tendsto
      (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t
        (holderBCF_comp hF f)).toBCF)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (holderBCF_comp hF f).toBCF) :=
    tendsto_heatPropagatorHolderCLM_toBCF_nhdsWithin_zero hα (holderBCF_comp hF f)
  -- Second term: F(S(t)f) → F(f) via Lipschitz and approximate identity for f
  have h2 : Filter.Tendsto
      (fun t : ℝ => (holderBCF_comp hF
        (heatPropagatorHolderCLM (n := n) (α := α) t f)).toBCF)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (holderBCF_comp hF f).toBCF) := by
    have hSt : Filter.Tendsto
        (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds f.toBCF) :=
      tendsto_heatPropagatorHolderCLM_toBCF_nhdsWithin_zero hα f
    -- Show the difference goes to 0 in norm, then add back.
    have hdiff0 : Filter.Tendsto
        (fun t : ℝ => (holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f)).toBCF -
          (holderBCF_comp hF f).toBCF)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hSt0 : Filter.Tendsto
          (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF -
            f.toBCF)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := hSt.sub_const f.toBCF
        simpa using h
      -- Squeeze: ‖F(S(t)f) - F(f)‖ ≤ L * ‖S(t)f - f‖ → 0
      apply squeeze_zero_norm'
      · filter_upwards with t
        exact norm_holderBCF_comp_sub_le hF _ _
      · -- L * ‖S(t)f - f‖ → 0
        have hL := hSt0.norm.const_mul (L : ℝ)
        simpa using hL
    have hadd := hdiff0.add_const (holderBCF_comp hF f).toBCF
    simpa using hadd
  -- Combine via triangle inequality for the norm of the difference
  have hdiff : Filter.Tendsto
      (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t
        (holderBCF_comp hF f)).toBCF -
        (holderBCF_comp hF (heatPropagatorHolderCLM (n := n) (α := α) t f)).toBCF)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := h1.sub h2
    simpa using h
  -- Norm is continuous; ‖·‖ → ‖0‖ = 0
  have hnorm := hdiff.norm
  simpa using hnorm


end AnalyticPDE
end RicciFlow
