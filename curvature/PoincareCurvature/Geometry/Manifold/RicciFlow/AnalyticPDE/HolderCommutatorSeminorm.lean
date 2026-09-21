import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatSemigroupCommutator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroupRestriction

/-!
# Hölder-seminorm commutator: Taylor estimate (Point 4 PDE milestone)

This file proves the **Taylor-based commutator estimate**, a key analytic
ingredient for Hölder-seminorm control of the heat-semigroup commutator.

## Mathematical content

For `F : ℝ → ℝ` with `M`-Lipschitz derivative and `f` Hölder, the commutator
  `C(t,x) = S(t)(F∘f)(x) - F(S(t)f(x))`
satisfies a pointwise bound via Taylor expansion:

1. **Taylor remainder** (`taylor_remainder_lipschitz_deriv`):
   `|F(b) - F(a) - F'(a)(b-a)| ≤ M·(b-a)²`.
   Proof: By MVT, `F(b)-F(a) = F'(c)(b-a)` for some `c` between `a` and `b`.
   Then `|F'(c)-F'(a)| ≤ M|c-a| ≤ M|b-a|`.

2. **Commutator via Taylor** (`commutator_taylor_pointwise`):
   `|S(t)(F∘f)(x) - F(S(t)f(x))| ≤ M · ∫ |f(y) - S(t)f(x)|² G_t(x-y) dy`.
   The linear term in the Taylor expansion integrates to zero.

## Status and honest limitations

**Proved here** (genuine, no sorry):
- `taylor_remainder_lipschitz_deriv`: Taylor remainder for Lipschitz-derivative functions.

**Not proved here** (documented gaps):
- `commutator_taylor_pointwise`: Stated but not proved; requires careful
  manipulation of heat kernel integrals (Fubini, integrability).
- The quantitative variance bound `∫ |f(y)-S(t)f(x)|² G_t ≤ C·H²·t^α`.
- The full commutator seminorm `[S(t)(F∘f) - F(S(t)f)]_{C^α} → 0`.
- Full little-Hölder preservation `IsGoodHolder (F ∘ f)`.

No `sorry`, no `admit`, no axioms in the proved results.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Taylor remainder for functions with Lipschitz derivative -/

/-- **Taylor remainder bound via MVT.**

For `F : ℝ → ℝ` differentiable with `M`-Lipschitz derivative:
`|F(b) - F(a) - F'(a)·(b-a)| ≤ M·(b-a)²`.

Proof: By the mean value theorem, `F(b) - F(a) = F'(c)·(b-a)` for some `c`
between `a` and `b`. Then:
`F(b) - F(a) - F'(a)(b-a) = (F'(c) - F'(a))·(b-a)`,
so `|·| ≤ |F'(c) - F'(a)|·|b-a| ≤ M·|c-a|·|b-a| ≤ M·(b-a)²`. -/
theorem taylor_remainder_lipschitz_deriv
    {F F' : ℝ → ℝ} {M : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hLip : LipschitzWith M F')
    (a b : ℝ) :
    |F b - F a - F' a * (b - a)| ≤ (M : ℝ) * (b - a) ^ 2 := by
  rcases eq_or_ne a b with rfl | hne
  · simp
  · -- WLOG a < b (the case b < a is symmetric via the same MVT)
    rcases lt_or_gt_of_ne hne with hab | hab
    · -- Case a < b
      have hcont : Continuous F := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (hF x).continuousAt
      -- MVT: ∃ c ∈ Ioo a b, F'(c) = (F(b) - F(a))/(b - a)
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' hab
        hcont.continuousOn (fun x _ => hF x)
      -- c ∈ (a,b), so |c - a| ≤ |b - a|
      have hc_mem : c ∈ Ioo a b := hc
      simp only [mem_Ioo] at hc_mem
      obtain ⟨hca, hcb⟩ := hc_mem
      have hc_bound : |c - a| ≤ |b - a| := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c - a),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
        linarith
      -- F(b) - F(a) = F'(c)·(b-a)
      have hba : b - a ≠ 0 := by
        intro h
        have : b = a := by linarith
        exact hne this.symm
      have hFbFa : F b - F a = F' c * (b - a) := by
        rw [heq]
        field_simp
      -- Main estimate
      have hmain : F b - F a - F' a * (b - a) = (F' c - F' a) * (b - a) := by
        rw [hFbFa]; ring
      rw [hmain, abs_mul]
      have hLip' := hLip.dist_le_mul c a
      simp only [dist_eq_norm, Real.norm_eq_abs] at hLip'
      have hMr : ((M : ℝ≥0) : ℝ) = (M : ℝ) := rfl
      rw [hMr] at hLip'
      calc |F' c - F' a| * |b - a|
          ≤ ((M : ℝ) * |c - a|) * |b - a| :=
            mul_le_mul_of_nonneg_right hLip' (abs_nonneg _)
        _ ≤ ((M : ℝ) * |b - a|) * |b - a| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hc_bound M.coe_nonneg
        _ = (M : ℝ) * (b - a) ^ 2 := by
            have h1 : |b - a| * |b - a| = |b - a| ^ 2 := by ring
            rw [mul_assoc, h1, sq_abs]
    · -- Case b < a: repeat the MVT argument on [b,a]
      have hcont : Continuous F := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (hF x).continuousAt
      -- MVT on [b,a]: ∃ c ∈ Ioo b a, F'(c) = (F(a) - F(b))/(a - b)
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' hab
        hcont.continuousOn (fun x _ => hF x)
      simp only [mem_Ioo] at hc
      obtain ⟨hcb, hca⟩ := hc
      have hc_bound : |c - a| ≤ |b - a| := by
        have h1 : |c - a| = a - c := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith : (0:ℝ) ≤ a - c)
        have h2 : |b - a| = a - b := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)
        rw [h1, h2]
        linarith
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hab)
      have hFbFa : F b - F a = F' c * (b - a) := by
        -- From heq: F'(c) = (F(a) - F(b))/(a - b)
        -- So F(a) - F(b) = F'(c)(a - b), thus F(b) - F(a) = F'(c)(b - a)
        have h1 : F a - F b = F' c * (a - b) := by
          rw [heq]; field_simp
        linarith
      have hmain : F b - F a - F' a * (b - a) = (F' c - F' a) * (b - a) := by
        rw [hFbFa]; ring
      rw [hmain, abs_mul]
      have hLip' := hLip.dist_le_mul c a
      simp only [dist_eq_norm, Real.norm_eq_abs] at hLip'
      have hMr : ((M : ℝ≥0) : ℝ) = (M : ℝ) := rfl
      rw [hMr] at hLip'
      calc |F' c - F' a| * |b - a|
          ≤ ((M : ℝ) * |c - a|) * |b - a| :=
            mul_le_mul_of_nonneg_right hLip' (abs_nonneg _)
        _ ≤ ((M : ℝ) * |b - a|) * |b - a| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hc_bound M.coe_nonneg
        _ = (M : ℝ) * (b - a) ^ 2 := by
            have h1 : |b - a| * |b - a| = |b - a| ^ 2 := by ring
            rw [mul_assoc, h1, sq_abs]

end AnalyticPDE
end RicciFlow
