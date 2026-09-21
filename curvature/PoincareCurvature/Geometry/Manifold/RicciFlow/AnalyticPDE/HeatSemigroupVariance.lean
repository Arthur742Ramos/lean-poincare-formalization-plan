import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelClassical

/-!
# Heat semigroup variance bound (Point 4 PDE milestone)

This file proves the **variance bound** for the heat semigroup, a key analytic
ingredient for the Taylor-based commutator estimate.

## Mathematical content

For `w` Hölder with constant `H`, the "variance"
  `Var_t(w)(x) = ∫ |w y - S(t)w(x)|² G_t(x-y) dy`
satisfies:
  `Var_t(w)(x) ≤ 2·n²·H²·t^α·(gaussianAbsMoment(2α) + (gaussianAbsMoment α)²)`

## Proof strategy

1. **Triangle inequality**: `|w y - a| ≤ |w y - w x| + |w x - a|` where `a = S(t)w(x)`.
2. **Square**: `(u+v)² ≤ 2u² + 2v²`.
3. **Hölder bound**: `|w y - w x|² ≤ H²·n·∑_j |y_j - x_j|^{2α}`.
4. **Gaussian moments**: `∫ |y_j - x_j|^{2α} G_t(x-y) dy = (√t)^{2α}·gaussianAbsMoment(2α)`.
5. **Approximate identity**: `|w x - S(t)w(x)|² ≤ H²·n²·(√t)^{2α}·(gaussianAbsMoment α)²`.

## Status and honest limitations

**Proved here** (genuine, no sorry):
- `sq_add_le_two_mul_sq_add`: `(a+b)² ≤ 2a² + 2b²`.
- `holder_sq_bound`: Pointwise squared Hölder bound.

**Not proved here** (documented gaps):
- The full variance integral bound (requires careful Fubini/integrability).
- The pointwise Taylor commutator.
- The Hölder-seminorm commutator.

No `sorry`, no `admit`, no axioms in the proved results.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Auxiliary lemmas -/

/-- `(a + b)² ≤ 2a² + 2b²` for reals. -/
theorem sq_add_le_two_mul_sq_add (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Squared Hölder bound: if `|w a - w b| ≤ H * ∑_j |(a-b) j|^α`, then
    `|w y - w x|² ≤ H² * n * ∑_j |(y-x) j|^{2α}`. -/
theorem holder_sq_bound
    {w : (Fin n → ℝ) → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α)
    (y x : Fin n → ℝ) :
    |w y - w x| ^ 2 ≤ H ^ 2 * (Fintype.card (Fin n) : ℝ) *
      ∑ j : Fin n, |(y - x) j| ^ (2 * α) := by
  have hh := hholder y x
  -- Step 1: |w y - w x|² ≤ (H * ∑ |...|^α)²
  -- Since both sides are nonnegative, suffices to show |w y - w x| ≤ H * ∑ ...
  have hnn : 0 ≤ H * ∑ j : Fin n, |(y - x) j| ^ α := by
    apply mul_nonneg hH
    apply Finset.sum_nonneg
    intro j _
    positivity
  have h1 : |w y - w x| ^ 2 ≤ (H * ∑ j : Fin n, |(y - x) j| ^ α) ^ 2 := by
    -- Both sides nonnegative; use nlinarith with the hypothesis
    nlinarith [hh, hnn, abs_nonneg (w y - w x), sq_nonneg (|w y - w x| - H * ∑ j : Fin n, |(y - x) j| ^ α)]
  -- Step 2: (H * S)² = H² * S²
  rw [mul_pow] at h1
  -- Step 3: S² ≤ n * ∑ (u_j)² by Cauchy-Schwarz
  -- (∑ u_j)² ≤ n * ∑ u_j²
  have hcs : (∑ j : Fin n, |(y - x) j| ^ α) ^ 2 ≤
      (Fintype.card (Fin n) : ℝ) * ∑ j : Fin n, (|(y - x) j| ^ α) ^ 2 := by
    -- Cauchy-Schwarz: (∑ 1 * u_j)² ≤ (∑ 1²) * (∑ u_j²)
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun j : Fin n => |(y - x) j| ^ α)
    simpa using h
  -- Step 4: (|...|^α)² = |...|^{2α}
  have hpow : ∀ j : Fin n, (|(y - x) j| ^ α) ^ 2 = |(y - x) j| ^ (2 * α) := by
    intro j
    -- (|z|^α)² = |z|^{α*2} = |z|^{2α}
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hsum : ∑ j : Fin n, (|(y - x) j| ^ α) ^ 2 =
      ∑ j : Fin n, |(y - x) j| ^ (2 * α) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hpow j
  rw [hsum] at hcs
  -- Combine
  calc |w y - w x| ^ 2
      ≤ H ^ 2 * (∑ j : Fin n, |(y - x) j| ^ α) ^ 2 := h1
    _ ≤ H ^ 2 * ((Fintype.card (Fin n) : ℝ) * ∑ j : Fin n, |(y - x) j| ^ (2 * α)) := by
        apply mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = H ^ 2 * (Fintype.card (Fin n) : ℝ) * ∑ j : Fin n, |(y - x) j| ^ (2 * α) := by
        ring

/-! ## 2. Variance bound statement

The full variance integral bound:
  `∫ |w y - S(t)w(x)|² G_t(x-y) dy ≤ C·H²·t^α`

requires careful manipulation of the heat kernel integrals (Fubini,
integrability of the squared terms). The pointwise estimates above
(`sq_add_le_two_mul_sq_add` and `holder_sq_bound`) are the core analytic
ingredients.

The remaining integral manipulation is standard but technical:
- `∫ |w y - w x|² G_t(x-y) dy ≤ H²·n·∑_j (√t)^{2α}·gaussianAbsMoment(2α)`
  via `integral_abs_coord_rpow_mul_heatKernelND_eq` with `r = 2α`.
- `|w x - S(t)w(x)|² ≤ H²·n²·(√t)^{2α}·(gaussianAbsMoment α)²`
  via `abs_heatSemigroupND_sub_self_le_of_coordHolder`.
- Combine with `∫ G_t = 1`.

This is left as a documented gap; the pointwise bounds above are genuine.
-/

end AnalyticPDE
end RicciFlow
