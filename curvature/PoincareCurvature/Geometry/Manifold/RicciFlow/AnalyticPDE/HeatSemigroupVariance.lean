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

1. **Triangle inequality**: `|w y - heatSemigroupND t w x| ≤ |w y - w x| + |w x - heatSemigroupND t w x|` where `a = S(t)w(x)`.
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

/-! ## 3. Shifted Gaussian moment via change of variables -/

/-- The reflection-translation `y ↦ x - y` as a measurable equivalence. -/
def subLeftEquiv {n : ℕ} (x : Fin n → ℝ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun y := x - y
  invFun z := x - z
  left_inv y := by simp [sub_sub_cancel]
  right_inv z := by simp [sub_sub_cancel]
  measurable_toFun := by measurability
  measurable_invFun := by measurability

/-- `y ↦ x - y` preserves the Lebesgue measure on `Fin n → ℝ`. -/
lemma measurePreserving_subLeftEquiv {n : ℕ} (x : Fin n → ℝ) :
    MeasurePreserving (subLeftEquiv x) volume volume := by
  have h1 : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have h2 : MeasurePreserving (fun z : Fin n → ℝ => x + z) volume volume := by
    have h := measurePreserving_add_right volume x
    have heq : (fun z : Fin n → ℝ => x + z) = (fun x_1 : Fin n → ℝ => x_1 + x) := by
      funext z
      exact add_comm x z
    rw [heq]
    exact h
  have heq : (subLeftEquiv x : (Fin n → ℝ) → (Fin n → ℝ)) =
      (fun z : Fin n → ℝ => x + z) ∘ (fun y : Fin n → ℝ => -y) := by
    funext y
    simp [subLeftEquiv, sub_eq_add_neg]
  rw [heq]
  exact h2.comp h1

/-- Shifted coordinatewise fractional moment of the heat kernel. -/
theorem integral_abs_sub_coord_rpow_mul_heatKernelND_eq
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : -1 < r) (j : Fin n) (x : Fin n → ℝ) :
    (∫ y : Fin n → ℝ, |(x - y) j| ^ r * heatKernelND t (x - y)) =
      (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  have h := (measurePreserving_subLeftEquiv x).integral_comp'
    (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z)
  have heq : (∫ y : Fin n → ℝ, |(x - y) j| ^ r * heatKernelND t (x - y)) =
      ∫ y : Fin n → ℝ, (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z)
        ((subLeftEquiv x) y) := by
    rfl
  rw [heq, h]
  exact integral_abs_coord_rpow_mul_heatKernelND_eq ht hr j

/-! ## 4. Integrated squared Hölder deviation -/

/-- The squared deviation `|w y - w x|²` is AEStronglyMeasurable. -/
lemma aestronglyMeasurable_sq_deviation
    {n : ℕ} {w : (Fin n → ℝ) → ℝ}
    (hwm : AEStronglyMeasurable w)
    (x : Fin n → ℝ) :
    AEStronglyMeasurable (fun y => |w y - w x| ^ 2) := by
  have hsub : AEStronglyMeasurable (fun y => w y - w x) :=
    hwm.sub aestronglyMeasurable_const
  have hsq : (fun y => |w y - w x| ^ 2) = (fun y => (w y - w x) ^ 2) := by
    funext y
    rw [sq_abs]
  rw [hsq]
  exact hsub.pow 2

/-- Bound for the squared deviation. -/
lemma sq_deviation_bound
    {n : ℕ} {w : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hwb : ∀ y, ‖w y‖ ≤ C) (x y : Fin n → ℝ) :
    |w y - w x| ^ 2 ≤ (2 * C) ^ 2 := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hwb x)
  have h1 : |w y| ≤ C := by rw [← Real.norm_eq_abs]; exact hwb y
  have h2 : |w x| ≤ C := by rw [← Real.norm_eq_abs]; exact hwb x
  have htri : |w y - w x| ≤ 2 * C := by
    have h := abs_add_le (w y) (-w x)
    have heq : w y - w x = w y + -w x := by ring
    have habs : |-w x| = |w x| := abs_neg _
    calc |w y - w x| = |w y + -w x| := by rw [← heq]
      _ ≤ |w y| + |-w x| := h
      _ = |w y| + |w x| := by rw [habs]
      _ ≤ C + C := by linarith
      _ = 2 * C := by ring
  have hnn : 0 ≤ |w y - w x| := abs_nonneg _
  have hnn2 : 0 ≤ 2 * C := by linarith
  calc |w y - w x| ^ 2 ≤ (2 * C) ^ 2 := pow_le_pow_left₀ hnn htri 2

/-- Integrability of squared deviation times heat kernel. -/
lemma integrable_sq_deviation_mul_heatKernel
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {w : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (x : Fin n → ℝ) :
    Integrable (fun y => |w y - w x| ^ 2 * heatKernelND t (x - y)) := by
  apply Integrable.bdd_mul (integrable_heatKernelND_sub ht x)
    (aestronglyMeasurable_sq_deviation hwm x)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |w y - w x| ^ 2)]
  exact sq_deviation_bound hwb x y

/-- Integrability of scaled squared deviation times heat kernel. -/
lemma integrable_scaled_sq_deviation_mul_heatKernel
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {w : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (x : Fin n → ℝ) :
    Integrable (fun y => (2 * |w y - w x| ^ 2) * heatKernelND t (x - y)) := by
  have hbase := integrable_sq_deviation_mul_heatKernel ht hwm hwb x
  have heq : (fun y => (2 * |w y - w x| ^ 2) * heatKernelND t (x - y)) =
      fun y => 2 * (|w y - w x| ^ 2 * heatKernelND t (x - y)) := by
    funext y; ring
  rw [heq]
  exact hbase.const_mul 2

/-- Integrated squared Hölder deviation: for `w` Hölder with constant `H`,
    `∫ y, |w y - w x|² * G_t(x-y) dy ≤ H² * n² * t^α * gaussianAbsMoment(2α)`. -/
theorem integral_sq_holder_deviation_le
    {n : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 < α)
    {w : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (hholder : ∀ a b, |w a - w b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α)
    (x : Fin n → ℝ) :
    ∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y) ≤
      H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
        gaussianAbsMoment (2 * α) := by
  -- Step 1: Pointwise bound
  have hpoint : ∀ y, |w y - w x| ^ 2 * heatKernelND t (x - y) ≤
      (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y) := by
    intro y
    have hK : 0 ≤ heatKernelND t (x - y) := heatKernelND_nonneg ht _
    have hsq := holder_sq_bound hH hholder y x
    have hsq' : |w y - w x| ^ 2 ≤ H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α) := by
      have habs : ∑ j : Fin n, |(y - x) j| ^ (2 * α) =
          ∑ j : Fin n, |(x - y) j| ^ (2 * α) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
      rw [habs] at hsq
      exact hsq
    exact mul_le_mul_of_nonneg_right hsq' hK
  -- Step 2: Integrability
  have hLHS_int : Integrable
      (fun y => |w y - w x| ^ 2 * heatKernelND t (x - y)) :=
    integrable_sq_deviation_mul_heatKernel ht hwm hwb x
  have hRHS_int : Integrable
      (fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y)) := by
    have h_each : ∀ j : Fin n, Integrable
        (fun y => |(x - y) j| ^ (2 * α) * heatKernelND t (x - y)) := by
      intro j
      have h := (integrable_abs_coord_rpow_mul_heatKernelND ht
        (show -1 < 2 * α by linarith) j).comp_sub_left x
      exact h
    have hsum : Integrable
        (fun y => ∑ j : Fin n, |(x - y) j| ^ (2 * α) * heatKernelND t (x - y)) :=
      integrable_finsetSum _ (fun j _ => h_each j)
    have hmul : Integrable
        (fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ)) *
          (∑ j : Fin n, |(x - y) j| ^ (2 * α) * heatKernelND t (x - y))) :=
      hsum.const_mul _
    have heq : (fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y)) =
        (fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ)) *
          (∑ j : Fin n, |(x - y) j| ^ (2 * α) * heatKernelND t (x - y))) := by
      funext y
      rw [mul_assoc, Finset.sum_mul]
    rw [heq]
    exact hmul
  -- Step 3: Integral monotonicity
  have h_mono : (∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)) ≤
      ∫ y, (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y) := by
    apply integral_mono hLHS_int hRHS_int
    intro y
    exact hpoint y
  -- Step 4: Simplify RHS integral
  have hRHS_eq : (∫ y, (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
      ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y)) =
      H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
        gaussianAbsMoment (2 * α) := by
    have heq1 : (fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
        ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y)) =
        fun y => (H ^ 2 * (Fintype.card (Fin n) : ℝ)) *
          ((∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y)) := by
      funext y; ring
    rw [heq1, integral_const_mul]
    have heq2 : (fun y => (∑ j : Fin n, |(x - y) j| ^ (2 * α)) *
        heatKernelND t (x - y)) =
        fun y => ∑ j : Fin n, (|(x - y) j| ^ (2 * α) * heatKernelND t (x - y)) := by
      funext y
      rw [Finset.sum_mul]
    rw [heq2, integral_finsetSum]
    · have hmoment : ∀ j : Fin n,
          (∫ y, |(x - y) j| ^ (2 * α) * heatKernelND t (x - y)) =
            (Real.sqrt t) ^ (2 * α) * gaussianAbsMoment (2 * α) := by
        intro j
        exact integral_abs_sub_coord_rpow_mul_heatKernelND_eq ht
          (show -1 < 2 * α by linarith) j x
      have hsum_eq : ∑ j : Fin n,
          (∫ y, |(x - y) j| ^ (2 * α) * heatKernelND t (x - y)) =
          (Fintype.card (Fin n) : ℝ) * ((Real.sqrt t) ^ (2 * α) *
            gaussianAbsMoment (2 * α)) := by
        rw [Finset.sum_congr rfl (fun j _ => hmoment j)]
        rw [Finset.sum_const, Finset.card_univ]
        simp [nsmul_eq_mul]
      rw [hsum_eq]
      have hsqrt : (Real.sqrt t) ^ (2 * α) = t ^ α := by
        have ht0 : (0:ℝ) ≤ t := le_of_lt ht
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
        congr 1
        ring
      rw [hsqrt]
      ring
    · intro j _
      exact (integrable_abs_coord_rpow_mul_heatKernelND ht
        (show -1 < 2 * α by linarith) j).comp_sub_left x
  -- Combine
  calc ∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)
      ≤ ∫ y, (H ^ 2 * (Fintype.card (Fin n) : ℝ) *
          ∑ j : Fin n, |(x - y) j| ^ (2 * α)) * heatKernelND t (x - y) := h_mono
    _ = H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
          gaussianAbsMoment (2 * α) := hRHS_eq

/-! ## 5. Full variance bound with heat semigroup -/

/-- The heat semigroup value is bounded. -/
lemma abs_heatSemigroupND_bound
    {n : ℕ} {t : ℝ} (ht : 0 < t) {w : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hwb : ∀ y, ‖w y‖ ≤ C) (x : Fin n → ℝ) :
    |heatSemigroupND t w x| ≤ C := by
  apply abs_heatSemigroupND_le ht x
  intro y
  rw [← Real.norm_eq_abs]
  exact hwb y

/-- Integrability of the RHS sum for variance bound. -/
lemma integrable_variance_RHS
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {w : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (x : Fin n → ℝ) :
    Integrable
      (fun y => (2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2) *
        heatKernelND t (x - y)) := by
  have h1 := integrable_scaled_sq_deviation_mul_heatKernel ht hwm hwb x
  have h2 := (integrable_heatKernelND_sub ht x).const_mul (2 * |w x - heatSemigroupND t w x| ^ 2)
  have hsum := h1.add h2
  refine hsum.congr ?_
  filter_upwards with y
  simp only [Pi.add_apply]
  ring

/-- Full variance bound: `∫ |w y - S(t)w(x)|² G ≤ 2n²H²t^α (M(2α) + M(α)²)`. -/
theorem variance_integral_bound
    {n : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 < α)
    {w : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (hholder : ∀ a b, |w a - w b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α)
    (x : Fin n → ℝ) :
    ∫ y, |w y - heatSemigroupND t w x| ^ 2 * heatKernelND t (x - y) ≤
      2 * (Fintype.card (Fin n) : ℝ) ^ 2 * H ^ 2 * t ^ α *
        (gaussianAbsMoment (2 * α) + (gaussianAbsMoment α) ^ 2) := by
  -- Step 1: Pointwise split via (u+v)² ≤ 2u² + 2v²
  -- |w y - S(t)w(x)|² ≤ 2|w y - w x|² + 2|w x - S(t)w(x)|²
  have hsplit : ∀ y, |w y - heatSemigroupND t w x| ^ 2 ≤
      2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2 := by
    intro y
    have htri : |w y - heatSemigroupND t w x| ≤
        |w y - w x| + |w x - heatSemigroupND t w x| := by
      have h := abs_add_le (w y - w x) (w x - heatSemigroupND t w x)
      have heq : (w y - w x) + (w x - heatSemigroupND t w x) =
          w y - heatSemigroupND t w x := by ring
      rw [heq] at h
      exact h
    have h1 : |w y - heatSemigroupND t w x| ^ 2 ≤
        (|w y - w x| + |w x - heatSemigroupND t w x|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) htri 2
    have h2 := sq_add_le_two_mul_sq_add (|w y - w x|) (|w x - heatSemigroupND t w x|)
    linarith
  -- Step 2: Integrability
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hwb x)
  have hmeas_S : AEStronglyMeasurable (fun y => |w y - heatSemigroupND t w x| ^ 2) := by
    have hsub : AEStronglyMeasurable (fun y => w y - heatSemigroupND t w x) :=
      hwm.sub aestronglyMeasurable_const
    have hsq : (fun y => |w y - heatSemigroupND t w x| ^ 2) = (fun y => (w y - heatSemigroupND t w x) ^ 2) := by
      funext y
      rw [sq_abs]
    rw [hsq]
    exact hsub.pow 2
  have hLHS_int : Integrable
      (fun y => |w y - heatSemigroupND t w x| ^ 2 * heatKernelND t (x - y)) := by
    apply Integrable.bdd_mul (integrable_heatKernelND_sub ht x) hmeas_S
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |w y - heatSemigroupND t w x| ^ 2)]
    have h1 : |w y| ≤ C := by rw [← Real.norm_eq_abs]; exact hwb y
    have htri : |w y - heatSemigroupND t w x| ≤ 2 * C := by
      have hSa : |heatSemigroupND t w x| ≤ C := abs_heatSemigroupND_bound ht hwb x
      have heq : w y - heatSemigroupND t w x = w y + -(heatSemigroupND t w x) := by ring
      rw [heq]
      have h := abs_add_le (w y) (-(heatSemigroupND t w x))
      rw [abs_neg] at h
      linarith
    exact pow_le_pow_left₀ (abs_nonneg _) htri 2
  -- Step 3: Integral monotonicity
  have h_mono : (∫ y, |w y - heatSemigroupND t w x| ^ 2 * heatKernelND t (x - y)) ≤
      ∫ y, (2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2) *
        heatKernelND t (x - y) := by
    apply integral_mono hLHS_int (integrable_variance_RHS ht hwm hwb x)
    intro y
    have hK : 0 ≤ heatKernelND t (x - y) := heatKernelND_nonneg ht _
    exact mul_le_mul_of_nonneg_right (hsplit y) hK
  -- Step 4: Split RHS integral
  have hRHS_eq : (∫ y, (2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2) *
      heatKernelND t (x - y)) =
      2 * (∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)) +
        2 * |w x - heatSemigroupND t w x| ^ 2 * (∫ y, heatKernelND t (x - y)) := by
    have heq : (fun y => (2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2) *
        heatKernelND t (x - y)) =
        fun y => 2 * (|w y - w x| ^ 2 * heatKernelND t (x - y)) +
          (2 * |w x - heatSemigroupND t w x| ^ 2) * heatKernelND t (x - y) := by
      funext y; ring
    rw [heq, integral_add]
    · rw [← integral_const_mul, ← integral_const_mul]
    · exact (integrable_sq_deviation_mul_heatKernel ht hwm hwb x).const_mul 2
    · exact (integrable_heatKernelND_sub ht x).const_mul _
  -- Step 5: Apply bounds
  have h_first : (∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)) ≤
      H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
        gaussianAbsMoment (2 * α) :=
    integral_sq_holder_deviation_le ht hα hH hwm hwb hholder x
  have h_kernel_mass : (∫ y, heatKernelND t (x - y)) = 1 :=
    integral_heatKernelND_sub ht x
  -- Approximate identity: |S(t)w(x) - w x| ≤ H * n * (√t)^α * M(α)
  have h_approx : |heatSemigroupND t w x - w x| ≤
      H * (Fintype.card (Fin n) : ℝ) * (Real.sqrt t) ^ α *
        gaussianAbsMoment α := by
    have h := abs_heatSemigroupND_sub_self_le_of_coordHolder ht (le_of_lt hα)
      hH hwm hwb hholder x
    have hsum : ∑ _j : Fin n, (Real.sqrt t) ^ α * gaussianAbsMoment α =
        (Fintype.card (Fin n) : ℝ) * ((Real.sqrt t) ^ α * gaussianAbsMoment α) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul]
    rw [hsum] at h
    linarith
  have h_second : |w x - heatSemigroupND t w x| ^ 2 ≤
      H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
        (gaussianAbsMoment α) ^ 2 := by
    have h1 : |w x - heatSemigroupND t w x| = |heatSemigroupND t w x - w x| := by
      rw [abs_sub_comm]
    rw [h1]
    have hnn : 0 ≤ |heatSemigroupND t w x - w x| := abs_nonneg _
    have hsq : |heatSemigroupND t w x - w x| ^ 2 ≤
        (H * (Fintype.card (Fin n) : ℝ) * (Real.sqrt t) ^ α *
          gaussianAbsMoment α) ^ 2 :=
      pow_le_pow_left₀ hnn h_approx 2
    have hsqrt : ((Real.sqrt t) ^ α) ^ 2 = t ^ α := by
      have ht0 : (0:ℝ) ≤ t := le_of_lt ht
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (Real.rpow_nonneg ht0 _),
        ← Real.rpow_mul ht0]
      congr 1
      push_cast
      ring
    calc |heatSemigroupND t w x - w x| ^ 2
        ≤ (H * (Fintype.card (Fin n) : ℝ) * (Real.sqrt t) ^ α *
            gaussianAbsMoment α) ^ 2 := hsq
      _ = H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
            (gaussianAbsMoment α) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, hsqrt]
  -- Combine all
  calc ∫ y, |w y - heatSemigroupND t w x| ^ 2 * heatKernelND t (x - y)
      ≤ ∫ y, (2 * |w y - w x| ^ 2 + 2 * |w x - heatSemigroupND t w x| ^ 2) *
          heatKernelND t (x - y) := h_mono
    _ = 2 * (∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)) +
          2 * |w x - heatSemigroupND t w x| ^ 2 * (∫ y, heatKernelND t (x - y)) := hRHS_eq
    _ = 2 * (∫ y, |w y - w x| ^ 2 * heatKernelND t (x - y)) +
          2 * |w x - heatSemigroupND t w x| ^ 2 * 1 := by rw [h_kernel_mass]
    _ ≤ 2 * (H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
            gaussianAbsMoment (2 * α)) +
          2 * (H ^ 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * t ^ α *
            (gaussianAbsMoment α) ^ 2) * 1 := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left h_first (by norm_num)
          · rw [mul_one, mul_one]
            exact mul_le_mul_of_nonneg_left h_second (by norm_num)
    _ = 2 * (Fintype.card (Fin n) : ℝ) ^ 2 * H ^ 2 * t ^ α *
          (gaussianAbsMoment (2 * α) + (gaussianAbsMoment α) ^ 2) := by ring

end AnalyticPDE
end RicciFlow
