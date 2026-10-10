import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatSemigroupVariance
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderCommutatorSeminorm

/-!
# Pointwise Taylor commutator for heat semigroup (Point 4 PDE milestone)

This file proves the **pointwise Taylor commutator estimate**:
`|S(t)(F∘f)(x) - F(S(t)f(x))| ≤ M · Var_t(f)(x) ≤ C·M·H²·t^α`.

## Mathematical content

For `F : ℝ → ℝ` with `M`-Lipschitz derivative and `f` Hölder with constant `H`:

1. Write `S(t)(F∘f)(x) - F(a) = ∫ G_t(x-y)·[F(f(y)) - F(a)] dy` where `a = S(t)f(x)`,
   using `∫ G_t = 1`.
2. Taylor expand: `F(f(y)) - F(a) = [F(f(y)) - F(a) - F'(a)(f(y)-a)] + F'(a)(f(y)-a)`.
3. The linear term integrates to zero:
   `∫ G_t(x-y)·F'(a)(f(y)-a) dy = F'(a)·(S(t)f(x) - a) = 0`.
4. Bound the remainder via `taylor_remainder_lipschitz_deriv` and
   `variance_integral_bound`.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. F∘f is bounded and measurable -/

/-- `F` is continuous when differentiable everywhere. -/
lemma continuous_of_forall_hasDerivAt {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hF x).continuousAt

/-- Composition `F ∘ f` is AEStronglyMeasurable. -/
lemma aestronglyMeasurable_comp_of_hasDerivAt
    {f : (Fin n → ℝ) → ℝ} {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hfm : AEStronglyMeasurable f) :
    AEStronglyMeasurable (fun y => F (f y)) := by
  have hcont := continuous_of_forall_hasDerivAt hF
  have heq : (fun y => F (f y)) = F ∘ f := rfl
  rw [heq]
  exact hcont.comp_aestronglyMeasurable hfm

/-- `F` is bounded on `Icc (-C) C` when continuous. -/
lemma bdd_on_Icc_of_hasDerivAt
    {F F' : ℝ → ℝ} {C : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) :
    ∃ B, ∀ z ∈ Set.Icc (-C) C, ‖F z‖ ≤ B := by
  have hcont := continuous_of_forall_hasDerivAt hF
  have himg : Bornology.IsBounded (F '' Set.Icc (-C) C) :=
    (isCompact_Icc.image hcont).isBounded
  obtain ⟨B, hB⟩ := himg.exists_norm_le
  exact ⟨B, fun z hz => hB _ (Set.mem_image_of_mem F hz)⟩

/-! ## 2. The linear Taylor term integrates to zero -/

/-- The deviation `∫ G_t(x-y)·(f(y) - S(t)f(x)) dy = 0`. -/
lemma integral_heatKernelND_sub_mul_deviation {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (x : Fin n → ℝ) :
    ∫ y, heatKernelND t (x - y) * (f y - heatSemigroupND t f x) = 0 := by
  have h_int_f := integrable_heatKernelND_sub_mul ht x hfm hfb
  have h_int_const : Integrable (fun y => heatKernelND t (x - y) * heatSemigroupND t f x) :=
    (integrable_heatKernelND_sub ht x).mul_const _
  have heq : (fun y => heatKernelND t (x - y) * (f y - heatSemigroupND t f x))
      = fun y => (heatKernelND t (x - y) * f y - heatKernelND t (x - y) * heatSemigroupND t f x) := by
    funext y; ring
  rw [heq, integral_sub h_int_f h_int_const, integral_mul_const,
    integral_heatKernelND_sub ht x, one_mul]
  have hdef : (∫ y, heatKernelND t (x - y) * f y) = heatSemigroupND t f x := rfl
  rw [hdef, sub_self]

/-! ## 3. Pointwise Taylor commutator -/

/-- **Pointwise Taylor commutator estimate.**
`|S(t)(F∘f)(x) - F(S(t)f(x))| ≤ M · 2n²H²t^α(M(2α) + M(α)²)`. -/
theorem commutator_taylor_pointwise
    {n : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 < α)
    {F F' : ℝ → ℝ} {M : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hLip : LipschitzWith M F')
    {f : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ a b, |f a - f b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α)
    (x : Fin n → ℝ) :
    |heatSemigroupND t (fun y => F (f y)) x - F (heatSemigroupND t f x)| ≤
      (M : ℝ) * (2 * (Fintype.card (Fin n) : ℝ) ^ 2 * H ^ 2 * t ^ α *
        (gaussianAbsMoment (2 * α) + (gaussianAbsMoment α) ^ 2)) := by
  -- Boundedness of F on the range
  obtain ⟨B, hB_Icc⟩ := bdd_on_Icc_of_hasDerivAt hF (C := C)
  have hmem_Icc : ∀ z : ℝ, |z| ≤ C → z ∈ Set.Icc (-C) C := by
    intro z hz
    rw [abs_le] at hz
    exact ⟨hz.1, hz.2⟩
  have hFf_bdd : ∀ y, ‖F (f y)‖ ≤ B := fun y =>
    hB_Icc _ (hmem_Icc _ (by rw [← Real.norm_eq_abs]; exact hfb y))
  have hFa_bdd : ‖F (heatSemigroupND t f x)‖ ≤ B :=
    hB_Icc _ (hmem_Icc _ (abs_heatSemigroupND_bound ht hfb x))
  have hFf_meas := aestronglyMeasurable_comp_of_hasDerivAt hF hfm
  have h_int_Ff : Integrable (fun y => heatKernelND t (x - y) * F (f y)) :=
    integrable_heatKernelND_sub_mul ht x hFf_meas hFf_bdd
  -- Measurability of deviation, linear, and remainder parts
  have h_dev_meas : AEStronglyMeasurable (fun y => f y - heatSemigroupND t f x) :=
    hfm.sub aestronglyMeasurable_const
  have h_lin_meas : AEStronglyMeasurable
      (fun y => F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)) :=
    h_dev_meas.const_mul _
  have h_rem_meas : AEStronglyMeasurable
      (fun y => F (f y) - F (heatSemigroupND t f x)
        - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)) :=
    (hFf_meas.sub aestronglyMeasurable_const).sub h_lin_meas
  -- Boundedness of deviation: |f y - a| ≤ 2C
  have h_dev_bdd : ∀ y, ‖f y - heatSemigroupND t f x‖ ≤ 2 * C := by
    intro y
    have h2 : ‖heatSemigroupND t f x‖ ≤ C := by
      rw [Real.norm_eq_abs]
      exact abs_heatSemigroupND_bound ht hfb x
    calc ‖f y - heatSemigroupND t f x‖ ≤ ‖f y‖ + ‖heatSemigroupND t f x‖ :=
          norm_sub_le _ _
      _ ≤ C + C := by linarith [hfb y]
      _ = 2 * C := by ring
  have h_lin_bdd : ∀ y, ‖F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)‖
      ≤ ‖F' (heatSemigroupND t f x)‖ * (2 * C) := by
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h_dev_bdd y) (norm_nonneg _)
  have h_rem_bdd : ∀ y, ‖F (f y) - F (heatSemigroupND t f x)
        - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)‖
      ≤ B + B + ‖F' (heatSemigroupND t f x)‖ * (2 * C) := by
    intro y
    calc ‖F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)‖
        ≤ ‖F (f y) - F (heatSemigroupND t f x)‖
          + ‖F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)‖ :=
          norm_sub_le _ _
      _ ≤ (‖F (f y)‖ + ‖F (heatSemigroupND t f x)‖)
          + ‖F' (heatSemigroupND t f x)‖ * (2 * C) := by
          apply add_le_add _ (h_lin_bdd y)
          exact norm_sub_le _ _
      _ ≤ (B + B) + ‖F' (heatSemigroupND t f x)‖ * (2 * C) := by
          apply add_le_add _ le_rfl
          exact add_le_add (hFf_bdd y) hFa_bdd
      _ = B + B + ‖F' (heatSemigroupND t f x)‖ * (2 * C) := by ring
  have h_int_lin : Integrable (fun y => heatKernelND t (x - y)
      * (F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))) :=
    integrable_heatKernelND_sub_mul ht x h_lin_meas h_lin_bdd
  have h_int_rem : Integrable (fun y => heatKernelND t (x - y)
      * (F (f y) - F (heatSemigroupND t f x)
        - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))) :=
    integrable_heatKernelND_sub_mul ht x h_rem_meas h_rem_bdd
  -- Key identity: commutator equals integral of Taylor remainder
  have h_key : heatSemigroupND t (fun y => F (f y)) x - F (heatSemigroupND t f x)
      = ∫ y, heatKernelND t (x - y)
        * (F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)) := by
    have hFa : F (heatSemigroupND t f x)
        = ∫ y, heatKernelND t (x - y) * F (heatSemigroupND t f x) := by
      rw [integral_mul_const, integral_heatKernelND_sub ht x, one_mul]
    have hS : heatSemigroupND t (fun y => F (f y)) x
        = ∫ y, heatKernelND t (x - y) * F (f y) := rfl
    have h_int_const_Fa : Integrable
        (fun y => heatKernelND t (x - y) * F (heatSemigroupND t f x)) :=
      (integrable_heatKernelND_sub ht x).mul_const _
    -- First rewrite only the LHS (avoid touching the remainder on RHS)
    have h1 : heatSemigroupND t (fun y => F (f y)) x - F (heatSemigroupND t f x)
        = (∫ y, heatKernelND t (x - y) * F (f y))
          - (∫ y, heatKernelND t (x - y) * F (heatSemigroupND t f x)) := by
      rw [hS]
      conv_lhs => rw [hFa]
    rw [h1, ← integral_sub h_int_Ff h_int_const_Fa]
    have h_split : (fun y => heatKernelND t (x - y) * F (f y)
          - heatKernelND t (x - y) * F (heatSemigroupND t f x))
        = fun y => (heatKernelND t (x - y)
            * (F (f y) - F (heatSemigroupND t f x)
              - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))
            + heatKernelND t (x - y)
              * (F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))) := by
      funext y; ring
    rw [h_split, integral_add h_int_rem h_int_lin]
    have h_lin_zero : ∫ y, heatKernelND t (x - y)
          * (F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)) = 0 := by
      have heq : (fun y => heatKernelND t (x - y)
            * (F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)))
          = fun y => F' (heatSemigroupND t f x)
            * (heatKernelND t (x - y) * (f y - heatSemigroupND t f x)) := by
        funext y; ring
      rw [heq, integral_const_mul,
        integral_heatKernelND_sub_mul_deviation ht hfm hfb x, mul_zero]
    rw [h_lin_zero, add_zero]
  -- Pointwise Taylor bound
  have h_taylor_pt : ∀ y, |F (f y) - F (heatSemigroupND t f x)
        - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)|
      ≤ (M : ℝ) * (f y - heatSemigroupND t f x) ^ 2 := by
    intro y
    exact taylor_remainder_lipschitz_deriv hF hLip (heatSemigroupND t f x) (f y)
  -- Integrability of the dominating function
  have h_sq_meas : AEStronglyMeasurable (fun y => (f y - heatSemigroupND t f x) ^ 2) :=
    h_dev_meas.pow 2
  have h_sq_bdd : ∀ y, ‖(f y - heatSemigroupND t f x) ^ 2‖ ≤ (2 * C) ^ 2 := by
    intro y
    have h2 : |f y - heatSemigroupND t f x| ≤ 2 * C := by
      have h3 : ‖f y - heatSemigroupND t f x‖ ≤ 2 * C := h_dev_bdd y
      rwa [Real.norm_eq_abs] at h3
    have h4 : (0:ℝ) ≤ |f y - heatSemigroupND t f x| := abs_nonneg _
    have h5 : (0:ℝ) ≤ 2 * C := by
      have h6 : (0:ℝ) ≤ ‖f y - heatSemigroupND t f x‖ := norm_nonneg _
      linarith [h_dev_bdd y]
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ h4 h2 2
  have h_int_dom : Integrable (fun y => heatKernelND t (x - y)
      * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2)) := by
    have h_base : Integrable (fun y => heatKernelND t (x - y)
        * (f y - heatSemigroupND t f x) ^ 2) :=
      integrable_heatKernelND_sub_mul ht x h_sq_meas h_sq_bdd
    have heq : (fun y => heatKernelND t (x - y) * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2))
        = fun y => (M : ℝ) * (heatKernelND t (x - y) * (f y - heatSemigroupND t f x) ^ 2) := by
      funext y; ring
    rw [heq]
    exact h_base.const_mul _
  -- |∫| ≤ ∫| | and bound
  have h_abs_le : |∫ y, heatKernelND t (x - y)
        * (F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))|
      ≤ ∫ y, heatKernelND t (x - y) * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2) := by
    have h_norm_le : |∫ y, heatKernelND t (x - y)
          * (F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))|
        ≤ ∫ y, |heatKernelND t (x - y)
          * (F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))| := by
      have h := norm_integral_le_integral_norm (μ := volume) (fun y => heatKernelND t (x - y)
        * (F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)))
      simp only [Real.norm_eq_abs] at h
      exact h
    have h_abs_eq : (∫ y, |heatKernelND t (x - y)
          * (F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))|)
        = ∫ y, heatKernelND t (x - y)
          * |F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)| := by
      apply integral_congr_ae
      filter_upwards with y
      rw [abs_mul, abs_of_nonneg (heatKernelND_nonneg ht _)]
    have h_int_abs : Integrable (fun y => heatKernelND t (x - y)
        * |F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)|) := by
      have h_norm_int : Integrable (fun y => ‖heatKernelND t (x - y)
          * (F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))‖) :=
        h_int_rem.norm
      have heq : (fun y => heatKernelND t (x - y)
            * |F (f y) - F (heatSemigroupND t f x)
              - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)|)
          = fun y => ‖heatKernelND t (x - y)
            * (F (f y) - F (heatSemigroupND t f x)
              - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))‖ := by
        funext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelND_nonneg ht _)]
      rw [heq]
      exact h_norm_int
    have h_mono : (∫ y, heatKernelND t (x - y)
          * |F (f y) - F (heatSemigroupND t f x)
            - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x)|)
        ≤ ∫ y, heatKernelND t (x - y) * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2) := by
      apply integral_mono h_int_abs h_int_dom
      intro y
      exact mul_le_mul_of_nonneg_left (h_taylor_pt y) (heatKernelND_nonneg ht _)
    rw [h_abs_eq] at h_norm_le
    exact le_trans h_norm_le h_mono
  -- Rewrite the dominating integral via the variance bound
  have h_var_eq : (∫ y, heatKernelND t (x - y)
        * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2))
      = (M : ℝ) * ∫ y, |f y - heatSemigroupND t f x| ^ 2
        * heatKernelND t (x - y) := by
    have heq : (fun y => heatKernelND t (x - y) * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2))
        = fun y => (M : ℝ) * (|f y - heatSemigroupND t f x| ^ 2 * heatKernelND t (x - y)) := by
      funext y
      have hsq : (f y - heatSemigroupND t f x) ^ 2 = |f y - heatSemigroupND t f x| ^ 2 :=
        (sq_abs _).symm
      rw [hsq]
      ring
    rw [heq, integral_const_mul]
  have h_var_le := variance_integral_bound ht hα hH hfm hfb hholder x
  have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  calc |heatSemigroupND t (fun y => F (f y)) x - F (heatSemigroupND t f x)|
      = |∫ y, heatKernelND t (x - y)
        * (F (f y) - F (heatSemigroupND t f x)
          - F' (heatSemigroupND t f x) * (f y - heatSemigroupND t f x))| := by
        rw [h_key]
    _ ≤ ∫ y, heatKernelND t (x - y) * ((M : ℝ) * (f y - heatSemigroupND t f x) ^ 2) :=
        h_abs_le
    _ = (M : ℝ) * ∫ y, |f y - heatSemigroupND t f x| ^ 2 * heatKernelND t (x - y) :=
        h_var_eq
    _ ≤ (M : ℝ) * (2 * (Fintype.card (Fin n) : ℝ) ^ 2 * H ^ 2 * t ^ α *
        (gaussianAbsMoment (2 * α) + (gaussianAbsMoment α) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_var_le hM_nonneg

end AnalyticPDE
end RicciFlow
