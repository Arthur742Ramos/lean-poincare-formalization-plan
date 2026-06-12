module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The one-dimensional Euclidean heat kernel

This module begins the parabolic-regularity foundation needed for the
Ricci–DeTurck Schauder estimates (roadmap point 4, uniqueness side).  Mathlib
v4.29.1 contains no heat-kernel / parabolic-PDE theory, so this is built from the
Gaussian-integral API.

The 1D heat kernel is
`heatKernel1D t x = (4 π t)^(-1/2) * exp (-x^2 / (4 t))` for `t > 0`.

This first increment proves the genuinely-checkable analytic facts:

* `heatKernel1D_pos` — strict positivity for `t > 0`;
* `integral_heatKernel1D` — total mass `∫ x, heatKernel1D t x = 1` for `t > 0`,
  obtained from `integral_gaussian`.

Later increments will add the heat equation `∂ₜ K = ∂ₓₓ K`, the semigroup
property, and the Hölder mapping estimates that feed the parabolic Schauder
theory.
-/

@[expose] public noncomputable section

open Real MeasureTheory
open scoped Real

namespace RicciFlow
namespace AnalyticPDE

/-- The one-dimensional Euclidean heat kernel
`K(t, x) = (4 π t)^(-1/2) · exp(-x² / (4 t))`. -/
def heatKernel1D (t x : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t))

lemma heatKernel1D_apply (t x : ℝ) :
    heatKernel1D t x = (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t)) := rfl

/-- The normalising prefactor `(4 π t)^(-1/2)` is positive for `t > 0`. -/
lemma heatKernel1D_prefactor_pos {t : ℝ} (ht : 0 < t) :
    0 < (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  have h4πt : 0 < 4 * π * t := by positivity
  exact Real.rpow_pos_of_pos h4πt _

/-- The heat kernel is strictly positive for `t > 0`. -/
lemma heatKernel1D_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel1D t x := by
  rw [heatKernel1D]
  exact mul_pos (heatKernel1D_prefactor_pos ht) (Real.exp_pos _)

/-- Total mass of the heat kernel: `∫ x, K(t, x) dx = 1` for `t > 0`. -/
theorem integral_heatKernel1D {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, heatKernel1D t x = 1 := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  -- Rewrite the exponent `-x²/(4t)` as `-(4t)⁻¹ * x²` to match `integral_gaussian`.
  have hexp : ∀ x : ℝ, -x ^ 2 / (4 * t) = -(4 * t)⁻¹ * x ^ 2 := by
    intro x; rw [neg_div, div_eq_inv_mul]; ring
  -- Pull the constant prefactor out of the integral.
  calc
    ∫ x : ℝ, heatKernel1D t x
        = ∫ x : ℝ, (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * x ^ 2) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ ?_))
          rw [heatKernel1D, hexp x]
    _ = (4 * π * t) ^ (-(1 : ℝ) / 2) * ∫ x : ℝ, Real.exp (-(4 * t)⁻¹ * x ^ 2) := by
          rw [integral_const_mul]
    _ = (4 * π * t) ^ (-(1 : ℝ) / 2) * √(π / (4 * t)⁻¹) := by
          rw [integral_gaussian]
    _ = 1 := by
          have h4πt : 0 < 4 * π * t := by positivity
          -- `π / (4t)⁻¹ = 4 π t`.
          have harg : π / (4 * t)⁻¹ = 4 * π * t := by
            rw [div_inv_eq_mul]; ring
          rw [harg, Real.sqrt_eq_rpow, ← Real.rpow_add h4πt]
          norm_num

/-- The spatial first derivative of the heat kernel:
`∂ₓ K(t, x) = K(t, x) · (-x / (2 t))`. -/
theorem hasDerivAt_heatKernel1D_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => heatKernel1D t y)
      (heatKernel1D t x * (-x / (2 * t))) x := by
  have htne : (4 * t) ≠ 0 := by positivity
  -- Derivative of the exponent `f y = -y²/(4t)`: `f' = -2x/(4t) = -x/(2t)`.
  have hf : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t)) (-x / (2 * t)) x := by
    have hpow : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    have hdiv := hpow.div_const (4 * t)
    -- `-(2x)/(4t) = -x/(2t)`.
    have heq : -(2 * x) / (4 * t) = -x / (2 * t) := by
      rw [div_eq_div_iff htne (by positivity)]; ring
    rwa [heq] at hdiv
  -- Chain rule for `exp ∘ f`, then multiply by the constant prefactor.
  have hexp := hf.exp
  have hconst := hexp.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  -- Rewrite the resulting derivative value into `K · (-x/(2t))`.
  have hval : (4 * π * t) ^ (-(1 : ℝ) / 2) *
      (Real.exp (-x ^ 2 / (4 * t)) * (-x / (2 * t))) =
      heatKernel1D t x * (-x / (2 * t)) := by
    rw [heatKernel1D]; ring
  rw [← hval]
  exact hconst

/-- The spatial second derivative of the heat kernel:
`∂ₓₓ K(t, x) = K(t, x) · (x² / (4 t²) - 1 / (2 t))`. -/
theorem hasDerivAt_heatKernel1D_space_second {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => heatKernel1D t y * (-y / (2 * t)))
      (heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) x := by
  have htne : (2 * t) ≠ 0 := by positivity
  -- First factor: `∂ₓ K = K · (-x/(2t))`.
  have hK := hasDerivAt_heatKernel1D_space ht x
  -- Second factor: `∂ₓ (-y/(2t)) = -1/(2t)`.
  have hg : HasDerivAt (fun y : ℝ => -y / (2 * t)) (-1 / (2 * t)) x := by
    have hid : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    simpa using hid.div_const (2 * t)
  -- Product rule.
  have hmul := hK.mul hg
  -- Rewrite the derivative value into `K · (x²/(4t²) - 1/(2t))`.
  have hval :
      heatKernel1D t x * (-x / (2 * t)) * (-x / (2 * t)) +
        heatKernel1D t x * (-1 / (2 * t)) =
      heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
    field_simp
    ring
  rw [← hval]
  exact hmul

/-- The time derivative of the heat kernel:
`∂ₜ K(t, x) = K(t, x) · (x² / (4 t²) - 1 / (2 t))`. -/
theorem hasDerivAt_heatKernel1D_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel1D s x)
      (heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) t := by
  have htne : t ≠ 0 := ne_of_gt ht
  have h4πtpos : 0 < 4 * π * t := by positivity
  have h4πtne : 4 * π * t ≠ 0 := ne_of_gt h4πtpos
  -- Prefactor `c s = (4 π s)^(-1/2)`; derivative via chain rule with inner `s ↦ 4 π s`.
  have hinner : HasDerivAt (fun s : ℝ => 4 * π * s) (4 * π) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * π))
  have hrpow : HasDerivAt (fun u : ℝ => u ^ (-(1 : ℝ) / 2))
      ((-(1 : ℝ) / 2) * (4 * π * t) ^ (-(1 : ℝ) / 2 - 1)) (4 * π * t) :=
    Real.hasDerivAt_rpow_const (Or.inl h4πtne)
  have hc : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(1 : ℝ) / 2))
      ((-(1 : ℝ) / 2) * (4 * π * t) ^ (-(1 : ℝ) / 2 - 1) * (4 * π)) t :=
    hrpow.comp t hinner
  -- Exponent `e s = -x²/(4 s) = (-x²/4) · s⁻¹`; derivative `x²/(4 t²)`.
  have he : HasDerivAt (fun s : ℝ => -x ^ 2 / (4 * s)) (x ^ 2 / (4 * t ^ 2)) t := by
    have hsinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := by
      simpa using hasDerivAt_inv htne
    have hmul := hsinv.const_mul (-x ^ 2 / 4)
    have hfuneq : (fun s : ℝ => -x ^ 2 / 4 * s⁻¹) = (fun s : ℝ => -x ^ 2 / (4 * s)) := by
      funext s; field_simp
    have hval : -x ^ 2 / 4 * -(t ^ 2)⁻¹ = x ^ 2 / (4 * t ^ 2) := by
      field_simp
    rw [hfuneq] at hmul
    rwa [hval] at hmul
  -- Exponential factor `exp (e s)`.
  have hexp := he.exp
  -- Product rule: `∂ₜ (c · exp e) = c' · exp e + c · (exp e · e')`.
  have hmul := hc.mul hexp
  -- Rewrite to `K · (x²/(4t²) - 1/(2t))`.
  have hval :
      (-(1 : ℝ) / 2) * (4 * π * t) ^ (-(1 : ℝ) / 2 - 1) * (4 * π) *
          Real.exp (-x ^ 2 / (4 * t)) +
        (4 * π * t) ^ (-(1 : ℝ) / 2) *
          (Real.exp (-x ^ 2 / (4 * t)) * (x ^ 2 / (4 * t ^ 2))) =
      heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
    rw [heatKernel1D]
    -- Reduce `(4πt)^(-1/2-1)` to `(4πt)^(-1/2) · (4πt)⁻¹`.
    rw [show (-(1 : ℝ) / 2 - 1) = (-(1 : ℝ) / 2) + (-1) by ring,
      Real.rpow_add h4πtpos, Real.rpow_neg_one]
    field_simp
    ring
  rw [← hval]
  exact hmul

/-- **The 1D heat kernel solves the heat equation** `∂ₜ K = ∂ₓₓ K`: the time
derivative equals the spatial second derivative, both being
`K(t, x) · (x² / (4 t²) - 1 / (2 t))`. -/
theorem heatKernel1D_heatEquation {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel1D s x)
        (heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) t ∧
      HasDerivAt (fun y => heatKernel1D t y * (-y / (2 * t)))
        (heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) x :=
  ⟨hasDerivAt_heatKernel1D_time ht x, hasDerivAt_heatKernel1D_space_second ht x⟩

/-- The heat kernel is integrable in the space variable for `t > 0`. -/
theorem integrable_heatKernel1D {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => heatKernel1D t x) := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(4 * t)⁻¹ * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hconst := hgauss.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine hconst.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [heatKernel1D_apply]
  have hexp : -(4 * t)⁻¹ * x ^ 2 = -x ^ 2 / (4 * t) := by
    rw [neg_div, div_eq_inv_mul]; ring
  rw [hexp]

/-- The heat kernel is even in the space variable: `K(t, -x) = K(t, x)`. -/
@[simp] lemma heatKernel1D_neg (t x : ℝ) : heatKernel1D t (-x) = heatKernel1D t x := by
  simp [heatKernel1D]

/-- The heat kernel is nonnegative for `t > 0` (a convenience form of positivity for
integral/`L¹` arguments). -/
lemma heatKernel1D_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ heatKernel1D t x :=
  (heatKernel1D_pos ht x).le

/-- The `L¹` mass of the heat kernel is `1`: `∫ x, |K(t, x)| = 1` for `t > 0`. -/
theorem integral_norm_heatKernel1D {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, ‖heatKernel1D t x‖ = 1 := by
  have hnorm : (fun x : ℝ => ‖heatKernel1D t x‖) = fun x : ℝ => heatKernel1D t x := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel1D_nonneg ht x)]
  rw [hnorm, integral_heatKernel1D ht]

end AnalyticPDE
end RicciFlow
