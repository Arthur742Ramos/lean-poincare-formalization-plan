module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral

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

/-- The heat kernel attains its maximum `(4πt)^(-1/2)` at the centre: for `t > 0`,
`K(t, x) ≤ (4 π t)^(-1/2)`. -/
lemma heatKernel1D_le_prefactor {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel1D t x ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  rw [heatKernel1D]
  -- `exp(-x²/(4t)) ≤ 1` since the exponent is ≤ 0.
  have hexp_le : Real.exp (-x ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos_of_nonneg (sq_nonneg x)
    · positivity
  calc
    (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t))
        ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left hexp_le (heatKernel1D_prefactor_pos ht).le
    _ = (4 * π * t) ^ (-(1 : ℝ) / 2) := mul_one _

/-- The heat kernel is continuous in the space variable for any fixed `t`. -/
lemma continuous_heatKernel1D_space (t : ℝ) :
    Continuous (fun x : ℝ => heatKernel1D t x) := by
  unfold heatKernel1D
  exact continuous_const.mul
    (Real.continuous_exp.comp (by fun_prop))

/-- The reflected/translated kernel `y ↦ K(t, x - y)` is continuous. -/
lemma continuous_heatKernel1D_sub (t : ℝ) (x : ℝ) :
    Continuous (fun y => heatKernel1D t (x - y)) :=
  (continuous_heatKernel1D_space t).comp (continuous_const.sub continuous_id)

/-- Strict peak bound: away from the centre the heat kernel is strictly below its
maximum, `K(t, x) < (4πt)^(-1/2)` for `x ≠ 0`. -/
lemma heatKernel1D_lt_prefactor_of_ne {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ≠ 0) :
    heatKernel1D t x < (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  rw [heatKernel1D_apply]
  have hpre : 0 < (4 * π * t) ^ (-(1 : ℝ) / 2) := heatKernel1D_prefactor_pos ht
  have hxsq : 0 < x ^ 2 := by positivity
  have hneg : -x ^ 2 / (4 * t) < 0 := by
    apply div_neg_of_neg_of_pos
    · linarith
    · linarith
  have hexp : Real.exp (-x ^ 2 / (4 * t)) < 1 := Real.exp_lt_one_iff.mpr hneg
  calc (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t))
      < (4 * π * t) ^ (-(1 : ℝ) / 2) * 1 := mul_lt_mul_of_pos_left hexp hpre
    _ = (4 * π * t) ^ (-(1 : ℝ) / 2) := mul_one _

/-- The shifted heat kernel `y ↦ K(t, x - y)` is a.e.-strongly-measurable. -/
theorem aestronglyMeasurable_heatKernel1D_sub {t : ℝ} (x : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => heatKernel1D t (x - y)) volume :=
  ((continuous_heatKernel1D_space t).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable

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

/-- The heat kernel is differentiable in the space variable at each point. -/
lemma differentiableAt_heatKernel1D_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    DifferentiableAt ℝ (fun y => heatKernel1D t y) x :=
  (hasDerivAt_heatKernel1D_space ht x).differentiableAt

/-- The heat kernel is differentiable in the space variable. -/
lemma differentiable_heatKernel1D_space {t : ℝ} (ht : 0 < t) :
    Differentiable ℝ (fun y => heatKernel1D t y) :=
  fun x => (hasDerivAt_heatKernel1D_space ht x).differentiableAt

/-- The reflected/translated kernel `y ↦ K(t, x - y)` is differentiable. -/
lemma differentiable_heatKernel1D_space_neg_sub {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Differentiable ℝ (fun y => heatKernel1D t (x - y)) :=
  (differentiable_heatKernel1D_space ht).comp (differentiable_id.const_sub x)

/-- The spatial derivative of the heat kernel, as a `deriv`. -/
lemma deriv_heatKernel1D_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun y => heatKernel1D t y) x = heatKernel1D t x * (-x / (2 * t)) :=
  (hasDerivAt_heatKernel1D_space ht x).deriv

/-- The chain-rule derivative of the reflected/translated kernel `z ↦ K(t, z - y)`. -/
lemma hasDerivAt_heatKernel1D_space_sub {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => heatKernel1D t (z - y))
      (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) x := by
  have hin : HasDerivAt (fun z => z - y) 1 x := (hasDerivAt_id x).sub_const y
  have h := (hasDerivAt_heatKernel1D_space ht (x - y)).comp x hin
  simpa using h

/-- The chain-rule second spatial derivative of the reflected/translated kernel:
`∂ₓ (z ↦ ∂ₓK(t, z - y)) = K(t, x-y) · ((x-y)²/(4t²) - 1/(2t))`. -/
lemma hasDerivAt_heatKernel1D_space_second_sub {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => heatKernel1D t (z - y) * (-(z - y) / (2 * t)))
      (heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) x := by
  have hin : HasDerivAt (fun z => z - y) 1 x := (hasDerivAt_id x).sub_const y
  have h := (hasDerivAt_heatKernel1D_space_second ht (x - y)).comp x hin
  simpa only [Function.comp, mul_one] using h

/-- The negated kernel's spatial derivative. -/
theorem hasDerivAt_neg_heatKernel1D_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => - heatKernel1D t y) (- (heatKernel1D t x * (-x / (2 * t)))) x :=
  (hasDerivAt_heatKernel1D_space ht x).neg

/-- The heat kernel is differentiable in time at each positive time. -/
lemma differentiableAt_heatKernel1D_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    DifferentiableAt ℝ (fun s => heatKernel1D s x) t :=
  (hasDerivAt_heatKernel1D_time ht x).differentiableAt

/-- The time derivative of the heat kernel, as a `deriv`. -/
lemma deriv_heatKernel1D_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => heatKernel1D s x) t
      = heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) :=
  (hasDerivAt_heatKernel1D_time ht x).deriv

/-- The heat kernel is continuous in time at each positive time. -/
lemma continuousAt_heatKernel1D_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousAt (fun s => heatKernel1D s x) t :=
  (hasDerivAt_heatKernel1D_time ht x).continuousAt

/-- **The heat equation as an equality of `deriv`s**: the time derivative equals the
spatial second derivative at every point. -/
theorem heatKernel1D_deriv_time_eq_deriv_space_second {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => heatKernel1D s x) t
      = deriv (fun y => heatKernel1D t y * (-y / (2 * t))) x := by
  rw [(hasDerivAt_heatKernel1D_time ht x).deriv,
      (hasDerivAt_heatKernel1D_space_second ht x).deriv]

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

/-- Nonnegativity of the shifted kernel. -/
lemma heatKernel1D_sub_nonneg {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 ≤ heatKernel1D t (x - y) :=
  heatKernel1D_nonneg ht (x - y)

/-- The heat kernel equals its own absolute value. -/
lemma abs_heatKernel1D {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |heatKernel1D t x| = heatKernel1D t x :=
  abs_of_nonneg (heatKernel1D_nonneg ht x)

/-- Absolute-value form of the peak bound: `|K(t, x)| ≤ (4πt)^(-1/2)`. -/
lemma abs_heatKernel1D_le_prefactor {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |heatKernel1D t x| ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  rw [abs_of_nonneg (heatKernel1D_nonneg ht x)]
  exact heatKernel1D_le_prefactor ht x

/-- The squared peak bound. -/
lemma sq_heatKernel1D_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel1D t x ^ 2 ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ 2 :=
  pow_le_pow_left₀ (heatKernel1D_nonneg ht x) (heatKernel1D_le_prefactor ht x) 2

/-- The squared peak bound in absolute-value form. -/
lemma sq_abs_heatKernel1D_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |heatKernel1D t x| ^ 2 ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ 2 := by
  rw [abs_heatKernel1D ht]; exact sq_heatKernel1D_le ht x

/-- The heat kernel is monotone decreasing in `|x|`: if `|x| ≤ |y|` then
`K(t, y) ≤ K(t, x)`. -/
lemma heatKernel1D_le_of_abs_le {t : ℝ} (ht : 0 < t) {x y : ℝ}
    (h : |x| ≤ |y|) : heatKernel1D t y ≤ heatKernel1D t x := by
  rw [heatKernel1D_apply, heatKernel1D_apply]
  apply mul_le_mul_of_nonneg_left _ (heatKernel1D_prefactor_pos ht).le
  apply Real.exp_le_exp.mpr
  have hxy : x ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs x, ← sq_abs y]; gcongr
  have h4t : (0 : ℝ) < 4 * t := by positivity
  gcongr

/-- The `L¹` mass of the heat kernel is `1`: `∫ x, |K(t, x)| = 1` for `t > 0`. -/
theorem integral_norm_heatKernel1D {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, ‖heatKernel1D t x‖ = 1 := by
  have hnorm : (fun x : ℝ => ‖heatKernel1D t x‖) = fun x : ℝ => heatKernel1D t x := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel1D_nonneg ht x)]
  rw [hnorm, integral_heatKernel1D ht]

/-- Shifted total mass: `∫ y, K(t, x - y) dy = 1` for `t > 0`.  This is the fact
that the heat semigroup preserves constants (`Hₜ 1 = 1`). -/
theorem integral_heatKernel1D_sub {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y : ℝ, heatKernel1D t (x - y) = 1 := by
  -- By evenness `K(t, x - y) = K(t, y - x) = K(t, y + (-x))`.
  have hfun : (fun y : ℝ => heatKernel1D t (x - y))
      = (fun y : ℝ => heatKernel1D t (y + -x)) := by
    funext y
    rw [← heatKernel1D_neg t (x - y)]
    congr 1
    ring
  rw [hfun, integral_add_right_eq_self (fun y : ℝ => heatKernel1D t y) (-x)]
  exact integral_heatKernel1D ht

/-- The shifted heat kernel `y ↦ K(t, x - y)` is integrable for `t > 0`. -/
theorem integrable_heatKernel1D_sub {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => heatKernel1D t (x - y)) :=
  (integrable_heatKernel1D ht).comp_sub_left x

/-- The 1D heat semigroup acting on a function `f`:
`(heatSemigroup1D t f) x = ∫ y, K(t, x - y) · f y dy`.  For `t > 0` and bounded
continuous `f` this is the solution of the heat equation with initial data `f`. -/
def heatSemigroup1D (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, heatKernel1D t (x - y) * f y

/-- The heat semigroup fixes constants: `heatSemigroup1D t (fun _ => c) x = c` for `t > 0`. -/
theorem heatSemigroup1D_const {t : ℝ} (ht : 0 < t) (c x : ℝ) :
    heatSemigroup1D t (fun _ => c) x = c := by
  rw [heatSemigroup1D]
  rw [integral_mul_const, integral_heatKernel1D_sub ht, one_mul]

/-- **Maximum principle / sup-norm contraction for the heat semigroup.**  If
`|f y| ≤ C` for all `y`, then `|heatSemigroup1D t f x| ≤ C` for `t > 0`.
(The domination by the integrable `K(t, x - ·)·C` makes the integrability of the
convolution integrand unnecessary as a hypothesis.) -/
theorem abs_heatSemigroup1D_le {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ} (x : ℝ)
    (hf : ∀ y, |f y| ≤ C) :
    |heatSemigroup1D t f x| ≤ C := by
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg _) (hf 0)
  -- Pointwise: `|K(t,x-y)·f y| ≤ K(t,x-y)·C`.
  have hpt : ∀ y, ‖heatKernel1D t (x - y) * f y‖ ≤ heatKernel1D t (x - y) * C := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel1D_nonneg ht (x - y))]
    exact mul_le_mul_of_nonneg_left (hf y) (heatKernel1D_nonneg ht (x - y))
  -- Integral bound.
  have hbound :
      ∫ y : ℝ, heatKernel1D t (x - y) * C = C := by
    rw [integral_mul_const, integral_heatKernel1D_sub ht, one_mul]
  calc
    |heatSemigroup1D t f x|
        = ‖∫ y : ℝ, heatKernel1D t (x - y) * f y‖ := by
          rw [heatSemigroup1D, Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, heatKernel1D t (x - y) * C := by
          refine le_trans (norm_integral_le_integral_norm _) ?_
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun y ↦ norm_nonneg _)) ?_
            (Filter.Eventually.of_forall hpt)
          exact (integrable_heatKernel1D_sub ht x).mul_const C
    _ = C := hbound

/-- **Positivity preservation for the heat semigroup.**  If `f ≥ 0`, then
`heatSemigroup1D t f x ≥ 0` for `t > 0`. -/
theorem heatSemigroup1D_nonneg {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (x : ℝ)
    (hf : ∀ y, 0 ≤ f y) :
    0 ≤ heatSemigroup1D t f x := by
  rw [heatSemigroup1D]
  refine integral_nonneg ?_
  intro y
  exact mul_nonneg (heatKernel1D_nonneg ht (x - y)) (hf y)

/-- The convolution integrand `y ↦ K(t, x - y) · f y` is integrable for `t > 0`
whenever `f` is a.e.-strongly-measurable and bounded.  This unblocks linearity and
the two-sided maximum principle for the heat semigroup. -/
theorem integrable_heatKernel1D_sub_mul {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y : ℝ => heatKernel1D t (x - y) * f y) :=
  (integrable_heatKernel1D_sub ht x).mul_bdd hmeas
    (Filter.Eventually.of_forall hbound)

/-- Linearity of the heat semigroup in the data (for bounded measurable inputs):
`Hₜ(f + g) = Hₜf + Hₜg`. -/
theorem heatSemigroup1D_add {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ} {C : ℝ} (x : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ C) :
    heatSemigroup1D t (fun y => f y + g y) x =
      heatSemigroup1D t f x + heatSemigroup1D t g x := by
  rw [heatSemigroup1D, heatSemigroup1D, heatSemigroup1D]
  have hsplit : ∀ y, heatKernel1D t (x - y) * (f y + g y)
      = heatKernel1D t (x - y) * f y + heatKernel1D t (x - y) * g y := by
    intro y; ring
  simp only [hsplit]
  exact integral_add (integrable_heatKernel1D_sub_mul ht x hfm hfb)
    (integrable_heatKernel1D_sub_mul ht x hgm hgb)

/-- Scalar homogeneity of the heat semigroup: `Hₜ(c·f) = c·Hₜf`. -/
theorem heatSemigroup1D_smul {t : ℝ} (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heatSemigroup1D t (fun y => c * f y) x = c * heatSemigroup1D t f x := by
  unfold heatSemigroup1D
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Negation linearity of the heat semigroup: `Hₜ(-f) = -Hₜf`. -/
theorem heatSemigroup1D_neg {t : ℝ} (f : ℝ → ℝ) (x : ℝ) :
    heatSemigroup1D t (fun y => - f y) x = - heatSemigroup1D t f x := by
  unfold heatSemigroup1D
  simp_rw [mul_neg]
  rw [integral_neg]

/-- Subtraction linearity of the heat semigroup (for bounded measurable inputs):
`Hₜ(f - g) = Hₜf - Hₜg`. -/
theorem heatSemigroup1D_sub {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ} {C : ℝ} (x : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ C) :
    heatSemigroup1D t (fun y => f y - g y) x
      = heatSemigroup1D t f x - heatSemigroup1D t g x := by
  unfold heatSemigroup1D
  have hsplit : ∀ y, heatKernel1D t (x - y) * (f y - g y)
      = heatKernel1D t (x - y) * f y - heatKernel1D t (x - y) * g y := by
    intro y; ring
  simp only [hsplit]
  exact integral_sub (integrable_heatKernel1D_sub_mul ht x hfm hfb)
    (integrable_heatKernel1D_sub_mul ht x hgm hgb)

/-- The heat semigroup annihilates the zero function: `Hₜ0 = 0`. -/
theorem heatSemigroup1D_zero {t : ℝ} (x : ℝ) :
    heatSemigroup1D t (fun _ => 0) x = 0 := by
  unfold heatSemigroup1D
  simp

/-- One-sided constant bound: `|f| ≤ C ⟹ Hₜf ≤ C`. -/
theorem heatSemigroup1D_le_of_le {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hf : ∀ y, |f y| ≤ C) : heatSemigroup1D t f x ≤ C :=
  le_of_abs_le (abs_heatSemigroup1D_le ht x hf)

/-- One-sided constant bound: `|f| ≤ C ⟹ -C ≤ Hₜf`. -/
theorem neg_le_heatSemigroup1D {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hf : ∀ y, |f y| ≤ C) : -C ≤ heatSemigroup1D t f x :=
  (abs_le.mp (abs_heatSemigroup1D_le ht x hf)).1

/-- Adding a constant commutes with the heat semigroup: `Hₜ(f + m) = Hₜf + m`. -/
theorem heatSemigroup1D_add_const {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x m : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroup1D t (fun y => f y + m) x = heatSemigroup1D t f x + m := by
  unfold heatSemigroup1D
  have hsplit : ∀ y, heatKernel1D t (x - y) * (f y + m)
      = heatKernel1D t (x - y) * f y + heatKernel1D t (x - y) * m := by
    intro y; ring
  simp only [hsplit]
  rw [integral_add (integrable_heatKernel1D_sub_mul ht x hfm hfb)
    ((integrable_heatKernel1D_sub ht x).mul_const m)]
  rw [integral_mul_const, integral_heatKernel1D_sub ht, one_mul]


theorem heatSemigroup1D_sub_const {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ} (x m : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroup1D t (fun y => f y - m) x = heatSemigroup1D t f x - m := by
  rw [heatSemigroup1D, heatSemigroup1D]
  have hsplit : ∀ y, heatKernel1D t (x - y) * (f y - m)
      = heatKernel1D t (x - y) * f y - heatKernel1D t (x - y) * m := by
    intro y; ring
  simp only [hsplit]
  rw [integral_sub (integrable_heatKernel1D_sub_mul ht x hfm hfb)
    ((integrable_heatKernel1D_sub ht x).mul_const m)]
  rw [integral_mul_const, integral_heatKernel1D_sub ht, one_mul]

/-- **Two-sided maximum principle.**  If `c ≤ f y ≤ C` for all `y` and `f` is
a.e.-strongly-measurable, then `c ≤ heatSemigroup1D t f x ≤ C` for `t > 0`. -/
theorem heatSemigroup1D_mem_Icc {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {c C : ℝ} (x : ℝ)
    (hfm : AEStronglyMeasurable f) (hlo : ∀ y, c ≤ f y) (hhi : ∀ y, f y ≤ C) :
    heatSemigroup1D t f x ∈ Set.Icc c C := by
  set m := (c + C) / 2 with hm
  set R := (C - c) / 2 with hR
  -- `|f y - m| ≤ R`, and `‖f y‖ ≤ max |c| |C|` gives the boundedness for linearity.
  have hfb : ∀ y, ‖f y‖ ≤ |c| + |C| := by
    intro y
    have hc1 : -|c| ≤ c := neg_abs_le c
    have hC1 : C ≤ |C| := le_abs_self C
    have hcnn : 0 ≤ |c| := abs_nonneg c
    have hCnn : 0 ≤ |C| := abs_nonneg C
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hlo y], by linarith [hhi y]⟩
  have hshift : ∀ y, |f y - m| ≤ R := by
    intro y; rw [abs_le]; constructor <;> [linarith [hlo y]; linarith [hhi y]]
  have hbound := abs_heatSemigroup1D_le ht x (f := fun y => f y - m) (C := R) hshift
  rw [heatSemigroup1D_sub_const ht x m hfm hfb] at hbound
  rw [abs_le] at hbound
  exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

/-- **Comparison principle for the heat semigroup.**  If `f ≤ g` pointwise and both
convolution integrands are integrable, then `heatSemigroup1D t f x ≤ heatSemigroup1D t g x`. -/
theorem heatSemigroup1D_mono {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ} (x : ℝ)
    (hfg : ∀ y, f y ≤ g y)
    (hfint : Integrable (fun y : ℝ => heatKernel1D t (x - y) * f y))
    (hgint : Integrable (fun y : ℝ => heatKernel1D t (x - y) * g y)) :
    heatSemigroup1D t f x ≤ heatSemigroup1D t g x := by
  rw [heatSemigroup1D, heatSemigroup1D]
  refine integral_mono hfint hgint ?_
  intro y
  exact mul_le_mul_of_nonneg_left (hfg y) (heatKernel1D_nonneg ht (x - y))

/-- Comparison principle from boundedness hypotheses: `f ≤ g` (both bounded
measurable) implies `Hₜf ≤ Hₜg`. -/
theorem heatSemigroup1D_le_heatSemigroup1D_of_le {t : ℝ} (ht : 0 < t) {f g : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ C) (hfg : ∀ y, f y ≤ g y) :
    heatSemigroup1D t f x ≤ heatSemigroup1D t g x :=
  heatSemigroup1D_mono ht x hfg
    (integrable_heatKernel1D_sub_mul ht x hfm hfb)
    (integrable_heatKernel1D_sub_mul ht x hgm hgb)

/-- For nonnegative bounded data, the semigroup output stays in `[0, C]`. -/
theorem heatSemigroup1D_mem_Icc_of_nonneg {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (h0 : ∀ y, 0 ≤ f y) (hC : ∀ y, f y ≤ C) :
    heatSemigroup1D t f x ∈ Set.Icc 0 C :=
  heatSemigroup1D_mem_Icc ht x hfm h0 hC

/-- **Spatial differentiability of the heat semigroup.**  For bounded
a.e.-strongly-measurable `f` and `t > 0`, the convolution `z ↦ Hₜf z` is
differentiable, and its derivative is obtained by differentiating the kernel under
the integral sign:
`∂ₓ Hₜf = ∫ y, ∂ₓK(t, x - y) · f y`.
The proof uses Leibniz's rule (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
with an explicit Gaussian dominating envelope. -/
theorem hasDerivAt_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt (fun z => heatSemigroup1D t f z)
      (∫ y, (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y) x := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set F : ℝ → ℝ → ℝ := fun z y => heatKernel1D t (z - y) * f y with hF
  set F' : ℝ → ℝ → ℝ := fun z y => heatKernel1D t (z - y) * (-(z - y) / (2 * t)) * f y with hF'
  set M := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) * C / (2 * t) with hM
  set bound : ℝ → ℝ := fun y => M * ((1 + |y - x|) * Real.exp (-(y - x) ^ 2 / (8 * t)))
    with hbound
  have hs : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x (by norm_num)
  have hFmeas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    exact (aestronglyMeasurable_heatKernel1D_sub z).mul hfm
  have hFint : Integrable (F x) volume :=
    integrable_heatKernel1D_sub_mul ht x hfm hfb
  have hF'meas : AEStronglyMeasurable (F' x) volume := by
    refine (((continuous_heatKernel1D_space t).comp
      (continuous_const.sub continuous_id)).mul ?_).aestronglyMeasurable.mul hfm
    fun_prop
  have hbnd : ∀ᵐ y ∂(volume : Measure ℝ), ∀ z ∈ Metric.ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hzle : |z - x| ≤ 1 := hz.le
    have hpre : (0 : ℝ) < (4 * π * t) ^ (-(1 : ℝ) / 2) := heatKernel1D_prefactor_pos ht
    have hnorm : ‖F' z y‖
        = heatKernel1D t (z - y) * (|z - y| / (2 * t)) * |f y| := by
      simp only [hF']
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_neg,
        abs_of_pos h2t, abs_of_nonneg (heatKernel1D_nonneg ht (z - y))]
    rw [hnorm]
    have hzx2 : (z - x) ^ 2 ≤ 1 := by
      rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_one, Real.sqrt_sq_eq_abs]
      exact hzle
    have hK : heatKernel1D t (z - y)
        ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t))
            * Real.exp (-(y - x) ^ 2 / (8 * t)) := by
      rw [heatKernel1D_apply, mul_assoc ((4 * π * t) ^ (-(1 : ℝ) / 2)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hpre.le
      apply Real.exp_le_exp.mpr
      have hq : (z - y) ^ 2 ≥ (y - x) ^ 2 / 2 - (z - x) ^ 2 := by
        nlinarith [sq_nonneg ((y - x) - 2 * (z - x))]
      rw [← sub_nonneg]
      have key : 1 / (4 * t) + -(y - x) ^ 2 / (8 * t) - -(z - y) ^ 2 / (4 * t)
          = (2 - ((y - x) ^ 2 - 2 * (z - y) ^ 2)) / (8 * t) := by
        field_simp; ring
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hq, hzx2]
    have hzy : |z - y| ≤ 1 + |y - x| := by
      have hzysplit : z - y = (z - x) + (x - y) := by ring
      calc |z - y| ≤ |z - x| + |x - y| := by rw [hzysplit]; exact abs_add_le _ _
        _ ≤ 1 + |y - x| := by rw [abs_sub_comm x y]; linarith
    set Eg := Real.exp (-(y - x) ^ 2 / (8 * t)) with hEg
    have hEgpos : 0 < Eg := Real.exp_pos _
    set P := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) with hP
    have hPpos : 0 < P := by positivity
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hub : heatKernel1D t (z - y) * (|z - y| / (2 * t)) * |f y|
        ≤ (P * Eg) * ((1 + |y - x|) / (2 * t)) * C := by
      apply mul_le_mul _ hfa (abs_nonneg _) (by positivity)
      apply mul_le_mul hK _ (by positivity) (by positivity)
      exact div_le_div_of_nonneg_right hzy h2t.le
    refine hub.trans (le_of_eq ?_)
    simp only [hbound, hM, hP]; ring
  have hboundint : Integrable bound volume := by
    have hb8 : 0 < (8 * t)⁻¹ := by positivity
    have h0 : Integrable (fun w : ℝ => Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
      integrable_exp_neg_mul_sq hb8
    have h1 : Integrable (fun w : ℝ => w ^ (1 : ℝ) * Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
    have hbase : Integrable (fun w : ℝ => (1 + |w|) * Real.exp (-w ^ 2 / (8 * t))) := by
      have hsum := h0.add h1.abs
      refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [Pi.add_apply, Real.rpow_one]
      have hexp : -(8 * t)⁻¹ * w ^ 2 = -w ^ 2 / (8 * t) := by
        rw [neg_div, div_eq_inv_mul]; ring
      rw [hexp, abs_mul, abs_of_pos (Real.exp_pos _)]; ring
    have htrans : Integrable
        (fun y : ℝ => (1 + |y - x|) * Real.exp (-(y - x) ^ 2 / (8 * t))) :=
      hbase.comp_sub_right x
    simpa only [hbound] using htrans.const_mul M
  have hderiv : ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z => F z y) (F' z y) z := by
    filter_upwards with y z _
    have hin : HasDerivAt (fun z : ℝ => z - y) 1 z := by
      simpa using (hasDerivAt_id z).sub_const y
    have hcomp : HasDerivAt (fun z : ℝ => heatKernel1D t (z - y))
        (heatKernel1D t (z - y) * (-(z - y) / (2 * t))) z := by
      have := (hasDerivAt_heatKernel1D_space ht (z - y)).comp z hin
      simpa using this
    have := hcomp.mul_const (f y)
    simpa only [hF, hF'] using this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (x₀ := x) (bound := bound) (s := Metric.ball x 1)
    hs hFmeas hFint hF'meas hbnd hboundint hderiv
  simpa only [hF, hF', heatSemigroup1D] using key.2

/-- The heat semigroup is spatially differentiable (for bounded measurable data). -/
theorem differentiableAt_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    DifferentiableAt ℝ (fun z => heatSemigroup1D t f z) x :=
  (hasDerivAt_heatSemigroup1D_space ht x hfm hfb).differentiableAt

/-- The spatial derivative of the heat semigroup, as a `deriv`. -/
theorem deriv_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (fun z => heatSemigroup1D t f z) x
      = ∫ y, (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y :=
  (hasDerivAt_heatSemigroup1D_space ht x hfm hfb).deriv

/-- The heat semigroup is spatially continuous (for bounded measurable data). -/
theorem continuousAt_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    ContinuousAt (fun z => heatSemigroup1D t f z) x :=
  (hasDerivAt_heatSemigroup1D_space ht x hfm hfb).continuousAt

/-- The heat semigroup is (globally) spatially continuous for bounded data. -/
theorem continuous_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    Continuous (fun z => heatSemigroup1D t f z) :=
  continuous_iff_continuousAt.mpr (fun x => continuousAt_heatSemigroup1D_space ht x hfm hfb)

/-- The heat semigroup is (globally) spatially differentiable for bounded data. -/
theorem differentiable_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    Differentiable ℝ (fun z => heatSemigroup1D t f z) :=
  fun x => differentiableAt_heatSemigroup1D_space ht x hfm hfb

/-! ## The `n`-dimensional Euclidean heat kernel

The `n`-dimensional heat kernel is the product of the 1D kernels over the
coordinates.  We work on `Fin n → ℝ` with the product Lebesgue measure. -/

/-- The `n`-dimensional Euclidean heat kernel on `Fin n → ℝ`:
`Kₙ(t, x) = ∏ i, K(t, x i)`. -/
def heatKernelND {n : ℕ} (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, heatKernel1D t (x i)

lemma heatKernelND_apply {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    heatKernelND t x = ∏ i, heatKernel1D t (x i) := rfl

/-- The `n`-dimensional heat kernel is strictly positive for `t > 0`. -/
lemma heatKernelND_pos {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    0 < heatKernelND t x :=
  Finset.prod_pos (fun i _ => heatKernel1D_pos ht (x i))

/-- The `n`-dimensional heat kernel is nonnegative for `t > 0`. -/
lemma heatKernelND_nonneg {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    0 ≤ heatKernelND t x :=
  (heatKernelND_pos ht x).le

/-- The `n`-dimensional heat kernel is continuous in the space variable. -/
lemma continuous_heatKernelND {n : ℕ} (t : ℝ) :
    Continuous (fun x : Fin n → ℝ => heatKernelND t x) := by
  unfold heatKernelND
  refine continuous_finset_prod Finset.univ (fun i _ => ?_)
  exact (continuous_heatKernel1D_space t).comp (continuous_apply i)

/-- The shifted `n`-dimensional heat kernel `y ↦ Kₙ(t, x - y)` is continuous. -/
theorem continuous_heatKernelND_sub {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    Continuous (fun y : Fin n → ℝ => heatKernelND t (x - y)) :=
  (continuous_heatKernelND t).comp (continuous_const.sub continuous_id)

/-- The shifted `n`-dimensional heat kernel is a.e.-strongly-measurable. -/
theorem aestronglyMeasurable_heatKernelND_sub {n : ℕ} {t : ℝ} (x : Fin n → ℝ) :
    AEStronglyMeasurable (fun y : Fin n → ℝ => heatKernelND t (x - y)) volume :=
  (continuous_heatKernelND_sub t x).aestronglyMeasurable

/-- The `n`-dimensional heat kernel is even in the space variable. -/
lemma heatKernelND_neg {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    heatKernelND t (-x) = heatKernelND t x := by
  simp [heatKernelND, Pi.neg_apply]

/-- The `n`-dimensional peak bound: `Kₙ(t, x) ≤ ((4πt)^(-1/2))^n`. -/
lemma heatKernelND_le_pow {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    heatKernelND t x ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ n := by
  rw [heatKernelND_apply]
  calc ∏ i, heatKernel1D t (x i)
      ≤ ∏ _i : Fin n, (4 * π * t) ^ (-(1 : ℝ) / 2) := by
        apply Finset.prod_le_prod
        · intro i _; exact heatKernel1D_nonneg ht (x i)
        · intro i _; exact heatKernel1D_le_prefactor ht (x i)
    _ = ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Total mass of the `n`-dimensional heat kernel: `∫ x, Kₙ(t, x) = 1` for `t > 0`,
via Fubini and the 1D mass. -/
theorem integral_heatKernelND {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∫ x : Fin n → ℝ, heatKernelND t x = 1 := by
  simp only [heatKernelND]
  rw [integral_fin_nat_prod_volume_eq_prod (fun _ (z : ℝ) => heatKernel1D t z)]
  simp only [integral_heatKernel1D ht, Finset.prod_const_one]

/-- The `n`-dimensional heat kernel is integrable for `t > 0`. -/
theorem integrable_heatKernelND {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Fin n → ℝ => heatKernelND t x) := by
  have : (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) := by
    rw [volume_pi]
  rw [show (fun x : Fin n → ℝ => heatKernelND t x)
      = (fun x : Fin n → ℝ => ∏ i, heatKernel1D t (x i)) from rfl, this]
  exact Integrable.fin_nat_prod (fun _ => integrable_heatKernel1D ht)

/-- The `L¹` mass of the `n`-dimensional heat kernel is `1` for `t > 0`. -/
theorem integral_norm_heatKernelND {n : ℕ} {t : ℝ} (ht : 0 < t) :
    ∫ x : Fin n → ℝ, ‖heatKernelND t x‖ = 1 := by
  have hnorm : (fun x : Fin n → ℝ => ‖heatKernelND t x‖)
      = fun x : Fin n → ℝ => heatKernelND t x := by
    funext x; rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelND_nonneg ht x)]
  rw [hnorm, integral_heatKernelND ht]

/-- Shifted total mass of the `n`-dimensional heat kernel: `∫ y, Kₙ(t, x - y) dy = 1`
for `t > 0`.  This is the constant-preservation property of the `n`-dimensional heat
semigroup. -/
theorem integral_heatKernelND_sub {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, heatKernelND t (x - y) = 1 := by
  -- `Kₙ(t, x - y) = ∏ i, K(t, x i - y i)`; Fubini reduces to the 1D shifted mass.
  have hfun : (fun y : Fin n → ℝ => heatKernelND t (x - y))
      = fun y : Fin n → ℝ => ∏ i, heatKernel1D t (x i - y i) := by
    funext y; rw [heatKernelND]; rfl
  rw [hfun,
    integral_fin_nat_prod_volume_eq_prod (fun i (z : ℝ) => heatKernel1D t (x i - z))]
  simp only [integral_heatKernel1D_sub ht, Finset.prod_const_one]

/-- The `n`-dimensional heat semigroup acting on `f : (Fin n → ℝ) → ℝ`:
`(heatSemigroupND t f) x = ∫ y, Kₙ(t, x - y) · f y dy`. -/
def heatSemigroupND {n : ℕ} (t : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, heatKernelND t (x - y) * f y

/-- The `n`-dimensional heat semigroup fixes constants. -/
theorem heatSemigroupND_const {n : ℕ} {t : ℝ} (ht : 0 < t) (c : ℝ) (x : Fin n → ℝ) :
    heatSemigroupND t (fun _ => c) x = c := by
  rw [heatSemigroupND, integral_mul_const, integral_heatKernelND_sub ht, one_mul]

/-- Scalar homogeneity of the `n`-dimensional heat semigroup: `Hₜ(c·f) = c·Hₜf`. -/
theorem heatSemigroupND_smul {n : ℕ} {t : ℝ} (c : ℝ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    heatSemigroupND t (fun y => c * f y) x = c * heatSemigroupND t f x := by
  unfold heatSemigroupND
  simp_rw [mul_left_comm]
  rw [integral_const_mul]

/-- Negation linearity of the `n`-dimensional heat semigroup: `Hₜ(-f) = -Hₜf`. -/
theorem heatSemigroupND_neg {n : ℕ} {t : ℝ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    heatSemigroupND t (fun y => - f y) x = - heatSemigroupND t f x := by
  unfold heatSemigroupND
  simp_rw [mul_neg]
  rw [integral_neg]

/-- `n`-dimensional heat-kernel nonnegativity gives semigroup positivity preservation. -/
theorem heatSemigroupND_nonneg {n : ℕ} {t : ℝ} (ht : 0 < t) {f : (Fin n → ℝ) → ℝ}
    (x : Fin n → ℝ) (hf : ∀ y, 0 ≤ f y) :
    0 ≤ heatSemigroupND t f x := by
  rw [heatSemigroupND]
  refine integral_nonneg ?_
  intro y
  exact mul_nonneg (heatKernelND_nonneg ht (x - y)) (hf y)

/-- The shifted `n`-dimensional heat kernel `y ↦ Kₙ(t, x - y)` is integrable for `t > 0`. -/
theorem integrable_heatKernelND_sub {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => heatKernelND t (x - y)) :=
  (integrable_heatKernelND ht).comp_sub_left x

/-- **Maximum principle for the `n`-dimensional heat semigroup.**  If `|f y| ≤ C`
for all `y`, then `|heatSemigroupND t f x| ≤ C` for `t > 0`. -/
theorem abs_heatSemigroupND_le {n : ℕ} {t : ℝ} (ht : 0 < t) {f : (Fin n → ℝ) → ℝ}
    {C : ℝ} (x : Fin n → ℝ) (hf : ∀ y, |f y| ≤ C) :
    |heatSemigroupND t f x| ≤ C := by
  have hpt : ∀ y, ‖heatKernelND t (x - y) * f y‖ ≤ heatKernelND t (x - y) * C := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelND_nonneg ht (x - y))]
    exact mul_le_mul_of_nonneg_left (hf y) (heatKernelND_nonneg ht (x - y))
  have hbound : ∫ y : Fin n → ℝ, heatKernelND t (x - y) * C = C := by
    rw [integral_mul_const, integral_heatKernelND_sub ht, one_mul]
  calc
    |heatSemigroupND t f x|
        = ‖∫ y : Fin n → ℝ, heatKernelND t (x - y) * f y‖ := by
          rw [heatSemigroupND, Real.norm_eq_abs]
    _ ≤ ∫ y : Fin n → ℝ, heatKernelND t (x - y) * C := by
          refine le_trans (norm_integral_le_integral_norm _) ?_
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun y ↦ norm_nonneg _)) ?_
            (Filter.Eventually.of_forall hpt)
          exact (integrable_heatKernelND_sub ht x).mul_const C
    _ = C := hbound

/-- The `n`-dimensional heat semigroup annihilates the zero function. -/
theorem heatSemigroupND_zero {n : ℕ} {t : ℝ} (x : Fin n → ℝ) :
    heatSemigroupND t (fun _ => 0) x = 0 := by
  unfold heatSemigroupND
  simp

/-- One-sided constant bound in `n` dimensions: `|f| ≤ C ⟹ Hₜf ≤ C`. -/
theorem heatSemigroupND_le_of_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hf : ∀ y, |f y| ≤ C) : heatSemigroupND t f x ≤ C :=
  le_of_abs_le (abs_heatSemigroupND_le ht x hf)

/-- The `n`-dim convolution integrand `y ↦ Kₙ(t, x - y) · f y` is integrable for
bounded a.e.-strongly-measurable `f`. -/
theorem integrable_heatKernelND_sub_mul {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y : Fin n → ℝ => heatKernelND t (x - y) * f y) :=
  (integrable_heatKernelND_sub ht x).mul_bdd hmeas
    (Filter.Eventually.of_forall hbound)

/-- Additive linearity of the `n`-dimensional heat semigroup (for bounded measurable
inputs): `Hₜ(f + g) = Hₜf + Hₜg`. -/
theorem heatSemigroupND_add {n : ℕ} {t : ℝ} (ht : 0 < t) {f g : (Fin n → ℝ) → ℝ}
    {C : ℝ} (x : Fin n → ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ C) :
    heatSemigroupND t (fun y => f y + g y) x
      = heatSemigroupND t f x + heatSemigroupND t g x := by
  unfold heatSemigroupND
  have hsplit : ∀ y, heatKernelND t (x - y) * (f y + g y)
      = heatKernelND t (x - y) * f y + heatKernelND t (x - y) * g y := by
    intro y; ring
  simp only [hsplit]
  rw [integral_add (integrable_heatKernelND_sub_mul ht x hfm hfb)
    (integrable_heatKernelND_sub_mul ht x hgm hgb)]

/-- Subtraction linearity of the `n`-dimensional heat semigroup (for bounded
measurable inputs): `Hₜ(f - g) = Hₜf - Hₜg`. -/
theorem heatSemigroupND_sub {n : ℕ} {t : ℝ} (ht : 0 < t) {f g : (Fin n → ℝ) → ℝ}
    {C : ℝ} (x : Fin n → ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ C) :
    heatSemigroupND t (fun y => f y - g y) x
      = heatSemigroupND t f x - heatSemigroupND t g x := by
  unfold heatSemigroupND
  have hsplit : ∀ y, heatKernelND t (x - y) * (f y - g y)
      = heatKernelND t (x - y) * f y - heatKernelND t (x - y) * g y := by
    intro y; ring
  simp only [hsplit]
  rw [integral_sub (integrable_heatKernelND_sub_mul ht x hfm hfb)
    (integrable_heatKernelND_sub_mul ht x hgm hgb)]

/-- Subtracting a constant commutes with the `n`-dimensional heat semigroup. -/
theorem heatSemigroupND_sub_const {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (m : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroupND t (fun y => f y - m) x = heatSemigroupND t f x - m := by
  rw [heatSemigroupND, heatSemigroupND]
  have hsplit : ∀ y, heatKernelND t (x - y) * (f y - m)
      = heatKernelND t (x - y) * f y - heatKernelND t (x - y) * m := by
    intro y; ring
  simp only [hsplit]
  rw [integral_sub (integrable_heatKernelND_sub_mul ht x hfm hfb)
    ((integrable_heatKernelND_sub ht x).mul_const m)]
  rw [integral_mul_const, integral_heatKernelND_sub ht, one_mul]

/-- Adding a constant commutes with the `n`-dimensional heat semigroup. -/
theorem heatSemigroupND_add_const {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (m : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroupND t (fun y => f y + m) x = heatSemigroupND t f x + m := by
  rw [heatSemigroupND, heatSemigroupND]
  have hsplit : ∀ y, heatKernelND t (x - y) * (f y + m)
      = heatKernelND t (x - y) * f y + heatKernelND t (x - y) * m := by
    intro y; ring
  simp only [hsplit]
  rw [integral_add (integrable_heatKernelND_sub_mul ht x hfm hfb)
    ((integrable_heatKernelND_sub ht x).mul_const m)]
  rw [integral_mul_const, integral_heatKernelND_sub ht, one_mul]


theorem heatSemigroupND_mem_Icc {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {c C : ℝ} (x : Fin n → ℝ)
    (hfm : AEStronglyMeasurable f) (hlo : ∀ y, c ≤ f y) (hhi : ∀ y, f y ≤ C) :
    heatSemigroupND t f x ∈ Set.Icc c C := by
  set m := (c + C) / 2 with hm
  set R := (C - c) / 2 with hR
  have hfb : ∀ y, ‖f y‖ ≤ |c| + |C| := by
    intro y
    have hc1 : -|c| ≤ c := neg_abs_le c
    have hC1 : C ≤ |C| := le_abs_self C
    have hcnn : 0 ≤ |c| := abs_nonneg c
    have hCnn : 0 ≤ |C| := abs_nonneg C
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hlo y], by linarith [hhi y]⟩
  have hshift : ∀ y, |f y - m| ≤ R := by
    intro y; rw [abs_le]; constructor <;> [linarith [hlo y]; linarith [hhi y]]
  have hbound := abs_heatSemigroupND_le ht x (f := fun y => f y - m) (C := R) hshift
  rw [heatSemigroupND_sub_const ht x m hfm hfb] at hbound
  rw [abs_le] at hbound
  exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

/-- **Comparison principle for the `n`-dimensional heat semigroup.**  If `f ≤ g`
pointwise and both convolution integrands are integrable, then
`heatSemigroupND t f x ≤ heatSemigroupND t g x`. -/
theorem heatSemigroupND_mono {n : ℕ} {t : ℝ} (ht : 0 < t) {f g : (Fin n → ℝ) → ℝ}
    (x : Fin n → ℝ) (hfg : ∀ y, f y ≤ g y)
    (hfint : Integrable (fun y : Fin n → ℝ => heatKernelND t (x - y) * f y))
    (hgint : Integrable (fun y : Fin n → ℝ => heatKernelND t (x - y) * g y)) :
    heatSemigroupND t f x ≤ heatSemigroupND t g x := by
  rw [heatSemigroupND, heatSemigroupND]
  refine integral_mono hfint hgint ?_
  intro y
  exact mul_le_mul_of_nonneg_left (hfg y) (heatKernelND_nonneg ht (x - y))

/-- The first moment of the heat kernel is integrable: `y ↦ |y| · K(t, y)` is
integrable for `t > 0`.  Equivalently, the spatial derivative `∂ₓ K(t, ·)` is
dominated by an integrable function — the envelope needed to differentiate the
heat-semigroup convolution under the integral sign. -/
theorem integrable_abs_mul_heatKernel1D {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => |x| * heatKernel1D t x) := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  -- `Integrable (x ↦ x^1 · exp(-(4t)⁻¹ x²))` from the Gaussian-moment lemma.
  have hmoment : Integrable (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(4 * t)⁻¹ * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)
  -- Its absolute value is `|x| · exp(...)`; scale by the prefactor to get `|x| · K`.
  have habs := hmoment.abs.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine habs.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [heatKernel1D_apply]
  have hxexp : -x ^ 2 / (4 * t) = -(4 * t)⁻¹ * x ^ 2 := by
    rw [neg_div, div_eq_inv_mul]; ring
  rw [hxexp, Real.rpow_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  ring

/-- The first spatial derivative of the heat kernel is integrable in the space
variable for `t > 0` — the convolution against `∂ₓK` is well-defined. -/
theorem integrable_deriv_heatKernel1D_space {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => heatKernel1D t x * (-x / (2 * t))) := by
  have hdom := (integrable_abs_mul_heatKernel1D ht).const_mul ((2 * t)⁻¹)
  refine hdom.mono' ?_ (Filter.Eventually.of_forall (fun x ↦ ?_))
  · exact ((continuous_heatKernel1D_space t).mul (by fun_prop)).aestronglyMeasurable
  · have htt : 0 < 2 * t := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos htt,
      abs_of_nonneg (heatKernel1D_nonneg ht x)]
    rw [show (2 * t)⁻¹ * (|x| * heatKernel1D t x)
        = heatKernel1D t x * (|x| / (2 * t)) by ring]

/-- The second moment of the heat kernel is integrable: `y ↦ y² · K(t, y)` —
the envelope needed for the second spatial derivative of the convolution. -/
theorem integrable_sq_mul_heatKernel1D {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ 2 * heatKernel1D t x) := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have hmoment : Integrable (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(4 * t)⁻¹ * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
  have hscaled := hmoment.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine hscaled.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [heatKernel1D_apply]
  have hxexp : -x ^ 2 / (4 * t) = -(4 * t)⁻¹ * x ^ 2 := by
    rw [neg_div, div_eq_inv_mul]; ring
  have hxsq : x ^ (2 : ℝ) = x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hxexp, hxsq]
  ring

/-- The convolution integrand for the spatial-derivative formula is integrable. -/
theorem integrable_deriv_heatKernel1D_space_sub_mul {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y => (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y) := by
  have hg : Integrable (fun y : ℝ => heatKernel1D t (x - y) * (-(x - y) / (2 * t))) :=
    (integrable_deriv_heatKernel1D_space ht).comp_sub_left x
  exact hg.mul_bdd hfm (Filter.Eventually.of_forall hfb)

/-- The second-derivative convolution integrand is integrable. -/
theorem integrable_deriv2_heatKernel1D_space_sub_mul {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y => (heatKernel1D t (x - y) *
      ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) := by
  have hsq : Integrable (fun y => (x - y) ^ 2 * heatKernel1D t (x - y)) :=
    (integrable_sq_mul_heatKernel1D ht).comp_sub_left x
  have hK : Integrable (fun y => heatKernel1D t (x - y)) := integrable_heatKernel1D_sub ht x
  have hbase : Integrable (fun y =>
      heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
    have hcomb := (hsq.const_mul (1 / (4 * t ^ 2))).sub (hK.const_mul (1 / (2 * t)))
    refine hcomb.congr ?_
    filter_upwards with y
    simp only [Pi.sub_apply]
    ring
  exact hbase.mul_bdd hfm (Filter.Eventually.of_forall hfb)

/-- **Second spatial derivative of the heat semigroup.**  Differentiating the
first-derivative formula again, `z ↦ ∂ₓHₜf z` is itself differentiable, with
`∂ₓₓHₜf = ∫ y, ∂ₓₓK(t, x - y) · f y`.  This establishes that `Hₜf` is twice
spatially differentiable for bounded measurable data (the second smoothing
result), again via Leibniz with a Gaussian envelope using the second moment. -/
theorem hasDerivAt_deriv_heatSemigroup1D_space {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt (fun z => ∫ y, (heatKernel1D t (z - y) * (-(z - y) / (2 * t))) * f y)
      (∫ y, (heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) x := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set F : ℝ → ℝ → ℝ := fun z y =>
    heatKernel1D t (z - y) * (-(z - y) / (2 * t)) * f y with hF
  set F' : ℝ → ℝ → ℝ := fun z y =>
    heatKernel1D t (z - y) * ((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y with hF'
  set M := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) * C with hM
  set bound : ℝ → ℝ := fun y =>
    M * (((1 + |y - x|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
      * Real.exp (-(y - x) ^ 2 / (8 * t))) with hbound
  have hs : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x (by norm_num)
  have hFmeas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    refine (((continuous_heatKernel1D_space t).comp
      (continuous_const.sub continuous_id)).mul ?_).aestronglyMeasurable.mul hfm
    fun_prop
  have hFint : Integrable (F x) volume := by
    simpa only [hF] using integrable_deriv_heatKernel1D_space_sub_mul ht x hfm hfb
  have hF'meas : AEStronglyMeasurable (F' x) volume := by
    refine (((continuous_heatKernel1D_space t).comp
      (continuous_const.sub continuous_id)).mul ?_).aestronglyMeasurable.mul hfm
    fun_prop
  have hbnd : ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ z ∈ Metric.ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hzle : |z - x| ≤ 1 := hz.le
    have hpre : (0 : ℝ) < (4 * π * t) ^ (-(1 : ℝ) / 2) := heatKernel1D_prefactor_pos ht
    have hnorm : ‖F' z y‖
        = heatKernel1D t (z - y) * |((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * |f y| := by
      simp only [hF']
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (heatKernel1D_nonneg ht (z - y))]
    rw [hnorm]
    have hzx2 : (z - x) ^ 2 ≤ 1 := by
      rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_one, Real.sqrt_sq_eq_abs]
      exact hzle
    set Eg := Real.exp (-(y - x) ^ 2 / (8 * t)) with hEg
    have hEgpos : 0 < Eg := Real.exp_pos _
    set P := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) with hP
    have hPpos : 0 < P := by positivity
    set Poly := (1 + |y - x|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) with hPoly
    have hPolynn : 0 ≤ Poly := by rw [hPoly]; positivity
    have hK : heatKernel1D t (z - y) ≤ P * Eg := by
      rw [hP, hEg, heatKernel1D_apply, mul_assoc ((4 * π * t) ^ (-(1 : ℝ) / 2)),
        ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hpre.le
      apply Real.exp_le_exp.mpr
      have hq : (z - y) ^ 2 ≥ (y - x) ^ 2 / 2 - (z - x) ^ 2 := by
        nlinarith [sq_nonneg ((y - x) - 2 * (z - x))]
      rw [← sub_nonneg]
      have key : 1 / (4 * t) + -(y - x) ^ 2 / (8 * t) - -(z - y) ^ 2 / (4 * t)
          = (2 - ((y - x) ^ 2 - 2 * (z - y) ^ 2)) / (8 * t) := by
        field_simp; ring
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hq, hzx2]
    have hzy : |z - y| ≤ 1 + |y - x| := by
      have hzysplit : z - y = (z - x) + (x - y) := by ring
      calc |z - y| ≤ |z - x| + |x - y| := by rw [hzysplit]; exact abs_add_le _ _
        _ ≤ 1 + |y - x| := by rw [abs_sub_comm x y]; linarith
    have hsqle : (z - y) ^ 2 ≤ (1 + |y - x|) ^ 2 := by
      nlinarith [hzy, sq_abs (z - y), abs_nonneg (z - y), abs_nonneg (y - x)]
    have hpolybd : |((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| ≤ Poly := by
      have hA : (0 : ℝ) ≤ (z - y) ^ 2 / (4 * t ^ 2) := by positivity
      have hB : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
      have hstep1 : |((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|
          ≤ (z - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
        rw [abs_le]; exact ⟨by linarith, by linarith⟩
      have hstep2 : (z - y) ^ 2 / (4 * t ^ 2)
          ≤ (1 + |y - x|) ^ 2 / (4 * t ^ 2) :=
        div_le_div_of_nonneg_right hsqle (by positivity)
      rw [hPoly]; linarith
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hub : heatKernel1D t (z - y) * |((z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * |f y|
        ≤ (P * Eg) * Poly * C := by
      apply mul_le_mul _ hfa (abs_nonneg _)
        (mul_nonneg (mul_nonneg hPpos.le hEgpos.le) hPolynn)
      apply mul_le_mul hK hpolybd (abs_nonneg _) (mul_nonneg hPpos.le hEgpos.le)
    refine hub.trans (le_of_eq ?_)
    simp only [hbound, hM, hP, hEg, hPoly]; ring
  have hboundint : Integrable bound volume := by
    have hb8 : 0 < (8 * t)⁻¹ := by positivity
    have h0 : Integrable (fun w : ℝ => Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
      integrable_exp_neg_mul_sq hb8
    have h1 : Integrable (fun w : ℝ => w ^ (1 : ℝ) * Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
    have h2 : Integrable (fun w : ℝ => w ^ (2 : ℝ) * Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
    have hbase : Integrable
        (fun w : ℝ => ((1 + |w|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          * Real.exp (-w ^ 2 / (8 * t))) := by
      have hsum := (((h0.const_mul (1 / (4 * t ^ 2) + 1 / (2 * t))).add
        ((h1.abs).const_mul (1 / (2 * t ^ 2)))).add (h2.const_mul (1 / (4 * t ^ 2))))
      refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [Pi.add_apply, Real.rpow_one, Real.rpow_two]
      have hexp : -(8 * t)⁻¹ * w ^ 2 = -w ^ 2 / (8 * t) := by
        rw [neg_div, div_eq_inv_mul]; ring
      rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp, ← sq_abs w]; ring
    have htrans : Integrable
        (fun y : ℝ => ((1 + |y - x|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          * Real.exp (-(y - x) ^ 2 / (8 * t))) :=
      hbase.comp_sub_right x
    simpa only [hbound] using htrans.const_mul M
  have hderiv : ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z => F z y) (F' z y) z := by
    filter_upwards with y z _
    have hin : HasDerivAt (fun z : ℝ => z - y) 1 z := by
      simpa using (hasDerivAt_id z).sub_const y
    have hcomp := (hasDerivAt_heatKernel1D_space_second ht (z - y)).comp z hin
    rw [mul_one] at hcomp
    have hmul := hcomp.mul_const (f y)
    simp only [hF, hF']
    exact hmul
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (x₀ := x) (bound := bound) (s := Metric.ball x 1)
    hs hFmeas hFint hF'meas hbnd hboundint hderiv
  simpa only [hF, hF'] using key.2

/-- The second spatial derivative of `Hₜf`, as an iterated `deriv`. -/
theorem deriv2_heatSemigroup1D_eq_integral {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (deriv (fun z => heatSemigroup1D t f z)) x
      = ∫ y, (heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y := by
  have hfun : deriv (fun z => heatSemigroup1D t f z)
      = (fun z => ∫ y, (heatKernel1D t (z - y) * (-(z - y) / (2 * t))) * f y) := by
    funext z
    exact deriv_heatSemigroup1D_space ht z hfm hfb
  rw [hfun]
  exact (hasDerivAt_deriv_heatSemigroup1D_space ht x hfm hfb).deriv

/-- **Time derivative of the heat semigroup** at a fixed positive time `t₀`:
`∂ₜ Hₜf x = ∫ y, ∂ₜK(t₀, x - y) · f y`.  Proved by Leibniz in time, with a
Gaussian envelope uniform over a compact time-interval around `t₀`. -/
theorem hasDerivAt_heatSemigroup1D_time {t₀ : ℝ} (ht₀ : 0 < t₀) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt (fun s => heatSemigroup1D s f x)
      (∫ y, (heatKernel1D t₀ (x - y) * ((x - y) ^ 2 / (4 * t₀ ^ 2) - 1 / (2 * t₀))) * f y) t₀ := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  have h2πt₀pos : (0 : ℝ) < 2 * π * t₀ := by positivity
  set F : ℝ → ℝ → ℝ := fun s y => heatKernel1D s (x - y) * f y with hF
  set F' : ℝ → ℝ → ℝ := fun s y =>
    heatKernel1D s (x - y) * ((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) * f y with hF'
  set P := (2 * π * t₀) ^ (-(1 : ℝ) / 2) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  set M := P * C with hM
  set bound : ℝ → ℝ := fun y =>
    M * (((x - y) ^ 2 / t₀ ^ 2 + 1 / t₀) * Real.exp (-(x - y) ^ 2 / (6 * t₀))) with hbound
  have hs : Metric.ball t₀ (t₀ / 2) ∈ nhds t₀ := Metric.ball_mem_nhds t₀ (half_pos ht₀)
  have hFmeas : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (F s) volume := by
    filter_upwards with s
    exact (aestronglyMeasurable_heatKernel1D_sub (t := s) x).mul hfm
  have hFint : Integrable (F t₀) volume :=
    integrable_heatKernel1D_sub_mul ht₀ x hfm hfb
  have hF'meas : AEStronglyMeasurable (F' t₀) volume := by
    refine (((continuous_heatKernel1D_space t₀).comp
      (continuous_const.sub continuous_id)).mul ?_).aestronglyMeasurable.mul hfm
    fun_prop
  have hbnd : ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ s ∈ Metric.ball t₀ (t₀ / 2), ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hpair := abs_lt.1 hz
    have hs_lo : t₀ / 2 < s := by linarith [hpair.1]
    have hs_hi : s < 3 * t₀ / 2 := by linarith [hpair.2]
    have hspos : 0 < s := by linarith
    have hle : 2 * π * t₀ ≤ 4 * π * s := by nlinarith [Real.pi_pos, hs_lo]
    have h46 : 4 * s ≤ 6 * t₀ := by linarith
    set Eg := Real.exp (-(x - y) ^ 2 / (6 * t₀)) with hEg
    have hEgpos : 0 < Eg := by rw [hEg]; exact Real.exp_pos _
    set Poly := (x - y) ^ 2 / t₀ ^ 2 + 1 / t₀ with hPoly
    have hPolynn : 0 ≤ Poly := by rw [hPoly]; positivity
    have hnorm : ‖F' s y‖
        = heatKernel1D s (x - y) * |((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| * |f y| := by
      simp only [hF']
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (heatKernel1D_nonneg hspos (x - y))]
    rw [hnorm]
    have hexp : -(x - y) ^ 2 / (4 * s) ≤ -(x - y) ^ 2 / (6 * t₀) := by
      rw [neg_div, neg_div, neg_le_neg_iff]; gcongr
    have hApre : (4 * π * s) ^ (-(1 : ℝ) / 2) ≤ P := by
      rw [hP]; exact Real.rpow_le_rpow_of_nonpos h2πt₀pos hle (by norm_num)
    have hBexp : Real.exp (-(x - y) ^ 2 / (4 * s)) ≤ Eg := by
      rw [hEg]; exact Real.exp_le_exp.mpr hexp
    have hK : heatKernel1D s (x - y) ≤ P * Eg := by
      rw [heatKernel1D_apply]
      exact mul_le_mul hApre hBexp (Real.exp_pos _).le hPpos.le
    have hstep1 : |((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s))|
        ≤ (x - y) ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
      have h1 : 0 ≤ (x - y) ^ 2 / (4 * s ^ 2) := by positivity
      have h2 : 0 ≤ 1 / (2 * s) := by positivity
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hstep2a : (x - y) ^ 2 / (4 * s ^ 2) ≤ (x - y) ^ 2 / t₀ ^ 2 := by
      gcongr; nlinarith [hs_lo, ht₀]
    have hstep2b : 1 / (2 * s) ≤ 1 / t₀ := by gcongr; linarith
    have hpolybd : |((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| ≤ Poly := by
      rw [hPoly]; linarith
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hub : heatKernel1D s (x - y) * |((x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| * |f y|
        ≤ (P * Eg) * Poly * C := by
      apply mul_le_mul _ hfa (abs_nonneg _)
        (mul_nonneg (mul_nonneg hPpos.le hEgpos.le) hPolynn)
      apply mul_le_mul hK hpolybd (abs_nonneg _) (mul_nonneg hPpos.le hEgpos.le)
    refine hub.trans (le_of_eq ?_)
    simp only [hbound, hM, hP, hEg, hPoly]; ring
  have hboundint : Integrable bound volume := by
    have hb6 : 0 < (6 * t₀)⁻¹ := by positivity
    have h0 : Integrable (fun w : ℝ => Real.exp (-(6 * t₀)⁻¹ * w ^ 2)) :=
      integrable_exp_neg_mul_sq hb6
    have h2 : Integrable (fun w : ℝ => w ^ (2 : ℝ) * Real.exp (-(6 * t₀)⁻¹ * w ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb6 (by norm_num : (-1 : ℝ) < 2)
    have hbase : Integrable (fun w : ℝ =>
        (w ^ 2 / t₀ ^ 2 + 1 / t₀) * Real.exp (-w ^ 2 / (6 * t₀))) := by
      have hsum := (h2.const_mul (1 / t₀ ^ 2)).add (h0.const_mul (1 / t₀))
      refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [Pi.add_apply]
      have hxsq : w ^ (2 : ℝ) = w ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hexp6 : -(6 * t₀)⁻¹ * w ^ 2 = -w ^ 2 / (6 * t₀) := by
        rw [neg_div, div_eq_inv_mul]; ring
      rw [hxsq, hexp6]; ring
    have hM0 := (hbase.const_mul M).comp_sub_left x
    simpa only [hbound] using hM0
  have hderiv : ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ s ∈ Metric.ball t₀ (t₀ / 2), HasDerivAt (fun s => F s y) (F' s y) s := by
    filter_upwards with y s hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hpair := abs_lt.1 hz
    have hspos : 0 < s := by
      have : t₀ / 2 < s := by linarith [hpair.1]
      linarith
    have htime := (hasDerivAt_heatKernel1D_time hspos (x - y)).mul_const (f y)
    simp only [hF, hF']
    exact htime
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (x₀ := t₀) (bound := bound) (s := Metric.ball t₀ (t₀ / 2))
    hs hFmeas hFint hF'meas hbnd hboundint hderiv
  simpa only [hF, hF', heatSemigroup1D] using key.2

/-- **The heat semigroup solves the heat equation.**  For bounded measurable data
`f` and `t > 0`, the value `u(s, z) = Hₛf z` satisfies `∂ₜu = ∂ₓₓu` at `(t, x)`:
the time derivative of `s ↦ Hₛf x` equals the second spatial derivative of
`z ↦ Hₜf z`, both being `∫ y, K(t, x-y)·(…)·f y` with the same coefficient
(because the kernel itself solves the heat equation pointwise). -/
theorem heatSemigroup1D_solves_heatEquation {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (fun s => heatSemigroup1D s f x) t
      = deriv (deriv (fun z => heatSemigroup1D t f z)) x := by
  rw [(hasDerivAt_heatSemigroup1D_time ht x hfm hfb).deriv,
      deriv2_heatSemigroup1D_eq_integral ht x hfm hfb]

/-- The spatial derivative of `Hₜ1` vanishes: `∫ y, ∂ₓK(t, x-y) dy = 0` (the
kernel's first spatial moment is an odd integral). Consistent with `Hₜc = c`. -/
theorem integral_neg_mul_heatKernel1D_sub {t : ℝ} (_ht : 0 < t) (x : ℝ) :
    (∫ y, heatKernel1D t (x - y) * (-(x - y) / (2 * t))) = 0 := by
  set h : ℝ → ℝ := fun w => heatKernel1D t w * (-w / (2 * t)) with hh
  have hstep : (∫ y, heatKernel1D t (x - y) * (-(x - y) / (2 * t))) = ∫ y, h y := by
    have := integral_sub_left_eq_self h volume x
    simpa [hh] using this
  rw [hstep]
  have hodd : ∀ w, h (-w) = - h w := by
    intro w
    simp only [hh, heatKernel1D_apply, neg_neg, neg_sq]
    ring
  have e1 : (∫ w, h (-w)) = ∫ w, h w := integral_neg_eq_self h volume
  have e2 : (∫ w, h (-w)) = - ∫ w, h w := by
    rw [show (∫ w, h (-w)) = ∫ w, -h w from
        integral_congr_ae (Filter.Eventually.of_forall hodd)]
    rw [integral_neg]
  linarith [e1, e2]

/-- The spatial derivative of `Hₜ` applied to a constant vanishes. -/
theorem deriv_heatSemigroup1D_space_eq_zero_of_const {t : ℝ} (ht : 0 < t) (c x : ℝ) :
    deriv (fun z => heatSemigroup1D t (fun _ => c) z) x = 0 := by
  have h : (fun z => heatSemigroup1D t (fun _ => c) z) = fun _ => c :=
    funext (fun z => heatSemigroup1D_const ht c z)
  rw [h]
  exact deriv_const x c

/-- Explicit form of the time derivative of `Hₛf x`. -/
theorem heatSemigroup1D_time_deriv_eq_space_second_integral {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {C : ℝ} (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (fun s => heatSemigroup1D s f x) t =
      ∫ y, (heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y :=
  (hasDerivAt_heatSemigroup1D_time ht x hfm hfb).deriv

/-- `Hₜ` applied to a constant has zero spatial derivative (as a `HasDerivAt`). -/
theorem hasDerivAt_heatSemigroup1D_space_const_zero {t : ℝ} (ht : 0 < t) (c : ℝ)
    (x : ℝ) : HasDerivAt (fun z => heatSemigroup1D t (fun _ => c) z) 0 x := by
  have h : (fun z => heatSemigroup1D t (fun _ => c) z) = fun _ => c :=
    funext (fun z => heatSemigroup1D_const ht c z)
  rw [h]
  exact hasDerivAt_const x c

/-- The heat kernel is continuous in the time variable on `(0, ∞)`. -/
theorem continuousOn_heatKernel1D_time {x : ℝ} :
    ContinuousOn (fun s => heatKernel1D s x) (Set.Ioi 0) :=
  fun s hs => (hasDerivAt_heatKernel1D_time hs x).continuousAt.continuousWithinAt

/-- The `n`-dimensional heat semigroup annihilates the zero function (Pi-zero form). -/
theorem heatSemigroupND_zero_fun {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    heatSemigroupND t (0 : (Fin n → ℝ) → ℝ) x = 0 := by
  simpa [Pi.zero_def] using heatSemigroupND_const ht 0 x

/-- Key Gaussian-moment estimate: `exp(-x²/(4t)) · |x| ≤ √t` for `t > 0`. -/
lemma heatKernel1D_exp_mul_abs_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.exp (-x ^ 2 / (4 * t)) * |x| ≤ Real.sqrt t := by
  set s := Real.sqrt t with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht.le
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have he : (1 : ℝ) + x ^ 2 / (4 * t) ≤ Real.exp (x ^ 2 / (4 * t)) := by
    have := Real.add_one_le_exp (x ^ 2 / (4 * t)); linarith
  have hpos1 : (0 : ℝ) < 1 + x ^ 2 / (4 * t) := by positivity
  have hle1 : Real.exp (-x ^ 2 / (4 * t)) ≤ 1 / (1 + x ^ 2 / (4 * t)) := by
    rw [show -x ^ 2 / (4 * t) = -(x ^ 2 / (4 * t)) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos1 he
  have h2 : Real.exp (-x ^ 2 / (4 * t)) * |x| ≤ (1 / (1 + x ^ 2 / (4 * t))) * |x| :=
    mul_le_mul_of_nonneg_right hle1 (abs_nonneg x)
  refine h2.trans ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos1]
  rw [← hs2]
  have hxa : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hssq : (0 : ℝ) < 4 * s ^ 2 := by rw [hs2]; positivity
  rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  have hexp : s * (1 + |x| ^ 2 / (4 * s ^ 2)) = s + |x| ^ 2 / (4 * s) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simp
    · field_simp
  rw [hexp]
  have hspos : 0 < s := Real.sqrt_pos.mpr ht
  rw [show s + |x| ^ 2 / (4 * s) = (4 * s ^ 2 + |x| ^ 2) / (4 * s) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * s - |x|), hs0, hxa]

/-- **The 1D heat kernel is globally Lipschitz in the space variable** (for fixed
`t > 0`), with explicit constant `(4πt)^(-1/2)·√t/(2t)`.  This is the first
Hölder-type bound — the spatial regularity estimate that feeds parabolic Schauder
theory. -/
theorem exists_lipschitz_heatKernel1D {t : ℝ} (ht : 0 < t) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x x', |heatKernel1D t x - heatKernel1D t x'| ≤ L * |x - x'| := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hpre : (0 : ℝ) < (4 * π * t) ^ (-(1 : ℝ) / 2) := heatKernel1D_prefactor_pos ht
  set L : ℝ := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hbound : ∀ y ∈ (Set.univ : Set ℝ), ‖deriv (fun z => heatKernel1D t z) y‖ ≤ L := by
    intro y _
    rw [deriv_heatKernel1D_space ht y, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (heatKernel1D_nonneg ht y)]
    rw [abs_div, abs_neg, abs_of_pos h2t]
    rw [heatKernel1D_apply]
    have hkey := heatKernel1D_exp_mul_abs_le ht y
    have hc : (0 : ℝ) ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) / (2 * t) := by positivity
    have hrw : (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-y ^ 2 / (4 * t)) * (|y| / (2 * t))
        = ((4 * π * t) ^ (-(1 : ℝ) / 2) / (2 * t)) *
            (Real.exp (-y ^ 2 / (4 * t)) * |y|) := by
      field_simp
    rw [hrw, hL, mul_div_assoc]
    calc ((4 * π * t) ^ (-(1 : ℝ) / 2) / (2 * t)) *
            (Real.exp (-y ^ 2 / (4 * t)) * |y|)
        ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2) / (2 * t)) * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hkey hc
      _ = (4 * π * t) ^ (-(1 : ℝ) / 2) * (Real.sqrt t / (2 * t)) := by ring
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (fun z => heatKernel1D t z) y :=
    fun y _ => differentiableAt_heatKernel1D_space ht y
  refine ⟨L, hL0, fun x x' => ?_⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (Set.mem_univ x') (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using hmvt

/-- `√t / (2t) = 1 / (2√t)`. -/
lemma sqrt_t_div_two_t_eq (t : ℝ) (ht : 0 < t) :
    Real.sqrt t / (2 * t) = 1 / (2 * Real.sqrt t) := by
  have h : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [h]

/-- Uniform bound on the kernel's spatial derivative: `|∂ₓK(t,x)| ≤ (4πt)^(-1/2)·√t/(2t)`. -/
lemma norm_deriv_heatKernel1D_space_le (t : ℝ) (ht : 0 < t) (x : ℝ) :
    |deriv (fun y => heatKernel1D t y) x| ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) := by
  rw [deriv_heatKernel1D_space ht x]
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hK : 0 ≤ heatKernel1D t x := heatKernel1D_nonneg ht x
  have hpre : (0 : ℝ) ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := (heatKernel1D_prefactor_pos ht).le
  have hkey := heatKernel1D_exp_mul_abs_le ht x
  rw [abs_mul, abs_of_nonneg hK, abs_div, abs_neg, abs_of_pos h2t]
  rw [heatKernel1D_apply]
  calc (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t)) * (|x| / (2 * t))
      = (4 * π * t) ^ (-(1 : ℝ) / 2) * (Real.exp (-x ^ 2 / (4 * t)) * |x|) / (2 * t) := by ring
    _ ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) := by gcongr

/-- The shifted first-moment integrand `y ↦ |x - y| · K(t, x - y)` is integrable. -/
lemma integrable_abs_sub_mul_heatKernel1D_sub {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => |x - y| * heatKernel1D t (x - y)) := by
  have h := (integrable_abs_mul_heatKernel1D ht).comp_sub_left x
  simpa using h

/-- **Stability of the heat semigroup in the data**: if `|f - g| ≤ C` pointwise
(with both `f, g` bounded measurable), then `|Hₜf x - Hₜg x| ≤ C`. -/
theorem abs_heatSemigroup1D_sub_le (t : ℝ) (ht : 0 < t) (f g : ℝ → ℝ)
    (C D : ℝ) (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ D)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ D)
    (hbound : ∀ y, |f y - g y| ≤ C) :
    |heatSemigroup1D t f x - heatSemigroup1D t g x| ≤ C := by
  rw [← heatSemigroup1D_sub ht x hfm hfb hgm hgb]
  exact abs_heatSemigroup1D_le ht x hbound

/-- Nonnegativity of the shifted `n`-dimensional kernel. -/
lemma heatKernelND_sub_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t) (x y : Fin n → ℝ) :
    0 ≤ heatKernelND t (x - y) :=
  heatKernelND_nonneg ht (x - y)

/-- One-sided constant bound (from two-sided pointwise bound) for the `n`-dim semigroup. -/
theorem heatSemigroupND_le_of_forall_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : (Fin n → ℝ) → ℝ) (C : ℝ) (x : Fin n → ℝ)
    (hf : ∀ y, f y ≤ C) (hf2 : ∀ y, -C ≤ f y) :
    heatSemigroupND t f x ≤ C :=
  heatSemigroupND_le_of_le ht x (fun y => abs_le.mpr (And.intro (hf2 y) (hf y)))

/-- **The heat semigroup is globally Lipschitz in space** (for bounded measurable
data), with constant `L = C·A/(2t)` where `A = ∫ |w|·K(t,w) dw`.  This spatial
Hölder estimate is exactly the regularity bound that feeds parabolic Schauder
theory for the variable-coefficient operators. -/
theorem exists_lipschitz_heatSemigroup1D (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b, |heatSemigroup1D t f a - heatSemigroup1D t f b| ≤ L * |a - b| := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set A : ℝ := ∫ (w : ℝ), |w| * heatKernel1D t w with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg (fun w => mul_nonneg (abs_nonneg w) (heatKernel1D_nonneg ht w))
  set L : ℝ := C * (2 * t)⁻¹ * A with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]; exact mul_nonneg (mul_nonneg hCnn (by positivity)) hAnn
  refine ⟨L, hLnn, ?_⟩
  have hbnd : ∀ x ∈ (Set.univ : Set ℝ),
      ‖deriv (fun z => heatSemigroup1D t f z) x‖ ≤ L := by
    intro x _
    rw [Real.norm_eq_abs, deriv_heatSemigroup1D_space ht x hfm hfb]
    have hint : Integrable
        (fun y => (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y) :=
      integrable_deriv_heatKernel1D_space_sub_mul ht x hfm hfb
    have hbint : Integrable
        (fun y => heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C) := by
      have hg : Integrable (fun y : ℝ => |x - y| * heatKernel1D t (x - y)) :=
        (integrable_abs_mul_heatKernel1D ht).comp_sub_left x
      refine (hg.const_mul (C * (2 * t)⁻¹)).congr ?_
      filter_upwards with y; ring
    calc |∫ y, (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y|
        ≤ ∫ y, ‖(heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C := by
          refine integral_mono hint.norm hbint (fun y => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos h2t,
            abs_of_nonneg (heatKernel1D_nonneg ht (x - y))]
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (heatKernel1D_nonneg ht (x - y)) (by positivity))
          exact (Real.norm_eq_abs (f y)) ▸ hfb y
      _ = L := by
          have heq : (fun y => heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C)
              = fun y => (C * (2 * t)⁻¹) * (|x - y| * heatKernel1D t (x - y)) := by
            funext y; ring
          rw [heq, integral_const_mul,
            integral_sub_left_eq_self (fun w => |w| * heatKernel1D t w) volume x, ← hAdef, hLdef]
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun z => heatSemigroup1D t f z) x :=
    fun x _ => differentiable_heatSemigroup1D_space ht hfm hfb x
  intro a b
  have hmvt := (convex_univ).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using hmvt

/-- The `L¹` norm of the kernel's spatial derivative, as a constant times the first
moment. -/
lemma integral_abs_deriv_heatKernel1D {t : ℝ} (ht : 0 < t) :
    (∫ y, |heatKernel1D t y * (-y / (2 * t))|)
      = (1 / (2 * t)) * ∫ y, |y| * heatKernel1D t y := by
  rw [show (1 / (2 * t)) * (∫ y, |y| * heatKernel1D t y)
        = ∫ y, (1 / (2 * t)) * (|y| * heatKernel1D t y) from
      (integral_const_mul _ _).symm]
  apply integral_congr_ae
  filter_upwards with y
  rw [abs_mul, abs_of_nonneg (heatKernel1D_nonneg ht y), abs_div, abs_neg,
    abs_of_pos (show (0 : ℝ) < 2 * t by positivity)]
  ring

/-- **Explicit-constant Hölder/Lipschitz bound for the kernel in space**:
`|K(t, a) - K(t, b)| ≤ ((4πt)^(-1/2)·√t/(2t))·|a - b|`.  The constant is exactly
the sup of `|∂ₓK|`.  This is the `C^{0,1}` (Lipschitz) modulus that the parabolic
Schauder `C^{0,α}` estimates are built on. -/
theorem heatKernel1D_sub_abs_le (t : ℝ) (ht : 0 < t) (a b : ℝ) :
    |heatKernel1D t a - heatKernel1D t b| ≤
      ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t)) * |a - b| := by
  have hdiff : Differentiable ℝ (fun z => heatKernel1D t z) :=
    differentiable_heatKernel1D_space ht
  have hbound : ∀ y ∈ (Set.univ : Set ℝ),
      ‖deriv (fun z => heatKernel1D t z) y‖ ≤
        (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) := by
    intro y _
    rw [Real.norm_eq_abs]
    exact norm_deriv_heatKernel1D_space_le t ht y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hdiff x) hbound convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

/-- The heat semigroup evaluated at `0`. -/
lemma heatSemigroup1D_apply_zero (t : ℝ) (f : ℝ → ℝ) :
    heatSemigroup1D t f 0 = ∫ y, heatKernel1D t (-y) * f y := by
  simp only [heatSemigroup1D, zero_sub]

/-- Explicit form of the kernel's spatial derivative. -/
lemma deriv_heatKernel1D_space_eq (t : ℝ) (ht : 0 < t) (x : ℝ) :
    deriv (fun y => heatKernel1D t y) x
      = (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t)) * (-x / (2 * t)) := by
  rw [deriv_heatKernel1D_space ht x, heatKernel1D_apply]

/-- The kernel at the centre equals the prefactor. -/
lemma heatKernel1D_zero_eq_prefactor (t : ℝ) :
    heatKernel1D t 0 = (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  rw [heatKernel1D_apply]; simp

/-- The heat semigroup annihilates a pointwise-zero function. -/
theorem heatSemigroup1D_eq_zero_of_eq_zero (t : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hf : ∀ y, f y = 0) : heatSemigroup1D t f x = 0 := by
  unfold heatSemigroup1D
  simp only [hf, mul_zero, integral_zero]

/-- Uniform bound on the kernel difference: `|K(t,a) - K(t,b)| ≤ 2·(4πt)^(-1/2)`. -/
theorem heatKernel1D_sub_abs_le_min (t : ℝ) (ht : 0 < t) (a b : ℝ) :
    |heatKernel1D t a - heatKernel1D t b| ≤ 2 * (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  calc |heatKernel1D t a - heatKernel1D t b|
      ≤ |heatKernel1D t a| + |heatKernel1D t b| := abs_sub _ _
    _ = heatKernel1D t a + heatKernel1D t b := by
          rw [abs_heatKernel1D ht, abs_heatKernel1D ht]
    _ ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) + (4 * π * t) ^ (-(1 : ℝ) / 2) := by
          gcongr <;> exact heatKernel1D_le_prefactor ht _
    _ = 2 * (4 * π * t) ^ (-(1 : ℝ) / 2) := by ring

/-- **The heat kernel as a `LipschitzWith` map** (mathlib's Lipschitz API), with the
explicit NNReal constant. -/
lemma lipschitzWith_heatKernel1D (t : ℝ) (ht : 0 < t) :
    LipschitzWith ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t)).toNNReal
      (fun x => heatKernel1D t x) := by
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact heatKernel1D_sub_abs_le t ht a b

/-- Alternative form of the kernel-derivative bound: `|∂ₓK| ≤ (1/(2√t))·(4πt)^(-1/2)`. -/
lemma abs_deriv_heatKernel1D_space_le (t : ℝ) (ht : 0 < t) (x : ℝ) :
    |deriv (fun y => heatKernel1D t y) x| ≤ 1 / (2 * Real.sqrt t) * (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  have h := norm_deriv_heatKernel1D_space_le t ht x
  rw [mul_div_assoc, sqrt_t_div_two_t_eq t ht] at h
  linarith [h]

/-- The `n`-dimensional heat kernel is continuous along a single coordinate. -/
theorem continuous_heatKernelND_update (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    Continuous (fun r : ℝ => heatKernelND t (Function.update x i r)) := by
  have hupd : Continuous (fun r : ℝ => Function.update x i r) := by
    refine continuous_pi (fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa [Function.update_self] using (continuous_id : Continuous (fun r : ℝ => r))
    · simpa [Function.update_of_ne hj] using (continuous_const : Continuous (fun _ : ℝ => x j))
  exact (continuous_heatKernelND t).comp hupd

/-- Lower bound counterpart of the semigroup maximum principle. -/
theorem heatSemigroup1D_neg_le (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ) (x : ℝ)
    (hf : ∀ y, |f y| ≤ C) : -C ≤ heatSemigroup1D t f x :=
  (abs_le.mp (abs_heatSemigroup1D_le ht x hf)).1

/-- Two-point spatial difference bound: `|Hₜf x - Hₜf x'| ≤ 2C` when `|f| ≤ C`. -/
theorem heatSemigroup1D_dist_le_two_C (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (x x' : ℝ) (hf : ∀ y, |f y| ≤ C) :
    |heatSemigroup1D t f x - heatSemigroup1D t f x'| ≤ 2 * C := by
  have htri : |heatSemigroup1D t f x - heatSemigroup1D t f x'|
      ≤ |heatSemigroup1D t f x| + |heatSemigroup1D t f x'| := abs_sub _ _
  linarith [abs_heatSemigroup1D_le ht x hf, abs_heatSemigroup1D_le ht x' hf]

/-- The `n`-dimensional heat semigroup annihilates a pointwise-zero function. -/
theorem heatSemigroupND_eq_zero_of_eq_zero (n : ℕ) (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hf : ∀ y, f y = 0) :
    heatSemigroupND t f x = 0 := by
  unfold heatSemigroupND
  simp only [hf, mul_zero, integral_zero]

/-- **The heat semigroup as a `LipschitzWith` map** (mathlib API) for bounded data. -/
theorem lipschitzWith_heatSemigroup1D (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    ∃ K : NNReal, LipschitzWith K (fun x => heatSemigroup1D t f x) := by
  obtain ⟨L, hL0, hLip⟩ := exists_lipschitz_heatSemigroup1D t ht f C hfm hfb
  refine ⟨L.toNNReal, ?_⟩
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
  exact hLip a b

/-- The heat kernel is uniformly continuous in space. -/
theorem uniformContinuous_heatKernel1D_space (t : ℝ) (ht : 0 < t) :
    UniformContinuous (fun x => heatKernel1D t x) :=
  (lipschitzWith_heatKernel1D t ht).uniformContinuous

/-- The semigroup output lies in `[-C, C]` for `|f| ≤ C`. -/
theorem heatSemigroup1D_mem_Icc_neg_pos (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ)
    (C : ℝ) (x : ℝ) (hf : ∀ y, |f y| ≤ C) :
    heatSemigroup1D t f x ∈ Set.Icc (-C) C :=
  Set.mem_Icc.mpr ⟨heatSemigroup1D_neg_le t ht f C x hf,
    le_of_abs_le (abs_heatSemigroup1D_le ht x hf)⟩

/-- **Joint continuity of the heat kernel** on `(0, ∞) × ℝ`. -/
lemma continuousOn_heatKernel1D_prod :
    ContinuousOn (fun p : ℝ × ℝ => heatKernel1D p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  simp only [heatKernel1D_apply]
  apply ContinuousOn.mul
  · apply ContinuousOn.rpow_const
    · exact (continuous_const.mul continuous_fst).continuousOn
    · intro p hp
      left
      have : 0 < 4 * π * p.1 := by
        have : 0 < p.1 := hp.1
        positivity
      exact ne_of_gt this
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div
    · exact ((continuous_snd.pow 2).neg).continuousOn
    · exact (continuous_const.mul continuous_fst).continuousOn
    · intro p hp
      have : 0 < p.1 := hp.1
      positivity

/-- **Shifted-kernel spatial Hölder bound** (core of convolution Hölder estimates):
`|K(t, x-y) - K(t, x'-y)| ≤ Lip · |x - x'|`, uniformly in `y`. -/
theorem heatKernel1D_sub_shift_abs_le (t : ℝ) (ht : 0 < t) (x x' y : ℝ) :
    |heatKernel1D t (x - y) - heatKernel1D t (x' - y)| ≤
      ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t)) * |x - x'| := by
  have h := heatKernel1D_sub_abs_le t ht (x - y) (x' - y)
  have he : (x - y) - (x' - y) = x - x' := by ring
  rw [he] at h
  exact h

/-- The named spatial-Lipschitz constant of the heat kernel at time `t`. -/
noncomputable def heatKernel1DLipConst (t : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t)

lemma heatKernel1DLipConst_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ heatKernel1DLipConst t := by
  unfold heatKernel1DLipConst
  positivity

/-- Kernel spatial-Hölder bound through the named constant. -/
lemma heatKernel1D_sub_abs_le_const (t : ℝ) (ht : 0 < t) (a b : ℝ) :
    |heatKernel1D t a - heatKernel1D t b| ≤ heatKernel1DLipConst t * |a - b| := by
  unfold heatKernel1DLipConst
  exact heatKernel1D_sub_abs_le t ht a b

/-- **Explicit Lipschitz constant for the heat semigroup**: with `A = ∫ |w|·K(t,w)`,
`|Hₜf a - Hₜf b| ≤ (C·A/(2t))·|a - b|` whenever `|f| ≤ C`. -/
theorem abs_heatSemigroup1D_sub_self_le (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (a b : ℝ) :
    |heatSemigroup1D t f a - heatSemigroup1D t f b| ≤
      (C * (∫ w, |w| * heatKernel1D t w) / (2 * t)) * |a - b| := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set A : ℝ := ∫ (w : ℝ), |w| * heatKernel1D t w with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg (fun w => mul_nonneg (abs_nonneg w) (heatKernel1D_nonneg ht w))
  set L : ℝ := C * A / (2 * t) with hLdef
  have hbnd : ∀ x ∈ (Set.univ : Set ℝ),
      ‖deriv (fun z => heatSemigroup1D t f z) x‖ ≤ L := by
    intro x _
    rw [Real.norm_eq_abs, deriv_heatSemigroup1D_space ht x hfm hfb]
    have hint : Integrable
        (fun y => (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y) :=
      integrable_deriv_heatKernel1D_space_sub_mul ht x hfm hfb
    have hbint : Integrable
        (fun y => heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C) := by
      have hg : Integrable (fun y : ℝ => |x - y| * heatKernel1D t (x - y)) :=
        (integrable_abs_mul_heatKernel1D ht).comp_sub_left x
      refine (hg.const_mul (C * (2 * t)⁻¹)).congr ?_
      filter_upwards with y; ring
    calc |∫ y, (heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y|
        ≤ ∫ y, ‖(heatKernel1D t (x - y) * (-(x - y) / (2 * t))) * f y‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C := by
          refine integral_mono hint.norm hbint (fun y => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos h2t,
            abs_of_nonneg (heatKernel1D_nonneg ht (x - y))]
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (heatKernel1D_nonneg ht (x - y)) (by positivity))
          exact (Real.norm_eq_abs (f y)) ▸ hfb y
      _ = L := by
          have heq : (fun y => heatKernel1D t (x - y) * (|x - y| / (2 * t)) * C)
              = fun y => (C * (2 * t)⁻¹) * (|x - y| * heatKernel1D t (x - y)) := by
            funext y; ring
          rw [heq, integral_const_mul,
            integral_sub_left_eq_self (fun w => |w| * heatKernel1D t w) volume x, ← hAdef, hLdef]
          ring
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun z => heatSemigroup1D t f z) x :=
    fun x _ => differentiable_heatSemigroup1D_space ht hfm hfb x
  have hmvt := (convex_univ).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ b) (Set.mem_univ a)
  rw [hLdef] at hmvt
  simpa [Real.norm_eq_abs] using hmvt

/-- Scalar homogeneity (explicit name) for the `n`-dim semigroup. -/
theorem heatSemigroupND_smul_const (n : ℕ) (t : ℝ) (ht : 0 < t) (c : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    heatSemigroupND t (fun y => c * f y) x = c * heatSemigroupND t f x := by
  simpa using heatSemigroupND_smul (t := t) c f x

/-- Adding a constant on the left commutes with the heat semigroup. -/
theorem heatSemigroup1D_const_add (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C m : ℝ)
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroup1D t (fun y => m + f y) x = m + heatSemigroup1D t f x := by
  have hcomm : (fun y => m + f y) = (fun y => f y + m) := by funext y; ring
  rw [hcomm, heatSemigroup1D_add_const ht x m hfm hfb, add_comm]

/-- The `n`-dim semigroup of a constant is continuous (it is constant). -/
theorem continuous_heatSemigroupND_const (n : ℕ) (t : ℝ) (ht : 0 < t) (c : ℝ) :
    Continuous (fun x : Fin n → ℝ => heatSemigroupND t (fun _ => c) x) := by
  have h : (fun x : Fin n → ℝ => heatSemigroupND t (fun _ => c) x) = fun _ => c :=
    funext (fun x => heatSemigroupND_const ht c x)
  rw [h]
  exact continuous_const

/-- The kernel at a self-difference equals the kernel at the centre. -/
lemma heatKernel1D_sub_self (t : ℝ) (x : ℝ) :
    heatKernel1D t (x - x) = heatKernel1D t 0 := by
  rw [sub_self]

/-- Combined two-sided bound for the semigroup. -/
theorem heatSemigroup1D_le_iff_bound (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (x : ℝ) (hf : ∀ y, |f y| ≤ C) :
    heatSemigroup1D t f x ≤ C ∧ -C ≤ heatSemigroup1D t f x :=
  ⟨le_of_abs_le (abs_heatSemigroup1D_le ht x hf), heatSemigroup1D_neg_le t ht f C x hf⟩

/-- **Factorization of the `n`-dimensional kernel** along one coordinate:
`Kₙ(t, x) = K(t, xᵢ)·∏_{j≠i} K(t, xⱼ)`.  The structural lemma for coordinate
partial derivatives of `Kₙ`. -/
lemma heatKernelND_eq_update_mul (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    heatKernelND t x
      = heatKernel1D t (x i) * ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) := by
  rw [heatKernelND_apply,
    ← Finset.mul_prod_erase Finset.univ (fun j => heatKernel1D t (x j)) (Finset.mem_univ i)]

/-- The `n`-dim kernel is bounded by one 1D factor times the prefactor power `(n-1)`. -/
lemma heatKernelND_le_factor (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ)
    (i : Fin n) :
    heatKernelND t x
      ≤ heatKernel1D t (x i) * ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) := by
  rw [heatKernelND_apply]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => heatKernel1D t (x j))
      (Finset.mem_univ i)]
  apply mul_le_mul_of_nonneg_left _ (heatKernel1D_nonneg ht (x i))
  calc ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j)
      ≤ ∏ _j ∈ Finset.univ.erase i, (4 * π * t) ^ (-(1 : ℝ) / 2) := by
        apply Finset.prod_le_prod
        · intro j _; exact heatKernel1D_nonneg ht (x j)
        · intro j _; exact heatKernel1D_le_prefactor ht (x j)
    _ = ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]

/-- The `n`-dim kernel at the origin equals the prefactor to the `n`-th power. -/
lemma heatKernelND_zero_eq (n : ℕ) (t : ℝ) :
    heatKernelND t (0 : Fin n → ℝ) = ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ n := by
  rw [heatKernelND_apply]
  simp only [Pi.zero_apply, heatKernel1D_zero_eq_prefactor, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- **Stability of the `n`-dim heat semigroup in the data**: `|f - g| ≤ C` pointwise
(with both bounded measurable) gives `|Hₜf x - Hₜg x| ≤ C`. -/
theorem abs_heatSemigroupND_sub_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f g : (Fin n → ℝ) → ℝ) (C D : ℝ) (x : Fin n → ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ D)
    (hgm : AEStronglyMeasurable g) (hgb : ∀ y, ‖g y‖ ≤ D)
    (hbound : ∀ y, |f y - g y| ≤ C) :
    |heatSemigroupND t f x - heatSemigroupND t g x| ≤ C := by
  rw [← heatSemigroupND_sub ht x hfm hfb hgm hgb]
  exact abs_heatSemigroupND_le ht x hbound

/-- Lower bound counterpart of the `n`-dim semigroup maximum principle. -/
theorem heatSemigroupND_neg_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : (Fin n → ℝ) → ℝ) (C : ℝ) (x : Fin n → ℝ)
    (hf : ∀ y, |f y| ≤ C) : -C ≤ heatSemigroupND t f x :=
  (abs_le.mp (abs_heatSemigroupND_le ht x hf)).1

/-- The `n`-dim semigroup output lies in `[-C, C]` for `|f| ≤ C`. -/
theorem heatSemigroupND_mem_Icc_neg_pos (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : (Fin n → ℝ) → ℝ) (C : ℝ) (x : Fin n → ℝ) (hf : ∀ y, |f y| ≤ C) :
    heatSemigroupND t f x ∈ Set.Icc (-C) C :=
  Set.mem_Icc.mpr ⟨(abs_le.mp (abs_heatSemigroupND_le ht x hf)).1,
    le_of_abs_le (abs_heatSemigroupND_le ht x hf)⟩

/-- Alternative form of the kernel Lipschitz constant: `Lip(t) = (1/(2√t))·(4πt)^(-1/2)`. -/
lemma heatKernel1DLipConst_eq (t : ℝ) (ht : 0 < t) :
    heatKernel1DLipConst t = 1 / (2 * Real.sqrt t) * (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  rw [heatKernel1DLipConst, mul_div_assoc, sqrt_t_div_two_t_eq t ht]
  ring

/-- Positivity of the named kernel Lipschitz constant. -/
lemma heatKernel1DLipConst_pos (t : ℝ) (ht : 0 < t) : 0 < heatKernel1DLipConst t := by
  unfold heatKernel1DLipConst
  positivity

/-- Updating coordinate `i` to its own value is the identity. -/
lemma heatKernelND_update_self (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    heatKernelND t (Function.update x i (x i)) = heatKernelND t x := by
  rw [Function.update_eq_self]

/-- The `n`-dim kernel with coordinate `i` set to `r` factors as `K(t,r)·∏_{j≠i}K(t,xⱼ)`. -/
lemma heatKernelND_update_factor (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    heatKernelND t (Function.update x i r)
      = heatKernel1D t r * ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) := by
  rw [heatKernelND_eq_update_mul n t (Function.update x i r) i]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The erased-coordinate product is nonnegative. -/
lemma heatKernelND_prod_erase_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) :=
  Finset.prod_nonneg (fun j _ => heatKernel1D_nonneg ht (x j))

/-- **The coordinate partial derivative of the `n`-dimensional heat kernel**:
`∂_{xᵢ} Kₙ(t, x) = Kₙ(t, x)·(-xᵢ/(2t))`.  Proved via the factorization
`Kₙ = K(t,xᵢ)·∏_{j≠i}K(t,xⱼ)` (the non-`i` factors are constant in `xᵢ`).  This is
the structural input for the `n`-dimensional heat equation of the semigroup. -/
lemma hasDerivAt_heatKernelND_coord (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun r => heatKernelND t (Function.update x i r))
      (heatKernelND t x * (-(x i) / (2 * t))) (x i) := by
  set P : ℝ := ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) with hP
  have hfun : (fun r => heatKernelND t (Function.update x i r))
      = (fun r => heatKernel1D t r * P) := by
    funext r
    rw [heatKernelND_eq_update_mul n t (Function.update x i r) i]
    rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hfun]
  have hbase := (hasDerivAt_heatKernel1D_space ht (x i)).mul_const P
  convert hbase using 1
  rw [heatKernelND_eq_update_mul n t x i, ← hP]
  ring

/-- Differentiability of the `n`-dim kernel along a coordinate. -/
lemma differentiableAt_heatKernelND_coord (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) :
    DifferentiableAt ℝ (fun r => heatKernelND t (Function.update x i r)) (x i) :=
  (hasDerivAt_heatKernelND_coord n t ht x i).differentiableAt

/-- Scalar bound for the `n`-dim semigroup: `|Hₜ(c·f)| ≤ c·C` for `c ≥ 0`, `|f| ≤ C`. -/
theorem heatSemigroupND_smul_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : (Fin n → ℝ) → ℝ) (c C : ℝ) (x : Fin n → ℝ) (hc : 0 ≤ c)
    (hf : ∀ y, |f y| ≤ C) :
    |heatSemigroupND t (fun y => c * f y) x| ≤ c * C := by
  rw [heatSemigroupND_smul, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_heatSemigroupND_le ht x hf) hc

/-- The factorization identity, reversed (product form to `Kₙ`). -/
lemma heatKernelND_update_eq_self_factor (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    heatKernel1D t (x i) * ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j)
      = heatKernelND t x :=
  (heatKernelND_eq_update_mul n t x i).symm

/-- The coordinate partial derivative of `Kₙ` at an arbitrary point `a` (not just `xᵢ`):
`∂_r Kₙ(t, update x i r)|_a = K(t,a)·(-a/(2t))·∏_{j≠i}K(t,xⱼ)`. -/
lemma hasDerivAt_heatKernelND_coord_at (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) (a : ℝ) :
    HasDerivAt (fun r => heatKernelND t (Function.update x i r))
      (heatKernel1D t a * (-(a) / (2 * t)) *
        (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j))) a := by
  set P := (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j)) with hP
  have hfun : (fun r => heatKernelND t (Function.update x i r))
      = (fun r => heatKernel1D t r * P) := by
    funext r; exact heatKernelND_update_factor n t x i r
  rw [hfun]
  exact (hasDerivAt_heatKernel1D_space ht a).mul_const P

/-- The coordinate partial derivative of `Kₙ`, as a `deriv`. -/
lemma deriv_heatKernelND_coord (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) (i : Fin n) :
    deriv (fun r => heatKernelND t (Function.update x i r)) (x i)
      = heatKernelND t x * (-(x i) / (2 * t)) :=
  (hasDerivAt_heatKernelND_coord n t ht x i).deriv

/-- **The second coordinate partial derivative of the `n`-dimensional heat kernel**:
differentiating `r ↦ ∂_{xᵢ}Kₙ(t, update x i r)` again at `r = xᵢ` gives
`Kₙ(t,x)·(xᵢ²/(4t²) - 1/(2t))`.  Together with the first partials, this assembles
the `n`-dimensional Laplacian of `Kₙ`. -/
lemma hasDerivAt_heatKernelND_coord_second (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t)))
      (heatKernelND t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) (x i) := by
  set P := ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) with hP
  have hfun : (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t)))
      = (fun r => (heatKernel1D t r * (-(r) / (2 * t))) * P) := by
    funext r
    rw [heatKernelND_update_factor n t x i r, hP]
    ring
  rw [hfun]
  convert (hasDerivAt_heatKernel1D_space_second ht (x i)).mul_const P using 1
  rw [heatKernelND_eq_update_mul n t x i, hP]
  ring

/-- The `n`-dim kernel is Lipschitz along a single coordinate, with explicit constant. -/
theorem heatKernelND_update_sub_abs_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) (r s : ℝ) :
    |heatKernelND t (Function.update x i r) - heatKernelND t (Function.update x i s)| ≤
      (((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) *
        ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t))) * |r - s| := by
  rw [heatKernelND_update_factor n t x i r, heatKernelND_update_factor n t x i s, ← sub_mul,
    abs_mul]
  rw [abs_of_nonneg (heatKernelND_prod_erase_nonneg n t ht x i)]
  have hP : (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j))
      ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) := by
    calc (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j))
        ≤ ∏ _j ∈ Finset.univ.erase i, (4 * π * t) ^ (-(1 : ℝ) / 2) :=
          Finset.prod_le_prod (fun j _ => heatKernel1D_nonneg ht (x j))
            (fun j _ => heatKernel1D_le_prefactor ht (x j))
      _ = ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  have hK : |heatKernel1D t r - heatKernel1D t s|
      ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) * |r - s| :=
    heatKernel1D_sub_abs_le t ht r s
  calc |heatKernel1D t r - heatKernel1D t s|
        * (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j))
      ≤ ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t) * |r - s|) *
          ((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) :=
        mul_le_mul hK hP (heatKernelND_prod_erase_nonneg n t ht x i)
          (le_trans (abs_nonneg _) hK)
    _ = (((4 * π * t) ^ (-(1 : ℝ) / 2)) ^ (n - 1) *
          ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.sqrt t / (2 * t))) * |r - s| := by ring

/-- The `n`-dim semigroup annihilates the zero constant. -/
theorem heatSemigroupND_zero_const (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) :
    heatSemigroupND t (fun _ => (0 : ℝ)) x = 0 := by
  simpa using heatSemigroupND_const ht 0 x

/-- The second coordinate partial derivative as a `deriv` value. -/
lemma heatKernelND_coord_second_value (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) (i : Fin n) :
    deriv (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t))) (x i)
      = heatKernelND t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) :=
  (hasDerivAt_heatKernelND_coord_second n t ht x i).deriv

/-- Differentiability of the coordinate first-derivative slice. -/
lemma differentiableAt_heatKernelND_coord_second (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) (i : Fin n) :
    DifferentiableAt ℝ (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t))) (x i) :=
  (hasDerivAt_heatKernelND_coord_second n t ht x i).differentiableAt

/-- **The Laplacian of the `n`-dimensional kernel factors out `Kₙ`**: the sum of the
second coordinate partials equals `Kₙ(t,x)·Σᵢ(xᵢ²/(4t²) − 1/(2t))`. -/
lemma heatKernelND_laplacian_eq (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    (∑ i : Fin n, heatKernelND t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))
      = heatKernelND t x * (∑ i : Fin n, ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
  rw [Finset.mul_sum]

/-- The sum of the per-coordinate heat-equation coefficients:
`Σᵢ(xᵢ²/(4t²) − 1/(2t)) = (Σᵢxᵢ²)/(4t²) − n/(2t)`.  Hence the `n`-dimensional
kernel Laplacian is `Kₙ(t,x)·(|x|²/(4t²) − n/(2t))`. -/
lemma sum_heatKernel_coeff (n : ℕ) (t : ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))
      = (∑ i : Fin n, (x i) ^ 2) / (4 * t ^ 2) - n / (2 * t) := by
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_div]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- The coordinate partial at the centre vanishes. -/
lemma heatKernelND_coord_at_zero (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ)
    (i : Fin n) :
    heatKernel1D t 0 * (-(0 : ℝ) / (2 * t)) * (∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j)) = 0 := by
  simp

/-- Strict positivity of the erased-coordinate product. -/
lemma heatKernelND_pos_prod_factor (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ)
    (i : Fin n) : 0 < ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j) :=
  Finset.prod_pos (fun j _ => heatKernel1D_pos ht (x j))

/-- The single-factor product identity reconstructs `Kₙ`. -/
lemma heatKernel1D_factor_eq_kernelND (n : ℕ) (t : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    heatKernel1D t (x i) * ∏ j ∈ Finset.univ.erase i, heatKernel1D t (x j)
      = heatKernelND t x := by
  rw [heatKernelND_apply]
  exact Finset.mul_prod_erase _ (fun j => heatKernel1D t (x j)) (Finset.mem_univ i)

/-- The shifted `n`-dim kernel as a product of shifted 1D kernels. -/
lemma heatKernelND_sub_apply (n : ℕ) (t : ℝ) (x y : Fin n → ℝ) :
    heatKernelND t (x - y) = ∏ i, heatKernel1D t (x i - y i) := by
  rw [heatKernelND_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.sub_apply]

/-- The `n`-dim kernel is nonzero. -/
lemma heatKernelND_ne_zero (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    heatKernelND t x ≠ 0 :=
  ne_of_gt (heatKernelND_pos ht x)

/-- **The time derivative of the `n`-dimensional heat kernel** (via the finite
product rule over coordinates): `∂ₜKₙ(t,x) = Kₙ(t,x)·Σᵢ(xᵢ²/(4t²) − 1/(2t))`. -/
lemma hasDerivAt_heatKernelND_time (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    HasDerivAt (fun s => heatKernelND s x)
      (heatKernelND t x * (∑ i : Fin n, ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))) t := by
  have h := HasDerivAt.finset_prod (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin n)))
    (f := fun i => fun s => heatKernel1D s (x i))
    (f' := fun i => heatKernel1D t (x i) * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))
    (x := t)
    (fun i _ => hasDerivAt_heatKernel1D_time ht (x i))
  have hfun : (fun s => heatKernelND s x)
      = ∏ i : Fin n, (fun s => heatKernel1D s (x i)) := by
    funext s
    rw [Finset.prod_apply, heatKernelND_apply]
  rw [hfun]
  convert h using 1
  rw [← heatKernelND_laplacian_eq n t ht x]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_mul, heatKernelND_apply,
      ← Finset.mul_prod_erase Finset.univ (fun j => heatKernel1D t (x j)) (Finset.mem_univ i)]
  ring

/-- Differentiability of the `n`-dim kernel in time. -/
lemma differentiableAt_heatKernelND_time (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : Fin n → ℝ) : DifferentiableAt ℝ (fun s => heatKernelND s x) t :=
  (hasDerivAt_heatKernelND_time n t ht x).differentiableAt

/-- The `n`-dim kernel is continuous in time on `(0, ∞)`. -/
lemma heatKernelND_continuous_time (n : ℕ) (x : Fin n → ℝ) :
    ContinuousOn (fun s => heatKernelND s x) (Set.Ioi 0) := by
  simp only [heatKernelND_apply]
  apply continuousOn_finset_prod
  intro i _
  intro s hs
  exact (hasDerivAt_heatKernel1D_time hs (x i)).continuousAt.continuousWithinAt

/-- **The `n`-dimensional heat kernel solves the `n`-dimensional heat equation**:
`∂ₜKₙ = ΔKₙ` at every `(t, x)` with `t > 0`.  The time derivative
`Kₙ·Σᵢ(xᵢ²/(4t²) − 1/(2t))` is exactly the sum of the second coordinate partials
(the Laplacian), since each 1D factor solves the 1D heat equation. -/
theorem heatKernelND_solves_heatEquation (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    deriv (fun s => heatKernelND s x) t
      = ∑ i : Fin n, deriv (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t))) (x i) := by
  rw [(hasDerivAt_heatKernelND_time n t ht x).deriv]
  rw [show (∑ i : Fin n, deriv (fun r => heatKernelND t (Function.update x i r) * (-(r) / (2 * t))) (x i))
      = ∑ i : Fin n, heatKernelND t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) from
    Finset.sum_congr rfl (fun i _ => (hasDerivAt_heatKernelND_coord_second n t ht x i).deriv)]
  rw [heatKernelND_laplacian_eq n t ht x]

/-- The `n`-dim kernel time derivative, as a `deriv`. -/
lemma deriv_heatKernelND_time_eq (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    deriv (fun s => heatKernelND s x) t
      = heatKernelND t x * (∑ i : Fin n, ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) :=
  (hasDerivAt_heatKernelND_time n t ht x).deriv

/-- The `n`-dim kernel time derivative in closed form: `Kₙ·(|x|²/(4t²) − n/(2t))`. -/
lemma deriv_heatKernelND_time_eq_closed (n : ℕ) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    deriv (fun s => heatKernelND s x) t
      = heatKernelND t x * ((∑ i : Fin n, (x i) ^ 2) / (4 * t ^ 2) - n / (2 * t)) := by
  rw [(hasDerivAt_heatKernelND_time n t ht x).deriv, sum_heatKernel_coeff n t x]

/-- The 1D heat-equation coefficient `xᵢ²/(4t²) − 1/(2t)`, named for variable-coefficient
operator work. -/
noncomputable def laplacianCoeff (t : ℝ) (x : ℝ) : ℝ := x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)

/-- The 1D kernel second spatial derivative expressed through `laplacianCoeff`. -/
lemma heatKernel1D_space_second_eq_coeff (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => heatKernel1D t y * (-y / (2 * t)))
      (heatKernel1D t x * laplacianCoeff t x) x := by
  unfold laplacianCoeff
  exact hasDerivAt_heatKernel1D_space_second ht x

/-- The shifted `n`-dim kernel at a self-difference. -/
lemma heatKernelND_sub_self_eq (n : ℕ) (t : ℝ) (x : Fin n → ℝ) :
    heatKernelND t (x - x) = heatKernelND t (0 : Fin n → ℝ) := by
  rw [sub_self]

/-- The `n`-dim convolution integrand is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_heatKernelND_sub_mul (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hfm : AEStronglyMeasurable f) :
    AEStronglyMeasurable (fun y => heatKernelND t (x - y) * f y) volume :=
  (aestronglyMeasurable_heatKernelND_sub (t := t) x).mul hfm

/-- Positivity of a product of two 1D kernels. -/
lemma heatKernel1D_mul_pos (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    0 < heatKernel1D t x * heatKernel1D t y :=
  mul_pos (heatKernel1D_pos ht x) (heatKernel1D_pos ht y)

/-- The 1-dimensional kernel reduces to the 1D kernel. -/
lemma heatKernelND_one_eq (t : ℝ) (x : Fin 1 → ℝ) :
    heatKernelND t x = heatKernel1D t (x 0) := by
  rw [heatKernelND_apply, Fin.prod_univ_one]

/-- The 2-dimensional kernel as a product of two 1D kernels. -/
lemma heatKernelND_two_eq (t : ℝ) (x : Fin 2 → ℝ) :
    heatKernelND t x = heatKernel1D t (x 0) * heatKernel1D t (x 1) := by
  rw [heatKernelND_apply, Fin.prod_univ_two]

/-- The 3-dimensional kernel as a product of three 1D kernels. -/
lemma heatKernelND_three_eq (t : ℝ) (x : Fin 3 → ℝ) :
    heatKernelND t x = heatKernel1D t (x 0) * heatKernel1D t (x 1) * heatKernel1D t (x 2) := by
  rw [heatKernelND_apply, Fin.prod_univ_three]

/-- Unfolding of `laplacianCoeff`. -/
lemma laplacianCoeff_eq (t : ℝ) (x : ℝ) :
    laplacianCoeff t x = x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) := rfl

/-- `laplacianCoeff` is even in the space variable. -/
lemma laplacianCoeff_neg_eq (t : ℝ) (x : ℝ) :
    laplacianCoeff t (-x) = laplacianCoeff t x := by
  simp [laplacianCoeff]

/-- A weighted (variable-coefficient) second-order operator `a·∂ₓₓg`, the first
scaffolding toward variable-coefficient parabolic operators. -/
noncomputable def weightedHeatOp (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  a * deriv (deriv g) x

/-- The weighted operator annihilates constants. -/
lemma weightedHeatOp_const_zero (a : ℝ) (c x : ℝ) :
    weightedHeatOp a (fun _ => c) x = 0 := by
  have h : deriv (fun _ : ℝ => c) = fun _ => (0 : ℝ) := by
    ext y; exact deriv_const y c
  rw [weightedHeatOp, h]
  simp

end AnalyticPDE
end RicciFlow
