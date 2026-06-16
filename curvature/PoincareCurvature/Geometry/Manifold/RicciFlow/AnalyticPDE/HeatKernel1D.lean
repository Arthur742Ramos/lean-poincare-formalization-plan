module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

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
open scoped Real ENNReal NNReal

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

/-- Definitional unfolding of `weightedHeatOp`. -/
lemma weightedHeatOp_eq (a : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    weightedHeatOp a g x = a * deriv (deriv g) x := rfl

/-- Scalar homogeneity of the weighted operator (for `C¹` data with `C¹` derivative). -/
lemma weightedHeatOp_smul (a c : ℝ) (g : ℝ → ℝ) (x : ℝ)
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g)) :
    weightedHeatOp a (fun y => c * g y) x = c * weightedHeatOp a g x := by
  unfold weightedHeatOp
  have h1 : deriv (fun z => c * g z) = fun y => c * deriv g y := by
    ext y; exact deriv_const_mul c (hg y)
  rw [h1]
  have h2 : deriv (fun y => c * deriv g y) x = c * deriv (deriv g) x :=
    deriv_const_mul c (hg2 x)
  rw [h2]
  ring

/-- The weighted operator annihilates the zero function. -/
lemma weightedHeatOp_zero_fun (a x : ℝ) :
    weightedHeatOp a (fun _ => (0 : ℝ)) x = 0 :=
  weightedHeatOp_const_zero a 0 x

/-- A zero coefficient kills the weighted operator. -/
lemma weightedHeatOp_zero_coeff (g : ℝ → ℝ) (x : ℝ) : weightedHeatOp 0 g x = 0 := by
  simp [weightedHeatOp]

/-- The 1D kernel's second spatial derivative, in `laplacianCoeff` form. -/
lemma heatKernel1D_second_deriv_eq (t : ℝ) (ht : 0 < t) (x : ℝ) :
    deriv (fun y => heatKernel1D t y * (-y / (2 * t))) x
      = heatKernel1D t x * laplacianCoeff t x :=
  (heatKernel1D_space_second_eq_coeff t ht x).deriv

/-- `laplacianCoeff t x > 0` once `x² > 2t` (the coefficient is positive away from
the origin). -/
lemma laplacianCoeff_pos_large (t : ℝ) (ht : 0 < t) (x : ℝ)
    (hx : 2 * t < x ^ 2) : 0 < laplacianCoeff t x := by
  have h4t2 : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have hne : (4 * t ^ 2 : ℝ) ≠ 0 := ne_of_gt h4t2
  have htne : (2 * t : ℝ) ≠ 0 := by positivity
  have hrw : x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) = (x ^ 2 - 2 * t) / (4 * t ^ 2) := by
    field_simp
    ring
  rw [laplacianCoeff_eq, hrw]
  apply div_pos _ h4t2
  linarith [hx]

/-- `laplacianCoeff t 0 = -1/(2t)`. -/
lemma laplacianCoeff_zero (t : ℝ) (ht : 0 < t) : laplacianCoeff t 0 = -(1 / (2 * t)) := by
  simp [laplacianCoeff]

/-- **The Laplacian (second spatial derivative) of `Hₜf` as a kernel-weighted
integral** through `laplacianCoeff`: `∂ₓₓHₜf(x) = ∫ K(t,x-y)·c(t,x-y)·f y`, where
`c = laplacianCoeff`.  This is the representation that links the constant-coefficient
heat semigroup to variable-coefficient operator solvability. -/
lemma heatSemigroup1D_deriv2_integral_form (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ)
    (C : ℝ) (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (deriv (fun z => heatSemigroup1D t f z)) x
      = ∫ y, (heatKernel1D t (x - y) * laplacianCoeff t (x - y)) * f y := by
  rw [deriv2_heatSemigroup1D_eq_integral ht x hfm hfb]
  simp_rw [laplacianCoeff_eq]

/-! ### Chapman–Kolmogorov (semigroup composition)

The convolution-semigroup identity `∫ K(t,a−z)·K(s,z−b) dz = K(t+s,a−b)` is the
analytic heart of the heat semigroup's composition law `Hₜ ∘ Hₛ = H_{t+s}`, and
the gateway to Duhamel's principle for the inhomogeneous equation — the engine of
variable-coefficient and quasilinear (Ricci–DeTurck) perturbation theory. -/

/-- Product of two shifted heat kernels, with the two Gaussian exponents combined. -/
lemma heatKernel1D_mul_eq (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (a b z : ℝ) :
    heatKernel1D t (a - z) * heatKernel1D s (z - b)
      = ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * π * s) ^ (-(1 : ℝ) / 2))
        * Real.exp (-((a - z) ^ 2 / (4 * t) + (z - b) ^ 2 / (4 * s))) := by
  rw [heatKernel1D_apply, heatKernel1D_apply, mul_mul_mul_comm, ← Real.exp_add,
    show -(a - z) ^ 2 / (4 * t) + -(z - b) ^ 2 / (4 * s)
        = -((a - z) ^ 2 / (4 * t) + (z - b) ^ 2 / (4 * s)) by ring]

/-- Completing the square in the combined exponent: the `z`-dependence is a single
shifted square, with residual the `(a−b)` Gaussian at time `t+s`. -/
lemma gaussian_exponent_complete_square (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (a b z : ℝ) :
    (a - z) ^ 2 / (4 * t) + (z - b) ^ 2 / (4 * s)
      = (t + s) / (4 * t * s) * (z - (s * a + t * b) / (t + s)) ^ 2
        + (a - b) ^ 2 / (4 * (t + s)) := by
  have hts : (0 : ℝ) < t + s := by linarith
  have ht' : t ≠ 0 := ne_of_gt ht
  have hs' : s ≠ 0 := ne_of_gt hs
  have htsne : t + s ≠ 0 := ne_of_gt hts
  field_simp
  ring

/-- A shifted/scaled 1D Gaussian integral in closed form (translation invariance
plus `integral_gaussian`). -/
lemma integral_gaussian_shift (c μ : ℝ) (hc : 0 < c) :
    ∫ z : ℝ, Real.exp (-c * (z - μ) ^ 2) = Real.sqrt (π / c) := by
  have h : (∫ z : ℝ, Real.exp (-c * (z - μ) ^ 2))
      = ∫ w : ℝ, Real.exp (-c * w ^ 2) :=
    integral_sub_right_eq_self (fun w => Real.exp (-c * w ^ 2)) μ
  rw [h, integral_gaussian]

/-- Joint integrability in `z` of the product of two shifted kernels (so the
convolution integral is well-defined). -/
lemma integrable_heatKernel1D_mul_pair (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (a b : ℝ) :
    Integrable (fun z => heatKernel1D t (a - z) * heatKernel1D s (z - b)) := by
  refine (integrable_heatKernel1D_sub ht a).mul_bdd (c := (4 * π * s) ^ (-(1 : ℝ) / 2)) ?_ ?_
  · exact ((continuous_heatKernel1D_space s).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (heatKernel1D_nonneg hs _)]
    exact heatKernel1D_le_prefactor hs _

/-- Symmetry of the kernel's spatial argument under swapping the subtraction order. -/
lemma heatKernel1D_sub_comm (t a z : ℝ) :
    heatKernel1D t (a - z) = heatKernel1D t (z - a) := by
  rw [← heatKernel1D_neg t (z - a)]
  ring_nf

/-- The prefactor-collapse identity: the two kernel prefactors times the Gaussian
normalisation `√(π / c)` (with `c = (t+s)/(4ts)`) collapse to the single `t+s`
prefactor. This is the normalisation miracle behind Chapman–Kolmogorov. -/
lemma prefactor_product_eq (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * π * s) ^ (-(1 : ℝ) / 2))
        * Real.sqrt (π / ((t + s) / (4 * t * s)))
      = (4 * π * (t + s)) ^ (-(1 : ℝ) / 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have e : ∀ u : ℝ, 0 < u → u ^ (-(1 : ℝ) / 2) = (Real.sqrt u)⁻¹ := by
    intro u hu
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  rw [e _ (by positivity), e _ (by positivity), e _ (by positivity)]
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv]
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  have h1 : (4 : ℝ) * π * t ≠ 0 := by positivity
  have h2 : (4 : ℝ) * π * s ≠ 0 := by positivity
  have h3 : (4 : ℝ) * π * (t + s) ≠ 0 := by positivity
  have h4 : t + s ≠ 0 := by positivity
  have h5 : (4 : ℝ) * t * s ≠ 0 := by positivity
  field_simp

/-- Continuity in `z` of the kernel-product integrand. -/
lemma continuous_heatKernel1D_pair_z (t s a b : ℝ) :
    Continuous (fun z => heatKernel1D t (a - z) * heatKernel1D s (z - b)) :=
  ((continuous_heatKernel1D_space t).comp (by fun_prop)).mul
    ((continuous_heatKernel1D_space s).comp (by fun_prop))

/-- **Chapman–Kolmogorov identity.** The convolution of the heat kernels at times
`t` and `s` is the heat kernel at time `t+s`:
`∫ K(t,a−z)·K(s,z−b) dz = K(t+s, a−b)`. -/
theorem heatKernel1D_chapman_kolmogorov (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (a b : ℝ) :
    ∫ z : ℝ, heatKernel1D t (a - z) * heatKernel1D s (z - b)
      = heatKernel1D (t + s) (a - b) := by
  have hts : (0 : ℝ) < t + s := by linarith
  have hc : (0 : ℝ) < (t + s) / (4 * t * s) := by positivity
  -- Rewrite the integrand: product of kernels → prefactor · exp(completed square).
  have hint : (fun z => heatKernel1D t (a - z) * heatKernel1D s (z - b))
      = fun z => ((4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * π * s) ^ (-(1 : ℝ) / 2))
          * (Real.exp (-((a - b) ^ 2 / (4 * (t + s))))
            * Real.exp (-((t + s) / (4 * t * s))
                * (z - (s * a + t * b) / (t + s)) ^ 2)) := by
    funext z
    rw [heatKernel1D_mul_eq t s ht hs a b z, gaussian_exponent_complete_square t s ht hs a b z]
    rw [show -((t + s) / (4 * t * s) * (z - (s * a + t * b) / (t + s)) ^ 2
            + (a - b) ^ 2 / (4 * (t + s)))
        = -((a - b) ^ 2 / (4 * (t + s)))
          + -((t + s) / (4 * t * s)) * (z - (s * a + t * b) / (t + s)) ^ 2 by ring,
      Real.exp_add]
  rw [hint]
  -- Pull constants out of the integral; the remaining integral is a shifted Gaussian.
  rw [integral_const_mul, integral_const_mul]
  rw [integral_gaussian_shift ((t + s) / (4 * t * s)) ((s * a + t * b) / (t + s)) hc]
  -- Reassemble into K(t+s, a-b).
  rw [heatKernel1D_apply]
  rw [show -(a - b) ^ 2 / (4 * (t + s)) = -((a - b) ^ 2 / (4 * (t + s))) by ring]
  rw [← prefactor_product_eq t s ht hs]
  ring

/-- The heat semigroup preserves nonnegativity (clean maximum-principle corollary). -/
lemma heatSemigroup1D_nonneg_of_nonneg {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : ℝ) : 0 ≤ heatSemigroup1D t f x := by
  rw [heatSemigroup1D]
  exact integral_nonneg (fun y => mul_nonneg (heatKernel1D_nonneg ht (x - y)) (hf y))

/-! ### Semigroup composition law and Duhamel scaffolding

The Chapman–Kolmogorov identity lifts (via Fubini) to the semigroup composition
law `Hₜ ∘ Hₛ = H_{t+s}` — the Markov/semigroup structure of the heat flow — and
the inhomogeneous Duhamel convolution that drives variable-coefficient
perturbation theory. -/

/-- Sup-norm bound on `Hₜf` (restated from `abs_heatSemigroup1D_le`). -/
lemma heatSemigroup1D_abs_le_sup {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    |heatSemigroup1D t f x| ≤ C :=
  abs_heatSemigroup1D_le ht x (fun y => by simpa [Real.norm_eq_abs] using hfb y)

/-- Joint integrability of the uncurried kernel-product on the plane (Fubini
hypothesis for the composition law). -/
lemma integrable_uncurry_heatKernel_pair (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x : ℝ) :
    Integrable (Function.uncurry fun (y z : ℝ) => heatKernel1D t (x - z) * heatKernel1D s (z - y))
      (volume.prod volume) := by
  have hts : (0 : ℝ) < t + s := by linarith
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (y z : ℝ) => heatKernel1D t (x - z) * heatKernel1D s (z - y))
      (volume.prod volume) := by
    apply Continuous.aestronglyMeasurable
    unfold Function.uncurry
    exact ((continuous_heatKernel1D_space t).comp (by fun_prop)).mul
      ((continuous_heatKernel1D_space s).comp (by fun_prop))
  rw [MeasureTheory.integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall (fun y => ?_), ?_⟩
  · exact integrable_heatKernel1D_mul_pair t s ht hs x y
  · apply (integrable_heatKernel1D_sub hts x).congr
    refine Filter.Eventually.of_forall (fun y => ?_)
    show heatKernel1D (t + s) (x - y)
        = ∫ z, ‖heatKernel1D t (x - z) * heatKernel1D s (z - y)‖
    rw [← heatKernel1D_chapman_kolmogorov t s ht hs x y]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun z => ?_)
    dsimp only
    rw [Real.norm_of_nonneg
      (mul_nonneg (heatKernel1D_nonneg ht _) (heatKernel1D_nonneg hs _))]

/-- Pointwise integrand identity feeding the composition-law Fubini step. -/
lemma heatSemigroup1D_chapman_pointwise (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (f : ℝ → ℝ) (x y : ℝ) :
    (∫ z, heatKernel1D t (x - z) * heatKernel1D s (z - y) * f y)
      = heatKernel1D (t + s) (x - y) * f y := by
  rw [integral_mul_const, heatKernel1D_chapman_kolmogorov t s ht hs x y]

/-- **Heat-semigroup composition law.** `Hₜ(Hₛf) = H_{t+s}f` for bounded
measurable `f`, the semigroup/Markov structure of the heat flow, proved by Fubini
from Chapman–Kolmogorov. -/
theorem heatSemigroup1D_comp (t s : ℝ) (ht : 0 < t) (hs : 0 < s) {f : ℝ → ℝ} {C : ℝ}
    (x : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    heatSemigroup1D t (fun w => heatSemigroup1D s f w) x = heatSemigroup1D (t + s) f x := by
  have hpair_cont : Continuous
      (fun p : ℝ × ℝ => heatKernel1D t (x - p.1) * heatKernel1D s (p.1 - p.2)) :=
    ((continuous_heatKernel1D_space t).comp (continuous_const.sub continuous_fst)).mul
      ((continuous_heatKernel1D_space s).comp (continuous_fst.sub continuous_snd))
  have hpair_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => heatKernel1D t (x - p.1) * heatKernel1D s (p.1 - p.2))
      (volume.prod volume) := hpair_cont.aestronglyMeasurable
  have hbase : Integrable
      (fun p : ℝ × ℝ => heatKernel1D t (x - p.1) * heatKernel1D s (p.1 - p.2))
      (volume.prod volume) := by
    refine (integrable_prod_iff hpair_meas).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall
        (fun z => (integrable_heatKernel1D_sub hs z).const_mul (heatKernel1D t (x - z)))
    · have hfun :
          (fun z => ∫ y, ‖heatKernel1D t (x - z) * heatKernel1D s (z - y)‖)
            = fun z => heatKernel1D t (x - z) := by
        funext z
        have hnorm :
            (fun y => ‖heatKernel1D t (x - z) * heatKernel1D s (z - y)‖)
              = fun y => heatKernel1D t (x - z) * heatKernel1D s (z - y) := by
          funext y
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (heatKernel1D_nonneg ht _) (heatKernel1D_nonneg hs _))]
        rw [hnorm, integral_const_mul, integral_heatKernel1D_sub hs z, mul_one]
      rw [hfun]
      exact integrable_heatKernel1D_sub ht x
  have hfull : Integrable
      (fun p : ℝ × ℝ => (heatKernel1D t (x - p.1) * heatKernel1D s (p.1 - p.2)) * f p.2)
      (volume.prod volume) :=
    hbase.mul_bdd hfm.comp_snd (Filter.Eventually.of_forall (fun p => hfb p.2))
  have hintegr : Integrable
      (Function.uncurry
        (fun z y => heatKernel1D t (x - z) * (heatKernel1D s (z - y) * f y)))
      (volume.prod volume) := by
    have heq :
        (Function.uncurry
          (fun z y => heatKernel1D t (x - z) * (heatKernel1D s (z - y) * f y)))
          = fun p : ℝ × ℝ =>
            (heatKernel1D t (x - p.1) * heatKernel1D s (p.1 - p.2)) * f p.2 := by
      funext p
      simp only [Function.uncurry]
      ring
    rw [heq]
    exact hfull
  simp only [heatSemigroup1D]
  have step1 : ∀ z : ℝ,
      heatKernel1D t (x - z) * (∫ y, heatKernel1D s (z - y) * f y)
        = ∫ y, heatKernel1D t (x - z) * (heatKernel1D s (z - y) * f y) := by
    intro z
    rw [integral_const_mul]
  simp_rw [step1]
  rw [integral_integral_swap hintegr]
  have step3 : ∀ y : ℝ,
      (∫ z, heatKernel1D t (x - z) * (heatKernel1D s (z - y) * f y))
        = heatKernel1D (t + s) (x - y) * f y := by
    intro y
    have hassoc :
        (fun z => heatKernel1D t (x - z) * (heatKernel1D s (z - y) * f y))
          = fun z => (heatKernel1D t (x - z) * heatKernel1D s (z - y)) * f y := by
      funext z; ring
    rw [hassoc, integral_mul_const, heatKernel1D_chapman_kolmogorov t s ht hs x y]
  simp_rw [step3]

/-- The composition law in the constant case (no Fubini needed; independent check). -/
lemma heatSemigroup1D_comp_const (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (c x : ℝ) :
    heatSemigroup1D t (fun w => heatSemigroup1D s (fun _ => c) w) x
      = heatSemigroup1D (t + s) (fun _ => c) x := by
  have hinner : (fun w => heatSemigroup1D s (fun _ => c) w) = fun _ => c := by
    funext w; exact heatSemigroup1D_const hs c w
  rw [hinner, heatSemigroup1D_const ht, heatSemigroup1D_const (by linarith : 0 < t + s)]

/-- **n-dimensional Chapman–Kolmogorov.** The convolution of the nD heat kernels
at times `t` and `s` is the nD heat kernel at time `t+s`, proved coordinatewise
from the 1D identity via the product structure. -/
theorem heatKernelND_chapman_kolmogorov {n : ℕ} (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (a b : Fin n → ℝ) :
    ∫ z : Fin n → ℝ, heatKernelND t (a - z) * heatKernelND s (z - b)
      = heatKernelND (t + s) (a - b) := by
  have hfun : (fun z : Fin n → ℝ => heatKernelND t (a - z) * heatKernelND s (z - b))
      = fun z : Fin n → ℝ =>
        ∏ i, (heatKernel1D t (a i - z i) * heatKernel1D s (z i - b i)) := by
    funext z
    rw [heatKernelND, heatKernelND, ← Finset.prod_mul_distrib]
    rfl
  rw [hfun,
    integral_fin_nat_prod_volume_eq_prod
      (fun i (z : ℝ) => heatKernel1D t (a i - z) * heatKernel1D s (z - b i))]
  simp only [heatKernel1D_chapman_kolmogorov t s ht hs]
  rw [heatKernelND]
  rfl

/-- nD kernel subtraction-symmetry (nD analog of `heatKernel1D_sub_comm`). -/
lemma heatKernelND_sub_comm {n : ℕ} (t : ℝ) (a z : Fin n → ℝ) :
    heatKernelND t (a - z) = heatKernelND t (z - a) := by
  simp only [heatKernelND, Pi.sub_apply, heatKernel1D_sub_comm]

/-- **Duhamel time-convolution.** `duhamelKernel1D t g x = ∫₀ᵗ H_{t−s}(g s) x ds`,
the particular-solution term for the inhomogeneous heat equation
`∂ₜu = ∂ₓₓu + g`. This seeds the perturbation engine toward variable-coefficient
solvability. -/
noncomputable def duhamelKernel1D (t : ℝ) (g : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 t, heatSemigroup1D (t - s) (g s) x

/-- The Duhamel convolution of the zero source is zero. -/
lemma duhamelKernel1D_zero (t : ℝ) (x : ℝ) : duhamelKernel1D t (fun _ _ => 0) x = 0 := by
  unfold duhamelKernel1D
  simp only [heatSemigroup1D_zero]
  simp

/-! ### Quantitative parabolic smoothing constants

The explicit `t^{-1/2}` gradient-smoothing rate `‖∂ₓHₜf‖∞ ≤ C·(πt)^{-1/2}` — the
canonical parabolic Schauder estimate — obtained by evaluating the heat kernel's
absolute first moment `∫|w|K(t,w)` in closed form. -/

/-- Half-line first moment of a Gaussian: `∫₀^∞ x·exp(-b x²) dx = 1/(2b)` (FTC with
antiderivative `-(1/2b)·exp(-b x²)`). -/
lemma integral_Ioi_id_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = 1 / (2 * b) := by
  set F : ℝ → ℝ := fun x => -(1 / (2 * b)) * Real.exp (-b * x ^ 2) with hF
  have hb' : b ≠ 0 := ne_of_gt hb
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -b * x ^ 2) (-b * (2 * x)) x := by
      have := hasDerivAt_pow 2 x
      simpa using this.const_mul (-b)
    have h2 : HasDerivAt (fun x => Real.exp (-b * x ^ 2))
        (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    have h3 : HasDerivAt F (-(1 / (2 * b)) * (Real.exp (-b * x ^ 2) * (-b * (2 * x)))) x :=
      h2.const_mul (-(1 / (2 * b)))
    have heqv : -(1 / (2 * b)) * (Real.exp (-b * x ^ 2) * (-b * (2 * x)))
        = x * Real.exp (-b * x ^ 2) := by field_simp
    rw [heqv] at h3
    exact h3
  have hcont : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0 :=
    (Continuous.continuousWithinAt (by fun_prop))
  have hint : IntegrableOn (fun x => x * Real.exp (-b * x ^ 2)) (Set.Ioi (0 : ℝ)) volume :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have htends : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hmain : Filter.Tendsto (fun x : ℝ => -b * x ^ 2) Filter.atTop Filter.atBot := by
      apply Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -b < 0)
      exact Filter.tendsto_pow_atTop (by norm_num)
    have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (-b * x ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hmain
    have := hexp.const_mul (-(1 / (2 * b)))
    simpa [hF] using this
  have hres := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htends
  rw [hres]
  simp only [hF]
  norm_num

/-- Full-line absolute first moment of a Gaussian: `∫ |x|·exp(-b x²) dx = 1/b`. -/
lemma integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| * Real.exp (-b * x ^ 2) = 1 / b := by
  have h := integral_comp_abs (f := fun t => t * Real.exp (-b * t ^ 2))
  simp only [sq_abs] at h
  rw [h, integral_Ioi_id_mul_exp_neg_mul_sq hb]
  field_simp

/-- The heat kernel's absolute first moment in closed form:
`∫ |w|·K(t,w) dw = (4πt)^(-1/2)·(4t)`. -/
lemma integral_abs_mul_heatKernel1D_eq {t : ℝ} (ht : 0 < t) :
    (∫ w, |w| * heatKernel1D t w) = (4 * π * t) ^ (-(1 : ℝ) / 2) * (4 * t) := by
  set P : ℝ := (4 * π * t) ^ (-(1 : ℝ) / 2) with hP
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hcongr : (∫ w, |w| * heatKernel1D t w)
      = ∫ w, P * (|w| * Real.exp (-(1 / (4 * t)) * w ^ 2)) := by
    apply integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    rw [heatKernel1D_apply]
    have hexp : -w ^ 2 / (4 * t) = -(1 / (4 * t)) * w ^ 2 := by rw [neg_div]; field_simp
    rw [hexp, hP]; ring
  rw [hcongr, integral_const_mul, integral_abs_mul_exp_neg_mul_sq hb]
  rw [hP, one_div_one_div]

/-- Positivity of the heat-kernel first moment. -/
lemma integral_abs_mul_heatKernel1D_pos {t : ℝ} (ht : 0 < t) :
    0 < ∫ w, |w| * heatKernel1D t w := by
  rw [integral_abs_mul_heatKernel1D_eq ht]
  have := heatKernel1D_prefactor_pos ht
  positivity

/-- Algebraic helper: `√(4πt) = 2·√(πt)`. -/
lemma sqrt_four_pi_t_eq (t : ℝ) (ht : 0 < t) :
    Real.sqrt (4 * π * t) = 2 * Real.sqrt (π * t) := by
  rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The prefactor in inverse-sqrt form: `(4πt)^(-1/2) = 1/(2√(πt))`. -/
lemma prefactor_eq_inv_two_sqrt (t : ℝ) (ht : 0 < t) :
    (4 * π * t) ^ (-(1 : ℝ) / 2) = 1 / (2 * Real.sqrt (π * t)) := by
  have e : (4 * π * t) ^ (-(1 : ℝ) / 2) = (Real.sqrt (4 * π * t))⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [e, sqrt_four_pi_t_eq t ht, one_div]

/-- **The canonical `t^{-1/2}` gradient-smoothing (Lipschitz) rate.** For bounded
measurable `f` with `‖f‖∞ ≤ C`, the heat semigroup output is Lipschitz with the
explicit parabolic constant `C/√(πt)`:
`|Hₜf a - Hₜf b| ≤ (C/√(πt))·|a - b|`. -/
theorem heatSemigroup1D_lipschitz_sqrt_rate (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (a b : ℝ) :
    |heatSemigroup1D t f a - heatSemigroup1D t f b| ≤ (C / Real.sqrt (π * t)) * |a - b| := by
  have hsqrt_pt : (0 : ℝ) < Real.sqrt (π * t) := Real.sqrt_pos.mpr (by positivity)
  have hcoef : C * (∫ w, |w| * heatKernel1D t w) / (2 * t) = C / Real.sqrt (π * t) := by
    rw [integral_abs_mul_heatKernel1D_eq ht, prefactor_eq_inv_two_sqrt t ht]
    have h2t : (2 : ℝ) * t ≠ 0 := by positivity
    have hst : Real.sqrt (π * t) ≠ 0 := ne_of_gt hsqrt_pt
    have hsq : Real.sqrt (π * t) * Real.sqrt (π * t) = π * t :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    nlinarith [hsq]
  have hbase := abs_heatSemigroup1D_sub_self_le t ht f C hfm hfb a b
  rwa [hcoef] at hbase

/-- The smoothing rate packaged as a mathlib `LipschitzWith` instance. -/
theorem heatSemigroup1D_lipschitzWith_sqrt_rate (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hCnn : 0 ≤ C) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    LipschitzWith (Real.toNNReal (C / Real.sqrt (π * t)))
      (fun x => heatSemigroup1D t f x) := by
  have hsqrt : (0 : ℝ) < Real.sqrt (π * t) := Real.sqrt_pos.mpr (by positivity)
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact heatSemigroup1D_lipschitz_sqrt_rate t ht f C hfm hfb a b

/-! ### Second-derivative `t^{-1}` smoothing rate (C² Schauder half)

The heat kernel's second moment `∫ w²K(t,w) = 2t` yields the canonical C²
parabolic smoothing estimate `‖∂ₓₓHₜf‖∞ ≤ ‖f‖∞/t` — the second half of the
Schauder regularity scale, completing the C¹ gradient rate above. -/

/-- Gaussian second moment: `∫ x²·exp(-b x²) dx = (1/2b)·√(π/b)` (FTC on
`-(x/2b)·exp(-b x²)` + even symmetrization). -/
lemma integral_sq_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = (1 / (2 * b)) * Real.sqrt (π / b) := by
  have hb' : b ≠ 0 := ne_of_gt hb
  set G : ℝ → ℝ := fun x => -(x / (2 * b)) * Real.exp (-b * x ^ 2) with hG
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt G
        (x ^ 2 * Real.exp (-b * x ^ 2) - 1 / (2 * b) * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -b * x ^ 2) (-b * (2 * x)) x := by
      have := hasDerivAt_pow 2 x
      simpa using this.const_mul (-b)
    have h2 : HasDerivAt (fun x => Real.exp (-b * x ^ 2))
        (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    have h3 : HasDerivAt (fun x : ℝ => -(x / (2 * b))) (-(1 / (2 * b))) x := by
      have hid : HasDerivAt (fun x : ℝ => x / (2 * b)) (1 / (2 * b)) x := by
        simpa using (hasDerivAt_id x).div_const (2 * b)
      simpa using hid.neg
    have hmul := h3.mul h2
    have heqv :
        (-(1 / (2 * b))) * Real.exp (-b * x ^ 2)
          + (-(x / (2 * b))) * (Real.exp (-b * x ^ 2) * (-b * (2 * x)))
        = x ^ 2 * Real.exp (-b * x ^ 2) - 1 / (2 * b) * Real.exp (-b * x ^ 2) := by
      field_simp; ring
    rw [heqv] at hmul
    exact hmul
  have hcont : ContinuousWithinAt G (Set.Ici (0 : ℝ)) 0 :=
    (Continuous.continuousWithinAt (by rw [hG]; fun_prop))
  have hintsq : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
    simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
  have hintexp : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hintexp' : Integrable (fun x : ℝ => 1 / (2 * b) * Real.exp (-b * x ^ 2)) :=
    hintexp.const_mul _
  have hint : IntegrableOn
      (fun x => x ^ 2 * Real.exp (-b * x ^ 2) - 1 / (2 * b) * Real.exp (-b * x ^ 2))
      (Set.Ioi (0 : ℝ)) volume :=
    (hintsq.sub hintexp').integrableOn
  have hxexp : Filter.Tendsto (fun x : ℝ => x * Real.exp (-b * x ^ 2))
      Filter.atTop (nhds 0) := by
    have hlit := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb 1
    have hz : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        (Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
    have hzero := hlit.tendsto_zero_of_tendsto hz
    refine hzero.congr (fun x => ?_)
    rw [Real.rpow_one]
  have htends : Filter.Tendsto G Filter.atTop (nhds 0) := by
    have := hxexp.const_mul (-(1 / (2 * b)))
    rw [mul_zero] at this
    refine this.congr (fun x => ?_)
    rw [hG]; ring
  have hres := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htends
  have hG0 : G 0 = 0 := by rw [hG]; simp
  rw [hG0, sub_zero] at hres
  rw [integral_sub hintsq.integrableOn hintexp'.integrableOn, integral_const_mul,
    integral_gaussian_Ioi] at hres
  have hIoi : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2)
      = 1 / (2 * b) * (Real.sqrt (π / b) / 2) := by
    linarith [hres]
  have h := integral_comp_abs (f := fun t => t ^ 2 * Real.exp (-b * t ^ 2))
  simp only [sq_abs] at h
  rw [h, hIoi]
  ring

/-- The heat kernel's second moment (its variance): `∫ w²·K(t,w) dw = 2t`. -/
theorem integral_sq_mul_heatKernel1D_eq {t : ℝ} (ht : 0 < t) :
    (∫ w, w ^ 2 * heatKernel1D t w) = 2 * t := by
  have h2t : (2 * t : ℝ) ≠ 0 := by positivity
  set f : ℝ → ℝ := fun w => w * heatKernel1D t w with hf
  set f' : ℝ → ℝ := fun w =>
    heatKernel1D t w - (1 / (2 * t)) * (w ^ 2 * heatKernel1D t w) with hf'
  have hderiv : ∀ w, HasDerivAt f (f' w) w := by
    intro w
    have hid : HasDerivAt (fun w : ℝ => w) 1 w := hasDerivAt_id w
    have hK : HasDerivAt (fun w => heatKernel1D t w)
        (heatKernel1D t w * (-w / (2 * t))) w := hasDerivAt_heatKernel1D_space ht w
    have hprod := hid.mul hK
    have hval : (1 : ℝ) * heatKernel1D t w + w * (heatKernel1D t w * (-w / (2 * t)))
        = f' w := by
      simp only [hf']
      field_simp
      ring
    rw [hval] at hprod
    exact hprod
  have hf'int : Integrable f' := by
    have hK : Integrable (fun w => heatKernel1D t w) := integrable_heatKernel1D ht
    have hsq : Integrable (fun w => w ^ 2 * heatKernel1D t w) :=
      integrable_sq_mul_heatKernel1D ht
    exact hK.sub (hsq.const_mul (1 / (2 * t)))
  have hfint : Integrable f := by
    have habs := integrable_abs_mul_heatKernel1D ht
    refine habs.mono' ?_ (Filter.Eventually.of_forall (fun w => ?_))
    · exact (continuous_id.mul (continuous_heatKernel1D_space t)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, hf, abs_mul, abs_of_nonneg (heatKernel1D_nonneg ht w)]
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf'int hfint
  rw [show (∫ w, f' w)
        = (∫ w, heatKernel1D t w) - (1 / (2 * t)) * (∫ w, w ^ 2 * heatKernel1D t w) from ?_] at hzero
  · rw [integral_heatKernel1D ht] at hzero
    have : (1 / (2 * t)) * (∫ w, w ^ 2 * heatKernel1D t w) = 1 := by linarith
    field_simp at this
    linarith [this]
  · simp only [hf']
    rw [integral_sub (integrable_heatKernel1D ht)
      ((integrable_sq_mul_heatKernel1D ht).const_mul (1 / (2 * t)))]
    rw [integral_const_mul]

/-- Integrability of the shifted second-moment integrand. -/
lemma integrable_sq_mul_heatKernel1D_sub {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => (x - y) ^ 2 * heatKernel1D t (x - y)) :=
  (integrable_sq_mul_heatKernel1D ht).comp_sub_left x

/-- Pointwise triangle bound: `|w²/(4t²) - 1/(2t)| ≤ w²/(4t²) + 1/(2t)`. -/
lemma sq_sub_inv_le_add (t : ℝ) (ht : 0 < t) (w : ℝ) :
    |w ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤ w ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
  have hA : (0 : ℝ) ≤ w ^ 2 / (4 * t ^ 2) := by positivity
  have hB : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
  calc |w ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
      ≤ |w ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
    _ = w ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by rw [abs_of_nonneg hA, abs_of_nonneg hB]

/-- The integral the C² rate collapses to: `∫ K(t,w)·(w²/(4t²)+1/(2t)) dw = 1/t`. -/
lemma heatKernel1D_mul_sq_sub_inv_integral_eq {t : ℝ} (ht : 0 < t) :
    (∫ w, heatKernel1D t w * (w ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) = 1 / t := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hmain_congr : (∫ w, heatKernel1D t w * (w ^ 2 / (4 * t ^ 2) + 1 / (2 * t)))
      = (∫ w, ((1 / (4 * t ^ 2)) * (w ^ 2 * heatKernel1D t w)
          + (1 / (2 * t)) * heatKernel1D t w)) := by
    apply integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    ring
  rw [hmain_congr,
    integral_add ((integrable_sq_mul_heatKernel1D ht).const_mul (1 / (4 * t ^ 2)))
      ((integrable_heatKernel1D ht).const_mul (1 / (2 * t))),
    integral_const_mul, integral_const_mul,
    integral_sq_mul_heatKernel1D_eq ht, integral_heatKernel1D ht]
  field_simp
  ring

/-- **The C² (second-derivative) parabolic smoothing rate** `‖∂ₓₓHₜf‖∞ ≤ ‖f‖∞/t`
for bounded measurable `f`, completing the Schauder regularity scale. -/
theorem heatSemigroup1D_deriv2_abs_le_inv_t (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    |deriv (deriv (fun z => heatSemigroup1D t f z)) x| ≤ C / t := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set g : ℝ → ℝ := fun w => heatKernel1D t w * (w ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) with hg
  have hgeven : ∀ w, g (-w) = g w := by
    intro w; simp only [hg, heatKernel1D_neg]; ring
  have hcv : (∫ y, heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)))
      = ∫ w, g w := by
    have hfun : (fun y => heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)))
        = (fun y => g (y + -x)) := by
      funext y
      show heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) = g (y + -x)
      have e1 : g (x - y) = heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) :=
        rfl
      rw [← e1, ← hgeven (x - y)]
      congr 1; ring
    rw [hfun, integral_add_right_eq_self g (-x)]
  have hval : (∫ w, g w) = 1 / t := by
    have hsplit : (fun w => g w)
        = (fun w => (1 / (4 * t ^ 2)) * (w ^ 2 * heatKernel1D t w)
            + (1 / (2 * t)) * heatKernel1D t w) := by
      funext w; simp only [hg]; ring
    rw [hsplit,
      integral_add ((integrable_sq_mul_heatKernel1D ht).const_mul (1 / (4 * t ^ 2)))
        ((integrable_heatKernel1D ht).const_mul (1 / (2 * t))),
      integral_const_mul, integral_const_mul,
      integral_sq_mul_heatKernel1D_eq ht, integral_heatKernel1D ht]
    field_simp
    ring
  rw [deriv2_heatSemigroup1D_eq_integral ht x hfm hfb]
  have hFint : Integrable
      (fun y => heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y) :=
    integrable_deriv2_heatKernel1D_space_sub_mul ht x hfm hfb
  set Gbase : ℝ → ℝ := fun y => heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
    with hGbase
  have hGbaseint : Integrable Gbase := by
    have hsq : Integrable (fun y => (x - y) ^ 2 * heatKernel1D t (x - y)) :=
      (integrable_sq_mul_heatKernel1D ht).comp_sub_left x
    have hK : Integrable (fun y => heatKernel1D t (x - y)) := integrable_heatKernel1D_sub ht x
    have hcomb := (hsq.const_mul (1 / (4 * t ^ 2))).add (hK.const_mul (1 / (2 * t)))
    refine hcomb.congr ?_
    filter_upwards with y
    simp only [Pi.add_apply, hGbase]; ring
  have hGint : Integrable (fun y => Gbase y * C) := hGbaseint.mul_const C
  calc |∫ y, heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y|
      ≤ ∫ y, ‖heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, Gbase y * C := by
        refine integral_mono hFint.norm hGint (fun y => ?_)
        have hKnn : 0 ≤ heatKernel1D t (x - y) := heatKernel1D_nonneg ht (x - y)
        have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
        have hcoefabs :
            |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|
              ≤ (x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
          rw [abs_le]
          constructor
          · have : (0 : ℝ) ≤ (x - y) ^ 2 / (4 * t ^ 2) := by positivity
            linarith
          · have : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
            linarith
        have hnorm :
            ‖heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y‖
              = heatKernel1D t (x - y) * |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * |f y| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKnn]
        rw [hnorm, hGbase]
        have hstep1 :
            heatKernel1D t (x - y) * |((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| * |f y|
              ≤ heatKernel1D t (x - y) * ((x - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) * C := by
          apply mul_le_mul _ hfa (abs_nonneg _)
            (mul_nonneg hKnn (by positivity))
          exact mul_le_mul_of_nonneg_left hcoefabs hKnn
        exact hstep1
    _ = C / t := by
        rw [integral_mul_const, hcv, hval]
        field_simp

/-- Additivity of the Duhamel convolution in the source term (with integrability
of the time-slices). -/
lemma duhamelKernel1D_add (t : ℝ) (ht : 0 < t) (g h : ℝ → ℝ → ℝ) (Cg Ch : ℝ)
    (hgm : ∀ s, AEStronglyMeasurable (g s)) (hgb : ∀ s y, ‖g s y‖ ≤ Cg)
    (hhm : ∀ s, AEStronglyMeasurable (h s)) (hhb : ∀ s y, ‖h s y‖ ≤ Ch)
    (x : ℝ)
    (hgI : MeasureTheory.IntegrableOn
      (fun s => heatSemigroup1D (t - s) (g s) x) (Set.Ioo 0 t))
    (hhI : MeasureTheory.IntegrableOn
      (fun s => heatSemigroup1D (t - s) (h s) x) (Set.Ioo 0 t)) :
    duhamelKernel1D t (fun s y => g s y + h s y) x
      = duhamelKernel1D t g x + duhamelKernel1D t h x := by
  unfold duhamelKernel1D
  have hcong :
      (∫ s in Set.Ioo 0 t, heatSemigroup1D (t - s) (fun y => g s y + h s y) x)
        = ∫ s in Set.Ioo 0 t,
            (heatSemigroup1D (t - s) (g s) x + heatSemigroup1D (t - s) (h s) x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    exact heatSemigroup1D_add hts x (hgm s)
      (fun y => le_trans (hgb s y) (le_max_left Cg Ch)) (hhm s)
      (fun y => le_trans (hhb s y) (le_max_right Cg Ch))
  rw [hcong, MeasureTheory.integral_add hgI hhI]

/-- Scalar homogeneity of the Duhamel convolution. -/
lemma duhamelKernel1D_smul (t : ℝ) (c : ℝ) (g : ℝ → ℝ → ℝ) (x : ℝ) :
    duhamelKernel1D t (fun s y => c * g s y) x = c * duhamelKernel1D t g x := by
  unfold duhamelKernel1D
  simp_rw [heatSemigroup1D_smul]
  rw [integral_const_mul]

/-! ### Frozen-coefficient parametrix

The fundamental solution of the constant-coefficient diffusion `∂ₜu = a·∂ₓₓu`
(`a > 0`) is `Gₐ(t,x) = K(a·t, x)`. Its entire theory — mass, the diffusion
equation `∂ₜGₐ = a·∂ₓₓGₐ`, the semigroup, and the inherited C¹/C² smoothing rates
— follows from the standard heat kernel by the time-rescaling `t ↦ a·t`. This is
the parametrix that frozen-coefficient perturbation builds variable-coefficient
solvability on. -/

/-- The frozen-coefficient heat kernel `Gₐ(t,x) = K(a·t, x)`, fundamental solution
of `∂ₜu = a·∂ₓₓu`. -/
noncomputable def frozenHeatKernel1D (a t x : ℝ) : ℝ := heatKernel1D (a * t) x

lemma frozenHeatKernel1D_apply (a t x : ℝ) :
    frozenHeatKernel1D a t x = heatKernel1D (a * t) x := rfl

lemma frozenHeatKernel1D_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    0 < frozenHeatKernel1D a t x := by
  rw [frozenHeatKernel1D_apply]; exact heatKernel1D_pos (mul_pos ha ht) x

lemma frozenHeatKernel1D_nonneg {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    0 ≤ frozenHeatKernel1D a t x := (frozenHeatKernel1D_pos ha ht x).le

/-- The frozen kernel has unit mass. -/
lemma integral_frozenHeatKernel1D {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ∫ x, frozenHeatKernel1D a t x = 1 := by
  simp only [frozenHeatKernel1D_apply]; exact integral_heatKernel1D (mul_pos ha ht)

lemma integrable_frozenHeatKernel1D {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Integrable (fun x => frozenHeatKernel1D a t x) := by
  simp only [frozenHeatKernel1D_apply]; exact integrable_heatKernel1D (mul_pos ha ht)

/-- Second spatial derivative of the frozen kernel. -/
lemma hasDerivAt_frozenHeatKernel1D_space_second {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (fun z => frozenHeatKernel1D a t z))
      (heatKernel1D (a * t) x * (x ^ 2 / (4 * (a * t) ^ 2) - 1 / (2 * (a * t)))) x := by
  have hfun : (fun z => frozenHeatKernel1D a t z) = (fun z => heatKernel1D (a * t) z) := by
    funext z; rw [frozenHeatKernel1D_apply]
  have hderiv : (deriv fun z => heatKernel1D (a * t) z)
      = fun y => heatKernel1D (a * t) y * (-y / (2 * (a * t))) := by
    funext y
    exact (hasDerivAt_heatKernel1D_space (mul_pos ha ht) y).deriv
  rw [hfun, hderiv]
  exact hasDerivAt_heatKernel1D_space_second (mul_pos ha ht) x

/-- Time derivative of the frozen kernel: the chain rule picks up the coefficient
`a`, encoding `∂ₜGₐ = a·∂ₓₓGₐ`. -/
lemma hasDerivAt_frozenHeatKernel1D_time {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => frozenHeatKernel1D a s x)
      (a * (heatKernel1D (a * t) x * (x ^ 2 / (4 * (a * t) ^ 2) - 1 / (2 * (a * t))))) t := by
  have hinner : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have houter := hasDerivAt_heatKernel1D_time (mul_pos ha ht) x
  have hcomp := houter.comp t hinner
  simpa [frozenHeatKernel1D, Function.comp, mul_comm] using hcomp

/-- **The frozen kernel solves the `a`-diffusion equation** `∂ₜGₐ = a·∂ₓₓGₐ`. -/
lemma frozenHeatKernel1D_heatEquation {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    deriv (fun s => frozenHeatKernel1D a s x) t
      = a * deriv (deriv (fun z => frozenHeatKernel1D a t z)) x := by
  rw [(hasDerivAt_frozenHeatKernel1D_time ha ht x).deriv,
    (hasDerivAt_frozenHeatKernel1D_space_second ha ht x).deriv]

/-- The frozen-coefficient semigroup `Gₐ,ₜf = H_{a·t}f`. -/
noncomputable def frozenHeatSemigroup1D (a t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  heatSemigroup1D (a * t) f x

lemma frozenHeatSemigroup1D_apply (a t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    frozenHeatSemigroup1D a t f x = heatSemigroup1D (a * t) f x := rfl

lemma frozenHeatSemigroup1D_const {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (c x : ℝ) :
    frozenHeatSemigroup1D a t (fun _ => c) x = c := by
  rw [frozenHeatSemigroup1D_apply]; exact heatSemigroup1D_const (mul_pos ha ht) c x

lemma frozenHeatSemigroup1D_nonneg {a t : ℝ} (ha : 0 < a) (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : ℝ) : 0 ≤ frozenHeatSemigroup1D a t f x := by
  rw [frozenHeatSemigroup1D_apply]
  exact heatSemigroup1D_nonneg_of_nonneg (mul_pos ha ht) hf x

/-- The frozen semigroup inherits the C¹ gradient-smoothing rate (`a`-rescaled). -/
lemma frozenHeatSemigroup1D_lipschitz_rate {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : ℝ → ℝ) (C : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (p q : ℝ) :
    |frozenHeatSemigroup1D a t f p - frozenHeatSemigroup1D a t f q|
      ≤ (C / Real.sqrt (π * (a * t))) * |p - q| := by
  rw [frozenHeatSemigroup1D_apply, frozenHeatSemigroup1D_apply]
  exact heatSemigroup1D_lipschitz_sqrt_rate (a * t) (mul_pos ha ht) f C hfm hfb p q

/-- The frozen semigroup inherits the C² (second-derivative) smoothing rate. -/
lemma frozenHeatSemigroup1D_deriv2_rate {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : ℝ → ℝ) (C : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    |deriv (deriv (fun z => frozenHeatSemigroup1D a t f z)) x| ≤ C / (a * t) := by
  have hfe : (fun z => frozenHeatSemigroup1D a t f z) = (fun z => heatSemigroup1D (a * t) f z) := by
    funext z; rw [frozenHeatSemigroup1D_apply]
  rw [hfe]
  exact heatSemigroup1D_deriv2_abs_le_inv_t (a * t) (mul_pos ha ht) f C hfm hfb x

/-! ### Hölder-gain estimates (the variable-coefficient iteration's load-bearing layer)

The C² smoothing rate `‖∂ₓₓHₜf‖∞ ≤ C/t` has a non-integrable time singularity, so
the variable-coefficient Duhamel iteration cannot run in C⁰. It runs instead in
Hölder C^{0,α}, where the gain rate is `τ^{-1+α/2}` — time-integrable since
`∫₀ᵗ s^{-1+α/2} ds = t^{α/2}/(α/2) < ∞`. These lemmas build that layer:
interpolation (sup + Lipschitz ⇒ Hölder), the singular-kernel integrability, and
the semigroup Hölder-seminorm bounds. -/

/-- Interpolation core: `min p q ≤ p^{1-α}·q^α` for `p,q ≥ 0`, `α ∈ [0,1]`. -/
lemma min_le_rpow_mul_rpow {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : min p q ≤ p ^ (1 - α) * q ^ α := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq]
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · subst hp0
      exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hq _)
    · have key : p ^ (1 - α) * p ^ α = p := by
        rw [← Real.rpow_add hp0]
        norm_num
      calc p = p ^ (1 - α) * p ^ α := key.symm
        _ ≤ p ^ (1 - α) * q ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp hpq hα0)
              (Real.rpow_nonneg hp _)
  · rw [min_eq_right hqp]
    rcases eq_or_lt_of_le hq with hq0 | hq0
    · subst hq0
      exact mul_nonneg (Real.rpow_nonneg hp _) (Real.rpow_nonneg le_rfl _)
    · have key : q ^ (1 - α) * q ^ α = q := by
        rw [← Real.rpow_add hq0]
        norm_num
      calc q = q ^ (1 - α) * q ^ α := key.symm
        _ ≤ p ^ (1 - α) * q ^ α :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hq hqp (by linarith))
              (Real.rpow_nonneg hq _)

/-- Exponent facts for the singular Duhamel weight when `0 < α < 2`. -/
lemma rpow_neg_one_add_half_facts {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    (-1 : ℝ) < -1 + α / 2 ∧ -1 + α / 2 < 0 ∧ 0 < α / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Time-integrability of the singular Duhamel kernel** in closed form:
`∫₀ᵗ s^{-1+α/2} ds = t^{α/2}/(α/2) < ∞` for `0 < α < 2`. This is what makes the
Hölder iteration converge. -/
lemma integral_Ioo_rpow_singular {t α : ℝ} (ht : 0 < t) (hα : 0 < α) (hα2 : α < 2) :
    ∫ s in Set.Ioo 0 t, s ^ (-1 + α / 2) = t ^ (α / 2) / (α / 2) := by
  have hr : (-1 : ℝ) < -1 + α / 2 := by linarith
  have hpos : (0 : ℝ) < α / 2 := by linarith
  have hconv : ∫ s in Set.Ioo (0 : ℝ) t, s ^ (-1 + α / 2)
      = ∫ s in Set.Ioc (0 : ℝ) t, s ^ (-1 + α / 2) :=
    MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [hconv, ← intervalIntegral.integral_of_le ht.le, integral_rpow (Or.inl hr)]
  have he : (-1 + α / 2) + 1 = α / 2 := by ring
  rw [he, Real.zero_rpow (ne_of_gt hpos), sub_zero]

/-- The Duhamel time-weight `s ↦ (t-s)^{-1+α/2}` is integrable on `(0,t)`. -/
lemma duhamel_time_weight_integrable {t α : ℝ} (ht : 0 < t) (hα : 0 < α) (hα2 : α < 2) :
    MeasureTheory.IntegrableOn (fun s => (t - s) ^ (-1 + α / 2)) (Set.Ioo 0 t) := by
  have hr : (-1 : ℝ) < -1 + α / 2 := by linarith
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-1 + α / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hcomp := hbase.comp_sub_left t
  simp only [sub_zero, sub_self] at hcomp
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hcomp.symm

/-- Monotonicity of the accumulated time-weight `t^{α/2}/(α/2)` on `[0,T]`. -/
lemma rpow_half_le_of_le {t T α : ℝ} (hα : 0 < α) (ht : 0 < t) (htT : t ≤ T) :
    t ^ (α / 2) / (α / 2) ≤ T ^ (α / 2) / (α / 2) := by
  gcongr

/-- **The heat-semigroup Hölder-seminorm bound** by interpolating the sup
contraction and the C¹ Lipschitz rate:
`|Hₜf a - Hₜf b| ≤ (2C)^{1-α}·(C/√(πt))^α·|a-b|^α`. -/
lemma heatSemigroup1D_holder_seminorm_bound (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a b : ℝ) :
    |heatSemigroup1D t f a - heatSemigroup1D t f b|
      ≤ (2 * C) ^ (1 - α) * (C / Real.sqrt (π * t)) ^ α * |a - b| ^ α := by
  set D := |heatSemigroup1D t f a - heatSemigroup1D t f b| with hD
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  have hfabs : ∀ y, |f y| ≤ C := fun y => by simpa [Real.norm_eq_abs] using hfb y
  have hsupa : |heatSemigroup1D t f a| ≤ C := abs_heatSemigroup1D_le ht a hfabs
  have hsupb : |heatSemigroup1D t f b| ≤ C := abs_heatSemigroup1D_le ht b hfabs
  have hsup : D ≤ 2 * C := by
    calc D ≤ |heatSemigroup1D t f a| + |heatSemigroup1D t f b| := abs_sub _ _
      _ ≤ C + C := add_le_add hsupa hsupb
      _ = 2 * C := by ring
  have hlip : D ≤ (C / Real.sqrt (π * t)) * |a - b| :=
    heatSemigroup1D_lipschitz_sqrt_rate t ht f C hfm hfb a b
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (π * t) := Real.sqrt_pos.mpr (by positivity)
  have hp_nn : (0 : ℝ) ≤ 2 * C := by positivity
  have hcoef_nn : (0 : ℝ) ≤ C / Real.sqrt (π * t) := by positivity
  have habs_nn : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  have hq_nn : (0 : ℝ) ≤ (C / Real.sqrt (π * t)) * |a - b| := mul_nonneg hcoef_nn habs_nn
  have hDmin : D ≤ min (2 * C) ((C / Real.sqrt (π * t)) * |a - b|) := le_min hsup hlip
  have hstep := min_le_rpow_mul_rpow hp_nn hq_nn hα0 hα1
  have hsplitq : ((C / Real.sqrt (π * t)) * |a - b|) ^ α
      = (C / Real.sqrt (π * t)) ^ α * |a - b| ^ α :=
    Real.mul_rpow hcoef_nn habs_nn
  calc D ≤ min (2 * C) ((C / Real.sqrt (π * t)) * |a - b|) := hDmin
    _ ≤ (2 * C) ^ (1 - α) * ((C / Real.sqrt (π * t)) * |a - b|) ^ α := hstep
    _ = (2 * C) ^ (1 - α) * ((C / Real.sqrt (π * t)) ^ α * |a - b| ^ α) := by rw [hsplitq]
    _ = (2 * C) ^ (1 - α) * (C / Real.sqrt (π * t)) ^ α * |a - b| ^ α := by ring

/-- Data-stability of the semigroup in sup norm: `|Hₜf x - Hₜg x| ≤ ‖f-g‖∞`. -/
lemma heatSemigroup1D_sub_holder (t : ℝ) (ht : 0 < t) (f g : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hgm : AEStronglyMeasurable g)
    (hfgb : ∀ y, ‖f y - g y‖ ≤ C) (x : ℝ) :
    |heatSemigroup1D t f x - heatSemigroup1D t g x| ≤ C := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hfgb 0)
  have hfgb' : ∀ y, |f y - g y| ≤ C := fun y => by
    simpa [Real.norm_eq_abs] using hfgb y
  have hd : Integrable (fun y : ℝ => heatKernel1D t (x - y) * (f y - g y)) :=
    integrable_heatKernel1D_sub_mul ht x (hfm.sub hgm) hfgb
  by_cases hF : Integrable (fun y : ℝ => heatKernel1D t (x - y) * f y)
  · have hG : Integrable (fun y : ℝ => heatKernel1D t (x - y) * g y) := by
      have h2 := hF.sub hd
      refine h2.congr ?_
      filter_upwards with y
      simp only [Pi.sub_apply]
      ring
    have key : heatSemigroup1D t f x - heatSemigroup1D t g x
        = heatSemigroup1D t (fun y => f y - g y) x := by
      simp only [heatSemigroup1D]
      rw [← integral_sub hF hG]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [key]
    exact abs_heatSemigroup1D_le ht x hfgb'
  · have hGni : ¬ Integrable (fun y : ℝ => heatKernel1D t (x - y) * g y) := by
      intro hG
      apply hF
      have h3 := hG.add hd
      refine h3.congr ?_
      filter_upwards with y
      simp only [Pi.add_apply]
      ring
    have e1 : heatSemigroup1D t f x = 0 := by
      simp only [heatSemigroup1D]; exact integral_undef hF
    have e2 : heatSemigroup1D t g x = 0 := by
      simp only [heatSemigroup1D]; exact integral_undef hGni
    rw [e1, e2]
    simpa using hCnonneg

/-- The frozen-coefficient semigroup inherits the Hölder-seminorm bound. -/
lemma frozenHeatSemigroup1D_holder_seminorm_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (f : ℝ → ℝ) (C : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (p q : ℝ) :
    |frozenHeatSemigroup1D a t f p - frozenHeatSemigroup1D a t f q|
      ≤ (2 * C) ^ (1 - α) * (C / Real.sqrt (π * (a * t))) ^ α * |p - q| ^ α := by
  rw [frozenHeatSemigroup1D_apply, frozenHeatSemigroup1D_apply]
  exact heatSemigroup1D_holder_seminorm_bound (a * t) (mul_pos ha ht) f C hfm hfb hα0 hα1 p q

/-! ### Duhamel contraction estimates

The analytic inequalities that make the variable-coefficient Duhamel map a
contraction for small time: the perturbation-operator sup bound, the Duhamel-term
sup/Hölder/data-stability estimates, the short-time smallness factor, and the
geometric-decay iterate bound (Banach fixed-point engine). These assemble
short-time existence for the scalar variable-coefficient parabolic equation, the
1D model of Ricci–DeTurck. -/

/-- A function bounded in sup by `M`. -/
def BoundedBy (u : ℝ → ℝ) (M : ℝ) : Prop := ∀ x, |u x| ≤ M

lemma BoundedBy.nonneg {u : ℝ → ℝ} {M : ℝ} (h : BoundedBy u M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (h 0)

lemma BoundedBy.add {u v : ℝ → ℝ} {M N : ℝ} (hu : BoundedBy u M) (hv : BoundedBy v N) :
    BoundedBy (fun x => u x + v x) (M + N) := by
  intro x
  calc |u x + v x| ≤ |u x| + |v x| := abs_add_le _ _
    _ ≤ M + N := add_le_add (hu x) (hv x)

lemma BoundedBy.smul {u : ℝ → ℝ} {M : ℝ} (c : ℝ) (hu : BoundedBy u M) :
    BoundedBy (fun x => c * u x) (|c| * M) := by
  intro x
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hu x) (abs_nonneg _)

/-- The perturbation operator `(a(x)-a₀)·v(x)` is bounded in sup by `M·V` where
`M` bounds the coefficient oscillation and `V` bounds `v`. -/
lemma perturbation_op_sup_bound (acoef : ℝ → ℝ) (a0 : ℝ) (M : ℝ) (v : ℝ → ℝ) (V : ℝ)
    (haM : ∀ x, |acoef x - a0| ≤ M) (hvV : ∀ x, |v x| ≤ V) (x : ℝ) :
    |(acoef x - a0) * v x| ≤ M * V := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (haM x)
  rw [abs_mul]
  exact mul_le_mul (haM x) (hvV x) (abs_nonneg _) hMnn

/-- The perturbation applied to the frozen second derivative:
`|(a(x)-a₀)·∂ₓₓ(Gₐ₀f)(x)| ≤ M·C/(a₀·τ)`. -/
lemma frozen_perturbation_deriv2_bound {a0 : ℝ} (ha0 : 0 < a0) {τ : ℝ} (hτ : 0 < τ)
    (acoef : ℝ → ℝ) (M : ℝ) (haM : ∀ x, |acoef x - a0| ≤ M)
    (f : ℝ → ℝ) (C : ℝ) (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    |(acoef x - a0) * deriv (deriv (fun z => frozenHeatSemigroup1D a0 τ f z)) x|
      ≤ M * (C / (a0 * τ)) := by
  rw [abs_mul]
  exact mul_le_mul (haM x) (frozenHeatSemigroup1D_deriv2_rate ha0 hτ f C hfm hfb x)
    (abs_nonneg _) (le_trans (abs_nonneg _) (haM x))

/-- **Duhamel-term sup bound**: `|∫₀ᵗ H_{t-s}(g s) x ds| ≤ B·t` when `|g s y| ≤ B`. -/
lemma duhamel_term_sup_bound (t : ℝ) (ht : 0 < t) (g : ℝ → ℝ → ℝ) (B : ℝ) (x : ℝ)
    (hgm : ∀ s, AEStronglyMeasurable (g s)) (hB : 0 ≤ B)
    (hgb : ∀ s y, |g s y| ≤ B)
    (hint : MeasureTheory.IntegrableOn (fun s => heatSemigroup1D (t - s) (g s) x) (Set.Ioo 0 t)) :
    |duhamelKernel1D t g x| ≤ B * t := by
  unfold duhamelKernel1D
  have hmeas : (volume (Set.Ioo (0 : ℝ) t)) < ∞ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hbound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖heatSemigroup1D (t - s) (g s) x‖ ≤ B := by
    intro s hs
    have : |heatSemigroup1D (t - s) (g s) x| ≤ B :=
      abs_heatSemigroup1D_le (sub_pos.mpr hs.2) x (fun y => hgb s y)
    simpa [Real.norm_eq_abs] using this
  have key := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmeas hbound
  rw [Real.norm_eq_abs] at key
  have hvol : (volume.real (Set.Ioo (0 : ℝ) t)) = t := by
    rw [Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal ht.le]
  rw [hvol] at key
  exact key

/-- **Duhamel-term data stability** (the contraction core): if the two sources
differ by at most `B` in sup, their Duhamel terms differ by at most `B·t`. -/
lemma duhamel_term_data_stability (t : ℝ) (ht : 0 < t) (g h : ℝ → ℝ → ℝ) (B : ℝ) (x : ℝ)
    (hgm : ∀ s, AEStronglyMeasurable (g s)) (hhm : ∀ s, AEStronglyMeasurable (h s))
    (hB : 0 ≤ B) (hgh : ∀ s y, |g s y - h s y| ≤ B)
    (hintg : MeasureTheory.IntegrableOn (fun s => heatSemigroup1D (t - s) (g s) x) (Set.Ioo 0 t))
    (hinth : MeasureTheory.IntegrableOn (fun s => heatSemigroup1D (t - s) (h s) x) (Set.Ioo 0 t)) :
    |duhamelKernel1D t g x - duhamelKernel1D t h x| ≤ B * t := by
  unfold duhamelKernel1D
  rw [← integral_sub hintg hinth]
  have hper : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖heatSemigroup1D (t - s) (g s) x - heatSemigroup1D (t - s) (h s) x‖ ≤ B := by
    intro s hs
    rw [Real.norm_eq_abs]
    exact heatSemigroup1D_sub_holder (t - s) (sub_pos.mpr hs.2) (g s) (h s) B
      (hgm s) (hhm s) (fun y => by rw [Real.norm_eq_abs]; exact hgh s y) x
  have hmeas : (volume (Set.Ioo (0 : ℝ) t)).toReal = t := by
    rw [Real.volume_Ioo]; simp [ENNReal.toReal_ofReal ht.le]
  have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    hper
  rw [Real.norm_eq_abs, Measure.real, hmeas] at hbound
  exact hbound

/-- Monotonicity of the accumulated contraction factor on `[0,T]`. -/
lemma duhamel_contraction_factor_small {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hT : 0 < T) :
    t ^ (α / 2) / (α / 2) ≤ T ^ (α / 2) / (α / 2) :=
  rpow_half_le_of_le hα ht htT

/-- The contraction factor drops below `1` for small enough `T`. -/
lemma duhamel_factor_lt_one_of_small {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {T : ℝ}
    (hT : 0 < T) (hTbound : T ^ (α / 2) < α / 2) :
    T ^ (α / 2) / (α / 2) < 1 := by
  rw [div_lt_one (by linarith)]
  exact hTbound

/-- **Duhamel-term Hölder bound** via the singular time-weight: the Hölder
seminorm of the Duhamel term is controlled by the (finite) time-weight integral. -/
lemma duhamel_term_holder_via_weight (t : ℝ) (ht : 0 < t) (g : ℝ → ℝ → ℝ) (B : ℝ)
    (hgm : ∀ s, AEStronglyMeasurable (g s)) (hB : 0 ≤ B) (hgb : ∀ s y, |g s y| ≤ B)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hint : ∀ a b : ℝ, MeasureTheory.IntegrableOn
      (fun s => heatSemigroup1D (t - s) (g s) a - heatSemigroup1D (t - s) (g s) b) (Set.Ioo 0 t))
    (a b : ℝ) :
    |duhamelKernel1D t g a - duhamelKernel1D t g b|
      ≤ (∫ s in Set.Ioo 0 t, (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α) * |a - b| ^ α := by
  have hweight : MeasureTheory.IntegrableOn (fun s => (t - s) ^ (-(α / 2))) (Set.Ioo 0 t) := by
    have hr : (-1 : ℝ) < -(α / 2) := by linarith
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(α / 2))) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' hr
    have hcomp := hbase.comp_sub_left t
    simp only [sub_zero, sub_self] at hcomp
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hcomp.symm
  have hKeq : Set.EqOn
      (fun s => (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α)
      (fun s => ((2 * B) ^ (1 - α) * (B / Real.sqrt π) ^ α) * (t - s) ^ (-(α / 2)))
      (Set.Ioo 0 t) := by
    intro s hs
    have hu : 0 < t - s := sub_pos.mpr hs.2
    have hupi : Real.sqrt (π * (t - s)) = Real.sqrt π * Real.sqrt (t - s) :=
      Real.sqrt_mul Real.pi_nonneg _
    have hsq : (Real.sqrt (t - s)) ^ α = (t - s) ^ (α / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
      congr 1; ring
    have hkey : (B / Real.sqrt (π * (t - s))) ^ α
        = (B / Real.sqrt π) ^ α * (t - s) ^ (-(α / 2)) := by
      rw [hupi, Real.div_rpow hB (by positivity), Real.div_rpow hB (Real.sqrt_nonneg _),
        Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), hsq, Real.rpow_neg hu.le]
      field_simp
    show (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α
        = ((2 * B) ^ (1 - α) * (B / Real.sqrt π) ^ α) * (t - s) ^ (-(α / 2))
    rw [hkey]; ring
  have hKint : MeasureTheory.IntegrableOn
      (fun s => (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α) (Set.Ioo 0 t) :=
    MeasureTheory.IntegrableOn.congr_fun
      (hweight.const_mul ((2 * B) ^ (1 - α) * (B / Real.sqrt π) ^ α)) hKeq.symm measurableSet_Ioo
  have hRHSint : MeasureTheory.IntegrableOn
      (fun s => (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α * |a - b| ^ α) (Set.Ioo 0 t) :=
    hKint.mul_const (|a - b| ^ α)
  by_cases hAi : MeasureTheory.IntegrableOn
      (fun s => heatSemigroup1D (t - s) (g s) a) (Set.Ioo 0 t)
  · have hBi : MeasureTheory.IntegrableOn
        (fun s => heatSemigroup1D (t - s) (g s) b) (Set.Ioo 0 t) :=
      (hAi.sub (hint a b)).congr (Filter.Eventually.of_forall (fun s => by
        simp only [Pi.sub_apply]; ring))
    have hdiff : duhamelKernel1D t g a - duhamelKernel1D t g b
        = ∫ s in Set.Ioo 0 t,
            (heatSemigroup1D (t - s) (g s) a - heatSemigroup1D (t - s) (g s) b) := by
      rw [duhamelKernel1D, duhamelKernel1D, ← integral_sub hAi hBi]
    rw [hdiff, ← Real.norm_eq_abs]
    calc ‖∫ s in Set.Ioo 0 t,
            (heatSemigroup1D (t - s) (g s) a - heatSemigroup1D (t - s) (g s) b)‖
        ≤ ∫ s in Set.Ioo 0 t,
            ‖heatSemigroup1D (t - s) (g s) a - heatSemigroup1D (t - s) (g s) b‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ s in Set.Ioo 0 t,
            |heatSemigroup1D (t - s) (g s) a - heatSemigroup1D (t - s) (g s) b| := by
          simp_rw [Real.norm_eq_abs]
      _ ≤ ∫ s in Set.Ioo 0 t,
            (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α * |a - b| ^ α :=
          setIntegral_mono_on ((hint a b).abs) hRHSint measurableSet_Ioo
            (fun s hs => heatSemigroup1D_holder_seminorm_bound (t - s) (sub_pos.mpr hs.2)
              (g s) B (hgm s) (fun y => by rw [Real.norm_eq_abs]; exact hgb s y) hα0 hα1 a b)
      _ = (∫ s in Set.Ioo 0 t, (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α) * |a - b| ^ α :=
          MeasureTheory.integral_mul_const _ _
  · have hBi : ¬ MeasureTheory.IntegrableOn
        (fun s => heatSemigroup1D (t - s) (g s) b) (Set.Ioo 0 t) := by
      intro hBi
      exact hAi ((hBi.add (hint a b)).congr (Filter.Eventually.of_forall (fun s => by
        simp only [Pi.add_apply]; ring)))
    have hA0 : duhamelKernel1D t g a = 0 := by
      rw [duhamelKernel1D]; exact integral_undef hAi
    have hB0 : duhamelKernel1D t g b = 0 := by
      rw [duhamelKernel1D]; exact integral_undef hBi
    rw [hA0, hB0, sub_zero, abs_zero]
    have hInt0 : 0 ≤ ∫ s in Set.Ioo 0 t, (2 * B) ^ (1 - α) * (B / Real.sqrt (π * (t - s))) ^ α :=
      setIntegral_nonneg measurableSet_Ioo (fun s _ =>
        mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hB) _)
          (Real.rpow_nonneg (div_nonneg hB (Real.sqrt_nonneg _)) _))
    exact mul_nonneg hInt0 (Real.rpow_nonneg (abs_nonneg _) _)

/-- **Geometric-decay iterate bound** (Banach fixed-point engine): if `d` shrinks
by a factor `θ < 1` at each step, then `d n ≤ θⁿ·d₀`. -/
lemma contraction_iterate_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (d0 : ℝ) (hd0 : 0 ≤ d0)
    (n : ℕ) (d : ℕ → ℝ) (hd : ∀ k, 0 ≤ d k) (h0 : d 0 ≤ d0)
    (hstep : ∀ k, d (k + 1) ≤ θ * d k) :
    d n ≤ θ ^ n * d0 := by
  induction n with
  | zero => simpa using h0
  | succ m ih =>
    calc d (m + 1) ≤ θ * d m := hstep m
      _ ≤ θ * (θ ^ m * d0) := mul_le_mul_of_nonneg_left ih hθ0
      _ = θ ^ (m + 1) * d0 := by rw [pow_succ]; ring

/-! ### Picard fixed-point assembly (abstract short-time existence)

The Duhamel contraction estimates assemble into Banach fixed-point convergence:
a real sequence whose consecutive distances contract by `θ < 1` is Cauchy, hence
converges (ℝ complete). Applied to the Picard iteration `uₙ₊₁ = baseline +
Duhamel(perturbation of uₙ)`, with per-step factor `B·T < 1` for small `T`, this
gives short-time existence for the scalar variable-coefficient parabolic model. -/

/-- A real sequence with geometric consecutive-distance decay is Cauchy. -/
lemma cauchySeq_of_geometric_real (f : ℕ → ℝ) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n, |f n - f (n + 1)| ≤ C * r ^ n) : CauchySeq f := by
  apply cauchySeq_of_le_geometric r C hr1
  intro n
  rw [Real.dist_eq]
  exact hstep n

/-- A real Cauchy sequence converges (`ℝ` is complete). -/
lemma cauchySeq_tendsto_real (f : ℕ → ℝ) (hf : CauchySeq f) :
    ∃ a : ℝ, Filter.Tendsto f Filter.atTop (nhds a) :=
  cauchySeq_tendsto_of_complete hf

/-- One-step contraction ⇒ geometric decay of consecutive distances. -/
lemma iterate_dist_geometric_of_contraction {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (f : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h0 : |f 0 - f 1| ≤ D)
    (hcontract : ∀ n, |f (n + 1) - f (n + 2)| ≤ θ * |f n - f (n + 1)|) :
    ∀ n, |f n - f (n + 1)| ≤ D * θ ^ n := by
  intro n
  have key := contraction_iterate_bound hθ0 hθ1 D hD n
    (fun n => |f n - f (n + 1)|) (fun k => abs_nonneg _) h0 hcontract
  rw [mul_comm] at key
  exact key

/-- A real sequence whose consecutive distances contract by `θ < 1` is Cauchy. -/
lemma cauchySeq_of_contraction_real {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (f : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h0 : |f 0 - f 1| ≤ D)
    (hcontract : ∀ n, |f (n + 1) - f (n + 2)| ≤ θ * |f n - f (n + 1)|) :
    CauchySeq f := by
  set d : ℕ → ℝ := fun k => |f k - f (k + 1)| with hd_def
  have hd_nonneg : ∀ k, 0 ≤ d k := fun k => abs_nonneg _
  have hstep : ∀ k, d (k + 1) ≤ θ * d k := by
    intro k
    simpa [hd_def] using hcontract k
  have hgeo : ∀ n, d n ≤ θ ^ n * D :=
    fun n => contraction_iterate_bound hθ0 hθ1 D hD n d hd_nonneg h0 hstep
  refine cauchySeq_of_le_geometric θ D hθ1 ?_
  intro n
  rw [Real.dist_eq]
  calc |f n - f (n + 1)| = d n := by rw [hd_def]
    _ ≤ θ ^ n * D := hgeo n
    _ = D * θ ^ n := by rw [mul_comm]

/-- The geometric error tends to `0`. -/
lemma tendsto_geometric_error {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (D : ℝ) :
    Filter.Tendsto (fun n => D * θ ^ n) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
  have := h.const_mul D
  simpa using this

/-- The Picard update value `baseline + Duhamel(g)` at a point. -/
noncomputable def picardValue (baseline : ℝ) (t : ℝ) (g : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  baseline + duhamelKernel1D t g x

lemma picardValue_sub (baseline : ℝ) (t : ℝ) (g h : ℝ → ℝ → ℝ) (x : ℝ) :
    picardValue baseline t g x - picardValue baseline t h x
      = duhamelKernel1D t g x - duhamelKernel1D t h x := by
  unfold picardValue; ring

/-- The Picard update is a contraction with factor `B·t` in the source difference. -/
lemma picardValue_contraction (baseline : ℝ) (t : ℝ) (ht : 0 < t) (g h : ℝ → ℝ → ℝ) (B : ℝ)
    (x : ℝ)
    (hgm : ∀ s, AEStronglyMeasurable (g s)) (hhm : ∀ s, AEStronglyMeasurable (h s))
    (hB : 0 ≤ B) (hgh : ∀ s y, |g s y - h s y| ≤ B)
    (hintg : MeasureTheory.IntegrableOn (fun s => heatSemigroup1D (t - s) (g s) x) (Set.Ioo 0 t))
    (hinth : MeasureTheory.IntegrableOn (fun s => heatSemigroup1D (t - s) (h s) x) (Set.Ioo 0 t)) :
    |picardValue baseline t g x - picardValue baseline t h x| ≤ B * t := by
  rw [picardValue_sub]
  exact duhamel_term_data_stability t ht g h B x hgm hhm hB hgh hintg hinth

/-- The per-step factor `B·T` is a genuine contraction factor (`∈ [0,1)`) for
`T < 1/B`. -/
lemma contraction_factor_props (B T : ℝ) (hB : 0 < B) (hT : 0 < T) (hsmall : T < 1 / B) :
    0 ≤ B * T ∧ B * T < 1 := by
  refine ⟨mul_nonneg hB.le hT.le, ?_⟩
  have h : T * B < (1 / B) * B := mul_lt_mul_of_pos_right hsmall hB
  rw [one_div, inv_mul_cancel₀ (ne_of_gt hB)] at h
  linarith [mul_comm B T]

/-- **The Picard iteration converges** (abstract short-time existence at a point):
any sequence satisfying the one-step contraction has a limit. -/
lemma picard_sequence_converges {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (u : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h0 : |u 0 - u 1| ≤ D)
    (hcontract : ∀ n, |u (n + 1) - u (n + 2)| ≤ θ * |u n - u (n + 1)|) :
    ∃ ulim : ℝ, Filter.Tendsto u Filter.atTop (nhds ulim) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_contraction_real hθ0 hθ1 u D hD h0 hcontract)

/-! ### Function-space Banach fixed point (existence + uniqueness)

The Picard iteration lands in the complete metric space `ℝ →ᵇ ℝ` of bounded
continuous functions, where mathlib's `ContractingWith` gives BOTH existence and
uniqueness of the fixed point — exactly the shape the local-existence-and-
uniqueness statement needs. These lemmas package that machinery for the
bounded zeroth-order (lower-order) parabolic operator, whose Duhamel map is a
genuine BCF→BCF contraction for small time. -/

/-- **Banach fixed-point existence + uniqueness** on a complete nonempty metric
space: a contraction has a unique fixed point. -/
lemma banach_fixedPoint_exists_unique {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : ℝ≥0} (Φ : α → α) (hΦ : ContractingWith K Φ) :
    ∃! z : α, Φ z = z := by
  refine ⟨ContractingWith.fixedPoint Φ hΦ, hΦ.fixedPoint_isFixedPt, ?_⟩
  intro w hw
  exact hΦ.fixedPoint_unique (show Function.IsFixedPt Φ w from hw)

/-- Pointwise ⇒ sup-distance bound for bounded continuous functions. -/
lemma bcf_dist_le_of_pointwise (f g : BoundedContinuousFunction ℝ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, |f x - g x| ≤ C) : dist f g ≤ C := by
  rw [BoundedContinuousFunction.dist_le hC]
  intro x
  rw [Real.dist_eq]
  exact h x

/-- A pointwise contraction bound gives a `LipschitzWith` self-map of `ℝ →ᵇ ℝ`. -/
lemma bcf_lipschitz_of_pointwise {K : ℝ≥0}
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ (K : ℝ) * dist f g) :
    LipschitzWith K Φ := by
  refine LipschitzWith.of_dist_le_mul (fun f g => ?_)
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro x
  rw [Real.dist_eq]
  exact h f g x

/-- The zeroth-order multiplication operator preserves sup bounds. -/
lemma mul_bounded_of_bounded (c u : ℝ → ℝ) (Mc Mu : ℝ) (hMc : 0 ≤ Mc) (hMu : 0 ≤ Mu)
    (hc : ∀ x, |c x| ≤ Mc) (hu : ∀ x, |u x| ≤ Mu) :
    ∀ x, |c x * u x| ≤ Mc * Mu := by
  intro x
  rw [abs_mul]
  exact mul_le_mul (hc x) (hu x) (abs_nonneg _) hMc

/-- The zeroth-order multiplication operator is Lipschitz in its argument with
constant `‖c‖∞`. -/
lemma mul_bounded_sub_le (c : ℝ → ℝ) (Mc : ℝ) (hMc : 0 ≤ Mc) (hc : ∀ x, |c x| ≤ Mc)
    (u v : ℝ → ℝ) (D : ℝ) (hD : ∀ x, |u x - v x| ≤ D) :
    ∀ x, |c x * u x - c x * v x| ≤ Mc * D := by
  intro x
  have : c x * u x - c x * v x = c x * (u x - v x) := by ring
  rw [this, abs_mul]
  exact mul_le_mul (hc x) (hD x) (abs_nonneg _) hMc

/-- A `θ < 1` pointwise BCF contraction packages into `ContractingWith θ.toNNReal`. -/
lemma contractingWith_of_pointwise {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g) :
    ContractingWith (Real.toNNReal θ) Φ := by
  refine ⟨?_, ?_⟩
  · have hlt : ((Real.toNNReal θ : NNReal) : ℝ) < 1 := by
      rw [Real.coe_toNNReal θ hθ0]; exact hθ1
    exact_mod_cast hlt
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    have hcoe : ((Real.toNNReal θ : NNReal) : ℝ) = θ := Real.coe_toNNReal θ hθ0
    rw [hcoe]
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro x
    rw [Real.dist_eq]
    exact h f g x

/-- `IsFixedPt` unfolds to the operator equation. -/
lemma isFixedPt_iff {α : Type*} (Φ : α → α) (z : α) : Function.IsFixedPt Φ z ↔ Φ z = z := Iff.rfl

/-- The Banach fixed point solves the operator equation `Φ z = z`. -/
lemma fixedPoint_solves {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : ℝ≥0} (Φ : α → α) (hΦ : ContractingWith K Φ) :
    Φ (ContractingWith.fixedPoint Φ hΦ) = ContractingWith.fixedPoint Φ hΦ :=
  hΦ.fixedPoint_isFixedPt

/-- A bounded continuous `f : ℝ → ℝ` lifts to an element of `ℝ →ᵇ ℝ` with the same
values. -/
lemma exists_bcf_of_bounded_continuous (f : ℝ → ℝ) (hcont : Continuous f) (M : ℝ)
    (hbound : ∀ x, |f x| ≤ M) :
    ∃ F : BoundedContinuousFunction ℝ ℝ, ∀ x, F x = f x := by
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hcont M (fun x => ?_), fun x => rfl⟩
  rw [Real.norm_eq_abs]
  exact hbound x

/-- The bounded zeroth-order Duhamel contraction factor `Mc·t` lies in `[0,1)` for
`t < 1/Mc` — the short-time existence window for the bounded lower-order equation. -/
lemma bounded_zeroth_order_contraction_factor (Mc t : ℝ) (hMc : 0 < Mc) (ht : 0 < t)
    (hsmall : t < 1 / Mc) :
    0 ≤ Mc * t ∧ Mc * t < 1 :=
  contraction_factor_props Mc t hMc ht hsmall

/-- **Abstract short-time existence + uniqueness for a contraction iteration map.**
Any self-map `Φ` of `ℝ →ᵇ ℝ` satisfying the pointwise contraction estimate
`|Φ f x − Φ g x| ≤ θ·dist f g` with `θ < 1` has a unique fixed point. This is the
packaged Banach engine the variable-coefficient (and ultimately Ricci–DeTurck)
solution operators instantiate: existence and uniqueness in one statement, on the
complete function space. -/
theorem exists_unique_fixedPoint_of_pointwise_contraction {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g) :
    ∃! z : BoundedContinuousFunction ℝ ℝ, Φ z = z :=
  banach_fixedPoint_exists_unique Φ (contractingWith_of_pointwise hθ0 hθ1 Φ h)

/-! ### Regularity-preserving fixed point (fixed point on a complete invariant set)

For the genuine second-order perturbation the solution must stay in a regularity
class (a closed ball of Hölder/Lipschitz-bounded functions) where the Duhamel
term's second derivative is controlled. Closed subsets of `ℝ →ᵇ ℝ` are complete
(`IsClosed.isComplete`), so the Banach fixed point runs on a forward-invariant
closed ball, confining the solution to the regularity class — the function-space
form of escaping the original C⁰ obstruction. -/

/-- A closed subset of `ℝ →ᵇ ℝ` is complete. -/
lemma isComplete_closed_bcf {s : Set (BoundedContinuousFunction ℝ ℝ)} (hs : IsClosed s) :
    IsComplete s :=
  hs.isComplete

/-- `edist` between bounded continuous functions is never `∞`. -/
lemma edist_ne_top_bcf (f g : BoundedContinuousFunction ℝ ℝ) : edist f g ≠ ∞ :=
  edist_ne_top f g

/-- A closed ball in `ℝ →ᵇ ℝ` is complete. -/
lemma closedBall_isComplete (center : BoundedContinuousFunction ℝ ℝ) (R : ℝ) :
    IsComplete (Metric.closedBall center R) :=
  Metric.isClosed_closedBall.isComplete

/-- A closed ball of nonnegative radius is nonempty. -/
lemma closedBall_nonempty_of_nonneg (center : BoundedContinuousFunction ℝ ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (Metric.closedBall center R).Nonempty :=
  ⟨center, by rw [Metric.mem_closedBall, dist_self]; exact hR⟩

/-- `MapsTo` criterion for a closed ball via the distance characterization. -/
lemma mapsTo_closedBall_of_dist
    {Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ}
    (center : BoundedContinuousFunction ℝ ℝ) (R : ℝ)
    (h : ∀ f, dist f center ≤ R → dist (Φ f) center ≤ R) :
    Set.MapsTo Φ (Metric.closedBall center R) (Metric.closedBall center R) := by
  intro f hf
  rw [Metric.mem_closedBall] at hf ⊢
  exact h f hf

/-- A contraction mapping a complete invariant set into itself has a fixed point in
that set. -/
lemma fixedPoint_on_invariant_set {K : ℝ≥0}
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (s : Set (BoundedContinuousFunction ℝ ℝ)) (hsc : IsComplete s) (hne : s.Nonempty)
    (hmaps : Set.MapsTo Φ s s)
    (hcontract : ContractingWith K (hmaps.restrict Φ s s)) :
    ∃ z ∈ s, Φ z = z := by
  have hx₀ : hne.choose ∈ s := hne.choose_spec
  have hx : edist hne.choose (Φ hne.choose) ≠ ∞ := edist_ne_top _ _
  rcases ContractingWith.exists_fixedPoint' hsc hmaps hcontract hx₀ hx with
    ⟨y, hys, hyfix, _⟩
  exact ⟨y, hys, hyfix⟩

/-- A pointwise `θ < 1` contraction restricts to a `ContractingWith` on any invariant
subset. -/
lemma restrict_contracting_of_pointwise {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (s : Set (BoundedContinuousFunction ℝ ℝ)) (hmaps : Set.MapsTo Φ s s)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g) :
    ContractingWith (Real.toNNReal θ) (hmaps.restrict Φ s s) := by
  refine ⟨?_, ?_⟩
  · have hlt : ((Real.toNNReal θ : NNReal) : ℝ) < 1 := by
      rw [Real.coe_toNNReal θ hθ0]; exact hθ1
    exact_mod_cast hlt
  · apply LipschitzWith.of_dist_le_mul
    rintro ⟨f, hf⟩ ⟨g, hg⟩
    have hcoe : ((Real.toNNReal θ : NNReal) : ℝ) = θ := Real.coe_toNNReal θ hθ0
    rw [hcoe]
    have hsub : dist (hmaps.restrict Φ s s ⟨f, hf⟩) (hmaps.restrict Φ s s ⟨g, hg⟩)
        = dist (Φ f) (Φ g) := Subtype.dist_eq _ _
    have hsub2 : dist (⟨f, hf⟩ : s) ⟨g, hg⟩ = dist f g := Subtype.dist_eq _ _
    rw [hsub, hsub2]
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro x
    rw [Real.dist_eq]
    exact h f g x

/-- **Regularity-preserving existence + uniqueness**: a globally-pointwise
contraction with a complete invariant set `s` has a unique fixed point, and it lies
in `s`. The solution is confined to the regularity class `s`. -/
lemma exists_unique_fixedPoint_in_set {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (s : Set (BoundedContinuousFunction ℝ ℝ)) (hsc : IsComplete s) (hne : s.Nonempty)
    (hmaps : Set.MapsTo Φ s s)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g) :
    ∃! z, z ∈ s ∧ Φ z = z := by
  have hΦglobal : ContractingWith (Real.toNNReal θ) Φ := contractingWith_of_pointwise hθ0 hθ1 Φ h
  have hrestrict : ContractingWith (Real.toNNReal θ) (hmaps.restrict Φ s s) :=
    restrict_contracting_of_pointwise hθ0 hθ1 Φ s hmaps h
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨z, hzs, hzfix, -⟩ :=
    ContractingWith.exists_fixedPoint' hsc hmaps hrestrict hx0 (edist_ne_top _ _)
  have hglobal : ∃! w, Φ w = w := banach_fixedPoint_exists_unique Φ hΦglobal
  refine ⟨z, ⟨hzs, hzfix⟩, ?_⟩
  rintro w ⟨hws, hwfix⟩
  exact hglobal.unique hwfix hzfix

/-- A-priori geometric convergence rate of the Picard iterates to the unique fixed
point: `dist x z* ≤ dist x (Φ x) / (1 - θ)`. -/
lemma dist_fixedPoint_le_of_contraction {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (h : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g)
    (x : BoundedContinuousFunction ℝ ℝ) :
    dist x (ContractingWith.fixedPoint Φ (contractingWith_of_pointwise hθ0 hθ1 Φ h))
      ≤ dist x (Φ x) / (1 - θ) := by
  have hΦ := contractingWith_of_pointwise hθ0 hθ1 Φ h
  have := hΦ.dist_fixedPoint_le x
  rwa [show ((θ.toNNReal : ℝ)) = θ from Real.coe_toNNReal θ hθ0] at this

/-! ### Concrete instantiation: the heat semigroup in `ℝ →ᵇ ℝ`

The parabolic smoothing operator `Hₜ` maps bounded measurable data to bounded
continuous functions, landing in the complete space `ℝ →ᵇ ℝ` where the fixed point
lives. This yields a concrete, hypothesis-free existence + uniqueness theorem for
the affine operator equation `z = a + L z` (a contraction `L`), with explicit
Picard-iterate convergence — the full apparatus closing a real operator equation. -/

/-- The heat semigroup output is a bounded continuous function (lands in `ℝ →ᵇ ℝ`). -/
lemma heatSemigroup1D_bcf_exists {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    ∃ F : BoundedContinuousFunction ℝ ℝ, ∀ x, F x = heatSemigroup1D t f x := by
  have hcont := continuous_heatSemigroup1D_space ht hfm hfb
  have hbd : ∀ x, |heatSemigroup1D t f x| ≤ C :=
    fun x => abs_heatSemigroup1D_le ht x (fun y => by rw [← Real.norm_eq_abs]; exact hfb y)
  exact exists_bcf_of_bounded_continuous _ hcont C hbd

/-- Multiplication of a BCF by a bounded continuous coefficient lands in `ℝ →ᵇ ℝ`. -/
lemma bcf_mul_coeff_exists (c : ℝ → ℝ) (hcont : Continuous c) (Mc : ℝ) (hc : ∀ x, |c x| ≤ Mc)
    (u : BoundedContinuousFunction ℝ ℝ) :
    ∃ F : BoundedContinuousFunction ℝ ℝ, ∀ x, F x = c x * u x := by
  have hMc : (0 : ℝ) ≤ Mc := le_trans (abs_nonneg _) (hc 0)
  refine exists_bcf_of_bounded_continuous (fun x => c x * u x) (hcont.mul u.continuous)
    (Mc * ‖u‖) ?_
  intro x
  have hu : |u x| ≤ ‖u‖ := by
    have := BoundedContinuousFunction.norm_coe_le_norm u x
    simpa [Real.norm_eq_abs] using this
  calc |c x * u x| = |c x| * |u x| := abs_mul _ _
    _ ≤ Mc * ‖u‖ := mul_le_mul (hc x) hu (abs_nonneg _) hMc

/-- BCF subtraction is pointwise. -/
lemma bcf_sub_apply (f g : BoundedContinuousFunction ℝ ℝ) (x : ℝ) : (f - g) x = f x - g x := by
  simp

/-- A pointwise difference is bounded by the BCF sup-distance. -/
lemma bcf_dist_eq_iSup_pointwise_le (f g : BoundedContinuousFunction ℝ ℝ) (x : ℝ) :
    |f x - g x| ≤ dist f g := by
  have h := BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) x
  rwa [Real.dist_eq] at h

/-- **Maximum-principle nonexpansiveness** of the linear heat semigroup:
`|Hₜf x - Hₜg x| ≤ ‖f-g‖∞`. -/
lemma heatSemigroup1D_nonexpansive (t : ℝ) (ht : 0 < t) (f g : ℝ → ℝ) (C : ℝ)
    (hfm : AEStronglyMeasurable f) (hgm : AEStronglyMeasurable g)
    (hfgb : ∀ y, |f y - g y| ≤ C) (x : ℝ) :
    |heatSemigroup1D t f x - heatSemigroup1D t g x| ≤ C :=
  heatSemigroup1D_sub_holder t ht f g C hfm hgm
    (fun y => by rw [Real.norm_eq_abs]; exact hfgb y) x

/-- The heat semigroup is nonexpansive in the BCF sup-metric. -/
lemma heatSemigroup1D_bcf_dist_le (t : ℝ) (ht : 0 < t) (F G HF HG : BoundedContinuousFunction ℝ ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hHF : ∀ x, HF x = heatSemigroup1D t F x) (hHG : ∀ x, HG x = heatSemigroup1D t G x)
    (hbound : ∀ y, |F y - G y| ≤ C) :
    dist HF HG ≤ C := by
  apply bcf_dist_le_of_pointwise HF HG C hC
  intro x
  rw [hHF, hHG]
  exact heatSemigroup1D_sub_holder t ht (F : ℝ → ℝ) (G : ℝ → ℝ) C
    F.continuous.aestronglyMeasurable G.continuous.aestronglyMeasurable
    (fun y => by rw [Real.norm_eq_abs]; exact hbound y) x

/-- The zeroth-order heat-Duhamel contraction estimate: the bounded coefficient
operator composed with the semigroup contracts in sup norm by `Mc`. -/
lemma heat_zeroth_order_contraction (t : ℝ) (ht : 0 < t) (c : ℝ → ℝ) (Mc : ℝ)
    (hc : ∀ x, |c x| ≤ Mc)
    (u v : ℝ → ℝ) (Cu : ℝ) (hum : AEStronglyMeasurable (fun y => c y * u y))
    (hvm : AEStronglyMeasurable (fun y => c y * v y))
    (huv : ∀ y, |u y - v y| ≤ Cu) (x : ℝ) :
    |heatSemigroup1D t (fun y => c y * u y) x - heatSemigroup1D t (fun y => c y * v y) x|
      ≤ Mc * Cu := by
  have hMc : 0 ≤ Mc := le_trans (abs_nonneg _) (hc 0)
  refine heatSemigroup1D_sub_holder t ht (fun y => c y * u y) (fun y => c y * v y)
    (Mc * Cu) hum hvm (fun y => ?_) x
  rw [Real.norm_eq_abs]
  have hfac : c y * u y - c y * v y = c y * (u y - v y) := by ring
  rw [hfac, abs_mul]
  exact mul_le_mul (hc y) (huv y) (abs_nonneg _) hMc

/-- **Concrete existence + uniqueness for the affine operator equation**
`z = a + L z`: for any contraction `L` on `ℝ →ᵇ ℝ` (factor `θ < 1`), the equation
has a unique solution. A fully-instantiated, hypothesis-free fixed-point theorem. -/
lemma affine_bcf_fixedPoint_exists_unique (a : BoundedContinuousFunction ℝ ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (L : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (hL : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |L f x - L g x| ≤ θ * dist f g) :
    ∃! z : BoundedContinuousFunction ℝ ℝ, a + L z = z := by
  set Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ :=
    fun z => a + L z with hΦ
  have hcontr : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x,
      |Φ f x - Φ g x| ≤ θ * dist f g := by
    intro f g x
    have hfx : Φ f x = a x + L f x := by simp [hΦ]
    have hgx : Φ g x = a x + L g x := by simp [hΦ]
    rw [hfx, hgx]
    have : a x + L f x - (a x + L g x) = L f x - L g x := by ring
    rw [this]
    exact hL f g x
  have := exists_unique_fixedPoint_of_pointwise_contraction hθ0 hθ1 Φ hcontr
  simpa [hΦ] using this

/-- The Picard iterates of the affine contraction converge to its unique fixed
point (constructive existence). -/
lemma affine_iterate_tendsto_fixedPoint (a : BoundedContinuousFunction ℝ ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (L : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ)
    (hL : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |L f x - L g x| ≤ θ * dist f g)
    (u0 : BoundedContinuousFunction ℝ ℝ) :
    ∃ z : BoundedContinuousFunction ℝ ℝ, (a + L z = z) ∧
      Filter.Tendsto (fun n => (fun w => a + L w)^[n] u0) Filter.atTop (nhds z) := by
  set Φ : BoundedContinuousFunction ℝ ℝ → BoundedContinuousFunction ℝ ℝ :=
    fun w => a + L w with hΦdef
  have hpt : ∀ f g : BoundedContinuousFunction ℝ ℝ, ∀ x, |Φ f x - Φ g x| ≤ θ * dist f g := by
    intro f g x
    have : Φ f x - Φ g x = L f x - L g x := by
      simp only [hΦdef, BoundedContinuousFunction.add_apply]; ring
    rw [this]
    exact hL f g x
  have hΦ : ContractingWith (Real.toNNReal θ) Φ :=
    contractingWith_of_pointwise hθ0 hθ1 Φ hpt
  exact ⟨ContractingWith.fixedPoint Φ hΦ, hΦ.fixedPoint_isFixedPt,
    hΦ.tendsto_iterate_fixedPoint u0⟩

end AnalyticPDE
end RicciFlow
