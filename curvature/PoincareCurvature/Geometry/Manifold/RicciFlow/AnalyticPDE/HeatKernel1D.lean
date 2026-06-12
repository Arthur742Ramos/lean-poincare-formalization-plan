module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Pi

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

/-- Subtracting a constant commutes with the heat semigroup:
`Hₜ(f - m) = Hₜf - m` for bounded measurable `f`. -/
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

/-- The `n`-dim convolution integrand `y ↦ Kₙ(t, x - y) · f y` is integrable for
bounded a.e.-strongly-measurable `f`. -/
theorem integrable_heatKernelND_sub_mul {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y : Fin n → ℝ => heatKernelND t (x - y) * f y) :=
  (integrable_heatKernelND_sub ht x).mul_bdd hmeas
    (Filter.Eventually.of_forall hbound)

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

/-- **Two-sided maximum principle for the `n`-dimensional heat semigroup.**  If
`c ≤ f y ≤ C` for all `y` and `f` is a.e.-strongly-measurable, then
`c ≤ heatSemigroupND t f x ≤ C`. -/
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

end AnalyticPDE
end RicciFlow
