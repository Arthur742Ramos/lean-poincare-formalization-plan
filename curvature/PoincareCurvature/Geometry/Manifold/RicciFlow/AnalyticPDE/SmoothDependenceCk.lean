module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false

/-!
# Smooth dependence of ODE flows on initial data — Lipschitz (`C^{0,1}`) base layer

This module begins the missing upstream theory needed by roadmap point 4,
Items 1 and 2: *dependence of the flow of a vector field on the initial
condition*.  Mathlib v4.29.1 provides Grönwall trajectory estimates and
local existence of integral curves, but the flow's dependence on the initial
point — the `C^k` regularity that the compact-manifold gauge flow ultimately
consumes — is not available.

This file proves the base (`C^0` / Lipschitz, i.e. `C^{0,1}`) layer of that
tower for *global* integral curves of a uniformly (in time) Lipschitz vector
field on a real Banach space:

* `isIntegralCurve_comp_neg`  — the time-reversed curve is an integral curve of
  the time-reversed field (an isometry-Lipschitz field with the same constant);
* `dist_le_of_isIntegralCurve_of_le` — the **forward** exponential dependence
  bound, packaging Mathlib's `dist_le_of_trajectories_ODE` in `IsIntegralCurve`
  form;
* `dist_le_of_isIntegralCurve` — the **two-sided** bound
  `dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · |t - t₀|)`, obtained from the
  forward bound applied to the time-reversed curves (Mathlib only supplies the
  forward, `t ≥ t₀`, half);
* `dist_le_of_isIntegralCurve_of_abs_le` — a uniform Lipschitz-in-initial-data
  bound valid on a symmetric compact time interval;
* `eq_of_isIntegralCurve_of_eq` — the resulting global uniqueness of an integral
  curve through a given point.

Everything here is proved from Mathlib's Banach-level ODE results; no PDE or
manifold content is used.  Higher (`C^1`, …, `C^k`) dependence is deferred to
subsequent layers.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {t₀ t : ℝ}

/-- If `f` is a global integral curve of `v`, then the time-reversed curve
`s ↦ f (-s)` is a global integral curve of the time-reversed vector field
`(s, x) ↦ -(v (-s) x)`.  This is the algebraic core of the backward-in-time
Grönwall estimate. -/
theorem isIntegralCurve_comp_neg (hf : IsIntegralCurve f v) :
    IsIntegralCurve (fun s => f (-s)) (fun s x => -(v (-s) x)) := by
  intro t
  have h2 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := hasDerivAt_neg' t
  have hcomp : HasDerivAt (f ∘ fun s : ℝ => -s) ((-1 : ℝ) • v (-t) (f (-t))) t :=
    HasDerivAt.scomp t (hf (-t)) h2
  simpa only [Function.comp_def, neg_one_smul] using hcomp

/-- **Forward** exponential dependence on initial data: two global integral
curves of a uniformly (in time) `K`-Lipschitz vector field satisfy
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · (t - t₀))` for `t₀ ≤ t`.
This repackages Mathlib's `dist_le_of_trajectories_ODE` in `IsIntegralCurve`
form. -/
theorem dist_le_of_isIntegralCurve_of_le
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (h : t₀ ≤ t) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * (t - t₀)) := by
  have key := dist_le_of_trajectories_ODE (a := t₀) (b := t) (δ := dist (f t₀) (g t₀)) hv
    hf.continuous.continuousOn (fun s _ => (hf s).hasDerivWithinAt)
    hg.continuous.continuousOn (fun s _ => (hg s).hasDerivWithinAt) le_rfl
  exact key t ⟨h, le_rfl⟩

/-- **Two-sided** exponential dependence on initial data:
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · |t - t₀|)` for *all* `t`.
Mathlib supplies only the forward (`t ≥ t₀`) half; the backward half is obtained
by applying the forward bound to the time-reversed integral curves. -/
theorem dist_le_of_isIntegralCurve
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (t₀ t : ℝ) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact dist_le_of_isIntegralCurve_of_le hv hf hg h
  · have hw : ∀ s, LipschitzWith K (fun x => -(v (-s) x)) := by
      intro s
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_neg_neg]
      exact (hv (-s)).dist_le_mul a b
    have hfn := isIntegralCurve_comp_neg hf
    have hgn := isIntegralCurve_comp_neg hg
    have key := dist_le_of_isIntegralCurve_of_le hw hfn hgn (neg_le_neg h)
    simp only [neg_neg] at key
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have harg : (K : ℝ) * -(t - t₀) = (K : ℝ) * (-t - -t₀) := by ring
    rw [harg]
    exact key

/-- Uniform Lipschitz dependence on initial data over a symmetric compact time
interval: if `|t - t₀| ≤ T` then
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · T)`. -/
theorem dist_le_of_isIntegralCurve_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {T : ℝ} (hT : |t - t₀| ≤ T) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * T) := by
  refine (dist_le_of_isIntegralCurve hv hf hg t₀ t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ dist_nonneg
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT K.coe_nonneg)

/-- Global uniqueness of an integral curve through a given point: two global
integral curves of a uniformly Lipschitz vector field that agree at one time
agree everywhere. -/
theorem eq_of_isIntegralCurve_of_eq
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (h0 : f t₀ = g t₀) (t : ℝ) : f t = g t := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t₀ t
  rw [h0, dist_self, zero_mul] at hb
  exact dist_le_zero.mp hb

/-- Uniqueness from agreement at *any* single time: two global integral curves of a
uniformly Lipschitz field that coincide at one time `t₁` coincide everywhere. -/
theorem eq_of_isIntegralCurve_of_eq_at
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {t₁ : ℝ} (h1 : f t₁ = g t₁) (t : ℝ) : f t = g t := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t₁ t
  rw [h1, dist_self, zero_mul] at hb
  exact dist_le_zero.mp hb

/-!
## Stability under perturbation of the vector field

Continuous dependence of an integral curve on the *field* it solves: if two curves solve
uniformly `ε`-close fields (one of them uniformly `K`-Lipschitz), their separation is
controlled by the Grönwall bound.  This is the driver behind "the flow depends
continuously on the vector field", used to transfer regularity of the DeTurck field to
the DeTurck flow.
-/

/-- **Forward stability under perturbation of the vector field.**  If `f` is an integral
curve of the uniformly `K`-Lipschitz field `v`, `g` is an integral curve of a field `w`
that stays within `ε` of `v` uniformly, then for `t₀ ≤ t`,
`dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) K ε (t - t₀)`. -/
theorem dist_le_of_isIntegralCurve_perturb_of_le {w : ℝ → E → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε) (h : t₀ ≤ t) :
    dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) (K : ℝ) ε (t - t₀) := by
  have key := dist_le_of_approx_trajectories_ODE (a := t₀) (b := t)
    (εf := 0) (εg := ε) (δ := dist (f t₀) (g t₀)) hv
    hf.continuous.continuousOn (fun s _ => (hf s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    hg.continuous.continuousOn (fun s _ => (hg s).hasDerivWithinAt)
    (fun s _ => by rw [dist_comm]; exact hvw s (g s)) le_rfl
  have hb := key t ⟨h, le_rfl⟩
  rwa [zero_add] at hb

/-- **Two-sided stability under perturbation of the vector field.**  If `f` is an integral
curve of the uniformly `K`-Lipschitz field `v` and `g` is an integral curve of a field `w`
that stays within `ε` of `v` uniformly, then for *all* `t`,
`dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) K ε |t - t₀|`.  Mathlib's Grönwall
approximation lemma only supplies the forward (`t ≥ t₀`) half; the backward half comes
from applying the forward bound to the time-reversed curves, whose fields are still
`K`-Lipschitz and `ε`-close.  This is the two-sided *continuous dependence on the field*
that transfers regularity of the DeTurck vector field to the DeTurck flow. -/
theorem dist_le_of_isIntegralCurve_perturb {w : ℝ → E → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε) (t₀ t : ℝ) :
    dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) (K : ℝ) ε |t - t₀| := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact dist_le_of_isIntegralCurve_perturb_of_le hv hf hg hvw h
  · have hw : ∀ s, LipschitzWith K (fun x => -(v (-s) x)) := by
      intro s
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_neg_neg]
      exact (hv (-s)).dist_le_mul a b
    have hfn := isIntegralCurve_comp_neg hf
    have hgn := isIntegralCurve_comp_neg hg
    have hvw' : ∀ s x, dist (-(v (-s) x)) (-(w (-s) x)) ≤ ε := by
      intro s x
      rw [dist_neg_neg]
      exact hvw (-s) x
    have key := dist_le_of_isIntegralCurve_perturb_of_le hw hfn hgn hvw' (neg_le_neg h)
    simp only [neg_neg] at key
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have harg : -t - -t₀ = -(t - t₀) := by ring
    rwa [harg] at key

/-!
## The flow map is exponentially Lipschitz in the initial value

Packaging the two-sided Grönwall bound for a *flow family* `Φ : E → ℝ → E`, where for
each initial value `x` the curve `Φ x` is the integral curve of `v` anchored at
`Φ x t₀ = x`.  This is exactly the `C^0` dependence-on-initial-data statement that the
compact-manifold gauge flow (Item 2) consumes: the time-`t` flow map `x ↦ Φ x t` is
Lipschitz, with an explicit exponential constant, uniformly on compact time intervals.
-/

variable {Φ : E → ℝ → E}

/-- Two-sided dependence bound for a flow family: if for each initial value `x` the
curve `Φ x` is an integral curve of the uniformly `K`-Lipschitz field `v` anchored at
`Φ x t₀ = x`, then `dist (Φ x t) (Φ y t) ≤ dist x y · exp (K · |t - t₀|)`. -/
theorem dist_flow_apply_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (x y : E) (t : ℝ) :
    dist (Φ x t) (Φ y t) ≤ dist x y * Real.exp ((K : ℝ) * |t - t₀|) := by
  have hb := dist_le_of_isIntegralCurve hv (hΦ x) (hΦ y) t₀ t
  rwa [h0 x, h0 y] at hb

/-- The time-`t` flow map `x ↦ Φ x t` is Lipschitz with constant `exp (K · |t - t₀|)`. -/
theorem lipschitzWith_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    LipschitzWith (Real.exp ((K : ℝ) * |t - t₀|)).toNNReal (fun x => Φ x t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  calc dist (Φ x t) (Φ y t) ≤ dist x y * Real.exp ((K : ℝ) * |t - t₀|) :=
        dist_flow_apply_le hv hΦ h0 x y t
    _ = Real.exp ((K : ℝ) * |t - t₀|) * dist x y := mul_comm _ _

/-- The time-`t` flow map `x ↦ Φ x t` is continuous in the initial value. -/
theorem continuous_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Continuous (fun x => Φ x t) :=
  (lipschitzWith_flow_apply hv hΦ h0 t).continuous

/-- The time-`t` flow map `x ↦ Φ x t` is injective: distinct initial values stay distinct
under the flow.  (This is the injectivity half of the flow being a diffeomorphism onto its
image, consumed by the gauge-flow diffeomorphism family of Item 2.) -/
theorem injective_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Injective (fun x => Φ x t) := by
  intro x y hxy
  have hb := eq_of_isIntegralCurve_of_eq_at hv (hΦ x) (hΦ y) hxy t₀
  rwa [h0 x, h0 y] at hb

/-- Uniform Lipschitz dependence of the flow map on a symmetric compact time interval:
whenever `|t - t₀| ≤ T`, the time-`t` flow map is Lipschitz with the single constant
`exp (K · T)`. -/
theorem lipschitzWith_flow_apply_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) {T : ℝ} (hT : |t - t₀| ≤ T) :
    LipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal (fun x => Φ x t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm (Real.exp ((K : ℝ) * T)) (dist x y)]
  have hxy := dist_le_of_isIntegralCurve_of_abs_le hv (hΦ x) (hΦ y) hT
  rwa [h0 x, h0 y] at hxy

/-- **Joint continuity of the flow.**  For a flow family `Φ` of the uniformly
`K`-Lipschitz field `v` anchored at `Φ x t₀ = x`, the map `(t, x) ↦ Φ x t` is jointly
continuous on `ℝ × E`.  Continuity in the initial value is uniform (Lipschitz with the
exponential constant) and continuity in time comes from each curve being an integral
curve; the two combine by a triangle-inequality squeeze. -/
theorem continuous_flow
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun p : ℝ × E => Φ p.2 p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₁, x₁⟩
  have key : Filter.Tendsto (fun p : ℝ × E => dist (Φ p.2 p.1) (Φ x₁ t₁))
      (nhds (t₁, x₁)) (nhds 0) := by
    refine squeeze_zero (fun p => dist_nonneg) (g := fun p : ℝ × E =>
        dist p.2 x₁ * Real.exp ((K : ℝ) * |p.1 - t₀|) + dist (Φ x₁ p.1) (Φ x₁ t₁))
        (fun p => ?_) ?_
    · calc dist (Φ p.2 p.1) (Φ x₁ t₁)
          ≤ dist (Φ p.2 p.1) (Φ x₁ p.1) + dist (Φ x₁ p.1) (Φ x₁ t₁) := dist_triangle _ _ _
        _ ≤ dist p.2 x₁ * Real.exp ((K : ℝ) * |p.1 - t₀|) + dist (Φ x₁ p.1) (Φ x₁ t₁) := by
            gcongr
            exact dist_flow_apply_le hv hΦ h0 p.2 x₁ p.1
    · have hd : Filter.Tendsto (fun p : ℝ × E => dist p.2 x₁) (nhds (t₁, x₁)) (nhds 0) := by
        have hcont : Continuous (fun p : ℝ × E => dist p.2 x₁) :=
          continuous_snd.dist continuous_const
        simpa using hcont.tendsto (t₁, x₁)
      have he : Filter.Tendsto (fun p : ℝ × E => Real.exp ((K : ℝ) * |p.1 - t₀|))
          (nhds (t₁, x₁)) (nhds (Real.exp ((K : ℝ) * |t₁ - t₀|))) := by
        have hcont : Continuous (fun p : ℝ × E => Real.exp ((K : ℝ) * |p.1 - t₀|)) :=
          Real.continuous_exp.comp
            (continuous_const.mul (continuous_fst.sub continuous_const).abs)
        simpa using hcont.tendsto (t₁, x₁)
      have hB2 : Filter.Tendsto (fun p : ℝ × E => dist (Φ x₁ p.1) (Φ x₁ t₁))
          (nhds (t₁, x₁)) (nhds 0) := by
        have hcont : Continuous (fun p : ℝ × E => dist (Φ x₁ p.1) (Φ x₁ t₁)) :=
          ((hΦ x₁).continuous.comp continuous_fst).dist continuous_const
        simpa using hcont.tendsto (t₁, x₁)
      have hB1 := hd.mul he
      simpa using (hB1.add hB2)
  have hiff := tendsto_iff_dist_tendsto_zero (a := Φ x₁ t₁)
    (f := fun p : ℝ × E => Φ p.2 p.1) (x := nhds (t₁, x₁))
  exact hiff.mpr key

/-!
## The flow map is a bi-Lipschitz uniform embedding in the initial value

The two-sided distance bound also yields a *lower* exponential control: the flow
cannot contract distances faster than `exp (-K · |t - t₀|)`.  Combined with the
Lipschitz upper bound this exhibits the time-`t` flow map as a **bi-Lipschitz**
(indeed a uniform) embedding onto its image — the `C^0` shadow of the
"diffeomorphism onto its image" property consumed by the compact-manifold gauge
flow of Item 2.  Antilipschitz packaging is the quantitative statement that the
inverse of the flow map (on its image) is itself Lipschitz with the reciprocal
exponential constant.
-/

/-- **Lower** two-sided exponential dependence for integral curves:
`dist (f t₀) (g t₀) · exp (-K · |t - t₀|) ≤ dist (f t) (g t)`.  Obtained from the
two-sided upper bound `dist_le_of_isIntegralCurve` with the anchor and evaluation
times swapped: the flow run *backward* from time `t` to `t₀` can expand
`dist (f t) (g t)` by at most `exp (K · |t - t₀|)`. -/
theorem dist_ge_of_isIntegralCurve
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (t₀ t : ℝ) :
    dist (f t₀) (g t₀) * Real.exp (-(K : ℝ) * |t - t₀|) ≤ dist (f t) (g t) := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t t₀
  rw [abs_sub_comm] at hb
  calc dist (f t₀) (g t₀) * Real.exp (-(K : ℝ) * |t - t₀|)
      ≤ dist (f t) (g t) * Real.exp ((K : ℝ) * |t - t₀|) * Real.exp (-(K : ℝ) * |t - t₀|) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = dist (f t) (g t) := by
        rw [mul_assoc, ← Real.exp_add,
          show (K : ℝ) * |t - t₀| + -(K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one]

/-- Lower exponential dependence on initial data for a flow family:
`dist x y · exp (-K · |t - t₀|) ≤ dist (Φ x t) (Φ y t)`. -/
theorem dist_flow_apply_ge
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (x y : E) (t : ℝ) :
    dist x y * Real.exp (-(K : ℝ) * |t - t₀|) ≤ dist (Φ x t) (Φ y t) := by
  have hb := dist_ge_of_isIntegralCurve hv (hΦ x) (hΦ y) t₀ t
  rwa [h0 x, h0 y] at hb

/-- The time-`t` flow map `x ↦ Φ x t` is **antilipschitz** with constant
`exp (K · |t - t₀|)`: distinct initial values are separated at least
`exp (-K · |t - t₀|)` as far after flowing.  This is the quantitative injectivity
that upgrades `injective_flow_apply` to a bi-Lipschitz embedding. -/
theorem antilipschitzWith_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    AntilipschitzWith (Real.exp ((K : ℝ) * |t - t₀|)).toNNReal (fun x => Φ x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  have hb := dist_flow_apply_ge hv hΦ h0 x y t
  have key := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((K : ℝ) * |t - t₀|)).le
  rw [mul_assoc, ← Real.exp_add,
    show -(K : ℝ) * |t - t₀| + (K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one] at key
  exact key.trans_eq (mul_comm _ _)

/-- Uniform antilipschitz dependence of the flow map on a symmetric compact time
interval: whenever `|t - t₀| ≤ T`, the time-`t` flow map is antilipschitz with the
single constant `exp (K · T)`. -/
theorem antilipschitzWith_flow_apply_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) {T : ℝ} (hT : |t - t₀| ≤ T) :
    AntilipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal (fun x => Φ x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  have hb := dist_flow_apply_ge hv hΦ h0 x y t
  have key := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((K : ℝ) * |t - t₀|)).le
  rw [mul_assoc, ← Real.exp_add,
    show -(K : ℝ) * |t - t₀| + (K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one] at key
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT K.coe_nonneg)

/-- **The time-`t` flow map is a uniform embedding onto its image.**  Being both
Lipschitz (`lipschitzWith_flow_apply`) and antilipschitz (`antilipschitzWith_flow_apply`)
in the initial value, `x ↦ Φ x t` is a bi-Lipschitz — hence uniform — embedding.
This is the `C^0` incarnation of "the gauge flow is a diffeomorphism onto its
image" that Item 2 consumes. -/
theorem isUniformEmbedding_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    IsUniformEmbedding (fun x => Φ x t) :=
  (antilipschitzWith_flow_apply hv hΦ h0 t).isUniformEmbedding
    (lipschitzWith_flow_apply hv hΦ h0 t).uniformContinuous

/-- The time-`t` flow map is a topological embedding onto its image. -/
theorem isEmbedding_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Topology.IsEmbedding (fun x => Φ x t) :=
  (isUniformEmbedding_flow_apply hv hΦ h0 t).isEmbedding

/-!
## Flow-family packaging of uniqueness and field-perturbation stability

The two-sided perturbation bound and the uniqueness lemma, packaged for two flow
*families* `Φ, Ψ` anchored at the same initial value.  With `ε = 0` the
perturbation bound degenerates to uniqueness of the flow family; with `ε > 0` it is
the quantitative "two flows of `ε`-close fields stay close" that transfers
regularity of the DeTurck vector field to the DeTurck flow (Item 3 / Item 2).
-/

/-- **Two flow families of uniformly `ε`-close fields, anchored at the same initial
value, stay close.**  If `Φ x` solves the uniformly `K`-Lipschitz field `v` and `Ψ x`
solves an `ε`-close field `w`, both with `Φ x t₀ = Ψ x t₀ = x`, then
`dist (Φ x t) (Ψ x t) ≤ gronwallBound 0 K ε |t - t₀|` for all `t`. -/
theorem dist_flow_perturb_le {w : ℝ → E → E} {Ψ : E → ℝ → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t))
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hΨ : ∀ x, IsIntegralCurve (Ψ x) w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε)
    (h0Φ : ∀ x, Φ x t₀ = x) (h0Ψ : ∀ x, Ψ x t₀ = x) (x : E) (t : ℝ) :
    dist (Φ x t) (Ψ x t) ≤ gronwallBound 0 (K : ℝ) ε |t - t₀| := by
  have hb := dist_le_of_isIntegralCurve_perturb hv (hΦ x) (hΨ x) hvw t₀ t
  rwa [h0Φ x, h0Ψ x, dist_self] at hb

/-- **Uniqueness of the flow family.**  Any two flow families of the *same* uniformly
`K`-Lipschitz field anchored at `Φ x t₀ = Ψ x t₀ = x` agree everywhere. -/
theorem flow_eq_of_isIntegralCurve {Ψ : E → ℝ → E}
    (hv : ∀ t, LipschitzWith K (v t))
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (h0Φ : ∀ x, Φ x t₀ = x) (h0Ψ : ∀ x, Ψ x t₀ = x) (x : E) (t : ℝ) :
    Φ x t = Ψ x t := by
  have h0 : Φ x t₀ = Ψ x t₀ := by rw [h0Φ x, h0Ψ x]
  exact eq_of_isIntegralCurve_of_eq hv (hΦ x) (hΨ x) h0 t

/-!
## Time regularity of the flow under a uniform velocity bound

The `continuous_flow` result gives *joint* continuity of `(t, x) ↦ Φ x t` but no
quantitative modulus in the time direction.  When the field is uniformly bounded
along the curve, `‖v t (f t)‖ ≤ M`, the integral curve is `M`-Lipschitz in time
(its derivative is the velocity, of norm `≤ M`).  This is the time-direction
companion of the exponential Lipschitz-in-initial-data bound, and together they
give a joint Lipschitz modulus of the flow on compact time intervals.
-/

/-- An integral curve of a field whose velocity along the curve is uniformly bounded by
`M` is `M`-Lipschitz in time: `dist (f s) (f t) ≤ M · dist s t`.  The curve's derivative
is `v t (f t)`, of norm `≤ M`, so the mean value inequality applies. -/
theorem lipschitzWith_of_isIntegralCurve_of_norm_le {M : ℝ}
    (hf : IsIntegralCurve f v) (hM : 0 ≤ M) (hvb : ∀ t, ‖v t (f t)‖ ≤ M) :
    LipschitzWith M.toNNReal f := by
  have hdiff : Differentiable ℝ f := fun t => (hf t).differentiableAt
  refine lipschitzWith_of_nnnorm_deriv_le hdiff fun t => ?_
  rw [(hf t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM]
  exact hvb t

/-- Each curve of a flow family whose velocity is uniformly bounded by `M` along the flow
is `M`-Lipschitz in time. -/
theorem lipschitzWith_flow_of_norm_le {M : ℝ}
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hM : 0 ≤ M)
    (hvb : ∀ x t, ‖v t (Φ x t)‖ ≤ M) (x : E) :
    LipschitzWith M.toNNReal (Φ x) :=
  lipschitzWith_of_isIntegralCurve_of_norm_le (hΦ x) hM (hvb x)

/-- **Joint Lipschitz modulus of the flow on a symmetric compact time interval.**  Under a
uniform velocity bound `M` and with `|t - t₀|, |s - t₀| ≤ T`, the flow separation is
controlled by the time gap (rate `M`) plus the initial-value gap (rate `exp (K · T)`):
`dist (Φ x t) (Φ y s) ≤ M · |t - s| + exp (K · T) · dist x y`.  This is the quantitative
strengthening of `continuous_flow` combining time- and initial-value-regularity. -/
theorem dist_flow_le_of_norm_le {M : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hM : 0 ≤ M) (hvb : ∀ x t, ‖v t (Φ x t)‖ ≤ M)
    {T : ℝ} (x y : E) {s t : ℝ} (hs : |s - t₀| ≤ T) :
    dist (Φ x t) (Φ y s) ≤ M * |t - s| + Real.exp ((K : ℝ) * T) * dist x y := by
  calc dist (Φ x t) (Φ y s)
      ≤ dist (Φ x t) (Φ x s) + dist (Φ x s) (Φ y s) := dist_triangle _ _ _
    _ ≤ M * |t - s| + Real.exp ((K : ℝ) * T) * dist x y := by
        gcongr
        · have hL := lipschitzWith_flow_of_norm_le hΦ hM hvb x
          have hd := hL.dist_le_mul t s
          rwa [Real.coe_toNNReal M hM, Real.dist_eq] at hd
        · have hLip := lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hs
          have hd := hLip.dist_le_mul x y
          rwa [Real.coe_toNNReal _ (Real.exp_pos _).le] at hd

/-!
## First brick of the `C^1` layer: the linear (variational) field is Lipschitz

Toward *differentiable* dependence on initial data one linearises: the flow
derivative `D_x Φ_t` is expected to solve the operator-valued **variational** ODE
`W'(t) = A(t) ∘ W(t)`, where `A(t) = D_x v (t, Φ_t x)` is the spatial derivative of
the field along the flow.  The algebraic core underpinning well-posedness of that
linear ODE is that, for a uniformly bounded operator path `A : ℝ → (E →L[ℝ] E)`
with `‖A t‖ ≤ K`, the associated linear vector field on the operator Banach space
`E →L[ℝ] E`, namely `W ↦ (A t).comp W`, is `K`-Lipschitz in `W`.  Uniqueness and
the exponential a priori bound for the variational ODE then follow from the `C^0`
dependence lemmas above, now instantiated on the Banach space of operators.  This
opens the `C^1` layer: the object on which differentiable dependence is built is
in place and well-posed. -/

/-- The linear (variational) vector field `W ↦ (A t).comp W` on the operator Banach space
`E →L[ℝ] E`, associated to an operator path `A`.  Its integral curves are the solutions of
the variational equation `W'(t) = A(t) ∘ W(t)`. -/
def variationalField (A : ℝ → (E →L[ℝ] E)) :
    ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) :=
  fun t W => (A t).comp W

/-- **The variational field is Lipschitz.**  Under a uniform operator-norm bound
`‖A t‖ ≤ K`, the linear field `W ↦ (A t).comp W` is `K`-Lipschitz in `W` — the core
estimate behind well-posedness of the variational ODE.  (Submultiplicativity of the
operator norm: `‖A t ∘ (W₁ - W₂)‖ ≤ ‖A t‖ · ‖W₁ - W₂‖ ≤ K · ‖W₁ - W₂‖`.) -/
theorem lipschitzWith_variationalField {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (t : ℝ) :
    LipschitzWith K (variationalField A t) := by
  refine LipschitzWith.of_dist_le_mul fun W₁ W₂ => ?_
  simp only [variationalField, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
  calc ‖(A t).comp (W₁ - W₂)‖
      ≤ ‖A t‖ * ‖W₁ - W₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (K : ℝ) * ‖W₁ - W₂‖ := by
        gcongr
        exact_mod_cast hA t

/-- **Uniqueness for the variational ODE.**  Two solutions of the linear variational ODE
`W'(t) = (A t).comp (W t)` with `‖A t‖ ≤ K` that agree at one time agree everywhere. -/
theorem variational_eq_of_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W₁ W₂ : ℝ → (E →L[ℝ] E)}
    (h1 : IsIntegralCurve W₁ (variationalField A))
    (h2 : IsIntegralCurve W₂ (variationalField A))
    {t₁ : ℝ} (h : W₁ t₁ = W₂ t₁) (t : ℝ) : W₁ t = W₂ t :=
  eq_of_isIntegralCurve_of_eq_at (fun s => lipschitzWith_variationalField hA s) h1 h2 h t

/-- **A priori exponential bound for the variational ODE.**  Two solutions of
`W'(t) = (A t).comp (W t)` with `‖A t‖ ≤ K` satisfy
`dist (W₁ t) (W₂ t) ≤ dist (W₁ t₀) (W₂ t₀) · exp (K · |t - t₀|)`. -/
theorem dist_variational_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W₁ W₂ : ℝ → (E →L[ℝ] E)}
    (h1 : IsIntegralCurve W₁ (variationalField A))
    (h2 : IsIntegralCurve W₂ (variationalField A))
    (t₀ t : ℝ) :
    dist (W₁ t) (W₂ t) ≤ dist (W₁ t₀) (W₂ t₀) * Real.exp ((K : ℝ) * |t - t₀|) :=
  dist_le_of_isIntegralCurve (fun s => lipschitzWith_variationalField hA s) h1 h2 t₀ t

/-- The **vector** variational field `u ↦ A t u` on `E`, associated to an operator path `A`.
Its integral curves solve the vector variational equation `u'(t) = A(t) (u(t))` satisfied
by the directional derivative `∂_h Φ_t` (evaluation of the fundamental solution on a fixed
direction) — the form of the linearised equation consumed by the tensor time-derivative
chain rule of Item 1. -/
def variationalFieldVec (A : ℝ → (E →L[ℝ] E)) : ℝ → E → E :=
  fun t u => A t u

/-- **The vector variational field is Lipschitz.**  Under a uniform bound `‖A t‖ ≤ K`, the
linear field `u ↦ A t u` is `K`-Lipschitz in `u`. -/
theorem lipschitzWith_variationalFieldVec {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (t : ℝ) :
    LipschitzWith K (variationalFieldVec A t) := by
  refine LipschitzWith.of_dist_le_mul fun u₁ u₂ => ?_
  simp only [variationalFieldVec, dist_eq_norm, ← map_sub]
  calc ‖(A t) (u₁ - u₂)‖
      ≤ ‖A t‖ * ‖u₁ - u₂‖ := (A t).le_opNorm _
    _ ≤ (K : ℝ) * ‖u₁ - u₂‖ := by
        gcongr
        exact_mod_cast hA t

/-- **Uniqueness for the vector variational ODE.**  Two solutions of `u'(t) = A(t) (u(t))`
with `‖A t‖ ≤ K` that agree at one time agree everywhere. -/
theorem variationalVec_eq_of_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {u₁ u₂ : ℝ → E}
    (h1 : IsIntegralCurve u₁ (variationalFieldVec A))
    (h2 : IsIntegralCurve u₂ (variationalFieldVec A))
    {t₁ : ℝ} (h : u₁ t₁ = u₂ t₁) (t : ℝ) : u₁ t = u₂ t :=
  eq_of_isIntegralCurve_of_eq_at (fun s => lipschitzWith_variationalFieldVec hA s) h1 h2 h t

/-- **A priori exponential bound for the vector variational ODE.**
`dist (u₁ t) (u₂ t) ≤ dist (u₁ t₀) (u₂ t₀) · exp (K · |t - t₀|)`. -/
theorem dist_variationalVec_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {u₁ u₂ : ℝ → E}
    (h1 : IsIntegralCurve u₁ (variationalFieldVec A))
    (h2 : IsIntegralCurve u₂ (variationalFieldVec A))
    (t₀ t : ℝ) :
    dist (u₁ t) (u₂ t) ≤ dist (u₁ t₀) (u₂ t₀) * Real.exp ((K : ℝ) * |t - t₀|) :=
  dist_le_of_isIntegralCurve (fun s => lipschitzWith_variationalFieldVec hA s) h1 h2 t₀ t

/-- **The operator variational solution, evaluated on a fixed direction, solves the vector
variational ODE.**  If `W` solves `W'(t) = A(t) ∘ W(t)` (the fundamental-solution equation),
then for any `u₀` the curve `t ↦ W t u₀` solves `u'(t) = A(t) (u(t))`.  This links the
operator- and vector-valued variational equations: the directional derivative
`∂_{u₀} Φ_t = D_x Φ_t · u₀ = W t u₀` obeys the vector variational equation, via the chain
rule for the (continuous linear) evaluation map `L ↦ L u₀`. -/
theorem isIntegralCurve_variational_apply {A : ℝ → (E →L[ℝ] E)}
    {W : ℝ → (E →L[ℝ] E)} (hW : IsIntegralCurve W (variationalField A)) (u₀ : E) :
    IsIntegralCurve (fun t => W t u₀) (variationalFieldVec A) := by
  intro t
  have hcomp := (hW t).clm_apply (hasDerivAt_const t u₀)
  simpa only [variationalField, variationalFieldVec, ContinuousLinearMap.comp_apply,
    map_zero, add_zero] using hcomp

/-!
### Superposition principle for the vector variational ODE

Being *linear*, the vector variational equation `u'(t) = A(t) (u(t))` has a solution set
closed under addition and scalar multiplication.  This is exactly what makes the map
`u₀ ↦ (solution through u₀) t` — i.e. the directional derivative `u₀ ↦ D_x Φ_t · u₀` —
**linear in the direction `u₀`**, so that it assembles into the bounded operator
`D_x Φ_t ∈ E →L[ℝ] E`.
-/

/-- **Superposition (additivity).**  The sum of two solutions of the vector variational
ODE is again a solution. -/
theorem isIntegralCurve_variationalFieldVec_add {A : ℝ → (E →L[ℝ] E)} {u w : ℝ → E}
    (hu : IsIntegralCurve u (variationalFieldVec A))
    (hw : IsIntegralCurve w (variationalFieldVec A)) :
    IsIntegralCurve (fun t => u t + w t) (variationalFieldVec A) := by
  intro t
  have h := (hu t).add (hw t)
  simpa only [variationalFieldVec, map_add] using h

/-- **Superposition (homogeneity).**  A scalar multiple of a solution of the vector
variational ODE is again a solution. -/
theorem isIntegralCurve_variationalFieldVec_smul {A : ℝ → (E →L[ℝ] E)} {u : ℝ → E} (c : ℝ)
    (hu : IsIntegralCurve u (variationalFieldVec A)) :
    IsIntegralCurve (fun t => c • u t) (variationalFieldVec A) := by
  intro t
  have h := (hu t).const_smul c
  simpa only [variationalFieldVec, map_smul] using h

/-!
### The fundamental solution operator `D_x Φ_t` as a bounded operator

Combining the superposition principle with the `C^0` uniqueness
(`variationalVec_eq_of_isIntegralCurve`) and the exponential a priori bound
(`dist_flow_apply_le`), the time-`t` flow map of the *linear* vector variational field is
additive, homogeneous, and operator-norm bounded, so it assembles into an honest bounded
operator `E →L[ℝ] E` — the fundamental solution / resolvent `D_x Φ_t` predicted by the
variational equation `u'(t) = A(t) (u(t))`.  Here `Φ : E → ℝ → E` is any flow family of
`variationalFieldVec A` anchored at `Φ x t₀ = x`.  This is the concrete `E →L[ℝ] E` object
— linear in the initial direction and with an explicit exponential operator bound — that
the compact-manifold gauge flow (Item 2) and the tensor time-derivative chain rule
(Item 1) ultimately consume.
-/

/-- **Additivity of the linear flow map.**  For a flow family `Φ` of the vector variational
field `variationalFieldVec A` (with `‖A t‖ ≤ K`) anchored at `Φ x t₀ = x`, the time-`t` map
`x ↦ Φ x t` is additive.  (Both `Φ (x + y)` and `t ↦ Φ x t + Φ y t` solve the same linear
ODE — the latter by superposition — and agree at the anchor `t₀`, so they agree everywhere
by uniqueness.) -/
theorem flow_variationalFieldVec_add {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x y : E) (t : ℝ) : Φ (x + y) t = Φ x t + Φ y t :=
  variationalVec_eq_of_isIntegralCurve hA (hΦ (x + y))
    (isIntegralCurve_variationalFieldVec_add (hΦ x) (hΦ y)) (t₁ := t₀) (by simp only [h0]) t

/-- **Homogeneity of the linear flow map.**  The time-`t` map `x ↦ Φ x t` commutes with
scalar multiplication: `Φ (c • x) t = c • Φ x t`. -/
theorem flow_variationalFieldVec_smul {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (c : ℝ) (x : E) (t : ℝ) : Φ (c • x) t = c • Φ x t :=
  variationalVec_eq_of_isIntegralCurve hA (hΦ (c • x))
    (isIntegralCurve_variationalFieldVec_smul c (hΦ x)) (t₁ := t₀) (by simp only [h0]) t

/-- **The linear flow map fixes the origin.**  `Φ 0 t = 0`: the zero direction has zero
directional derivative (the special case `c = 0` of homogeneity). -/
theorem flow_variationalFieldVec_zero {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : Φ 0 t = 0 := by
  have h := flow_variationalFieldVec_smul hA hΦ h0 (0 : ℝ) (0 : E) t
  simpa using h

/-- **Operator bound for the linear flow map.**  `‖Φ x t‖ ≤ exp (K · |t - t₀|) · ‖x‖`,
obtained from the `C^0` two-sided Lipschitz bound `dist_flow_apply_le` applied between the
initial values `x` and `0` together with `Φ 0 t = 0`.  This is the operator-norm bound that
makes the fundamental solution a *bounded* linear map. -/
theorem norm_flow_variationalFieldVec_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) : ‖Φ x t‖ ≤ Real.exp ((K : ℝ) * |t - t₀|) * ‖x‖ := by
  have hb := dist_flow_apply_le (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 x 0 t
  rw [flow_variationalFieldVec_zero hA hΦ h0 t, dist_zero_right, dist_zero_right] at hb
  calc ‖Φ x t‖ ≤ ‖x‖ * Real.exp ((K : ℝ) * |t - t₀|) := hb
    _ = Real.exp ((K : ℝ) * |t - t₀|) * ‖x‖ := mul_comm _ _

/-- **The fundamental solution operator `D_x Φ_t ∈ E →L[ℝ] E`.**  For a flow family `Φ` of
the linear vector variational field `variationalFieldVec A` (`‖A t‖ ≤ K`) anchored at
`Φ x t₀ = x`, the time-`t` flow map `x ↦ Φ x t` — additive, homogeneous, and bounded by
`exp (K · |t - t₀|)` — packaged as an honest bounded linear operator.  This is the concrete
resolvent / fundamental solution that the directional derivatives `∂_{u₀} Φ_t = W t u₀`
assemble into. -/
def fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => Φ x t
      map_add' := fun x y => flow_variationalFieldVec_add hA hΦ h0 x y t
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact flow_variationalFieldVec_smul hA hΦ h0 c x t }
    (Real.exp ((K : ℝ) * |t - t₀|))
    (fun x => norm_flow_variationalFieldVec_le hA hΦ h0 x t)

@[simp]
theorem fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (x : E) : fundamentalSolution hA hΦ h0 t x = Φ x t := rfl

/-- **The fundamental solution has operator norm at most `exp (K · |t - t₀|)`.**  The
quantitative bound `‖D_x Φ_t‖ ≤ exp (K · |t - t₀|)` on the resolvent, inherited from the
pointwise operator bound. -/
theorem norm_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : ‖fundamentalSolution hA hΦ h0 t‖ ≤ Real.exp ((K : ℝ) * |t - t₀|) := by
  exact LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- **The fundamental solution is the identity at the anchor time.**  `D_x Φ_{t₀} = 1`: the
resolvent from `t₀` to `t₀` is the identity operator, matching the initial condition
`W t₀ = 1` of the fundamental-solution equation. -/
theorem fundamentalSolution_anchor {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    fundamentalSolution hA hΦ h0 t₀ = ContinuousLinearMap.id ℝ E := by
  ext x
  rw [fundamentalSolution_apply, h0, ContinuousLinearMap.id_apply]

/-!
### The fundamental solution is bounded below and injective (a non-degenerate resolvent)

Dual to the operator bound: the *lower* exponential control `dist_flow_apply_ge` of the
`C^0` layer forces the linear flow map to be bounded below by `exp (-K · |t - t₀|)`.  Hence
the fundamental solution `D_x Φ_t` has a controlled left inverse on its image — it is
injective, the linear/operator shadow of the bi-Lipschitz embedding
`isUniformEmbedding_flow_apply`, and the resolvent is non-degenerate. -/

/-- **Lower operator bound for the linear flow map.**  `exp (-K · |t - t₀|) · ‖x‖ ≤ ‖Φ x t‖`,
from the `C^0` lower dependence bound `dist_flow_apply_ge` applied between `x` and `0` with
`Φ 0 t = 0`.  The resolvent cannot contract a direction faster than `exp (-K · |t - t₀|)`. -/
theorem norm_flow_variationalFieldVec_ge {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) : Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖ ≤ ‖Φ x t‖ := by
  have hb := dist_flow_apply_ge (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 x 0 t
  rw [flow_variationalFieldVec_zero hA hΦ h0 t, dist_zero_right, dist_zero_right] at hb
  calc Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖
      = ‖x‖ * Real.exp (-(K : ℝ) * |t - t₀|) := mul_comm _ _
    _ ≤ ‖Φ x t‖ := hb

/-- **The fundamental solution operator is bounded below.**
`exp (-K · |t - t₀|) · ‖x‖ ≤ ‖D_x Φ_t x‖`: the resolvent applied to a nonzero direction is
nonzero, with the reciprocal exponential lower bound. -/
theorem norm_fundamentalSolution_apply_ge {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) :
    Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖ ≤ ‖fundamentalSolution hA hΦ h0 t x‖ := by
  rw [fundamentalSolution_apply]
  exact norm_flow_variationalFieldVec_ge hA hΦ h0 x t

/-- **The fundamental solution operator is injective.**  Being bounded below, the resolvent
`D_x Φ_t ∈ E →L[ℝ] E` has trivial kernel — the operator shadow of the flow map being a
bi-Lipschitz embedding (`injective_flow_apply`).  This is the linear non-degeneracy that
makes the directional derivative assignment `u₀ ↦ D_x Φ_t u₀` faithful. -/
theorem fundamentalSolution_injective {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : Function.Injective (fundamentalSolution hA hΦ h0 t) := by
  intro x y hxy
  refine injective_flow_apply (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 t ?_
  simpa only [fundamentalSolution_apply] using hxy

/-!
### Identification with the operator-valued fundamental-matrix ODE

The `fundamentalSolution` built from the *vector* flow family coincides with any solution of
the *operator*-valued variational equation `W'(t) = A(t) ∘ W(t)` normalised by `W t₀ = 1`
(the fundamental matrix).  This ties the two variational ODEs together at the operator level:
whenever the operator fundamental matrix exists, it *is* the resolvent `D_x Φ_t`. -/

/-- **The resolvent equals the operator-valued fundamental matrix.**  If `W` solves the
operator variational ODE `W'(t) = A(t) ∘ W(t)` with `W t₀ = 1`, then for any vector flow
family `Φ` of `variationalFieldVec A` anchored at `Φ x t₀ = x`,
`fundamentalSolution hA hΦ h0 t = W t`.  (For each `x`, both `t ↦ Φ x t` and `t ↦ W t x`
solve the vector variational ODE — the latter by `isIntegralCurve_variational_apply` — and
agree at `t₀`, so they coincide by vector uniqueness.) -/
theorem fundamentalSolution_eq_of_operator_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W : ℝ → (E →L[ℝ] E)}
    (hW : IsIntegralCurve W (variationalField A))
    (hW0 : W t₀ = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : fundamentalSolution hA hΦ h0 t = W t := by
  ext x
  rw [fundamentalSolution_apply]
  refine variationalVec_eq_of_isIntegralCurve hA (hΦ x)
    (isIntegralCurve_variational_apply hW x) (t₁ := t₀) ?_ t
  rw [h0, hW0, ContinuousLinearMap.id_apply]

/-!
### Continuity of the resolvent action in time

Since the resolvent acts by `D_x Φ_t · u₀ = Φ u₀ t`, the `C^0` time/joint continuity of the
flow (`IsIntegralCurve.continuous`, `continuous_flow`) transfers verbatim to the fundamental
solution: `t ↦ D_x Φ_t u₀` is continuous, and the full action `(t, u₀) ↦ D_x Φ_t u₀` is jointly
continuous. -/

/-- **Strong continuity of the resolvent in time.**  For a fixed direction `u₀`, the path
`t ↦ D_x Φ_t · u₀` is continuous. -/
theorem continuous_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) : Continuous (fun t => fundamentalSolution hA hΦ h0 t u₀) := by
  simp only [fundamentalSolution_apply]
  exact (hΦ u₀).continuous

/-- **Joint continuity of the resolvent action.**  The map `(t, u₀) ↦ D_x Φ_t · u₀` is jointly
continuous on `ℝ × E`. -/
theorem continuous_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) := by
  simp only [fundamentalSolution_apply]
  exact continuous_flow (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0

/-!
### The resolvent's columns are the variational-ODE solutions

The action `t ↦ D_x Φ_t · u₀` is exactly the solution of the vector variational ODE through
`u₀` at `t₀`.  This is the characterisation a subsequent `C^1`-differentiability proof
consumes: it is precisely the fact that the candidate derivative `D_x Φ_t` applied to a
direction obeys the linearised equation with the correct initial value. -/

/-- **The resolvent columns solve the variational ODE.**  For each direction `u₀`, the path
`t ↦ D_x Φ_t · u₀` is an integral curve of the vector variational field `variationalFieldVec A`. -/
theorem isIntegralCurve_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) :
    IsIntegralCurve (fun t => fundamentalSolution hA hΦ h0 t u₀) (variationalFieldVec A) := by
  simp only [fundamentalSolution_apply]
  exact hΦ u₀

/-- **The resolvent recovers the initial direction at the anchor.**  `D_x Φ_{t₀} · u₀ = u₀`. -/
@[simp]
theorem fundamentalSolution_apply_anchor {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) : fundamentalSolution hA hΦ h0 t₀ u₀ = u₀ := by
  rw [fundamentalSolution_apply, h0]

/-- **The resolvent is canonical.**  Any two flow families `Φ`, `Ψ` of `variationalFieldVec A`
anchored at `t₀` give the same fundamental solution operator: the resolvent `D_x Φ_t` depends
only on the field `A` (and `t₀`, `t`), not on the choice of flow family used to build it.
(Immediate from vector uniqueness `variationalVec_eq_of_isIntegralCurve`.) -/
theorem fundamentalSolution_congr {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) (variationalFieldVec A))
    (h0Ψ : ∀ x, Ψ x t₀ = x) (t : ℝ) :
    fundamentalSolution hA hΦ h0 t = fundamentalSolution hA hΨ h0Ψ t := by
  ext x
  simp only [fundamentalSolution_apply]
  exact variationalVec_eq_of_isIntegralCurve hA (hΦ x) (hΨ x) (t₁ := t₀) (by rw [h0, h0Ψ]) t

/-!
### The linearisation-remainder Grönwall bound (the analytic core of `C¹` dependence)

The decisive estimate underlying *differentiable* dependence on initial data.  Let `f`, `g`
be two integral curves of a (possibly nonlinear) field `v`, and let `w` solve the vector
variational ODE `w'(s) = A(s) (w(s))` — the linearisation of `v` along the pair, with
`‖A s‖ ≤ K` — matching the *initial* separation exactly, `w t₀ = g t₀ - f t₀`.  If the
pointwise **linearisation defect** `‖v s (g s) - v s (f s) - A s (g s - f s)‖` is uniformly
`≤ δ`, then the linear prediction `w` tracks the true flow separation `g - f` to within
`gronwallBound 0 K δ |t - t₀|`.

The proof recognises the remainder `r := g - f - w` as an integral curve of the variational
field `variationalFieldVec A` **perturbed** by the (`δ`-bounded, `u`-independent) defect, and
compares it — via the two-sided perturbation Grönwall bound
`dist_le_of_isIntegralCurve_perturb` — to the zero solution, with which it shares its initial
value `r t₀ = 0`.  When `v` is `C¹` with `A s = D_x v (s, f s)` the defect is
`o(‖g s - f s‖) = o(‖g t₀ - f t₀‖)`, so `δ → 0` faster than the initial separation and this
bound upgrades to Fréchet differentiability of the flow with derivative the fundamental
solution `D_x Φ_t` — the `C¹` layer of the dependence tower.  Nothing about `v` beyond the two
integral curves and the defect bound is used (in particular `v` need not be Lipschitz). -/

/-- **Linearisation-remainder Grönwall bound.**  For two integral curves `f`, `g` of a field
`v`, a solution `w` of the vector variational ODE `w' = A(s) w` (`‖A s‖ ≤ K`) matching the
initial separation `w t₀ = g t₀ - f t₀`, and a uniform bound `δ` on the linearisation defect
`‖v s (g s) - v s (f s) - A s (g s - f s)‖`, the linear prediction `w` tracks the true flow
separation `g - f` to within `gronwallBound 0 K δ |t - t₀|`:
`‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ |t - t₀|`.  The analytic core of differentiable
dependence on initial data. -/
theorem norm_flow_sub_variational_le
    (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {w : ℝ → E} (hw : IsIntegralCurve w (variationalFieldVec A))
    {δ : ℝ} (hdefect : ∀ s, ‖v s (g s) - v s (f s) - A s (g s - f s)‖ ≤ δ)
    (hinit : w t₀ = g t₀ - f t₀) (t : ℝ) :
    ‖(g t - f t) - w t‖ ≤ gronwallBound 0 (K : ℝ) δ |t - t₀| := by
  -- the zero curve solves the (linear) vector variational ODE
  have hzero : IsIntegralCurve (fun _ : ℝ => (0 : E)) (variationalFieldVec A) := by
    intro s
    simpa only [variationalFieldVec, map_zero] using hasDerivAt_const (c := (0 : E)) (x := s)
  -- `r := g - f - w` solves the variational ODE perturbed by the (u-independent) defect
  have hr : IsIntegralCurve (fun s => g s - f s - w s)
      (fun s u => A s u + (v s (g s) - v s (f s) - A s (g s - f s))) := by
    intro s
    show HasDerivAt (fun s => g s - f s - w s)
        (A s (g s - f s - w s) + (v s (g s) - v s (f s) - A s (g s - f s))) s
    have hd := ((hg s).sub (hf s)).sub (hw s)
    convert hd using 1
    simp only [variationalFieldVec, map_sub]
    abel
  -- the base and perturbed fields differ by at most `δ`, uniformly in `(s, u)`
  have hpert : ∀ s u, dist (variationalFieldVec A s u)
      (A s u + (v s (g s) - v s (f s) - A s (g s - f s))) ≤ δ := by
    intro s u
    simp only [variationalFieldVec, dist_eq_norm]
    rw [show A s u - (A s u + (v s (g s) - v s (f s) - A s (g s - f s)))
          = -(v s (g s) - v s (f s) - A s (g s - f s)) from by abel, norm_neg]
    exact hdefect s
  -- compare `r` to the zero solution by the perturbation Grönwall bound
  have hkey := dist_le_of_isIntegralCurve_perturb
      (fun s => lipschitzWith_variationalFieldVec hA s) hzero hr hpert t₀ t
  simp only [dist_eq_norm, zero_sub, norm_neg] at hkey
  rw [show g t₀ - f t₀ - w t₀ = (0 : E) from by rw [hinit]; abel, norm_zero] at hkey
  exact hkey

/-- **Interval-restricted linearisation-remainder bound.**  The refinement of
`norm_flow_sub_variational_le` in which the linearisation defect need only be controlled on the
*forward interval* `Ico t₀ b`, not for all times.  For integral curves `f`, `g` of a field `v`,
a solution `w` of the variational ODE `w' = A(s) w` (`‖A s‖ ≤ K`) matching the initial
separation `w t₀ = g t₀ - f t₀`, and a bound `δ` on the defect
`‖v s (g s) - v s (f s) - A s (g s - f s)‖` *for `s ∈ Ico t₀ b`*, the linear prediction tracks
the flow separation on `Icc t₀ b`:
`‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ (t - t₀)`  for `t ∈ Icc t₀ b`.

This is the version differentiable dependence actually consumes: as the flow separation
`‖g s - f s‖` grows exponentially in `s`, the defect can only be made uniformly small on a
*compact* time interval (the tube around the reference trajectory), so a globally-uniform `δ`
is unavailable — but on `[t₀, b]` the `C¹` modulus of `v` does supply one.  Proved by comparing
the remainder `r := g - f - w` (an approximate solution of the variational field, defect `≤ δ`
on `Ico t₀ b`) against the exact zero solution via Mathlib's interval Grönwall estimate
`dist_le_of_approx_trajectories_ODE`. -/
theorem norm_flow_sub_variational_le_Icc
    (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {w : ℝ → E} (hw : IsIntegralCurve w (variationalFieldVec A))
    {δ b : ℝ}
    (hdefect : ∀ s ∈ Ico t₀ b, ‖v s (g s) - v s (f s) - A s (g s - f s)‖ ≤ δ)
    (hinit : w t₀ = g t₀ - f t₀) {t : ℝ} (ht : t ∈ Icc t₀ b) :
    ‖(g t - f t) - w t‖ ≤ gronwallBound 0 (K : ℝ) δ (t - t₀) := by
  -- the zero curve is the exact solution of the (linear) variational ODE
  have hzero : IsIntegralCurve (fun _ : ℝ => (0 : E)) (variationalFieldVec A) := by
    intro s
    simpa only [variationalFieldVec, map_zero] using hasDerivAt_const (c := (0 : E)) (x := s)
  -- the remainder `r := g - f - w`: its derivative and continuity
  have hrderiv : ∀ s, HasDerivAt (fun s => g s - f s - w s)
      (v s (g s) - v s (f s) - variationalFieldVec A s (w s)) s :=
    fun s => ((hg s).sub (hf s)).sub (hw s)
  have hrcont : Continuous (fun s => g s - f s - w s) :=
    (hg.continuous.sub hf.continuous).sub hw.continuous
  -- the remainder's derivative is `A`-linear up to the defect, uniformly `≤ δ` on `Ico t₀ b`
  have g_bound : ∀ s ∈ Ico t₀ b,
      dist (v s (g s) - v s (f s) - variationalFieldVec A s (w s))
        (variationalFieldVec A s (g s - f s - w s)) ≤ δ := by
    intro s hs
    have hdef : (v s (g s) - v s (f s) - variationalFieldVec A s (w s))
        - variationalFieldVec A s (g s - f s - w s)
        = v s (g s) - v s (f s) - A s (g s - f s) := by
      simp only [variationalFieldVec, map_sub]; abel
    rw [dist_eq_norm, hdef]
    exact hdefect s hs
  -- initial separation is predicted exactly, so the remainder starts at `0`
  have ha : dist ((fun _ : ℝ => (0 : E)) t₀) ((fun s => g s - f s - w s) t₀) ≤ (0 : ℝ) := by
    have h0 : g t₀ - f t₀ - w t₀ = (0 : E) := by rw [hinit]; abel
    simp only [h0, dist_self, le_refl]
  -- interval Grönwall: compare the remainder to the exact zero solution
  have key := dist_le_of_approx_trajectories_ODE (a := t₀) (b := b)
    (εf := 0) (εg := δ) (δ := 0)
    (fun s => lipschitzWith_variationalFieldVec hA s)
    hzero.continuous.continuousOn (fun s _ => (hzero s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    hrcont.continuousOn (fun s _ => (hrderiv s).hasDerivWithinAt)
    g_bound ha
  have hb := key t ht
  rw [zero_add] at hb
  simp only [dist_eq_norm, zero_sub, norm_neg] at hb
  exact hb

/-- **Homogeneity of the (zero-initial) Grönwall bound in the defect.**  For the vanishing
initial value, the Grönwall bound is *linear* in the perturbation size `ε`:
`gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x`.  (Immediate from the closed form
`ε/K · (exp (K x) - 1)`, resp. `ε · x` when `K = 0`.)  This is the algebraic step that turns
the linearisation-remainder bound `‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ (t - t₀)` into an
estimate *proportional* to the defect `δ`, so that a defect of order `o(‖g t₀ - f t₀‖)` yields
a remainder of the same order — the passage from the remainder bound to Fréchet
differentiability of the flow. -/
theorem gronwallBound_zero_left_mul (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  by_cases hK : K = 0
  · subst hK; simp only [gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK]; ring

/-- **Operator form of the interval remainder bound.**  The interval linearisation-remainder
bound `norm_flow_sub_variational_le_Icc` recast with the honest resolvent operator
`fundamentalSolution` (`D_x Φ_t`) as the linear prediction.  For the nonlinear flow family `Φ`
of `v` and the variational flow family `Φ'` of `variationalFieldVec A` (`‖A s‖ ≤ K`), the
difference between the actual flow separation `Φ y t - Φ x t` and its resolvent prediction
`D_x Φ_t · (y - x) = fundamentalSolution … t (y - x)` is controlled by the defect on the
forward interval:
`‖(Φ y t - Φ x t) - fundamentalSolution hA hΦ' h0' t (y - x)‖ ≤ gronwallBound 0 K δ (t - t₀)`
for `t ∈ Icc t₀ b`, whenever `‖v s (Φ y s) - v s (Φ x s) - A s (Φ y s - Φ x s)‖ ≤ δ` on
`Ico t₀ b`.  This is precisely the numerator of the Fréchet difference quotient for
`x ↦ Φ x t`, in the form its differentiability proof consumes. -/
theorem norm_flow_sub_fundamentalSolution_le_Icc
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x y : E) {δ b : ℝ}
    (hdefect : ∀ s ∈ Ico t₀ b,
      ‖v s (Φ y s) - v s (Φ x s) - A s (Φ y s - Φ x s)‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc t₀ b) :
    ‖(Φ y t - Φ x t) - fundamentalSolution hA hΦ' h0' t (y - x)‖
      ≤ gronwallBound 0 (K : ℝ) δ (t - t₀) := by
  have hw : IsIntegralCurve (fun s => fundamentalSolution hA hΦ' h0' s (y - x))
      (variationalFieldVec A) := isIntegralCurve_fundamentalSolution_apply hA hΦ' h0' (y - x)
  have hinit : (fun s => fundamentalSolution hA hΦ' h0' s (y - x)) t₀ = Φ y t₀ - Φ x t₀ := by
    simp only [fundamentalSolution_apply_anchor, h0]
  exact norm_flow_sub_variational_le_Icc (hΦ x) (hΦ y) hA hw hdefect hinit ht

/-!
### `C¹` dependence on initial data (conditional on a linearisation modulus)

Assembling the pieces, the flow map `x ↦ Φ x t` is **Fréchet differentiable** at a base point
`x₀`, with derivative the fundamental solution / resolvent `D_x Φ_t = fundamentalSolution … t`,
*provided* the linearisation defect along the reference trajectory is of order `o(‖z - x₀‖)` as
`z → x₀`, uniformly on the forward time interval.  This isolates the remaining analytic input
(the `C¹` modulus of the field `v`, which — via the mean-value form `‖v(b) - v(a) - D_x v(a)
(b - a)‖ ≤ o(‖b - a‖)` and the exponential flow-separation bound — supplies such a defect
modulus on a compact time tube) as a single clean hypothesis, and derives the differentiable
dependence from it.  The proof: the interval remainder bound
`norm_flow_sub_fundamentalSolution_le_Icc` gives `‖numerator z‖ ≤ gronwallBound 0 K (D z)
(t - t₀)`, the Grönwall homogeneity `gronwallBound_zero_left_mul` turns the right side into
`gronwallBound 0 K 1 (t - t₀) · D z`, so `numerator = O(D)`; composing with the hypothesis
`D = o(z - x₀)` yields `numerator = o(z - x₀)`, i.e. `HasFDerivAt`. -/

open Asymptotics in
/-- **`C¹` dependence of the flow on the initial condition (conditional on a defect modulus).**
For a nonlinear flow family `Φ` of `v`, the variational flow family `Φ'` of the linearisation
`variationalFieldVec A` (`‖A s‖ ≤ K`), a forward time `t ≥ t₀`, and a defect bound `D : E → ℝ`
with `0 ≤ D z` and `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z` on `Ico t₀ t`,
if the defect is little-o of the initial separation, `D =o[𝓝 x₀] (· - x₀)`, then
`x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent
`fundamentalSolution hA hΦ' h0' t = D_x Φ_t`.  The `C¹` layer of the dependence tower. -/
theorem hasFDerivAt_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  -- interval remainder bound + Grönwall homogeneity: the numerator is `O(D)`
  have hnum : ∀ z, ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
      ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * D z := by
    intro z
    have hb := norm_flow_sub_fundamentalSolution_le_Icc hA hΦ' h0' hΦ h0 x₀ z
      (hdefect z) (Set.mem_Icc.mpr ⟨ht0, le_refl t⟩)
    rwa [gronwallBound_zero_left_mul, mul_comm (D z)] at hb
  have hbig : (fun z => Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀))
      =O[𝓝 x₀] fun z => D z := by
    rw [isBigO_iff]
    refine ⟨gronwallBound 0 (K : ℝ) 1 (t - t₀), Filter.Eventually.of_forall (fun z => ?_)⟩
    show ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
        ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖D z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
    exact hnum z
  -- compose with `D =o (z - x₀)` to get the little-o numerator, i.e. `HasFDerivAt`
  exact HasFDerivAt.of_isLittleO (hbig.trans_isLittleO hDo)

open Asymptotics in
/-- **The flow map is differentiable at the base point** (under the defect-modulus hypothesis of
`hasFDerivAt_flow_of_defect_isLittleO`): `x ↦ Φ x t` is `DifferentiableAt ℝ` at `x₀`. -/
theorem differentiableAt_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect hDo).differentiableAt

open Asymptotics in
/-- **The Fréchet derivative of the flow map is the resolvent** (under the defect-modulus
hypothesis of `hasFDerivAt_flow_of_defect_isLittleO`):
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t = D_x Φ_t`.  The identification
consumed downstream: the spatial derivative of the flow *is* the fundamental solution operator. -/
theorem fderiv_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect hDo).fderiv

/-!
### Toward discharging the defect modulus: the mean-value defect bound

A step toward making `hasFDerivAt_flow_of_defect_isLittleO` *unconditional*: the linearisation
defect along the flow is bounded by the *oscillation* of the field's spatial derivative on the
segment joining the two trajectories, times the flow separation — which the exponential
dependence bound turns into `exp (K |s - t₀|) · ‖z - x₀‖`.  A subsequent Heine–Cantor argument on
the compact trajectory tube (uniform continuity of `D_x v`) makes the oscillation `C(z) → 0` as
`z → x₀`, delivering the `o(‖z - x₀‖)` hypothesis. -/

/-- **Defect ≤ (derivative oscillation) × (flow separation).**  If `v s` has spatial derivative
`Dv s` on the segment `[Φ x₀ s, Φ z s]` with `‖Dv s ξ - A s‖ ≤ C` there, then the mean-value
inequality bounds the linearisation defect by `C · ‖Φ z s - Φ x₀ s‖`, and the exponential
initial-data dependence `dist_flow_apply_le` bounds the separation by `exp (K |s - t₀|) · ‖z -
x₀‖`:
`‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C · (exp (K |s - t₀|) · ‖z - x₀‖)`.
The bridge from `C¹`-regularity of the field to the defect modulus consumed by
`hasFDerivAt_flow_of_defect_isLittleO`. -/
theorem norm_flow_defect_le_of_segment_oscillation
    (hv : ∀ τ, LipschitzWith K (v τ))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    {A : ℝ → (E →L[ℝ] E)} {Dv : ℝ → E → (E →L[ℝ] E)} {C : ℝ}
    (x₀ z : E) (s : ℝ)
    (hderiv : ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    (hbound : ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C) :
    ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
      ≤ C * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := by
  have hC : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hbound (Φ x₀ s) (left_mem_segment ℝ _ _))
  have hmv : ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C * ‖Φ z s - Φ x₀ s‖ :=
    (convex_segment (Φ x₀ s) (Φ z s)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hderiv hbound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
    have h := dist_flow_apply_le hv hΦ h0 z x₀ s
    rwa [dist_eq_norm, dist_eq_norm] at h
  refine hmv.trans ?_
  rw [mul_comm (Real.exp ((K : ℝ) * |s - t₀|)) (‖z - x₀‖)]
  exact mul_le_mul_of_nonneg_left hsep hC

/-!
### Asymptotic glue and the oscillation-driven `C¹` dependence theorem

The mean-value bound `norm_flow_defect_le_of_segment_oscillation` controls the linearisation
defect at each time `s` by `C · exp (K |s - t₀|) · ‖z - x₀‖`, where `C` is the oscillation of the
field's spatial derivative on the trajectory chord.  What `hasFDerivAt_flow_of_defect_isLittleO`
consumes is a *little-o* defect modulus.  The bridge is purely asymptotic: once a single
uniform-in-time oscillation modulus `C(z)` is available with `C(z) → 0` as `z → x₀`, the defect
bound is `(vanishing modulus) · ‖z - x₀‖`, which is `o(‖z - x₀‖)`.  This upgrades the conditional
`C¹` dependence to one whose only hypothesis is the *vanishing* of the uniform oscillation
modulus. -/

open Asymptotics Filter in
/-- **Little-o from a vanishing pointwise modulus.**  If `‖f x‖ ≤ g x · ‖u x‖` holds eventually
along `l` and the scalar modulus `g` tends to `0` along `l`, then `f =o[l] u`.  The asymptotic
glue turning a bound "`defect ≤ (modulus → 0) · separation`" into the little-o hypothesis
consumed by `hasFDerivAt_flow_of_defect_isLittleO`. -/
theorem isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
    {α : Type*} {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
    {l : Filter α} {f : α → F₁} {u : α → F₂} {g : α → ℝ}
    (hle : ∀ᶠ x in l, ‖f x‖ ≤ g x * ‖u x‖) (hg : Tendsto g l (𝓝 0)) :
    f =o[l] u := by
  rw [isLittleO_iff]
  intro c hc
  have hgc : ∀ᶠ x in l, g x < c := hg.eventually (Iio_mem_nhds hc)
  filter_upwards [hle, hgc] with x hx hgx
  exact hx.trans (mul_le_mul_of_nonneg_right hgx.le (norm_nonneg _))

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a vanishing uniform oscillation modulus.**  Let `Φ` be a
nonlinear flow family of `v`, `Φ'` the variational flow family of the linearisation
`variationalFieldVec A` (`‖A s‖ ≤ K`), and `t ≥ t₀`.  Suppose a *single, time-uniform* oscillation
modulus `C : E → ℝ` with `0 ≤ C z`, `C z → 0` as `z → x₀`, bounds the linearisation defect on
`Ico t₀ t` by `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C z · (exp (K |s - t₀|) ·
‖z - x₀‖)`.  Then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent
`fundamentalSolution … t = D_x Φ_t`.  This discharges the defect-modulus hypothesis of
`hasFDerivAt_flow_of_defect_isLittleO` down to the *vanishing* of the uniform oscillation modulus
(the residual `C¹`-regularity input, supplied by Heine–Cantor on the compact trajectory tube). -/
theorem hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set D : E → ℝ := fun z => C z * (Real.exp ((K : ℝ) * (t - t₀)) * ‖z - x₀‖) with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z =>
    mul_nonneg (hCnn z) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hdefect' : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z := by
    intro z s hs
    have hsle : |s - t₀| ≤ t - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hexple : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)
    refine (hdefect z s hs).trans ?_
    simp only [hD]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexple (norm_nonneg _)) (hCnn z)
  have hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀ := by
    refine isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
      (g := fun z => C z * Real.exp ((K : ℝ) * (t - t₀))) ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
      refine le_of_eq ?_
      simp only [hD]
      ring
    · simpa using hCto.mul_const (Real.exp ((K : ℝ) * (t - t₀)))
  exact hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect' hDo

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a vanishing uniform oscillation
modulus (the consumer-facing corollary of `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`):
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a vanishing uniform
oscillation modulus:
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect).fderiv

/-!
### From defect modulus to derivative oscillation: the `C¹`-regularity hypothesis

The final composable reduction: `norm_flow_defect_le_of_segment_oscillation` turns a bound on the
*oscillation of the field's spatial derivative on the trajectory chord* into the per-time defect
bound consumed by `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`.  Composing the two, the
`C¹` dependence of the flow reduces to a single hypothesis phrased purely in terms of the field:
the chord-oscillation `‖Dv s ξ - A s‖` (uniform in `s ∈ [t₀, t]`, over `ξ` on the chord
`[Φ x₀ s, Φ z s]`) vanishes as `z → x₀`.  This is exactly the modulus-of-continuity input a genuine
`C¹` field supplies via Heine–Cantor on the compact trajectory tube. -/

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a vanishing derivative chord-oscillation.**  With `Φ`, `Φ'`
the nonlinear/variational flow families and `t ≥ t₀`, suppose the field `v s` has spatial
derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`), and a single
uniform modulus `C : E → ℝ` with `0 ≤ C z`, `C z → 0` as `z → x₀`, bounds the derivative
oscillation `‖Dv s ξ - A s‖ ≤ C z` there.  Then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with
derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.  The mean-value bound
`norm_flow_defect_le_of_segment_oscillation` converts the oscillation into the defect modulus of
`hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`; the only residual input is the vanishing of
the derivative oscillation — a pure `C¹`-regularity statement about `v`. -/
theorem hasFDerivAt_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := fun z s hs =>
    norm_flow_defect_le_of_segment_oscillation hv hΦ h0 x₀ z s (hderiv z s hs) (hosc z s hs)
  exact hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a vanishing derivative
chord-oscillation: `DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hCnn
    hCto hosc).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a vanishing derivative
chord-oscillation: `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hCnn
    hCto hosc).fderiv

/-!
### Manufacturing the vanishing oscillation from a modulus of continuity

The final input to the `C¹` dependence tower is the *vanishing* of the derivative chord-oscillation.
For a `C¹` field this is furnished by a modulus of continuity `ω` of the spatial derivative
(uniform in `s ∈ [t₀, t]` on the compact trajectory tube, via Heine–Cantor): `ω` is nonnegative,
monotone, and vanishes at `0⁺`.  The two ingredients below turn such a modulus into the
hypotheses of `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`: the modulus composed with the
(exponentially controlled) flow separation still tends to `0`, and the chord-oscillation is bounded
by that composition. -/

open Filter in
/-- **A vanishing modulus composed with the vanishing scaled separation still vanishes.**  If
`ω → 0` along `𝓝[≥] 0` and `0 ≤ c`, then `z ↦ ω (c · ‖z - x₀‖)` tends to `0` as `z → x₀`.  The
"`C(z) → 0`" engine of the modulus-of-continuity route to `C¹` flow-dependence. -/
theorem tendsto_modulus_comp_norm_sub {ω : ℝ → ℝ} {c : ℝ} (x₀ : E)
    (hc : 0 ≤ c) (hω : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun z => ω (c * ‖z - x₀‖)) (𝓝 x₀) (𝓝 0) := by
  have hsep : Tendsto (fun z : E => c * ‖z - x₀‖) (𝓝 x₀) (𝓝[≥] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun z => Set.mem_Ici.mpr (mul_nonneg hc (norm_nonneg _))⟩
    have hnorm : Tendsto (fun z : E => ‖z - x₀‖) (𝓝 x₀) (𝓝 0) := by
      have hcont : Continuous fun z : E => ‖z - x₀‖ :=
        (continuous_id.sub continuous_const).norm
      simpa using hcont.tendsto x₀
    simpa using hnorm.const_mul c
  exact hω.comp hsep

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a uniform modulus of continuity of the spatial derivative.**
With `Φ`, `Φ'` the nonlinear/variational flow families and `t ≥ t₀`, suppose the field `v s` has
spatial derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`), and a single
nonnegative, monotone modulus `ω : ℝ → ℝ` vanishing at `0⁺` bounds the derivative oscillation there
by the distance to the anchor trajectory, `‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)`.  Then `x ↦ Φ x t`
is Fréchet differentiable at `x₀` with derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.
The chord points lie within `exp (K |s - t₀|) · ‖z - x₀‖` of `Φ x₀ s` (`dist_flow_apply_le`), so the
monotone modulus caps the oscillation by `C z := ω (exp (K (t - t₀)) · ‖z - x₀‖) → 0`
(`tendsto_modulus_comp_norm_sub`), discharging the hypothesis of
`hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`.  This is the `C¹`-regularity input in its
most usable form: a modulus of continuity for the field's spatial derivative. -/
theorem hasFDerivAt_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set C : E → ℝ := fun z => ω (c * ‖z - x₀‖) with hC
  have hCnn : ∀ z, 0 ≤ C z := fun z => hωnn _
  have hCto : Tendsto C (𝓝 x₀) (𝓝 0) := tendsto_modulus_comp_norm_sub x₀ hc0 hω0
  have hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z := by
    intro z s hs ξ hξ
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    calc ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖) := hmod z s hs ξ hξ
      _ ≤ ω (c * ‖z - x₀‖) := hωmono hle
      _ = C z := by simp only [hC]
  exact hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    hCnn hCto hosc

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a uniform modulus of continuity of
the spatial derivative: `DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn hωmono hω0
    hmod).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a uniform modulus of
continuity of the spatial derivative:
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn hωmono hω0
    hmod).fderiv

/-!
### The `C^{1,1}` specialisation: a Lipschitz spatial derivative

The most directly usable entry point: when the field's spatial derivative is *Lipschitz* on the
trajectory chords (uniformly in `s`), i.e. `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`, the linear modulus
`ω r = L · r⁺` (nonnegative, monotone, vanishing at `0⁺`) feeds
`hasFDerivAt_flow_of_uniform_deriv_modulus` directly.  This covers every smooth (`C^∞`) field — in
particular the intended Ricci-flow application, whose right-hand sides are smooth — so it is the
practical `C¹`-dependence theorem: no abstract modulus of continuity to supply, only a Lipschitz
constant for the derivative. -/

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a Lipschitz spatial derivative (`C^{1,1}`).**  If the field
`v s` has spatial derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`) and
the derivative oscillation there is Lipschitz in the distance to the anchor trajectory,
`‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` with `0 ≤ L` uniform in `s`, then `x ↦ Φ x t` is Fréchet
differentiable at `x₀` with derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.  The linear
modulus `ω r = L · max r 0` discharges `hasFDerivAt_flow_of_uniform_deriv_modulus`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  refine hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    (ω := fun r => L * max r 0) (fun r => mul_nonneg hL (le_max_right r 0)) ?_ ?_ ?_
  · intro a b hab
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) hL
  · have hbase : Tendsto (fun r : ℝ => L * r) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => L * r) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      exact h2.mono_left nhdsWithin_le_nhds
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [max_eq_left (Set.mem_Ici.mp hr)]
  · intro z s hs ξ hξ
    simpa [max_eq_left (norm_nonneg (ξ - Φ x₀ s))] using hlip z s hs ξ hξ

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a Lipschitz spatial derivative:
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a Lipschitz spatial
derivative: `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).fderiv

open Asymptotics Filter in
/-- **Global-derivative convenience form** of `hasFDerivAt_flow_of_lipschitz_deriv`.  Takes the
*global* Fréchet derivative `Dv s` of `v s` at every point (as a genuine `C¹` field provides,
`HasFDerivAt (v s) (Dv s ξ) ξ`) instead of the chord-restricted `HasFDerivWithinAt`; the chord
hypothesis follows by `HasFDerivAt.hasFDerivWithinAt`.  The single cleanest entry point to the
`C^1` flow-dependence tower for a smooth field with a spatially-Lipschitz derivative. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ :=
  hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0
    (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt) hL hlip

/-!
### Local (`∀ᶠ z in 𝓝 x₀`) refinements of the `C¹` dependence tower

Fréchet differentiability of `x ↦ Φ x t` at the base point `x₀` is a **local** property, so the
defect / oscillation / derivative-existence hypotheses of the theorems above need only hold for
initial conditions `z` in a *neighbourhood* of `x₀`, not for every `z : E`.  The following variants
weaken the global `∀ z` hypotheses to `∀ᶠ z in 𝓝 x₀` (the nonnegativity of the modulus and the
structural flow-family hypotheses stay global, being harmless / non-analytic).

This is the honest form consumed by a genuine smooth field: its spatial derivative `D_x v` is only
*locally* Lipschitz, so the global Lipschitz-derivative bound of `hasFDerivAt_flow_of_lipschitz_deriv`
generally fails, whereas its local counterpart `hasFDerivAt_flow_of_lipschitz_deriv_eventually`
holds on the neighbourhood of `x₀` where the local Lipschitz estimate is available. -/

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_defect_isLittleO`.**  The `C¹` dependence of the flow on
the initial condition, needing the defect bound `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
≤ D z` only for `z` in a neighbourhood of `x₀` (`∀ᶠ z in 𝓝 x₀`) rather than for every `z`.  Since
`HasFDerivAt` is determined by the behaviour of `z ↦ Φ z t` near `x₀`, the big-O numerator estimate
`numerator = O(D)` is an eventual (in `𝓝 x₀`) statement, so the eventual defect bound suffices. -/
theorem hasFDerivAt_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hbig : (fun z => Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀))
      =O[𝓝 x₀] fun z => D z := by
    rw [isBigO_iff]
    refine ⟨gronwallBound 0 (K : ℝ) 1 (t - t₀), ?_⟩
    filter_upwards [hdefect] with z hdefectz
    show ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
        ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖D z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
    have hb := norm_flow_sub_fundamentalSolution_le_Icc hA hΦ' h0' hΦ h0 x₀ z
      hdefectz (Set.mem_Icc.mpr ⟨ht0, le_refl t⟩)
    rwa [gronwallBound_zero_left_mul, mul_comm (D z)] at hb
  exact HasFDerivAt.of_isLittleO (hbig.trans_isLittleO hDo)

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** (local defect-modulus form):
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect
    hDo).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** (local defect-modulus form):
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t = D_x Φ_t`. -/
theorem fderiv_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect
    hDo).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`.**  The per-time defect
bound `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C z · (exp (K |s - t₀|) · ‖z - x₀‖)`,
with `C z → 0`, is required only for `z` in a neighbourhood of `x₀`.  Reduces to
`hasFDerivAt_flow_of_defect_isLittleO_eventually` with `D z = C z · exp (K (t - t₀)) · ‖z - x₀‖`. -/
theorem hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set D : E → ℝ := fun z => C z * (Real.exp ((K : ℝ) * (t - t₀)) * ‖z - x₀‖) with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z =>
    mul_nonneg (hCnn z) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hdefect' : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z := by
    filter_upwards [hdefect] with z hdefectz
    intro s hs
    have hsle : |s - t₀| ≤ t - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hexple : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)
    refine (hdefectz s hs).trans ?_
    simp only [hD]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexple (norm_nonneg _)) (hCnn z)
  have hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀ := by
    refine isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
      (g := fun z => C z * Real.exp ((K : ℝ) * (t - t₀))) ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
      refine le_of_eq ?_
      simp only [hD]
      ring
    · simpa using hCto.mul_const (Real.exp ((K : ℝ) * (t - t₀)))
  exact hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect' hDo

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_uniform_oscillation_tendsto_zero`. -/
theorem differentiableAt_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hCnn
    hCto hdefect).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_uniform_oscillation_tendsto_zero`. -/
theorem fderiv_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hCnn
    hCto hdefect).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`.**  The derivative
existence on trajectory chords and the chord-oscillation bound `‖Dv s ξ - A s‖ ≤ C z` (with
`C z → 0`) are required only for `z` in a neighbourhood of `x₀`.  The mean-value bound
`norm_flow_defect_le_of_segment_oscillation` converts them (eventually) into the defect modulus of
`hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually`. -/
theorem hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := by
    filter_upwards [hderiv, hosc] with z hderivz hoscz
    intro s hs
    exact norm_flow_defect_le_of_segment_oscillation hv hΦ h0 x₀ z s (hderivz s hs) (hoscz s hs)
  exact hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0
    hCnn hCto hdefect

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_segment_oscillation_tendsto_zero`. -/
theorem differentiableAt_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_segment_oscillation_tendsto_zero`. -/
theorem fderiv_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_uniform_deriv_modulus`.**  With a nonnegative, monotone
modulus `ω` vanishing at `0⁺`, the derivative existence on trajectory chords and the modulus bound
`‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)` are required only for `z` in a neighbourhood of `x₀`.  Same
proof as the global form (the chord points lie within `exp (K (t - t₀)) · ‖z - x₀‖` of the anchor,
so `C z := ω (exp (K (t - t₀)) · ‖z - x₀‖) → 0` caps the oscillation), feeding
`hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually`. -/
theorem hasFDerivAt_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set C : E → ℝ := fun z => ω (c * ‖z - x₀‖) with hC
  have hCnn : ∀ z, 0 ≤ C z := fun z => hωnn _
  have hCto : Tendsto C (𝓝 x₀) (𝓝 0) := tendsto_modulus_comp_norm_sub x₀ hc0 hω0
  have hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z := by
    filter_upwards [hmod] with z hmodz
    intro s hs ξ hξ
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    calc ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖) := hmodz s hs ξ hξ
      _ ≤ ω (c * ‖z - x₀‖) := hωmono hle
      _ = C z := by simp only [hC]
  exact hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_uniform_deriv_modulus`. -/
theorem differentiableAt_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn
    hωmono hω0 hmod).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_uniform_deriv_modulus`. -/
theorem fderiv_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn
    hωmono hω0 hmod).fderiv

/-!
### The local `C^{1,1}` entry point: a *locally* Lipschitz spatial derivative

The practical payoff of the localisation.  A genuine smooth field has a spatial derivative that is
only **locally** Lipschitz, so the global bound `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` of
`hasFDerivAt_flow_of_lipschitz_deriv` need not hold for *all* `z`.  It does hold, however, for `z`
ranging over a neighbourhood of `x₀` (where the chord `[Φ x₀ s, Φ z s]` stays inside the region on
which the local Lipschitz estimate is valid).  These `_eventually` forms are exactly what such a
field supplies, giving unconditional `C¹` dependence of the flow on initial data for every smooth
field. -/

open Asymptotics Filter in
/-- **Local `C^{1,1}` `C¹`-dependence.**  If the derivative oscillation is Lipschitz in the distance
to the anchor trajectory, `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`, for `z` in a neighbourhood of `x₀`,
then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent.  The linear
modulus `ω r = L · max r 0` discharges `hasFDerivAt_flow_of_uniform_deriv_modulus_eventually`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  refine hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    (ω := fun r => L * max r 0) (fun r => mul_nonneg hL (le_max_right r 0)) ?_ ?_ ?_
  · intro a b hab
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) hL
  · have hbase : Tendsto (fun r : ℝ => L * r) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => L * r) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      exact h2.mono_left nhdsWithin_le_nhds
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [max_eq_left (Set.mem_Ici.mp hr)]
  · filter_upwards [hlip] with z hlipz
    intro s hs ξ hξ
    simpa [max_eq_left (norm_nonneg (ξ - Φ x₀ s))] using hlipz s hs ξ hξ

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_lipschitz_deriv`. -/
theorem differentiableAt_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL
    hlip).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_lipschitz_deriv`. -/
theorem fderiv_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).fderiv

open Asymptotics Filter in
/-- **Global-derivative convenience form** of `hasFDerivAt_flow_of_lipschitz_deriv_eventually`.
Takes the *global* Fréchet derivative `HasFDerivAt (v s) (Dv s ξ) ξ` at every point (as a genuine
`C¹` field provides) instead of the chord-restricted `HasFDerivWithinAt`, so only the *local*
Lipschitz-derivative bound (`∀ᶠ z in 𝓝 x₀`) need be supplied.  The single cleanest entry point to
the `C¹` flow-dependence tower for a smooth field whose derivative is *locally* Lipschitz. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ :=
  hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    (Filter.Eventually.of_forall (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt)) hL hlip

open Filter in
/-- **`C¹` dependence from a spatial derivative Lipschitz on a ball around the anchor trajectory.**
The most directly consumable entry point for a smooth field on a chart: `v s` has a global spatial
derivative `Dv s` (`HasFDerivAt (v s) (Dv s ξ) ξ`), and on the fixed radius-`r` ball around each
anchor point `Φ x₀ s` (`s ∈ Ico t₀ t`) the derivative oscillation is `L`-Lipschitz in the distance
to the anchor, `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`.  Then `x ↦ Φ x t` is Fréchet differentiable at
`x₀` with derivative the resolvent.  A genuine `C^∞` field supplies exactly this — its derivative is
*locally* Lipschitz on balls — even when it is not *globally* Lipschitz-derivative.  The proof shows
that for `‖z - x₀‖ < r / exp (K (t - t₀))` every trajectory chord `[Φ x₀ s, Φ z s]` stays inside the
`r`-ball (flow separation `‖Φ z s - Φ x₀ s‖ ≤ exp (K (t - t₀)) ‖z - x₀‖`), so the ball estimate
supplies the *eventual* Lipschitz-derivative hypothesis of
`hasFDerivAt_flow_of_lipschitz_deriv_eventually`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  -- for `z` in the ball of radius `r / c`, every chord point stays in the `r`-ball around the anchor
  have hev : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ξ ∈ Metric.closedBall (Φ x₀ s) r := by
    filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : 0 < r / c)] with z hz
    intro s hs ξ hξ
    have hzlt : ‖z - x₀‖ < r / c := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    have hcrc : c * (r / c) = r := by field_simp
    have hlt : c * ‖z - x₀‖ < r := by
      have h := mul_lt_mul_of_pos_left hzlt hc0
      rwa [hcrc] at h
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (lt_of_le_of_lt hle hlt)
  refine hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    (Eventually.of_forall (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt)) hL ?_
  filter_upwards [hev] with z hzev
  intro s hs ξ hξ
  exact hlipball s hs ξ (hzev s hs ξ hξ)

open Filter in
/-- The flow map is differentiable at `x₀` from a ball-Lipschitz spatial derivative
(`hasFDerivAt_flow_of_lipschitz_deriv_on_ball`). -/
theorem differentiableAt_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv_on_ball hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hr hL
    hlipball).differentiableAt

open Filter in
/-- The Fréchet derivative of the flow map is the resolvent, from a ball-Lipschitz spatial
derivative (`hasFDerivAt_flow_of_lipschitz_deriv_on_ball`). -/
theorem fderiv_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv_on_ball hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hr hL
    hlipball).fderiv

/-!
### Continuous dependence of the resolvent on the coefficient field

The fundamental solution `D_x Φ_t` depends continuously — indeed Lipschitz-ly — on the coefficient
field `A`.  If two uniformly-`K`-bounded coefficients `A`, `A'` are uniformly `ε`-close,
`‖A s - A' s‖ ≤ ε`, then on a forward compact time interval `[t₀, T]` their resolvents differ in
operator norm by at most `ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)`.  The linearised
perturbation `‖(A s - A' s) u‖ ≤ ε ‖u‖` is *not uniform* in `u`, so this is not a corollary of the
uniform-field-perturbation bound `dist_flow_perturb_le`; instead it uses the a-priori trajectory
growth `‖Φ₂ u₀ s‖ ≤ exp (K (T - t₀)) ‖u₀‖` (`norm_flow_variationalFieldVec_le`) to turn the
per-point linearisation defect into a *uniform* one on the compact interval, then feeds Mathlib's
approximate-trajectory Grönwall estimate `dist_le_of_approx_trajectories_ODE`.  This is the
operator-level continuous dependence of the linearised flow / resolvent on its coefficient — an
input to the `C²` regularity of the flow in initial data (where `A` itself varies with the base
point) and to the continuous dependence of the DeTurck flow on the metric. -/

/-- **Nonnegativity of the unit Grönwall bound.**  `0 ≤ gronwallBound 0 K 1 x` for `0 ≤ K` and
`0 ≤ x`: on the diagonal `δ = 0`, `ε = 1`, the bound is `x` (if `K = 0`) or `(exp (K x) - 1)/K ≥ 0`
(if `K > 0`). -/
theorem gronwallBound_zero_one_nonneg {K x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) :
    0 ≤ gronwallBound 0 K 1 x := by
  rcases eq_or_lt_of_le hK with hK0 | hK0
  · rw [← hK0]
    simp only [gronwallBound_K0]
    simpa using hx
  · rw [gronwallBound_of_K_ne_0 (ne_of_gt hK0)]
    have hexp : (1 : ℝ) ≤ Real.exp (K * x) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hK0.le hx)
    have h1 : (0 : ℝ) ≤ Real.exp (K * x) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ 1 / K := by positivity
    simp only [zero_mul, zero_add]
    exact mul_nonneg h2 h1

/-- **Continuous dependence of the resolvent on the coefficient (directional form).**  For two
uniformly-`K`-bounded coefficient fields `A`, `A'` with variational flow families `Φ₁`, `Φ₂`, and
`‖A s - A' s‖ ≤ ε` for all `s`, the resolvents applied to a fixed direction `u₀` satisfy, on the
forward compact interval `[t₀, T]`,
`‖D_x Φ_t^A u₀ - D_x Φ_t^{A'} u₀‖ ≤ ε · exp (K (T - t₀)) · ‖u₀‖ · gronwallBound 0 K 1 (t - t₀)`.
The `A'`-column `s ↦ Φ₂ u₀ s` is treated as an approximate solution of the `A`-field, its
linearisation defect `‖(A' s - A s)(Φ₂ u₀ s)‖ ≤ ε · exp (K (T - t₀)) · ‖u₀‖` uniform on `[t₀, T]`. -/
theorem norm_fundamentalSolution_sub_apply_le_of_forall_le
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hAA' : ∀ s, ‖A s - A' s‖ ≤ ε)
    (u₀ : E) {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t u₀ - fundamentalSolution hA' hΦ₂ h2 t u₀‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  set εg : ℝ := ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ with hεg
  have hgbound : ∀ s ∈ Ico t₀ T,
      dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s)) ≤ εg := by
    intro s hs
    have hsle : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hgnorm : ‖Φ₂ u₀ s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ := by
      refine (norm_flow_variationalFieldVec_le hA' hΦ₂ h2 u₀ s).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)) (norm_nonneg _)
    have hcoeff : ‖A' s - A s‖ ≤ ε := by
      rw [show A' s - A s = -(A s - A' s) by abel, norm_neg]; exact hAA' s
    calc dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s))
        = ‖(A' s - A s) (Φ₂ u₀ s)‖ := by
          simp only [variationalFieldVec, dist_eq_norm, ContinuousLinearMap.sub_apply]
      _ ≤ ‖A' s - A s‖ * ‖Φ₂ u₀ s‖ := (A' s - A s).le_opNorm _
      _ ≤ ε * (Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖) :=
          mul_le_mul hcoeff hgnorm (norm_nonneg _) (le_trans (norm_nonneg _) hcoeff)
      _ = εg := by rw [hεg]; ring
  have key := dist_le_of_approx_trajectories_ODE
    (v := variationalFieldVec A) (a := t₀) (b := T)
    (f := fun s => Φ₁ u₀ s) (g := fun s => Φ₂ u₀ s)
    (f' := fun s => variationalFieldVec A s (Φ₁ u₀ s))
    (g' := fun s => variationalFieldVec A' s (Φ₂ u₀ s))
    (εf := 0) (εg := εg) (δ := 0) (K := K)
    (fun s => lipschitzWith_variationalFieldVec hA s)
    (hΦ₁ u₀).continuous.continuousOn
    (fun s _ => (hΦ₁ u₀ s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    (hΦ₂ u₀).continuous.continuousOn
    (fun s _ => (hΦ₂ u₀ s).hasDerivWithinAt)
    hgbound
    (by simp [h1, h2])
  have hb := key t ht
  rw [zero_add, gronwallBound_zero_left_mul] at hb
  rw [fundamentalSolution_apply, fundamentalSolution_apply, ← dist_eq_norm]
  exact hb

/-- **Operator-norm continuous dependence of the resolvent on the coefficient.**  Assembling the
directional bound `norm_fundamentalSolution_sub_apply_le_of_forall_le` over all unit directions:
for coefficient fields `A`, `A'` (both `≤ K`) with `‖A s - A' s‖ ≤ ε`, the resolvents satisfy
`‖D_x Φ_t^A - D_x Φ_t^{A'}‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.
The resolvent is thus a (locally) Lipschitz function of its coefficient field. -/
theorem norm_fundamentalSolution_sub_le_of_forall_le
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A s - A' s‖ ≤ ε)
    {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t - fundamentalSolution hA' hΦ₂ h2 t‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun u₀ => ?_)
  · exact mul_nonneg (mul_nonneg hε (Real.exp_pos _).le)
      (gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1))
  · rw [ContinuousLinearMap.sub_apply]
    refine (norm_fundamentalSolution_sub_apply_le_of_forall_le hA hA' hΦ₁ h1 hΦ₂ h2 hAA' u₀ ht).trans
      (le_of_eq ?_)
    ring

/-- **Operator-norm local Lipschitz continuity of the resolvent in time.**  Beyond the
strong (fixed-direction) continuity `continuous_fundamentalSolution_apply`, the fundamental
solution is Lipschitz in time in the *operator* norm on every bounded time window: for any
two times `t₁`, `t₂`,
`‖D_x Φ_{t₂} - D_x Φ_{t₁}‖ ≤ K · exp (K · max |t₁ - t₀| |t₂ - t₀|) · |t₂ - t₁|`.  Each
resolvent column `s ↦ Φ u s` solves the variational ODE `u' = A s (u s)`, so the
one-dimensional mean-value inequality bounds its increment by the supremum over the time
window of `‖A s (Φ u s)‖ ≤ K · exp (K |s - t₀|) · ‖u‖`; the exponential is maximised at an
endpoint (`abs_le_max_abs_abs`), and taking the operator-norm supremum over unit directions
gives the stated bound.  This upgrades the resolvent path `t ↦ D_x Φ_t` from strongly
continuous to norm-continuous — an input to the `C^k` bootstrap (continuity of the resolvent
in time) and to Bochner integration of the resolvent in the parabolic theory. -/
theorem norm_fundamentalSolution_sub_le_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t₁ t₂ : ℝ) :
    ‖fundamentalSolution hA hΦ h0 t₂ - fundamentalSolution hA hΦ h0 t₁‖
      ≤ (K : ℝ) * Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * |t₂ - t₁| := by
  set C : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg K.coe_nonneg (Real.exp_pos _).le
  have habs : ∀ σ ∈ Set.uIcc t₁ t₂, |σ - t₀| ≤ max |t₁ - t₀| |t₂ - t₀| := by
    intro σ hσ
    rcases le_total t₁ t₂ with h | h
    · rw [Set.uIcc_of_le h, Set.mem_Icc] at hσ
      obtain ⟨hσ1, hσ2⟩ := hσ
      exact abs_le_max_abs_abs (by linarith) (by linarith)
    · rw [Set.uIcc_of_ge h, Set.mem_Icc] at hσ
      obtain ⟨hσ1, hσ2⟩ := hσ
      rw [max_comm]
      exact abs_le_max_abs_abs (by linarith) (by linarith)
  have key : ∀ u : E, ‖Φ u t₂ - Φ u t₁‖ ≤ C * |t₂ - t₁| * ‖u‖ := by
    intro u
    have hderiv : ∀ σ ∈ Set.uIcc t₁ t₂,
        HasDerivWithinAt (Φ u) (A σ (Φ u σ)) (Set.uIcc t₁ t₂) σ :=
      fun σ _ => (hΦ u σ).hasDerivWithinAt
    have hbound : ∀ σ ∈ Set.uIcc t₁ t₂, ‖A σ (Φ u σ)‖ ≤ C * ‖u‖ := by
      intro σ hσ
      have hAσ : ‖A σ‖ ≤ (K : ℝ) := by exact_mod_cast hA σ
      have hexp : Real.exp ((K : ℝ) * |σ - t₀|)
          ≤ Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (habs σ hσ) K.coe_nonneg)
      have hΦσ : ‖Φ u σ‖ ≤ Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * ‖u‖ :=
        (norm_flow_variationalFieldVec_le hA hΦ h0 u σ).trans
          (mul_le_mul_of_nonneg_right hexp (norm_nonneg u))
      calc ‖A σ (Φ u σ)‖ ≤ ‖A σ‖ * ‖Φ u σ‖ := (A σ).le_opNorm _
        _ ≤ (K : ℝ) * (Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * ‖u‖) :=
            mul_le_mul hAσ hΦσ (norm_nonneg _) K.coe_nonneg
        _ = C * ‖u‖ := by rw [hCdef]; ring
    have hmv : ‖Φ u t₂ - Φ u t₁‖ ≤ C * ‖u‖ * |t₂ - t₁| := by
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
        (convex_uIcc t₁ t₂) left_mem_uIcc right_mem_uIcc
      rwa [Real.norm_eq_abs] at h
    calc ‖Φ u t₂ - Φ u t₁‖ ≤ C * ‖u‖ * |t₂ - t₁| := hmv
      _ = C * |t₂ - t₁| * ‖u‖ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 (abs_nonneg _)) (fun u => ?_)
  simp only [ContinuousLinearMap.sub_apply, fundamentalSolution_apply]
  exact key u

/-- **The resolvent path is norm-continuous in time.**  `t ↦ D_x Φ_t` is a continuous curve in
the operator Banach space `E →L[ℝ] E`, not merely strongly (fixed-direction) continuous:
immediate from the operator-norm local-Lipschitz bound `norm_fundamentalSolution_sub_le_time` by
squeezing the distance `‖D_x Φ_a - D_x Φ_t‖` between `0` and the vanishing bound
`K · exp (K · max |t - t₀| |a - t₀|) · |a - t| → 0`.  This norm-continuity of the resolvent as a
curve of operators is the input consumed when Bochner-integrating the resolvent along time (the
Duhamel/variation-of-constants representation) in the parabolic theory. -/
theorem continuous_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun t => fundamentalSolution hA hΦ h0 t) := by
  rw [continuous_iff_continuousAt]
  intro t
  show Filter.Tendsto (fun a => fundamentalSolution hA hΦ h0 a) (𝓝 t)
    (𝓝 (fundamentalSolution hA hΦ h0 t))
  rw [tendsto_iff_dist_tendsto_zero]
  have hgcont : Continuous
      (fun a => (K : ℝ) * Real.exp ((K : ℝ) * max |t - t₀| |a - t₀|) * |a - t|) := by
    fun_prop
  have hgt : (K : ℝ) * Real.exp ((K : ℝ) * max |t - t₀| |t - t₀|) * |t - t| = 0 := by simp
  refine squeeze_zero (fun a => dist_nonneg) (fun a => ?_) (hgcont.tendsto' t 0 hgt)
  rw [dist_eq_norm]
  exact norm_fundamentalSolution_sub_le_time hA hΦ h0 t a

open Asymptotics Filter in
/-- **The fundamental solution solves the operator-valued variational ODE (`W' = A W`).**  For a
*norm-continuous* coefficient path `A` (`‖A t‖ ≤ K`), the resolvent `t ↦ D_x Φ_t` is
differentiable in the operator norm with
`d/dt (D_x Φ_t) = A t ∘ (D_x Φ_t)`.  This is genuine *operator-norm* (not merely strong)
differentiability: the linearisation-remainder is controlled uniformly over unit directions.
Proof: each column `s ↦ Φ u s` solves the vector ODE `u' = A s (u s)`, so the operator
Taylor remainder applied to `u` is, by the one-dimensional mean-value inequality, bounded by
`‖s - t‖ · (sup over the chord of ‖A σ ∘ D_x Φ_σ - A t ∘ D_x Φ_t‖) · ‖u‖`; the operator-norm
supremum over `u` and the norm-continuity of `σ ↦ A σ ∘ D_x Φ_σ`
(`continuous_fundamentalSolution_time` composed with `Continuous A`) drive the remainder to
`o(‖s - t‖)`. -/
theorem hasDerivAt_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    HasDerivAt (fun s => fundamentalSolution hA hΦ h0 s)
      ((A t).comp (fundamentalSolution hA hΦ h0 t)) t := by
  set W : ℝ → (E →L[ℝ] E) := fun s => fundamentalSolution hA hΦ h0 s with hWdef
  set H : ℝ → (E →L[ℝ] E) := fun σ => (A σ).comp (W σ) with hHdef
  have hHcont : Continuous H :=
    hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hUnhds : {σ : ℝ | ‖H σ - H t‖ < ε} ∈ 𝓝 t := by
    refine (isOpen_lt ((hHcont.sub continuous_const).norm) continuous_const).mem_nhds ?_
    simpa using hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hUnhds
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hε.le (norm_nonneg _)) (fun u => ?_)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  have hderiv : ∀ σ ∈ Set.uIcc t s,
      HasDerivWithinAt (fun σ => W σ u - (σ - t) • (A t (W t u)))
        (A σ (W σ u) - A t (W t u)) (Set.uIcc t s) σ := by
    intro σ _
    have hcol : HasDerivAt (fun σ => W σ u) (A σ (W σ u)) σ :=
      isIntegralCurve_fundamentalSolution_apply hA hΦ h0 u σ
    have hlin : HasDerivAt (fun σ => (σ - t) • (A t (W t u))) (A t (W t u)) σ := by
      simpa using (((hasDerivAt_id σ).sub (hasDerivAt_const σ t)).smul_const (A t (W t u)))
    exact (hcol.sub hlin).hasDerivWithinAt
  have hbound : ∀ σ ∈ Set.uIcc t s, ‖A σ (W σ u) - A t (W t u)‖ ≤ ε * ‖u‖ := by
    intro σ hσ
    have hσδ : dist σ t < δ := by
      have h1 : dist σ t ≤ dist t s := Real.dist_le_of_mem_uIcc hσ left_mem_uIcc
      rw [dist_comm t s] at h1
      exact lt_of_le_of_lt h1 hs
    have hHσ : ‖H σ - H t‖ < ε := hball (Metric.mem_ball.mpr hσδ)
    have heq : A σ (W σ u) - A t (W t u) = (H σ - H t) u := by
      simp only [hHdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [heq]
    calc ‖(H σ - H t) u‖ ≤ ‖H σ - H t‖ * ‖u‖ := (H σ - H t).le_opNorm u
      _ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_right hHσ.le (norm_nonneg u)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc t s) left_mem_uIcc right_mem_uIcc
  have hφeq : (fun σ => W σ u - (σ - t) • (A t (W t u))) s
      - (fun σ => W σ u - (σ - t) • (A t (W t u))) t
      = W s u - W t u - (s - t) • (A t (W t u)) := by
    simp only [sub_self, zero_smul, sub_zero]
    abel
  rw [hφeq] at hmv
  exact hmv.trans (le_of_eq (by ring))

open Filter in
/-- **The resolvent path is the operator integral curve of the variational field.**  Packaged
form of `hasDerivAt_fundamentalSolution`: for a norm-continuous `A`, the curve `t ↦ D_x Φ_t` is a
global integral curve of the operator variational field `variationalField A` (`W ↦ A t ∘ W`).
Together with `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`) this is the full characterisation of
the fundamental solution as *the* solution of the operator ODE `W' = A W`, `W t₀ = 1` — the
statement `fundamentalSolution_eq_of_operator_isIntegralCurve` consumes hypothetically, now
discharged.  It also makes the operator resolvent's own dynamics available to the `C^k` bootstrap. -/
theorem isIntegralCurve_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    IsIntegralCurve (fun t => fundamentalSolution hA hΦ h0 t) (variationalField A) :=
  fun t => hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t

/-- **A priori velocity bound for the resolvent path.**  The time-derivative of the resolvent —
the right-hand side `A t ∘ D_x Φ_t` of the operator ODE `hasDerivAt_fundamentalSolution` — has
operator norm at most `K · exp (K · |t - t₀|)`: the resolvent curve moves through operator space
with speed controlled by the same exponential that bounds the resolvent itself.  Immediate from
submultiplicativity of the operator norm and `norm_fundamentalSolution_le`. -/
theorem norm_comp_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    ‖(A t).comp (fundamentalSolution hA hΦ h0 t)‖ ≤ (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) := by
  refine (ContinuousLinearMap.opNorm_comp_le (A t) (fundamentalSolution hA hΦ h0 t)).trans ?_
  refine mul_le_mul ?_ (norm_fundamentalSolution_le hA hΦ h0 t) (norm_nonneg _) K.coe_nonneg
  exact_mod_cast hA t

open MeasureTheory intervalIntegral in
/-- **The fundamental solution satisfies the Volterra / Duhamel integral equation.**  For a
*norm-continuous* coefficient path `A` (`‖A t‖ ≤ K`), the resolvent `t ↦ D_x Φ_t` obeys the
integral form of the operator variational ODE `W' = A W`, `W t₀ = 1`:
`D_x Φ_t = 1 + ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`.  This is the fixed-point / Picard characterisation of
the fundamental solution: applying the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) to the operator ODE
`hasDerivAt_fundamentalSolution` — whose right-hand side `σ ↦ A σ ∘ D_x Φ_σ` is norm-continuous
(`hAcont.clm_comp continuous_fundamentalSolution_time`), hence interval-integrable — and folding in
the anchor `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`) turns the differential equation into its
Volterra integral equation.  This is the operator-Duhamel identity underlying differentiable
dependence of the resolvent on its coefficient field (the second-order variational equation) toward
the `C^k` bootstrap. -/
theorem fundamentalSolution_eq_one_add_integral {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    fundamentalSolution hA hΦ h0 t
      = 1 + ∫ σ in t₀..t, (A σ).comp (fundamentalSolution hA hΦ h0 σ) := by
  have hHcont : Continuous (fun σ => (A σ).comp (fundamentalSolution hA hΦ h0 σ)) :=
    hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)
  have hderiv : ∀ σ ∈ Set.uIcc t₀ t,
      HasDerivAt (fun s => fundamentalSolution hA hΦ h0 s)
        ((A σ).comp (fundamentalSolution hA hΦ h0 σ)) σ :=
    fun σ _ => hasDerivAt_fundamentalSolution hA hAcont hΦ h0 σ
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hHcont.intervalIntegrable t₀ t)
  rw [fundamentalSolution_anchor hA hΦ h0] at hint
  rw [hint, ← ContinuousLinearMap.one_def]
  abel

open MeasureTheory intervalIntegral in
/-- **The resolvent is close to the identity near the anchor.**  Quantitative "resolvent `≈ 1`"
bound: `‖D_x Φ_t - 1‖ ≤ K · exp (K · |t - t₀|) · |t - t₀|`, so the resolvent departs from the
identity operator at most linearly (times the exponential) in the elapsed time, vanishing as
`t → t₀`.  Immediate from the Volterra identity `fundamentalSolution_eq_one_add_integral`
(`D_x Φ_t - 1 = ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`) and the a-priori velocity bound
`norm_comp_fundamentalSolution_le` (`‖A σ ∘ D_x Φ_σ‖ ≤ K · exp (K · |σ - t₀|)`), whose integrand is
`≤ K · exp (K · |t - t₀|)` on the time window `Ι t₀ t` (`|σ - t₀| ≤ |t - t₀|`), integrated by
`intervalIntegral.norm_integral_le_of_norm_le_const`.  This is the operator-Duhamel short-time
estimate underlying the contraction/invertibility of the resolvent for small `|t - t₀|`. -/
theorem norm_fundamentalSolution_sub_one_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    ‖fundamentalSolution hA hΦ h0 t - 1‖
      ≤ (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| := by
  rw [fundamentalSolution_eq_one_add_integral hA hAcont hΦ h0 t, add_sub_cancel_left]
  refine intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|)) ?_
  intro σ hσ
  refine (norm_comp_fundamentalSolution_le hA hΦ h0 σ).trans ?_
  have hσle : |σ - t₀| ≤ |t - t₀| := by
    have hmem : σ ∈ Set.uIcc t₀ t := Set.uIoc_subset_uIcc hσ
    have := Real.dist_le_of_mem_uIcc hmem Set.left_mem_uIcc
    simpa [Real.dist_eq, abs_sub_comm] using this
  gcongr

/-- **The resolvent is invertible whenever it is within distance `1` of the identity.**  If
`‖D_x Φ_t - 1‖ < 1` then the resolvent `D_x Φ_t` is a unit of the operator ring `E →L[ℝ] E` (an
invertible bounded operator), by the Neumann-series openness of the units around `1`
(`Units.oneSub`).  This is the operator/inverse-function-theorem shadow of the bi-Lipschitz
embedding: on top of `fundamentalSolution_injective` (injectivity) it provides a genuine two-sided
operator inverse. -/
theorem isUnit_fundamentalSolution_of_norm_sub_one_lt {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (ht : ‖fundamentalSolution hA hΦ h0 t - 1‖ < 1) :
    IsUnit (fundamentalSolution hA hΦ h0 t) := by
  have h1 : ‖1 - fundamentalSolution hA hΦ h0 t‖ < 1 := by rwa [norm_sub_rev]
  exact sub_sub_self 1 (fundamentalSolution hA hΦ h0 t) ▸
    (Units.oneSub (1 - fundamentalSolution hA hΦ h0 t) h1).isUnit

/-- **Short-time invertibility of the resolvent.**  For a norm-continuous coefficient `A`, whenever
the elapsed-time bound `K · exp (K · |t - t₀|) · |t - t₀| < 1` holds the resolvent `D_x Φ_t` is a
unit of `E →L[ℝ] E`.  Combines the short-time closeness `norm_fundamentalSolution_sub_one_le`
(`‖D_x Φ_t - 1‖ ≤ K · exp (K · |t - t₀|) · |t - t₀|`) with the Neumann-series invertibility
`isUnit_fundamentalSolution_of_norm_sub_one_lt`; in particular the flow map `x ↦ Φ x t` is a linear
isomorphism for all `t` close enough to `t₀` — the local-diffeomorphism input for the compact
manifold gauge flow of Item 2. -/
theorem isUnit_fundamentalSolution_of_time_lt {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (ht : (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| < 1) :
    IsUnit (fundamentalSolution hA hΦ h0 t) :=
  isUnit_fundamentalSolution_of_norm_sub_one_lt hA hΦ h0 t
    (lt_of_le_of_lt (norm_fundamentalSolution_sub_one_le hA hAcont hΦ h0 t) ht)

open MeasureTheory intervalIntegral in
/-- **Duhamel difference formula for the resolvent.**  For two norm-continuous coefficient fields
`A₁`, `A₂` (both `‖·‖ ≤ K`) with variational flow families `Φ₁`, `Φ₂`, the difference of the two
resolvents obeys the variation-of-parameters identity
`D_x Φ₁_t - D_x Φ₂_t = ∫_{t₀}^{t} A₁ σ ∘ (D_x Φ₁_σ - D_x Φ₂_σ) dσ + ∫_{t₀}^{t} (A₁ σ - A₂ σ) ∘ D_x Φ₂_σ dσ`.
Subtracting the two Volterra equations `fundamentalSolution_eq_one_add_integral` cancels the
identities, and the integrand difference `A₁ ∘ W₁ - A₂ ∘ W₂ = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`
(bilinearity of composition, `comp_sub`/`sub_comp`) splits the single integral into the two Duhamel
terms — the "homogeneous propagation of the resolvent gap" plus the "source term from the coefficient
gap".  As `A₂ → A₁` the first term is `O(‖W₁ - W₂‖)` and the second is the leading `(A₁ - A₂)`
contribution, so this identity is the exact ancestor of the *differentiable* dependence of the
resolvent on its coefficient field (the second-order variational equation) toward the `C^k`
bootstrap. -/
theorem fundamentalSolution_sub_eq_integral {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E] {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    (t : ℝ) :
    fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t
      = (∫ σ in t₀..t, (A₁ σ).comp
            (fundamentalSolution hA₁ hΦ₁ h0₁ σ - fundamentalSolution hA₂ hΦ₂ h0₂ σ))
        + ∫ σ in t₀..t, (A₁ σ - A₂ σ).comp (fundamentalSolution hA₂ hΦ₂ h0₂ σ) := by
  set W₁ := fundamentalSolution hA₁ hΦ₁ h0₁ with hW₁
  set W₂ := fundamentalSolution hA₂ hΦ₂ h0₂ with hW₂
  have hcW₁ : Continuous W₁ := continuous_fundamentalSolution_time hA₁ hΦ₁ h0₁
  have hcW₂ : Continuous W₂ := continuous_fundamentalSolution_time hA₂ hΦ₂ h0₂
  have hi1 : IntervalIntegrable (fun σ => (A₁ σ).comp (W₁ σ)) volume t₀ t :=
    (hA₁cont.clm_comp hcW₁).intervalIntegrable t₀ t
  have hi2 : IntervalIntegrable (fun σ => (A₂ σ).comp (W₂ σ)) volume t₀ t :=
    (hA₂cont.clm_comp hcW₂).intervalIntegrable t₀ t
  have hi3 : IntervalIntegrable (fun σ => (A₁ σ).comp (W₁ σ - W₂ σ)) volume t₀ t :=
    (hA₁cont.clm_comp (hcW₁.sub hcW₂)).intervalIntegrable t₀ t
  have hi4 : IntervalIntegrable (fun σ => (A₁ σ - A₂ σ).comp (W₂ σ)) volume t₀ t :=
    ((hA₁cont.sub hA₂cont).clm_comp hcW₂).intervalIntegrable t₀ t
  have hV₁ : W₁ t = 1 + ∫ σ in t₀..t, (A₁ σ).comp (W₁ σ) :=
    fundamentalSolution_eq_one_add_integral hA₁ hA₁cont hΦ₁ h0₁ t
  have hV₂ : W₂ t = 1 + ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ) :=
    fundamentalSolution_eq_one_add_integral hA₂ hA₂cont hΦ₂ h0₂ t
  rw [hV₁, hV₂]
  have hlhs : (1 + ∫ σ in t₀..t, (A₁ σ).comp (W₁ σ))
      - (1 + ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ))
      = (∫ σ in t₀..t, (A₁ σ).comp (W₁ σ)) - ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ) := by abel
  rw [hlhs, ← intervalIntegral.integral_sub hi1 hi2,
    ← intervalIntegral.integral_add hi3 hi4]
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

/-- **The time-derivative of the resolvent path is `A t ∘ D_x Φ_t`.**  The explicit `deriv` form of
the operator variational ODE `hasDerivAt_fundamentalSolution`: for a norm-continuous coefficient
`A`, `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t`.  A convenience readout for regularity consumers that
work with `deriv` rather than `HasDerivAt`. -/
theorem deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    deriv (fun s => fundamentalSolution hA hΦ h0 s) t
      = (A t).comp (fundamentalSolution hA hΦ h0 t) :=
  (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t).deriv

/-- **The resolvent path is `C¹` in time as an operator-valued curve.**  For a norm-continuous
coefficient `A`, the curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is continuously differentiable
(`ContDiff ℝ 1`): it is differentiable everywhere (`hasDerivAt_fundamentalSolution`) with derivative
`t ↦ A t ∘ D_x Φ_t`, which is norm-continuous
(`hAcont.clm_comp continuous_fundamentalSolution_time`).  The packaged regularity — as opposed to the
raw `HasDerivAt` + continuity pieces — is what higher-order (`C^k`) consumers compose against. -/
theorem contDiff_one_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ 1 (fun s => fundamentalSolution hA hΦ h0 s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t).differentiableAt, ?_⟩
  have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
      = fun t => (A t).comp (fundamentalSolution hA hΦ h0 t) :=
    funext fun t => deriv_fundamentalSolution hA hAcont hΦ h0 t
  rw [hd]
  exact hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)

open MeasureTheory intervalIntegral in
/-- **A priori bound on a resolvent-forcing integral (the Duhamel source term).**  For any
operator-valued path `B` with `‖B σ‖ ≤ ε` (`0 ≤ ε`),
`‖∫_{t₀}^{t} B σ ∘ D_x Φ_σ dσ‖ ≤ ε · exp (K · |t - t₀|) · |t - t₀|`.  Applied with `B = A₁ - A₂` this
bounds the inhomogeneous "source term" of the Duhamel difference formula
`fundamentalSolution_sub_eq_integral` — the leading-order response of the resolvent to a coefficient
perturbation of size `ε`.  Proof: pointwise `‖B σ ∘ D_x Φ_σ‖ ≤ ‖B σ‖ · ‖D_x Φ_σ‖ ≤ ε · exp (K · |σ -
t₀|) ≤ ε · exp (K · |t - t₀|)` (operator-norm submultiplicativity, `norm_fundamentalSolution_le`, and
`|σ - t₀| ≤ |t - t₀|` on the window `Ι t₀ t`), integrated by
`intervalIntegral.norm_integral_le_of_norm_le_const`. -/
theorem norm_integral_comp_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {ε : ℝ}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (hε : 0 ≤ ε) (B : ℝ → (E →L[ℝ] E)) (hB : ∀ σ, ‖B σ‖ ≤ ε) (t : ℝ) :
    ‖∫ σ in t₀..t, (B σ).comp (fundamentalSolution hA hΦ h0 σ)‖
      ≤ ε * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const
    (C := ε * Real.exp ((K : ℝ) * |t - t₀|)) ?_
  intro σ hσ
  have hσle : |σ - t₀| ≤ |t - t₀| := by
    have hmem : σ ∈ Set.uIcc t₀ t := Set.uIoc_subset_uIcc hσ
    have := Real.dist_le_of_mem_uIcc hmem Set.left_mem_uIcc
    simpa [Real.dist_eq, abs_sub_comm] using this
  refine (ContinuousLinearMap.opNorm_comp_le (B σ) (fundamentalSolution hA hΦ h0 σ)).trans ?_
  refine (mul_le_mul (hB σ) (norm_fundamentalSolution_le hA hΦ h0 σ) (norm_nonneg _) hε).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) hε

/-- **Time-regularity bootstrap of the resolvent (finite order).**  If the coefficient path `A`
is `C^n` in time (`ContDiff ℝ n A`), then the resolvent curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is
`C^{n+1}` in time.  Proof by induction on `n`: the base case (`n = 0`, i.e. norm-continuous `A`
⟹ `C¹` resolvent) is `contDiff_one_fundamentalSolution`; the inductive step reads the resolvent's
derivative off the operator ODE `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t`
(`deriv_fundamentalSolution`) — a composition of the `C^{n+1}` field `A` with the (inductively)
`C^{n+1}` resolvent, hence itself `C^{n+1}` via `ContDiff.clm_comp`, so `deriv W ∈ C^{n+1}` and
therefore `W ∈ C^{n+2}` by `contDiff_succ_iff_deriv`.  This is the time-direction half of the
`C^k` resolvent regularity that the Ricci-flow / DeTurck `C^k` bootstrap consumes. -/
theorem contDiff_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) A →
      ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun s => fundamentalSolution hA hΦ h0 s) := by
  intro n
  induction n with
  | zero =>
    intro hA0
    have hc : Continuous A := hA0.continuous
    simpa using contDiff_one_fundamentalSolution hA hc hΦ h0
  | succ n ih =>
    intro hAn1
    have hc : Continuous A := hAn1.continuous
    have hAn : ContDiff ℝ (n : WithTop ℕ∞) A :=
      hAn1.of_le (by exact_mod_cast Nat.le_succ n)
    have hWn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun s => fundamentalSolution hA hΦ h0 s) := by
      rw [Nat.cast_add_one]; exact ih hAn
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_fundamentalSolution hA hc hΦ h0 t).differentiableAt, ?_, ?_⟩
    · simp
    · have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
          = fun t => (A t).comp (fundamentalSolution hA hΦ h0 t) :=
        funext fun t => deriv_fundamentalSolution hA hc hΦ h0 t
      rw [hd]
      exact hAn1.clm_comp hWn

open scoped ContDiff in
/-- **Time-regularity of the resolvent: a smooth coefficient gives a smooth resolvent.**  If the
coefficient path `A` is `C^∞` in time, then so is the resolvent curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E`.
`C^∞`-ness is tested order by order (`contDiff_infty`): for every `n`, `A ∈ C^n` (indeed `C^∞`),
so the finite bootstrap `contDiff_fundamentalSolution_time` gives `W ∈ C^{n+1} ⊆ C^n`. -/
theorem contDiff_infty_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ ∞ (fun s => fundamentalSolution hA hΦ h0 s) := by
  rw [contDiff_infty]
  intro n
  exact (contDiff_fundamentalSolution_time hA hΦ h0 n (contDiff_infty.mp hAsmooth n)).of_le
    le_self_add

/-- **Time-regularity of the resolvent action (a pushforward of a fixed vector).**  For a `C^n`
coefficient path `A`, the resolvent *action* `t ↦ D_x Φ_t · u₀ = Φ u₀ t ∈ E` — the pushforward of a
fixed initial vector `u₀` along the flow — is `C^{n+1}` in time.  Immediate from the operator-level
bootstrap `contDiff_fundamentalSolution_time` composed with evaluation at `u₀` (a continuous linear
map, `ContDiff.clm_apply` against `contDiff_const`).  This is the form the tensor time-derivative
chain rule of Item 1 consumes for the pushforward legs `Φ_t · u`, `Φ_t · v`. -/
theorem contDiff_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) (u₀ : E) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  (contDiff_fundamentalSolution_time hA hΦ h0 n hAdiff).clm_apply contDiff_const

open scoped ContDiff in
/-- **Smoothness of the resolvent action.**  If the coefficient path `A` is `C^∞` in time then so
is the resolvent action `t ↦ D_x Φ_t · u₀`. -/
theorem contDiff_infty_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) (u₀ : E) :
    ContDiff ℝ ∞ (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  (contDiff_infty_fundamentalSolution_time hA hAsmooth hΦ h0).clm_apply contDiff_const

/-- **The second-order time equation of the resolvent (its "acceleration").**  For a `C¹`
coefficient path `A` — supplied as `A' = deriv A`, `HasDerivAt A (A' t) t` — the velocity field of
the resolvent, `t ↦ A t ∘ D_x Φ_t` (`= deriv (t ↦ D_x Φ_t)` by `deriv_fundamentalSolution`), is
itself differentiable with
`d/dt (A t ∘ D_x Φ_t) = A' t ∘ D_x Φ_t + A t ∘ (A t ∘ D_x Φ_t)`.  This is the operator product
rule `HasDerivAt.clm_comp` applied to `A t ∘ D_x Φ_t`, using the first-order operator ODE
`hasDerivAt_fundamentalSolution` for the second factor; equivalently, the resolvent is `C²` in time
with this explicit second derivative — the `k = 2` instance of the `C^k` bootstrap made concrete. -/
theorem hasDerivAt_deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {A' : ℝ → (E →L[ℝ] E)} (hA' : ∀ t, HasDerivAt A (A' t) t) (t : ℝ) :
    HasDerivAt (fun s => (A s).comp (fundamentalSolution hA hΦ h0 s))
      ((A' t).comp (fundamentalSolution hA hΦ h0 t)
        + (A t).comp ((A t).comp (fundamentalSolution hA hΦ h0 t))) t :=
  (hA' t).clm_comp (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t)

/-- **Explicit second time-derivative of the resolvent.**  The `deriv`-readout of
`hasDerivAt_deriv_fundamentalSolution`: for a `C¹` coefficient `A`,
`deriv (deriv (t ↦ D_x Φ_t)) t = A' t ∘ D_x Φ_t + A t ∘ (A t ∘ D_x Φ_t)`, the closed form of the
resolvent's second time derivative (the operator ODE differentiated once more). -/
theorem deriv_deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {A' : ℝ → (E →L[ℝ] E)} (hA' : ∀ t, HasDerivAt A (A' t) t) (t : ℝ) :
    deriv (deriv (fun s => fundamentalSolution hA hΦ h0 s)) t
      = (A' t).comp (fundamentalSolution hA hΦ h0 t)
        + (A t).comp ((A t).comp (fundamentalSolution hA hΦ h0 t)) := by
  have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
      = fun s => (A s).comp (fundamentalSolution hA hΦ h0 s) :=
    funext fun s => deriv_fundamentalSolution hA hAcont hΦ h0 s
  rw [hd]
  exact (hasDerivAt_deriv_fundamentalSolution hA hAcont hΦ h0 hA' t).deriv

/-- **Time-regularity of an integral curve.**  An integral curve `γ` of a field `v : ℝ → E → E`
that is jointly `C^n` in `(time, space)` (`ContDiff ℝ n (Function.uncurry v)`) is `C^{n+1}` in time.
Proof by induction on `n`: `γ` solves `γ'(t) = v t (γ t) = (↿v) (t, γ t)`, the composition of the
(inductively) `C^{n+1}` map `t ↦ (t, γ t)` with the `C^{n+1}` field `↿v`, hence itself `C^{n+1}`; so
`γ` is differentiable with a `C^{n+1}` derivative, i.e. `C^{n+2}` (`contDiff_succ_iff_deriv`).  The
base case is joint continuity of `↿v`, giving a `C¹` curve (`contDiff_one_iff_deriv`).  Unlike the
resolvent bootstrap this holds for a general (nonlinear) field, so it also delivers the
time-regularity of the *base* gauge flow `t ↦ Φ x t` that Item 2's compact-manifold flow uses. -/
theorem contDiff_of_isIntegralCurve {γ : ℝ → E} (hγ : IsIntegralCurve γ v) :
    ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v) →
      ContDiff ℝ ((n : WithTop ℕ∞) + 1) γ := by
  have hderiv : deriv γ = fun t => v t (γ t) := funext fun t => (hγ t).deriv
  have hdiff : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  intro n
  induction n with
  | zero =>
    intro hv0
    have hcont : ContDiff ℝ (1 : WithTop ℕ∞) γ := by
      rw [contDiff_one_iff_deriv]
      refine ⟨hdiff, ?_⟩
      rw [hderiv]
      exact hv0.continuous.comp (continuous_id.prodMk hγ.continuous)
    simpa using hcont
  | succ n ih =>
    intro hvn1
    have hvn : ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v) :=
      hvn1.of_le (by exact_mod_cast Nat.le_succ n)
    have hγcn1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) γ := by
      rw [Nat.cast_add_one]; exact ih hvn
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiff, ?_, ?_⟩
    · simp
    · rw [hderiv]
      exact hvn1.comp (contDiff_id.prodMk hγcn1)

open scoped ContDiff in
/-- **Smoothness of an integral curve.**  An integral curve of a jointly-`C^∞` field is `C^∞` in
time (order-by-order via `contDiff_infty` and the finite bootstrap). -/
theorem contDiff_infty_of_isIntegralCurve {γ : ℝ → E} (hγ : IsIntegralCurve γ v)
    (huv : ContDiff ℝ ∞ (Function.uncurry v)) : ContDiff ℝ ∞ γ := by
  rw [contDiff_infty]
  intro n
  exact (contDiff_of_isIntegralCurve hγ n (contDiff_infty.mp huv n)).of_le le_self_add

/-- **Time-regularity of the base flow.**  Each trajectory `t ↦ Ψ x t` of a flow family of a
jointly-`C^n` field is `C^{n+1}` in time — the specialisation of `contDiff_of_isIntegralCurve` to a
flow family, the form Item 2's compact-manifold gauge flow consumes for the time direction. -/
theorem contDiff_flow_time {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (n : ℕ) (huv : ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v)) (x : E) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun t => Ψ x t) :=
  contDiff_of_isIntegralCurve (hΨ x) n huv

open scoped ContDiff in
/-- **Smoothness of the base flow.**  Each trajectory `t ↦ Ψ x t` of a flow family of a
jointly-`C^∞` field is `C^∞` in time. -/
theorem contDiff_infty_flow_time {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (huv : ContDiff ℝ ∞ (Function.uncurry v)) (x : E) :
    ContDiff ℝ ∞ (fun t => Ψ x t) :=
  contDiff_infty_of_isIntegralCurve (hΨ x) huv

/-- **Joint regularity of the resolvent action in (time, vector).**  For a `C^n` coefficient path
`A`, the pushforward map `(t, u₀) ↦ D_x Φ_t · u₀` is jointly `C^{n+1}` on `ℝ × E`.  The resolvent
operator curve `t ↦ D_x Φ_t` is `C^{n+1}` (`contDiff_fundamentalSolution_time`), pulled back along the
projection `Prod.fst`, then evaluated against the smooth `Prod.snd` through the bounded-bilinear
(hence smooth) evaluation map (`ContDiff.clm_apply`).  So the flow pushforward is regular jointly in
the flow time and the pushed vector. -/
theorem contDiff_fundamentalSolution_apply_joint {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1)
      (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) :=
  ((contDiff_fundamentalSolution_time hA hΦ h0 n hAdiff).comp contDiff_fst).clm_apply contDiff_snd

open scoped ContDiff in
/-- **Joint smoothness of the resolvent action.**  For a `C^∞` coefficient `A`, the pushforward
`(t, u₀) ↦ D_x Φ_t · u₀` is jointly `C^∞` on `ℝ × E`. -/
theorem contDiff_infty_fundamentalSolution_apply_joint {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) :=
  ((contDiff_infty_fundamentalSolution_time hA hAsmooth hΦ h0).comp contDiff_fst).clm_apply
    contDiff_snd

/-!
### Differentiable dependence of the resolvent on its coefficient field

The Duhamel difference formula `fundamentalSolution_sub_eq_integral` is the *integral* form of the
equation governing the resolvent gap `W₁ - W₂` of two coefficient fields.  Its *differential* form —
the inhomogeneous operator ODE for the gap — starts the second-order variational analysis:
*differentiable* dependence of the resolvent on its coefficient field. -/

/-- **Differential form of the Duhamel gap equation.**  For norm-continuous coefficient fields `A₁`,
`A₂` (`‖·‖ ≤ K`) with variational flow families and resolvents `W₁ = D_x Φ₁`, `W₂ = D_x Φ₂`, the gap
`t ↦ W₁ t - W₂ t` solves the inhomogeneous operator ODE
`d/dt (W₁ - W₂) = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`.  This is the differential (`HasDerivAt`) form of
the integral identity `fundamentalSolution_sub_eq_integral`: subtract the two operator ODEs
`W₁' = A₁ ∘ W₁`, `W₂' = A₂ ∘ W₂` (`hasDerivAt_fundamentalSolution`) and regroup via bilinearity of
composition, `A₁ ∘ W₁ - A₂ ∘ W₂ = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`.  The homogeneous part
`A₁ ∘ (W₁ - W₂)` propagates the gap; the source `(A₁ - A₂) ∘ W₂` is the leading
coefficient-perturbation forcing — the second-order variational equation is built on this. -/
theorem hasDerivAt_fundamentalSolution_sub {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    (t : ℝ) :
    HasDerivAt (fun s => fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)
      ((A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t)
        + (A₁ t - A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t)) t := by
  have h1 := hasDerivAt_fundamentalSolution hA₁ hA₁cont hΦ₁ h0₁ t
  have h2 := hasDerivAt_fundamentalSolution hA₂ hA₂cont hΦ₂ h0₂ t
  have heq : (A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t)
        + (A₁ t - A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t)
      = (A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t)
        - (A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [heq]
  exact h1.sub h2

/-- **Second-order variational estimate — quantitative differentiability of the resolvent in its
coefficient field.**  Let `A₁`, `A₂` be norm-continuous coefficient fields (`‖·‖ ≤ K`) with
resolvents `W₁ = D_x Φ₁`, `W₂ = D_x Φ₂`, and let the coefficient gap be `ε`-small,
`‖A₁ s - A₂ s‖ ≤ ε`.  If `V` is the *first variation* — a solution of the inhomogeneous operator ODE
`V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂` anchored at `V t₀ = 0` (the leading linear response of the resolvent
to the coefficient perturbation `A₁ - A₂`) — then the resolvent gap agrees with its linear prediction
`V` to **second order**:
`‖(W₁ t - W₂ t) - V t‖ ≤ ε² · exp (K (T - t₀)) · (gronwallBound 0 K 1 (T - t₀))²` on `[t₀, T]`.

Proof: the remainder `R := (W₁ - W₂) - V` satisfies the *homogeneous* variational ODE with a
quadratically-small forcing, `R' = A₂ ∘ R + (A₁ - A₂) ∘ (W₁ - W₂)`, obtained by subtracting the
first-variation ODE from the gap ODE `hasDerivAt_fundamentalSolution_sub` — the two `(A₁ - A₂) ∘ W₂`
source terms cancel — with `R t₀ = 0`.  The forcing is `O(ε²)` since
`‖(A₁ - A₂) ∘ (W₁ - W₂)‖ ≤ ε · ‖W₁ - W₂‖` and the gap is itself `O(ε)` by the first-order Lipschitz
bound `norm_fundamentalSolution_sub_le_of_forall_le`.  Grönwall's inequality
(`norm_le_gronwallBound_of_norm_deriv_right_le`) then bounds `‖R t‖` by
`gronwallBound 0 K Γ (t - t₀) = Γ · gronwallBound 0 K 1 (t - t₀)` with the `O(ε²)` forcing constant
`Γ`.  This is the second-order variational equation underlying *differentiable* dependence of the
resolvent on its coefficient field — the base-point `C²`/`C^k` bootstrap for the flow. -/
theorem norm_fundamentalSolution_sub_sub_variation_le
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A₁ s - A₂ s‖ ≤ ε)
    {V : ℝ → (E →L[ℝ] E)}
    (hVderiv : ∀ s, HasDerivAt V
      ((A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)) s)
    (hV0 : V t₀ = 0)
    {T t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      ≤ ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have ht0T : t₀ ≤ T := le_trans ht.1 ht.2
  have hg0 : 0 ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg hKr (sub_nonneg.mpr ht0T)
  set R : ℝ → (E →L[ℝ] E) :=
    fun s => (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) - V s
    with hRdef
  have hcR : Continuous R := by
    rw [hRdef]
    exact ((continuous_fundamentalSolution_time hA₁ hΦ₁ h0₁).sub
      (continuous_fundamentalSolution_time hA₂ hΦ₂ h0₂)).sub
      (continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt))
  have hR0 : R t₀ = 0 := by
    rw [hRdef]
    simp [fundamentalSolution_anchor hA₁ hΦ₁ h0₁, fundamentalSolution_anchor hA₂ hΦ₂ h0₂, hV0]
  set Γ : ℝ := ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)
    with hΓdef
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef]; exact mul_nonneg (mul_nonneg (sq_nonneg ε) (Real.exp_pos _).le) hg0
  have hgap : ∀ s ∈ Set.Icc t₀ T,
      ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖
        ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    refine (norm_fundamentalSolution_sub_le_of_forall_le hA₁ hA₂ hΦ₁ h0₁ hΦ₂ h0₂ hε hAA' hs).trans ?_
    exact mul_le_mul_of_nonneg_left
      (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [hs.2]))
      (mul_nonneg hε (Real.exp_pos _).le)
  have hRderiv : ∀ s, HasDerivAt R
      ((A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)) s := by
    intro s
    have hgs := (hasDerivAt_fundamentalSolution_sub hA₁ hA₁cont hA₂ hA₂cont hΦ₁ h0₁ hΦ₂ h0₂ s).sub
      (hVderiv s)
    have hval :
        (A₁ s).comp (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)
        - ((A₂ s).comp (V s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s))
        = (A₂ s).comp (R s) + (A₁ s - A₂ s).comp
          (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) := by
      rw [hRdef]
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    rwa [hval] at hgs
  have ha : ‖R t₀‖ ≤ 0 := by simp [hR0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
        ≤ (K : ℝ) * ‖R s‖ + Γ := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t₀ T := ⟨hs.1, le_trans hs.2.le ht.2⟩
    have hA₂s : ‖A₂ s‖ ≤ (K : ℝ) := by exact_mod_cast hA₂ s
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(A₂ s).comp (R s)‖ ≤ ‖A₂ s‖ * ‖R s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖R s‖ := mul_le_mul_of_nonneg_right hA₂s (norm_nonneg _)
    · calc ‖(A₁ s - A₂ s).comp
              (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
            ≤ ‖A₁ s - A₂ s‖
              * ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * (ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) :=
            mul_le_mul (hAA' s) (hgap s hsIcc) (norm_nonneg _) hε
        _ = Γ := by rw [hΓdef]; ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcR.continuousOn (fun x _ => (hRderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      = ‖R t‖ := by rw [hRdef]
    _ ≤ gronwallBound 0 (K : ℝ) Γ (t - t₀) := hgron
    _ = Γ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := gronwallBound_zero_left_mul _ _ _
    _ ≤ Γ * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
        mul_le_mul_of_nonneg_left
          (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [ht.2])) hΓ0
    _ = ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
        rw [hΓdef]; ring

/-- **A-priori `O(ε)` bound on the first variation of the resolvent.**  The first variation `V` — the
solution of the inhomogeneous operator ODE `V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂`, `V t₀ = 0`, i.e. the
leading linear response of the resolvent `W₂ = D_x Φ₂` to a coefficient perturbation `A₁ - A₂` of
size `ε` — is itself `O(ε)`:
`‖V t‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Together with the
second-order estimate `norm_fundamentalSolution_sub_sub_variation_le` (`‖(W₁ - W₂) - V‖ = O(ε²)`)
this exhibits the resolvent gap as `W₁ - W₂ = V + O(ε²)` with linear leading term `V = O(ε)` — so `V`
is genuinely the (Gateaux) derivative of the resolvent in the coefficient direction `A₁ - A₂`.  Proof:
the forcing `(A₁ - A₂) ∘ W₂` has norm `≤ ε · ‖W₂ s‖ ≤ ε · exp (K (T - t₀))` (operator
submultiplicativity, `norm_fundamentalSolution_le`, and `|s - t₀| ≤ T - t₀`), whence
`‖V' s‖ ≤ K · ‖V s‖ + ε · exp (K (T - t₀))`, and Grönwall
(`norm_le_gronwallBound_of_norm_deriv_right_le`) closes it. -/
theorem norm_fundamentalSolution_variation_le
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {Φ₂ : E → ℝ → E}
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A₁ s - A₂ s‖ ≤ ε)
    {V : ℝ → (E →L[ℝ] E)}
    (hVderiv : ∀ s, HasDerivAt V
      ((A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)) s)
    (hV0 : V t₀ = 0)
    {T t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖ ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hcV : Continuous V := continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have ha : ‖V t₀‖ ≤ 0 := by simp [hV0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
        ≤ (K : ℝ) * ‖V s‖ + ε * Real.exp ((K : ℝ) * (T - t₀)) := by
    intro s hs
    have hA₂s : ‖A₂ s‖ ≤ (K : ℝ) := by exact_mod_cast hA₂ s
    have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [hs.2, ht.2]) hKr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(A₂ s).comp (V s)‖ ≤ ‖A₂ s‖ * ‖V s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖V s‖ := mul_le_mul_of_nonneg_right hA₂s (norm_nonneg _)
    · calc ‖(A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
            ≤ ‖A₁ s - A₂ s‖ * ‖fundamentalSolution hA₂ hΦ₂ h0₂ s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) :=
            mul_le_mul (hAA' s)
              ((norm_fundamentalSolution_le hA₂ hΦ₂ h0₂ s).trans hexp) (norm_nonneg _) hε
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcV.continuousOn (fun x _ => (hVderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖V t‖
      ≤ gronwallBound 0 (K : ℝ) (ε * Real.exp ((K : ℝ) * (T - t₀))) (t - t₀) := hgron
    _ = ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
        gronwallBound_zero_left_mul _ _ _

/-!
### Linearity and uniqueness of the first variation

The second-order variational estimates above (`norm_fundamentalSolution_sub_sub_variation_le`,
`norm_fundamentalSolution_variation_le`) take the *first variation* `V` — a solution of the
inhomogeneous operator ODE `V' = A ∘ V + F` anchored at `V t₀ = 0` — as a hypothesis.  Here `F` is
the coefficient-perturbation forcing `(A₁ - A₂) ∘ W₂`, *linear* in the perturbation `A₁ - A₂`.  The
lemmas below establish that the map `F ↦ V` (equivalently `perturbation ↦ V`) is a genuine
**linear** and **single-valued** assignment: the inhomogeneous variational ODE is linear, so its
solution set is closed under addition and scalar multiplication (superposition), and Grönwall
uniqueness pins the anchored solution down.  This is exactly the linearity-in-perturbation that
upgrades the Gateaux estimate `W₁ - W₂ = V + O(ε²)` toward an honest *bounded linear* Gateaux/Fréchet
derivative of the resolvent `A ↦ D_x Φ_t` in its coefficient field — the algebraic backbone of the
base-point `C^k` bootstrap. -/

/-- **Superposition (additivity) for the inhomogeneous variational ODE.**  If `V₁` solves
`V₁' = A ∘ V₁ + F₁` and `V₂` solves `V₂' = A ∘ V₂ + F₂` (the first-variation ODEs with forcings
`F₁`, `F₂`), then their sum solves the ODE with the summed forcing,
`(V₁ + V₂)' = A ∘ (V₁ + V₂) + (F₁ + F₂)`.  Linearity of the operator ODE: add the two `HasDerivAt`
statements and regroup via bilinearity of composition (`comp_add`). -/
theorem hasDerivAt_inhomogVariation_add {A F₁ F₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F₁ s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F₂ s) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r + V₂ r)
      ((A s).comp (V₁ s + V₂ s) + (F₁ s + F₂ s)) s := by
  have h := (hV₁ s).add (hV₂ s)
  have heq : (A s).comp (V₁ s) + F₁ s + ((A s).comp (V₂ s) + F₂ s)
      = (A s).comp (V₁ s + V₂ s) + (F₁ s + F₂ s) := by
    rw [ContinuousLinearMap.comp_add]; abel
  rwa [heq] at h

/-- **Homogeneity (scalar multiplication) for the inhomogeneous variational ODE.**  If `V` solves
`V' = A ∘ V + F`, then `c • V` solves the ODE with the scaled forcing,
`(c • V)' = A ∘ (c • V) + c • F`.  Linearity of the operator ODE: scale the `HasDerivAt` statement
and use `A ∘ (c • V) = c • (A ∘ V)` (`comp_smul`). -/
theorem hasDerivAt_inhomogVariation_smul {A F V : ℝ → (E →L[ℝ] E)} (c : ℝ)
    (hV : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (s : ℝ) :
    HasDerivAt (fun r => c • V r) ((A s).comp (c • V s) + c • F s) s := by
  have h := (hV s).const_smul c
  have heq : c • ((A s).comp (V s) + F s) = (A s).comp (c • V s) + c • F s := by
    rw [smul_add, ContinuousLinearMap.comp_smul]
  rwa [heq] at h

/-- **Uniqueness of the first variation.**  Two solutions `V₁`, `V₂` of the *same* inhomogeneous
variational ODE `V' = A ∘ V + F` (with `‖A s‖ ≤ K`) that agree at one time `t₀` agree everywhere.
Proof: the difference `D = V₁ - V₂` solves the *homogeneous* variational ODE `D' = A ∘ D` (the
forcings cancel) with `D t₀ = 0`, hence equals the zero solution by Grönwall uniqueness
(`variational_eq_of_isIntegralCurve`).  Together with existence this makes the first variation a
*single-valued* (well-defined) function of the forcing. -/
theorem inhomogVariation_unique {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {F V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F s) s)
    (h0 : V₁ t₀ = V₂ t₀) (t : ℝ) : V₁ t = V₂ t := by
  have hDcurve : IsIntegralCurve (fun s => V₁ s - V₂ s) (variationalField A) := by
    intro s
    have h := (hV₁ s).sub (hV₂ s)
    have heq : (A s).comp (V₁ s) + F s - ((A s).comp (V₂ s) + F s)
        = variationalField A s (V₁ s - V₂ s) := by
      simp only [variationalField, ContinuousLinearMap.comp_sub]; abel
    rwa [heq] at h
  have hZcurve : IsIntegralCurve (fun _ : ℝ => (0 : E →L[ℝ] E)) (variationalField A) := by
    intro s
    simpa [variationalField] using hasDerivAt_const s (0 : E →L[ℝ] E)
  have hD0 : (fun s => V₁ s - V₂ s) t₀ = (fun _ : ℝ => (0 : E →L[ℝ] E)) t₀ :=
    sub_eq_zero.mpr h0
  have hfin := variational_eq_of_isIntegralCurve hA hDcurve hZcurve hD0 t
  have hzero : V₁ t - V₂ t = 0 := hfin
  exact sub_eq_zero.mp hzero

/-- **The first variation is additive in the coefficient perturbation.**  With a fixed background
resolvent `W` (e.g. `W = D_x Φ₂ = fundamentalSolution hA₂ hΦ₂ h0₂`), the forcing of the
first-variation ODE is `B ∘ W`, *linear* in the perturbation `B = A₁ - A₂`.  Hence if `V₁` is the
first variation for perturbation `B₁` and `V₂` for `B₂`, their sum `V₁ + V₂` is the first variation
for `B₁ + B₂`:
`(V₁ + V₂)' = A₂ ∘ (V₁ + V₂) + (B₁ + B₂) ∘ W`.  (Superposition
`hasDerivAt_inhomogVariation_add` composed with linearity of `B ↦ B ∘ W`, `add_comp`.) -/
theorem hasDerivAt_firstVariation_perturbation_add
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r + V₂ r)
      ((A₂ s).comp (V₁ s + V₂ s) + (B₁ s + B₂ s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_add hV₁ hV₂ s
  rwa [← ContinuousLinearMap.add_comp] at h

/-- **The first variation is homogeneous in the coefficient perturbation.**  With a fixed background
resolvent `W`, if `V` is the first variation for perturbation `B`, then `c • V` is the first
variation for `c • B`:
`(c • V)' = A₂ ∘ (c • V) + (c • B) ∘ W`.  (Homogeneity `hasDerivAt_inhomogVariation_smul` composed
with linearity of `B ↦ B ∘ W`, `smul_comp`.)  Together with additivity this exhibits the first
variation as a *linear* function of the coefficient perturbation. -/
theorem hasDerivAt_firstVariation_perturbation_smul
    {A₂ W B V : ℝ → (E →L[ℝ] E)} (c : ℝ)
    (hV : ∀ s, HasDerivAt V ((A₂ s).comp (V s) + (B s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => c • V r)
      ((A₂ s).comp (c • V s) + (c • B s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_smul c hV s
  rwa [← ContinuousLinearMap.smul_comp] at h

/-- **General a-priori size bound for the inhomogeneous variational ODE.**  Forcing-agnostic
Grönwall estimate: if `V` solves `V' = A ∘ V + F` (with `‖A s‖ ≤ K`) anchored at `V t₀ = 0`, and the
forcing is bounded by `M ≥ 0` on `[t₀, T]` (`‖F s‖ ≤ M`), then
`‖V t‖ ≤ M · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Proof: `‖V' s‖ ≤ K · ‖V s‖ + M` (operator
submultiplicativity of `A ∘ V` and the forcing bound), and Grönwall
(`norm_le_gronwallBound_of_norm_deriv_right_le`) closes it, with `gronwallBound_zero_left_mul`
factoring the linear response `M`.  This is the general first-variation size estimate of which
`norm_fundamentalSolution_variation_le` (specialised to the coefficient-perturbation forcing
`F = (A₁ - A₂) ∘ W₂`, `M = ε · exp (K (T - t₀))`) is the leading instance. -/
theorem norm_inhomogVariation_le {A F V : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hV0 : V t₀ = 0) {M : ℝ} {T : ℝ} (hFbound : ∀ s ∈ Set.Icc t₀ T, ‖F s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖ ≤ M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hcV : Continuous V := continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have ha : ‖V t₀‖ ≤ 0 := by simp [hV0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A s).comp (V s) + F s‖ ≤ (K : ℝ) * ‖V s‖ + M := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t₀ T := ⟨hs.1, le_trans hs.2.le ht.2⟩
    have hAs : ‖A s‖ ≤ (K : ℝ) := by exact_mod_cast hA s
    refine (norm_add_le _ _).trans (add_le_add ?_ (hFbound s hsIcc))
    calc ‖(A s).comp (V s)‖ ≤ ‖A s‖ * ‖V s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖V s‖ := mul_le_mul_of_nonneg_right hAs (norm_nonneg _)
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcV.continuousOn (fun x _ => (hVderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖V t‖ ≤ gronwallBound 0 (K : ℝ) M (t - t₀) := hgron
    _ = M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := gronwallBound_zero_left_mul _ _ _

/-- **Zero forcing gives the zero first variation.**  The first variation for a vanishing
perturbation is identically zero: if `V' = A ∘ V + F` with `F ≡ 0` and `V t₀ = 0`, then `V ≡ 0`.
(Uniqueness `inhomogVariation_unique` against the zero solution.)  This is the value at the origin of
the *linear* first-variation map `perturbation ↦ V` — a linear map sends `0` to `0` — consistent with
`hasDerivAt_firstVariation_perturbation_add/smul`. -/
theorem inhomogVariation_eq_zero_of_forcing_zero {A F V : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hF : ∀ s, F s = 0) (hV0 : V t₀ = 0) (t : ℝ) : V t = 0 := by
  have hZderiv : ∀ s, HasDerivAt (fun _ : ℝ => (0 : E →L[ℝ] E))
      ((A s).comp ((fun _ : ℝ => (0 : E →L[ℝ] E)) s) + F s) s := by
    intro s
    have hz : (A s).comp ((fun _ : ℝ => (0 : E →L[ℝ] E)) s) + F s = 0 := by simp [hF s]
    rw [hz]
    exact hasDerivAt_const s 0
  have hfin := inhomogVariation_unique hA hVderiv hZderiv hV0 t
  exact hfin

/-- **Superposition (subtraction) for the inhomogeneous variational ODE.**  If `V₁` solves
`V₁' = A ∘ V₁ + F₁` and `V₂` solves `V₂' = A ∘ V₂ + F₂`, then their difference solves the ODE with
the subtracted forcing, `(V₁ - V₂)' = A ∘ (V₁ - V₂) + (F₁ - F₂)`.  (Linearity of the operator ODE;
`comp_sub`.) -/
theorem hasDerivAt_inhomogVariation_sub {A F₁ F₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F₁ s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F₂ s) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r - V₂ r)
      ((A s).comp (V₁ s - V₂ s) + (F₁ s - F₂ s)) s := by
  have h := (hV₁ s).sub (hV₂ s)
  have heq : (A s).comp (V₁ s) + F₁ s - ((A s).comp (V₂ s) + F₂ s)
      = (A s).comp (V₁ s - V₂ s) + (F₁ s - F₂ s) := by
    rw [ContinuousLinearMap.comp_sub]; abel
  rwa [heq] at h

/-- **The first variation is subtractive in the coefficient perturbation.**  With a fixed background
resolvent `W`, if `V₁` is the first variation for perturbation `B₁` and `V₂` for `B₂`, their
difference `V₁ - V₂` is the first variation for `B₁ - B₂`:
`(V₁ - V₂)' = A₂ ∘ (V₁ - V₂) + (B₁ - B₂) ∘ W`.  (Superposition `hasDerivAt_inhomogVariation_sub`
composed with linearity of `B ↦ B ∘ W`, `sub_comp`.)  This is the differential input to the Lipschitz
dependence of the first variation on the perturbation. -/
theorem hasDerivAt_firstVariation_perturbation_sub
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r - V₂ r)
      ((A₂ s).comp (V₁ s - V₂ s) + (B₁ s - B₂ s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_sub hV₁ hV₂ s
  rwa [← ContinuousLinearMap.sub_comp] at h

/-- **Lipschitz dependence of the first variation on the coefficient perturbation.**  With a fixed
background resolvent `W` bounded by `C` on `[t₀, T]` (`‖W s‖ ≤ C`), the first variation depends
Lipschitz-continuously on the perturbation: if `V₁`, `V₂` are the (anchored) first variations for
perturbations `B₁`, `B₂` with `‖B₁ s - B₂ s‖ ≤ ε`, then
`‖V₁ t - V₂ t‖ ≤ (ε · C) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Proof: `V₁ - V₂` is the first
variation for `B₁ - B₂` (`hasDerivAt_firstVariation_perturbation_sub`) with forcing bounded by
`‖(B₁ - B₂) ∘ W‖ ≤ ε · C`, and the general a-priori bound `norm_inhomogVariation_le` closes it.
Taking `ε → 0` this is the *continuity* of the Gateaux-derivative map `perturbation ↦ V`; together
with additivity/homogeneity (`hasDerivAt_firstVariation_perturbation_add/smul`) it exhibits the first
variation as a genuinely *bounded linear* map of the coefficient perturbation — the honest
Gateaux/Fréchet derivative of the resolvent `A ↦ D_x Φ_t`. -/
theorem norm_firstVariation_perturbation_sub_le
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0)
    {ε C T : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ s ∈ Set.Icc t₀ T, ‖B₁ s - B₂ s‖ ≤ ε)
    (hW : ∀ s ∈ Set.Icc t₀ T, ‖W s‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V₁ t - V₂ t‖ ≤ (ε * C) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hDderiv := hasDerivAt_firstVariation_perturbation_sub hV₁ hV₂
  have hD0 : (fun r => V₁ r - V₂ r) t₀ = 0 := by simp [hV₁0, hV₂0]
  have hFbound : ∀ s ∈ Set.Icc t₀ T, ‖(B₁ s - B₂ s).comp (W s)‖ ≤ ε * C := by
    intro s hs
    calc ‖(B₁ s - B₂ s).comp (W s)‖
        ≤ ‖B₁ s - B₂ s‖ * ‖W s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ε * C := mul_le_mul (hB s hs) (hW s hs) (norm_nonneg _) hε
  exact norm_inhomogVariation_le hA₂ hDderiv hD0 hFbound ht

/-- **The first-variation map is additive.**  Combining superposition
(`hasDerivAt_firstVariation_perturbation_add`) with Grönwall uniqueness (`inhomogVariation_unique`):
the *unique* anchored first variation `V₁₂` for the summed perturbation `B₁ + B₂` equals the sum of
the individual first variations, `V₁₂ t = V₁ t + V₂ t`.  This is the honest *map-level* additivity of
the coefficient-derivative assignment `perturbation ↦ V` (not merely closure of the solution set
under addition). -/
theorem firstVariation_perturbation_add_eq
    {A₂ W B₁ B₂ V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂ ((A₂ s).comp (V₁₂ s) + (B₁ s + B₂ s).comp (W s)) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hsum := hasDerivAt_firstVariation_perturbation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA₂ hV₁₂ hsum h0 t

/-- **The first-variation map is homogeneous.**  Combining homogeneity
(`hasDerivAt_firstVariation_perturbation_smul`) with Grönwall uniqueness: the unique anchored first
variation `Vc` for the scaled perturbation `c • B` equals the scaled first variation,
`Vc t = c • V t`.  Together with `firstVariation_perturbation_add_eq` and
`inhomogVariation_eq_zero_of_forcing_zero` this makes `perturbation ↦ V` a genuine *linear map*. -/
theorem firstVariation_perturbation_smul_eq
    {A₂ W B V Vc : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} (c : ℝ)
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV : ∀ s, HasDerivAt V ((A₂ s).comp (V s) + (B s).comp (W s)) s)
    (hVc : ∀ s, HasDerivAt Vc ((A₂ s).comp (Vc s) + (c • B s).comp (W s)) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hsmul := hasDerivAt_firstVariation_perturbation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA₂ hVc hsmul h0 t

/-- **Volterra (integral) form of the first variation.**  The anchored solution of the inhomogeneous
variational ODE `V' = A ∘ V + F` (`V t₀ = 0`) satisfies the fixed-point integral equation
`V t = ∫_{t₀}^{t} (A σ ∘ V σ + F σ) dσ`.  Immediate from the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) with the anchor `V t₀ = 0`, the integrand being
continuous (`A`, `F` continuous, `V` continuous from `HasDerivAt`) hence interval-integrable.  This is
the Volterra/Picard equation whose iteration constructs the first variation — the integral-equation
starting point for the *existence* of the first variation (the remaining, continuation-flavoured half
of the linearity-and-existence target), companion to `fundamentalSolution_eq_one_add_integral` for
the homogeneous resolvent. -/
theorem inhomogVariation_eq_integral [CompleteSpace E]
    {A F V : ℝ → (E →L[ℝ] E)}
    (hAcont : Continuous A) (hFcont : Continuous F)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hV0 : V t₀ = 0) (t : ℝ) :
    V t = ∫ σ in t₀..t, ((A σ).comp (V σ) + F σ) := by
  have hVcont : Continuous V :=
    continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have hHcont : Continuous (fun σ => (A σ).comp (V σ) + F σ) :=
    (hAcont.clm_comp hVcont).add hFcont
  have hderiv : ∀ σ ∈ Set.uIcc t₀ t, HasDerivAt V ((A σ).comp (V σ) + F σ) σ :=
    fun σ _ => hVderiv σ
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hHcont.intervalIntegrable t₀ t)
  rw [hV0, sub_zero] at hint
  exact hint.symm

/-!
### Existence of the first variation via the augmented homogeneous flow

The linearity/uniqueness/bound lemmas above take the first variation `V` — a solution of the
*inhomogeneous* operator ODE `V' = A ∘ V + F` anchored at `V t₀ = 0` — as a hypothesis.  Here we
reduce the *existence* of such a `V` to the existence of a genuine **homogeneous** linear flow, by
the classical homogenisation of an affine ODE.

On the augmented Banach space `(E →L[ℝ] E) × ℝ` consider the *linear* (homogeneous) field
`ℳ(s)(V, c) = (A s ∘ V + c • F s, 0)`.  An integral curve `z = (V, c)` of `ℳ` through `(0, 1)` has a
constant scalar coordinate `c ≡ 1` (its derivative is `0`), so the operator coordinate `V` satisfies
`V' = A ∘ V + 1 • F = A ∘ V + F` with `V t₀ = 0`: it *is* the first variation.  Thus the inhomogeneous
first variation is a component of a homogeneous resolvent — the operator-ODE shadow of Duhamel's
principle — and its existence follows from the very same flow-existence input this file consumes for
`variationalFieldVec`.  No new analysis is required beyond homogeneous flow existence. -/

/-- The **augmented (homogenised) variational field** on `(E →L[ℝ] E) × ℝ` associated to an operator
path `A` and a forcing path `F`: `(V, c) ↦ (A s ∘ V + c • F s, 0)`.  It is linear (homogeneous) in
`(V, c)`; an integral curve through `(0, 1)` carries the first variation of the inhomogeneous
variational ODE `V' = A ∘ V + F` in its operator coordinate. -/
def augmentedVariationalField (A F : ℝ → (E →L[ℝ] E)) :
    ℝ → ((E →L[ℝ] E) × ℝ) → ((E →L[ℝ] E) × ℝ) :=
  fun s p => ((A s).comp p.1 + p.2 • F s, 0)

/-- **The augmented variational field is uniformly Lipschitz.**  Under uniform bounds `‖A s‖ ≤ K` and
`‖F s‖ ≤ M`, the linear augmented field `(V, c) ↦ (A s ∘ V + c • F s, 0)` on `(E →L[ℝ] E) × ℝ` is
`(K + M)`-Lipschitz in `(V, c)`, with the constant independent of `s`.  (Sup-norm on the product,
submultiplicativity of `A s ∘ ·`, and `‖c • F s‖ ≤ ‖c‖ · M`; the two component gaps are each bounded
by the product-norm gap.)  This places the augmented homogeneous flow squarely in the uniformly
Lipschitz regime handled by the `C⁰`/`C¹` dependence theory above — so the flow-existence input
required by `hasDerivAt_inhomogVariation_of_augmented` is of exactly the same well-posed kind consumed
throughout this file for `variationalFieldVec`. -/
theorem lipschitzWith_augmentedVariationalField {A F : ℝ → (E →L[ℝ] E)} {K M : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hF : ∀ s, ‖F s‖₊ ≤ M) (s : ℝ) :
    LipschitzWith (K + M) (augmentedVariationalField A F s) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hAs : ‖A s‖ ≤ (K : ℝ) := by exact_mod_cast hA s
  have hFs : ‖F s‖ ≤ (M : ℝ) := by exact_mod_cast hF s
  have hfst : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hsnd : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  rw [dist_eq_norm, dist_eq_norm]
  have hnorm : ‖augmentedVariationalField A F s p - augmentedVariationalField A F s q‖
      = ‖(A s).comp (p.1 - q.1) + (p.2 - q.2) • F s‖ := by
    rw [Prod.norm_def]
    have e1 : (augmentedVariationalField A F s p - augmentedVariationalField A F s q).1
        = (A s).comp (p.1 - q.1) + (p.2 - q.2) • F s := by
      show ((A s).comp p.1 + p.2 • F s) - ((A s).comp q.1 + q.2 • F s)
          = (A s).comp (p.1 - q.1) + (p.2 - q.2) • F s
      rw [ContinuousLinearMap.comp_sub, sub_smul]; abel
    have e2 : (augmentedVariationalField A F s p - augmentedVariationalField A F s q).2 = 0 := by
      show (0 : ℝ) - 0 = 0
      simp
    rw [e1, e2, norm_zero, max_eq_left (norm_nonneg _)]
  rw [hnorm]
  have h1 : ‖(A s).comp (p.1 - q.1)‖ ≤ (K : ℝ) * ‖p - q‖ :=
    calc ‖(A s).comp (p.1 - q.1)‖
        ≤ ‖A s‖ * ‖p.1 - q.1‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖p - q‖ := mul_le_mul hAs hfst (norm_nonneg _) (by positivity)
  have h2 : ‖(p.2 - q.2) • F s‖ ≤ ‖p - q‖ * (M : ℝ) := by
    rw [norm_smul]
    exact mul_le_mul hsnd hFs (norm_nonneg _) (norm_nonneg _)
  calc ‖(A s).comp (p.1 - q.1) + (p.2 - q.2) • F s‖
      ≤ ‖(A s).comp (p.1 - q.1)‖ + ‖(p.2 - q.2) • F s‖ := norm_add_le _ _
    _ ≤ (K : ℝ) * ‖p - q‖ + ‖p - q‖ * (M : ℝ) := add_le_add h1 h2
    _ = ((K + M : ℝ≥0) : ℝ) * ‖p - q‖ := by push_cast; ring

/-- **The scalar coordinate of the augmented flow has zero derivative.**  For any integral curve `z`
of `augmentedVariationalField A F`, the scalar component `s ↦ (z s).2` has derivative `0` everywhere
(the second slot of the augmented field is identically `0`); obtained by post-composing with the
continuous linear projection `snd`. -/
theorem hasDerivAt_augmentedVariationalField_snd {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s) (s : ℝ) :
    HasDerivAt (fun r => (z r).2) 0 s := by
  have h := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) ℝ).hasFDerivAt.comp_hasDerivAt s (hz s)
  simpa [augmentedVariationalField, ContinuousLinearMap.coe_snd', Function.comp_def] using h

/-- **The scalar coordinate of the augmented flow through `(0, 1)` is constantly `1`.**  Its
derivative vanishes everywhere (`hasDerivAt_augmentedVariationalField_snd`) and it starts at `1`, so
it is constant equal to `1` by `is_const_of_deriv_eq_zero`. -/
theorem augmentedVariationalField_snd_eq_one {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) (s : ℝ) : (z s).2 = 1 := by
  have hderiv := hasDerivAt_augmentedVariationalField_snd hz
  have hdiff : Differentiable ℝ (fun r => (z r).2) := fun r => (hderiv r).differentiableAt
  have hzero : ∀ r, deriv (fun r => (z r).2) r = 0 := fun r => (hderiv r).deriv
  have hconst : (z s).2 = (z t₀).2 := is_const_of_deriv_eq_zero hdiff hzero s t₀
  rw [hconst, hz0]

/-- **Existence of the first variation via the augmented homogeneous flow.**  If `z` is an integral
curve of the homogeneous augmented field `augmentedVariationalField A F` through `(0, 1)`, then its
operator coordinate `V = (z ·).1` solves the *inhomogeneous* variational ODE `V' = A ∘ V + F`.  (The
scalar coordinate is constantly `1`, so the forcing `c • F` reduces to `F`.)  This reduces existence
of the first variation to homogeneous flow existence — the operator-ODE Duhamel principle — supplying
the `HasDerivAt V (A ∘ V + F)` hypothesis consumed by the linearity/uniqueness/bound lemmas above. -/
theorem hasDerivAt_inhomogVariation_of_augmented {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) (s : ℝ) :
    HasDerivAt (fun r => (z r).1) ((A s).comp ((z s).1) + F s) s := by
  have hone : (z s).2 = 1 := augmentedVariationalField_snd_eq_one hz hz0 s
  have h := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) ℝ).hasFDerivAt.comp_hasDerivAt s (hz s)
  simpa [augmentedVariationalField, ContinuousLinearMap.coe_fst', Function.comp_def, hone] using h

/-- **The augmented first variation is anchored at `0`.**  The operator coordinate of the augmented
flow through `(0, 1)` vanishes at the anchor time: `V t₀ = 0`.  Together with
`hasDerivAt_inhomogVariation_of_augmented` this delivers the full anchored first variation `V`, whose
existence is thereby reduced to that of the augmented homogeneous flow. -/
theorem inhomogVariation_of_augmented_anchor
    {z : ℝ → ((E →L[ℝ] E) × ℝ)} (hz0 : z t₀ = (0, 1)) :
    (fun r => (z r).1) t₀ = (0 : E →L[ℝ] E) := by
  show (z t₀).1 = 0
  rw [hz0]

/-- **Existence and a-priori bound of the first variation from the augmented flow.**  The operator
coordinate `V = (z ·).1` of an integral curve `z` of `augmentedVariationalField A F` through `(0, 1)`
is the anchored first variation of `V' = A ∘ V + F` (`hasDerivAt_inhomogVariation_of_augmented`,
`inhomogVariation_of_augmented_anchor`), so it inherits the general Grönwall a-priori bound: with
`‖A s‖ ≤ K` and `‖F s‖ ≤ M` on `[t₀, T]`, `‖V t‖ ≤ M · gronwallBound 0 K 1 (t - t₀)` there.  This is
the capstone of the augmented-flow reduction: existence *and* the exponential size control of the
first variation follow from homogeneous flow existence alone, delivering the complete first-variation
data (existence, anchoring, size bound) consumed by the second-variation estimates. -/
theorem norm_inhomogVariation_of_augmented_le {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) {M T : ℝ} (hFbound : ∀ s ∈ Set.Icc t₀ T, ‖F s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖(z t).1‖ ≤ M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hV := hasDerivAt_inhomogVariation_of_augmented hz hz0
  have hV0 : (fun r => (z r).1) t₀ = 0 := inhomogVariation_of_augmented_anchor hz0
  exact norm_inhomogVariation_le hA hV hV0 hFbound ht

/-- **Well-definedness of the augmented first variation.**  Any two integral curves `z₁, z₂` of the
augmented field `augmentedVariationalField A F` through `(0, 1)` carry the *same* operator coordinate:
`(z₁ t).1 = (z₂ t).1`.  Both operator coordinates solve the anchored inhomogeneous ODE
`V' = A ∘ V + F`, `V t₀ = 0` (`hasDerivAt_inhomogVariation_of_augmented`,
`inhomogVariation_of_augmented_anchor`), so Grönwall uniqueness (`inhomogVariation_unique`) pins them
together.  Thus the first variation extracted by the augmented-flow reduction is a canonical,
flow-independent object — it depends only on `A` and `F`, not on the particular augmented flow. -/
theorem augmentedVariationalField_fst_unique {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {z₁ z₂ : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz₁ : ∀ s, HasDerivAt z₁ (augmentedVariationalField A F s (z₁ s)) s)
    (hz₂ : ∀ s, HasDerivAt z₂ (augmentedVariationalField A F s (z₂ s)) s)
    (hz₁0 : z₁ t₀ = (0, 1)) (hz₂0 : z₂ t₀ = (0, 1)) (t : ℝ) :
    (z₁ t).1 = (z₂ t).1 := by
  have hV₁ := hasDerivAt_inhomogVariation_of_augmented hz₁ hz₁0
  have hV₂ := hasDerivAt_inhomogVariation_of_augmented hz₂ hz₂0
  have h0 : (fun r => (z₁ r).1) t₀ = (fun r => (z₂ r).1) t₀ := by
    rw [inhomogVariation_of_augmented_anchor hz₁0, inhomogVariation_of_augmented_anchor hz₂0]
  exact inhomogVariation_unique hA hV₁ hV₂ h0 t

/-!
### Gluing integral curves across a junction (the continuation primitive)

Mathlib v4.29.1 supplies *local* existence of integral curves (Picard–Lindelöf on a compact
interval) but no way to **glue** integral curves that meet at a common time into a single curve valid
on the union.  The two lemmas here provide that missing continuation primitive.

The payoff is `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`: a curve which is an integral curve on
the left half-line `Iic b` and on the right half-line `Ici b` is a **global** integral curve.  This
is exactly the shape (`IsIntegralCurve` — a genuine two-sided derivative at *every* time) consumed by
every flow-existence hypothesis in this file (`hΦ : ∀ x, IsIntegralCurve (Φ x) …`, and the augmented
homogeneous flow `∀ s, HasDerivAt z …` of `hasDerivAt_inhomogVariation_of_augmented`).  Thus a global
integral curve can be assembled from a forward local solution on `[b, ∞)` and a backward local
solution on `(-∞, b]` glued at the anchor `b` — reducing global existence to one-sided existence.

`isIntegralCurve_glue_Iic_Ici` is the constructive companion: it *builds* the glued curve
`fun t => if t ≤ b then γ₁ t else γ₂ t` from two one-sided integral curves that agree at the junction
`γ₁ b = γ₂ b`, and shows it is a global integral curve.  Only Mathlib's Banach-level within-set
derivative calculus is used — no PDE or manifold content. -/

/-- **Half-line gluing to a global integral curve.**  If `γ` is an integral curve of `v` on the left
half-line `Iic b` *and* on the right half-line `Ici b`, then it is a *global* integral curve of `v`.
At a time `t < b` the set `Iic b` is a neighbourhood of `t`, so the within-`Iic b` derivative upgrades
to a two-sided `HasDerivAt`; symmetrically for `t > b` using `Ici b`; and at the junction `t = b` the
two one-sided within-set derivatives combine via `HasDerivWithinAt.union` over `Iic b ∪ Ici b = univ`
into the two-sided derivative.  This is the continuation primitive that turns one-sided existence into
the global `IsIntegralCurve` consumed throughout this file. -/
theorem isIntegralCurve_of_isIntegralCurveOn_Iic_Ici {b : ℝ}
    (h₁ : IsIntegralCurveOn γ v (Set.Iic b)) (h₂ : IsIntegralCurveOn γ v (Set.Ici b)) :
    IsIntegralCurve γ v := by
  intro t
  rcases lt_trichotomy t b with hlt | heq | hgt
  · have hd := h₁ t (le_of_lt hlt)
    have hnhd : Set.Iic b ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt)) Set.Iio_subset_Iic_self
    exact hd.hasDerivAt hnhd
  · rw [heq]
    have hd1 := h₁ b (Set.mem_Iic.mpr le_rfl)
    have hd2 := h₂ b (Set.mem_Ici.mpr le_rfl)
    have hu := hd1.union hd2
    rw [Set.Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · have hd := h₂ t (le_of_lt hgt)
    have hnhd : Set.Ici b ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hgt)) Set.Ioi_subset_Ici_self
    exact hd.hasDerivAt hnhd

/-- **Constructive continuation: gluing two one-sided integral curves into a global one.**  Given a
left integral curve `γ₁` on `Iic b` and a right integral curve `γ₂` on `Ici b` that agree at the
junction (`γ₁ b = γ₂ b`), the piecewise curve `fun t => if t ≤ b then γ₁ t else γ₂ t` is a *global*
integral curve of `v`.  The glued curve agrees with `γ₁` on `Iic b` and with `γ₂` on `Ici b` (the
junction value being pinned by `γ₁ b = γ₂ b`), so each one-sided integral-curve property transfers by
`HasDerivWithinAt.congr`, and `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici` assembles them into the
global curve.  This is the concrete tool for continuing a solution past a time `b` — the operational
heart of extending local ODE solutions to global ones. -/
theorem isIntegralCurve_glue_Iic_Ici {b : ℝ} {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurveOn γ₁ v (Set.Iic b)) (h₂ : IsIntegralCurveOn γ₂ v (Set.Ici b))
    (hmatch : γ₁ b = γ₂ b) :
    IsIntegralCurve (fun t => if t ≤ b then γ₁ t else γ₂ t) v := by
  set γ := fun t => if t ≤ b then γ₁ t else γ₂ t with hγdef
  have hEq1 : Set.EqOn γ γ₁ (Set.Iic b) := by
    intro x hx
    simp only [hγdef]
    rw [if_pos (Set.mem_Iic.mp hx)]
  have hEq2 : Set.EqOn γ γ₂ (Set.Ici b) := by
    intro x hx
    have hbx : b ≤ x := Set.mem_Ici.mp hx
    rcases hbx.lt_or_eq with h | h
    · simp only [hγdef]
      rw [if_neg (not_le.mpr h)]
    · subst h
      simp only [hγdef]
      rw [if_pos le_rfl]
      exact hmatch
  have step1 : IsIntegralCurveOn γ v (Set.Iic b) := by
    intro x hx
    have hgx : γ x = γ₁ x := hEq1 hx
    rw [hgx]
    exact (h₁ x hx).congr (fun y hy => hEq1 hy) hgx
  have step2 : IsIntegralCurveOn γ v (Set.Ici b) := by
    intro x hx
    have hgx : γ x = γ₂ x := hEq2 hx
    rw [hgx]
    exact (h₂ x hx).congr (fun y hy => hEq2 hy) hgx
  exact isIntegralCurve_of_isIntegralCurveOn_Iic_Ici step1 step2

/-- **Closed-interval gluing.**  If `γ` is an integral curve of `v` on `Icc a b` and on `Icc b c`
(with `a ≤ b ≤ c`), then it is an integral curve on the whole interval `Icc a c`.  Away from the
junction `b` the relevant closed subinterval is a within-`Icc a c` neighbourhood of the point, so the
subinterval derivative transports to `Icc a c` by `HasDerivWithinAt.mono_of_mem_nhdsWithin`; at the
junction the two one-sided within-derivatives combine via `HasDerivWithinAt.union` over
`Icc a b ∪ Icc b c = Icc a c`.  This is the finite-interval companion of
`isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`, used to concatenate successive local solutions. -/
theorem isIntegralCurveOn_Icc_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : IsIntegralCurveOn γ v (Set.Icc a b)) (h₂ : IsIntegralCurveOn γ v (Set.Icc b c)) :
    IsIntegralCurveOn γ v (Set.Icc a c) := by
  rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
  intro t ht
  rcases lt_trichotomy t b with hlt | heq | hgt
  · have htab : t ∈ Set.Icc a b := by
      rcases ht with h | h
      · exact h
      · exact absurd h.1 (not_le.mpr hlt)
    have hd := h₁ t htab
    apply hd.mono_of_mem_nhdsWithin
    rw [Set.Icc_union_Icc_eq_Icc hab hbc, mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, Set.mem_Iio.mpr hlt,
      fun x hx => ⟨hx.2.1, le_of_lt (Set.mem_Iio.mp hx.1)⟩⟩
  · rw [heq]
    have hd1 := h₁ b (Set.mem_Icc.mpr ⟨hab, le_rfl⟩)
    have hd2 := h₂ b (Set.mem_Icc.mpr ⟨le_rfl, hbc⟩)
    exact hd1.union hd2
  · have htbc : t ∈ Set.Icc b c := by
      rcases ht with h | h
      · exact absurd h.2 (not_le.mpr hgt)
      · exact h
    have hd := h₂ t htbc
    apply hd.mono_of_mem_nhdsWithin
    rw [Set.Icc_union_Icc_eq_Icc hab hbc, mem_nhdsWithin]
    exact ⟨Set.Ioi b, isOpen_Ioi, Set.mem_Ioi.mpr hgt,
      fun x hx => ⟨le_of_lt (Set.mem_Ioi.mp hx.1), hx.2.2⟩⟩

/-- **Constructive closed-interval continuation.**  Given a left integral curve `γ₁` on `Icc a b` and
a right integral curve `γ₂` on `Icc b c` (with `a ≤ b ≤ c`) that agree at the junction `γ₁ b = γ₂ b`,
the piecewise curve `fun t => if t ≤ b then γ₁ t else γ₂ t` is an integral curve of `v` on `Icc a c`.
The glued curve agrees with `γ₁` on `Icc a b` and with `γ₂` on `Icc b c`, so each subinterval
integral-curve property transfers by `HasDerivWithinAt.congr` and `isIntegralCurveOn_Icc_union` fuses
them.  Iterating this over a chain `a = t₀ ≤ t₁ ≤ ⋯ ≤ tₙ = c` concatenates finitely many local
Picard–Lindelöf solutions into one solution on the whole span — the finite-continuation building
block toward global existence. -/
theorem isIntegralCurveOn_glue_Icc {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurveOn γ₁ v (Set.Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Set.Icc b c))
    (hmatch : γ₁ b = γ₂ b) :
    IsIntegralCurveOn (fun t => if t ≤ b then γ₁ t else γ₂ t) v (Set.Icc a c) := by
  set γ := fun t => if t ≤ b then γ₁ t else γ₂ t with hγdef
  have hEq1 : Set.EqOn γ γ₁ (Set.Icc a b) := by
    intro x hx
    simp only [hγdef]
    rw [if_pos hx.2]
  have hEq2 : Set.EqOn γ γ₂ (Set.Icc b c) := by
    intro x hx
    rcases hx.1.lt_or_eq with h | h
    · simp only [hγdef]
      rw [if_neg (not_le.mpr h)]
    · subst h
      simp only [hγdef]
      rw [if_pos le_rfl]
      exact hmatch
  have step1 : IsIntegralCurveOn γ v (Set.Icc a b) := by
    intro x hx
    have hgx : γ x = γ₁ x := hEq1 hx
    rw [hgx]
    exact (h₁ x hx).congr (fun y hy => hEq1 hy) hgx
  have step2 : IsIntegralCurveOn γ v (Set.Icc b c) := by
    intro x hx
    have hgx : γ x = γ₂ x := hEq2 hx
    rw [hgx]
    exact (h₂ x hx).congr (fun y hy => hEq2 hy) hgx
  exact isIntegralCurveOn_Icc_union hab hbc step1 step2

/-- **Exhaustion: global integral curve from a countable family of bounded-interval solutions.**  If
`γ` is an integral curve of `v` on every symmetric closed interval `Icc (t₀ - n) (t₀ + n)`, `n : ℕ`,
then it is a *global* integral curve of `v`.  Any time `t` lies in the open interior of some
`Icc (t₀ - n) (t₀ + n)` (Archimedean: choose `n > |t - t₀|`), where that interval is a genuine
neighbourhood of `t`, so the within-interval derivative upgrades to a two-sided `HasDerivAt`.  This is
the countable-exhaustion counterpart of `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`: it reduces
global existence to solving on a growing sequence of compact intervals — the natural target of
iterating `isIntegralCurveOn_glue_Icc` over local Picard–Lindelöf solutions. -/
theorem isIntegralCurve_of_forall_mem_Icc {t₀ : ℝ}
    (h : ∀ n : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - n) (t₀ + n))) :
    IsIntegralCurve γ v := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (|t - t₀|)
  obtain ⟨hl, hr⟩ := abs_lt.mp hn
  have hmem : t ∈ Set.Icc (t₀ - (n : ℝ)) (t₀ + (n : ℝ)) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hnhd : Set.Icc (t₀ - (n : ℝ)) (t₀ + (n : ℝ)) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  exact (h n t hmem).hasDerivAt hnhd

/-- **Finite-chain concatenation of consecutive-interval solutions.**  If `a : ℕ → ℝ` is monotone and
`γ` is an integral curve of `v` on every consecutive interval `Icc (a i) (a (i+1))`, then `γ` is an
integral curve on the whole span `Icc (a 0) (a (N+1))` for every `N`.  Proved by induction on `N`,
fusing one more interval at each step with `isIntegralCurveOn_Icc_union`.  This lifts the two-interval
gluing to arbitrarily many pieces — the induction that turns a sequence of local Picard–Lindelöf
solutions (arranged to share endpoints) into a single solution on an arbitrarily long interval, the
main input to the exhaustion lemma `isIntegralCurve_of_forall_mem_Icc`. -/
theorem isIntegralCurveOn_Icc_chain {a : ℕ → ℝ} (hmono : Monotone a)
    (h : ∀ i, IsIntegralCurveOn γ v (Set.Icc (a i) (a (i + 1)))) :
    ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (a 0) (a (N + 1))) := by
  intro N
  induction N with
  | zero => exact h 0
  | succ n ih =>
      exact isIntegralCurveOn_Icc_union
        (hmono (Nat.zero_le (n + 1))) (hmono (Nat.le_succ (n + 1))) ih (h (n + 1))

/-- **Right half-line from a growing family of forward compact-interval solutions.**  If `γ` is an
integral curve of `v` on every forward interval `Icc t₀ (t₀ + N)`, `N : ℕ`, then it is an integral
curve on the whole right half-line `Ici t₀`.  Any `t ≥ t₀` lies in `Icc t₀ (t₀ + N)` for large `N`
(Archimedean), and that interval is a within-`Ici t₀` neighbourhood of `t`, so the within-interval
derivative transports to `Ici t₀` by `HasDerivWithinAt.mono_of_mem_nhdsWithin`. -/
theorem isIntegralCurveOn_Ici_of_forall_Icc {t₀ : ℝ}
    (h : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc t₀ (t₀ + N))) :
    IsIntegralCurveOn γ v (Set.Ici t₀) := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t - t₀)
  have htmem : t ∈ Set.Icc t₀ (t₀ + (N : ℝ)) :=
    Set.mem_Icc.mpr ⟨Set.mem_Ici.mp ht, by linarith⟩
  have hd := h N t htmem
  apply hd.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  exact ⟨Set.Iio (t₀ + (N : ℝ)), isOpen_Iio, Set.mem_Iio.mpr (by linarith),
    fun x hx => Set.mem_Icc.mpr ⟨Set.mem_Ici.mp hx.2, le_of_lt (Set.mem_Iio.mp hx.1)⟩⟩

/-- **Left half-line from a growing family of backward compact-interval solutions.**  The mirror of
`isIntegralCurveOn_Ici_of_forall_Icc`: integral-curve data on every backward interval
`Icc (t₀ - N) t₀`, `N : ℕ`, yields an integral curve on the whole left half-line `Iic t₀`. -/
theorem isIntegralCurveOn_Iic_of_forall_Icc {t₀ : ℝ}
    (h : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - N) t₀)) :
    IsIntegralCurveOn γ v (Set.Iic t₀) := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t₀ - t)
  have htmem : t ∈ Set.Icc (t₀ - (N : ℝ)) t₀ :=
    Set.mem_Icc.mpr ⟨by linarith, Set.mem_Iic.mp ht⟩
  have hd := h N t htmem
  apply hd.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  exact ⟨Set.Ioi (t₀ - (N : ℝ)), isOpen_Ioi, Set.mem_Ioi.mpr (by linarith),
    fun x hx => Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioi.mp hx.1), Set.mem_Iic.mp hx.2⟩⟩

/-- **Global integral curve from forward and backward families of compact-interval solutions.**  If
`γ` is an integral curve of `v` on every forward interval `Icc t₀ (t₀ + N)` *and* on every backward
interval `Icc (t₀ - N) t₀`, then it is a *global* integral curve of `v`.  The two families give
integral-curve data on the right half-line `Ici t₀` and the left half-line `Iic t₀`
(`isIntegralCurveOn_Ici_of_forall_Icc`, `isIntegralCurveOn_Iic_of_forall_Icc`), and these glue at the
anchor `t₀` via `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`.  This is the end of the continuation
chain assembled in this section: it reduces *global* existence of an integral curve to solving the ODE
on the two growing families of compact intervals around the anchor — precisely the output produced by
iterating `isIntegralCurveOn_Icc_chain` over local Picard–Lindelöf solutions.  It discharges the
global-flow hypothesis shape `IsIntegralCurve` consumed throughout this file to the compact-interval
local theory that Mathlib v4.29.1 does supply. -/
theorem isIntegralCurve_of_forall_Icc_Ici_Iic {t₀ : ℝ}
    (hf : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc t₀ (t₀ + N)))
    (hb : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - N) t₀)) :
    IsIntegralCurve γ v :=
  isIntegralCurve_of_isIntegralCurveOn_Iic_Ici
    (isIntegralCurveOn_Iic_of_forall_Icc hb) (isIntegralCurveOn_Ici_of_forall_Icc hf)

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
