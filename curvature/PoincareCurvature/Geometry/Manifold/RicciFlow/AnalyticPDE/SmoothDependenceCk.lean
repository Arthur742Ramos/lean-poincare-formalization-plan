module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall

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

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
