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

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
