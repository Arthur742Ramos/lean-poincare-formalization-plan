module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceManifold

/-!
# Field-jet extraction from a jointly-`ContDiff` time-dependent field (roadmap point 4, Item 2)

The Banach → manifold smooth-dependence tower (`AnalyticPDE/SmoothDependenceCk`,
`AnalyticPDE/FlowDiffeomorphism`, `AnalyticPDE/SmoothDependenceManifold`,
`AnalyticPDE/ModelManifoldGaugeFlow`) drives the `C³` gauge flow of Item 2 from a **field jet**:
the spatial Fréchet derivatives `Dv`, `D²v`, `D³v` of the time-dependent field `v : ℝ → E → E`,
supplied as separate objects with pointwise `HasFDerivAt`, joint `(t, x)`-continuity, and global
Lipschitz bounds.

Those jet hypotheses are stated abstractly so the tower is agnostic to how the derivatives arise.
This module supplies the honest bridge from a *single* clean smoothness hypothesis — `v` jointly
`ContDiff` in `(time, space)` (`ContDiff ℝ n (Function.uncurry v)`) — to the **first jet layer**:

* `contDiff_apply_of_contDiff_uncurry` — each time slice `v s` is spatially `ContDiff ℝ n`;
* `hasFDerivAt_fderiv_of_contDiff_uncurry` — the spatial derivative object `fderiv ℝ (v s)` is a
  genuine Fréchet derivative of `v s` at every point (`1 ≤ n`);
* `continuous_fderiv_of_contDiff_uncurry` — the spatial derivative is jointly continuous in `(t, x)`,
  via the partial-derivative identity `fderiv ℝ (v t) x = fderiv ℝ (uncurry v) (t, x) ∘L inr`.

Together these produce exactly the `hDv`/`hDvc` inputs of the tower's flow theorems (`Dv := fun s ↦
fderiv ℝ (v s)`).  No new analytic content: a transport of Mathlib's `ContDiff` calculus into the
jet shape the smooth-dependence tower consumes.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

@[expose] public section

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {n : WithTop ℕ∞}

/-- Each time slice `v s` of a jointly-`ContDiff` field is spatially `ContDiff ℝ n`, obtained by
precomposing `Function.uncurry v` with the affine inclusion `x ↦ (s, x)`. -/
theorem contDiff_apply_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (s : ℝ) :
    ContDiff ℝ n (v s) := by
  have hcomp : ContDiff ℝ n (Function.uncurry v ∘ fun x : E => (s, x)) :=
    h.comp (contDiff_prodMk_right s)
  have heq : (Function.uncurry v ∘ fun x : E => (s, x)) = v s := by funext x; rfl
  rwa [heq] at hcomp

/-- The spatial derivative object `fderiv ℝ (v s)` is a genuine Fréchet derivative of the time slice
`v s` at every point, for a jointly-`ContDiff` field with `1 ≤ n`.  This is the `hDv` input of the
smooth-dependence tower with `Dv := fun s ↦ fderiv ℝ (v s)`. -/
theorem hasFDerivAt_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (v s) (fderiv ℝ (v s) ξ) ξ :=
  (((contDiff_apply_of_contDiff_uncurry h s).differentiable
    ((lt_of_lt_of_le zero_lt_one hn).ne')).differentiableAt).hasFDerivAt

/-- **Joint `(t, x)`-continuity of the spatial derivative** of a jointly-`ContDiff` field
(`1 ≤ n`).  The partial spatial derivative equals the full joint derivative postcomposed with the
inclusion `inr : E →L[ℝ] ℝ × E`, `fderiv ℝ (v t) x = fderiv ℝ (Function.uncurry v) (t, x) ∘L inr`,
and both `p ↦ fderiv ℝ (uncurry v) p` and right-composition with the fixed `inr` are continuous.
This is the `hDvc` input of the smooth-dependence tower. -/
theorem continuous_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (v p.1) p.2) := by
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have key : (fun p : ℝ × E => fderiv ℝ (v p.1) p.2)
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (v p.1)
        ((fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry v ∘ fun x : E => (p.1, x)) = v p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact (h.continuous_fderiv hne).clm_comp continuous_const

/-- **Global Lipschitz bound on the spatial derivative from a second-derivative bound.**  If `v` is
jointly `ContDiff ℝ n` with `2 ≤ n` and the second spatial derivative `fderiv ℝ (fderiv ℝ (v s))` is
globally bounded in operator norm by `L`, then the spatial derivative object `fderiv ℝ (v s)` is
`L`-Lipschitz.  This is the `hDvlip` input of the smooth-dependence tower, obtained from the
mean-value bound `lipschitzWith_of_nnnorm_fderiv_le` together with differentiability of the derivative
(`ContDiff.fderiv_right`). -/
theorem lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    {L : ℝ≥0} (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L) (s : ℝ) :
    LipschitzWith L (fderiv ℝ (v s)) := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_num) hn
  have hdiff : Differentiable ℝ (fderiv ℝ (v s)) :=
    (hvs.fderiv_right (m := 1) hmn).differentiable one_ne_zero
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff (hL s)

/-- **Manifold spatial `C¹` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
field-jet extraction with the tower's `C^{1,1}` manifold regularity theorem
`contMDiff_one_flow_apply_of_lipschitz_deriv`: for a jointly-`ContDiff ℝ n` field `v` (`2 ≤ n`) that
is spatially `K`-Lipschitz and time-continuous, with a globally bounded second spatial derivative, any
integral-curve flow family `Φ` of `v` anchored at `t₀` has each time-`t` map `z ↦ Φ z t` in
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1`.  The field-jet hypotheses `hDv`/`hDvc`/`hDvlip` are supplied here from
the single `ContDiff` hypothesis via `hasFDerivAt_fderiv_of_contDiff_uncurry`,
`continuous_fderiv_of_contDiff_uncurry`, and
`lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le`; this is the first flow-regularity
statement in the tower stated purely in terms of joint `ContDiff` of the field. -/
theorem contMDiff_one_flow_apply_of_contDiff [CompleteSpace E]
    {K L : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_one_flow_apply_of_lipschitz_deriv (Dv := fun s => fderiv ℝ (v s))
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    (fun s => lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le h hn hL s)
    hΦ h0 t

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
