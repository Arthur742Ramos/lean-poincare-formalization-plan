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
open scoped Topology NNReal ContDiff

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

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
