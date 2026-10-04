/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Genuine second derivatives under constant linear coordinate/readout maps

The first derivative field below is certified at every point. Its derivative
at the evaluation point is also certified. Constant linear precomposition and
postcomposition then transport the actual iterated Fréchet derivative; no
independent second-jet slot is identified by assumption.
-/

noncomputable section

namespace PoincareCurvature

variable {X E W V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Transport of the actual second derivative through two fixed linear maps. -/
theorem second_fderiv_linear_readout
    (L : X →L[ℝ] E) (R : W →L[ℝ] V)
    (f : E → W) (D : E → E →L[ℝ] W)
    (hD : ∀ y, HasFDerivAt f (D y) y)
    (x : X) (D₂ : E →L[ℝ] E →L[ℝ] W)
    (hD₂ : HasFDerivAt D D₂ (L x)) (a b : X) :
    fderiv ℝ (fderiv ℝ (fun y => R (f (L y)))) x a b =
      R (D₂ (L a) (L b)) := by
  let S : (E →L[ℝ] W) →L[ℝ] X →L[ℝ] V :=
    (ContinuousLinearMap.compL ℝ X W V R).comp
      ((ContinuousLinearMap.compL ℝ X E W).flip L)
  have hfirst : fderiv ℝ (fun y => R (f (L y))) =
      fun y => S (D (L y)) := by
    funext y
    exact ((R.hasFDerivAt.comp y
      ((hD (L y)).comp y L.hasFDerivAt)).fderiv)
  have hsecond : HasFDerivAt (fun y => S (D (L y)))
      (S.comp (D₂.comp L)) x :=
    S.hasFDerivAt.comp x (hD₂.comp x L.hasFDerivAt)
  rw [hfirst, hsecond.fderiv]
  rfl

end PoincareCurvature
