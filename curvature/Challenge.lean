import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public noncomputable section

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The augmented generator `(v, s) ↦ (L v + s • b, 0)` for an affine ODE. -/
noncomputable def affineAugment (L : E →L[ℝ] E) (b : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ E ℝ)
      + (ContinuousLinearMap.snd ℝ E ℝ).smulRight b).prod (0 : (E × ℝ) →L[ℝ] ℝ)

/-- First coordinate of the augmented operator-exponential orbit through `(y₀, 1)`. -/
noncomputable def affineFundamentalSolution
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) : E :=
  (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)).1

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow

namespace PoincareCurvature.Palomar

theorem affineAugment_snd_orbit_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    (NormedSpace.exp ((t - t₀) • RicciFlow.AnalyticPDE.SmoothDependenceCk.affineAugment L b)
      (y₀, 1)).2 = 1 := by
  sorry

theorem affineFundamentalSolution_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) :
    RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t₀ = y₀ := by
  sorry

theorem hasDerivAt_affineFundamentalSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    HasDerivAt (RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀)
      (L (RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t) + b) t := by
  sorry

theorem affineODE_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) {y₁ y₂ : ℝ → E}
    (h1 : ∀ t, HasDerivAt y₁ (L (y₁ t) + b) t)
    (h2 : ∀ t, HasDerivAt y₂ (L (y₂ t) + b) t)
    {t₀ : ℝ} (h : y₁ t₀ = y₂ t₀) (t : ℝ) : y₁ t = y₂ t := by
  sorry

theorem eq_affineFundamentalSolution_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (L (y t) + b) t) (h0 : y t₀ = y₀) (t : ℝ) :
    y t = RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t := by
  sorry

theorem norm_affineFundamentalSolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    ‖RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖(y₀, (1 : ℝ))‖ := by
  sorry

theorem norm_affineFundamentalSolution_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ y₀' : E) (t : ℝ) :
    ‖RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t -
        RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀' t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖y₀ - y₀'‖ := by
  sorry

end PoincareCurvature.Palomar
