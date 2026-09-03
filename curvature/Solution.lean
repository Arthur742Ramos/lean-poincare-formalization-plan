import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.AutonomousResolventExp

public noncomputable section

namespace PoincareCurvature.Palomar

theorem affineAugment_snd_orbit_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    (NormedSpace.exp ((t - t₀) • RicciFlow.AnalyticPDE.SmoothDependenceCk.affineAugment L b)
      (y₀, 1)).2 = 1 :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.affineAugment_snd_orbit_eq_one L b t₀ y₀ t

theorem affineFundamentalSolution_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) :
    RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t₀ = y₀ :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution_initial L b t₀ y₀

theorem hasDerivAt_affineFundamentalSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    HasDerivAt (RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀)
      (L (RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t) + b) t :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.hasDerivAt_affineFundamentalSolution L b t₀ y₀ t

theorem affineODE_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) {y₁ y₂ : ℝ → E}
    (h1 : ∀ t, HasDerivAt y₁ (L (y₁ t) + b) t)
    (h2 : ∀ t, HasDerivAt y₂ (L (y₂ t) + b) t)
    {t₀ : ℝ} (h : y₁ t₀ = y₂ t₀) (t : ℝ) : y₁ t = y₂ t :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.affineODE_unique L b h1 h2 h t

theorem eq_affineFundamentalSolution_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (L (y t) + b) t) (h0 : y t₀ = y₀) (t : ℝ) :
    y t = RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.eq_affineFundamentalSolution_of_hasDerivAt
    L b t₀ y₀ hy h0 t

theorem norm_affineFundamentalSolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    ‖RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖(y₀, (1 : ℝ))‖ :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.norm_affineFundamentalSolution_le L b t₀ y₀ t

theorem norm_affineFundamentalSolution_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ y₀' : E) (t : ℝ) :
    ‖RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀ t -
        RicciFlow.AnalyticPDE.SmoothDependenceCk.affineFundamentalSolution L b t₀ y₀' t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖y₀ - y₀'‖ :=
  RicciFlow.AnalyticPDE.SmoothDependenceCk.norm_affineFundamentalSolution_sub_le L b t₀ y₀ y₀' t

end PoincareCurvature.Palomar
