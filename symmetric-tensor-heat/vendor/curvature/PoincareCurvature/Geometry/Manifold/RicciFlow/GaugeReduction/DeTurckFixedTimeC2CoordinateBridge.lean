import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFixedTimeRegularity

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# The fixed-time `C²` chart bridge for the geometric DeTurck field

The Picard estimates need a `C²` coordinate field at each fixed time.  The
preceding fixed-time module proves the actual coordinate identification and
derives `C¹` from the intrinsic DeTurck section under the regularity available
for the current `MetricFamily` interface.  This file records the next exact
bridge: any independently established intrinsic `C²` tangent-bundle section
regularity is transported to `C²` regularity of the genuine
`deTurckGaugeCoordinateField`.

The intrinsic `C²` premise is intentional.  A `MetricFamily` only registers a
`C²` metric, whose Levi-Civita connection is currently available at the `C¹`
level; this theorem does not pretend to manufacture the missing parabolic
regularity or an extra derivative from that interface.
-/

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Transport an intrinsic fixed-time `C²` DeTurck section through the actual
chart-field definition.  The premise is on the tangent-bundle section, not on
an unrelated coordinate function. -/
theorem deTurckGaugeCoordinateField_contDiffOn_fixedTime_of_intrinsic_contMDiffOn_two
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t : ℝ)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x : M =>
        (⟨x, intrinsicDeTurckGaugeField (I := I) (M := M) g background t x⟩ :
          TangentBundle I M))
      (extChartAt I p₀).source) :
    ContDiffOn ℝ (2 : ℕ∞)
      (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
      (extChartAt I p₀).target := by
  let X : ℝ → M → E := intrinsicDeTurckGaugeField (I := I) (M := M) g background
  have hchart :=
    PoincareCurvature.GaugeFlowAssembly.contDiffOn_chartPushforwardField
      (I := I) (M := M) (n := (2 : ℕ∞)) (X := X) (p := p₀) (τ := t) hX
  refine hchart.congr (fun y hy => ?_)
  let x := (extChartAt I p₀).symm y
  have hx : x ∈ (extChartAt I p₀).source := (extChartAt I p₀).map_target hy
  have hxy : extChartAt I p₀ x = y := (extChartAt I p₀).right_inv hy
  change NormedSpace.fromTangentSpace
      ((extChartAt I p₀) ((extChartAt I p₀).symm y))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) ((extChartAt I p₀).symm y)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          ((extChartAt I p₀).symm y))) =
    PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p₀ t y
  rw [← hxy]
  rw [(extChartAt I p₀).left_inv hx]
  symm
  exact chartPushforwardField_extChartAt_eq_fromTangentSpace_mfderiv X p₀ x t hx

/-! **The fixed-time Picard Lipschitz package.** -/

/-- A fixed-time intrinsic `C²` section supplies the two spatial Lipschitz bounds
needed by the variational Picard estimate on a closed coordinate ball.  The
slightly larger closed ball is the explicit chart-containment buffer; no
uniformity in time is asserted here. -/
theorem exists_lipschitzOnWith_deTurckGaugeCoordinateField_and_derivative_of_intrinsic_contMDiffOn_two
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t : ℝ)
    {y₀ : E} {a : ℝ≥0}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x : M =>
        (⟨x, intrinsicDeTurckGaugeField (I := I) (M := M) g background t x⟩ :
          TangentBundle I M))
      (extChartAt I p₀).source)
    (hball : Metric.closedBall y₀ ((a : ℝ) + 1) ⊆ (extChartAt I p₀).target) :
    ∃ Kf KD : ℝ≥0,
      LipschitzOnWith Kf
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
        (Metric.closedBall y₀ (a : ℝ)) ∧
      LipschitzOnWith KD
        (deTurckGaugeCoordinateDerivative (I := I) (M := M) g background p₀ t)
        (Metric.closedBall y₀ (a : ℝ)) := by
  let f : E → E :=
    deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t
  have hf₂ : ContDiffOn ℝ (2 : ℕ∞) f (extChartAt I p₀).target := by
    simpa [f] using
      deTurckGaugeCoordinateField_contDiffOn_fixedTime_of_intrinsic_contMDiffOn_two
        (I := I) (M := M) g background p₀ t hX
  have hball_open_sub : Metric.ball y₀ ((a : ℝ) + 1) ⊆ (extChartAt I p₀).target :=
    Metric.ball_subset_closedBall.trans hball
  have hclosed_sub : Metric.closedBall y₀ (a : ℝ) ⊆ Metric.ball y₀ ((a : ℝ) + 1) := by
    exact Metric.closedBall_subset_ball (by linarith [show (0 : ℝ) ≤ a from a.coe_nonneg])
  have hf₂_open : ContDiffOn ℝ (2 : ℕ∞) f (Metric.ball y₀ ((a : ℝ) + 1)) :=
    hf₂.mono hball_open_sub
  have hf₁_closed : ContDiffOn ℝ (1 : ℕ∞) f (Metric.closedBall y₀ (a : ℝ)) :=
    (hf₂_open.of_le (by norm_num)).mono hclosed_sub
  have hconv : Convex ℝ (Metric.closedBall y₀ (a : ℝ)) := convex_closedBall y₀ a
  have hcompact : IsCompact (Metric.closedBall y₀ (a : ℝ)) :=
    isCompact_closedBall y₀ a
  obtain ⟨Kf, hKf⟩ := hf₁_closed.exists_lipschitzOnWith (by norm_num) hconv hcompact
  have hfderiv₁_open : ContDiffOn ℝ (1 : ℕ∞) (fun y => fderiv ℝ f y)
      (Metric.ball y₀ ((a : ℝ) + 1)) :=
    hf₂_open.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hfderiv₁_closed : ContDiffOn ℝ (1 : ℕ∞) (fun y => fderiv ℝ f y)
      (Metric.closedBall y₀ (a : ℝ)) :=
    hfderiv₁_open.mono hclosed_sub
  obtain ⟨KD, hKD⟩ :=
    hfderiv₁_closed.exists_lipschitzOnWith (by norm_num) hconv hcompact
  refine ⟨Kf, KD, hKf, ?_⟩
  change LipschitzOnWith KD (fun y => fderiv ℝ f y) (Metric.closedBall y₀ (a : ℝ))
  exact hKD

end RicciFlow
