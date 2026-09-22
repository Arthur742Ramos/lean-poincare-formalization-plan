import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckPicardRegularityReduction
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.GaugeFlowAssembly

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Fixed-time regularity of the geometric DeTurck coordinate field

The Picard reduction consumes the chart field
`deTurckGaugeCoordinateField`.  The intrinsic DeTurck regularity lemmas already
give a fixed-time `C¹` tangent-bundle section when the chosen background
connection slice is `C¹`, while `GaugeFlowAssembly` gives `C¹` regularity of a
chart pushforward from such a section.  This file connects those two facts to
the exact chart-field definition used by the variational witness.

This is deliberately a fixed-time result.  It does not provide the missing
`C²` spatial estimate or any time regularity; those remain explicit inputs to
the Picard estimates and the variational flow construction.
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

/-! The generic coordinate identity used below. -/

theorem chartPushforwardField_extChartAt_eq_fromTangentSpace_mfderiv
    (X : ℝ → M → E) (p₀ x : M) (t : ℝ)
    (hx : x ∈ (extChartAt I p₀).source) :
    PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p₀ t
        (extChartAt I p₀ x) =
      NormedSpace.fromTangentSpace (extChartAt I p₀ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) x (X t x)) := by
  rw [PoincareCurvature.GaugeFlowAssembly.chartPushforwardField_extChartAt X t hx]
  rw [tangentCoordChange_def]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · apply mdifferentiableAt_extChartAt
    simpa only [extChartAt_source] using hx

/-! **The actual fixed-time coordinate regularity theorem.** -/

theorem deTurckGaugeCoordinateField_contDiffOn_fixedTime_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContDiffOn ℝ (1 : ℕ∞)
      (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
      (extChartAt I p₀).target := by
  let X : ℝ → M → E := intrinsicDeTurckGaugeField (I := I) (M := M) g background
  have hXfull : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y : M => (⟨y, X t y⟩ : TangentBundle I M)) := by
    intro x
    have hvec := intrinsicDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
      (I := I) (M := M) g background t hbackground x
    simpa [X, intrinsicDeTurckGaugeField] using hvec.neg_section
  have hXon : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun y : M => (⟨y, X t y⟩ : TangentBundle I M))
      (extChartAt I p₀).source := by
    intro x hx
    exact (hXfull x).contMDiffWithinAt
  have hchart :=
    PoincareCurvature.GaugeFlowAssembly.contDiffOn_chartPushforwardField
      (I := I) (M := M) (n := (1 : ℕ∞)) (X := X) (p := p₀) (τ := t) hXon
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

end RicciFlow
