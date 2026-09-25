import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointC2PicardRegularity
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckWitnessPhase1

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Conditional flow construction from joint intrinsic `C²`

This file composes the joint geometric-to-coordinate regularity bridge with
the existing cycle-free Picard variational-flow constructor.  The result is a
single theorem for the next constructive boundary: a jointly `C²` intrinsic
DeTurck section, together with chart containment, produces an actual
model-space `VariationalLocalFlowSolution` whose selected time is `t₀`.

The joint intrinsic regularity and chart containment remain explicit.  This
is a composition theorem, not a claim that the current slicewise
`MetricFamily`/`ConnectionFamily` interfaces already provide those premises.
-/

open RicciFlow
open Metric Set
open scoped Manifold ContDiff Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- A jointly intrinsic `C²` DeTurck section feeds the exact Picard package
and then the existing model variational-flow constructor. -/
theorem DeTurckWitnessPhase1.variationalLocalFlowSolution_of_joint_intrinsic_contMDiffOn_two
    [I.Boundaryless]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun r : ℝ × M =>
        (⟨r.2, intrinsicDeTurckGaugeField (I := I) (M := M) g background r.1 r.2⟩ :
          TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p₀).source))
    (hball : Metric.closedBall (extChartAt I p₀ p₀) ((a : ℝ) + 1) ⊆
      (extChartAt I p₀).target) :
    ∃ (tmin tmax : ℝ) (r : ℝ≥0) (t₀' : Icc tmin tmax)
      (_α : @ModelGaugeFlowODE.VariationalLocalFlowSolution
        E _ _ (DeTurckWitnessPhase1.witnessModelField g background p₀)
        (DeTurckWitnessPhase1.witnessModelDerivative g background p₀)
        tmin tmax t₀' (extChartAt I p₀ p₀) r),
      t₀'.1 = t₀ := by
  obtain ⟨hreg, hjoint, hjoint2⟩ :=
    deTurckGaugeCoordinateField_picardRegularityPackage_of_joint_intrinsic_contMDiffOn_two
      (I := I) (M := M) g background p₀
      (t₀ := t₀) (y₀ := extChartAt I p₀ p₀) (a := a) hX hball
  exact DeTurckWitnessPhase1.variationalLocalFlowSolution_of_picardEstimates
    (I := I) (M := M) g background p₀ t₀ a ha hreg hjoint hjoint2
