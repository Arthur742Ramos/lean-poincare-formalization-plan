module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFlowVariationalTimeBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Point-4 chosen-background assembly bridge

The chosen DeTurck solution records that its background connection is the
Levi-Civita connection of the intrinsic metric.  Its existing regularity
theorem therefore supplies the pointwise differentiability of the intrinsic
DeTurck vector field required by the variational assembly bridge.  This module
packages that consequence and removes the duplicate pointwise hypothesis from
the conditional `hvalue` constructor.  Together with the witness-core
constructor below, it also gives the first direct route from constructive
geometric inputs to a `FullVariationalWitness`.
-/

@[expose] public noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

namespace DeTurckFlowVariationalWitness

open ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- The chosen solution's Levi-Civita background gives the differentiability
needed by the variational assembly at every selected time and image point. -/
theorem chosenSolution_intrinsicDeTurckVectorField_mdiffAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t)) x := by
  exact intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
    (I := I) (M := M)
    sol.1.toIntrinsicDeTurckSolution.metric
    sol.1.toIntrinsicDeTurckSolution.background t
    (sol.background_contMDiff t) x

/-- Reuse the chosen-background differentiability result to assemble `hvalue`
from the temporal remainder, without repeating the pointwise `hW` argument. -/
def FullVariationalWitness.ofMetricTimeDifferenceData_of_chosenBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (w : FullVariationalWitness (t := t) G sol x)
    (hdata : MetricTimeDifferenceData (t := t) x w.toCore) :
    FullVariationalWitness (t := t) G sol x :=
  w.ofMetricTimeDifferenceData
    (chosenSolution_intrinsicDeTurckVectorField_mdiffAt
      (I := I) (M := M) sol (t := t) ((G.maps3 sol t) x))
    hdata

/-- Build the witness core from the explicit geometric and model-side inputs,
without asking for the scalar assembly as a separate hypothesis. -/
def FullVariationalWitnessCore.ofModelBracketDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (gdot : MetricTensorFamily (I := I) (M := M))
    (hgdot : gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
      (G.gauge sol))
    (picard : DeTurckFlowVariationalWitness.VariationalWitness
      (G.maps3 sol) t x)
    (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
    (hBfield : HasFDerivAt
      (SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution.metric
        ((G.maps3 sol t) x))
      Bfield'
      (t, (extChartAt I ((G.maps3 sol t) x)) ((G.maps3 sol t) x)))
    (hbracket : ModelBracketDerivativeData (t := t) (x := x) picard) :
    FullVariationalWitnessCore (t := t) G sol x where
  gdot := gdot
  hgdot := hgdot
  picard := picard
  Bfield' := Bfield'
  hBfield := hBfield
  hD_bracket := hbracket.hD_bracket

/-- The chosen solution supplies the metric velocity canonically, so callers
only need to provide the genuinely analytic Picard, Fréchet, and bracket data.
-/
def FullVariationalWitnessCore.ofModelBracketDerivativeData_of_gaugeCorrectedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (picard : DeTurckFlowVariationalWitness.VariationalWitness
      (G.maps3 sol) t x)
    (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
    (hBfield : HasFDerivAt
      (SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution.metric
        ((G.maps3 sol t) x))
      Bfield'
      (t, (extChartAt I ((G.maps3 sol t) x)) ((G.maps3 sol t) x)))
    (hbracket : ModelBracketDerivativeData (t := t) (x := x) picard) :
    FullVariationalWitnessCore (t := t) G sol x :=
  FullVariationalWitnessCore.ofModelBracketDerivativeData
    (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
    rfl picard Bfield' hBfield hbracket

/-- The chosen solution's time derivative supplies the temporal input needed
to complete a witness core once the core's geometric bracket data is present. -/
def FullVariationalWitnessCore.toFullVariationalWitness_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (w : FullVariationalWitnessCore (t := t) G sol x)
    (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) :
    FullVariationalWitness (t := t) G sol x :=
  w.toFullVariationalWitness_of_metricTimeDifferenceData
    (chosenSolution_intrinsicDeTurckVectorField_mdiffAt
      (I := I) (M := M) sol (t := t) ((G.maps3 sol t) x))
    (metricTimeDifferenceData_of_hasTimeDerivativeOn ht w)

end DeTurckFlowVariationalWitness

end RicciFlow
