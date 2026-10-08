module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFlowVariationalDataBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Point-4 variational Lie-bracket bridge

This module removes one remaining assumption from the full local witness
boundary.  A Picard variational solution already supplies the linearization
`Df`.  If that linearization is identified with the genuine fixed-chart
derivative of the intrinsic DeTurck gauge field, the existing manifold
calculus bridge proves the `hD_bracket` slot of M4.1.

The derivative identification is kept as an explicit field of the reduced
witness.  It is the analytic model-to-geometry obligation; the theorem below
does not replace it by a proposition or infer it from the ODE equation alone.
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

/-! ### Model-side derivative input -/

/-- The fixed-chart derivative identity needed to turn a Picard linearization
into the geometric Lie-bracket slot.

The `x₀` and `α` fields are deliberately inherited from the actual Picard
witness.  Thus this is a local analytic obligation at the selected base point,
not a free-standing theorem hypothesis about an unrelated ODE. -/
structure ModelBracketDerivativeData
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (picard : DeTurckFlowVariationalWitness.VariationalWitness
      (G.maps3 sol) t x) where
  hDfCoord : ∀ wE : E,
    (picard.Df t (picard.α.flow (picard.x₀, t))) wE =
      (fderivWithin ℝ
        (fun y : E =>
          let p : M := (G.maps3 sol t) x
          let q : M := (extChartAt I p).symm y
          tangentCoordChange I q p q
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t q))
        (Set.range I) ((extChartAt I ((G.maps3 sol t) x)) ((G.maps3 sol t) x))) wE

/-- The fixed-chart derivative input discharges the exact Lie-bracket identity
used by `FullVariationalWitness`. -/
theorem ModelBracketDerivativeData.hD_bracket
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    {picard : DeTurckFlowVariationalWitness.VariationalWitness
      (G.maps3 sol) t x}
    (hdata : ModelBracketDerivativeData (t := t) (x := x) picard) :
    ∀ w : TangentSpace I x,
      variationalTangentVectorOfCoordinate
          ((G.maps3 sol t) x)
          ((picard.Df t (picard.α.flow (picard.x₀, t)))
            (variationalSourceTangentCoordinate
              ((G.maps3 sol t) x) ((G.maps3 sol t).pushforwardTangent x w))) =
        VectorField.mlieBracket I
          (FiberBundle.extend E ((G.maps3 sol t).pushforwardTangent x w))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t)
          ((G.maps3 sol t) x) := by
  intro w
  let p : M := (G.maps3 sol t) x
  let pw : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x w
  let cw : E :=
    SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pw
  let V : E → E := fun y : E =>
    let q : M := (extChartAt I p).symm y
    tangentCoordChange I q p q
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t q)
  have hDf :
      (picard.Df t (picard.α.flow (picard.x₀, t))) cw =
        (fderivWithin ℝ V (Set.range I) ((extChartAt I p) p)) cw := by
    simpa [p, pw, cw, V] using hdata.hDfCoord cw
  have hGaugeCoord :
      (VectorField.mpullbackWithin (𝓘(ℝ, E)) I (extChartAt I p).symm
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t)
        (Set.range I)) =ᶠ[𝓝[Set.range I] ((extChartAt I p) p)] V := by
    simpa [V] using
      SmoothSelfDiffeomorph3Family.mpullbackWithin_extChartAt_symm_eventuallyEq_tangentCoordChange
        (I := I) (M := M) p
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t)
  have hLie :=
    SmoothSelfDiffeomorph3Family.mlieBracket_extend_eq_tangentVectorOfCoordinate_fderivWithin_of_eventuallyEq_mpullbackWithin
      (I := I) (M := M) p pw
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t)
      V hGaugeCoord
  change
    SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
        ((picard.Df t (picard.α.flow (picard.x₀, t))) cw) =
      VectorField.mlieBracket I (FiberBundle.extend E pw)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t) p
  rw [hDf]
  exact hLie.symm

/-- Construct a complete local witness while leaving only the fixed-chart
linearization as the model-side analytic input.

The constructor is intentionally explicit about `hvalue`: proving the
gauge-corrected velocity assembly is a separate geometric calculation and is
not obtained from the bracket bridge. -/
def FullVariationalWitness.ofModelBracketDerivativeData
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
    (hvalue : ∀ u v : TangentSpace I x,
      let uE := variationalSourceTangentCoordinate x u
      let vE := variationalSourceTangentCoordinate x v
      let At := variationalTangentCoordinateMap (G.maps3 sol) t t x
      let Bt := variationalBilinearCoordinateMap
        (G.maps3 sol) sol.1.toIntrinsicDeTurckSolution.metric t t x
      let D := picard.Df t (picard.α.flow (picard.x₀, t))
      let B' := Bfield'
        (1, tangentCoordChange I ((G.maps3 sol t) x) ((G.maps3 sol t) x)
          ((G.maps3 sol t) x)
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t
            ((G.maps3 sol t) x)))
      B' (At uE) (At vE) + Bt (D (At uE)) (At vE) +
          Bt (At uE) (D (At vE)) = gdot t x u v)
    (hbracket : ModelBracketDerivativeData (t := t) (x := x) picard) :
    FullVariationalWitness (t := t) G sol x where
  gdot := gdot
  hgdot := hgdot
  picard := picard
  Bfield' := Bfield'
  hBfield := hBfield
  hD_bracket := hbracket.hD_bracket
  hvalue := hvalue

end DeTurckFlowVariationalWitness

end RicciFlow
