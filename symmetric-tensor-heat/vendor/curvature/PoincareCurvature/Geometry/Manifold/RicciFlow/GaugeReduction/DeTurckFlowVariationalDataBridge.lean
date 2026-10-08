module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFlowVariationalWitness

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Point-4 variational-data bridge

This module assembles the pieces which are already supplied by a genuine local
Picard variational witness into the exact per-point data consumed by
Milestone 4.1.  It deliberately works only at times where the selected
solution time set is a neighborhood of the time: the endpoint version still
needs a separate closed-interval chart argument.

The bridge discharges two bookkeeping steps that should not be repeated by
every eventual construction:

* the Picard tangent equation gives the derivative of the coordinate
  pushforward map;
* a Fréchet derivative of the metric-coordinate field gives the derivative of
  the moving bilinear coordinate map.

The Lie-bracket identity and the final gauge-velocity assembly remain explicit
fields of `FullVariationalWitness`.  They are the genuine geometric analytic
obligations, not assumptions hidden in an adapter.
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

/-! ### Interior variational-data boundary -/

/-- The portion of `HasVariationalData` which is meaningful at times whose
solution time set is a neighborhood.  It is separated from the ordinary flow
record so endpoint data cannot be inferred from relative-time derivatives. -/
def HasInteriorVariationalData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
      sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t → ∀ x : M,
      ∃ gdot : MetricTensorFamily (I := I) (M := M),
        gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (G.gauge sol) ∧
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
          (I := I) (M := M)
          (G.maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          gdot t x

/-- A local Picard witness together with the remaining geometric scalar data.

`hBfield` is a genuine Fréchet derivative of the metric-coordinate field.
The bridge turns it into the derivative of the moving bilinear coordinate map;
the `hD_bracket` and `hvalue` fields are retained verbatim because they are the
actual Lie-bracket and gauge-velocity calculations still needed for M4.1. -/
structure FullVariationalWitness
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (x : M) where
  gdot : MetricTensorFamily (I := I) (M := M)
  hgdot : gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
    (G.gauge sol)
  picard : DeTurckFlowVariationalWitness.VariationalWitness
    (G.maps3 sol) t x
  Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)
  hBfield : HasFDerivAt
    (SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution.metric
      ((G.maps3 sol t) x))
    Bfield'
    (t, (extChartAt I ((G.maps3 sol t) x)) ((G.maps3 sol t) x))
  hD_bracket : ∀ w : TangentSpace I x,
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
        ((G.maps3 sol t) x)
  hvalue : ∀ u v : TangentSpace I x,
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
        Bt (At uE) (D (At vE)) = gdot t x u v

/-- Assemble exact M4.1 variational data from a full local witness.

The tangent derivative comes from the Picard variational equation.  The
bilinear derivative comes from the named metric-coordinate field and the
ordinary-neighborhood chart lemma.  No endpoint or full compact-manifold
construction is inferred here. -/
theorem FullVariationalWitness.toVariationalData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hnhds : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (w : FullVariationalWitness (t := t) G sol x) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
      (I := I) (M := M)
      (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      w.gdot t x := by
  let R : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    { maps3 := G.maps3 sol
      anchored := G.anchored sol
      satisfies := G.satisfies sol }
  let D : E →L[ℝ] E := w.picard.Df t (w.picard.α.flow (w.picard.x₀, t))
  let B' : E →L[ℝ] E →L[ℝ] ℝ := w.Bfield'
    (1, tangentCoordChange I ((G.maps3 sol t) x) ((G.maps3 sol t) x)
      ((G.maps3 sol t) x)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
        ((G.maps3 sol t) x)))
  refine ⟨D, B', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [R] using R.eventually_mem_trivializationAt_eval hnhds x
  · have hx₀ : w.picard.x₀ ∈ Metric.closedBall w.picard.x₀ w.picard.r := by
      rw [Metric.mem_closedBall, dist_self]
      exact NNReal.coe_nonneg w.picard.r
    have htan := w.picard.α.tangent_hasDerivAt_of_mem_Ioo hx₀
      w.picard.htIoo
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) (G.maps3 sol) t τ x) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ w.picard.α.tangent w.picard.x₀ τ) := by
      apply Filter.eventuallyEq_of_mem
        (Icc_mem_nhds w.picard.htIoo.1 w.picard.htIoo.2)
      intro τ hτ
      exact (w.picard.htangent τ hτ).symm
    have hderiv := htan.congr_of_eventuallyEq hEq
    have htIcc : t ∈ Icc w.picard.tmin w.picard.tmax :=
      Ioo_subset_Icc_self w.picard.htIoo
    have hAt := w.picard.htangent t htIcc
    rw [hAt] at hderiv
    change HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t τ x)
      (D.comp
        (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t t x)) t
    simpa [D] using hderiv
  · have hBmap :=
      R.pullbackMetricBilinearCoordinateMap_hasDerivAt_of_metricCoordinateField_hasFDerivAt
        hnhds sol.1.toIntrinsicDeTurckSolution.metric x w.hBfield
    change HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
          (I := I) (M := M) (G.maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric t τ x)
      B' t
    simpa [R, B'] using hBmap
  · simpa [D] using w.hD_bracket
  · simpa [D, B'] using w.hvalue

/-- A family of full local witnesses supplies the interior variational-data
predicate.  The neighborhood premise is intentionally explicit, so this
constructor cannot silently turn endpoint-relative data into ordinary data. -/
theorem hasInteriorVariationalData_of_fullWitness
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hwitness : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t → ∀ x : M,
        Nonempty (FullVariationalWitness (t := t) G sol x)) :
    HasInteriorVariationalData G := by
  intro sol t ht hnhds x
  obtain ⟨w⟩ := hwitness sol ht hnhds x
  exact ⟨w.gdot, w.hgdot, w.toVariationalData ht hnhds⟩

end DeTurckFlowVariationalWitness

end RicciFlow
