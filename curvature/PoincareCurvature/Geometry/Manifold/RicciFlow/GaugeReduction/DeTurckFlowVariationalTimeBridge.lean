module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFlowVariationalAssemblyBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Point-4 variational time bridge

The intrinsic DeTurck solution already carries the ordinary tensor time
derivative of its metric.  This module isolates the corresponding temporal
component of the named two-variable metric-coordinate field and feeds it into
the `MetricTimeDifferenceData` interface used by the variational assembly
bridge.  The spatial derivative remains the genuine `fderivWithin` term; no
coordinate smoothness or gauge-flow construction is inferred here.
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

/-! The time derivative of the metric-coordinate field is already available
from the intrinsic solution's tensor derivative. -/

theorem metricTimeDifferenceData_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (w : FullVariationalWitness (t := t) G sol x) :
    MetricTimeDifferenceData (t := t) x w := by
  refine ⟨?_⟩
  intro u v
  let p : M := (G.maps3 sol t) x
  let pu : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x u
  let pv : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x v
  let cu : E := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate
    (I := I) (M := M) p pu
  let cv : E := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate
    (I := I) (M := M) p pv
  let At : E →L[ℝ] E :=
    SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
      (I := I) (M := M) (G.maps3 sol) t t x
  let Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ :=
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution.metric p
  let q : E := (extChartAt I p) p
  let Yp : TangentSpace I p :=
    intrinsicDeTurckGaugeField (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background t p
  let Xcoord : E := tangentCoordChange I p p p Yp
  let B' := w.Bfield' (1, Xcoord)
  let spatial : E →L[ℝ] E →L[ℝ] ℝ :=
    (fderivWithin ℝ
      (fun yE : E ↦ Bfield (t, yE))
      (Set.range I) q) Xcoord
  have hBfield' : HasFDerivAt Bfield w.Bfield' (t, q) := by
    simpa [Bfield, q, p] using w.hBfield
  have hmetric := intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution
  have htime_center :=
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M) (hmetric ht) p cu cv
  have htime_center' :
      HasDerivAt (fun τ : ℝ ↦ Bfield (τ, q) cu cv)
        (sol.1.toIntrinsicDeTurckSolution.metricVelocity t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cu)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cv)) t := by
    simpa [Bfield, q, cu, cv, p, pu, pv] using htime_center
  have htime_from_frechet :
      HasDerivAt (fun τ : ℝ ↦ Bfield (τ, q) cu cv)
        (w.Bfield' (1, 0) cu cv) t := by
    have hcurve :=
      hasDerivAt_bilinearFormField_along_curve
        (Bfield := Bfield) (Bfield' := w.Bfield')
        (y := fun _ : ℝ ↦ q) (y' := 0) (t := t)
        hBfield' (hasDerivAt_const t q)
    have hcurve' := hcurve.clm_apply (hasDerivAt_const t cu)
    have hcurve'' := hcurve'.clm_apply (hasDerivAt_const t cv)
    simpa [Bfield, q, B', ContinuousLinearMap.add_apply] using hcurve''
  have htime_zero :
      w.Bfield' (1, 0) cu cv =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cu)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cv) :=
    htime_from_frechet.unique htime_center'
  have hspace_fderiv :
      fderivWithin ℝ (fun yE : E ↦ Bfield (t, yE)) (Set.range I) q =
        w.Bfield'.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hslice :
        HasFDerivAt (fun yE : E ↦ Bfield (t, yE))
          (w.Bfield'.comp (ContinuousLinearMap.inr ℝ ℝ E)) q := by
      simpa [Bfield, q, Function.comp_def] using
        HasFDerivAt.comp
          (f := fun yE : E ↦ (t, yE))
          (g := Bfield) (g' := w.Bfield') (x := q)
          hBfield'
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) t q)
    have hq : q ∈ Set.range I := by
      simpa [q] using
        extChartAt_target_subset_range (I := I) p (mem_extChartAt_target (I := I) p)
    exact hslice.hasFDerivWithinAt.fderivWithin (I.uniqueDiffOn q hq)
  have hspace_apply :
      spatial cu cv = w.Bfield' (0, Xcoord) cu cv := by
    change (fderivWithin ℝ (fun yE : E ↦ Bfield (t, yE))
      (Set.range I) q) Xcoord cu cv = _
    rw [hspace_fderiv]
    rfl
  have htime_at_center :
      (w.Bfield' (1, Xcoord) cu cv - spatial cu cv) =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cu)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate
            (I := I) (M := M) p cv) := by
    rw [hspace_apply]
    have hfirst : ((1 : ℝ), Xcoord) = ((1 : ℝ), (0 : E)) + ((0 : ℝ), Xcoord) := by
      ext <;> simp
    have hlinear :
        w.Bfield' ((1 : ℝ), Xcoord) =
          w.Bfield' ((1 : ℝ), (0 : E)) + w.Bfield' ((0 : ℝ), Xcoord) := by
      calc
        w.Bfield' ((1 : ℝ), Xcoord) =
            w.Bfield' (((1 : ℝ), (0 : E)) + ((0 : ℝ), Xcoord)) := by rw [hfirst]
        _ = w.Bfield' ((1 : ℝ), (0 : E)) + w.Bfield' ((0 : ℝ), Xcoord) :=
          w.Bfield'.map_add _ _
    have hlinear' := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L cu cv) hlinear
    simp only [ContinuousLinearMap.add_apply] at hlinear'
    rw [htime_zero] at hlinear'
    linarith
  have hAt_u :
      At (variationalSourceTangentCoordinate x u) = cu := by
    simpa [p, pu, At, cu, variationalTangentCoordinateMap,
      variationalSourceTangentCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) (G.maps3 sol) t x u
  have hAt_v :
      At (variationalSourceTangentCoordinate x v) = cv := by
    simpa [p, pv, At, cv, variationalTangentCoordinateMap,
      variationalSourceTangentCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) (G.maps3 sol) t x v
  change
    B' (At (variationalSourceTangentCoordinate x u))
        (At (variationalSourceTangentCoordinate x v)) -
      (fderivWithin ℝ (fun yE : E ↦ Bfield (t, yE)) (Set.range I) q)
        Xcoord (At (variationalSourceTangentCoordinate x u))
        (At (variationalSourceTangentCoordinate x v)) =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv
  rw [hAt_u, hAt_v]
  simpa [B', Bfield, p, pu, pv, cu, cv, Xcoord, Yp, q, spatial] using
    htime_at_center

end DeTurckFlowVariationalWitness

end RicciFlow
