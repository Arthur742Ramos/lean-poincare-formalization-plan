module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFlowVariationalBracketBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Point-4 variational gauge-velocity assembly bridge

The preceding variational bridges turn Picard data into the genuine fixed-chart
Lie-bracket slot.  This module isolates the remaining scalar assembly at one
interior spacetime point.  The only analytic input retained here is the
time-difference identity for the metric-coordinate field; the spatial part is
proved from the fixed-time Levi-Civita calculation, the Picard bracket field,
and the existing pulled-back DeTurck correction theorem.

In particular, the final `hvalue` field is no longer an independent witness
obligation once this exact time-difference identity and the required
differentiability of the DeTurck vector field are available.
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

/-- The one remaining scalar input needed to assemble `FullVariationalWitness`.

It is the exact corrected time derivative of the metric-coordinate field at the
selected chart center.  The spatial `fderivWithin` term is subtracted before
the equality is stated, so this is precisely the temporal contribution to the
full Fréchet derivative along the moving gauge chart.
-/
structure MetricTimeDifferenceData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} (x : M)
    (w : FullVariationalWitness (t := t) G sol x) : Prop where
  htime : ∀ u v : TangentSpace I x,
    let p : M := (G.maps3 sol t) x
    let pu : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x u
    let pv : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x v
    let uE := variationalSourceTangentCoordinate x u
    let vE := variationalSourceTangentCoordinate x v
    let At := variationalTangentCoordinateMap (G.maps3 sol) t t x
    let B' := w.Bfield'
      (1, tangentCoordChange I p p p
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t p))
    B' (At uE) (At vE) -
        ((fderivWithin ℝ
          (fun yE : E ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric p (t, yE))
          (Set.range I) ((extChartAt I p) p))
          (tangentCoordChange I p p p
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t p))
          (At uE) (At vE)) =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv

/-- Pointwise covariant form of the Picard derivative field supplied by the
bracket bridge.  This local helper avoids asking for a global `Df` identity
when the selected `FullVariationalWitness` only carries the chosen point. -/
theorem fullWitness_tangentVectorOfCoordinate_Df_eq_cov_sub_extend
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (w : FullVariationalWitness (t := t) G sol x)
    (u : TangentSpace I x)
    (hW : MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t))
      ((G.maps3 sol t) x)) :
    let p : M := (G.maps3 sol t) x
    let pu : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x u
    let D := w.picard.Df t (w.picard.α.flow (w.picard.x₀, t))
    SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
        (D (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu)) =
      (((chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t) p pu) -
      (((chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t)
        (FiberBundle.extend E pu) p
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t p)) := by
  let p : M := (G.maps3 sol t) x
  let pu : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x u
  let cov := (chosenLeviCivitaFamily (I := I) (M := M)
    sol.1.toIntrinsicDeTurckSolution.metric) t
  let Y : ∀ q : M, TangentSpace I q :=
    intrinsicDeTurckGaugeField (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background t
  let D := w.picard.Df t (w.picard.α.flow (w.picard.x₀, t))
  have hBracket :
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu)) =
        VectorField.mlieBracket I (FiberBundle.extend E pu) Y p := by
    simpa [p, pu, D, Y, variationalTangentVectorOfCoordinate,
      variationalSourceTangentCoordinate,
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using w.hD_bracket u
  have hT : cov.torsion = 0 := by
    exact ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric) t).1
  have hext_mdiff : MDiffAt (T% (FiberBundle.extend E pu)) p := by
    simpa using FiberBundle.mdifferentiableAt_extend (I := I) (F := E) pu
  have hY_mdiff : MDiffAt (T% Y) p := by
    simpa [Y, p] using
      intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt
        (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (t := t) (x := p) hW
  have htor :
      cov Y p ((FiberBundle.extend E pu) p) -
          cov (FiberBundle.extend E pu) p (Y p) =
        VectorField.mlieBracket I (FiberBundle.extend E pu) Y p := by
    exact
      (CovariantDerivative.torsion_eq_zero_iff
        (I := I) (E := E) (M := M) (cov := cov)).mp hT hext_mdiff hY_mdiff
  have hpw : (FiberBundle.extend E pu) p = pu := by
    simp [FiberBundle.extend]
  rw [← htor] at hBracket
  simpa [p, pu, cov, Y, hpw] using hBracket

/-- The exact time-difference identity plus the geometric bracket field
discharges the scalar `hvalue` assembly of a full witness. -/
theorem FullVariationalWitness.hvalue_of_metricTimeDifference
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (w : FullVariationalWitness (t := t) G sol x)
    (hW : MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t))
      ((G.maps3 sol t) x))
    (hdata : MetricTimeDifferenceData (t := t) x w) :
    ∀ u v : TangentSpace I x,
      let uE := variationalSourceTangentCoordinate x u
      let vE := variationalSourceTangentCoordinate x v
      let At := variationalTangentCoordinateMap (G.maps3 sol) t t x
      let Bt := variationalBilinearCoordinateMap
        (G.maps3 sol) sol.1.toIntrinsicDeTurckSolution.metric t t x
      let D := w.picard.Df t (w.picard.α.flow (w.picard.x₀, t))
      let B' := w.Bfield'
        (1, tangentCoordChange I ((G.maps3 sol t) x) ((G.maps3 sol t) x)
          ((G.maps3 sol t) x)
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t
            ((G.maps3 sol t) x)))
      B' (At uE) (At vE) + Bt (D (At uE)) (At vE) +
          Bt (At uE) (D (At vE)) = w.gdot t x u v := by
  intro u v
  let p : M := (G.maps3 sol t) x
  let pu : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x u
  let pv : TangentSpace I p := (G.maps3 sol t).pushforwardTangent x v
  let cu : E := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pu
  let cv : E := SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p pv
  let At := SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
    (I := I) (M := M) (G.maps3 sol) t t x
  let Bt := SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
    (I := I) (M := M) (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric t t x
  let D := w.picard.Df t (w.picard.α.flow (w.picard.x₀, t))
  let Y : ∀ q : M, TangentSpace I q :=
    intrinsicDeTurckGaugeField (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background t
  let Xcoord : E := tangentCoordChange I p p p (Y p)
  let B' := w.Bfield' (1, tangentCoordChange I p p p (Y p))
  let B := (sol.1.toIntrinsicDeTurckSolution.metric t).inner p
  let cov := (chosenLeviCivitaFamily (I := I) (M := M)
    sol.1.toIntrinsicDeTurckSolution.metric) t
  let Au : TangentSpace I p := cov (FiberBundle.extend E pu) p (Y p)
  let Av : TangentSpace I p := cov (FiberBundle.extend E pv) p (Y p)
  let Bu : TangentSpace I p := cov Y p pu
  let Bv : TangentSpace I p := cov Y p pv
  let A : ℝ :=
    (fderivWithin ℝ
      (fun yE : E ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric p (t, yE))
      (Set.range I) ((extChartAt I p) p)) Xcoord cu cv
  have hXcoord : Xcoord = Y p := by
    dsimp [Xcoord]
    rw [tangentCoordChange_self (I := I) (x := p) (z := p) (v := Y p)
      (mem_extChartAt_source (I := I) p)]
  have hAt_u : At (variationalSourceTangentCoordinate x u) = cu := by
    simpa [p, pu, At, cu, variationalTangentCoordinateMap,
      variationalSourceTangentCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) (G.maps3 sol) t x u
  have hAt_v : At (variationalSourceTangentCoordinate x v) = cv := by
    simpa [p, pv, At, cv, variationalTangentCoordinateMap,
      variationalSourceTangentCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_self_sourceTangentCoordinate_eq_targetCoordinate
        (I := I) (M := M) (G.maps3 sol) t x v
  have hBt : Bt (At (variationalSourceTangentCoordinate x u))
      (At (variationalSourceTangentCoordinate x v)) = B pu pv := by
    rw [hAt_u, hAt_v]
    change
      (SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
        (I := I) (M := M) (G.maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric t t x cu cv) = B pu pv
    rw [SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_self_apply_eq]
    simp [p, pu, pv, B, cu, cv,
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate]
  have hA : A =
      (fderivWithin ℝ
        (fun yE : E ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric p (t, yE))
        (Set.range I) ((extChartAt I p) p)) (Y p) cu cv := by
    simpa [A, Xcoord, hXcoord]
  have hspace : A = B Au pv + B pu Av := by
    rw [hA]
    simpa [B, Au, Av, cu, cv, cov] using
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_fixedTime_fderivWithin_sourceTangentCoordinate_eq_chosenLeviCivita_extend
        (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric t p (Y p) pu pv
  have hD_u :
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cu) = Bu - Au := by
    simpa [p, pu, cu, D, Au, Bu, cov, Y] using
      fullWitness_tangentVectorOfCoordinate_Df_eq_cov_sub_extend
        (w := w) (u := u) hW
  have hD_v :
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cv) = Bv - Av := by
    simpa [p, pv, cv, D, Av, Bv, cov, Y] using
      fullWitness_tangentVectorOfCoordinate_Df_eq_cov_sub_extend
        (w := w) (u := v) hW
  have htime' : B' cu cv - A =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv := by
    have htime0 := hdata.htime u v
    dsimp at htime0
    have hAt_u' :
        variationalTangentCoordinateMap (G.maps3 sol) t t x
            (variationalSourceTangentCoordinate x u) = cu := by
      exact hAt_u
    have hAt_v' :
        variationalTangentCoordinateMap (G.maps3 sol) t t x
            (variationalSourceTangentCoordinate x v) = cv := by
      exact hAt_v
    rw [hAt_u', hAt_v'] at htime0
    have hpu : pu = (G.maps3 sol t).tangentMap x u := rfl
    have hpv : pv = (G.maps3 sol t).tangentMap x v := rfl
    rw [hpu, hpv]
    simpa [A, B', Xcoord, p, cu, cv, Y,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate] using htime0
  have hsign : B Bu pv + B pu Bv =
      -intrinsicDeTurckCorrection (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t p pu pv := by
    simpa [B, Bu, Bv, cov, Y] using
      intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection
        (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t p pu pv hW
  have hvelocity : w.gdot t x u v =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv -
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t p pu pv := by
    rw [w.hgdot]
    rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
    rw [sol.1.pullbackSourceDeTurckCorrectionOfDiffeomorph3Gauge_eq_sourceDeTurckCorrection]
    simp only [p, pu, pv,
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.gauge_maps]
    rfl
  have hBt_Du :
      Bt (D (At (variationalSourceTangentCoordinate x u)))
          (At (variationalSourceTangentCoordinate x v)) =
        B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cu)) pv := by
    rw [hAt_u, hAt_v]
    change
      (SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
        (I := I) (M := M) (G.maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric t t x (D cu) cv) =
        B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cu)) pv
    rw [SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_self_apply_eq]
    simp [p, pu, pv, B, cu, cv,
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate]
  have hBt_Dv :
      Bt (At (variationalSourceTangentCoordinate x u))
          (D (At (variationalSourceTangentCoordinate x v))) =
        B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cv)) := by
    rw [hAt_u, hAt_v]
    change
      (SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
        (I := I) (M := M) (G.maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric t t x cu (D cv)) =
        B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cv))
    rw [SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_self_apply_eq]
    simp [p, pu, pv, B, cu, cv,
      SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate,
      SmoothSelfDiffeomorph3Family.sourceTangentCoordinate]
  have hspatialD :
      A + B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cu)) pv +
        B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
          (D cv)) = B Bu pv + B pu Bv := by
    rw [hspace, hD_u, hD_v]
    simp [sub_eq_add_neg]
    abel
  have hsum :
      B' cu cv +
          B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
            (D cu)) pv +
          B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
            (D cv)) = w.gdot t x u v := by
    calc
      B' cu cv +
            B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              (D cu)) pv +
            B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              (D cv)) =
          (B' cu cv - A) +
            (A + B (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
              (D cu)) pv +
              B pu (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p
                (D cv))) := by ring
      _ = sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv +
            (B Bu pv + B pu Bv) := by rw [htime', hspatialD]
      _ = sol.1.toIntrinsicDeTurckSolution.metricVelocity t p pu pv -
            intrinsicDeTurckCorrection (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t p pu pv := by
        rw [hsign]
        ring
      _ = w.gdot t x u v := hvelocity.symm
  change
    B' (At (variationalSourceTangentCoordinate x u))
          (At (variationalSourceTangentCoordinate x v)) +
        Bt (D (At (variationalSourceTangentCoordinate x u)))
          (At (variationalSourceTangentCoordinate x v)) +
        Bt (At (variationalSourceTangentCoordinate x u))
          (D (At (variationalSourceTangentCoordinate x v))) = w.gdot t x u v
  rw [hBt_Du, hBt_Dv, hAt_u, hAt_v]
  exact hsum

/-- The temporal remainder is a constructor-level replacement for the former
`hvalue` witness field.  The bracket identity stays in `w`; only the exact
time-difference input and the DeTurck differentiability hypothesis are new. -/
def FullVariationalWitness.ofMetricTimeDifferenceData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp}
    {sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp}
    {t : ℝ} {x : M}
    (w : FullVariationalWitness (t := t) G sol x)
    (hW : MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t))
      ((G.maps3 sol t) x))
    (hdata : MetricTimeDifferenceData (t := t) x w) :
    FullVariationalWitness (t := t) G sol x :=
  { w with
    hvalue := w.hvalue_of_metricTimeDifference hW hdata }

end DeTurckFlowVariationalWitness

end RicciFlow
