module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Subsingleton-tangent time-derivative closure for `C^3` gauge flows

This module closes the non-identity gauge-pulled metric time-derivative
obligation in the zero-dimensional tangent-fiber case.  No chain-rule
calculation is needed there: every metric component and every corrected
velocity component vanishes.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- On subsingleton tangent fibers, every component of the concrete corrected
velocity for a `C^3` DeTurck gauge vanishes. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v = 0 := by
  have hvel :
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) = 0 :=
    source.toIntrinsicDeTurckSolution.metricVelocity_eq_zero_of_subsingleton_tangent
      ht ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)
  have hu : u = 0 := Subsingleton.elim u 0
  have hv : v = 0 := Subsingleton.elim v 0
  have hvel0 :
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) 0 0 = 0 := by
    simpa [hu, hv] using hvel
  simp [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge,
    hvel0, hu, hv]

/-- On subsingleton tangent fibers, any `C^3` DeTurck gauge supplies the required
time derivative of the gauge-pulled metric. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocity_hasTimeDerivativeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht x u v
  have hmetric :
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
        (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        τ x u v) = fun _ : ℝ ↦ 0 := by
    funext τ
    exact SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) gauge3.maps source.toIntrinsicDeTurckSolution.metric τ x u v
  have hvelocity :
      source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v = 0 :=
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_subsingleton_tangent
      gauge3 ht x u v
  change HasDerivAt
    (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      τ x u v)
    (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t
  rw [hmetric, hvelocity]
  exact (hasDerivAt_const (x := t) (c := (0 : ℝ)) :
    HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) 0 t)

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- Fixed-IVP bundled non-identity `C^3` gauge flows automatically satisfy the
pulled-metric time-derivative obligation on subsingleton tangent fibers. -/
theorem hpullDerivative_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  sol.1.gaugeCorrectedPullbackVelocity_hasTimeDerivativeOn_of_subsingleton_tangent
    (G.gauge sol)

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- Theorem-family bundled non-identity `C^3` gauge flows automatically satisfy
the pulled-metric time-derivative obligation on subsingleton tangent fibers. -/
theorem hpullDerivative_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hpullDerivative_of_subsingleton_tangent sol

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from any
geometric `C^3` intrinsic gauge-flow family on subsingleton tangent fibers,
without an additional time-derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G (G.hpullDerivative_of_subsingleton_tangent)

/-- Intrinsic Ricci-flow theorem-family projection from any geometric `C^3`
intrinsic gauge-flow family on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from any geometric `C^3`
intrinsic gauge-flow family on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G).toOrdinary

end RicciFlow

