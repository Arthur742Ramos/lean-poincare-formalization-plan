module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Derivative views of `C^3` DeTurck gauge flows

This small extension module keeps derivative-level gauge-flow adapters out of the
large gauge-reduction file.  It exposes the exact pointwise derivative hypothesis
used by derivative-level non-identity gauge routes from the more geometric
`SatisfiesGaugeFlowOn` statement.
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

/-- The primitive pointwise derivative form of the intrinsic DeTurck gauge-flow equation
for a `C^3` diffeomorphism family. -/
def Diffeomorph3IntrinsicGaugeFlowDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))

/-- A `C^3` diffeomorphism family satisfying the DeTurck gauge-flow equation
also provides the primitive pointwise derivative data expected by the
derivative-level gauge-reduction APIs. -/
theorem SmoothSelfDiffeomorph3Family.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hflow : SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x))) := by
  simpa using hflow.hasMFDerivWithinAt ht x

/-- For `C^3` diffeomorphism families, the geometric intrinsic DeTurck
gauge-flow statement is equivalent to the primitive derivative data used by
the derivative-level theorem packages. -/
theorem SmoothSelfDiffeomorph3Family.satisfiesGaugeFlowOn_intrinsic_iff_derivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s ↔
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  constructor
  · intro hflow t ht x
    exact Φ.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn hflow ht x
  · intro hderiv
    exact SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (Φ := Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (s := s)
      (fun t ht x ↦ hderiv t ht x)

/-- Family-level primitive derivative data for the intrinsic DeTurck gauges of all
chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level derivative data extracted from geometric `C^3` gauge-flow
solutions for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) maps3 := by
  intro ivp sol t ht x
  exact (maps3 ivp sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (hflow ivp sol) ht x

/-- A reusable bundle of geometric `C^3` intrinsic DeTurck gauge flows for all
chosen DeTurck local solutions in a theorem-family argument. -/
structure ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily where
  maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 ivp sol) ivp.initialTime
  satisfies : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- The derivative-family view of a bundled geometric gauge-flow family. -/
theorem derivativeFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) G.maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (I := I) (M := M) G.maps3 G.satisfies

/-- The anchored intrinsic DeTurck gauge associated to one member of a bundled
geometric gauge-flow family. -/
def gauge
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.satisfies ivp sol)

/-- The same anchored gauge, constructed through the derivative-family view.  This
matches derivative-level APIs whose scalar derivative formula references
`of_hasMFDerivWithinAt`. -/
def gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.derivativeFamily ivp sol)

@[simp] theorem gauge_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gauge ivp sol).maps = G.maps3 ivp sol := rfl

@[simp] theorem gaugeViaDerivative_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gaugeViaDerivative ivp sol).maps = G.maps3 ivp sol := rfl

/-- The concrete corrected pullback velocity depends on the underlying `C^3`
diffeomorphism family, not on whether the anchored gauge was constructed from the
geometric flow statement or from its derivative view. -/
@[simp] theorem gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol) =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gaugeViaDerivative ivp sol) := rfl

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

end RicciFlow
