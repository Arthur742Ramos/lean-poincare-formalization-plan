module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Existence interfaces for `C^3` DeTurck gauge flows

This module isolates the remaining raw gauge-flow existence obligation from the
Ricci-flow theorem packages.  A future manifold ODE-flow construction should
produce `Diffeomorph3GaugeFlowOn` witnesses; this file turns those witnesses into
the fixed-IVP and theorem-family geometric gauge-flow bundles consumed by the
endpoint Ricci-flow APIs.
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

/-- A concrete `C^3` diffeomorphism flow for a time-dependent vector field on a
time set, anchored at a base time.  This is the raw object expected from the
future manifold ODE-flow existence theorem. -/
structure Diffeomorph3GaugeFlowOn
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps3 t₀
  satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
    maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s

namespace Diffeomorph3GaugeFlowOn

/-- If the time-dependent vector field vanishes on the time set, the identity `C³`
diffeomorphism family is a raw gauge flow. -/
noncomputable def identity_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)
  anchored := SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t₀
  satisfies := SmoothSelfDiffeomorph3Family.id_satisfiesGaugeFlowOn_of_eq_zero
    (I := I) (M := M) (X := X) (s := s) hX

/-- Derivative form of a raw `C^3` diffeomorphism flow. -/
theorem hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) := by
  simpa using G.satisfies.hasMFDerivWithinAt ht x

/-- Specialize a raw flow for the intrinsic DeTurck vector field to the anchored
gauge object used by gauge reduction. -/
def toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M) (g := g) (background := background)
    (s := s) (t₀ := t₀) G.maps3 G.anchored G.satisfies

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).maps = G.maps3 := rfl

end Diffeomorph3GaugeFlowOn

/-- Raw intrinsic DeTurck `C^3` gauge-flow existence data for every chosen
DeTurck local solution of a fixed initial-value problem. -/
structure IntrinsicDeTurckGaugeFlowExistence
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  flow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistence

/-- Chosen-background intrinsic DeTurck solutions have zero intrinsic DeTurck gauge field, so the
identity diffeomorphism family supplies the raw `C³` gauge-flow existence data for a fixed IVP. -/
noncomputable def identityOfChosenBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (fun t _ht x ↦ by
        have hLC :
            CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
              (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background :=
          usesChosenBackground_isLeviCivita
            (I := I) (M := M) sol.1 sol.2
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background hLC
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- When every tangent fiber is a subsingleton, the intrinsic DeTurck vector field vanishes
identically, so the identity `C³` diffeomorphism family supplies the raw gauge-flow existence
data for any chosen DeTurck local solution of a fixed initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (fun t _ht x ↦ by
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_subsingleton_tangent
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, every tangent fiber is automatically subsingleton, so the identity `C³` family
supplies raw gauge-flow existence data. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  identityOfSubsingletonTangent (I := I) (M := M) ivp

/-- On an empty manifold, the gauge-flow obligation is vacuous, so the identity `C³` diffeomorphism
family supplies the raw gauge-flow existence data for any chosen DeTurck local solution of a fixed
initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (fun _t _ht x ↦ isEmptyElim x)
def toDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := fun sol ↦ (G.flow sol).maps3
  anchored := fun sol ↦ (G.flow sol).anchored
  satisfies := fun sol ↦ (G.flow sol).satisfies

@[simp] theorem toDiffeomorph3GaugeFlow_maps3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.maps3 sol) = (G.flow sol).maps3 := rfl

end IntrinsicDeTurckGaugeFlowExistence

/-- The theorem-family version of raw intrinsic DeTurck `C^3` gauge-flow
existence data. -/
structure IntrinsicDeTurckGaugeFlowExistenceFamily where
  flow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistenceFamily

/-- Chosen-background intrinsic DeTurck solutions admit the identity raw `C³` gauge flow for every
initial-value problem. -/
noncomputable def identityOfChosenBackground :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- When every tangent fiber is a subsingleton, the identity `C³` diffeomorphism family supplies
the raw gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, the identity `C³` diffeomorphism family supplies raw gauge-flow existence data for
every initial-value problem. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  identityOfSubsingletonTangent (I := I) (M := M)

/-- On an empty manifold, the identity `C³` diffeomorphism family supplies the raw gauge-flow
existence data vacuously for every initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Restrict theorem-family raw gauge-flow existence data to one initial-value
problem. -/
def forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := G.flow ivp

/-- Turn theorem-family raw intrinsic gauge-flow existence data into the
geometric gauge-flow family consumed by endpoint routes. -/
def toDiffeomorph3GaugeFlowFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M) where
  maps3 := fun ivp sol ↦ (G.flow ivp sol).maps3
  anchored := fun ivp sol ↦ (G.flow ivp sol).anchored
  satisfies := fun ivp sol ↦ (G.flow ivp sol).satisfies

/-- The family-level chosen-background raw flow induces the same anchored gauge as the existing
identity `C³` gauge attached to a chosen-background solution. -/
theorem identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((identityOfChosenBackground
        (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol =
      sol.1.identityDiffeomorph3GaugeOn
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2) := by
  unfold ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.gauge
  unfold toDiffeomorph3GaugeFlowFamily identityOfChosenBackground
  unfold IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
  unfold IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn
  unfold identityDiffeomorph3GaugeOn_of_isLeviCivita
  unfold AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
  congr

/-- For the chosen-background identity raw gauge-flow family, the gauge-corrected pullback metric
has the original intrinsic DeTurck metric velocity. -/
theorem identityOfChosenBackground_hpullDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let hbackground :=
    usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
  rw [identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (E := E) (H := H) (I := I) (M := M) ivp sol,
    sol.1.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity hbackground]
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    sol.1.toIntrinsicDeTurckSolution.metricVelocity
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution

@[simp] theorem toDiffeomorph3GaugeFlowFamily_forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (G.toDiffeomorph3GaugeFlowFamily.forInitialValueProblem ivp) =
      (G.forInitialValueProblem ivp).toDiffeomorph3GaugeFlow := rfl

end IntrinsicDeTurckGaugeFlowExistenceFamily

end RicciFlow

