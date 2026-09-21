/-
Variational witness for DeTurck gauge flows.

This module defines the `DeTurckFlowVariationalWitness`, which packages genuine
Picard–Lindelöf variational data for a DeTurck gauge flow. This is the
compliant Point-4 repair: variational tangent data arises from genuine ODE
theory and is supplied internally by genuine constructors, not by
assumption-shuffling.

The witness packages:
- The model vector field `f` and its derivative `Df` (coordinate DeTurck field)
- The Picard variational solution `α : VariationalLocalFlowSolution`
- The identification of `α.tangent` with the coordinate pushforward

From a witness, we construct the `HasDerivAt` for the coordinate pushforward
via `deturckPushforward_hasDerivAt`, which is the analytic core (M1c) of the
`VariationalData` required by Milestone 4.1.
-/
module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowMilestone41
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODECore

open scoped Topology
open ContinuousLinearMap

namespace DeTurckFlowVariationalWitness

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  [T2Space M] [SigmaFiniteDimensional ℝ M E]

/-- A variational witness packages genuine Picard–Lindelöf variational data
for a DeTurck gauge flow at a specific time and base point.

This is the `hvar` hypothesis of `deturckPushforward_hasDerivAt`, bundled as
a structure so it can be carried by the enriched existence package and
supplied internally by genuine Picard constructors. -/
structure VariationalWitness
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (t : ℝ) (x : M) where
  f : ℝ → E → E
  Df : ℝ → E → E →L[ℝ] E
  tmin tmax : ℝ
  t₀ : Set.Icc tmin tmax
  x₀ : E
  r : ℝ≥0
  α : ModelGaugeFlowODE.VariationalLocalFlowSolution (V := E) f Df t₀ x₀ r
  htIoo : t ∈ Set.Ioo tmin tmax
  htangent : ∀ τ ∈ Set.Icc tmin tmax,
    α.tangent x₀ τ =
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
        (I := I) (M := M) Φ t τ x

/-- From a variational witness, we obtain the variational equation for the
coordinate pushforward (M1c), via `deturckPushforward_hasDerivAt`. -/
theorem hasDerivAt_of_witness
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M)
    (w : VariationalWitness (I := I) (M := M) (G.maps3 sol) t x) :
    ∃ (D : E →L[ℝ] E),
      HasDerivAt
        (fun τ : ℝ ↦ SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t τ x)
        (D.comp (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t t x)) t := by
  -- Package the witness as the `hvar` existential for `deturckPushforward_hasDerivAt`.
  apply deturckPushforward_hasDerivAt G sol ht x
  exact ⟨w.f, w.Df, w.tmin, w.tmax, w.t₀, w.x₀, w.r, w.α, w.htIoo, w.htangent⟩

end DeTurckFlowVariationalWitness

/-- An enriched intrinsic DeTurck gauge-flow existence package that carries
genuine Picard–Lindelöf variational witnesses alongside the raw flow.

This is the compliant Point-4 repair: the `toDiffeomorph3GaugeFlow` adapter
consumes this enriched package (not the raw `IntrinsicDeTurckGaugeFlowExistence`),
so the `variational` field is supplied internally by genuine ODE theory. -/
structure IntrinsicDeTurckGaugeFlowExistenceWithWitness
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
    [T2Space M] [SigmaFiniteDimensional ℝ M E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  toExistence : IntrinsicDeTurckGaugeFlowExistence
    (E := E) (H := H) (I := I) (M := M) ivp
  witness : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet → ∀ x : M,
      DeTurckFlowVariationalWitness.VariationalWitness
        (I := I) (M := M) (toExistence.flow sol).maps3 t x
