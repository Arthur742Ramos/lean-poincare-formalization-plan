module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Model-space ODE core for gauge-flow existence

This module contains the pure Banach-model ODE structures needed for
DeTurck gauge-flow variational data. It does NOT import
`Diffeomorph3FlowExistence`, breaking the import cycle that blocks Point 4.

The structures here are the chart-level objects for Picard-Lindelöf
variational flow solutions. The constructors (Picard-Lindelöf existence
theorems) remain in `ModelGaugeFlowODE`, which imports this core.
-/

@[expose] public noncomputable section

open Metric Set
open scoped NNReal Topology ContDiff

namespace RicciFlow

namespace ModelGaugeFlowODE

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A local model-space flow for a time-dependent vector field on a Banach model.

The radius is measured in initial data, and the time interval is the closed
Picard-Lindelöf interval.  This is the chart-level object that must eventually
be glued and upgraded to the `C³` manifold diffeomorphism flow used by point 4.
-/
structure LocalFlowSolution
    (f : ℝ → V → V) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : V)
    (r : ℝ≥0) where
  flow : V → ℝ → V
  initial_eq : ∀ x ∈ closedBall x₀ r, flow x t₀ = x
  hasDerivWithinAt :
    ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (flow x) (f t (flow x t)) (Icc tmin tmax) t

/-- A Picard-Lindelöf local flow, with the spatial Lipschitz dependence on
initial data that mathlib provides. -/
structure LipschitzLocalFlowSolution
    (f : ℝ → V → V) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : V)
    (r : ℝ≥0) extends LocalFlowSolution f t₀ x₀ r where
  exists_lipschitz_time :
    ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax,
      LipschitzOnWith L' (fun x => flow x t) (closedBall x₀ r)

/-- A local model-space flow packaged as a continuous partial map on space-time.

This is the form needed for chart-gluing arguments: the solution is an ODE
curve in the time coordinate for each initial point, and the combined map is
continuous on the product of the initial-data ball and the Picard-Lindelöf time
interval.
-/
structure ContinuousLocalFlowSolution
    (f : ℝ → V → V) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : V)
    (r : ℝ≥0) where
  flow : V × ℝ → V
  initial_eq : ∀ x ∈ closedBall x₀ r, flow (x, t₀) = x
  hasDerivWithinAt :
    ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => flow (x, τ)) (f t (flow (x, t)))
        (Icc tmin tmax) t
  continuousOn : ContinuousOn flow (closedBall x₀ r ×ˢ Icc tmin tmax)

/-- A local model-space flow equipped with its linearized tangent equation.

For a chart vector field `f` and a spatial derivative candidate `Df`, this is the
Banach-model form of the tangent-map variational equation
`A'(t) = Df(t, flow(t)) ∘ A(t)`, initialized by the identity at the base time.
This is the model ODE ingredient needed to prove the `A`-derivative hypothesis
in the dynamic gauge-pullback scalar calculation. -/
structure VariationalLocalFlowSolution
    (f : ℝ → V → V) (Df : ℝ → V → V →L[ℝ] V)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : V)
    (r : ℝ≥0) extends ContinuousLocalFlowSolution f t₀ x₀ r where
  tangent : V → ℝ → V →L[ℝ] V
  tangent_initial_eq : ∀ x ∈ closedBall x₀ r, tangent x t₀ = 1
  tangent_hasDerivWithinAt :
    ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (tangent x)
        ((Df t (flow (x, t))).comp (tangent x t)) (Icc tmin tmax) t

/-- The product variational vector field combining the base flow and its
linearization. For `z = (x, A)`, this is `(f t x, Df t x ∘ A)`. -/
def variationalVectorField
    (f : ℝ → V → V) (Df : ℝ → V → V →L[ℝ] V) :
    ℝ → V × (V →L[ℝ] V) → V × (V →L[ℝ] V) :=
  fun t z => (f t z.1, (Df t z.1).comp z.2)

end ModelGaugeFlowODE

end RicciFlow
