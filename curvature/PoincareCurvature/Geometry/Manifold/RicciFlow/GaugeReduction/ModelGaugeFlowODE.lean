module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
public import Mathlib.Analysis.ODE.PicardLindelof

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Model-space ODE bridge for raw gauge-flow existence

This module isolates the Banach-model Picard-Lindelöf component needed for
positive-dimensional DeTurck gauge-flow existence.  It does not yet construct a
global `C³` manifold diffeomorphism flow, but it records the hard local
time-dependent ODE theorem in a point-4-friendly package that can be used after
passing to charts.
-/

@[expose] public noncomputable section

open Metric Set
open scoped NNReal Topology

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

namespace LocalFlowSolution

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V}
  {r : ℝ≥0}

/-- Evaluate the local flow at the center of the initial ball. -/
theorem center_initial_eq (α : LocalFlowSolution f t₀ x₀ r) :
    α.flow x₀ t₀ = x₀ :=
  α.initial_eq x₀ (mem_closedBall_self r.2)

/-- The center curve solves the model ODE on the Picard-Lindelöf interval. -/
theorem center_hasDerivWithinAt
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (α.flow x₀) (f t (α.flow x₀ t)) (Icc tmin tmax) t :=
  α.hasDerivWithinAt x₀ (mem_closedBall_self r.2) t ht

end LocalFlowSolution

namespace ContinuousLocalFlowSolution

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V}
  {r : ℝ≥0}

/-- Evaluate the continuous space-time local flow at the center of the initial ball. -/
theorem center_initial_eq (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    α.flow (x₀, t₀) = x₀ :=
  α.initial_eq x₀ (mem_closedBall_self r.2)

/-- The center curve of the continuous space-time flow solves the model ODE. -/
theorem center_hasDerivWithinAt
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (fun τ : ℝ => α.flow (x₀, τ))
      (f t (α.flow (x₀, t))) (Icc tmin tmax) t :=
  α.hasDerivWithinAt x₀ (mem_closedBall_self r.2) t ht

end ContinuousLocalFlowSolution

namespace IsPicardLindelof

variable [CompleteSpace V]
  {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
  {x₀ : V} {a r L K : ℝ≥0}

/-- Package mathlib's Picard-Lindelöf flow theorem as the model local-flow data
needed in the chart-level gauge-flow construction. -/
def toLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    LocalFlowSolution f t₀ x₀ r :=
  let h := hf.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  let α := Classical.choose h
  let hα := Classical.choose_spec h
  { flow := α
    initial_eq := fun x hx => (hα x hx).1
    hasDerivWithinAt := fun x hx t ht => (hα x hx).2 t ht }

/-- Picard-Lindelöf also supplies Lipschitz dependence on the initial point, a
key ingredient for upgrading the chartwise ODE solutions to a local flow. -/
def toLipschitzLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    LipschitzLocalFlowSolution f t₀ x₀ r :=
  let h := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  let α := Classical.choose h
  let hα := (Classical.choose_spec h).1
  let hLip := (Classical.choose_spec h).2
  { flow := α
    initial_eq := fun x hx => (hα x hx).1
    hasDerivWithinAt := fun x hx t ht => (hα x hx).2 t ht
    exists_lipschitz_time := hLip }

/-- Picard-Lindelöf also yields a continuous partial space-time flow on the
initial-data ball times the closed time interval. -/
def toContinuousLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousLocalFlowSolution f t₀ x₀ r :=
  let h := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  let α := Classical.choose h
  let hα := (Classical.choose_spec h).1
  let hcont := (Classical.choose_spec h).2
  { flow := α
    initial_eq := fun x hx => (hα x hx).1
    hasDerivWithinAt := fun x hx t ht => (hα x hx).2 t ht
    continuousOn := hcont }

end IsPicardLindelof

namespace ContDiffAt

variable [CompleteSpace V] {f : V → V} {x₀ : V}

/-- A `C¹` autonomous vector field has model-space local integral curves for all
initial data in a small ball.  This is the autonomous chart-level special case
of raw gauge-flow existence. -/
theorem exists_autonomous_local_integral_curves
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r,
      ∃ α : ℝ → V, α t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt t₀

/-- Centered version of
`exists_autonomous_local_integral_curves`, matching the single-trajectory ODE
statement used when only the gauge curve through one point is needed. -/
theorem exists_autonomous_center_integral_curve
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → V, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

end ContDiffAt

end ModelGaugeFlowODE

end RicciFlow
