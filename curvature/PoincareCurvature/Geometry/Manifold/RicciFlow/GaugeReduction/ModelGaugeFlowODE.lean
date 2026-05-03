module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Prod

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

/-- Interior points of the Picard cylinder see the closed Picard cylinder as an
ordinary neighborhood. -/
theorem closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo
    {tmin tmax : ℝ} {x₀ x : V} {r : ℝ≥0} {t : ℝ}
    (hx : x ∈ ball x₀ r) (ht : t ∈ Ioo tmin tmax) :
    closedBall x₀ r ×ˢ Icc tmin tmax ∈ 𝓝 (x, t) := by
  have hx' : closedBall x₀ r ∈ 𝓝 x :=
    mem_nhds_iff.mpr ⟨ball x₀ r, ball_subset_closedBall, isOpen_ball, hx⟩
  have ht' : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  exact prod_mem_nhds hx' ht'

/-- The product ODE whose first component is the base gauge-flow equation and
whose second component is the tangent-map variational equation. -/
def variationalVectorField
    (f : ℝ → V → V) (Df : ℝ → V → V →L[ℝ] V) :
    ℝ → V × (V →L[ℝ] V) → V × (V →L[ℝ] V) :=
  fun t z => (f t z.1, (Df t z.1).comp z.2)

/-- Project the base ODE from a solution of the product variational system. -/
theorem hasDerivWithinAt_fst_of_variationalVectorField
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {curve : ℝ → V × (V →L[ℝ] V)} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt curve (variationalVectorField f Df t (curve t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (curve τ).1) (f t (curve t).1) s t := by
  have hf := h.hasFDerivWithinAt.fst
  simpa [variationalVectorField] using hf.hasDerivWithinAt

/-- Project the tangent-map variational ODE from a solution of the product
variational system. -/
theorem hasDerivWithinAt_snd_of_variationalVectorField
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {curve : ℝ → V × (V →L[ℝ] V)} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt curve (variationalVectorField f Df t (curve t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (curve τ).2)
      ((Df t (curve t).1).comp (curve t).2) s t := by
  have hf := h.hasFDerivWithinAt.snd
  simpa [variationalVectorField] using hf.hasDerivWithinAt

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

/-- On the interior of the Picard interval, the center curve has an ordinary
time derivative. -/
theorem center_hasDerivAt_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (α.flow x₀) (f t (α.flow x₀ t)) t :=
  (α.center_hasDerivWithinAt (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Every initial point in the local ball has the ordinary model-flow derivative
on the interior of the Picard interval. -/
theorem flow_hasDerivAt_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (α.flow x) (f t (α.flow x t)) t :=
  (α.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Every initial point in the local ball has within-interval continuity on the
Picard interval. -/
theorem flow_continuousWithinAt
    (α : LocalFlowSolution f t₀ x₀ r) {x : V} (hx : x ∈ closedBall x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (α.flow x) (Icc tmin tmax) t :=
  (α.hasDerivWithinAt x hx t ht).continuousWithinAt

/-- Center-curve within-interval continuity on the Picard interval. -/
theorem center_continuousWithinAt
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (α.flow x₀) (Icc tmin tmax) t :=
  α.flow_continuousWithinAt (mem_closedBall_self r.2) ht

/-- A local model-flow curve is eventually, relative to the closed Picard
interval, in any open set containing its endpoint value. -/
theorem flow_eventuallyWithin_mem_of_mem_Icc
    (α : LocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x t ∈ U) :
    (α.flow x) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  (α.flow_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center-curve specialization of `flow_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_eventuallyWithin_mem_of_mem_Icc
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x₀ t ∈ U) :
    (α.flow x₀) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  α.flow_eventuallyWithin_mem_of_mem_Icc (mem_closedBall_self r.2) ht hU hmem

/-- Every initial point in the local ball has ordinary continuity on the
interior of the Picard interval. -/
theorem flow_continuousAt_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (α.flow x) t :=
  (α.flow_hasDerivAt_of_mem_Ioo hx ht).continuousAt

/-- Center-curve ordinary continuity on the interior of the Picard interval. -/
theorem center_continuousAt_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (α.flow x₀) t :=
  α.flow_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- A local model-flow curve is eventually in any open set containing its
interior-time value.  This is the model-side source-neighborhood readout used
when a Picard curve is known to lie in a selected chart domain. -/
theorem flow_eventually_mem_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x t ∈ U) :
    (α.flow x) ⁻¹' U ∈ 𝓝 t :=
  (α.flow_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center-curve specialization of `flow_eventually_mem_of_mem_Ioo`. -/
theorem center_eventually_mem_of_mem_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x₀ t ∈ U) :
    (α.flow x₀) ⁻¹' U ∈ 𝓝 t :=
  α.flow_eventually_mem_of_mem_Ioo (mem_closedBall_self r.2) ht hU hmem

/-- Every packaged local model-flow curve is continuous on the Picard interval. -/
theorem flow_continuousOn
    (α : LocalFlowSolution f t₀ x₀ r) {x : V} (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (α.flow x) (Icc tmin tmax) :=
  HasDerivWithinAt.continuousOn (fun t ht => α.hasDerivWithinAt x hx t ht)

/-- Center-curve continuity on the Picard interval. -/
theorem center_continuousOn (α : LocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (α.flow x₀) (Icc tmin tmax) :=
  α.flow_continuousOn (mem_closedBall_self r.2)

/-- Every packaged local model-flow curve is continuous on the open Picard
interior. -/
theorem flow_continuousOn_Ioo
    (α : LocalFlowSolution f t₀ x₀ r) {x : V} (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (α.flow x) (Ioo tmin tmax) :=
  (α.flow_continuousOn hx).mono (fun _t ht => Ioo_subset_Icc_self ht)

/-- Center-curve continuity on the open Picard interior. -/
theorem center_continuousOn_Ioo (α : LocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (α.flow x₀) (Ioo tmin tmax) :=
  α.flow_continuousOn_Ioo (mem_closedBall_self r.2)

/-- Restrict a packaged local flow to a smaller initial ball and a smaller
closed time interval containing the same base time. -/
def restrict
    (α : LocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    LocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' where
  flow := α.flow
  initial_eq := by
    intro x hx
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    simpa using α.initial_eq x hx'
  hasDerivWithinAt := by
    intro x hx t ht
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    exact (α.hasDerivWithinAt x hx' t (htime ht)).mono htime

@[simp] theorem restrict_flow
    (α : LocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).flow = α.flow := rfl

/-- Restrict a nonempty packaged local-flow existence witness to a smaller
initial ball and closed time interval. -/
theorem nonempty_restrict
    (hα : Nonempty (LocalFlowSolution f t₀ x₀ r)) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (LocalFlowSolution f
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  rcases hα with ⟨α⟩
  exact ⟨α.restrict htime ht₀' hr⟩

/-- Two packaged local model flows agree on the interior time interval whenever
their curves start from the same initial point and stay in a region where the
vector field is uniformly Lipschitz.  The two packages may have different
initial-data centers and radii; this is the overlap form needed for chart
gluing. -/
theorem eqOn_Ioo_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : LocalFlowSolution f t₀ xα rα) (β : LocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Ioo tmin tmax) := by
  refine ODE_solution_unique_of_mem_Ioo (v := f) (s := state) hf_lip ht₀ ?_ ?_ ?_
  · intro t ht
    exact
      ⟨(α.hasDerivWithinAt x hxα t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),
        hα_mem t ht⟩
  · intro t ht
    exact
      ⟨(β.hasDerivWithinAt x hxβ t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),
        hβ_mem t ht⟩
  · rw [α.initial_eq x hxα, β.initial_eq x hxβ]

/-- Pointwise interior overlap uniqueness for packaged local model flows. -/
theorem flow_eq_of_lipschitzOnWith_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : LocalFlowSolution f t₀ xα rα) (β : LocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.flow x t = β.flow x t :=
  α.eqOn_Ioo_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hf_lip hα_mem hβ_mem ht

/-- Two packaged local model flows agree on the interior time interval whenever
their curves stay in a region where the vector field is uniformly Lipschitz. -/
theorem eqOn_Ioo_of_lipschitzOnWith
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Ioo tmin tmax) :=
  α.eqOn_Ioo_of_lipschitzOnWith_of_mem β hx hx ht₀ hf_lip hα_mem hβ_mem

/-- Closed-interval uniqueness form for packaged local model flows on overlap.
This is the version needed when endpoint continuity is available from the
within-interval ODE statements. -/
theorem eqOn_Icc_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : LocalFlowSolution f t₀ xα rα) (β : LocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Icc tmin tmax) := by
  refine ODE_solution_unique_of_mem_Icc (v := f) (s := state) hf_lip ht₀ ?_ ?_ hα_mem ?_ ?_
    hβ_mem ?_
  · exact HasDerivWithinAt.continuousOn (fun t ht => α.hasDerivWithinAt x hxα t ht)
  · intro t ht
    exact (α.hasDerivWithinAt x hxα t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact HasDerivWithinAt.continuousOn (fun t ht => β.hasDerivWithinAt x hxβ t ht)
  · intro t ht
    exact (β.hasDerivWithinAt x hxβ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · rw [α.initial_eq x hxα, β.initial_eq x hxβ]

/-- Pointwise closed-interval overlap uniqueness for packaged local model flows. -/
theorem flow_eq_of_lipschitzOnWith_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : LocalFlowSolution f t₀ xα rα) (β : LocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.flow x t = β.flow x t :=
  α.eqOn_Icc_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hf_lip hα_mem hβ_mem ht

/-- Common-subinterval overlap uniqueness for packaged local model flows whose
ambient Picard intervals may differ.  This is the chart-gluing form obtained by
restricting both packages to a shared closed interval containing the same base
time. -/
theorem eqOn_common_Icc_of_lipschitzOnWith_of_mem
    {aα bα aβ bβ a b tbase : ℝ}
    {htbaseα : tbase ∈ Icc aα bα} {htbaseβ : tbase ∈ Icc aβ bβ}
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : LocalFlowSolution f (⟨tbase, htbaseα⟩ : Icc aα bα) xα rα)
    (β : LocalFlowSolution f (⟨tbase, htbaseβ⟩ : Icc aβ bβ) xβ rβ)
    (hαtime : Icc a b ⊆ Icc aα bα)
    (hβtime : Icc a b ⊆ Icc aβ bβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (htbase : tbase ∈ Ioo a b)
    (hf_lip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo a b, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo a b, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Icc a b) := by
  let t₀' : Icc a b := ⟨tbase, Ioo_subset_Icc_self htbase⟩
  let α' : LocalFlowSolution f t₀' xα rα :=
    α.restrict hαtime (Ioo_subset_Icc_self htbase) le_rfl
  let β' : LocalFlowSolution f t₀' xβ rβ :=
    β.restrict hβtime (Ioo_subset_Icc_self htbase) le_rfl
  have htbase' : (t₀' : ℝ) ∈ Ioo a b := by
    simpa [t₀'] using htbase
  have hα_mem' : ∀ t ∈ Ioo a b, α'.flow x t ∈ state t := by
    intro t ht
    simpa [α'] using hα_mem t ht
  have hβ_mem' : ∀ t ∈ Ioo a b, β'.flow x t ∈ state t := by
    intro t ht
    simpa [β'] using hβ_mem t ht
  have hcommon : EqOn (α'.flow x) (β'.flow x) (Icc a b) :=
    α'.eqOn_Icc_of_lipschitzOnWith_of_mem β' hxα hxβ htbase'
      hf_lip hα_mem' hβ_mem'
  simpa [α', β'] using hcommon

/-- Closed-interval uniqueness form for packaged local model flows.  This is the
version needed when endpoint continuity is available from the within-interval
ODE statements. -/
theorem eqOn_Icc_of_lipschitzOnWith
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Icc tmin tmax) :=
  α.eqOn_Icc_of_lipschitzOnWith_of_mem β hx hx ht₀ hf_lip hα_mem hβ_mem

/-- Center-trajectory interior uniqueness for packaged local model flows. -/
theorem center_eqOn_Ioo_of_lipschitzOnWith
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x₀ t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x₀ t ∈ state t) :
    EqOn (α.flow x₀) (β.flow x₀) (Ioo tmin tmax) :=
  α.eqOn_Ioo_of_lipschitzOnWith β (mem_closedBall_self r.2)
    ht₀ hf_lip hα_mem hβ_mem

/-- Pointwise center-trajectory interior uniqueness for packaged local model flows. -/
theorem center_flow_eq_of_lipschitzOnWith_Ioo
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x₀ t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x₀ t ∈ state t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.flow x₀ t = β.flow x₀ t :=
  α.center_eqOn_Ioo_of_lipschitzOnWith β ht₀ hf_lip hα_mem hβ_mem ht

/-- Center-trajectory closed-interval uniqueness for packaged local model flows. -/
theorem center_eqOn_Icc_of_lipschitzOnWith
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x₀ t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x₀ t ∈ state t) :
    EqOn (α.flow x₀) (β.flow x₀) (Icc tmin tmax) :=
  α.eqOn_Icc_of_lipschitzOnWith β (mem_closedBall_self r.2)
    ht₀ hf_lip hα_mem hβ_mem

/-- Pointwise center-trajectory closed-interval uniqueness for packaged local
model flows. -/
theorem center_flow_eq_of_lipschitzOnWith_Icc
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x₀ t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x₀ t ∈ state t)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.flow x₀ t = β.flow x₀ t :=
  α.center_eqOn_Icc_of_lipschitzOnWith β ht₀ hf_lip hα_mem hβ_mem ht

end LocalFlowSolution

namespace LipschitzLocalFlowSolution

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V}
  {r : ℝ≥0}

/-- Restrict a Lipschitz local flow to a smaller initial ball and a smaller
closed time interval. -/
def restrict
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    LipschitzLocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' where
  toLocalFlowSolution := α.toLocalFlowSolution.restrict htime ht₀' hr
  exists_lipschitz_time := by
    obtain ⟨L', hL'⟩ := α.exists_lipschitz_time
    refine ⟨L', ?_⟩
    intro t ht
    refine (hL' t (htime ht)).mono ?_
    intro x hx
    rw [mem_closedBall] at hx ⊢
    exact le_trans hx (by exact_mod_cast hr)

@[simp] theorem restrict_flow
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).flow = α.flow := rfl

/-- A packaged Lipschitz local flow gives a Lipschitz time-slice map on the
initial-data ball at every Picard time. -/
theorem exists_lipschitzOnWith_time
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ∃ L' : ℝ≥0, LipschitzOnWith L' (fun x => α.flow x t) (closedBall x₀ r) := by
  obtain ⟨L', hL'⟩ := α.exists_lipschitz_time
  exact ⟨L', hL' t ht⟩

/-- Interior-time specialization of `exists_lipschitzOnWith_time`. -/
theorem exists_lipschitzOnWith_time_of_mem_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ∃ L' : ℝ≥0, LipschitzOnWith L' (fun x => α.flow x t) (closedBall x₀ r) :=
  α.exists_lipschitzOnWith_time (Ioo_subset_Icc_self ht)

/-- A packaged Lipschitz local flow has continuous time-slice maps on the
initial-data ball. -/
theorem flow_continuousOn_initialBall
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousOn (fun x => α.flow x t) (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ := α.exists_lipschitzOnWith_time ht
  exact hL'.continuousOn

/-- Interior-time specialization of time-slice continuity on the initial-data
ball. -/
theorem flow_continuousOn_initialBall_of_mem_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousOn (fun x => α.flow x t) (closedBall x₀ r) :=
  α.flow_continuousOn_initialBall (Ioo_subset_Icc_self ht)

/-- A packaged Lipschitz local flow gives a concrete distance estimate between
two initial points at every Picard time. -/
theorem exists_dist_flow_le_mul
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0, dist (α.flow x t) (α.flow y t) ≤ L' * dist x y := by
  obtain ⟨L', hL'⟩ := α.exists_lipschitzOnWith_time ht
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Interior-time specialization of the packaged local-flow distance estimate. -/
theorem exists_dist_flow_le_mul_of_mem_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0, dist (α.flow x t) (α.flow y t) ≤ L' * dist x y :=
  α.exists_dist_flow_le_mul (Ioo_subset_Icc_self ht) hx hy

/-- Uniform initial-data Lipschitz dependence plus the ODE time-continuity of
each trajectory gives joint space-time continuity on the local Picard cylinder. -/
theorem flow_continuousOn_spaceTime
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (fun p : V × ℝ => α.flow p.1 p.2) (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  rcases hp with ⟨hpx, hpt⟩
  obtain ⟨L, hL⟩ := α.exists_lipschitz_time
  have htime_cont := α.toLocalFlowSolution.flow_continuousWithinAt hpx hpt
  rw [Metric.continuousWithinAt_iff] at htime_cont
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δt, hδt_pos, hδt⟩ := htime_cont (ε / 2) hε2
  let δx : ℝ := (ε / 2) / ((L : ℝ) + 1)
  have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
  have hden_pos : 0 < (L : ℝ) + 1 := by linarith
  have hδx_pos : 0 < δx := by
    dsimp [δx]
    positivity
  refine ⟨min δt δx, lt_min hδt_pos hδx_pos, ?_⟩
  intro q hq hpq
  rcases hq with ⟨hqx, hqt⟩
  rw [Prod.dist_eq] at hpq
  have hqtime_lt : dist q.2 p.2 < δt :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hpq (min_le_left _ _))
  have hqx_lt : dist q.1 p.1 < δx :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hpq (min_le_right _ _))
  have hspace_le :
      dist (α.flow q.1 q.2) (α.flow p.1 q.2) ≤ (L : ℝ) * dist q.1 p.1 :=
    (hL q.2 hqt).dist_le_mul q.1 hqx p.1 hpx
  have hdist_nonneg : 0 ≤ dist q.1 p.1 := dist_nonneg
  have hmul_le : (L : ℝ) * dist q.1 p.1 ≤ (L : ℝ) * δx := by
    nlinarith
  have hmul_bound : (L : ℝ) * δx ≤ ε / 2 := by
    dsimp [δx]
    have hfrac : (L : ℝ) / ((L : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hden_pos]
      linarith
    have heps_nonneg : 0 ≤ ε / 2 := by linarith
    calc
      (L : ℝ) * ((ε / 2) / ((L : ℝ) + 1)) =
          ((L : ℝ) / ((L : ℝ) + 1)) * (ε / 2) := by ring
      _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right hfrac heps_nonneg
      _ = ε / 2 := by ring
  have hspace_bound : dist (α.flow q.1 q.2) (α.flow p.1 q.2) ≤ ε / 2 := by
    exact le_trans hspace_le (le_trans hmul_le hmul_bound)
  have htime_lt : dist (α.flow p.1 q.2) (α.flow p.1 p.2) < ε / 2 :=
    hδt hqt hqtime_lt
  have htri := dist_triangle (α.flow q.1 q.2) (α.flow p.1 q.2) (α.flow p.1 p.2)
  linarith

/-- Pointwise within-space-time continuity of a Lipschitz local-flow package. -/
theorem flow_continuousWithinAt_spaceTime
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {p : V × ℝ}
    (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt (fun q : V × ℝ => α.flow q.1 q.2)
      (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  α.flow_continuousOn_spaceTime.continuousWithinAt hp

/-- Coordinate form of space-time continuity for a Lipschitz local-flow package. -/
theorem flow_continuousWithinAt_spaceTime_at
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun q : V × ℝ => α.flow q.1 q.2)
      (closedBall x₀ r ×ˢ Icc tmin tmax) (x, t) :=
  α.flow_continuousWithinAt_spaceTime ⟨hx, ht⟩

/-- A Lipschitz local-flow package is eventually in any open target set around a
space-time endpoint, relative to the Picard cylinder. -/
theorem flow_eventuallyWithin_mem_of_mem_spaceTime
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {p : V × ℝ}
    (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow p.1 p.2 ∈ U) :
    (fun q : V × ℝ => α.flow q.1 q.2) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (α.flow_continuousWithinAt_spaceTime hp) (hU.mem_nhds hmem)

/-- Coordinate form of the space-time eventual-membership readout for a
Lipschitz local-flow package. -/
theorem flow_eventuallyWithin_mem_of_mem_spaceTime_at
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x t ∈ U) :
    (fun q : V × ℝ => α.flow q.1 q.2) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] (x, t) :=
  α.flow_eventuallyWithin_mem_of_mem_spaceTime ⟨hx, ht⟩ hU hmem

/-- A Lipschitz local-flow package is ordinarily continuous at interior points
of the Picard cylinder. -/
theorem flow_continuousAt_spaceTime_of_mem_ball_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun q : V × ℝ => α.flow q.1 q.2) (x, t) :=
  (α.flow_continuousWithinAt_spaceTime_at (ball_subset_closedBall hx)
    (Ioo_subset_Icc_self ht)).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- A Lipschitz local-flow package is continuous on the open Picard cylinder. -/
theorem flow_continuousOn_spaceTime_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (fun q : V × ℝ => α.flow q.1 q.2)
      (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (α.flow_continuousAt_spaceTime_of_mem_ball_Ioo hp.1 hp.2).continuousWithinAt

/-- Interior space-time eventual-membership readout for a Lipschitz local-flow
package. -/
theorem flow_eventually_mem_of_mem_spaceTime_Ioo
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow x t ∈ U) :
    (fun q : V × ℝ => α.flow q.1 q.2) ⁻¹' U ∈ 𝓝 (x, t) :=
  (α.flow_continuousAt_spaceTime_of_mem_ball_Ioo hx ht) (hU.mem_nhds hmem)

/-- A Lipschitz local-flow package is automatically a continuous space-time
local-flow package. -/
def toContinuousLocalFlowSolution
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) :
    ContinuousLocalFlowSolution f t₀ x₀ r where
  flow p := α.flow p.1 p.2
  initial_eq := α.initial_eq
  hasDerivWithinAt := by
    intro x hx t ht
    exact α.hasDerivWithinAt x hx t ht
  continuousOn := α.flow_continuousOn_spaceTime

@[simp] theorem toContinuousLocalFlowSolution_flow
    (α : LipschitzLocalFlowSolution f t₀ x₀ r) :
    α.toContinuousLocalFlowSolution.flow = fun p : V × ℝ => α.flow p.1 p.2 := rfl

/-- A proof-level Lipschitz local-flow witness automatically gives a continuous
space-time local-flow witness. -/
theorem nonempty_toContinuousLocalFlowSolution
    (hα : Nonempty (LipschitzLocalFlowSolution f t₀ x₀ r)) :
    Nonempty (ContinuousLocalFlowSolution f t₀ x₀ r) := by
  rcases hα with ⟨α⟩
  exact ⟨α.toContinuousLocalFlowSolution⟩

/-- Restrict a nonempty Lipschitz local-flow existence witness to a smaller
initial ball and closed time interval. -/
theorem nonempty_restrict
    (hα : Nonempty (LipschitzLocalFlowSolution f t₀ x₀ r)) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (LipschitzLocalFlowSolution f
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  rcases hα with ⟨α⟩
  exact ⟨α.restrict htime ht₀' hr⟩

end LipschitzLocalFlowSolution

namespace LocalFlowSolution

variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
  {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
  {z₀ : V × (V →L[ℝ] V)} {r : ℝ≥0}

/-- A packaged local solution of the product variational system yields the base
ODE for its first component. -/
theorem variational_base_hasDerivWithinAt
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (fun τ : ℝ => (α.flow z τ).1)
      (f t (α.flow z t).1) (Icc tmin tmax) t :=
  hasDerivWithinAt_fst_of_variationalVectorField
    (α.hasDerivWithinAt z hz t ht)

/-- A packaged local solution of the product variational system yields the
tangent-map ODE for its second component. -/
theorem variational_tangent_hasDerivWithinAt
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (fun τ : ℝ => (α.flow z τ).2)
      ((Df t (α.flow z t).1).comp (α.flow z t).2) (Icc tmin tmax) t :=
  hasDerivWithinAt_snd_of_variationalVectorField
    (α.hasDerivWithinAt z hz t ht)

/-- Applying the product variational tangent equation to a fixed model vector
gives the vector-slot derivative before repackaging as a
`VariationalLocalFlowSolution`. -/
theorem variational_tangent_apply_hasDerivWithinAt
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    HasDerivWithinAt (fun τ : ℝ => (α.flow z τ).2 v)
      (((Df t (α.flow z t).1).comp (α.flow z t).2) v) (Icc tmin tmax) t := by
  have htan := α.variational_tangent_hasDerivWithinAt hz ht
  have hev :
      HasFDerivWithinAt
        (fun A : V →L[ℝ] V => A v) (ContinuousLinearMap.apply ℝ V v)
        Set.univ (α.flow z t).2 :=
    (ContinuousLinearMap.apply ℝ V v).hasFDerivWithinAt
  have hcomp := hev.comp t htan.hasFDerivWithinAt
    (Set.mapsTo_univ (fun τ : ℝ => (α.flow z τ).2) (Icc tmin tmax))
  simpa [Function.comp] using hcomp.hasDerivWithinAt

/-- The base component of a product variational local-flow solution is
continuous on the Picard interval. -/
theorem variational_base_continuousOn
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r) :
    ContinuousOn (fun τ : ℝ => (α.flow z τ).1) (Icc tmin tmax) :=
  HasDerivWithinAt.continuousOn (fun t ht => α.variational_base_hasDerivWithinAt hz ht)

/-- The tangent-map component of a product variational local-flow solution is
continuous on the Picard interval. -/
theorem variational_tangent_continuousOn
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r) :
    ContinuousOn (fun τ : ℝ => (α.flow z τ).2) (Icc tmin tmax) :=
  HasDerivWithinAt.continuousOn (fun t ht => α.variational_tangent_hasDerivWithinAt hz ht)

/-- Interior ordinary base-curve ODE extracted from a packaged solution of the
product variational system. -/
theorem variational_base_hasDerivAt_of_mem_Ioo
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => (α.flow z τ).1)
      (f t (α.flow z t).1) t :=
  (α.variational_base_hasDerivWithinAt hz (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Interior ordinary tangent-map ODE extracted from a packaged solution of the
product variational system. -/
theorem variational_tangent_hasDerivAt_of_mem_Ioo
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => (α.flow z τ).2)
      ((Df t (α.flow z t).1).comp (α.flow z t).2) t :=
  (α.variational_tangent_hasDerivWithinAt hz (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Interior vector-slot derivative extracted from a packaged solution of the
product variational system before repackaging as a `VariationalLocalFlowSolution`. -/
theorem variational_tangent_apply_hasDerivAt_of_mem_Ioo
    (α : LocalFlowSolution (variationalVectorField f Df) t₀ z₀ r)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V) :
    HasDerivAt (fun τ : ℝ => (α.flow z τ).2 v)
      (((Df t (α.flow z t).1).comp (α.flow z t).2) v) t :=
  (α.variational_tangent_apply_hasDerivWithinAt hz (Ioo_subset_Icc_self ht) v).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end LocalFlowSolution

namespace ContinuousLocalFlowSolution

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V}
  {r : ℝ≥0}

/-- Forget the space-time continuity field and view a continuous partial flow as
a family of local ODE solutions. -/
def toLocalFlowSolution (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    LocalFlowSolution f t₀ x₀ r where
  flow x t := α.flow (x, t)
  initial_eq := α.initial_eq
  hasDerivWithinAt := α.hasDerivWithinAt

/-- Evaluate the continuous space-time local flow at the center of the initial ball. -/
theorem center_initial_eq (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    α.flow (x₀, t₀) = x₀ :=
  α.initial_eq x₀ (mem_closedBall_self r.2)

/-- Pointwise within-space-time continuity of the continuous local-flow package. -/
theorem flow_continuousWithinAt_spaceTime
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {p : V × ℝ}
    (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt α.flow (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  α.continuousOn.continuousWithinAt hp

/-- Coordinate form of space-time continuity for the continuous local-flow package. -/
theorem flow_continuousWithinAt_spaceTime_at
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt α.flow (closedBall x₀ r ×ˢ Icc tmin tmax) (x, t) :=
  α.flow_continuousWithinAt_spaceTime ⟨hx, ht⟩

/-- Center-trajectory specialization of space-time continuity. -/
theorem center_continuousWithinAt_spaceTime
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt α.flow (closedBall x₀ r ×ˢ Icc tmin tmax) (x₀, t) :=
  α.flow_continuousWithinAt_spaceTime_at (mem_closedBall_self r.2) ht

/-- A continuous local-flow package is eventually in any open target set around a
space-time endpoint, relative to the Picard cylinder. -/
theorem flow_eventuallyWithin_mem_of_mem_spaceTime
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {p : V × ℝ}
    (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow p ∈ U) :
    α.flow ⁻¹' U ∈ 𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (α.flow_continuousWithinAt_spaceTime hp) (hU.mem_nhds hmem)

/-- Coordinate form of the space-time eventual-membership readout. -/
theorem flow_eventuallyWithin_mem_of_mem_spaceTime_at
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    α.flow ⁻¹' U ∈ 𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] (x, t) :=
  α.flow_eventuallyWithin_mem_of_mem_spaceTime ⟨hx, ht⟩ hU hmem

/-- Center-trajectory specialization of the space-time eventual-membership readout. -/
theorem center_eventuallyWithin_mem_of_mem_spaceTime
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x₀, t) ∈ U) :
    α.flow ⁻¹' U ∈ 𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] (x₀, t) :=
  α.flow_eventuallyWithin_mem_of_mem_spaceTime_at
    (mem_closedBall_self r.2) ht hU hmem

/-- A continuous local-flow package is ordinarily continuous at interior points
of the Picard cylinder. -/
theorem flow_continuousAt_spaceTime_of_mem_ball_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt α.flow (x, t) :=
  (α.flow_continuousWithinAt_spaceTime_at (ball_subset_closedBall hx)
    (Ioo_subset_Icc_self ht)).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- A continuous local-flow package is continuous on the open Picard cylinder. -/
theorem flow_continuousOn_spaceTime_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    ContinuousOn α.flow (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (α.flow_continuousAt_spaceTime_of_mem_ball_Ioo hp.1 hp.2).continuousWithinAt

/-- Interior space-time eventual-membership readout for a continuous local-flow
package. -/
theorem flow_eventually_mem_of_mem_spaceTime_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    α.flow ⁻¹' U ∈ 𝓝 (x, t) :=
  (α.flow_continuousAt_spaceTime_of_mem_ball_Ioo hx ht) (hU.mem_nhds hmem)

/-- The center curve of the continuous space-time flow solves the model ODE. -/
theorem center_hasDerivWithinAt
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (fun τ : ℝ => α.flow (x₀, τ))
      (f t (α.flow (x₀, t))) (Icc tmin tmax) t :=
  α.hasDerivWithinAt x₀ (mem_closedBall_self r.2) t ht

/-- On the interior of the Picard interval, the center curve has an ordinary
time derivative. -/
theorem center_hasDerivAt_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => α.flow (x₀, τ))
      (f t (α.flow (x₀, t))) t :=
  (α.center_hasDerivWithinAt (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Every initial point in the local ball has the ordinary model-flow derivative
on the interior of the Picard interval. -/
theorem flow_hasDerivAt_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => α.flow (x, τ))
      (f t (α.flow (x, t))) t :=
  (α.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Each time slice of a continuous space-time local flow is continuous within
the Picard interval. -/
theorem flow_continuousWithinAt
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => α.flow (x, τ)) (Icc tmin tmax) t :=
  α.toLocalFlowSolution.flow_continuousWithinAt hx ht

/-- The center time slice of a continuous space-time local flow is continuous
within the Picard interval. -/
theorem center_continuousWithinAt
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => α.flow (x₀, τ)) (Icc tmin tmax) t :=
  α.flow_continuousWithinAt (mem_closedBall_self r.2) ht

/-- A continuous local model-flow time slice is eventually, relative to the
closed Picard interval, in any open set containing its endpoint value. -/
theorem flow_eventuallyWithin_mem_of_mem_Icc
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    (fun τ : ℝ => α.flow (x, τ)) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  (α.flow_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center-time-slice specialization of
`ContinuousLocalFlowSolution.flow_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_eventuallyWithin_mem_of_mem_Icc
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x₀, t) ∈ U) :
    (fun τ : ℝ => α.flow (x₀, τ)) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  α.flow_eventuallyWithin_mem_of_mem_Icc (mem_closedBall_self r.2) ht hU hmem

/-- Each time slice of a continuous space-time local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem flow_continuousAt_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => α.flow (x, τ)) t :=
  α.toLocalFlowSolution.flow_continuousAt_of_mem_Ioo hx ht

/-- The center time slice of a continuous space-time local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem center_continuousAt_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => α.flow (x₀, τ)) t :=
  α.flow_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- A continuous local model-flow time slice is eventually in any open set
containing its interior-time value. -/
theorem flow_eventually_mem_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    (fun τ : ℝ => α.flow (x, τ)) ⁻¹' U ∈ 𝓝 t :=
  (α.flow_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center-time-slice specialization of
`ContinuousLocalFlowSolution.flow_eventually_mem_of_mem_Ioo`. -/
theorem center_eventually_mem_of_mem_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x₀, t) ∈ U) :
    (fun τ : ℝ => α.flow (x₀, τ)) ⁻¹' U ∈ 𝓝 t :=
  α.flow_eventually_mem_of_mem_Ioo (mem_closedBall_self r.2) ht hU hmem

/-- Each time slice of a continuous space-time local flow is continuous on the
Picard interval. -/
theorem flow_continuousOn
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x, t)) (Icc tmin tmax) :=
  α.toLocalFlowSolution.flow_continuousOn hx

/-- The center time slice of a continuous space-time local flow is continuous
on the Picard interval. -/
theorem center_continuousOn (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x₀, t)) (Icc tmin tmax) :=
  α.flow_continuousOn (mem_closedBall_self r.2)

/-- Each time slice of a continuous space-time local flow is continuous on the
open Picard interior. -/
theorem flow_continuousOn_Ioo
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x, t)) (Ioo tmin tmax) :=
  (α.flow_continuousOn hx).mono (fun _t ht => Ioo_subset_Icc_self ht)

/-- The center time slice of a continuous space-time local flow is continuous on
the open Picard interior. -/
theorem center_continuousOn_Ioo (α : ContinuousLocalFlowSolution f t₀ x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x₀, t)) (Ioo tmin tmax) :=
  α.flow_continuousOn_Ioo (mem_closedBall_self r.2)

/-- Restrict a continuous space-time local flow to a smaller initial ball and a
smaller closed time interval. -/
def restrict
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    ContinuousLocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' where
  flow := α.flow
  initial_eq := by
    intro x hx
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    simpa using α.initial_eq x hx'
  hasDerivWithinAt := by
    intro x hx t ht
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    exact (α.hasDerivWithinAt x hx' t (htime ht)).mono htime
  continuousOn := by
    refine α.continuousOn.mono (Set.prod_mono ?_ htime)
    intro x hx
    rw [mem_closedBall] at hx ⊢
    exact le_trans hx (by exact_mod_cast hr)

@[simp] theorem restrict_flow
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).flow = α.flow := rfl

@[simp] theorem restrict_toLocalFlowSolution
    (α : ContinuousLocalFlowSolution f t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).toLocalFlowSolution =
      α.toLocalFlowSolution.restrict htime ht₀' hr := rfl

/-- Restrict a nonempty continuous local-flow existence witness to a smaller
initial ball and closed time interval. -/
theorem nonempty_restrict
    (hα : Nonempty (ContinuousLocalFlowSolution f t₀ x₀ r)) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (ContinuousLocalFlowSolution f
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  rcases hα with ⟨α⟩
  exact ⟨α.restrict htime ht₀' hr⟩

/-- Continuous space-time local flows inherit the open-interval overlap
uniqueness bridge from `LocalFlowSolution`. -/
theorem eqOn_Ioo_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : ContinuousLocalFlowSolution f t₀ xα rα)
    (β : ContinuousLocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t) :
    EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax) :=
  LocalFlowSolution.eqOn_Ioo_of_lipschitzOnWith_of_mem
    (α := α.toLocalFlowSolution) (β := β.toLocalFlowSolution)
    (x := x) hxα hxβ ht₀ hf_lip hα_mem hβ_mem

/-- Pointwise interior overlap uniqueness for continuous space-time local flows. -/
theorem flow_eq_of_lipschitzOnWith_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : ContinuousLocalFlowSolution f t₀ xα rα)
    (β : ContinuousLocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.flow (x, t) = β.flow (x, t) :=
  α.eqOn_Ioo_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hf_lip hα_mem hβ_mem ht

/-- Continuous space-time local flows inherit the open-interval uniqueness bridge
from `LocalFlowSolution`. -/
theorem eqOn_Ioo_of_lipschitzOnWith
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t) :
    EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax) :=
  α.eqOn_Ioo_of_lipschitzOnWith_of_mem β hx hx ht₀ hf_lip hα_mem hβ_mem

/-- Continuous space-time local flows inherit the closed-interval overlap
uniqueness bridge from `LocalFlowSolution`. -/
theorem eqOn_Icc_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : ContinuousLocalFlowSolution f t₀ xα rα)
    (β : ContinuousLocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t) :
    EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Icc tmin tmax) :=
  LocalFlowSolution.eqOn_Icc_of_lipschitzOnWith_of_mem
    (α := α.toLocalFlowSolution) (β := β.toLocalFlowSolution)
    (x := x) hxα hxβ ht₀ hf_lip hα_mem hβ_mem

/-- Common-subinterval overlap uniqueness for continuous space-time local flows
whose ambient Picard intervals may differ.  This is the continuous-flow version
of `LocalFlowSolution.eqOn_common_Icc_of_lipschitzOnWith_of_mem`. -/
theorem eqOn_common_Icc_of_lipschitzOnWith_of_mem
    {aα bα aβ bβ a b tbase : ℝ}
    {htbaseα : tbase ∈ Icc aα bα} {htbaseβ : tbase ∈ Icc aβ bβ}
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : ContinuousLocalFlowSolution f (⟨tbase, htbaseα⟩ : Icc aα bα) xα rα)
    (β : ContinuousLocalFlowSolution f (⟨tbase, htbaseβ⟩ : Icc aβ bβ) xβ rβ)
    (hαtime : Icc a b ⊆ Icc aα bα)
    (hβtime : Icc a b ⊆ Icc aβ bβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (htbase : tbase ∈ Ioo a b)
    (hf_lip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo a b, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo a b, β.flow (x, t) ∈ state t) :
    EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Icc a b) :=
  LocalFlowSolution.eqOn_common_Icc_of_lipschitzOnWith_of_mem
    (α := α.toLocalFlowSolution) (β := β.toLocalFlowSolution)
    hαtime hβtime hxα hxβ htbase hf_lip hα_mem hβ_mem

/-- Pointwise closed-interval overlap uniqueness for continuous space-time local
flows. -/
theorem flow_eq_of_lipschitzOnWith_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : ContinuousLocalFlowSolution f t₀ xα rα)
    (β : ContinuousLocalFlowSolution f t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.flow (x, t) = β.flow (x, t) :=
  α.eqOn_Icc_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hf_lip hα_mem hβ_mem ht

/-- Continuous space-time local flows inherit the closed-interval uniqueness
bridge from `LocalFlowSolution`. -/
theorem eqOn_Icc_of_lipschitzOnWith
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ state t) :
    EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Icc tmin tmax) :=
  α.eqOn_Icc_of_lipschitzOnWith_of_mem β hx hx ht₀ hf_lip hα_mem hβ_mem

/-- Center-trajectory interior uniqueness for continuous space-time local flows. -/
theorem center_eqOn_Ioo_of_lipschitzOnWith
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ state t) :
    EqOn (fun t : ℝ => α.flow (x₀, t)) (fun t : ℝ => β.flow (x₀, t))
      (Ioo tmin tmax) :=
  α.eqOn_Ioo_of_lipschitzOnWith β (mem_closedBall_self r.2)
    ht₀ hf_lip hα_mem hβ_mem

/-- Pointwise center-trajectory interior uniqueness for continuous space-time
local flows. -/
theorem center_flow_eq_of_lipschitzOnWith_Ioo
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ state t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.flow (x₀, t) = β.flow (x₀, t) :=
  α.center_eqOn_Ioo_of_lipschitzOnWith β ht₀ hf_lip hα_mem hβ_mem ht

/-- Center-trajectory closed-interval uniqueness for continuous space-time local
flows. -/
theorem center_eqOn_Icc_of_lipschitzOnWith
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ state t) :
    EqOn (fun t : ℝ => α.flow (x₀, t)) (fun t : ℝ => β.flow (x₀, t))
      (Icc tmin tmax) :=
  α.eqOn_Icc_of_lipschitzOnWith β (mem_closedBall_self r.2)
    ht₀ hf_lip hα_mem hβ_mem

/-- Pointwise center-trajectory closed-interval uniqueness for continuous
space-time local flows. -/
theorem center_flow_eq_of_lipschitzOnWith_Icc
    (α β : ContinuousLocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ state t)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.flow (x₀, t) = β.flow (x₀, t) :=
  α.center_eqOn_Icc_of_lipschitzOnWith β ht₀ hf_lip hα_mem hβ_mem ht

end ContinuousLocalFlowSolution

namespace VariationalLocalFlowSolution

variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
  {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}

/-- Left-composition by a continuous linear map is Lipschitz on operator space,
with constant bounded by the left factor's operator norm. -/
theorem lipschitzWith_leftComp (D : V →L[ℝ] V) :
    LipschitzWith ‖D‖₊ (fun A : V →L[ℝ] V => D.comp A) := by
  let L : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.compL ℝ V V V D
  have hL : ‖L‖₊ ≤ ‖D‖₊ := by
    rw [← NNReal.coe_le_coe]
    change ‖L‖ ≤ ‖D‖
    exact L.opNorm_le_bound (norm_nonneg D) (fun A => by
      simpa [L] using D.opNorm_comp_le A)
  simpa [L] using L.lipschitz.weaken hL

/-- Left-composition is Lipschitz on any state set, with constant bounded by the
left factor's operator norm. -/
theorem lipschitzOnWith_leftComp (D : V →L[ℝ] V) (state : Set (V →L[ℝ] V)) :
    LipschitzOnWith ‖D‖₊ (fun A : V →L[ℝ] V => D.comp A) state :=
  (lipschitzWith_leftComp D).lipschitzOnWith

/-- Distance estimate for composition with a fixed right factor. -/
theorem dist_comp_right_le (D₁ D₂ A : V →L[ℝ] V) :
    dist (D₁.comp A) (D₂.comp A) ≤ dist D₁ D₂ * ‖A‖ := by
  have h := (D₁ - D₂).opNorm_comp_le A
  simpa [dist_eq_norm, ContinuousLinearMap.sub_comp] using h

/-- Distance estimate for composition with a fixed left factor. -/
theorem dist_comp_left_le (D A B : V →L[ℝ] V) :
    dist (D.comp A) (D.comp B) ≤ ‖D‖ * dist A B := by
  have h := D.opNorm_comp_le (A - B)
  simpa [dist_eq_norm, ContinuousLinearMap.comp_sub] using h

/-- Applying two continuous linear maps to a fixed vector is controlled by their
operator distance. -/
theorem dist_apply_le_mul (A B : V →L[ℝ] V) (v : V) :
    dist (A v) (B v) ≤ dist A B * ‖v‖ := by
  have h := ContinuousLinearMap.le_opNorm (A - B) v
  simpa [dist_eq_norm, sub_eq_add_neg] using h

/-- The operator norm is bounded on a closed ball by the center norm plus the
radius. -/
theorem nnnorm_le_nnnorm_add_radius_of_mem_closedBall
    {A A₀ : V →L[ℝ] V} {a : ℝ≥0}
    (hA : A ∈ closedBall A₀ a) :
    ‖A‖₊ ≤ ‖A₀‖₊ + a := by
  rw [← NNReal.coe_le_coe]
  exact_mod_cast (norm_le_of_mem_closedBall hA)

/-- The operator norm is bounded by `1 + a` on the closed ball of radius `a`
around the identity operator. -/
theorem nnnorm_le_one_add_radius_of_mem_closedBall_one
    {A : V →L[ℝ] V} {a : ℝ≥0}
    (hA : A ∈ closedBall (1 : V →L[ℝ] V) a) :
    ‖A‖₊ ≤ 1 + a := by
  calc
    ‖A‖₊ ≤ ‖(1 : V →L[ℝ] V)‖₊ + a :=
      nnnorm_le_nnnorm_add_radius_of_mem_closedBall hA
    _ ≤ 1 + a := by
      gcongr
      rw [← NNReal.coe_le_coe]
      exact_mod_cast (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V))

/-- Product-space Lipschitz estimate for the base component of the variational
ODE. -/
theorem lipschitzOnWith_variationalBasePart
    {f_t : V → V} {baseState : Set V} {tangentState : Set (V →L[ℝ] V)}
    {Kf : ℝ≥0}
    (hf_lip : LipschitzOnWith Kf f_t baseState) :
    LipschitzOnWith Kf (fun z : V × (V →L[ℝ] V) => f_t z.1)
      (baseState ×ˢ tangentState) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz w hw
  have hbase := hf_lip.dist_le_mul z.1 hz.1 w.1 hw.1
  have hfst : dist z.1 w.1 ≤ dist z w := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  exact hbase.trans (by gcongr)

/-- Product-space Lipschitz estimate for the linearized component
`(y, A) ↦ Df(y) ∘ A` on a base state and an operator state. -/
theorem lipschitzOnWith_variationalLinearPart
    {Df_t : V → V →L[ℝ] V}
    {baseState : Set V} {tangentState : Set (V →L[ℝ] V)}
    {KD BA BD : ℝ≥0}
    (hDf_lip : LipschitzOnWith KD Df_t baseState)
    (hA_bound : ∀ A ∈ tangentState, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ baseState, ‖Df_t y‖₊ ≤ BD) :
    LipschitzOnWith (KD * BA + BD)
      (fun z : V × (V →L[ℝ] V) => (Df_t z.1).comp z.2)
      (baseState ×ˢ tangentState) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz w hw
  have hbase := hDf_lip.dist_le_mul z.1 hz.1 w.1 hw.1
  have hA_bound' : ‖z.2‖ ≤ (BA : ℝ) := by
    exact_mod_cast hA_bound z.2 hz.2
  have hD_bound' : ‖Df_t w.1‖ ≤ (BD : ℝ) := by
    exact_mod_cast hD_bound w.1 hw.1
  have hfst : dist z.1 w.1 ≤ dist z w := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hsnd : dist z.2 w.2 ≤ dist z w := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hterm₁ :
      dist ((Df_t z.1).comp z.2) ((Df_t w.1).comp z.2) ≤
        (KD : ℝ) * (BA : ℝ) * dist z w := by
    calc
      dist ((Df_t z.1).comp z.2) ((Df_t w.1).comp z.2)
          ≤ dist (Df_t z.1) (Df_t w.1) * ‖z.2‖ :=
            dist_comp_right_le (Df_t z.1) (Df_t w.1) z.2
      _ ≤ ((KD : ℝ) * dist z.1 w.1) * (BA : ℝ) := by
            gcongr
      _ = (KD : ℝ) * (BA : ℝ) * dist z.1 w.1 := by ring
      _ ≤ (KD : ℝ) * (BA : ℝ) * dist z w := by
            gcongr
  have hterm₂ :
      dist ((Df_t w.1).comp z.2) ((Df_t w.1).comp w.2) ≤
        (BD : ℝ) * dist z w := by
    calc
      dist ((Df_t w.1).comp z.2) ((Df_t w.1).comp w.2)
          ≤ ‖Df_t w.1‖ * dist z.2 w.2 :=
            dist_comp_left_le (Df_t w.1) z.2 w.2
      _ ≤ (BD : ℝ) * dist z.2 w.2 := by
            gcongr
      _ ≤ (BD : ℝ) * dist z w := by
            gcongr
  calc
    dist ((Df_t z.1).comp z.2) ((Df_t w.1).comp w.2)
        ≤ dist ((Df_t z.1).comp z.2) ((Df_t w.1).comp z.2) +
            dist ((Df_t w.1).comp z.2) ((Df_t w.1).comp w.2) :=
          dist_triangle _ _ _
    _ ≤ ((KD : ℝ) * (BA : ℝ) * dist z w) + (BD : ℝ) * dist z w :=
          add_le_add hterm₁ hterm₂
    _ ≤ ↑(KD * BA + BD) * dist z w := by
          rw [NNReal.coe_add, NNReal.coe_mul]
          ring_nf
          exact le_rfl

/-- Product-space Lipschitz estimate for the full variational vector field,
combining a base-field Lipschitz estimate with bounded/Lipschitz control of the
linearized coefficient on the chosen base and operator states. -/
theorem lipschitzOnWith_variationalVectorField
    {f_t : V → V} {Df_t : V → V →L[ℝ] V}
    {baseState : Set V} {tangentState : Set (V →L[ℝ] V)}
    {Kf KD BA BD : ℝ≥0}
    (hf_lip : LipschitzOnWith Kf f_t baseState)
    (hDf_lip : LipschitzOnWith KD Df_t baseState)
    (hA_bound : ∀ A ∈ tangentState, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ baseState, ‖Df_t y‖₊ ≤ BD) :
    LipschitzOnWith (max Kf (KD * BA + BD))
      (fun z : V × (V →L[ℝ] V) => (f_t z.1, (Df_t z.1).comp z.2))
      (baseState ×ˢ tangentState) :=
  (lipschitzOnWith_variationalBasePart (tangentState := tangentState) hf_lip).prodMk
    (lipschitzOnWith_variationalLinearPart hDf_lip hA_bound hD_bound)

/-- Time-dependent specialization of the product-space Lipschitz estimate for
`variationalVectorField`. -/
theorem lipschitzOnWith_variationalVectorField_at
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V} {t : ℝ}
    {baseState : Set V} {tangentState : Set (V →L[ℝ] V)}
    {Kf KD BA BD : ℝ≥0}
    (hf_lip : LipschitzOnWith Kf (f t) baseState)
    (hDf_lip : LipschitzOnWith KD (Df t) baseState)
    (hA_bound : ∀ A ∈ tangentState, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ baseState, ‖Df t y‖₊ ≤ BD) :
    LipschitzOnWith (max Kf (KD * BA + BD))
      (variationalVectorField f Df t) (baseState ×ˢ tangentState) := by
  simpa [variationalVectorField] using
    lipschitzOnWith_variationalVectorField
      (f_t := f t) (Df_t := Df t) (tangentState := tangentState)
      hf_lip hDf_lip hA_bound hD_bound

/-- Closed-ball specialization of the product-space Lipschitz estimate for the
variational vector field, matching the spatial state used by
`IsPicardLindelof`. -/
theorem lipschitzOnWith_variationalVectorField_closedBall_at
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V} {t : ℝ}
    {x₀ : V} {A₀ : V →L[ℝ] V} {a Kf KD BA BD : ℝ≥0}
    (hf_lip : LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD) :
    LipschitzOnWith (max Kf (KD * BA + BD))
      (variationalVectorField f Df t) (closedBall (x₀, A₀) a) := by
  rw [← closedBall_prod_same x₀ A₀ (a : ℝ)]
  exact lipschitzOnWith_variationalVectorField_at
    (f := f) (Df := Df) (t := t)
    (baseState := closedBall x₀ a) (tangentState := closedBall A₀ a)
    hf_lip hDf_lip hA_bound hD_bound

/-- Closed-ball norm estimate for the full variational vector field from
componentwise bounds on the base field, linearized coefficient, and tangent
operator state. -/
theorem norm_variationalVectorField_le_closedBall_at
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V} {t : ℝ}
    {x₀ : V} {A₀ : V →L[ℝ] V} {a Lf BA BD : ℝ≥0}
    (hf_bound : ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    {z : V × (V →L[ℝ] V)} (hz : z ∈ closedBall (x₀, A₀) a) :
    ‖variationalVectorField f Df t z‖ ≤ max Lf (BD * BA) := by
  have hzprod : z.1 ∈ closedBall x₀ a ∧ z.2 ∈ closedBall A₀ a := by
    have hz' : z ∈ closedBall x₀ (a : ℝ) ×ˢ closedBall A₀ (a : ℝ) := by
      rw [closedBall_prod_same x₀ A₀ (a : ℝ)]
      exact hz
    exact hz'
  have hD_bound' : ‖Df t z.1‖ ≤ (BD : ℝ) := by
    exact_mod_cast hD_bound z.1 hzprod.1
  have hA_bound' : ‖z.2‖ ≤ (BA : ℝ) := by
    exact_mod_cast hA_bound z.2 hzprod.2
  have hlin : ‖(Df t z.1).comp z.2‖ ≤ (BD * BA : ℝ≥0) := by
    calc
      ‖(Df t z.1).comp z.2‖ ≤ ‖Df t z.1‖ * ‖z.2‖ :=
        (Df t z.1).opNorm_comp_le z.2
      _ ≤ (BD : ℝ) * (BA : ℝ) := by
        gcongr
      _ = (BD * BA : ℝ≥0) := by
        rw [NNReal.coe_mul]
  rw [variationalVectorField, Prod.norm_mk]
  exact max_le_max (hf_bound z.1 hzprod.1) hlin

/-- Time-continuity adapter for the product variational vector field at a fixed
state `z = (y, A)`. -/
theorem continuousOn_variationalVectorField_const
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {s : Set ℝ} (z : V × (V →L[ℝ] V))
    (hf_cont : ContinuousOn (fun t : ℝ => f t z.1) s)
    (hDf_cont : ContinuousOn (fun t : ℝ => Df t z.1) s) :
    ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) s := by
  have hlin : ContinuousOn (fun t : ℝ => (Df t z.1).comp z.2) s := by
    simpa using hDf_cont.clm_comp (continuousOn_const (c := z.2))
  simpa [variationalVectorField] using hf_cont.prodMk hlin

/-- Assemble Picard-Lindelöf hypotheses for the product variational system from
closed-ball estimates for the base field and its linearization.

The spatial Lipschitz field is discharged by
`lipschitzOnWith_variationalVectorField_closedBall_at`; continuity, a vector
field norm bound, and the interval-size inequality remain as the standard
Picard-Lindelöf assumptions. -/
theorem isPicardLindelof_variationalVectorField_of_closedBall_estimates
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : V} {A₀ : V →L[ℝ] V}
    {a r L Kf KD BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, A₀) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hnorm : ∀ t ∈ Icc tmin tmax, ∀ z ∈ closedBall (x₀, A₀) a,
      ‖variationalVectorField f Df t z‖ ≤ L)
    (hmul : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    IsPicardLindelof (variationalVectorField f Df) t₀ (x₀, A₀) a r L
      (max Kf (KD * BA + BD)) where
  lipschitzOnWith := fun t ht =>
    lipschitzOnWith_variationalVectorField_closedBall_at
      (f := f) (Df := Df) (t := t)
      (hf_lip t ht) (hDf_lip t ht) hA_bound (hD_bound t ht)
  continuousOn := hcont
  norm_le := hnorm
  mul_max_le := hmul

/-- Assemble Picard-Lindelöf hypotheses for the product variational system from
componentwise closed-ball estimates, deriving the product vector-field norm
bound automatically. -/
theorem isPicardLindelof_variationalVectorField_of_component_closedBall_estimates
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : V} {A₀ : V →L[ℝ] V}
    {a r Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, A₀) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    IsPicardLindelof (variationalVectorField f Df) t₀ (x₀, A₀) a r
      (max Lf (BD * BA)) (max Kf (KD * BA + BD)) :=
  isPicardLindelof_variationalVectorField_of_closedBall_estimates
    (A₀ := A₀) hf_lip hDf_lip hA_bound hD_bound hcont
    (fun t ht z hz =>
      norm_variationalVectorField_le_closedBall_at
        (f := f) (Df := Df) (t := t)
        (hf_bound t ht) hA_bound (hD_bound t ht) hz)
    hmul

/-- Assemble Picard-Lindelöf hypotheses for the product variational system from
componentwise closed-ball estimates and componentwise time-continuity. -/
theorem isPicardLindelof_variationalVectorField_of_component_closedBall_continuity
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : V} {A₀ : V →L[ℝ] V}
    {a r Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - r) :
    IsPicardLindelof (variationalVectorField f Df) t₀ (x₀, A₀) a r
      (max Lf (BD * BA)) (max Kf (KD * BA + BD)) :=
  isPicardLindelof_variationalVectorField_of_component_closedBall_estimates
    (A₀ := A₀) hf_lip hDf_lip hf_bound hA_bound hD_bound
    (fun z hz => by
      have hzprod : z.1 ∈ closedBall x₀ a ∧ z.2 ∈ closedBall A₀ a := by
        have hz' : z ∈ closedBall x₀ (a : ℝ) ×ˢ closedBall A₀ (a : ℝ) := by
          rw [closedBall_prod_same x₀ A₀ (a : ℝ)]
          exact hz
        exact hz'
      exact continuousOn_variationalVectorField_const z
        (hf_cont z.1 hzprod.1) (hDf_cont z.1 hzprod.1))
    hmul

/-- Extract a variational local flow from a continuous local flow of the product
system `(y, A)' = (f(t, y), Df(t, y) ∘ A)` initialized on pairs `(x, 1)`.

The radius for the extracted initial base points can be smaller than the product
Picard radius; `hball` records that every `(x, 1)` lies in the product initial
ball. -/
def ofProductContinuousLocalFlowSolution
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r where
  flow p := (α.flow ((p.1, (1 : V →L[ℝ] V)), p.2)).1
  initial_eq := by
    intro x hx
    exact congrArg Prod.fst (α.initial_eq (x, (1 : V →L[ℝ] V)) (hball x hx))
  hasDerivWithinAt := by
    intro x hx t ht
    exact hasDerivWithinAt_fst_of_variationalVectorField
      (α.hasDerivWithinAt (x, (1 : V →L[ℝ] V)) (hball x hx) t ht)
  continuousOn := by
    let embed : V × ℝ → (V × (V →L[ℝ] V)) × ℝ :=
      fun p => ((p.1, (1 : V →L[ℝ] V)), p.2)
    have hemb : ContinuousOn embed (closedBall x₀ r ×ˢ Icc tmin tmax) :=
      (by fun_prop : Continuous embed).continuousOn
    have hmaps : MapsTo embed (closedBall x₀ r ×ˢ Icc tmin tmax)
        (closedBall (x₀, (1 : V →L[ℝ] V)) R ×ˢ Icc tmin tmax) := by
      intro p hp
      exact ⟨hball p.1 hp.1, hp.2⟩
    exact (α.continuousOn.comp hemb hmaps).fst
  tangent x t := (α.flow ((x, (1 : V →L[ℝ] V)), t)).2
  tangent_initial_eq := by
    intro x hx
    exact congrArg Prod.snd (α.initial_eq (x, (1 : V →L[ℝ] V)) (hball x hx))
  tangent_hasDerivWithinAt := by
    intro x hx t ht
    exact hasDerivWithinAt_snd_of_variationalVectorField
      (α.hasDerivWithinAt (x, (1 : V →L[ℝ] V)) (hball x hx) t ht)

/-- Product-derived variational local flows inherit joint space-time continuity
of the base flow and tangent map from the continuous product flow. -/
theorem ofProduct_flow_tangent_continuousOn_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    ContinuousOn
      (fun p : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow p,
          (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2))
      (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  let embed : V × ℝ → (V × (V →L[ℝ] V)) × ℝ :=
    fun p => ((p.1, (1 : V →L[ℝ] V)), p.2)
  have hemb : ContinuousOn embed (closedBall x₀ r ×ˢ Icc tmin tmax) :=
    (by fun_prop : Continuous embed).continuousOn
  have hmaps : MapsTo embed (closedBall x₀ r ×ˢ Icc tmin tmax)
      (closedBall (x₀, (1 : V →L[ℝ] V)) R ×ˢ Icc tmin tmax) := by
    intro p hp
    exact ⟨hball p.1 hp.1, hp.2⟩
  simpa [ofProductContinuousLocalFlowSolution, embed] using α.continuousOn.comp hemb hmaps

/-- Pointwise within-space-time continuity of the product-derived
base-flow/tangent-map pair. -/
theorem ofProduct_flow_tangent_continuousWithinAt_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  (ofProduct_flow_tangent_continuousOn_spaceTime α hball).continuousWithinAt hp

/-- Product-derived variational local flows are eventually in any open
base/tangent target set around a space-time endpoint. -/
theorem ofProduct_flow_tangent_eventuallyWithin_mem_of_mem_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem :
      ((ofProductContinuousLocalFlowSolution α hball).flow p,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2) ∈ U) :
    (fun q : V × ℝ =>
      ((ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2)) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (ofProduct_flow_tangent_continuousWithinAt_spaceTime α hball hp)
    (hU.mem_nhds hmem)

/-- Product-derived variational local flows are ordinarily continuous at
interior points of the open Picard cylinder as `(flow, tangent)` pairs. -/
theorem ofProduct_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (x, t) :=
  (ofProduct_flow_tangent_continuousWithinAt_spaceTime α hball
    ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self ht⟩).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- Product-derived variational local flows are continuous as `(flow, tangent)`
pairs on the open Picard cylinder. -/
theorem ofProduct_flow_tangent_continuousOn_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    ContinuousOn
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (ofProduct_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hp.1 hp.2).continuousWithinAt

/-- Interior ordinary eventual-membership readout for product-derived
base-flow/tangent-map pairs. -/
theorem ofProduct_flow_tangent_eventually_mem_of_mem_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem :
      ((ofProductContinuousLocalFlowSolution α hball).flow (x, t),
        (ofProductContinuousLocalFlowSolution α hball).tangent x t) ∈ U) :
    (fun q : V × ℝ =>
      ((ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2)) ⁻¹' U ∈
      𝓝 (x, t) :=
  (ofProduct_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo α hball hx ht)
    (hU.mem_nhds hmem)

/-- Product-derived variational local flows inherit joint space-time continuity
of the full operator derivative-domain tuple `(t, flow, tangent)`. -/
theorem ofProduct_time_flow_tangent_continuousOn_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    ContinuousOn
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (closedBall x₀ r ×ˢ Icc tmin tmax) :=
  continuousOn_snd.prodMk (ofProduct_flow_tangent_continuousOn_spaceTime α hball)

/-- Pointwise within-space-time continuity of the product-derived operator
derivative-domain tuple `(t, flow, tangent)`. -/
theorem ofProduct_time_flow_tangent_continuousWithinAt_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  (ofProduct_time_flow_tangent_continuousOn_spaceTime α hball).continuousWithinAt hp

/-- Product-derived operator derivative-domain tuples are eventually in any
open target set around a closed-cylinder space-time endpoint. -/
theorem ofProduct_time_flow_tangent_eventuallyWithin_mem_of_mem_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem :
      (p.2,
        (ofProductContinuousLocalFlowSolution α hball).flow p,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2) ∈ U) :
    (fun q : V × ℝ =>
      (q.2,
        (ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2)) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (ofProduct_time_flow_tangent_continuousWithinAt_spaceTime α hball hp)
    (hU.mem_nhds hmem)

/-- Product-derived operator derivative-domain tuples are ordinarily continuous
at interior points of the open Picard cylinder. -/
theorem ofProduct_time_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (x, t) :=
  (ofProduct_time_flow_tangent_continuousWithinAt_spaceTime α hball
    ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self ht⟩).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- Product-derived operator derivative-domain tuples are continuous on the open
Picard cylinder. -/
theorem ofProduct_time_flow_tangent_continuousOn_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    ContinuousOn
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2))
      (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (ofProduct_time_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hp.1 hp.2).continuousWithinAt

/-- Interior ordinary eventual-membership readout for product-derived operator
derivative-domain tuples. -/
theorem ofProduct_time_flow_tangent_eventually_mem_of_mem_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem :
      (t,
        (ofProductContinuousLocalFlowSolution α hball).flow (x, t),
        (ofProductContinuousLocalFlowSolution α hball).tangent x t) ∈ U) :
    (fun q : V × ℝ =>
      (q.2,
        (ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2)) ⁻¹' U ∈
      𝓝 (x, t) :=
  (ofProduct_time_flow_tangent_continuousAt_spaceTime_of_mem_ball_Ioo α hball hx ht)
    (hU.mem_nhds hmem)

/-- Product-derived variational local flows inherit joint space-time continuity
of the scalar-readout state `(flow, A(t)u, A(t)v)` from the continuous product
flow. -/
theorem ofProduct_flow_tangent_apply_pair_continuousOn_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) :
    ContinuousOn
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  have hpair := ofProduct_flow_tangent_continuousOn_spaceTime α hball
  have hflow : ContinuousOn
      (fun q : V × ℝ => (ofProductContinuousLocalFlowSolution α hball).flow q)
      (closedBall x₀ r ×ˢ Icc tmin tmax) := hpair.fst
  have htangent : ContinuousOn
      (fun q : V × ℝ => (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2)
      (closedBall x₀ r ×ˢ Icc tmin tmax) := hpair.snd
  have hu : ContinuousOn
      (fun q : V × ℝ => (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u)
      (closedBall x₀ r ×ˢ Icc tmin tmax) := by
    simpa using htangent.clm_apply (continuousOn_const (c := u))
  have hv : ContinuousOn
      (fun q : V × ℝ => (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v)
      (closedBall x₀ r ×ˢ Icc tmin tmax) := by
    simpa using htangent.clm_apply (continuousOn_const (c := v))
  exact hflow.prodMk (hu.prodMk hv)

/-- Pointwise within-space-time continuity of the product-derived
scalar-readout state `(flow, A(t)u, A(t)v)`. -/
theorem ofProduct_flow_tangent_apply_pair_continuousWithinAt_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  (ofProduct_flow_tangent_apply_pair_continuousOn_spaceTime α hball u v).continuousWithinAt hp

/-- Product-derived scalar-readout states are eventually in any open target set
around a closed-cylinder space-time endpoint. -/
theorem ofProduct_flow_tangent_apply_pair_eventuallyWithin_mem_of_mem_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set (V × V × V)} (hU : IsOpen U)
    (hmem :
      ((ofProductContinuousLocalFlowSolution α hball).flow p,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2 v) ∈ U) :
    (fun q : V × ℝ =>
      ((ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v)) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (ofProduct_flow_tangent_apply_pair_continuousWithinAt_spaceTime α hball u v hp)
    (hU.mem_nhds hmem)

/-- Product-derived scalar-readout states are ordinarily continuous at interior
points of the open Picard cylinder. -/
theorem ofProduct_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V) :
    ContinuousAt
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (x, t) :=
  (ofProduct_flow_tangent_apply_pair_continuousWithinAt_spaceTime α hball u v
    ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self ht⟩).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- Product-derived scalar-readout states are continuous on the open Picard
cylinder. -/
theorem ofProduct_flow_tangent_apply_pair_continuousOn_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) :
    ContinuousOn
      (fun q : V × ℝ =>
        ((ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (ofProduct_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hp.1 hp.2 u v).continuousWithinAt

/-- Interior ordinary eventual-membership readout for product-derived
scalar-readout states. -/
theorem ofProduct_flow_tangent_apply_pair_eventually_mem_of_mem_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V)
    {U : Set (V × V × V)} (hU : IsOpen U)
    (hmem :
      ((ofProductContinuousLocalFlowSolution α hball).flow (x, t),
        (ofProductContinuousLocalFlowSolution α hball).tangent x t u,
        (ofProductContinuousLocalFlowSolution α hball).tangent x t v) ∈ U) :
    (fun q : V × ℝ =>
      ((ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v)) ⁻¹' U ∈
      𝓝 (x, t) :=
  (ofProduct_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hx ht u v) (hU.mem_nhds hmem)

/-- Product-derived variational local flows inherit joint space-time continuity
of the full derivative-domain tuple `(t, flow, A(t)u, A(t)v)` from the
continuous product flow. -/
theorem ofProduct_time_flow_tangent_apply_pair_continuousOn_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) :
    ContinuousOn
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (closedBall x₀ r ×ˢ Icc tmin tmax) :=
  continuousOn_snd.prodMk
    (ofProduct_flow_tangent_apply_pair_continuousOn_spaceTime α hball u v)

/-- Pointwise within-space-time continuity of the product-derived
derivative-domain tuple `(t, flow, A(t)u, A(t)v)`. -/
theorem ofProduct_time_flow_tangent_apply_pair_continuousWithinAt_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax) :
    ContinuousWithinAt
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (closedBall x₀ r ×ˢ Icc tmin tmax) p :=
  (ofProduct_time_flow_tangent_apply_pair_continuousOn_spaceTime α hball u v).continuousWithinAt hp

/-- Product-derived derivative-domain tuples are eventually in any open target
set around a closed-cylinder space-time endpoint. -/
theorem ofProduct_time_flow_tangent_apply_pair_eventuallyWithin_mem_of_mem_spaceTime
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) {p : V × ℝ} (hp : p ∈ closedBall x₀ r ×ˢ Icc tmin tmax)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem :
      (p.2,
        (ofProductContinuousLocalFlowSolution α hball).flow p,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent p.1 p.2 v) ∈ U) :
    (fun q : V × ℝ =>
      (q.2,
        (ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v)) ⁻¹' U ∈
      𝓝[closedBall x₀ r ×ˢ Icc tmin tmax] p :=
  (ofProduct_time_flow_tangent_apply_pair_continuousWithinAt_spaceTime α hball u v hp)
    (hU.mem_nhds hmem)

/-- Product-derived derivative-domain tuples are ordinarily continuous at
interior points of the open Picard cylinder. -/
theorem ofProduct_time_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V) :
    ContinuousAt
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (x, t) :=
  (ofProduct_time_flow_tangent_apply_pair_continuousWithinAt_spaceTime α hball u v
    ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self ht⟩).continuousAt
      (closedBall_prod_Icc_mem_nhds_of_mem_ball_Ioo hx ht)

/-- Product-derived derivative-domain tuples are continuous on the open Picard
cylinder. -/
theorem ofProduct_time_flow_tangent_apply_pair_continuousOn_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    (u v : V) :
    ContinuousOn
      (fun q : V × ℝ =>
        (q.2,
          (ofProductContinuousLocalFlowSolution α hball).flow q,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
          (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v))
      (ball x₀ r ×ˢ Ioo tmin tmax) := by
  intro p hp
  exact (ofProduct_time_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hp.1 hp.2 u v).continuousWithinAt

/-- Interior ordinary eventual-membership readout for product-derived
derivative-domain tuples. -/
theorem ofProduct_time_flow_tangent_apply_pair_eventually_mem_of_mem_spaceTime_Ioo
    {R : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {x : V} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem :
      (t,
        (ofProductContinuousLocalFlowSolution α hball).flow (x, t),
        (ofProductContinuousLocalFlowSolution α hball).tangent x t u,
        (ofProductContinuousLocalFlowSolution α hball).tangent x t v) ∈ U) :
    (fun q : V × ℝ =>
      (q.2,
        (ofProductContinuousLocalFlowSolution α hball).flow q,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 u,
        (ofProductContinuousLocalFlowSolution α hball).tangent q.1 q.2 v)) ⁻¹' U ∈
      𝓝 (x, t) :=
  (ofProduct_time_flow_tangent_apply_pair_continuousAt_spaceTime_of_mem_ball_Ioo
    α hball hx ht u v) (hU.mem_nhds hmem)

/-- Product Lipschitz dependence gives Lipschitz dependence of the extracted
base-flow/tangent-map pair on the base initial point. -/
theorem ofProduct_flow_tangent_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t))
        (closedBall x₀ r) := by
  obtain ⟨L', hL'⟩ := α.exists_lipschitzOnWith_time ht
  refine ⟨L', ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have h := hL'.dist_le_mul (x, (1 : V →L[ℝ] V)) (hball x hx)
    (y, (1 : V →L[ℝ] V)) (hball y hy)
  simpa [ofProductContinuousLocalFlowSolution, dist_prod_same_right] using h

/-- The extracted base-flow/tangent-map pair is continuous in the base initial
point at each Picard time. -/
theorem ofProduct_flow_tangent_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousOn
      (fun x : V =>
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ :=
    ofProduct_flow_tangent_exists_lipschitzOnWith_time α hball ht
  exact hL'.continuousOn

/-- Distance estimate for the extracted base-flow/tangent-map pair at each
Picard time. -/
theorem ofProduct_exists_dist_flow_tangent_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_flow_tangent_exists_lipschitzOnWith_time α hball ht
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence also controls the full fixed-time operator
derivative-domain tuple `(t, flow(t), tangent(t))` as a function of the base
initial point. The time coordinate is constant in this estimate. -/
theorem ofProduct_time_flow_tangent_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          (t,
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t))
        (closedBall x₀ r) := by
  obtain ⟨Lstate, hstate⟩ := ofProduct_flow_tangent_exists_lipschitzOnWith_time α hball ht
  have htime : LipschitzOnWith 0 (fun _x : V => t) (closedBall x₀ r) :=
    (LipschitzWith.const (α := V) (β := ℝ) t).lipschitzOnWith
  exact ⟨max 0 Lstate, htime.prodMk hstate⟩

/-- The full fixed-time operator derivative-domain tuple is continuous in the
base initial point at each Picard time. -/
theorem ofProduct_time_flow_tangent_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousOn
      (fun x : V =>
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ := ofProduct_time_flow_tangent_exists_lipschitzOnWith_time α hball ht
  exact hL'.continuousOn

/-- Distance estimate for the full fixed-time operator derivative-domain tuple
`(t, flow(t), tangent(t))` as the base initial point varies. -/
theorem ofProduct_exists_dist_time_flow_tangent_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ := ofProduct_time_flow_tangent_exists_lipschitzOnWith_time α hball ht
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence gives Lipschitz dependence of the extracted
base flow on the base initial point. -/
theorem ofProduct_flow_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t))
        (closedBall x₀ r) := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_flow_tangent_exists_lipschitzOnWith_time α hball ht
  refine ⟨L', ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hpair := hL'.dist_le_mul x hx y hy
  have hflow :
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t))
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t)) ≤
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  exact le_trans hflow hpair

/-- The extracted base flow is continuous in the base initial point at each
Picard time. -/
theorem ofProduct_flow_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousOn
      (fun x : V =>
        (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ := ofProduct_flow_exists_lipschitzOnWith_time α hball ht
  exact hL'.continuousOn

/-- Distance estimate for the extracted base flow at each Picard time. -/
theorem ofProduct_exists_dist_flow_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t))
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t)) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ := ofProduct_flow_exists_lipschitzOnWith_time α hball ht
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence gives Lipschitz dependence of the extracted
tangent map on the base initial point. -/
theorem ofProduct_tangent_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        (closedBall x₀ r) := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_flow_tangent_exists_lipschitzOnWith_time α hball ht
  refine ⟨L', ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hpair := hL'.dist_le_mul x hx y hy
  have htangent :
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) ≤
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  exact le_trans htangent hpair

/-- The extracted tangent map is continuous in the base initial point at each
Picard time. -/
theorem ofProduct_tangent_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousOn
      (fun x : V =>
        (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ := ofProduct_tangent_exists_lipschitzOnWith_time α hball ht
  exact hL'.continuousOn

/-- Distance estimate for the extracted tangent map at each Picard time. -/
theorem ofProduct_exists_dist_tangent_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ := ofProduct_tangent_exists_lipschitzOnWith_time α hball ht
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence gives Lipschitz dependence of every extracted
tangent-map vector slot on the base initial point. -/
theorem ofProduct_tangent_apply_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        (closedBall x₀ r) := by
  obtain ⟨L', hL'⟩ := ofProduct_tangent_exists_lipschitzOnWith_time α hball ht
  refine ⟨L' * ‖v‖₊, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hopen := hL'.dist_le_mul x hx y hy
  have happ := dist_apply_le_mul
    ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
    ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) v
  calc
    dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t v)
        ≤ dist
            ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
            ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t) *
            ‖v‖ := happ
    _ ≤ ((L' : ℝ) * dist x y) * ‖v‖ := by gcongr
    _ = (L' * ‖v‖₊ : ℝ≥0) * dist x y := by
      rw [NNReal.coe_mul, coe_nnnorm]
      ring

/-- Extracted tangent-map vector slots are continuous in the base initial point
at each Picard time. -/
theorem ofProduct_tangent_apply_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    ContinuousOn
      (fun x : V =>
        (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ :=
    ofProduct_tangent_apply_exists_lipschitzOnWith_time α hball ht v
  exact hL'.continuousOn

/-- Distance estimate for extracted tangent-map vector slots at each Picard
time. -/
theorem ofProduct_exists_dist_tangent_apply_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t v) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_tangent_apply_exists_lipschitzOnWith_time α hball ht v
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence gives Lipschitz dependence of two extracted
tangent-map vector slots on the base initial point. This is the vector-slot
shape used by scalar pullback readouts depending on `A(t) u` and `A(t) v`
together. -/
theorem ofProduct_tangent_apply_pair_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
        (closedBall x₀ r) := by
  obtain ⟨Lu, hLu⟩ := ofProduct_tangent_apply_exists_lipschitzOnWith_time α hball ht u
  obtain ⟨Lv, hLv⟩ := ofProduct_tangent_apply_exists_lipschitzOnWith_time α hball ht v
  exact ⟨max Lu Lv, hLu.prodMk hLv⟩

/-- Two extracted tangent-map vector slots are continuous in the base initial
point at each Picard time. -/
theorem ofProduct_tangent_apply_pair_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ContinuousOn
      (fun x : V =>
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ :=
    ofProduct_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact hL'.continuousOn

/-- Distance estimate for two extracted tangent-map vector slots at each
Picard time. -/
theorem ofProduct_exists_dist_tangent_apply_pair_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t v) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence gives Lipschitz dependence of the extracted
base flow together with two extracted tangent-map vector slots. This is the
initial-data estimate matching scalar readouts on `(flow(t), A(t)u, A(t)v)`. -/
theorem ofProduct_flow_tangent_apply_pair_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
        (closedBall x₀ r) := by
  obtain ⟨Lf, hLf⟩ := ofProduct_flow_exists_lipschitzOnWith_time α hball ht
  obtain ⟨Lv, hLv⟩ :=
    ofProduct_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact ⟨max Lf Lv, hLf.prodMk hLv⟩

/-- The extracted base flow together with two extracted tangent-map vector slots
is continuous in the base initial point at each Picard time. -/
theorem ofProduct_flow_tangent_apply_pair_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ContinuousOn
      (fun x : V =>
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ :=
    ofProduct_flow_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact hL'.continuousOn

/-- Distance estimate for the extracted base flow together with two extracted
tangent-map vector slots at each Picard time. -/
theorem ofProduct_exists_dist_flow_tangent_apply_pair_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t v) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_flow_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Product Lipschitz dependence also controls the full fixed-time
derivative-domain tuple `(t, flow(t), A(t)u, A(t)v)` as a function of the base
initial point. The time coordinate is constant in this estimate. -/
theorem ofProduct_time_flow_tangent_apply_pair_exists_lipschitzOnWith_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ∃ L' : ℝ≥0,
      LipschitzOnWith L'
        (fun x : V =>
          (t,
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
            (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
        (closedBall x₀ r) := by
  obtain ⟨Lstate, hstate⟩ :=
    ofProduct_flow_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  have htime : LipschitzOnWith 0 (fun _x : V => t) (closedBall x₀ r) :=
    (LipschitzWith.const (α := V) (β := ℝ) t).lipschitzOnWith
  exact ⟨max 0 Lstate, htime.prodMk hstate⟩

/-- The full fixed-time derivative-domain tuple is continuous in the base
initial point at each Picard time. -/
theorem ofProduct_time_flow_tangent_apply_pair_continuousOn_initialBall_time
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ContinuousOn
      (fun x : V =>
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v))
      (closedBall x₀ r) := by
  obtain ⟨_L', hL'⟩ :=
    ofProduct_time_flow_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact hL'.continuousOn

/-- Distance estimate for the full fixed-time derivative-domain tuple
`(t, flow(t), A(t)u, A(t)v)` as the base initial point varies. -/
theorem ofProduct_exists_dist_time_flow_tangent_apply_pair_le_mul
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V)
    {x y : V} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r) :
    ∃ L' : ℝ≥0,
      dist
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (x, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t v)
        (t,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t),
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t u,
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent y t v) ≤
        L' * dist x y := by
  obtain ⟨L', hL'⟩ :=
    ofProduct_time_flow_tangent_apply_pair_exists_lipschitzOnWith_time α hball ht u v
  exact ⟨L', hL'.dist_le_mul x hx y hy⟩

/-- Extract variational local-flow existence from proof-level continuous product
flow existence without choosing the product flow at call sites. -/
theorem nonempty_ofProductContinuousLocalFlowSolution
    {R : ℝ≥0}
    (hα : Nonempty
      (ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
        (x₀, (1 : V →L[ℝ] V)) R))
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) := by
  rcases hα with ⟨α⟩
  exact ⟨ofProductContinuousLocalFlowSolution α hball⟩

/-- Forget both tangent-equation and space-time continuity fields. -/
def toLocalFlowSolution (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    LocalFlowSolution f t₀ x₀ r :=
  α.toContinuousLocalFlowSolution.toLocalFlowSolution

/-- The tangent map of the center trajectory is initialized by the identity. -/
theorem center_tangent_initial_eq (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    α.tangent x₀ t₀ = 1 :=
  α.tangent_initial_eq x₀ (mem_closedBall_self r.2)

/-- The center tangent map solves the variational equation on the Picard
closed interval. -/
theorem center_tangent_hasDerivWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (α.tangent x₀)
      ((Df t (α.flow (x₀, t))).comp (α.tangent x₀ t)) (Icc tmin tmax) t :=
  α.tangent_hasDerivWithinAt x₀ (mem_closedBall_self r.2) t ht

/-- Applying the variational tangent-map equation to a fixed model vector gives
the vector-slot derivative used in scalar metric chain rules. -/
theorem tangent_apply_hasDerivWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    HasDerivWithinAt (fun τ : ℝ => α.tangent x τ v)
      (((Df t (α.flow (x, t))).comp (α.tangent x t)) v) (Icc tmin tmax) t := by
  have htan := α.tangent_hasDerivWithinAt x hx t ht
  have hev :
      HasFDerivWithinAt
        (fun A : V →L[ℝ] V => A v) (ContinuousLinearMap.apply ℝ V v)
        Set.univ (α.tangent x t) :=
    (ContinuousLinearMap.apply ℝ V v).hasFDerivWithinAt
  have hcomp := hev.comp t htan.hasFDerivWithinAt
    (Set.mapsTo_univ (fun τ : ℝ => α.tangent x τ) (Icc tmin tmax))
  simpa [Function.comp] using hcomp.hasDerivWithinAt

/-- Center-trajectory specialization of
`VariationalLocalFlowSolution.tangent_apply_hasDerivWithinAt`. -/
theorem center_tangent_apply_hasDerivWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax) (v : V) :
    HasDerivWithinAt (fun τ : ℝ => α.tangent x₀ τ v)
      (((Df t (α.flow (x₀, t))).comp (α.tangent x₀ t)) v) (Icc tmin tmax) t :=
  α.tangent_apply_hasDerivWithinAt (mem_closedBall_self r.2) ht v

/-- Restrict a variational local flow to a smaller initial ball and a smaller
closed time interval. -/
def restrict
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' where
  toContinuousLocalFlowSolution :=
    α.toContinuousLocalFlowSolution.restrict htime ht₀' hr
  tangent := α.tangent
  tangent_initial_eq := by
    intro x hx
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    simpa using α.tangent_initial_eq x hx'
  tangent_hasDerivWithinAt := by
    intro x hx t ht
    have hx' : x ∈ closedBall x₀ r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx (by exact_mod_cast hr)
    exact (α.tangent_hasDerivWithinAt x hx' t (htime ht)).mono htime

@[simp] theorem restrict_flow
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).flow = α.flow := rfl

@[simp] theorem restrict_tangent
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).tangent = α.tangent := rfl

@[simp] theorem restrict_toContinuousLocalFlowSolution
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).toContinuousLocalFlowSolution =
      α.toContinuousLocalFlowSolution.restrict htime ht₀' hr := rfl

@[simp] theorem restrict_toLocalFlowSolution
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    (α.restrict htime ht₀' hr).toLocalFlowSolution =
      α.toLocalFlowSolution.restrict htime ht₀' hr := rfl

/-- Restrict a nonempty variational local-flow existence witness to a smaller
initial ball and closed time interval. -/
theorem nonempty_restrict
    (hα : Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r)) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  rcases hα with ⟨α⟩
  exact ⟨α.restrict htime ht₀' hr⟩

/-- Extract a variational local flow from a continuous local flow of the product
system, immediately localized to a smaller closed time interval. -/
def ofProductContinuousLocalFlowSolution_restrict
    {R r' : ℝ≥0}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hball : ∀ x ∈ closedBall x₀ r',
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  (ofProductContinuousLocalFlowSolution (r := r') α hball).restrict htime ht₀' le_rfl

/-- Localized variational local-flow existence from proof-level continuous
product flow existence. -/
theorem nonempty_ofProductContinuousLocalFlowSolution_restrict
    {R r' : ℝ≥0}
    (hα : Nonempty
      (ContinuousLocalFlowSolution (variationalVectorField f Df) t₀
        (x₀, (1 : V →L[ℝ] V)) R))
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hball : ∀ x ∈ closedBall x₀ r',
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  rcases hα with ⟨α⟩
  exact ⟨ofProductContinuousLocalFlowSolution_restrict α htime ht₀' hball⟩

/-- On the interior of the Picard interval, the center base curve has the
ordinary derivative required by coordinate chain rules. -/
theorem center_flow_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => α.flow (x₀, τ))
      (f t (α.flow (x₀, t))) t :=
  α.toContinuousLocalFlowSolution.center_hasDerivAt_of_mem_Ioo ht

/-- Every initial point in the local ball has the ordinary base-flow derivative
on the interior of the Picard interval. -/
theorem flow_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun τ : ℝ => α.flow (x, τ))
      (f t (α.flow (x, t))) t :=
  α.toContinuousLocalFlowSolution.flow_hasDerivAt_of_mem_Ioo hx ht

/-- On the interior of the Picard interval, the center tangent map has the
ordinary derivative required by the coordinate gauge-pullback chain rule. -/
theorem center_tangent_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (α.tangent x₀)
      ((Df t (α.flow (x₀, t))).comp (α.tangent x₀ t)) t :=
  (α.center_tangent_hasDerivWithinAt (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Every initial point in the local ball has the ordinary tangent-map
variational derivative on the interior of the Picard interval. -/
theorem tangent_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (α.tangent x)
      ((Df t (α.flow (x, t))).comp (α.tangent x t)) t :=
  (α.tangent_hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Interior vector-slot derivative for the variational tangent map. -/
theorem tangent_apply_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V) :
    HasDerivAt (fun τ : ℝ => α.tangent x τ v)
      (((Df t (α.flow (x, t))).comp (α.tangent x t)) v) t :=
  (α.tangent_apply_hasDerivWithinAt hx (Ioo_subset_Icc_self ht) v).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Center-trajectory interior vector-slot derivative for the variational
tangent map. -/
theorem center_tangent_apply_hasDerivAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) (v : V) :
    HasDerivAt (fun τ : ℝ => α.tangent x₀ τ v)
      (((Df t (α.flow (x₀, t))).comp (α.tangent x₀ t)) v) t :=
  α.tangent_apply_hasDerivAt_of_mem_Ioo (mem_closedBall_self r.2) ht v

/-- Each base-flow time slice of a variational local flow is continuous within
the Picard interval. -/
theorem flow_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => α.flow (x, τ)) (Icc tmin tmax) t :=
  α.toContinuousLocalFlowSolution.flow_continuousWithinAt hx ht

/-- The center base-flow time slice of a variational local flow is continuous
within the Picard interval. -/
theorem center_flow_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => α.flow (x₀, τ)) (Icc tmin tmax) t :=
  α.flow_continuousWithinAt (mem_closedBall_self r.2) ht

/-- A variational local model-flow base curve is eventually, relative to the
closed Picard interval, in any open set containing its endpoint value. -/
theorem flow_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    (fun τ : ℝ => α.flow (x, τ)) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  (α.flow_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center-base-curve specialization of
`VariationalLocalFlowSolution.flow_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_flow_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x₀, t) ∈ U) :
    (fun τ : ℝ => α.flow (x₀, τ)) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  α.flow_eventuallyWithin_mem_of_mem_Icc (mem_closedBall_self r.2) ht hU hmem

/-- Each base-flow time slice of a variational local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem flow_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => α.flow (x, τ)) t :=
  α.toContinuousLocalFlowSolution.flow_continuousAt_of_mem_Ioo hx ht

/-- The center base-flow time slice of a variational local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem center_flow_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => α.flow (x₀, τ)) t :=
  α.flow_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- A variational local model-flow base curve is eventually in any open set
containing its interior-time value. -/
theorem flow_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x, t) ∈ U) :
    (fun τ : ℝ => α.flow (x, τ)) ⁻¹' U ∈ 𝓝 t :=
  (α.flow_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center-base-curve specialization of
`VariationalLocalFlowSolution.flow_eventually_mem_of_mem_Ioo`. -/
theorem center_flow_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax)
    {U : Set V} (hU : IsOpen U) (hmem : α.flow (x₀, t) ∈ U) :
    (fun τ : ℝ => α.flow (x₀, τ)) ⁻¹' U ∈ 𝓝 t :=
  α.flow_eventually_mem_of_mem_Ioo (mem_closedBall_self r.2) ht hU hmem

/-- Each tangent-map time slice of a variational local flow is continuous within
the Picard interval. -/
theorem tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (α.tangent x) (Icc tmin tmax) t :=
  (α.tangent_hasDerivWithinAt x hx t ht).continuousWithinAt

/-- The center tangent-map time slice of a variational local flow is continuous
within the Picard interval. -/
theorem center_tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (α.tangent x₀) (Icc tmin tmax) t :=
  α.tangent_continuousWithinAt (mem_closedBall_self r.2) ht

/-- Each tangent-map time slice of a variational local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (α.tangent x) t :=
  (α.tangent_hasDerivAt_of_mem_Ioo hx ht).continuousAt

/-- The center tangent-map time slice of a variational local flow is ordinarily
continuous on the interior of the Picard interval. -/
theorem center_tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (α.tangent x₀) t :=
  α.tangent_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- A variational local model-flow tangent map is eventually, relative to the
closed Picard interval, in any open operator set containing its endpoint value. -/
theorem tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set (V →L[ℝ] V)} (hU : IsOpen U) (hmem : α.tangent x t ∈ U) :
    (α.tangent x) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  (α.tangent_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center-tangent specialization of
`VariationalLocalFlowSolution.tangent_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax)
    {U : Set (V →L[ℝ] V)} (hU : IsOpen U) (hmem : α.tangent x₀ t ∈ U) :
    (α.tangent x₀) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  α.tangent_eventuallyWithin_mem_of_mem_Icc (mem_closedBall_self r.2) ht hU hmem

/-- A variational local model-flow tangent map is eventually in any open operator
set containing its interior-time value. -/
theorem tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set (V →L[ℝ] V)} (hU : IsOpen U) (hmem : α.tangent x t ∈ U) :
    (α.tangent x) ⁻¹' U ∈ 𝓝 t :=
  (α.tangent_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center-tangent specialization of
`VariationalLocalFlowSolution.tangent_eventually_mem_of_mem_Ioo`. -/
theorem center_tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax)
    {U : Set (V →L[ℝ] V)} (hU : IsOpen U) (hmem : α.tangent x₀ t ∈ U) :
    (α.tangent x₀) ⁻¹' U ∈ 𝓝 t :=
  α.tangent_eventually_mem_of_mem_Ioo (mem_closedBall_self r.2) ht hU hmem

/-- The base-flow/tangent-map pair is continuous within the Picard interval. -/
theorem flow_tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => (α.flow (x, τ), α.tangent x τ))
      (Icc tmin tmax) t :=
  (α.flow_continuousWithinAt hx ht).prodMk (α.tangent_continuousWithinAt hx ht)

/-- Center base-flow/tangent-map pair continuity within the Picard interval. -/
theorem center_flow_tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => (α.flow (x₀, τ), α.tangent x₀ τ))
      (Icc tmin tmax) t :=
  α.flow_tangent_continuousWithinAt (mem_closedBall_self r.2) ht

/-- The base-flow/tangent-map pair is eventually, relative to the closed Picard
interval, in any open product set containing its endpoint value. -/
theorem flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (α.flow (x, t), α.tangent x t) ∈ U) :
    (fun τ : ℝ => (α.flow (x, τ), α.tangent x τ)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  (α.flow_tangent_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.flow_tangent_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (α.flow (x₀, t), α.tangent x₀ t) ∈ U) :
    (fun τ : ℝ => (α.flow (x₀, τ), α.tangent x₀ τ)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  α.flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (mem_closedBall_self r.2) ht hU hmem

/-- The base-flow/tangent-map pair is ordinarily continuous on the open Picard
interior. -/
theorem flow_tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => (α.flow (x, τ), α.tangent x τ)) t :=
  (α.flow_continuousAt_of_mem_Ioo hx ht).prodMk
    (α.tangent_continuousAt_of_mem_Ioo hx ht)

/-- Center base-flow/tangent-map pair continuity on the open Picard interior. -/
theorem center_flow_tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => (α.flow (x₀, τ), α.tangent x₀ τ)) t :=
  α.flow_tangent_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- The base-flow/tangent-map pair is eventually in any open product set
containing its interior-time value. -/
theorem flow_tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (α.flow (x, t), α.tangent x t) ∈ U) :
    (fun τ : ℝ => (α.flow (x, τ), α.tangent x τ)) ⁻¹' U ∈ 𝓝 t :=
  (α.flow_tangent_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.flow_tangent_eventually_mem_of_mem_Ioo`. -/
theorem center_flow_tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax)
    {U : Set (V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (α.flow (x₀, t), α.tangent x₀ t) ∈ U) :
    (fun τ : ℝ => (α.flow (x₀, τ), α.tangent x₀ τ)) ⁻¹' U ∈ 𝓝 t :=
  α.flow_tangent_eventually_mem_of_mem_Ioo
    (mem_closedBall_self r.2) ht hU hmem

/-- The time/base-flow/tangent-map graph is continuous within the Picard interval. -/
theorem time_flow_tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ))
      (Icc tmin tmax) t :=
  continuousWithinAt_id.prodMk (α.flow_tangent_continuousWithinAt hx ht)

/-- Center time/base-flow/tangent-map graph continuity within the Picard interval. -/
theorem center_time_flow_tangent_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ))
      (Icc tmin tmax) t :=
  α.time_flow_tangent_continuousWithinAt (mem_closedBall_self r.2) ht

/-- The time/base-flow/tangent-map graph is eventually, relative to the closed
Picard interval, in any open product set containing its endpoint value. -/
theorem time_flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (t, α.flow (x, t), α.tangent x t) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  (α.time_flow_tangent_continuousWithinAt hx ht) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.time_flow_tangent_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_time_flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (t, α.flow (x₀, t), α.tangent x₀ t) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  α.time_flow_tangent_eventuallyWithin_mem_of_mem_Icc
    (mem_closedBall_self r.2) ht hU hmem

/-- The time/base-flow/tangent-map graph is ordinarily continuous on the open
Picard interior. -/
theorem time_flow_tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ)) t :=
  continuousAt_id.prodMk (α.flow_tangent_continuousAt_of_mem_Ioo hx ht)

/-- Center time/base-flow/tangent-map graph continuity on the open Picard interior. -/
theorem center_time_flow_tangent_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) :
    ContinuousAt (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ)) t :=
  α.time_flow_tangent_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht

/-- The time/base-flow/tangent-map graph is eventually in any open product set
containing its interior-time value. -/
theorem time_flow_tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (t, α.flow (x, t), α.tangent x t) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ)) ⁻¹' U ∈ 𝓝 t :=
  (α.time_flow_tangent_continuousAt_of_mem_Ioo hx ht) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.time_flow_tangent_eventually_mem_of_mem_Ioo`. -/
theorem center_time_flow_tangent_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax)
    {U : Set (ℝ × V × (V →L[ℝ] V))} (hU : IsOpen U)
    (hmem : (t, α.flow (x₀, t), α.tangent x₀ t) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ)) ⁻¹' U ∈ 𝓝 t :=
  α.time_flow_tangent_eventually_mem_of_mem_Ioo
    (mem_closedBall_self r.2) ht hU hmem

/-- Applying the variational tangent map to a fixed vector gives within-interval
continuity of the vector-slot time curve. -/
theorem tangent_apply_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    ContinuousWithinAt (fun τ : ℝ => α.tangent x τ v) (Icc tmin tmax) t :=
  (α.tangent_apply_hasDerivWithinAt hx ht v).continuousWithinAt

/-- Center-trajectory vector-slot continuity within the Picard interval. -/
theorem center_tangent_apply_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V) :
    ContinuousWithinAt (fun τ : ℝ => α.tangent x₀ τ v) (Icc tmin tmax) t :=
  α.tangent_apply_continuousWithinAt (mem_closedBall_self r.2) ht v

/-- Applying the variational tangent map to a fixed vector gives ordinary
continuity of the vector-slot time curve on the interior of the Picard interval. -/
theorem tangent_apply_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V) :
    ContinuousAt (fun τ : ℝ => α.tangent x τ v) t :=
  (α.tangent_apply_hasDerivAt_of_mem_Ioo hx ht v).continuousAt

/-- Center-trajectory vector-slot ordinary continuity on the interior of the
Picard interval. -/
theorem center_tangent_apply_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V) :
    ContinuousAt (fun τ : ℝ => α.tangent x₀ τ v) t :=
  α.tangent_apply_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht v

/-- A variational local model-flow tangent vector slot is eventually, relative to
the closed Picard interval, in any open set containing its endpoint value. -/
theorem tangent_apply_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V)
    {U : Set V} (hU : IsOpen U) (hmem : α.tangent x t v ∈ U) :
    (fun τ : ℝ => α.tangent x τ v) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  (α.tangent_apply_continuousWithinAt hx ht v) (hU.mem_nhds hmem)

/-- Center-vector-slot specialization of
`VariationalLocalFlowSolution.tangent_apply_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_tangent_apply_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (v : V)
    {U : Set V} (hU : IsOpen U) (hmem : α.tangent x₀ t v ∈ U) :
    (fun τ : ℝ => α.tangent x₀ τ v) ⁻¹' U ∈ 𝓝[Icc tmin tmax] t :=
  α.tangent_apply_eventuallyWithin_mem_of_mem_Icc (mem_closedBall_self r.2) ht v hU hmem

/-- A variational local model-flow tangent vector slot is eventually in any open
set containing its interior-time value. -/
theorem tangent_apply_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V)
    {U : Set V} (hU : IsOpen U) (hmem : α.tangent x t v ∈ U) :
    (fun τ : ℝ => α.tangent x τ v) ⁻¹' U ∈ 𝓝 t :=
  (α.tangent_apply_continuousAt_of_mem_Ioo hx ht v) (hU.mem_nhds hmem)

/-- Center-vector-slot specialization of
`VariationalLocalFlowSolution.tangent_apply_eventually_mem_of_mem_Ioo`. -/
theorem center_tangent_apply_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) (v : V)
    {U : Set V} (hU : IsOpen U) (hmem : α.tangent x₀ t v ∈ U) :
    (fun τ : ℝ => α.tangent x₀ τ v) ⁻¹' U ∈ 𝓝 t :=
  α.tangent_apply_eventually_mem_of_mem_Ioo (mem_closedBall_self r.2) ht v hU hmem

/-- The time/base-flow/two-vector-slot graph is continuous within the Picard interval. -/
theorem time_flow_tangent_apply₂_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ContinuousWithinAt
      (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ u, α.tangent x τ v))
      (Icc tmin tmax) t :=
  continuousWithinAt_id.prodMk
    ((α.flow_continuousWithinAt hx ht).prodMk
      ((α.tangent_apply_continuousWithinAt hx ht u).prodMk
        (α.tangent_apply_continuousWithinAt hx ht v)))

/-- Center time/base-flow/two-vector-slot graph continuity within the Picard interval. -/
theorem center_time_flow_tangent_apply₂_continuousWithinAt
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V) :
    ContinuousWithinAt
      (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ u, α.tangent x₀ τ v))
      (Icc tmin tmax) t :=
  α.time_flow_tangent_apply₂_continuousWithinAt (mem_closedBall_self r.2) ht u v

/-- The time/base-flow/two-vector-slot graph is eventually, relative to the
closed Picard interval, in any open product set containing its endpoint value. -/
theorem time_flow_tangent_apply₂_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Icc tmin tmax) (u v : V)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem : (t, α.flow (x, t), α.tangent x t u, α.tangent x t v) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ u, α.tangent x τ v)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  (α.time_flow_tangent_apply₂_continuousWithinAt hx ht u v) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.time_flow_tangent_apply₂_eventuallyWithin_mem_of_mem_Icc`. -/
theorem center_time_flow_tangent_apply₂_eventuallyWithin_mem_of_mem_Icc
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Icc tmin tmax) (u v : V)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem : (t, α.flow (x₀, t), α.tangent x₀ t u, α.tangent x₀ t v) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ u, α.tangent x₀ τ v)) ⁻¹' U ∈
      𝓝[Icc tmin tmax] t :=
  α.time_flow_tangent_apply₂_eventuallyWithin_mem_of_mem_Icc
    (mem_closedBall_self r.2) ht u v hU hmem

/-- The time/base-flow/two-vector-slot graph is ordinarily continuous on the
open Picard interior. -/
theorem time_flow_tangent_apply₂_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V) :
    ContinuousAt
      (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ u, α.tangent x τ v)) t :=
  continuousAt_id.prodMk
    ((α.flow_continuousAt_of_mem_Ioo hx ht).prodMk
      ((α.tangent_apply_continuousAt_of_mem_Ioo hx ht u).prodMk
        (α.tangent_apply_continuousAt_of_mem_Ioo hx ht v)))

/-- Center time/base-flow/two-vector-slot graph continuity on the open Picard interior. -/
theorem center_time_flow_tangent_apply₂_continuousAt_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V) :
    ContinuousAt
      (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ u, α.tangent x₀ τ v)) t :=
  α.time_flow_tangent_apply₂_continuousAt_of_mem_Ioo (mem_closedBall_self r.2) ht u v

/-- The time/base-flow/two-vector-slot graph is eventually in any open product
set containing its interior-time value. -/
theorem time_flow_tangent_apply₂_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax) (u v : V)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem : (t, α.flow (x, t), α.tangent x t u, α.tangent x t v) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x, τ), α.tangent x τ u, α.tangent x τ v)) ⁻¹' U ∈
      𝓝 t :=
  (α.time_flow_tangent_apply₂_continuousAt_of_mem_Ioo hx ht u v) (hU.mem_nhds hmem)

/-- Center specialization of
`VariationalLocalFlowSolution.time_flow_tangent_apply₂_eventually_mem_of_mem_Ioo`. -/
theorem center_time_flow_tangent_apply₂_eventually_mem_of_mem_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (ht : t ∈ Ioo tmin tmax) (u v : V)
    {U : Set (ℝ × V × V × V)} (hU : IsOpen U)
    (hmem : (t, α.flow (x₀, t), α.tangent x₀ t u, α.tangent x₀ t v) ∈ U) :
    (fun τ : ℝ => (τ, α.flow (x₀, τ), α.tangent x₀ τ u, α.tangent x₀ τ v)) ⁻¹' U ∈
      𝓝 t :=
  α.time_flow_tangent_apply₂_eventually_mem_of_mem_Ioo
    (mem_closedBall_self r.2) ht u v hU hmem

/-- Each base-flow time slice of a variational local flow is continuous on the
Picard interval. -/
theorem flow_continuousOn
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x, t)) (Icc tmin tmax) :=
  α.toContinuousLocalFlowSolution.flow_continuousOn hx

/-- The center base-flow time slice of a variational local flow is continuous on
the Picard interval. -/
theorem center_flow_continuousOn (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x₀, t)) (Icc tmin tmax) :=
  α.flow_continuousOn (mem_closedBall_self r.2)

/-- Each tangent-map time slice of a variational local flow is continuous on the
Picard interval. -/
theorem tangent_continuousOn
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (α.tangent x) (Icc tmin tmax) := by
  intro t ht
  exact (α.tangent_hasDerivWithinAt x hx t ht).continuousWithinAt

/-- The center tangent-map time slice of a variational local flow is continuous
on the Picard interval. -/
theorem center_tangent_continuousOn (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    ContinuousOn (α.tangent x₀) (Icc tmin tmax) :=
  α.tangent_continuousOn (mem_closedBall_self r.2)

/-- Applying the variational tangent map to a fixed vector gives a continuous
vector-slot time curve on the Picard interval. -/
theorem tangent_apply_continuousOn
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) (v : V) :
    ContinuousOn (fun t : ℝ => α.tangent x t v) (Icc tmin tmax) := by
  intro t ht
  exact (α.tangent_apply_hasDerivWithinAt hx ht v).continuousWithinAt

/-- Center-trajectory vector-slot continuity for the variational tangent map. -/
theorem center_tangent_apply_continuousOn
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) (v : V) :
    ContinuousOn (fun t : ℝ => α.tangent x₀ t v) (Icc tmin tmax) :=
  α.tangent_apply_continuousOn (mem_closedBall_self r.2) v

/-- Each base-flow time slice of a variational local flow is continuous on the
open Picard interior. -/
theorem flow_continuousOn_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x, t)) (Ioo tmin tmax) :=
  (α.flow_continuousOn hx).mono (fun _t ht => Ioo_subset_Icc_self ht)

/-- The center base-flow time slice of a variational local flow is continuous on
the open Picard interior. -/
theorem center_flow_continuousOn_Ioo (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    ContinuousOn (fun t : ℝ => α.flow (x₀, t)) (Ioo tmin tmax) :=
  α.flow_continuousOn_Ioo (mem_closedBall_self r.2)

/-- Each tangent-map time slice of a variational local flow is continuous on the
open Picard interior. -/
theorem tangent_continuousOn_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (α.tangent x) (Ioo tmin tmax) :=
  (α.tangent_continuousOn hx).mono (fun _t ht => Ioo_subset_Icc_self ht)

/-- The center tangent-map time slice of a variational local flow is continuous
on the open Picard interior. -/
theorem center_tangent_continuousOn_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) :
    ContinuousOn (α.tangent x₀) (Ioo tmin tmax) :=
  α.tangent_continuousOn_Ioo (mem_closedBall_self r.2)

/-- Applying the variational tangent map to a fixed vector gives a continuous
vector-slot time curve on the open Picard interior. -/
theorem tangent_apply_continuousOn_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {x : V}
    (hx : x ∈ closedBall x₀ r) (v : V) :
    ContinuousOn (fun t : ℝ => α.tangent x t v) (Ioo tmin tmax) :=
  (α.tangent_apply_continuousOn hx v).mono (fun _t ht => Ioo_subset_Icc_self ht)

/-- Center-trajectory vector-slot continuity on the open Picard interior. -/
theorem center_tangent_apply_continuousOn_Ioo
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) (v : V) :
    ContinuousOn (fun t : ℝ => α.tangent x₀ t v) (Ioo tmin tmax) :=
  α.tangent_apply_continuousOn_Ioo (mem_closedBall_self r.2) v

/-- Two variational local flows have the same tangent map on the interior
interval whenever their base curves agree there and the induced linearized ODE is
uniformly Lipschitz on a state region containing both tangent curves.  The two
packages may have different centers and radii; the initial point only has to lie
in both closed balls. -/
theorem tangent_eqOn_Ioo_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hlin_lip : ∀ t ∈ Ioo tmin tmax,
      LipschitzOnWith K (fun A : V →L[ℝ] V => (Df t (α.flow (x, t))).comp A) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) := by
  refine ODE_solution_unique_of_mem_Ioo
    (v := fun (t : ℝ) (A : V →L[ℝ] V) => (Df t (α.flow (x, t))).comp A)
    (s := state) hlin_lip ht₀ ?_ ?_ ?_
  · intro t ht
    exact ⟨α.tangent_hasDerivAt_of_mem_Ioo hxα ht, hα_mem t ht⟩
  · intro t ht
    have hβderiv := β.tangent_hasDerivAt_of_mem_Ioo hxβ ht
    rw [show β.flow (x, t) = α.flow (x, t) from (hflow_eq ht).symm] at hβderiv
    exact ⟨hβderiv, hβ_mem t ht⟩
  · rw [α.tangent_initial_eq x hxα, β.tangent_initial_eq x hxβ]

/-- Two variational local flows have the same tangent map on the interior
interval whenever their base curves agree there and the induced linearized ODE is
uniformly Lipschitz on a state region containing both tangent curves. -/
theorem tangent_eqOn_Ioo_of_lipschitzOnWith
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hlin_lip : ∀ t ∈ Ioo tmin tmax,
      LipschitzOnWith K (fun A : V →L[ℝ] V => (Df t (α.flow (x, t))).comp A) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
  α.tangent_eqOn_Ioo_of_lipschitzOnWith_of_mem β hx hx ht₀ hflow_eq hlin_lip
    hα_mem hβ_mem

/-- Tangent-map uniqueness on the interior interval when the linearized
operators are uniformly bounded there.  The Lipschitz hypothesis required by the
Gronwall uniqueness theorem follows from left-composition on operator space. -/
theorem tangent_eqOn_Ioo_of_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
  α.tangent_eqOn_Ioo_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hflow_eq
    (fun t ht =>
      ((lipschitzWith_leftComp (Df t (α.flow (x, t)))).weaken (hD_bound t ht)).lipschitzOnWith)
    hα_mem hβ_mem

/-- Pointwise interior tangent-map uniqueness when the linearized operators are
uniformly bounded. -/
theorem tangent_eq_of_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.tangent x t = β.tangent x t :=
  α.tangent_eqOn_Ioo_of_opNorm_bound_of_mem β hxα hxβ ht₀ hflow_eq hD_bound
    hα_mem hβ_mem ht

/-- Tangent-map uniqueness on the interior interval when the linearized
operators are uniformly bounded there.  The Lipschitz hypothesis required by the
Gronwall uniqueness theorem follows from left-composition on operator space. -/
theorem tangent_eqOn_Ioo_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
  α.tangent_eqOn_Ioo_of_opNorm_bound_of_mem β hx hx ht₀ hflow_eq hD_bound hα_mem hβ_mem

/-- Interior vector-slot uniqueness for variational tangent maps when the
linearized operators are uniformly bounded. -/
theorem tangent_apply_eqOn_Ioo_of_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x t v) (fun t : ℝ => β.tangent x t v)
      (Ioo tmin tmax) := by
  have htangent : EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
    α.tangent_eqOn_Ioo_of_opNorm_bound_of_mem (β := β) (state := fun _ => Set.univ)
      hxα hxβ ht₀ hflow_eq hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact congrArg (fun A : V →L[ℝ] V => A v) (htangent ht)

/-- Pointwise interior vector-slot uniqueness for variational tangent maps under
an operator-norm bound. -/
theorem tangent_apply_eq_of_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    α.tangent x t v = β.tangent x t v :=
  α.tangent_apply_eqOn_Ioo_of_opNorm_bound_of_mem β hxα hxβ ht₀ hflow_eq
    hD_bound v ht

/-- Interior vector-slot uniqueness for variational tangent maps when the
linearized operators are uniformly bounded. -/
theorem tangent_apply_eqOn_Ioo_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x t v) (fun t : ℝ => β.tangent x t v)
      (Ioo tmin tmax) :=
  α.tangent_apply_eqOn_Ioo_of_opNorm_bound_of_mem β hx hx ht₀ hflow_eq hD_bound v

/-- Center-trajectory interior vector-slot uniqueness for variational tangent
maps under an operator-norm bound. -/
theorem center_tangent_apply_eqOn_Ioo_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x₀, t)) (fun t => β.flow (x₀, t))
      (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x₀, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x₀ t v) (fun t : ℝ => β.tangent x₀ t v)
      (Ioo tmin tmax) :=
  α.tangent_apply_eqOn_Ioo_of_opNorm_bound β (mem_closedBall_self r.2)
    ht₀ hflow_eq hD_bound v

/-- Interior uniqueness for the full variational pair `(flow, tangent)`.

The base curve is handled by the usual spatial Lipschitz hypothesis for `f`.
The tangent curve then needs only a uniform operator-norm bound on `Df` along the
base curve; left-composition supplies the operator-space Lipschitz estimate.
Overlap form allowing different centers/radii. -/
theorem flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t))
      (Ioo tmin tmax) := by
  have hflow : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Ioo tmin tmax) :=
    α.toContinuousLocalFlowSolution.eqOn_Ioo_of_lipschitzOnWith_of_mem
      β.toContinuousLocalFlowSolution hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem
  have htangent : EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
    α.tangent_eqOn_Ioo_of_opNorm_bound_of_mem (β := β) (state := fun _ => Set.univ)
      hxα hxβ ht₀ hflow hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact Prod.ext (hflow ht) (htangent ht)

/-- Pointwise interior uniqueness for the full variational pair `(flow, tangent)`.
-/
theorem flow_tangent_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    (α.flow (x, t), α.tangent x t) = (β.flow (x, t), β.tangent x t) :=
  α.flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
    ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound ht

/-- Interior overlap uniqueness for the full operator derivative-domain tuple
`(t, flow, tangent)`. -/
theorem time_flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (t, α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (t, β.flow (x, t), β.tangent x t))
      (Ioo tmin tmax) := by
  have hstate :
      EqOn
        (fun t : ℝ => (α.flow (x, t), α.tangent x t))
        (fun t : ℝ => (β.flow (x, t), β.tangent x t))
        (Ioo tmin tmax) :=
    α.flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
      ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound
  intro t ht
  exact Prod.ext rfl (hstate ht)

/-- Pointwise interior uniqueness for the full operator derivative-domain tuple
`(t, flow, tangent)`. -/
theorem time_flow_tangent_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    (t, α.flow (x, t), α.tangent x t) = (t, β.flow (x, t), β.tangent x t) :=
  α.time_flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
    ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound ht

/-- Interior uniqueness for the full variational pair `(flow, tangent)`.

The base curve is handled by the usual spatial Lipschitz hypothesis for `f`.
The tangent curve then needs only a uniform operator-norm bound on `Df` along the
base curve; left-composition supplies the operator-space Lipschitz estimate. -/
theorem flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t))
      (Ioo tmin tmax) :=
  α.flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β hx hx ht₀
    hf_lip hα_base_mem hβ_base_mem hD_bound

/-- Center-trajectory interior uniqueness for the full variational pair
`(flow, tangent)`. -/
theorem center_flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x₀, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x₀, t), α.tangent x₀ t))
      (fun t : ℝ => (β.flow (x₀, t), β.tangent x₀ t))
      (Ioo tmin tmax) :=
  α.flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound β
    (mem_closedBall_self r.2) ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound

/-- Closed-interval uniqueness for tangent maps of variational local flows.  The
endpoint conclusion follows from the within-interval derivative statements via
continuity, while uniqueness on the interior uses the same Gronwall argument as
the base ODE.  Overlap form allowing different centers/radii. -/
theorem tangent_eqOn_Icc_of_lipschitzOnWith_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hlin_lip : ∀ t ∈ Ioo tmin tmax,
      LipschitzOnWith K (fun A : V →L[ℝ] V => (Df t (α.flow (x, t))).comp A) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) := by
  refine ODE_solution_unique_of_mem_Icc
    (v := fun (t : ℝ) (A : V →L[ℝ] V) => (Df t (α.flow (x, t))).comp A)
    (s := state) hlin_lip ht₀ ?_ ?_ hα_mem ?_ ?_ hβ_mem ?_
  · exact HasDerivWithinAt.continuousOn
      (fun t ht => α.tangent_hasDerivWithinAt x hxα t ht)
  · intro t ht
    exact α.tangent_hasDerivAt_of_mem_Ioo hxα ht
  · exact HasDerivWithinAt.continuousOn
      (fun t ht => β.tangent_hasDerivWithinAt x hxβ t ht)
  · intro t ht
    have hβderiv := β.tangent_hasDerivAt_of_mem_Ioo hxβ ht
    rw [show β.flow (x, t) = α.flow (x, t) from (hflow_eq ht).symm] at hβderiv
    exact hβderiv
  · rw [α.tangent_initial_eq x hxα, β.tangent_initial_eq x hxβ]

/-- Closed-interval uniqueness for tangent maps of variational local flows.  The
endpoint conclusion follows from the within-interval derivative statements via
continuity, while uniqueness on the interior uses the same Gronwall argument as
the base ODE. -/
theorem tangent_eqOn_Icc_of_lipschitzOnWith
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hlin_lip : ∀ t ∈ Ioo tmin tmax,
      LipschitzOnWith K (fun A : V →L[ℝ] V => (Df t (α.flow (x, t))).comp A) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
  α.tangent_eqOn_Icc_of_lipschitzOnWith_of_mem β hx hx ht₀ hflow_eq hlin_lip
    hα_mem hβ_mem

/-- Closed-interval tangent-map uniqueness when the linearized operators are
uniformly bounded on the interior.  Overlap form allowing different
centers/radii. -/
theorem tangent_eqOn_Icc_of_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
  α.tangent_eqOn_Icc_of_lipschitzOnWith_of_mem β hxα hxβ ht₀ hflow_eq
    (fun t ht =>
      ((lipschitzWith_leftComp (Df t (α.flow (x, t)))).weaken (hD_bound t ht)).lipschitzOnWith)
    hα_mem hβ_mem

/-- Pointwise closed-interval tangent-map uniqueness when the linearized
operators are uniformly bounded on the interior. -/
theorem tangent_eq_of_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.tangent x t = β.tangent x t :=
  α.tangent_eqOn_Icc_of_opNorm_bound_of_mem β hxα hxβ ht₀ hflow_eq hD_bound
    hα_mem hβ_mem ht

/-- Closed-interval tangent-map uniqueness when the linearized operators are
uniformly bounded on the interior. -/
theorem tangent_eqOn_Icc_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {state : ℝ → Set (V →L[ℝ] V)}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K)
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.tangent x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.tangent x t ∈ state t) :
    EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
  α.tangent_eqOn_Icc_of_opNorm_bound_of_mem β hx hx ht₀ hflow_eq hD_bound
    hα_mem hβ_mem

/-- Closed-interval vector-slot uniqueness for variational tangent maps when the
linearized operators are uniformly bounded on the interior.  Overlap form
allowing different centers/radii. -/
theorem tangent_apply_eqOn_Icc_of_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x t v) (fun t : ℝ => β.tangent x t v)
      (Icc tmin tmax) := by
  have htangent : EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
    α.tangent_eqOn_Icc_of_opNorm_bound_of_mem (β := β) (state := fun _ => Set.univ)
      hxα hxβ ht₀ hflow_eq hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact congrArg (fun A : V →L[ℝ] V => A v) (htangent ht)

/-- Pointwise closed-interval vector-slot uniqueness for variational tangent maps
under an operator-norm bound. -/
theorem tangent_apply_eq_of_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {K : ℝ≥0} {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    α.tangent x t v = β.tangent x t v :=
  α.tangent_apply_eqOn_Icc_of_opNorm_bound_of_mem β hxα hxβ ht₀ hflow_eq
    hD_bound v ht

/-- Closed-interval vector-slot uniqueness for variational tangent maps when the
linearized operators are uniformly bounded on the interior. -/
theorem tangent_apply_eqOn_Icc_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0} {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x, t)) (fun t => β.flow (x, t)) (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x t v) (fun t : ℝ => β.tangent x t v)
      (Icc tmin tmax) :=
  α.tangent_apply_eqOn_Icc_of_opNorm_bound_of_mem β hx hx ht₀ hflow_eq hD_bound v

/-- Center-trajectory closed-interval vector-slot uniqueness for variational
tangent maps under an operator-norm bound. -/
theorem center_tangent_apply_eqOn_Icc_of_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {K : ℝ≥0}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hflow_eq : EqOn (fun t => α.flow (x₀, t)) (fun t => β.flow (x₀, t))
      (Ioo tmin tmax))
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x₀, t))‖₊ ≤ K) (v : V) :
    EqOn (fun t : ℝ => α.tangent x₀ t v) (fun t : ℝ => β.tangent x₀ t v)
      (Icc tmin tmax) :=
  α.tangent_apply_eqOn_Icc_of_opNorm_bound β (mem_closedBall_self r.2)
    ht₀ hflow_eq hD_bound v

/-- Closed-interval uniqueness for the full variational pair `(flow, tangent)`
from a base-flow Lipschitz estimate and an operator-norm bound on the linearized
coefficient.  Overlap form allowing different centers/radii. -/
theorem flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t))
      (Icc tmin tmax) := by
  have hflowIcc : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Icc tmin tmax) :=
    α.toContinuousLocalFlowSolution.eqOn_Icc_of_lipschitzOnWith_of_mem
      β.toContinuousLocalFlowSolution hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem
  have hflowIoo : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Ioo tmin tmax) := fun t ht => hflowIcc (Ioo_subset_Icc_self ht)
  have htangent : EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
    α.tangent_eqOn_Icc_of_opNorm_bound_of_mem (β := β) (state := fun _ => Set.univ)
      hxα hxβ ht₀ hflowIoo hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact Prod.ext (hflowIcc ht) (htangent ht)

/-- Pointwise closed-interval uniqueness for the full variational pair
`(flow, tangent)`. -/
theorem flow_tangent_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (α.flow (x, t), α.tangent x t) = (β.flow (x, t), β.tangent x t) :=
  α.flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
    ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound ht

/-- Closed-interval overlap uniqueness for the full operator derivative-domain
tuple `(t, flow, tangent)`. -/
theorem time_flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (t, α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (t, β.flow (x, t), β.tangent x t))
      (Icc tmin tmax) := by
  have hstate :
      EqOn
        (fun t : ℝ => (α.flow (x, t), α.tangent x t))
        (fun t : ℝ => (β.flow (x, t), β.tangent x t))
        (Icc tmin tmax) :=
    α.flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
      ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound
  intro t ht
  exact Prod.ext rfl (hstate ht)

/-- Pointwise closed-interval uniqueness for the full operator derivative-domain
tuple `(t, flow, tangent)`. -/
theorem time_flow_tangent_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (t, α.flow (x, t), α.tangent x t) = (t, β.flow (x, t), β.tangent x t) :=
  α.time_flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
    ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound ht

/-- Closed-interval uniqueness for the full variational pair `(flow, tangent)`
from a base-flow Lipschitz estimate and an operator-norm bound on the linearized
coefficient. -/
theorem flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t))
      (Icc tmin tmax) :=
  α.flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β hx hx ht₀
    hf_lip hα_base_mem hβ_base_mem hD_bound

/-- Center-trajectory closed-interval uniqueness for the full variational pair
`(flow, tangent)`. -/
theorem center_flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound
    (α β : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x₀, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x₀, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x₀, t))‖₊ ≤ KD) :
    EqOn
      (fun t : ℝ => (α.flow (x₀, t), α.tangent x₀ t))
      (fun t : ℝ => (β.flow (x₀, t), β.tangent x₀ t))
      (Icc tmin tmax) :=
  α.flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound β
    (mem_closedBall_self r.2) ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound

/-- Interior overlap uniqueness for the scalar-readout state
`(flow, A(t)u, A(t)v)`. This is the gluing form used by chart-local scalar
pullback expressions after full variational-pair uniqueness is known. -/
theorem flow_tangent_apply_pair_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t u, α.tangent x t v))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t u, β.tangent x t v))
      (Ioo tmin tmax) := by
  have hpair :=
    α.flow_tangent_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
      ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound
  intro t ht
  have h := hpair ht
  have hflow : α.flow (x, t) = β.flow (x, t) := congrArg Prod.fst h
  have htangent : α.tangent x t = β.tangent x t := congrArg Prod.snd h
  exact Prod.ext hflow
    (Prod.ext (congrArg (fun A : V →L[ℝ] V => A u) htangent)
      (congrArg (fun A : V →L[ℝ] V => A v) htangent))

/-- Pointwise interior overlap uniqueness for the scalar-readout state
`(flow, A(t)u, A(t)v)`. -/
theorem flow_tangent_apply_pair_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    (α.flow (x, t), α.tangent x t u, α.tangent x t v) =
      (β.flow (x, t), β.tangent x t u, β.tangent x t v) :=
  α.flow_tangent_apply_pair_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β
    hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v ht

/-- Closed-interval overlap uniqueness for the scalar-readout state
`(flow, A(t)u, A(t)v)`. -/
theorem flow_tangent_apply_pair_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) :
    EqOn
      (fun t : ℝ => (α.flow (x, t), α.tangent x t u, α.tangent x t v))
      (fun t : ℝ => (β.flow (x, t), β.tangent x t u, β.tangent x t v))
      (Icc tmin tmax) := by
  have hpair :=
    α.flow_tangent_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β hxα hxβ
      ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound
  intro t ht
  have h := hpair ht
  have hflow : α.flow (x, t) = β.flow (x, t) := congrArg Prod.fst h
  have htangent : α.tangent x t = β.tangent x t := congrArg Prod.snd h
  exact Prod.ext hflow
    (Prod.ext (congrArg (fun A : V →L[ℝ] V => A u) htangent)
      (congrArg (fun A : V →L[ℝ] V => A v) htangent))

/-- Pointwise closed-interval overlap uniqueness for the scalar-readout state
`(flow, A(t)u, A(t)v)`. -/
theorem flow_tangent_apply_pair_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (α.flow (x, t), α.tangent x t u, α.tangent x t v) =
      (β.flow (x, t), β.tangent x t u, β.tangent x t v) :=
  α.flow_tangent_apply_pair_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β
    hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v ht

/-- Interior overlap uniqueness for the full derivative-domain tuple
`(t, flow, A(t)u, A(t)v)`. -/
theorem time_flow_tangent_apply_pair_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) :
    EqOn
      (fun t : ℝ => (t, α.flow (x, t), α.tangent x t u, α.tangent x t v))
      (fun t : ℝ => (t, β.flow (x, t), β.tangent x t u, β.tangent x t v))
      (Ioo tmin tmax) := by
  have hstate :=
    α.flow_tangent_apply_pair_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β
      hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v
  intro t ht
  exact Prod.ext rfl (hstate ht)

/-- Pointwise interior overlap uniqueness for the full derivative-domain tuple
`(t, flow, A(t)u, A(t)v)`. -/
theorem time_flow_tangent_apply_pair_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Ioo
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    (t, α.flow (x, t), α.tangent x t u, α.tangent x t v) =
      (t, β.flow (x, t), β.tangent x t u, β.tangent x t v) :=
  α.time_flow_tangent_apply_pair_eqOn_Ioo_of_lipschitzOnWith_opNorm_bound_of_mem β
    hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v ht

/-- Closed-interval overlap uniqueness for the full derivative-domain tuple
`(t, flow, A(t)u, A(t)v)`. -/
theorem time_flow_tangent_apply_pair_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) :
    EqOn
      (fun t : ℝ => (t, α.flow (x, t), α.tangent x t u, α.tangent x t v))
      (fun t : ℝ => (t, β.flow (x, t), β.tangent x t u, β.tangent x t v))
      (Icc tmin tmax) := by
  have hstate :=
    α.flow_tangent_apply_pair_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β
      hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v
  intro t ht
  exact Prod.ext rfl (hstate ht)

/-- Pointwise closed-interval overlap uniqueness for the full derivative-domain
tuple `(t, flow, A(t)u, A(t)v)`. -/
theorem time_flow_tangent_apply_pair_eq_of_lipschitzOnWith_opNorm_bound_of_mem_Icc
    {xα xβ : V} {rα rβ : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ xα rα)
    (β : VariationalLocalFlowSolution f Df t₀ xβ rβ)
    {Kf KD : ℝ≥0} {baseState : ℝ → Set V}
    {x : V} (hxα : x ∈ closedBall xα rα) (hxβ : x ∈ closedBall xβ rβ)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith Kf (f t) (baseState t))
    (hα_base_mem : ∀ t ∈ Ioo tmin tmax, α.flow (x, t) ∈ baseState t)
    (hβ_base_mem : ∀ t ∈ Ioo tmin tmax, β.flow (x, t) ∈ baseState t)
    (hD_bound : ∀ t ∈ Ioo tmin tmax, ‖Df t (α.flow (x, t))‖₊ ≤ KD)
    (u v : V) {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (t, α.flow (x, t), α.tangent x t u, α.tangent x t v) =
      (t, β.flow (x, t), β.tangent x t u, β.tangent x t v) :=
  α.time_flow_tangent_apply_pair_eqOn_Icc_of_lipschitzOnWith_opNorm_bound_of_mem β
    hxα hxβ ht₀ hf_lip hα_base_mem hβ_base_mem hD_bound u v ht

end VariationalLocalFlowSolution

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

/-- Picard-Lindelöf local-flow data, immediately localized to a smaller closed
time interval and initial ball. -/
def toLocalFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    LocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  (toLocalFlowSolution hf).restrict htime ht₀' hr

/-- Picard-Lindelöf local-flow existence as a proof-level witness. -/
theorem nonempty_localFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    Nonempty (LocalFlowSolution f t₀ x₀ r) :=
  ⟨toLocalFlowSolution hf⟩

/-- Localized Picard-Lindelöf local-flow existence as a proof-level witness. -/
theorem nonempty_localFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (LocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨toLocalFlowSolution_restrict hf htime ht₀' hr⟩

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

/-- Picard-Lindelöf Lipschitz local-flow data, immediately localized to a
smaller closed time interval and initial ball. -/
def toLipschitzLocalFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    LipschitzLocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  (toLipschitzLocalFlowSolution hf).restrict htime ht₀' hr

/-- Picard-Lindelöf Lipschitz local-flow existence as a proof-level witness. -/
theorem nonempty_lipschitzLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    Nonempty (LipschitzLocalFlowSolution f t₀ x₀ r) :=
  ⟨toLipschitzLocalFlowSolution hf⟩

/-- Localized Picard-Lindelöf Lipschitz local-flow existence as a proof-level
witness. -/
theorem nonempty_lipschitzLocalFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (LipschitzLocalFlowSolution f
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨toLipschitzLocalFlowSolution_restrict hf htime ht₀' hr⟩

/-- Picard-Lindelöf also yields a continuous partial space-time flow on the
initial-data ball times the closed time interval. -/
def toContinuousLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousLocalFlowSolution f t₀ x₀ r :=
  (toLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution

/-- Picard-Lindelöf continuous local-flow data, immediately localized to a
smaller closed time interval and initial ball. -/
def toContinuousLocalFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    ContinuousLocalFlowSolution f (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  (toContinuousLocalFlowSolution hf).restrict htime ht₀' hr

/-- Picard-Lindelöf continuous local-flow existence as a proof-level witness. -/
theorem nonempty_continuousLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    Nonempty (ContinuousLocalFlowSolution f t₀ x₀ r) :=
  ⟨toContinuousLocalFlowSolution hf⟩

/-- Localized Picard-Lindelöf continuous local-flow existence as a proof-level
witness. -/
theorem nonempty_continuousLocalFlowSolution_restrict
    (hf : IsPicardLindelof f t₀ x₀ a r L K) {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    {r' : ℝ≥0} (hr : r' ≤ r) :
    Nonempty (ContinuousLocalFlowSolution f
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨toContinuousLocalFlowSolution_restrict hf htime ht₀' hr⟩

end IsPicardLindelof

namespace VariationalLocalFlowSolution

variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
  {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}

/-- Picard-Lindelöf for the product variational system directly supplies the
base-flow/tangent-flow package after restricting to a base ball contained in the
product Picard ball. -/
def ofProductPicardLindelof
    [CompleteSpace V]
    {a R L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductContinuousLocalFlowSolution
    (IsPicardLindelof.toContinuousLocalFlowSolution hf) hball

/-- Product Picard-Lindelöf variational flow existence as a proof-level
witness. -/
theorem nonempty_ofProductPicardLindelof
    [CompleteSpace V]
    {a R L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductPicardLindelof hf hball⟩

/-- Product Picard-Lindelöf variational flow data, immediately localized to a
smaller closed time interval. -/
def ofProductPicardLindelof_restrict
    [CompleteSpace V]
    {a R L K r' : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hball : ∀ x ∈ closedBall x₀ r',
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductContinuousLocalFlowSolution_restrict
    (IsPicardLindelof.toContinuousLocalFlowSolution hf) htime ht₀' hball

/-- Localized product Picard-Lindelöf variational flow existence as a
proof-level witness. -/
theorem nonempty_ofProductPicardLindelof_restrict
    [CompleteSpace V]
    {a R L K r' : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hball : ∀ x ∈ closedBall x₀ r',
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductPicardLindelof_restrict hf htime ht₀' hball⟩

/-- Picard-Lindelöf for the product variational system supplies the variational
flow package on any base ball whose radius is no larger than the product Picard
radius. -/
def ofProductPicardLindelof_of_le_radius
    [CompleteSpace V]
    {a R L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductPicardLindelof hf (by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    calc
      dist (x, (1 : V →L[ℝ] V)) (x₀, (1 : V →L[ℝ] V))
          = max (dist x x₀) (dist (1 : V →L[ℝ] V) 1) := by
            rw [Prod.dist_eq]
      _ = dist x x₀ := by simp
      _ ≤ (R : ℝ) := hx.trans (by exact_mod_cast hr))

/-- Product Picard-Lindelöf variational flow existence on any base ball whose
radius is no larger than the product Picard radius, kept proof-level. -/
theorem nonempty_ofProductPicardLindelof_of_le_radius
    [CompleteSpace V]
    {a R L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductPicardLindelof_of_le_radius hf hr⟩

/-- Product Picard-Lindelöf variational flow data on a smaller closed interval
and any base ball whose radius is no larger than the product Picard radius. -/
def ofProductPicardLindelof_restrict_of_le_radius
    [CompleteSpace V]
    {a R L K r' : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductPicardLindelof_restrict hf htime ht₀' (by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    calc
      dist (x, (1 : V →L[ℝ] V)) (x₀, (1 : V →L[ℝ] V))
          = max (dist x x₀) (dist (1 : V →L[ℝ] V) 1) := by
            rw [Prod.dist_eq]
      _ = dist x x₀ := by simp
      _ ≤ (R : ℝ) := hx.trans (by exact_mod_cast hr))

/-- Localized product Picard-Lindelöf variational flow existence on any base
ball whose radius is no larger than the product Picard radius, kept proof-level. -/
theorem nonempty_ofProductPicardLindelof_restrict_of_le_radius
    [CompleteSpace V]
    {a R L K r' : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) a R L K)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductPicardLindelof_restrict_of_le_radius hf htime ht₀' hr⟩

/-- One-step variational local-flow constructor from closed-ball
Picard-Lindelöf estimates for the product system centered at `(x₀, 1)`.

This is the chart-level form expected in the positive-dimensional gauge-flow
construction: base-field and linearized-coefficient Lipschitz/boundedness
estimates supply the product Lipschitz hypothesis, while the remaining
continuity, norm, and time-radius assumptions are exactly the usual
Picard-Lindelöf data. -/
def ofProductClosedBallEstimates
    [CompleteSpace V]
    {a R L Kf KD BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hnorm : ∀ t ∈ Icc tmin tmax,
      ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
        ‖variationalVectorField f Df t z‖ ≤ L)
    (hmul : L * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductPicardLindelof_of_le_radius
    (isPicardLindelof_variationalVectorField_of_closedBall_estimates
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hA_bound hD_bound hcont hnorm hmul)
    hr

/-- One-step variational local-flow existence from closed-ball estimates,
kept proof-level. -/
theorem nonempty_ofProductClosedBallEstimates
    [CompleteSpace V]
    {a R L Kf KD BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hnorm : ∀ t ∈ Icc tmin tmax,
      ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
        ‖variationalVectorField f Df t z‖ ≤ L)
    (hmul : L * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductClosedBallEstimates hf_lip hDf_lip hA_bound hD_bound hcont hnorm hmul hr⟩

/-- Localized one-step variational local-flow constructor from closed-ball
Picard-Lindelöf estimates for the product system centered at `(x₀, 1)`. -/
def ofProductClosedBallEstimates_restrict
    [CompleteSpace V]
    {a R L Kf KD BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hnorm : ∀ t ∈ Icc tmin tmax,
      ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
        ‖variationalVectorField f Df t z‖ ≤ L)
    (hmul : L * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductPicardLindelof_restrict_of_le_radius
    (isPicardLindelof_variationalVectorField_of_closedBall_estimates
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hA_bound hD_bound hcont hnorm hmul)
    htime ht₀' hr

/-- Localized one-step variational local-flow existence from closed-ball
estimates, kept proof-level. -/
theorem nonempty_ofProductClosedBallEstimates_restrict
    [CompleteSpace V]
    {a R L Kf KD BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hnorm : ∀ t ∈ Icc tmin tmax,
      ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
        ‖variationalVectorField f Df t z‖ ≤ L)
    (hmul : L * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductClosedBallEstimates_restrict hf_lip hDf_lip hA_bound hD_bound hcont hnorm
    hmul htime ht₀' hr⟩

/-- One-step variational local-flow constructor from componentwise closed-ball
Picard-Lindelöf estimates for the product system centered at `(x₀, 1)`.

Compared with `ofProductClosedBallEstimates`, this version derives the product
vector-field norm bound from the base-field bound, the linearized-coefficient
bound, and the tangent-operator-state bound. -/
def ofProductComponentClosedBallEstimates
    [CompleteSpace V]
    {a R Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductPicardLindelof_of_le_radius
    (isPicardLindelof_variationalVectorField_of_component_closedBall_estimates
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hf_bound hA_bound hD_bound hcont hmul)
    hr

/-- One-step variational local-flow existence from componentwise closed-ball
estimates, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallEstimates
    [CompleteSpace V]
    {a R Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductComponentClosedBallEstimates hf_lip hDf_lip hf_bound hA_bound hD_bound
    hcont hmul hr⟩

/-- Localized one-step variational local-flow constructor from componentwise
closed-ball Picard-Lindelöf estimates for the product system. -/
def ofProductComponentClosedBallEstimates_restrict
    [CompleteSpace V]
    {a R Kf KD Lf BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductPicardLindelof_restrict_of_le_radius
    (isPicardLindelof_variationalVectorField_of_component_closedBall_estimates
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hf_bound hA_bound hD_bound hcont hmul)
    htime ht₀' hr

/-- Localized one-step variational local-flow existence from componentwise
closed-ball estimates, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallEstimates_restrict
    [CompleteSpace V]
    {a R Kf KD Lf BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hcont : ∀ z ∈ closedBall (x₀, (1 : V →L[ℝ] V)) a,
      ContinuousOn (fun t : ℝ => variationalVectorField f Df t z) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductComponentClosedBallEstimates_restrict hf_lip hDf_lip hf_bound hA_bound
    hD_bound hcont hmul htime ht₀' hr⟩

/-- One-step variational local-flow constructor from componentwise closed-ball
Picard-Lindelöf estimates and componentwise time-continuity. -/
def ofProductComponentClosedBallContinuityEstimates
    [CompleteSpace V]
    {a R Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductPicardLindelof_of_le_radius
    (isPicardLindelof_variationalVectorField_of_component_closedBall_continuity
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hf_bound hA_bound hD_bound hf_cont hDf_cont hmul)
    hr

/-- One-step variational local-flow existence from componentwise estimates and
componentwise time-continuity, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates
    [CompleteSpace V]
    {a R Kf KD Lf BA BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductComponentClosedBallContinuityEstimates hf_lip hDf_lip hf_bound hA_bound
    hD_bound hf_cont hDf_cont hmul hr⟩

/-- Localized one-step variational local-flow constructor from componentwise
closed-ball estimates and componentwise time-continuity. -/
def ofProductComponentClosedBallContinuityEstimates_restrict
    [CompleteSpace V]
    {a R Kf KD Lf BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductPicardLindelof_restrict_of_le_radius
    (isPicardLindelof_variationalVectorField_of_component_closedBall_continuity
      (A₀ := (1 : V →L[ℝ] V))
      (r := R) hf_lip hDf_lip hf_bound hA_bound hD_bound hf_cont hDf_cont hmul)
    htime ht₀' hr

/-- Localized one-step variational local-flow existence from componentwise
estimates and componentwise time-continuity, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates_restrict
    [CompleteSpace V]
    {a R Kf KD Lf BA BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hA_bound : ∀ A ∈ closedBall (1 : V →L[ℝ] V) a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductComponentClosedBallContinuityEstimates_restrict hf_lip hDf_lip hf_bound
    hA_bound hD_bound hf_cont hDf_cont hmul htime ht₀' hr⟩

/-- One-step variational local-flow constructor with the tangent-operator bound
derived from the closed ball around the identity operator. -/
def ofProductComponentClosedBallContinuityEstimates_of_operatorBall
    [CompleteSpace V]
    {a R Kf KD Lf BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (‖(1 : V →L[ℝ] V)‖₊ + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductComponentClosedBallContinuityEstimates
    (BA := ‖(1 : V →L[ℝ] V)‖₊ + a)
    hf_lip hDf_lip hf_bound
    (fun A hA => nnnorm_le_nnnorm_add_radius_of_mem_closedBall hA)
    hD_bound hf_cont hDf_cont hmul hr

/-- One-step variational local-flow existence with the tangent-operator bound
derived from the closed ball around the identity operator, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates_of_operatorBall
    [CompleteSpace V]
    {a R Kf KD Lf BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (‖(1 : V →L[ℝ] V)‖₊ + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductComponentClosedBallContinuityEstimates_of_operatorBall
    hf_lip hDf_lip hf_bound hD_bound hf_cont hDf_cont hmul hr⟩

/-- Localized one-step variational local-flow constructor with the
tangent-operator bound derived from the closed ball around the identity
operator. -/
def ofProductComponentClosedBallContinuityEstimates_restrict_of_operatorBall
    [CompleteSpace V]
    {a R Kf KD Lf BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (‖(1 : V →L[ℝ] V)‖₊ + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductComponentClosedBallContinuityEstimates_restrict
    (BA := ‖(1 : V →L[ℝ] V)‖₊ + a)
    hf_lip hDf_lip hf_bound
    (fun A hA => nnnorm_le_nnnorm_add_radius_of_mem_closedBall hA)
    hD_bound hf_cont hDf_cont hmul htime ht₀' hr

/-- Localized one-step variational local-flow existence with the tangent-operator
bound derived from the closed ball around the identity operator, kept
proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates_restrict_of_operatorBall
    [CompleteSpace V]
    {a R Kf KD Lf BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (‖(1 : V →L[ℝ] V)‖₊ + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductComponentClosedBallContinuityEstimates_restrict_of_operatorBall
    hf_lip hDf_lip hf_bound hD_bound hf_cont hDf_cont hmul htime ht₀' hr⟩

/-- One-step variational local-flow constructor with the tangent-operator bound
derived as `‖A‖₊ ≤ 1 + a` on the closed ball around the identity operator. -/
def ofProductComponentClosedBallContinuityEstimates_of_identityBall
    [CompleteSpace V]
    {a R Kf KD Lf BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (1 + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    VariationalLocalFlowSolution f Df t₀ x₀ r :=
  ofProductComponentClosedBallContinuityEstimates
    (BA := 1 + a)
    hf_lip hDf_lip hf_bound
    (fun A hA => nnnorm_le_one_add_radius_of_mem_closedBall_one hA)
    hD_bound hf_cont hDf_cont hmul hr

/-- One-step variational local-flow existence with the tangent-operator bound
`‖A‖₊ ≤ 1 + a`, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates_of_identityBall
    [CompleteSpace V]
    {a R Kf KD Lf BD : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (1 + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    (hr : r ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df t₀ x₀ r) :=
  ⟨ofProductComponentClosedBallContinuityEstimates_of_identityBall
    hf_lip hDf_lip hf_bound hD_bound hf_cont hDf_cont hmul hr⟩

/-- Localized one-step variational local-flow constructor with the
tangent-operator bound derived as `‖A‖₊ ≤ 1 + a` on the closed ball around the
identity operator. -/
def ofProductComponentClosedBallContinuityEstimates_restrict_of_identityBall
    [CompleteSpace V]
    {a R Kf KD Lf BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (1 + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r' :=
  ofProductComponentClosedBallContinuityEstimates_restrict
    (BA := 1 + a)
    hf_lip hDf_lip hf_bound
    (fun A hA => nnnorm_le_one_add_radius_of_mem_closedBall_one hA)
    hD_bound hf_cont hDf_cont hmul htime ht₀' hr

/-- Localized one-step variational local-flow existence with the tangent-operator
bound `‖A‖₊ ≤ 1 + a`, kept proof-level. -/
theorem nonempty_ofProductComponentClosedBallContinuityEstimates_restrict_of_identityBall
    [CompleteSpace V]
    {a R Kf KD Lf BD r' : ℝ≥0}
    (hf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall x₀ a))
    (hDf_lip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (Df t) (closedBall x₀ a))
    (hf_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a, ‖f t y‖ ≤ Lf)
    (hD_bound : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall x₀ a,
      ‖Df t y‖₊ ≤ BD)
    (hf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax))
    (hDf_cont : ∀ y ∈ closedBall x₀ a, ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax))
    (hmul : (max Lf (BD * (1 + a))) *
      max (tmax - t₀) (t₀ - tmin) ≤ a - R)
    {tmin' tmax' : ℝ}
    (htime : Icc tmin' tmax' ⊆ Icc tmin tmax)
    (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax')
    (hr : r' ≤ R) :
    Nonempty (VariationalLocalFlowSolution f Df
      (⟨(t₀ : ℝ), ht₀'⟩ : Icc tmin' tmax') x₀ r') :=
  ⟨ofProductComponentClosedBallContinuityEstimates_restrict_of_identityBall
    hf_lip hDf_lip hf_bound hD_bound hf_cont hDf_cont hmul htime ht₀' hr⟩

end VariationalLocalFlowSolution

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

/-- Autonomous local integral curves from a `C¹` vector field, bundled with the
continuity on the open existence interval obtained from their derivatives. -/
theorem exists_autonomous_local_integral_curves_continuousOn
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r,
      ∃ α : ℝ → V, α t₀ = x ∧ ContinuousOn α (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  obtain ⟨r, hr, ε, hε, hcurves⟩ :=
    exists_autonomous_local_integral_curves (V := V) hf t₀
  refine ⟨r, hr, ε, hε, ?_⟩
  intro x hx
  obtain ⟨α, hinit, hderiv⟩ := hcurves x hx
  refine ⟨α, hinit, ?_, hderiv⟩
  intro t ht
  exact (hderiv t ht).continuousAt.continuousWithinAt

/-- A `C¹` autonomous vector field supplies a packaged `LocalFlowSolution` on a
smaller closed time interval and a smaller initial ball.  This is the direct
model-space raw-flow existence bridge extracted from mathlib's autonomous
integral-curve theorem. -/
theorem exists_autonomous_localFlowSolution
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∃ ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε),
        Nonempty (LocalFlowSolution (fun _ : ℝ => f)
          (⟨t₀, ht₀⟩ : Icc (t₀ - ε) (t₀ + ε)) x₀ r) := by
  classical
  obtain ⟨r₀, hr₀, ε₀, hε₀, hcurves⟩ :=
    exists_autonomous_local_integral_curves (V := V) hf t₀
  let r : ℝ≥0 := ⟨r₀ / 2, by linarith⟩
  let ε : ℝ := ε₀ / 2
  have hr : 0 < r := by
    rw [← NNReal.coe_lt_coe]
    change (0 : ℝ) < r₀ / 2
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by
    constructor <;> dsimp [ε] <;> linarith
  refine ⟨r, hr, ε, hε, ht₀, ?_⟩
  have hball_sub : ∀ x, x ∈ closedBall x₀ r → x ∈ closedBall x₀ r₀ := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    calc
      dist x x₀ ≤ (r : ℝ) := hx
      _ = r₀ / 2 := rfl
      _ ≤ r₀ := by linarith
  have hcurves_all : ∀ x : V, ∃ α : ℝ → V,
      x ∈ closedBall x₀ r →
        α t₀ = x ∧
          ∀ t ∈ Ioo (t₀ - ε₀) (t₀ + ε₀), HasDerivAt α (f (α t)) t := by
    intro x
    by_cases hx : x ∈ closedBall x₀ r
    · obtain ⟨α, hinit, hderiv⟩ := hcurves x (hball_sub x hx)
      exact ⟨α, fun _ => ⟨hinit, hderiv⟩⟩
    · exact ⟨fun _ => x, fun hx' => (hx hx').elim⟩
  refine ⟨?_⟩
  refine
    { flow := fun x t => Classical.choose (hcurves_all x) t
      initial_eq := ?_
      hasDerivWithinAt := ?_ }
  · intro x hx
    exact ((Classical.choose_spec (hcurves_all x)) hx).1
  · intro x hx t ht
    have hderiv := ((Classical.choose_spec (hcurves_all x)) hx).2
    have htopen : t ∈ Ioo (t₀ - ε₀) (t₀ + ε₀) := by
      constructor
      · dsimp [ε] at ht
        linarith [ht.1]
      · dsimp [ε] at ht
        linarith [ht.2]
    exact (hderiv t htopen).hasDerivWithinAt

/-- Localized autonomous `C¹` model-flow existence on any smaller closed
interval and smaller initial ball after the Picard radius has been chosen. -/
theorem exists_autonomous_localFlowSolution_restrict
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∀ {tmin' tmax' : ℝ},
        (htime : Icc tmin' tmax' ⊆ Icc (t₀ - ε) (t₀ + ε)) →
        (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax') →
        ∀ {r' : ℝ≥0}, r' ≤ r →
          Nonempty (LocalFlowSolution (fun _ : ℝ => f)
            (⟨t₀, ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  obtain ⟨r, hr, ε, hε, ht₀, hα⟩ := exists_autonomous_localFlowSolution (V := V) hf t₀
  refine ⟨r, hr, ε, hε, ?_⟩
  intro tmin' tmax' htime ht₀' r' hr'
  exact LocalFlowSolution.nonempty_restrict hα htime ht₀' hr'

/-- A `C¹` autonomous vector field supplies a packaged Lipschitz local flow on a
closed Picard interval.  This strengthens the bare local-flow extraction by
using the Lipschitz-dependence part of mathlib's Picard-Lindelöf theorem. -/
theorem exists_autonomous_lipschitzLocalFlowSolution
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∃ ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε),
        Nonempty (LipschitzLocalFlowSolution (fun _ : ℝ => f)
          (⟨t₀, ht₀⟩ : Icc (t₀ - ε) (t₀ + ε)) x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  refine ⟨r, hr, ε, hε, ht₀, ?_⟩
  simpa using
    (ModelGaugeFlowODE.IsPicardLindelof.nonempty_lipschitzLocalFlowSolution
      (V := V) (f := fun _ : ℝ => f)
      (t₀ := (⟨t₀, ht₀⟩ : Icc (t₀ - ε) (t₀ + ε)))
      (x₀ := x₀) (a := a) (r := r) (L := L) (K := K) (hpl t₀))

/-- Localized Lipschitz autonomous model-flow existence on any smaller closed
time interval and smaller initial ball after the Picard radius has been chosen. -/
theorem exists_autonomous_lipschitzLocalFlowSolution_restrict
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∀ {tmin' tmax' : ℝ},
        (htime : Icc tmin' tmax' ⊆ Icc (t₀ - ε) (t₀ + ε)) →
        (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax') →
        ∀ {r' : ℝ≥0}, r' ≤ r →
          Nonempty (LipschitzLocalFlowSolution (fun _ : ℝ => f)
            (⟨t₀, ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  obtain ⟨r, hr, ε, hε, ht₀, hα⟩ :=
    exists_autonomous_lipschitzLocalFlowSolution (V := V) hf t₀
  refine ⟨r, hr, ε, hε, ?_⟩
  intro tmin' tmax' htime ht₀' r' hr'
  exact LipschitzLocalFlowSolution.nonempty_restrict hα htime ht₀' hr'

/-- A `C¹` autonomous vector field supplies a packaged continuous space-time
local flow on a closed Picard interval. -/
theorem exists_autonomous_continuousLocalFlowSolution
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∃ ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε),
        Nonempty (ContinuousLocalFlowSolution (fun _ : ℝ => f)
          (⟨t₀, ht₀⟩ : Icc (t₀ - ε) (t₀ + ε)) x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  refine ⟨r, hr, ε, hε, ht₀, ?_⟩
  simpa using
    (ModelGaugeFlowODE.IsPicardLindelof.nonempty_continuousLocalFlowSolution
      (V := V) (f := fun _ : ℝ => f)
      (t₀ := (⟨t₀, ht₀⟩ : Icc (t₀ - ε) (t₀ + ε)))
      (x₀ := x₀) (a := a) (r := r) (L := L) (K := K) (hpl t₀))

/-- Localized continuous autonomous model-flow existence on any smaller closed
time interval and smaller initial ball after the Picard radius has been chosen. -/
theorem exists_autonomous_continuousLocalFlowSolution_restrict
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε > (0 : ℝ),
      ∀ {tmin' tmax' : ℝ},
        (htime : Icc tmin' tmax' ⊆ Icc (t₀ - ε) (t₀ + ε)) →
        (ht₀' : (t₀ : ℝ) ∈ Icc tmin' tmax') →
        ∀ {r' : ℝ≥0}, r' ≤ r →
          Nonempty (ContinuousLocalFlowSolution (fun _ : ℝ => f)
            (⟨t₀, ht₀'⟩ : Icc tmin' tmax') x₀ r') := by
  obtain ⟨r, hr, ε, hε, ht₀, hα⟩ :=
    exists_autonomous_continuousLocalFlowSolution (V := V) hf t₀
  refine ⟨r, hr, ε, hε, ?_⟩
  intro tmin' tmax' htime ht₀' r' hr'
  exact ContinuousLocalFlowSolution.nonempty_restrict hα htime ht₀' hr'

/-- Centered version of
`exists_autonomous_local_integral_curves`, matching the single-trajectory ODE
statement used when only the gauge curve through one point is needed. -/
theorem exists_autonomous_center_integral_curve
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → V, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- Centered autonomous integral curve with continuity on the open existence
interval. -/
theorem exists_autonomous_center_integral_curve_continuousOn
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → V, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ContinuousOn α (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  obtain ⟨α, hinit, ε, hε, hderiv⟩ :=
    exists_autonomous_center_integral_curve (V := V) hf t₀
  refine ⟨α, hinit, ε, hε, ?_, hderiv⟩
  intro t ht
  exact (hderiv t ht).continuousAt.continuousWithinAt

end ContDiffAt

end ModelGaugeFlowODE

end RicciFlow
