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

/-- Two packaged local model flows agree on the interior time interval whenever
their curves stay in a region where the vector field is uniformly Lipschitz. -/
theorem eqOn_Ioo_of_lipschitzOnWith
    (α β : LocalFlowSolution f t₀ x₀ r) {K : ℝ≥0} {state : ℝ → Set V}
    {x : V} (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax)
    (hf_lip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (state t))
    (hα_mem : ∀ t ∈ Ioo tmin tmax, α.flow x t ∈ state t)
    (hβ_mem : ∀ t ∈ Ioo tmin tmax, β.flow x t ∈ state t) :
    EqOn (α.flow x) (β.flow x) (Ioo tmin tmax) := by
  refine ODE_solution_unique_of_mem_Ioo (v := f) (s := state) hf_lip ht₀ ?_ ?_ ?_
  · intro t ht
    exact
      ⟨(α.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),
        hα_mem t ht⟩
  · intro t ht
    exact
      ⟨(β.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),
        hβ_mem t ht⟩
  · rw [α.initial_eq x hx, β.initial_eq x hx]

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
    EqOn (α.flow x) (β.flow x) (Icc tmin tmax) := by
  refine ODE_solution_unique_of_mem_Icc (v := f) (s := state) hf_lip ht₀ ?_ ?_ hα_mem ?_ ?_
    hβ_mem ?_
  · exact HasDerivWithinAt.continuousOn (fun t ht => α.hasDerivWithinAt x hx t ht)
  · intro t ht
    exact (α.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact HasDerivWithinAt.continuousOn (fun t ht => β.hasDerivWithinAt x hx t ht)
  · intro t ht
    exact (β.hasDerivWithinAt x hx t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · rw [α.initial_eq x hx, β.initial_eq x hx]

end LocalFlowSolution

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
  LocalFlowSolution.eqOn_Ioo_of_lipschitzOnWith
    (α := α.toLocalFlowSolution) (β := β.toLocalFlowSolution)
    (x := x) hx ht₀ hf_lip hα_mem hβ_mem

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
  LocalFlowSolution.eqOn_Icc_of_lipschitzOnWith
    (α := α.toLocalFlowSolution) (β := β.toLocalFlowSolution)
    (x := x) hx ht₀ hf_lip hα_mem hβ_mem

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
    EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) := by
  refine ODE_solution_unique_of_mem_Ioo
    (v := fun (t : ℝ) (A : V →L[ℝ] V) => (Df t (α.flow (x, t))).comp A)
    (s := state) hlin_lip ht₀ ?_ ?_ ?_
  · intro t ht
    exact ⟨α.tangent_hasDerivAt_of_mem_Ioo hx ht, hα_mem t ht⟩
  · intro t ht
    have hβderiv := β.tangent_hasDerivAt_of_mem_Ioo hx ht
    rw [show β.flow (x, t) = α.flow (x, t) from (hflow_eq ht).symm] at hβderiv
    exact ⟨hβderiv, hβ_mem t ht⟩
  · rw [α.tangent_initial_eq x hx, β.tangent_initial_eq x hx]

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
  α.tangent_eqOn_Ioo_of_lipschitzOnWith β hx ht₀ hflow_eq
    (fun t ht =>
      ((lipschitzWith_leftComp (Df t (α.flow (x, t)))).weaken (hD_bound t ht)).lipschitzOnWith)
    hα_mem hβ_mem

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
      (Ioo tmin tmax) := by
  have hflow : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Ioo tmin tmax) :=
    α.toContinuousLocalFlowSolution.eqOn_Ioo_of_lipschitzOnWith
      β.toContinuousLocalFlowSolution hx ht₀ hf_lip hα_base_mem hβ_base_mem
  have htangent : EqOn (α.tangent x) (β.tangent x) (Ioo tmin tmax) :=
    α.tangent_eqOn_Ioo_of_opNorm_bound (β := β) (state := fun _ => Set.univ)
      hx ht₀ hflow hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact Prod.ext (hflow ht) (htangent ht)

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
    EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) := by
  refine ODE_solution_unique_of_mem_Icc
    (v := fun (t : ℝ) (A : V →L[ℝ] V) => (Df t (α.flow (x, t))).comp A)
    (s := state) hlin_lip ht₀ ?_ ?_ hα_mem ?_ ?_ hβ_mem ?_
  · exact HasDerivWithinAt.continuousOn
      (fun t ht => α.tangent_hasDerivWithinAt x hx t ht)
  · intro t ht
    exact α.tangent_hasDerivAt_of_mem_Ioo hx ht
  · exact HasDerivWithinAt.continuousOn
      (fun t ht => β.tangent_hasDerivWithinAt x hx t ht)
  · intro t ht
    have hβderiv := β.tangent_hasDerivAt_of_mem_Ioo hx ht
    rw [show β.flow (x, t) = α.flow (x, t) from (hflow_eq ht).symm] at hβderiv
    exact hβderiv
  · rw [α.tangent_initial_eq x hx, β.tangent_initial_eq x hx]

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
  α.tangent_eqOn_Icc_of_lipschitzOnWith β hx ht₀ hflow_eq
    (fun t ht =>
      ((lipschitzWith_leftComp (Df t (α.flow (x, t)))).weaken (hD_bound t ht)).lipschitzOnWith)
    hα_mem hβ_mem

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
      (Icc tmin tmax) := by
  have hflowIcc : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Icc tmin tmax) :=
    α.toContinuousLocalFlowSolution.eqOn_Icc_of_lipschitzOnWith
      β.toContinuousLocalFlowSolution hx ht₀ hf_lip hα_base_mem hβ_base_mem
  have hflowIoo : EqOn (fun t : ℝ => α.flow (x, t)) (fun t : ℝ => β.flow (x, t))
      (Ioo tmin tmax) := fun t ht => hflowIcc (Ioo_subset_Icc_self ht)
  have htangent : EqOn (α.tangent x) (β.tangent x) (Icc tmin tmax) :=
    α.tangent_eqOn_Icc_of_opNorm_bound (β := β) (state := fun _ => Set.univ)
      hx ht₀ hflowIoo hD_bound (by intro t ht; simp) (by intro t ht; simp)
  intro t ht
  exact Prod.ext (hflowIcc ht) (htangent ht)

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
