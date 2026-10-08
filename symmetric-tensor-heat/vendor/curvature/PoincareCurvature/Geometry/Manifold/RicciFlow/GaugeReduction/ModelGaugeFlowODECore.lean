module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
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


/-! ## Picard-Lindelöf constructors (moved from `ModelGaugeFlowODE`) -/

-- The following definitions were moved from `ModelGaugeFlowODE.lean` to break
-- the import cycle for Point 4. They are pure Banach-model ODE results with
-- no dependency on `Diffeomorph3FlowExistence`.

theorem hasDerivWithinAt_fst_of_variationalVectorField
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {curve : ℝ → V × (V →L[ℝ] V)} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt curve (variationalVectorField f Df t (curve t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (curve τ).1) (f t (curve t).1) s t := by
  have hf := h.hasFDerivWithinAt.fst
  simpa [variationalVectorField] using hf.hasDerivWithinAt

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

theorem flow_continuousWithinAt
    (α : LocalFlowSolution f t₀ x₀ r) {x : V} (hx : x ∈ closedBall x₀ r)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    ContinuousWithinAt (α.flow x) (Icc tmin tmax) t :=
  (α.hasDerivWithinAt x hx t ht).continuousWithinAt

end LocalFlowSolution

namespace LipschitzLocalFlowSolution

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V}
  {r : ℝ≥0}

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

end LipschitzLocalFlowSolution

namespace IsPicardLindelof

variable [CompleteSpace V]
  {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
  {x₀ : V} {a r L K : ℝ≥0}

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

def toContinuousLocalFlowSolution
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ContinuousLocalFlowSolution f t₀ x₀ r :=
  (toLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution

end IsPicardLindelof

namespace VariationalLocalFlowSolution

variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
  {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}

theorem dist_comp_right_le (D₁ D₂ A : V →L[ℝ] V) :
    dist (D₁.comp A) (D₂.comp A) ≤ dist D₁ D₂ * ‖A‖ := by
  have h := (D₁ - D₂).opNorm_comp_le A
  simpa [dist_eq_norm, ContinuousLinearMap.sub_comp] using h

theorem dist_comp_left_le (D A B : V →L[ℝ] V) :
    dist (D.comp A) (D.comp B) ≤ ‖D‖ * dist A B := by
  have h := D.opNorm_comp_le (A - B)
  simpa [dist_eq_norm, ContinuousLinearMap.comp_sub] using h

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
  exact
    lipschitzOnWith_variationalVectorField
      (f_t := f t) (Df_t := Df t) (tangentState := tangentState)
      hf_lip hDf_lip hA_bound hD_bound

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

end VariationalLocalFlowSolution

end ModelGaugeFlowODE

end RicciFlow
