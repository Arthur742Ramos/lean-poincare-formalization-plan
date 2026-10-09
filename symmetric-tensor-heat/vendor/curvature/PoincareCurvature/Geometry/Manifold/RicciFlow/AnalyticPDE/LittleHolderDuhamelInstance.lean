import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderJointContinuity

/-!
# DuhamelData instance on the little-Hölder space (Point 4 PDE milestone)

This module assembles the full `DuhamelData` instance for the little-Hölder
heat propagator, validating the mild-solution pipeline end-to-end.

## Status

The propagator data (`hSbound` with `M = 1`, `hSjoint`) is genuine, proved in
`LittleHolderJointContinuity.lean`.  The nonlinearity `N` is currently a
**clearly-marked placeholder** (the zero map): the genuine Ricci–DeTurck
nonlinearity with its local Lipschitz estimate in the little-Hölder norm is
the next milestone.  This file validates that the `DuhamelData` assembly and
the Banach fixed-point application go through; it does **not** claim PDE
existence for the genuine nonlinearity.
-/

namespace RicciFlow
namespace AnalyticPDE
namespace LittleHolder

open Filter Topology Set
open scoped NNReal Interval

variable {n : ℕ} {α : ℝ}

/-- The little-Hölder propagator satisfies the `DuhamelData.hSbound` bound
with `M = 1` (as `ℝ≥0`). -/
theorem hSbound_one {T : ℝ} (_hT : 0 < T) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖littleHolderPropagator (n := n) (α := α) t‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  intro t ht
  have h1 : ((1 : ℝ≥0) : ℝ) = 1 := by norm_num
  rw [h1]
  by_cases htpos : 0 < t
  · rw [littleHolderPropagator_of_pos (n := n) (α := α) htpos]
    exact norm_littleHolderPropagatorCLM_le (n := n) (α := α) htpos
  · rw [littleHolderPropagator_of_nonpos (n := n) (α := α) htpos]
    exact ContinuousLinearMap.norm_id_le

/-- **PLACEHOLDER** nonlinearity: the zero map.
The genuine Ricci–DeTurck nonlinearity with its little-Hölder local Lipschitz
estimate is a future milestone.  This placeholder validates the pipeline. -/
noncomputable def placeholderN : LittleHolder n α → LittleHolder n α :=
  fun _ => 0

/-- The `DuhamelData` instance for the little-Hölder heat propagator with
placeholder nonlinearity.  Genuine propagator bounds; placeholder `N`. -/
noncomputable def littleHolderDuhamelData (T : ℝ) (hT : 0 < T)
    (u₀ : LittleHolder n α) : DuhamelData (X := LittleHolder n α) where
  T := T
  hT := hT
  S := fun t => littleHolderPropagator (n := n) (α := α) t
  M := 1
  hSbound := hSbound_one (n := n) (α := α) hT
  hSjoint := littleHolderPropagator_hSjoint (n := n) (α := α) hT
  N := placeholderN (n := n) (α := α)
  L := 0
  hN := by
    -- The goal has the `PseudoEMetricSpace` instance from the
    -- `NormedAddCommGroup` hierarchy (as `DuhamelData` requires).
    -- Prove directly with explicit instances to avoid the subtype mismatch.
    intro x y
    have h0 : placeholderN (n := n) (α := α) x = 0 := rfl
    have h0' : placeholderN (n := n) (α := α) y = 0 := rfl
    rw [h0, h0']
    -- Goal: `edist 0 0 ≤ ↑0 * edist x y` (hierarchy instance).
    have hedist : @edist (LittleHolder n α)
        (@PseudoEMetricSpace.toEDist _
          MetricSpace.toEMetricSpace.toPseudoEMetricSpace)
        (0 : LittleHolder n α) 0 = 0 :=
      @edist_self _ MetricSpace.toEMetricSpace.toPseudoEMetricSpace _
    rw [hedist]
    -- Goal: `0 ≤ ↑0 * edist x y`.  `0` is the bottom element of `ℝ≥0∞`.
    exact bot_le
  u₀ := u₀

/-- With the placeholder nonlinearity (`L = 0`), the contraction condition
`M * L * T < 1` holds trivially, giving a unique mild solution. -/
theorem exists_unique_mild_solution_placeholder (T : ℝ) (hT : 0 < T)
    (u₀ : LittleHolder n α) :
    ∃! u : C(Icc (0 : ℝ) T, LittleHolder n α),
      (littleHolderDuhamelData (n := n) (α := α) T hT u₀).duhamelMap u = u := by
  have hcon : ((((1 : ℝ≥0) : ℝ) * ((0 : ℝ≥0) : ℝ) * T)) < 1 := by norm_num
  have hcon' : (((littleHolderDuhamelData (n := n) (α := α) T hT u₀).M : ℝ) *
    ((littleHolderDuhamelData (n := n) (α := α) T hT u₀).L : ℝ) *
    (littleHolderDuhamelData (n := n) (α := α) T hT u₀).T) < 1 := hcon
  exact DuhamelData.exists_unique_mild_solution
    (D := littleHolderDuhamelData (n := n) (α := α) T hT u₀) hcon'

end LittleHolder
end AnalyticPDE
end RicciFlow
