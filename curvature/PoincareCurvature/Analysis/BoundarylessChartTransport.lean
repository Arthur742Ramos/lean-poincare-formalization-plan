/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Local ordinary-derivative transport on a boundaryless manifold

Only the manifold is required to be boundaryless. The model range need not be
the whole vector space: each preferred chart target lies in its interior.
No chart or local transport certificate is supplied as an additional premise.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareCurvature.BoundarylessChartTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- Every preferred extended-chart target is open under manifold boundarylessness. -/
theorem isOpen_extChartAt_target (p : M) : IsOpen (extChartAt I p).target := by
  apply isOpen_iff_mem_nhds.2
  intro z hz
  have hx := (extChartAt I p).map_target hz
  have hpoint := (I.isInteriorPoint_iff_of_mem_atlas
    (n := ∞) (by simp) (chart_mem_atlas H p)
    (by simpa only [extChartAt_source] using hx)).1
      (BoundarylessManifold.isInteriorPoint (I := I) (x := (extChartAt I p).symm z))
  change extChartAt I p ((extChartAt I p).symm z) ∈ interior (extChartAt I p).target at hpoint
  rw [(extChartAt I p).right_inv hz] at hpoint
  exact mem_interior_iff_mem_nhds.1 hpoint

/-- The preferred chart target is contained in the interior of the model range. -/
theorem extChartAt_target_subset_interior_range (p : M) :
    (extChartAt I p).target ⊆ interior (range I) := by
  have h := (chartAt H p).interior_extend_target_subset_interior_range (I := I)
  change interior (extChartAt I p).target ⊆ interior (range I) at h
  rwa [(isOpen_extChartAt_target (I := I) p).interior_eq] at h

/-- At a chart-target point, the actual inverse-chart derivative within the
model range equals its ordinary manifold derivative. -/
theorem mfderivWithin_extChartAt_symm_eq_mfderiv (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) :
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z =
      mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z := by
  exact mfderivWithin_of_mem_nhds
    (mem_interior_iff_mem_nhds.1 (extChartAt_target_subset_interior_range (I := I) p hz))

/-- Pullback of any actual dependent tangent field through the inverse chart
agrees with ordinary pullback at every chart-target point. -/
theorem mpullbackWithin_extChartAt_symm_eq_mpullback (p : M)
    (V : ∀ x : M, TangentSpace I x) {z : E}
    (hz : z ∈ (extChartAt I p).target) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm V (range I) z =
      VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm V z := by
  unfold VectorField.mpullbackWithin VectorField.mpullback
  rw [mfderivWithin_extChartAt_symm_eq_mfderiv (I := I) p hz]

end PoincareCurvature.BoundarylessChartTransport
