/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixOperator

/-!
# Lower Christoffel-slot symmetry and the ordinary curvature trace

The two lower connection slots are symmetric because the actual metric
components are symmetric on an open domain. Their derivatives are compared
by differentiating a genuine neighborhood equality, not a point equality.
The trace formula keeps the curvature order R(e_k,e_j)e_i explicit. Its
identification with intrinsic Ricci curvature is a separate geometric result.
-/

noncomputable section

open Filter Matrix
open scoped Topology BigOperators

namespace PoincareCurvature.CoordinateMatrixJet

variable {d : ℕ} {g : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- Lower-slot symmetry of the actual Christoffel expression on an open
metric-symmetric domain; no connection symmetry is assumed. -/
theorem christoffel_lower_symm (hU : IsOpen U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (k i j : Fin d) : christoffel g x k i j = christoffel g x k j i := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [first_tensor_symm hU hx hsymm l i j]
  ring

/-- Symmetry holds on an actual neighborhood, hence can be differentiated. -/
theorem christoffel_lower_eventuallyEq (hU : IsOpen U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (k i j : Fin d) :
    (fun y => christoffel g y k i j) =ᶠ[nhds x]
      (fun y => christoffel g y k j i) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact christoffel_lower_symm hU hy hsymm k i j

/-- Actual Christoffel derivatives inherit lower-slot symmetry from the
neighborhood equality and the C² metric derivative formula. -/
theorem christoffelFirst_lower_symm (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (m k i j : Fin d) :
    christoffelFirst g x m k i j = christoffelFirst g x m k j i := by
  rw [← fderiv_christoffel_apply hU hg hx hdet m k i j,
    ← fderiv_christoffel_apply hU hg hx hdet m k j i,
    (christoffel_lower_eventuallyEq hU hx hsymm k i j).fderiv_eq]

/-- The coordinate Ricci readout is the ordinary unweighted diagonal trace
of R(e_k,e_j)e_i. Intrinsic Ricci-slot symmetry is not used here. -/
theorem coordinateRicci_eq_christoffel_curvature_trace
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (i j : Fin d) :
    coordinateRicci g x i j = ∑ k : Fin d,
      (christoffelFirst g x k k j i - christoffelFirst g x j k k i +
        ∑ q : Fin d,
          (christoffel g x k k q * christoffel g x q j i -
            christoffel g x k j q * christoffel g x q k i)) := by
  rw [coordinateRicci, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_christoffel_apply hU hg hx hdet,
      fderiv_christoffel_apply hU hg hx hdet,
      christoffelFirst_lower_symm hU hg hx hdet hsymm k k i j,
      christoffelFirst_lower_symm hU hg hx hdet hsymm j k i k]
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    rw [christoffel_lower_symm hU hx hsymm q i j,
      christoffel_lower_symm hU hx hsymm q i k]

end PoincareCurvature.CoordinateMatrixJet
