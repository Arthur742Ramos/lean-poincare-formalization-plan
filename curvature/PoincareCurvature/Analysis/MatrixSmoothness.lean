/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smoothness of the matrix determinant, adjugate, and nonsingular inverse

This module records the *base-polymorphic, arbitrary-order* smoothness of the matrix
determinant, adjugate, and (nonsingular) inverse, viewed as maps on the finite-dimensional
real normed space `ι → ι → ℝ` of matrix entries.

The determinant and adjugate are polynomial maps of the entries, hence `ContDiff ℝ n` for every
order `n`; the inverse is `A⁻¹ = (det A)⁻¹ • adjugate A`, so it is `ContMDiffOn` on the locus where
the determinant is nonzero.

## Motivation

The spatial Riemannian *raising* machinery reduces raising a co-vector to inverting the local-frame
Gram matrix, and its existing smoothness support
(`CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv`) is proved only for a fixed base
manifold `M` and at the single order `2`.  Running that argument jointly over the *space-time* base
`ℝ × M` — the joint `(t, x)` smoothness of the Ricci–DeTurck gauge field for a genuinely
time-dependent metric — requires exactly these facts for an *arbitrary* base manifold and at
*arbitrary* order.  This module isolates that field-independent linear-algebra core so it can be
reused verbatim over any base.
-/

open scoped Manifold
open Matrix

namespace PoincareCurvature.MatrixSmoothness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : WithTop ℕ∞}

/-- The determinant, as a function of the matrix entries, is `ContDiff ℝ n` for every order `n`
(it is a polynomial in the entries). -/
theorem contDiff_det :
    ContDiff ℝ n (fun A : ι → ι → ℝ => (show Matrix ι ι ℝ from A).det) := by
  classical
  let f : (ι → ι → ℝ) → ℝ :=
    fun A => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i
  have hf : ContDiff ℝ n f := by
    rw [contDiff_iff_contDiffAt]
    intro A
    refine ContDiffAt.sum ?_
    intro σ _
    refine (contDiffAt_const : ContDiffAt ℝ n
      (fun _ : ι → ι → ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ)) A).mul ?_
    refine contDiffAt_prod ?_
    intro i _
    simpa using
      (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := n) (i := σ i) (j := i)).contDiffAt
  have hEq : f = fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A) := by
    funext A
    symm
    simpa using (Matrix.det_apply' (show Matrix ι ι ℝ from A))
  simpa [hEq] using hf

/-- Updating a single row of a matrix with a fixed vector is `ContDiff ℝ n` in the entries. -/
theorem contDiff_updateRow (i j : ι) :
    ContDiff ℝ n
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from
          Matrix.updateRow (show Matrix ι ι ℝ from A) j (Pi.single i (1 : ℝ)))) := by
  classical
  rw [contDiff_pi]
  intro k
  by_cases hk : k = j
  · subst hk
    simpa using
      (contDiff_const : ContDiff ℝ n (fun _ : ι → ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simpa [Matrix.updateRow_apply, hk] using
      (contDiff_apply (𝕜 := ℝ) (E := ι → ℝ) (n := n) (i := k))

/-- The adjugate, as a function of the matrix entries, is `ContDiff ℝ n` for every order `n`
(each entry is a signed minor, hence a polynomial in the entries). -/
theorem contDiff_adjugate :
    ContDiff ℝ n
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A))) := by
  classical
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  simpa [Function.comp, Matrix.adjugate_apply] using
    (contDiff_det (ι := ι) (n := n)).comp (contDiff_updateRow (ι := ι) (n := n) i j)

section Manifold

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The determinant of a `ContMDiffOn` family of matrices is `ContMDiffOn` (as a scalar function). -/
theorem contMDiffOn_matrixDet {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => (show Matrix ι ι ℝ from A x).det) u := by
  intro x hx
  exact (contDiff_det (ι := ι) (n := n)).comp_contMDiffWithinAt (hA x hx)

/-- The adjugate of a `ContMDiffOn` family of matrices is `ContMDiffOn`. -/
theorem contMDiffOn_matrixAdjugate {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A x))) u := by
  intro x hx
  exact (contDiff_adjugate (ι := ι) (n := n)).comp_contMDiffWithinAt (hA x hx)

/-- The reciprocal determinant of a `ContMDiffOn` family of matrices is `ContMDiffOn` on the locus
where the determinant is nonzero. -/
theorem contMDiffOn_matrixDetInv {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hdet : ∀ x ∈ u, (show Matrix ι ι ℝ from A x).det ≠ 0) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => ((show Matrix ι ι ℝ from A x).det)⁻¹) u :=
  (contMDiffOn_matrixDet (J := J) (n := n) hA).inv₀ hdet

/-- **Smoothness of the nonsingular matrix inverse.**  If `A : N → (ι → ι → ℝ)` is a `ContMDiffOn`
family of matrices over an arbitrary base and its determinant is nonzero throughout, then the
entrywise inverse `x ↦ (A x)⁻¹` is `ContMDiffOn` at the same order.

This is the base-polymorphic, arbitrary-order generalisation of the spatial, order-`2`
`CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv`, and is the linear-algebra tool
underlying joint space-time Riemannian raising. -/
theorem contMDiffOn_matrixInv {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hdet : ∀ x ∈ u, (show Matrix ι ι ℝ from A x).det ≠ 0) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from ((show Matrix ι ι ℝ from A x)⁻¹ : Matrix ι ι ℝ))) u := by
  simpa [Matrix.inv_def, Ring.inverse_eq_inv] using
    (contMDiffOn_matrixDetInv (J := J) (n := n) hA hdet).smul
      (contMDiffOn_matrixAdjugate (J := J) (n := n) hA)

end Manifold

end PoincareCurvature.MatrixSmoothness
