module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

/-!
# Derivative of a finite matrix inverse

The inverse-metric contribution to curvature variation rests on the identity
`(A⁻¹)' = -A⁻¹ A' A⁻¹`.  This file proves that identity for genuine finite
matrix curves by differentiating their matrix inverse relation entry by
entry.  No derivative formula is assumed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PoincareCurvature

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Derivative of a finite matrix product from entrywise derivatives. -/
theorem hasDerivAt_matrix_mul_entry
    {A B : ℝ → Matrix ι ι ℝ} {Adot Bdot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (Bdot i j) t)
    (i j : ι) :
    HasDerivAt (fun s => (A s * B s) i j)
      ((Adot * B t + A t * Bdot) i j) t := by
  have hsum := HasDerivAt.sum (u := Finset.univ) fun k (_hk : k ∈ Finset.univ) =>
    (hA i k).mul (hB k j)
  convert! hsum using 1
  funext s
  simp [Matrix.mul_apply]
  simp [Matrix.mul_apply, Finset.sum_add_distrib]

/-- If two differentiable finite matrix curves are mutual inverses, the
derivative of the inverse curve is `-B A' B`. -/
theorem matrix_inverse_derivative
    {A B : ℝ → Matrix ι ι ℝ} {Adot Bdot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (Bdot i j) t)
    (hAB : ∀ s, A s * B s = 1)
    (hBA : B t * A t = 1) :
    Bdot = -(B t * Adot * B t) := by
  have hvariation : Adot * B t + A t * Bdot = 0 := by
    ext i j
    have hprod := hasDerivAt_matrix_mul_entry hA hB i j
    have hconst : HasDerivAt (fun _ : ℝ => (1 : Matrix ι ι ℝ) i j) 0 t :=
      hasDerivAt_const t _
    have heq : (fun s => (A s * B s) i j) =
        (fun _ : ℝ => (1 : Matrix ι ι ℝ) i j) := by
      funext s
      rw [hAB s]
    rw [heq] at hprod
    have hzero := hprod.unique hconst
    simpa using hzero
  have hsolve : A t * Bdot = -(Adot * B t) :=
    eq_neg_of_add_eq_zero_right hvariation
  calc
    Bdot = (B t * A t) * Bdot := by rw [hBA, one_mul]
    _ = B t * (A t * Bdot) := by rw [mul_assoc]
    _ = B t * (-(Adot * B t)) := by rw [hsolve]
    _ = -(B t * Adot * B t) := by simp [mul_assoc]

/-- Specialization to the nonsingular inverse supplied by Mathlib. -/
theorem nonsing_inv_derivative
    {A : ℝ → Matrix ι ι ℝ} {Adot Bdot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hInv : ∀ i j, HasDerivAt (fun s => (A s)⁻¹ i j) (Bdot i j) t)
    (hdet : ∀ s, (A s).det ≠ 0) :
    Bdot = -((A t)⁻¹ * Adot * (A t)⁻¹) := by
  apply matrix_inverse_derivative hA hInv
  · intro s
    exact Matrix.mul_nonsing_inv (A s) (isUnit_iff_ne_zero.mpr (hdet s))
  · exact Matrix.nonsing_inv_mul (A t) (isUnit_iff_ne_zero.mpr (hdet t))

end PoincareCurvature
