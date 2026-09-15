import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PoincareCurvature.Analysis.MatrixSmoothness
import Mathlib.Tactic

/-!
# Derivative of a finite matrix inverse

The inverse-metric contribution to curvature variation rests on the identity
`(A⁻¹)' = -A⁻¹ A' A⁻¹`.  This file proves that identity for genuine finite
matrix curves by differentiating their matrix inverse relation entry by
entry.  No derivative formula is assumed.
-/

noncomputable section

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

/-- A nonsingular inverse matrix curve is differentiable whenever the original
matrix curve is differentiable entrywise.  This removes inverse regularity as
an independent hypothesis from metric-contraction variation formulas. -/
theorem differentiableAt_nonsing_inv_entry
    {A : ℝ → Matrix ι ι ℝ} {Adot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hdet : (A t).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun s => (A s)⁻¹ i j) t := by
  have hAmatrix : DifferentiableAt ℝ A t := by
    change DifferentiableAt ℝ (fun s => fun k l => A s k l) t
    exact differentiableAt_pi'' fun k => differentiableAt_pi'' fun l =>
      (hA k l).differentiableAt
  have hdetDiff : DifferentiableAt ℝ (fun s => (A s).det) t :=
    ((MatrixSmoothness.contDiff_det (ι := ι) (n := 1)).differentiable (by norm_num) (A t)).comp
      t hAmatrix
  have hadjDiff : DifferentiableAt ℝ (fun s => Matrix.adjugate (A s)) t :=
    ((MatrixSmoothness.contDiff_adjugate (ι := ι) (n := 1)).differentiable (by norm_num)
      (A t)).comp t hAmatrix
  have hadjEntry : DifferentiableAt ℝ (fun s => Matrix.adjugate (A s) i j) t :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hadjDiff i) j
  have hentry := (hdetDiff.inv hdet).mul hadjEntry
  change DifferentiableAt ℝ
    (fun s => (A s).det⁻¹ * Matrix.adjugate (A s) i j) t at hentry
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Pi.inv_apply, Pi.mul_apply,
    Matrix.smul_apply, smul_eq_mul] using hentry

/-- Entrywise derivative formula for a nonsingular inverse matrix curve,
with inverse differentiability derived from that of the original curve. -/
theorem hasDerivAt_nonsing_inv_entry
    {A : ℝ → Matrix ι ι ℝ} {Adot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hdet : ∀ s, (A s).det ≠ 0) (i j : ι) :
    HasDerivAt (fun s => (A s)⁻¹ i j)
      ((-((A t)⁻¹ * Adot * (A t)⁻¹) : Matrix ι ι ℝ) i j) t := by
  let Bdot : Matrix ι ι ℝ := fun k l => deriv (fun s => (A s)⁻¹ k l) t
  have hInv : ∀ k l, HasDerivAt (fun s => (A s)⁻¹ k l) (Bdot k l) t := by
    intro k l
    exact (differentiableAt_nonsing_inv_entry hA (hdet t) k l).hasDerivAt
  have hBdot : Bdot = -((A t)⁻¹ * Adot * (A t)⁻¹) :=
    nonsing_inv_derivative hA hInv hdet
  simpa only [hBdot] using hInv i j

/-- Double entrywise contraction of two finite matrices. -/
def matrixContraction (A S : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * S i j

omit [DecidableEq ι] in
/-- Product rule for a double finite matrix contraction. -/
theorem hasDerivAt_matrixContraction
    {A S : ℝ → Matrix ι ι ℝ} {Adot Sdot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hS : ∀ i j, HasDerivAt (fun s => S s i j) (Sdot i j) t) :
    HasDerivAt (fun s => matrixContraction (A s) (S s))
      (matrixContraction Adot (S t) + matrixContraction (A t) Sdot) t := by
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i (_hi : i ∈ Finset.univ) =>
    HasDerivAt.sum (u := Finset.univ) fun j (_hj : j ∈ Finset.univ) =>
      (hA i j).mul (hS i j)
  convert! hsum using 1
  · funext s
    simp [matrixContraction]
  · simp [matrixContraction, Finset.sum_add_distrib]

/-- Derivative of the contraction `tr(A⁻¹ S)` along differentiable finite
matrix curves.  The inverse derivative is eliminated in favor of the metric
velocity `Adot`. -/
theorem hasDerivAt_nonsing_inv_matrixContraction
    {A S : ℝ → Matrix ι ι ℝ} {Adot Sdot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hS : ∀ i j, HasDerivAt (fun s => S s i j) (Sdot i j) t)
    (hdet : ∀ s, (A s).det ≠ 0) :
    HasDerivAt
      (fun s => matrixContraction (A s)⁻¹ (S s))
      (matrixContraction (-((A t)⁻¹ * Adot * (A t)⁻¹)) (S t) +
        matrixContraction (A t)⁻¹ Sdot) t := by
  let Bdot : Matrix ι ι ℝ := fun i j => deriv (fun s => (A s)⁻¹ i j) t
  have hInv : ∀ i j, HasDerivAt (fun s => (A s)⁻¹ i j) (Bdot i j) t := by
    intro i j
    exact (differentiableAt_nonsing_inv_entry hA (hdet t) i j).hasDerivAt
  have hBdot : Bdot = -((A t)⁻¹ * Adot * (A t)⁻¹) :=
    nonsing_inv_derivative hA hInv hdet
  have hcontract := hasDerivAt_matrixContraction hInv hS
  simpa only [hBdot] using hcontract

end PoincareCurvature
