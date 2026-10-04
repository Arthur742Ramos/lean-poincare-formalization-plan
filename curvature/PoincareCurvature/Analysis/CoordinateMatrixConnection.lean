/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixJet
import PoincareCurvature.Analysis.LocalMatrixInverseDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Actual derivatives of coordinate inverse and Christoffel expressions

The inverse is Mathlib's explicitly typed nonsingular matrix inverse. Its
regularity follows from the actual determinant/adjugate maps, and its derivative
formula follows by restricting the actual field to coordinate lines and applying
the localized inverse-curve theorem. The Christoffel derivative then follows by
ordinary product and finite-sum differentiation of the actual C² field slots.
These are real coordinate calculus identities, without a manifold identification.
-/

noncomputable section

open Matrix Filter
open scoped Topology

namespace PoincareCurvature.CoordinateMatrixJet

variable {n d : ℕ}

/-- The actual nonsingular matrix inverse, explicitly typed before inversion. -/
def inverse (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin n → ℝ) (i k : Fin d) : ℝ :=
  ((show Matrix (Fin d) (Fin d) ℝ from g x)⁻¹) i k

/-- The genuine straight coordinate line through x. -/
def coordinateLine (x : Fin n → ℝ) (m : Fin n) (t : ℝ) : Fin n → ℝ :=
  x + t • coordinateVector m

@[simp] theorem coordinateLine_zero (x : Fin n → ℝ) (m : Fin n) :
    coordinateLine x m 0 = x := by simp [coordinateLine]

/-- Actual derivative of the straight coordinate line. -/
theorem hasDerivAt_coordinateLine (x : Fin n → ℝ) (m : Fin n) :
    HasDerivAt (coordinateLine x m) (coordinateVector m) 0 := by
  change HasDerivAt (fun t : ℝ => x + t • coordinateVector m) (coordinateVector m) 0
  have h := (hasDerivAt_const (0 : ℝ) x).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector m))
  change HasDerivAt (fun t : ℝ => x + t • coordinateVector m)
    (0 + (1 : ℝ) • coordinateVector m) 0 at h
  simpa only [zero_add, one_smul] using h

/-- Restrict a genuine scalar Fréchet derivative to a coordinate line. -/
theorem hasDerivAt_comp_coordinateLine {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} {D : (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f D x) (m : Fin n) :
    HasDerivAt (fun t => f (coordinateLine x m t)) (D (coordinateVector m)) 0 := by
  simpa [Function.comp_def] using
    hf.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x m) (coordinateLine_zero x m).symm

variable {g : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin n → ℝ)} {x : Fin n → ℝ}

/-- Inverse regularity is derived from determinant and adjugate regularity,
with invertibility only at the selected point. -/
theorem differentiableAt_inverse_entry
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i k : Fin d) :
    DifferentiableAt ℝ (fun y => inverse g y i k) x := by
  have hd : DifferentiableAt ℝ g x :=
    (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdetDiff : DifferentiableAt ℝ
      (fun y => (show Matrix (Fin d) (Fin d) ℝ from g y).det) x :=
    ((MatrixSmoothness.contDiff_det (ι := Fin d) (n := 1)).differentiable
      (by norm_num) (g x)).comp x hd
  have hadjDiff : DifferentiableAt ℝ
      (fun y => (show Fin d → Fin d → ℝ from
        Matrix.adjugate (show Matrix (Fin d) (Fin d) ℝ from g y))) x :=
    ((MatrixSmoothness.contDiff_adjugate (ι := Fin d) (n := 1)).differentiable
      (by norm_num) (g x)).comp x hd
  have hadjEntry := differentiableAt_pi.mp (differentiableAt_pi.mp hadjDiff i) k
  have hentry := (hdetDiff.inv hdet).mul hadjEntry
  change DifferentiableAt ℝ (fun y =>
    ((show Matrix (Fin d) (Fin d) ℝ from g y).det)⁻¹ *
      Matrix.adjugate (show Matrix (Fin d) (Fin d) ℝ from g y) i k) x at hentry
  have heq : (fun y => inverse g y i k) =
      (fun y => ((show Matrix (Fin d) (Fin d) ℝ from g y).det)⁻¹ *
        Matrix.adjugate (show Matrix (Fin d) (Fin d) ℝ from g y) i k) := by
    funext y
    unfold inverse
    simpa only [Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun C : Matrix (Fin d) (Fin d) ℝ => C i k)
        (Matrix.inv_def (show Matrix (Fin d) (Fin d) ℝ from g y))
  rw [heq]
  exact hentry

/-- Coordinate inverse derivative, computed using the actual first derivatives. -/
def inverseFirst (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin n → ℝ) (m : Fin n) (i k : Fin d) : ℝ :=
  ((-((show Matrix (Fin d) (Fin d) ℝ from g x)⁻¹ *
    (show Matrix (Fin d) (Fin d) ℝ from first g x m) *
    (show Matrix (Fin d) (Fin d) ℝ from g x)⁻¹) : Matrix (Fin d) (Fin d) ℝ) i k)

/-- The derivative formula is produced from the real field, not assumed as a
certificate: restrict to a coordinate line and use uniqueness of derivatives. -/
theorem fderiv_inverse_apply
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (m : Fin n) (i k : Fin d) :
    fderiv ℝ (fun y => inverse g y i k) x (coordinateVector m) =
      inverseFirst g x m i k := by
  let A : ℝ → Matrix (Fin d) (Fin d) ℝ :=
    fun t => (show Matrix (Fin d) (Fin d) ℝ from g (coordinateLine x m t))
  have hA : ∀ a b : Fin d,
      HasDerivAt (fun t => A t a b) (first g x m a b) 0 := by
    intro a b
    exact hasDerivAt_comp_coordinateLine (component_hasFDerivAt hU hg hx a b) m
  have hlocal := hasDerivAt_nonsing_inv_entry_of_det_ne_zero
    hA (by simpa only [A, coordinateLine_zero] using hdet) i k
  have hcomputed : HasDerivAt (fun t => inverse g (coordinateLine x m t) i k)
      (inverseFirst g x m i k) 0 := by
    simpa only [A, coordinateLine_zero, inverse, inverseFirst] using hlocal
  exact (hasDerivAt_comp_coordinateLine
    (differentiableAt_inverse_entry hU hg hx hdet i k).hasFDerivAt m).unique hcomputed

/-- Explicit coordinate double-sum inverse derivative. -/
theorem inverseFirst_eq_sum (m : Fin n) (i k : Fin d) :
    inverseFirst g x m i k =
      -∑ a : Fin d, ∑ b : Fin d, inverse g x i a * first g x m a b * inverse g x b k := by
  change -(∑ b : Fin d, (∑ a : Fin d, inverse g x i a * first g x m a b) *
    inverse g x b k) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The actual coordinate Christoffel expression of the produced field. -/
def christoffel (g : (Fin d → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin d → ℝ) (k i j : Fin d) : ℝ :=
  (1/2) * ∑ l : Fin d, inverse g x k l *
    (first g x i j l + first g x j i l - first g x l i j)

/-- The product-rule expression for the actual coordinate Christoffel derivative. -/
def christoffelFirst (g : (Fin d → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin d → ℝ) (m k i j : Fin d) : ℝ :=
  (1/2) * ∑ l : Fin d,
    (inverseFirst g x m k l * (first g x i j l + first g x j i l - first g x l i j) +
      inverse g x k l * (second g x m i j l + second g x m j i l - second g x m l i j))

variable {g : (Fin d → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- Genuine differentiability of the actual coordinate Christoffel expression. -/
theorem differentiableAt_christoffel
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (k i j : Fin d) :
    DifferentiableAt ℝ (fun y => christoffel g y k i j) x := by
  unfold christoffel
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro l _
  exact (differentiableAt_inverse_entry hU hg hx hdet k l).mul
    (((first_component_hasFDerivAt hU hg hx i j l).differentiableAt.add
      (first_component_hasFDerivAt hU hg hx j i l).differentiableAt).sub
      (first_component_hasFDerivAt hU hg hx l i j).differentiableAt)

/-- Actual Fréchet derivative of the coordinate Christoffel expression. -/
theorem fderiv_christoffel_apply
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (m k i j : Fin d) :
    fderiv ℝ (fun y => christoffel g y k i j) x (coordinateVector m) =
      christoffelFirst g x m k i j := by
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (differentiableAt_inverse_entry hU hg hx hdet k l).hasFDerivAt.mul
      (((first_component_hasFDerivAt hU hg hx i j l).add
        (first_component_hasFDerivAt hU hg hx j i l)).sub
        (first_component_hasFDerivAt hU hg hx l i j))
  have h := hsum.const_mul (1/2 : ℝ)
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply] at h
  change fderiv ℝ (fun y => (1/2 : ℝ) * ∑ l : Fin d, inverse g y k l *
    (first g y i j l + first g y j i l - first g y l i j)) x (coordinateVector m) = _
  rw [h.fderiv]
  simp [christoffelFirst, second, fderiv_inverse_apply hU hg hx hdet,
    mul_comm, add_comm]

end PoincareCurvature.CoordinateMatrixJet
