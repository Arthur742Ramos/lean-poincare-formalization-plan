/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Finite-coordinate matrices as genuine continuous bilinear forms

The finite Pi spaces use the sup norm. The adapter therefore has an explicit
dimension-squared norm factor; no basis-to-model isometry is assumed.
-/

noncomputable section

open scoped BigOperators

namespace PoincareCurvature.FiniteCoordinateBilinear

variable {d : ℕ}

/-- The actual finite bilinear contraction represented by a coordinate matrix. -/
def ofMatrix (A : Fin d → Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    A i j • (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)

theorem ofMatrix_apply (A : Fin d → Fin d → ℝ) (u v : Fin d → ℝ) :
    ofMatrix A u v = ∑ i : Fin d, ∑ j : Fin d, A i j * u i * v j := by
  simp only [ofMatrix, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  ext i
  congr 1
  ext j
  ring

theorem ofMatrix_add (A B : Fin d → Fin d → ℝ) :
    ofMatrix (A + B) = ofMatrix A + ofMatrix B := by
  ext u v
  simp [ofMatrix_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ofMatrix_sub (A B : Fin d → Fin d → ℝ) :
    ofMatrix (A - B) = ofMatrix A - ofMatrix B := by
  ext u v
  simp [ofMatrix_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ofMatrix_smul (c : ℝ) (A : Fin d → Fin d → ℝ) :
    ofMatrix (c • A) = c • ofMatrix A := by
  simp [ofMatrix, smul_smul, Finset.smul_sum, mul_comm]

theorem ofMatrix_coordinateVector (A : Fin d → Fin d → ℝ) (i j : Fin d) :
    ofMatrix A (Pi.single i 1) (Pi.single j 1) = A i j := by
  classical
  rw [ofMatrix_apply]
  simp [Pi.single_apply]

theorem norm_proj_le_one (i : Fin d) :
    ‖(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

/-- A uniform quantitative adapter bound, valid also in rank zero. -/
theorem norm_ofMatrix_le (A : Fin d → Fin d → ℝ) :
    ‖ofMatrix A‖ ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound₂ (ofMatrix A)
    (mul_nonneg (sq_nonneg _) (norm_nonneg A)) ?_
  intro u v
  rw [ofMatrix_apply]
  have hentry : ∀ i j, ‖A i j‖ ≤ ‖A‖ := fun i j =>
    (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
  have hterm : ∀ i j, ‖A i j * u i * v j‖ ≤ ‖A‖ * ‖u‖ * ‖v‖ := by
    intro i j
    rw [norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul (hentry i j) (norm_le_pi_norm u i)
        (norm_nonneg _) (norm_nonneg A))
      (norm_le_pi_norm v j) (norm_nonneg _)
      (mul_nonneg (norm_nonneg A) (norm_nonneg u))
  calc
    ‖∑ i : Fin d, ∑ j : Fin d, A i j * u i * v j‖ ≤
        ∑ i : Fin d, ‖∑ j : Fin d, A i j * u i * v j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ‖A i j * u i * v j‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ * ‖u‖ * ‖v‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (d : ℝ) ^ 2 * ‖A‖ * ‖u‖ * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Matrix-to-bilinear conversion is smooth at every finite differentiability order. -/
theorem contDiff_ofMatrix {r : WithTop ℕ∞} : ContDiff ℝ r (@ofMatrix d) := by
  classical
  letI : NormedSpace ℝ ((Fin d → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  letI : IsBoundedSMul ℝ ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ)
  unfold ofMatrix
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) i j).smul contDiff_const

end PoincareCurvature.FiniteCoordinateBilinear
