import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatEuclidean
import PoincareCurvature.Analysis.FiniteCoordinateBilinear

/-!
# Gaussian matrix heat preserves coercivity

SOURCE CANDIDATE, UNCOMPILED. This is the exact low-level proof slice of the
reviewed initial-metric heat candidate. Bounded-continuous matrix entries
supply integrability, so scalar heat comparison preserves the given quadratic
lower bound at every positive time. No nonlinear interval equation, manifold
realization, initial-metric corollary, uniqueness or Point 4 closure is claimed.
-/

noncomputable section
open scoped BigOperators
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

private def quadraticHeatInput {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (v : Fin d → ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, (v i * v j) • F i j

private theorem quadraticHeatInput_apply {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (v : Fin d → ℝ) (y : Fin n → ℝ) :
    quadraticHeatInput F v y = ofMatrix (fun i j => F i j y) v v := by
  classical
  change BoundedContinuousFunction.evalCLM ℝ y
    (∑ i : Fin d, ∑ j : Fin d, (v i * v j) • F i j) = _
  simp only [map_sum, map_smul, BoundedContinuousFunction.evalCLM_apply,
    smul_eq_mul, ofMatrix_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem heatSemigroupND_quadraticHeatInput {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin d → ℝ) :
    heatSemigroupND t (quadraticHeatInput F v) x =
      ofMatrix (matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v := by
  classical
  calc
    heatSemigroupND t (quadraticHeatInput F v) x =
        BoundedContinuousFunction.evalCLM ℝ x
          (heatSemigroupNDclm ht (quadraticHeatInput F v)) := rfl
    _ = ∑ i : Fin d, ∑ j : Fin d,
        (v i * v j) * heatSemigroupND t (F i j) x := by
      simp only [quadraticHeatInput, map_sum, map_smul,
        BoundedContinuousFunction.evalCLM_apply, heatSemigroupNDclm_apply,
        heatSemigroupNDbcf_apply, smul_eq_mul]
    _ = ofMatrix (matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v := by
      change (∑ i : Fin d, ∑ j : Fin d,
        (v i * v j) * heatSemigroupND t (F i j) x) =
          ofMatrix (fun i j => heatSemigroupND t (F i j) x) v v
      rw [ofMatrix_apply]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A uniform quadratic-form lower bound is preserved by the genuine matrix
heat integral. Bounded-continuous entries supply all required integrability;
symmetry and positivity of the reserve are not needed for this inequality. -/
theorem matrixHeatSemigroupND_preserves_coercivity {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (c : ℝ)
    (hcoercive : ∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin d → ℝ) :
    c * ‖v‖ ^ 2 ≤
      ofMatrix (matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v := by
  let q := quadraticHeatInput F v
  have hqint := integrable_heatKernelND_sub_mul ht x
    q.continuous.aestronglyMeasurable (fun y => q.norm_coe_le_norm y)
  have hcint := (integrable_heatKernelND_sub ht x).mul_const (c * ‖v‖ ^ 2)
  have hcompare := heatSemigroupND_mono ht x
    (f := fun _ => c * ‖v‖ ^ 2) (g := q)
    (fun y => by
      change c * ‖v‖ ^ 2 ≤ quadraticHeatInput F v y
      rw [quadraticHeatInput_apply]
      exact hcoercive y v) hcint hqint
  rw [heatSemigroupND_const ht] at hcompare
  change c * ‖v‖ ^ 2 ≤ heatSemigroupND t (quadraticHeatInput F v) x at hcompare
  rw [heatSemigroupND_quadraticHeatInput F ht] at hcompare
  exact hcompare

/-- The preserved positive reserve gives strict positive definiteness at
every positive time, including the vacuous zero-rank case. -/
theorem matrixHeatSemigroupND_pos_of_coercive {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < ofMatrix (matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v := by
  exact lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.mpr hv) 2))
    (matrixHeatSemigroupND_preserves_coercivity F c hcoercive ht x v)

end RicciFlow.AnalyticPDE
