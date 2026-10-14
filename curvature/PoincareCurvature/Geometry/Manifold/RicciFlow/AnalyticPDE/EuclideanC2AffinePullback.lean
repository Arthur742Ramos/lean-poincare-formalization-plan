import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffineTransport
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Certified affine pullback of literal bounded C2 data

Source candidate, uncompiled. The scalar Frechet bridge is a Source dependency
until its separate native qualification succeeds. The first and second fields
below are explicit finite chain-rule sums of the actual bounded fields. Both
coordinate derivative certificates are proved from the derived Frechet
derivatives; no differentiability or Holder oracle is added.

The dimensions are independent and the map need not be invertible. This is
scalar data transport, not tensor-frame normalization or a generator identity.
-/

noncomputable section

open scoped BigOperators Topology

namespace RicciFlow.AnalyticPDE

private def affineCoordinateMap {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) : C((Fin m → ℝ), (Fin n → ℝ)) :=
  ⟨fun x => a + L x, continuous_const.add L.continuous⟩

private theorem affineCoordinateMap_apply {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ) :
    affineCoordinateMap a L x = a + L x := rfl

private def affineFirstField {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k : Fin m) : BoundedContinuousFunction (Fin m → ℝ) ℝ :=
  ∑ p : Fin n, (L (Pi.single k 1) p) •
    (D.first p).compContinuous (affineCoordinateMap a L)

private def affineSecondField {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k l : Fin m) : BoundedContinuousFunction (Fin m → ℝ) ℝ :=
  ∑ p : Fin n, ∑ q : Fin n, (L (Pi.single k 1) p * L (Pi.single l 1) q) •
    (D.second p q).compContinuous (affineCoordinateMap a L)

private theorem affineFirstField_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k : Fin m) (x : Fin m → ℝ) :
    affineFirstField D a L k x =
      ∑ p : Fin n, L (Pi.single k 1) p * D.first p (a + L x) := by
  classical
  change BoundedContinuousFunction.evalCLM ℝ x
    (∑ p : Fin n, (L (Pi.single k 1) p) •
      (D.first p).compContinuous (affineCoordinateMap a L)) = _
  simp only [map_sum, map_smul, BoundedContinuousFunction.evalCLM_apply,
    smul_eq_mul, BoundedContinuousFunction.compContinuous_apply, affineCoordinateMap_apply]

private theorem affineSecondField_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k l : Fin m) (x : Fin m → ℝ) :
    affineSecondField D a L k l x =
      ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x) := by
  classical
  change BoundedContinuousFunction.evalCLM ℝ x
    (∑ p : Fin n, ∑ q : Fin n, (L (Pi.single k 1) p * L (Pi.single l 1) q) •
      (D.second p q).compContinuous (affineCoordinateMap a L)) = _
  simp only [map_sum, map_smul, BoundedContinuousFunction.evalCLM_apply,
    smul_eq_mul, BoundedContinuousFunction.compContinuous_apply, affineCoordinateMap_apply]

private theorem hasDerivAt_affineCoordinateCurve {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k : Fin m) (x : Fin m → ℝ) :
    HasDerivAt (fun r => a + L (Function.update x k r))
      (L (Pi.single k 1)) (x k) := by
  have hL : HasDerivAt (fun r => L (Function.update x k r))
      (L (Pi.single k 1)) (x k) := by
    simpa only [Function.comp_def] using
      L.hasFDerivAt.comp_hasDerivAt (x k) (hasDerivAt_update x k (x k))
  convert! (hasDerivAt_const (x k) a).add hL using 1 <;>
    simp only [zero_add]

private theorem hasDerivAt_value_affineCoordinate {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k : Fin m) (x : Fin m → ℝ) :
    HasDerivAt (fun r => D.value (a + L (Function.update x k r)))
      (∑ p : Fin n, L (Pi.single k 1) p * D.first p (a + L x)) (x k) := by
  classical
  have hchain := (D.hasFDerivAt_affineValueGradient (a + L x)).comp_hasDerivAt_of_eq
    (x k) (hasDerivAt_affineCoordinateCurve a L k x) (by simp)
  change HasDerivAt (fun r => D.value (a + L (Function.update x k r)))
    (D.affineValueGradient (a + L x) (L (Pi.single k 1))) (x k) at hchain
  have hcoeff : D.affineValueGradient (a + L x) (L (Pi.single k 1)) =
      ∑ p : Fin n, L (Pi.single k 1) p * D.first p (a + L x) := by
    rw [EuclideanBoundedC2Data.affineValueGradient, coordinateLinearFunctional_apply]
    apply Finset.sum_congr rfl
    intro p _
    ring
  exact hchain.congr_deriv hcoeff

private theorem hasDerivAt_first_affineCoordinate {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (l : Fin n) (k : Fin m) (x : Fin m → ℝ) :
    HasDerivAt (fun r => D.first l (a + L (Function.update x k r)))
      (∑ p : Fin n, L (Pi.single k 1) p * D.second p l (a + L x)) (x k) := by
  classical
  have hchain := (D.hasFDerivAt_affineFirstGradient l (a + L x)).comp_hasDerivAt_of_eq
    (x k) (hasDerivAt_affineCoordinateCurve a L k x) (by simp)
  change HasDerivAt (fun r => D.first l (a + L (Function.update x k r)))
    (D.affineFirstGradient l (a + L x) (L (Pi.single k 1))) (x k) at hchain
  have hcoeff : D.affineFirstGradient l (a + L x) (L (Pi.single k 1)) =
      ∑ p : Fin n, L (Pi.single k 1) p * D.second p l (a + L x) := by
    rw [EuclideanBoundedC2Data.affineFirstGradient, coordinateLinearFunctional_apply]
    apply Finset.sum_congr rfl
    intro p _
    ring
  exact hchain.congr_deriv hcoeff

namespace EuclideanBoundedC2Data

/-- Certified scalar affine precomposition of literal bounded C2 data. The
linear map may be rectangular, singular, or have empty domain/codomain. -/
def precompAffine {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) : EuclideanBoundedC2Data m where
  value := D.value.compContinuous (affineCoordinateMap a L)
  first := affineFirstField D a L
  second := affineSecondField D a L
  hasDeriv_value := by
    intro k x
    change HasDerivAt (fun r => D.value (a + L (Function.update x k r)))
      (affineFirstField D a L k x) (x k)
    rw [affineFirstField_apply]
    exact hasDerivAt_value_affineCoordinate D a L k x
  hasDeriv_first := by
    classical
    intro k l x
    change HasDerivAt (fun r => affineFirstField D a L l (Function.update x k r))
      (affineSecondField D a L k l x) (x k)
    have hfun : (fun r => affineFirstField D a L l (Function.update x k r)) =
        (fun r => ∑ q : Fin n, L (Pi.single l 1) q *
          D.first q (a + L (Function.update x k r))) := by
      funext r
      exact affineFirstField_apply D a L l (Function.update x k r)
    rw [hfun, affineSecondField_apply]
    have hsum : HasDerivAt
        (fun r => ∑ q : Fin n, L (Pi.single l 1) q *
          D.first q (a + L (Function.update x k r)))
        (∑ q : Fin n, L (Pi.single l 1) q *
          (∑ p : Fin n, L (Pi.single k 1) p * D.second p q (a + L x))) (x k) :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun q _ =>
        (hasDerivAt_first_affineCoordinate D a L q k x).const_mul (L (Pi.single l 1) q))
    have hcoeff : (∑ q : Fin n, L (Pi.single l 1) q *
        (∑ p : Fin n, L (Pi.single k 1) p * D.second p q (a + L x))) =
        ∑ p : Fin n, ∑ q : Fin n,
          (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x) := by
      calc
        _ = ∑ q : Fin n, ∑ p : Fin n,
            L (Pi.single l 1) q * (L (Pi.single k 1) p * D.second p q (a + L x)) := by
          simp only [Finset.mul_sum]
        _ = ∑ p : Fin n, ∑ q : Fin n,
            L (Pi.single l 1) q * (L (Pi.single k 1) p * D.second p q (a + L x)) :=
          Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          ring
    exact hsum.congr_deriv hcoeff

theorem precompAffine_value_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ) :
    (D.precompAffine a L).value x = D.value (a + L x) := rfl

theorem precompAffine_first_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k : Fin m) (x : Fin m → ℝ) :
    (D.precompAffine a L).first k x =
      ∑ p : Fin n, L (Pi.single k 1) p * D.first p (a + L x) :=
  affineFirstField_apply D a L k x

theorem precompAffine_second_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (k l : Fin m) (x : Fin m → ℝ) :
    (D.precompAffine a L).second k l x =
      ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x) :=
  affineSecondField_apply D a L k l x

theorem norm_precompAffine_value_le {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ‖(D.precompAffine a L).value‖ ≤ ‖D.value‖ :=
  D.value.norm_compContinuous_le (affineCoordinateMap a L)

theorem norm_precompAffine_first_le {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k : Fin m) :
    ‖(D.precompAffine a L).first k‖ ≤
      ∑ p : Fin n, |L (Pi.single k 1) p| * ‖D.first p‖ := by
  classical
  change ‖∑ p : Fin n, (L (Pi.single k 1) p) •
    (D.first p).compContinuous (affineCoordinateMap a L)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    ((D.first p).norm_compContinuous_le (affineCoordinateMap a L)) (abs_nonneg _)

theorem norm_precompAffine_second_le {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k l : Fin m) :
    ‖(D.precompAffine a L).second k l‖ ≤
      ∑ p : Fin n, ∑ q : Fin n,
        |L (Pi.single k 1) p * L (Pi.single l 1) q| * ‖D.second p q‖ := by
  classical
  change ‖∑ p : Fin n, ∑ q : Fin n, (L (Pi.single k 1) p * L (Pi.single l 1) q) •
    (D.second p q).compContinuous (affineCoordinateMap a L)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    ((D.second p q).norm_compContinuous_le (affineCoordinateMap a L)) (abs_nonneg _)

end EuclideanBoundedC2Data

end RicciFlow.AnalyticPDE
