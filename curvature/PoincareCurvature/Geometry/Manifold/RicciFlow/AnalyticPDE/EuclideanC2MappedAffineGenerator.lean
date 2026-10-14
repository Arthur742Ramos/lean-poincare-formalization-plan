import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffineHeatTrace

/-!
# Original-coordinate right initial generator of mapped affine heat

Source candidate, uncompiled. The actual scalar heat path of the certified
affine pullback is evaluated at the inverse affine spatial coordinates. Its
initial value is the original literal C2 value and its right initial derivative
is the explicit coefficient contraction obtained from the linear equivalence.

Both finite dimensions are retained separately. These coefficients are derived
structurally from L; they are not a supplied generator or closeness oracle.
Their identification with a literal metric inverse Gram matrix is a separate
geometric obligation. No positive-time PDE or interval Ricci solution is claimed.
-/

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace RicciFlow.AnalyticPDE

/-- The actual pulled scalar Gaussian heat path mapped to the original
coordinates. No metric tensor frame is changed by this scalar definition. -/
def mappedAffineHeatFlowPath {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  heatFlowPathBcf (D.precompAffine a L.toContinuousLinearMap).value t (L.symm (z - a))

/-- Structural spatial coefficients from the normalizing linear map, with
source dimension m and original coordinate dimension n kept explicit. -/
def affineSpatialGramCoefficient {n m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (p q : Fin n) : ℝ :=
  ∑ k : Fin m, L (Pi.single k 1) p * L (Pi.single k 1) q

private theorem affine_inverse_point {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    a + L (L.symm (z - a)) = z := by
  rw [L.apply_symm_apply]
  abel

/-- The constructed mapped heat path starts at the original literal value. -/
theorem mappedAffineHeatFlowPath_zero {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    mappedAffineHeatFlowPath D a L 0 z = D.value z := by
  unfold mappedAffineHeatFlowPath
  have hzero : heatFlowPathBcf (D.precompAffine a L.toContinuousLinearMap).value 0 =
      (D.precompAffine a L.toContinuousLinearMap).value := dif_neg (lt_irrefl 0)
  rw [hzero, EuclideanBoundedC2Data.precompAffine_value_apply]
  change D.value (a + L (L.symm (z - a))) = D.value z
  rw [affine_inverse_point]

/-- The actual right initial generator in the original coordinates is the
explicit structural L L-transpose contraction of the original Hessian. -/
theorem hasDerivWithinAt_mappedAffineHeatFlowPath_zero {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D a L t z)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * D.second p q z)
      (Ici 0) 0 := by
  classical
  have h := D.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero
    a L.toContinuousLinearMap (L.symm (z - a))
  change HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D a L t z)
    (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
      (L (Pi.single k 1) p * L (Pi.single k 1) q) *
        D.second p q (a + L (L.symm (z - a)))) (Ici 0) 0 at h
  rw [affine_inverse_point] at h
  have hcoeff : (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
      (L (Pi.single k 1) p * L (Pi.single k 1) q) * D.second p q z) =
      ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * D.second p q z := by
    calc
      _ = ∑ p : Fin n, ∑ k : Fin m, ∑ q : Fin n,
          (L (Pi.single k 1) p * L (Pi.single k 1) q) * D.second p q z :=
        Finset.sum_comm
      _ = ∑ p : Fin n, ∑ q : Fin n, ∑ k : Fin m,
          (L (Pi.single k 1) p * L (Pi.single k 1) q) * D.second p q z := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [affineSpatialGramCoefficient, Finset.sum_mul]
  exact h.congr_deriv hcoeff

end RicciFlow.AnalyticPDE
