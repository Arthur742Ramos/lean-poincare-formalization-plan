import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatStrongInitialGenerator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2MappedAffineGenerator

/-!
# Strong original-coordinate right initial derivative of actual mapped heat

Source candidate, uncompiled. The initial Hessian uniform-continuity evidence
is transported by certified affine pullback. The strong actual heat derivative
is mapped through the existing continuous linear BCF precomposition operator.
Evaluating the resulting derivative and using the genuine already-proved scalar
initial derivative identifies its finite coefficient contraction. No generator
or derivative witness is supplied as a premise.

The dimensions remain separate. This proves a right derivative in BCF norm for
these genuine initial data, not a characterization of an operator domain,
Banach range or nonlinear interval Ricci-flow existence.
-/

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace RicciFlow.AnalyticPDE

private def inverseAffineCoordinateMap {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) : C((Fin n → ℝ), (Fin m → ℝ)) :=
  ⟨fun z => L.symm (z - a), L.symm.continuous.comp (continuous_id.sub continuous_const)⟩

/-- The actual mapped scalar path as a bounded continuous function, defined
using the inverse affine spatial precomposition CLM. -/
def mappedAffineHeatFlowBcf {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (t : ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ (inverseAffineCoordinateMap a L)
    (heatFlowPathBcf (D.precompAffine a L.toContinuousLinearMap).value t)

theorem mappedAffineHeatFlowBcf_apply {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (t : ℝ) (z : Fin n → ℝ) :
    mappedAffineHeatFlowBcf D a L t z = mappedAffineHeatFlowPath D a L t z := rfl

/-- Strong right initial BCF derivative with the explicit structural coefficient
contraction of the stored original Hessian. Initial hsecond is retained. -/
theorem hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ)) :
    HasDerivWithinAt (mappedAffineHeatFlowBcf D a L)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q • D.second p q)
      (Ici 0) 0 := by
  classical
  let P := D.precompAffine a L.toContinuousLinearMap
  let Q := BoundedContinuousFunction.compContinuousCLM ℝ ℝ (inverseAffineCoordinateMap a L)
  have hP : ∀ k l, UniformContinuous (P.second k l : (Fin m → ℝ) → ℝ) :=
    fun k l => D.uniformContinuous_precompAffine_second a L.toContinuousLinearMap hsecond k l
  have hraw := Q.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ)
    (P.hasDerivWithinAt_heatFlowPathBcf_strong_zero hP)
  change HasDerivWithinAt (mappedAffineHeatFlowBcf D a L)
    (Q (∑ k : Fin m, P.second k k)) (Ici 0) 0 at hraw
  have hcoeff : Q (∑ k : Fin m, P.second k k) =
      ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q • D.second p q := by
    ext z
    have heval := (BoundedContinuousFunction.evalCLM ℝ z).hasFDerivAt.comp_hasDerivWithinAt
      (0 : ℝ) hraw
    change HasDerivWithinAt (fun t => mappedAffineHeatFlowBcf D a L t z)
      (Q (∑ k : Fin m, P.second k k) z) (Ici 0) 0 at heval
    have hfun : (fun t => mappedAffineHeatFlowBcf D a L t z) =
        (fun t => mappedAffineHeatFlowPath D a L t z) := by
      funext t
      exact mappedAffineHeatFlowBcf_apply D a L t z
    rw [hfun] at heval
    have hpoint : Q (∑ k : Fin m, P.second k k) z =
        ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * D.second p q z :=
      UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici (0 : ℝ)) heval
        (hasDerivWithinAt_mappedAffineHeatFlowPath_zero D a L z)
    have hsum : (∑ p : Fin n, ∑ q : Fin n,
        affineSpatialGramCoefficient L p q • D.second p q) z =
        ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * D.second p q z := by
      change BoundedContinuousFunction.evalCLM ℝ z
        (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q • D.second p q) = _
      simp only [map_sum, map_smul, BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
    exact hpoint.trans hsum.symm
  exact hraw.congr_deriv hcoeff

end RicciFlow.AnalyticPDE
