import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace

/-!
# Actual scalar Frechet derivatives needed for affine C2 transport

Source candidate, uncompiled. The full derivative is reconstructed from the
existing continuous bounded coordinate derivatives and their actual witnesses.
No Frechet differentiability, continuity, Lipschitz or Holder oracle is added.

These lemmas are the first scalar primitive for a later precompAffine
constructor and normalized frozen heat path. No anisotropic generator or
nonlinear interval equation is claimed here.
-/

noncomputable section

open scoped BigOperators Topology

namespace RicciFlow.AnalyticPDE.EuclideanBoundedC2Data

/-- The actual value gradient reconstructed from stored coordinate derivatives. -/
def affineValueGradient {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  coordinateLinearFunctional (fun k => D.first k x)

/-- The actual gradient of one first-derivative component, with the stored
second-index convention: second k l differentiates first l in direction k. -/
def affineFirstGradient {n : ℕ} (D : EuclideanBoundedC2Data n)
    (l : Fin n) (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  coordinateLinearFunctional (fun k => D.second k l x)

private theorem continuous_affineValueGradient {n : ℕ} (D : EuclideanBoundedC2Data n) :
    Continuous D.affineValueGradient := by
  classical
  unfold affineValueGradient coordinateLinearFunctional
  apply continuous_finsetSum
  intro k _
  exact (D.first k).continuous.smul continuous_const

private theorem continuous_affineFirstGradient {n : ℕ} (D : EuclideanBoundedC2Data n)
    (l : Fin n) : Continuous (D.affineFirstGradient l) := by
  classical
  unfold affineFirstGradient coordinateLinearFunctional
  apply continuous_finsetSum
  intro k _
  exact (D.second k l).continuous.smul continuous_const

/-- The actual coordinate value certificates produce a genuine full Frechet
derivative, also in zero-dimensional coordinate space. -/
theorem hasFDerivAt_affineValueGradient {n : ℕ} (D : EuclideanBoundedC2Data n)
    (x : Fin n → ℝ) : HasFDerivAt D.value (D.affineValueGradient x) x := by
  classical
  refine hasFDerivAt_of_continuous_coordinate_derivatives
    D.value D.affineValueGradient (continuous_affineValueGradient D) ?_ x
  intro y k
  rw [affineValueGradient, coordinateLinearFunctional_single]
  exact (D.hasDeriv_value k y).hasFDerivAt

/-- The actual stored second certificates produce a genuine full Frechet
derivative of each scalar first-derivative component. -/
theorem hasFDerivAt_affineFirstGradient {n : ℕ} (D : EuclideanBoundedC2Data n)
    (l : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (D.first l) (D.affineFirstGradient l x) x := by
  classical
  refine hasFDerivAt_of_continuous_coordinate_derivatives
    (D.first l) (D.affineFirstGradient l) (continuous_affineFirstGradient D l) ?_ x
  intro y k
  rw [affineFirstGradient, coordinateLinearFunctional_single]
  exact (D.hasDeriv_first k l y).hasFDerivAt

end RicciFlow.AnalyticPDE.EuclideanBoundedC2Data
