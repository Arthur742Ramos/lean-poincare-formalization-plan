module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi

/-!
# Contracted second Bianchi identity for a metric-compatible torsion-free connection

The differentiated curvature is the actual corrected connection commutator.  Neither its
symmetries nor a Bianchi equation is assumed in the selected theorem.  The sums are orthonormal
contractions of that derivative.  A separate identification with derivatives of the Ricci and
Einstein tensor fields is not claimed by this surface.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace ContractedBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]


theorem contractedSecondBianchi
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x))
    (w : TangentSpace I x) :
    (∑ i, ∑ k, CovariantDerivative.curvatureCovariantDerivativeInner
      cov x w (b k) (b i) (b i) (b k)) =
    2 * ∑ i, ∑ k, CovariantDerivative.curvatureCovariantDerivativeInner
      cov x (b i) (b k) (b i) w (b k) := by
  sorry

end ContractedBianchi
