import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MappedGaussianScalarEquation
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricOrthonormalInverseGram

/-!
# Literal g0 positive-time scalar frozen equation

Source candidate, uncompiled. The coefficient identity is the independently
reviewed literal g0 inverse-Gram Source bridge, not an assumed premise. Its
native qualification is still required before this corollary can be credited.
The preferred tensor component frame is unchanged; this theorem applies to
each genuine scalar component datum. It does not construct nonlinear Ricci or
DeTurck flow, identify a Banach generator domain, or assert joint regularity.
-/

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow.AnalyticPDE

variable {E : Type*} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    [finiteE : FiniteDimensional ℝ E] [completeE : CompleteSpace E]
    {H : Type*} [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [topM : TopologicalSpace M] [chartM : ChartedSpace H M] [hausdorffM : T2Space M]
    [manifoldM : IsManifold I ∞ M] [boundarylessM : BoundarylessManifold I M]
    [smoothTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)

include normE spaceE finiteE completeE topH topM chartM hausdorffM manifoldM boundarylessM smoothTangent

/-- At every positive time the actual scalar mapped Gaussian path has time
derivative equal to the literal g0 frozen inverse-Gram contraction of its
actual original-coordinate Hessian. No PDE or derivative witness is supplied. -/
theorem hasDerivAt_initialMetricMappedGaussian_eq_frozenHessian
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (D : EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) :
    HasDerivAt (fun s => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) s z)
      (∑ i : Fin d, ∑ j : Fin d,
        (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
          (Matrix.of (initialMetricCoordinates g₀ p b
            (initialMetricCoordinatePoint (I := I) p b)))) i j *
        (mappedGaussianBoundedC2Data D
          (initialMetricCoordinatePoint (I := I) p b)
          (initialMetricOrthonormalCoordinateEquiv g₀ p b) ht).second i j z) t := by
  simpa only [initialMetricOrthonormalCoefficient_eq_literal_inverseGram] using
    hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian D
      (initialMetricCoordinatePoint (I := I) p b)
      (initialMetricOrthonormalCoordinateEquiv g₀ p b) ht z

end RicciFlow.AnalyticPDE
