import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricMappedGaussianEquation

-- Source-only actual scalar positive-time equation, with no ambient metric/derivative oracle.
open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedLiteralInitialMetricMappedGaussianEquation :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] {d : ℕ}
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (D : EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ),
    HasDerivAt (fun s => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) s z)
      (∑ i : Fin d, ∑ j : Fin d,
        (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
          (Matrix.of (initialMetricCoordinates g₀ p b
            (initialMetricCoordinatePoint (I := I) p b)))) i j *
        (mappedGaussianBoundedC2Data D
          (initialMetricCoordinatePoint (I := I) p b)
          (initialMetricOrthonormalCoordinateEquiv g₀ p b) ht).second i j z) t

def literalInitialMetricMappedGaussianEquationFullSignatureAssignment :
    ExpectedLiteralInitialMetricMappedGaussianEquation.{u,v,w} :=
  @hasDerivAt_initialMetricMappedGaussian_eq_frozenHessian

section EmptyPreferredRank

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

example (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin 0) ℝ E)
    (D : EuclideanBoundedC2Data 0) {t : ℝ} (ht : 0 < t) (z : Fin 0 → ℝ) :
    HasDerivAt (fun s => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) s z) 0 t := by
  simpa using hasDerivAt_initialMetricMappedGaussian_eq_frozenHessian g₀ p b D ht z

end EmptyPreferredRank

set_option pp.universes false
set_option format.width 200
#check @hasDerivAt_initialMetricMappedGaussian_eq_frozenHessian
#print axioms RicciFlow.AnalyticPDE.hasDerivAt_initialMetricMappedGaussian_eq_frozenHessian
