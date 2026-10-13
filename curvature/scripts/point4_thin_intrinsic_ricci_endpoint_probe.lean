import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C2IntrinsicRicciEndpointThin

-- SOURCE-only proposed kernel type and axiom probe. Native execution is UNRUN.
open Bundle
open scoped Manifold ContDiff

universe u v w

abbrev ExpectedThinIntrinsicRicciJet :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (t₀ : ℝ),
    ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
      g t₀ = g₀ ∧ ∀ x : M, ∀ u w : TangentSpace I x,
        HasDerivAt (fun t => RicciFlow.metricTensor g t x u w)
          ((-2 : ℝ) * RicciFlow.intrinsicRicciTensor g t₀ x u w) t₀

def thinIntrinsicRicciJetFullSignatureAssignment :
    ExpectedThinIntrinsicRicciJet.{u,v,w} :=
  @RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_intrinsicRicci_endpoint_derivative_thin

#check @RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_intrinsicRicci_endpoint_derivative_thin
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_intrinsicRicci_endpoint_derivative_thin

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (t₀ : ℝ) :
    ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
      g t₀ = g₀ ∧ ∀ x : M, ∀ u w : TangentSpace I x,
        HasDerivAt (fun t => RicciFlow.metricTensor g t x u w)
          ((-2 : ℝ) * RicciFlow.intrinsicRicciTensor g t₀ x u w) t₀ :=
  RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_intrinsicRicci_endpoint_derivative_thin
    (I := I) (M := M) g₀ t₀
