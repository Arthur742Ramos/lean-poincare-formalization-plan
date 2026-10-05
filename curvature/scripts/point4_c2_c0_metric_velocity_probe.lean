import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C2MetricVelocityExtension

noncomputable section
set_option autoImplicit false
set_option pp.proofs false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.width 120

open Bundle Filter
open scoped Manifold ContDiff Topology

universe u v w

-- An exact universe-polymorphic assignment exposes hidden premises. In
-- particular no ambient RiemannianBundle, nonzero-rank, atlas, regularizer,
-- initial Holder, solver or PDE witness may enter the exported declaration.
abbrev ExpectedC2C0MetricVelocity :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (t₀ : ℝ),
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
    ∀ vel : RicciFlow.AnalyticPDE.C0Endpoint.ContinuousSymmetricVelocity (I := I) (M := M),
      ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
        g t₀ = g₀ ∧ ∀ x : M, ∀ a b : TangentSpace I x,
          HasDerivAt (fun t => RicciFlow.metricTensor g t x a b) (vel.tensor x a b) t₀

def c2C0MetricVelocityFullSignatureAssignment : ExpectedC2C0MetricVelocity.{u,v,w} :=
  @RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity

section MinimalGeometricContext
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]

example : CompleteSpace E := by infer_instance
example : SigmaCompactSpace M := by infer_instance
example : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I := by infer_instance

-- Apply the actual construction from the canonical geometric hypotheses,
-- with the auxiliary instances synthesized and no supplied smoothing data.
theorem c2C0MetricVelocityCanonicalContext
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (t₀ : ℝ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
    ∀ vel : RicciFlow.AnalyticPDE.C0Endpoint.ContinuousSymmetricVelocity (I := I) (M := M),
      ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
        g t₀ = g₀ ∧ ∀ x : M, ∀ a b : TangentSpace I x,
          HasDerivAt (fun t => RicciFlow.metricTensor g t x a b) (vel.tensor x a b) t₀ :=
  RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity g₀ t₀

-- Zero-dimensional models use the same actual exported construction.
theorem c2C0MetricVelocityRankZeroContext [Subsingleton E]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (t₀ : ℝ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
    ∀ vel : RicciFlow.AnalyticPDE.C0Endpoint.ContinuousSymmetricVelocity (I := I) (M := M),
      ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
        g t₀ = g₀ ∧ ∀ x : M, ∀ a b : TangentSpace I x,
          HasDerivAt (fun t => RicciFlow.metricTensor g t x a b) (vel.tensor x a b) t₀ :=
  RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity g₀ t₀

-- Empty manifolds require neither a selected point nor Nonempty M.
theorem c2C0MetricVelocityEmptyManifoldContext [IsEmpty M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (t₀ : ℝ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g₀.toRiemannianMetric⟩
    ∀ vel : RicciFlow.AnalyticPDE.C0Endpoint.ContinuousSymmetricVelocity (I := I) (M := M),
      ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
        g t₀ = g₀ ∧ ∀ x : M, ∀ a b : TangentSpace I x,
          HasDerivAt (fun t => RicciFlow.metricTensor g t x a b) (vel.tensor x a b) t₀ :=
  RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity g₀ t₀
end MinimalGeometricContext

-- Actual scalar zero-rank Gaussian and empty-family reserve specializations.
example (f : BoundedContinuousFunction (Fin 0 → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin 0 → ℝ) → ℝ)) (x : Fin 0 → ℝ) :
    HasDerivAt (fun h => h * RicciFlow.AnalyticPDE.C0Endpoint.gaussianPath f h x) (f x) 0 :=
  RicciFlow.AnalyticPDE.C0Endpoint.hasDerivAt_time_mul_gaussianPath f hf x

example (ε B : Fin 0 → ℝ) : ∃ δ > 0, ∀ i : Fin 0, δ * B i < ε i :=
  RicciFlow.AnalyticPDE.C0Endpoint.exists_common_amplitude ε B
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

-- Complete mathematical type/data reports, never truncated #check summaries.
#eval IO.println "C2_C0_METRIC_VELOCITY_TYPES_BEGIN"
#print ExpectedC2C0MetricVelocity
#print c2C0MetricVelocityFullSignatureAssignment
#print RicciFlow.AnalyticPDE.C0Endpoint.ContinuousSymmetricVelocity
#print RicciFlow.MetricFamily
#print RicciFlow.metricTensor
#print Bundle.ContMDiffRiemannianMetric
#print RicciFlow.AnalyticPDE.C0Endpoint.preferredCover
#print RicciFlow.AnalyticPDE.C0Endpoint.coordinateBuffer
#print RicciFlow.AnalyticPDE.C0Endpoint.localizedVelocityBcf
#print RicciFlow.AnalyticPDE.C0Endpoint.gaussianTensor
#print RicciFlow.AnalyticPDE.C0Endpoint.endpointTensor
#print RicciFlow.AnalyticPDE.C0Endpoint.centeredMetric
#print RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity
#print c2C0MetricVelocityCanonicalContext
#print c2C0MetricVelocityRankZeroContext
#print c2C0MetricVelocityEmptyManifoldContext
#eval IO.println "C2_C0_METRIC_VELOCITY_TYPES_END"

#print axioms RicciFlow.AnalyticPDE.C0Endpoint.gaussianPath_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.continuousAt_gaussianPath_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.norm_gaussianPath_le
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.contDiff_two_gaussianPath
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.hasDerivAt_time_mul_gaussianPath
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.isOpen_coordinateAnalysisDomain
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.nonempty_coordinateBuffer
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.uniformContinuous_localizedVelocityBcf
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.contDiff_two_gaussianMatrix
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.gaussianTensor_symmetric
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.contMDiff_two_gaussianTensor
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.gaussianTensor_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.continuousAt_gaussianTensor_component_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.hasDerivAt_time_mul_gaussianTensor
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.norm_matrixBilinear_gaussianMatrix_le
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_uniform_pos_ball_any
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_piece_positivity_radius
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_common_amplitude
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_gaussianTensor_positivity_reserve
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.endpointTensor_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.contMDiff_two_endpointTensor
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.hasDerivAt_endpointTensor_component_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.centeredMetric_zero
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.centeredMetric_inner
#print axioms RicciFlow.AnalyticPDE.C0Endpoint.exists_c2_metricFamily_with_c0_endpoint_velocity
#print axioms c2C0MetricVelocityFullSignatureAssignment
#print axioms c2C0MetricVelocityCanonicalContext
#print axioms c2C0MetricVelocityRankZeroContext
#print axioms c2C0MetricVelocityEmptyManifoldContext
