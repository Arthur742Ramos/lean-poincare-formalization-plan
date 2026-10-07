import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.BoundarylessInitialMetricLocalization
import PoincareCurvature.Geometry.Manifold.RicciFlow.PointFourContract

noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open RicciFlow.AnalyticPDE PoincareCurvature.FiniteCoordinateBilinear

universe u v w

section MinimalGeometricInstances
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]

-- The auxiliary classes are synthesized from these geometric hypotheses.
example : CompleteSpace E := by infer_instance
example : SigmaCompactSpace M := by infer_instance
example : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I := by infer_instance
end MinimalGeometricInstances

section CanonicalGeometricSpecialization
-- This is the actual preserved PointFourContract geometric context.
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
local notation "TM" => (TangentSpace I : M → Type _)

example
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) :
    let d := Module.finrank ℝ E
    let b := Module.finBasis ℝ E
    ∃ χ : (Fin d → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ initialMetricCoordinateDomain (I := I) p b ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data d,
        (∀ i k z, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k +
            χ z * (initialMetricCoordinates g₀ p b z i k -
              initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k)) ∧
        (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p b),
          ∀ i k, (D i k).value z = initialMetricCoordinates g₀ p b z i k) ∧
        (∀ z ∉ tsupport χ, ∀ i k, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k) ∧
        (∀ z i k, (D i k).value z = (D k i).value z) ∧
        (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i k => (D i k).value z) v v) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin d → ℝ) → ℝ)) := by
  exact exists_initialMetricLocalizedHeatData g₀ p
end CanonicalGeometricSpecialization

abbrev ExpectedInitialMetricLocalization :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M),
    let d := Module.finrank ℝ E
    let b := Module.finBasis ℝ E
    ∃ χ : (Fin d → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ initialMetricCoordinateDomain (I := I) p b ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data d,
        (∀ i k z, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k +
            χ z * (initialMetricCoordinates g₀ p b z i k -
              initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k)) ∧
        (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p b),
          ∀ i k, (D i k).value z = initialMetricCoordinates g₀ p b z i k) ∧
        (∀ z ∉ tsupport χ, ∀ i k, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k) ∧
        (∀ z i k, (D i k).value z = (D k i).value z) ∧
        (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i k => (D i k).value z) v v) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin d → ℝ) → ℝ))

def initialMetricLocalizationFullSignatureAssignment : ExpectedInitialMetricLocalization.{u, v, w} :=
  @RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData

#print axioms PoincareCurvature.CompactlySupportedC2Jet.uniformContinuous_second
#print axioms PoincareCurvature.FiniteCoordinateBilinear.norm_ofMatrix_le
#print axioms RicciFlow.AnalyticPDE.exists_positiveFrozenC2MatrixHeatData
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData
#check @RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData
#print axioms PoincareCurvature.CompactlySupportedC2Jet.second_eq_fderiv_fderiv
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.ofCompactSupport
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero_addConst_ofCompactSupport
#print axioms RicciFlow.AnalyticPDE.exists_positiveFrozenC2Bilinear
#print axioms RicciFlow.AnalyticPDE.contDiffOn_initialMetricCoordinates
#print axioms RicciFlow.AnalyticPDE.initialMetricCoordinates_pos_at_point
