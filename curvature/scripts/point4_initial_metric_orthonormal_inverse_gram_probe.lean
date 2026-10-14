import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricOrthonormalInverseGram

noncomputable section

-- Source-only full exported types, empty preferred rank and three genuine AX records.
open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedLiteralInitialMetricOrthonormalCoordinates :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {d : ℕ}
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin d) ℝ E),
    (Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ) ≃L[ℝ] (Fin d → ℝ)

def literalInitialMetricOrthonormalCoordinatesFullSignatureAssignment :
    ExpectedLiteralInitialMetricOrthonormalCoordinates.{u,v,w} :=
  @initialMetricOrthonormalCoordinateEquiv

abbrev ExpectedLiteralInitialMetricInverseGramIdentity :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] {d : ℕ}
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i j : Fin d),
    affineSpatialGramCoefficient (initialMetricOrthonormalCoordinateEquiv g₀ p b) i j =
      (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
        (Matrix.of (initialMetricCoordinates g₀ p b
          (initialMetricCoordinatePoint (I := I) p b)))) i j

def literalInitialMetricInverseGramIdentityFullSignatureAssignment :
    ExpectedLiteralInitialMetricInverseGramIdentity.{u,v,w} :=
  @initialMetricOrthonormalCoefficient_eq_literal_inverseGram

abbrev ExpectedLiteralInitialMetricMappedHeatGenerator :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] {d : ℕ}
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (D : EuclideanBoundedC2Data d) (z : Fin d → ℝ),
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) t z)
      (∑ i : Fin d, ∑ j : Fin d,
        (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
          (Matrix.of (initialMetricCoordinates g₀ p b
            (initialMetricCoordinatePoint (I := I) p b)))) i j * D.second i j z)
      (Ici 0) 0

def literalInitialMetricMappedHeatGeneratorFullSignatureAssignment :
    ExpectedLiteralInitialMetricMappedHeatGenerator.{u,v,w} :=
  @hasDerivWithinAt_initialMetricMappedHeat_zero

section EmptyPreferredRank

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

-- The orthonormal tangent index keeps its own finrank even for empty preferred coordinates.
example (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin 0) ℝ E) :
    (Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ) ≃L[ℝ] (Fin 0 → ℝ) :=
  initialMetricOrthonormalCoordinateEquiv g₀ p b

example (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (p : M) (b : Module.Basis (Fin 0) ℝ E)
    (D : EuclideanBoundedC2Data 0) (z : Fin 0 → ℝ) :
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) t z) 0 (Ici 0) 0 := by
  simpa using hasDerivWithinAt_initialMetricMappedHeat_zero g₀ p b D z

end EmptyPreferredRank

set_option pp.universes false
set_option format.width 200
#check @initialMetricOrthonormalCoordinateEquiv
#check @initialMetricOrthonormalCoefficient_eq_literal_inverseGram
#check @hasDerivWithinAt_initialMetricMappedHeat_zero

#print axioms RicciFlow.AnalyticPDE.initialMetricOrthonormalCoordinateEquiv
#print axioms RicciFlow.AnalyticPDE.initialMetricOrthonormalCoefficient_eq_literal_inverseGram
#print axioms RicciFlow.AnalyticPDE.hasDerivWithinAt_initialMetricMappedHeat_zero
