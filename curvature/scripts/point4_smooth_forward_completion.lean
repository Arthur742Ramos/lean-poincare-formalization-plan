import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardContract

open Bundle
open scoped Manifold ContDiff

/- This full dependent type is independent of the contract alias. Bare target
assignment at three independent universes rejects extra solver/analytic inputs,
empty-only constructions, omitted dimensions and universe specialization.
This probe intentionally fails until the actual general target is proved. -/

universe u₁ u₂ u₃
example :
  ∀ {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type 0} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type 0} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless],
      RicciFlow.SmoothForward.ExistenceUniquenessFamily
        (E := E) (H := H) (I := I) (M := M) :=
  @RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel

example :
  ∀ {E : Type u₁} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type u₂} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u₃} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless],
      RicciFlow.SmoothForward.ExistenceUniquenessFamily
        (E := E) (H := H) (I := I) (M := M) :=
  @RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel

example :
  ∀ {E : Type u₃} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type u₁} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u₂} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless],
      RicciFlow.SmoothForward.ExistenceUniquenessFamily
        (E := E) (H := H) (I := I) (M := M) :=
  @RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel

#print axioms RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel
