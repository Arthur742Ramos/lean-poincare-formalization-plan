module

public import LichnerowiczObata.GeometryComparison

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace LichnerowiczObataEntry.Geometry

/-- The complete Lichnerowicz--Obata theorem, including spectral attainment
and both directions of the global round-sphere rigidity statement. -/
theorem lichnerowiczObata
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M] :
    geometricStatement (I := I) (M := M) := by
  exact geometricStatement_proved

end LichnerowiczObataEntry.Geometry
