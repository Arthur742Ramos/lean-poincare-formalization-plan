module

public import LichnerowiczObata.ClosedStatement
public import LichnerowiczObata.GeometryComparison

/-! The renderer-compatible statement is definitionally equivalent to the
original theorem with every hypothesis and geometric operation unchanged. -/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace LichnerowiczObataEntry.Geometry

universe u v w

/-- Closing the parameters and inlining the definitions neither weakens nor
strengthens the original quantified statement. -/
theorem completeStatement_iff : completeStatement.{u,v,w} ↔
    (∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
      [RiemannianBundle (TangentSpace I : M → Type _)]
      [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
      [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
      [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
      [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
      [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M],
      geometricStatement (I := I) (M := M)) := by
  rfl

/-- The original geometric proof supplies the renderer-compatible statement. -/
theorem completeStatement_proved : completeStatement.{u,v,w} := by
  apply completeStatement_iff.mpr
  intros
  exact geometricStatement_proved

end LichnerowiczObataEntry.Geometry
