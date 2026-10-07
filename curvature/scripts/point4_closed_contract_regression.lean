import PoincareCurvature.Geometry.Manifold.RicciFlow.PointFourContract

/-!
Signature regression only: local `good`/`bad` inputs are test fixtures, not
constructions of the missing canonical target. Negative tests must reject the
same bare-constant assignment used by G5. Nothing here proves Ricci-flow
existence or changes the existing IVP/candidate/time interfaces.
-/

open Bundle
open scoped Manifold ContDiff

namespace PointFourContractRegression

universe u v w

open RicciFlow

-- The exact accepted signature at three independent universes.
example (good : PointFourClosedManifoldContract.{u, v, w}) :
    PointFourClosedManifoldContract.{u, v, w} := @good

abbrev ExtraPackage :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
    (package : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)),
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : ExtraPackage.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev ExtraSolver :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]
    (solve : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)),
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : ExtraSolver.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev ExtraAnalytic :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] (analytic : Prop) (certificate : analytic),
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : ExtraAnalytic.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev GlobalModelBoundaryless :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : GlobalModelBoundaryless.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev EmptyManifold :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] [IsEmpty M],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : EmptyManifold.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev SubsingletonModel :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] [Subsingleton E],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : SubsingletonModel.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev SubsingletonManifold :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] [Subsingleton M],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : SubsingletonManifold.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev RankOne :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] (rank_one : Module.finrank ℝ E = 1),
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : RankOne.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev PositiveRank :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] (positive_rank : 0 < Module.finrank ℝ E),
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : PositiveRank.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev TangentSubsingleton :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M] [∀ x : M, Subsingleton (TangentSpace I x)],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : TangentSubsingleton.{u, v, w}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

abbrev SmallUniverse :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type 0} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : SmallUniverse.{u, v}) : PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

-- A generic identity with a full contract supplied as input is not a target.
example (good : PointFourClosedManifoldContract.{u, v, w})
    (bad : PointFourClosedManifoldContract.{u, v, w} →
      PointFourClosedManifoldContract.{u, v, w}) :
    PointFourClosedManifoldContract.{u, v, w} := by
  fail_if_success exact @bad
  exact @good

-- Real geometric test: the accepted premise means precisely empty boundary,
-- without requiring the whole model range to be the ambient vector space.
example {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [BoundarylessManifold I M] : I.boundary M = ∅ :=
  ModelWithCorners.Boundaryless.boundary_eq_empty

example {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    (empty_boundary : I.boundary M = ∅) : BoundarylessManifold I M :=
  ModelWithCorners.Boundaryless.of_boundary_eq_empty empty_boundary

end PointFourContractRegression
