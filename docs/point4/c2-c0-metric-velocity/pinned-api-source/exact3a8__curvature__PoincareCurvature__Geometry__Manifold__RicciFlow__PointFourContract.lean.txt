module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Closed-manifold completion contract for Point 4

This is an expected **type**, not a construction of a Ricci flow. The canonical
`RicciFlow.intrinsicLocalExistenceUniquenessFamily_pointFour` is still absent.
The only approved geometric scope correction is `BoundarylessManifold I M`:
compact manifolds without boundary, with the model `I` still arbitrary.

The existing `IntrinsicLocalExistenceUniquenessFamily` is used literally, so its
all-C² initial data, weak candidate regularity, ordinary component derivatives
and common closed time intervals are unchanged. The general reusable interfaces
in `LocalExistence` remain available on manifolds with boundary as well.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

universe u v w

/-- The full expected type of the eventual Point-4 construction. No analytic,
solver, chart, package, rank or model-boundary premise is supplied. This alias
records an obligation; no inhabitant of it is defined here. -/
abbrev PointFourClosedManifoldContract :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

end RicciFlow
