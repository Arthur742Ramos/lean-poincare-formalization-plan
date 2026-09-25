module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Minimal tangent-space structure for covariant-derivative geometry

This module isolates the tangent-space instances and Riemannian-metric extensionality
needed by the intrinsic tensor-heat development. The broader section-space API remains
in `RiemannianSection`.
-/

@[expose] public noncomputable section

open scoped Bundle Manifold ContDiff

namespace PoincareCurvature

/-!
The tangent fiber `TangentSpace I x` is definitionally the model vector space `F`, but the
class search path does not unfold it while synthesizing normed-space structure.  These low-priority
instances expose that structure for fiberwise continuous-linear constructions on tangent bilinear
forms.
-/

instance (priority := 70) instNormedAddCommGroupTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    NormedAddCommGroup (TangentSpace I x) := by
  change NormedAddCommGroup F
  infer_instance

instance (priority := 100) instNormedSpaceTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    NormedSpace ℝ (TangentSpace I x) := by
  change NormedSpace ℝ F
  infer_instance

instance (priority := 100) instIsTopologicalAddGroupTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    IsTopologicalAddGroup (TangentSpace I x) := by
  change IsTopologicalAddGroup F
  infer_instance

instance (priority := 100) instT2SpaceTangentSpace
    {M F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ F H) [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    T2Space (TangentSpace I x) := by
  change T2Space F
  infer_instance

end PoincareCurvature

namespace Bundle

section Smooth

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

@[ext] theorem ContMDiffRiemannianMetric.ext
    {g g' : ContMDiffRiemannianMetric IB n F V}
    (hinner : ∀ x : B, ∀ u v : V x, g.inner x u v = g'.inner x u v) :
    g = g' := by
  have hinner' : g.inner = g'.inner := by
    funext x
    ext u v
    exact hinner x u v
  cases g
  cases g'
  simp at hinner' ⊢
  exact hinner'

end Smooth

end Bundle
