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

/-- The bundle of real bilinear forms on the fibers of V. -/
abbrev BilinearFormBundle {B : Type*} {V : B → Type*}
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] :
    B → Type _ :=
  fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ

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

section BilinearFormCoordinates

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

set_option synthInstance.maxHeartbeats 100000

/-- In preferred local coordinates, a bundled bilinear form evaluates by pulling the model vectors
back through the inverse fiber trivialization. -/
lemma trivializationAt_bilinearFormBundle_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x) (u v : F) :
    ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u v =
      B (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u)
        (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm v) := by
  let e : W x ≃L[ℝ] F := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  let eDual : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0).continuousLinearEquivAt ℝ x
      (by simpa using hx) : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ))
  have hdual (φ : W x →L[ℝ] ℝ) :
      ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2) v =
        φ (e.symm v) := by
    have htrivDual := hom_trivializationAt_apply (σ := RingHom.id ℝ)
        (F₁ := F) (E₁ := W) (F₂ := ℝ) (E₂ := fun _ : M => ℝ) x0 ⟨x, φ⟩
    have hφ :
        (trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2 =
          φ.comp (e.symm : F →L[ℝ] W x) := by
      simpa [e, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htrivDual
    have hv := congrArg (fun ψ : F →L[ℝ] ℝ => ψ v) hφ
    simpa [e] using hv
  have htriv := hom_trivializationAt_apply (σ := RingHom.id ℝ)
      (F₁ := F) (E₁ := W) (F₂ := F →L[ℝ] ℝ) (E₂ := fun y => W y →L[ℝ] ℝ) x0 ⟨x, B⟩
  have hB :
      (trivializationAt BilF BilW x0 ⟨x, B⟩).2 =
        eDual.comp (B.comp (e.symm : F →L[ℝ] W x)) := by
    simpa [e, eDual, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htriv
  have hu := congrArg (fun ψ : F →L[ℝ] F →L[ℝ] ℝ => ψ u v) hB
  simpa [hdual, e, eDual] using hu

/-- Preferred bilinear-form bundle trivializations are fiberwise linear. This explicit instance
avoids typeclass-search ambiguity from the nested hom-bundle construction when using coordinate
changes for bilinear-form coordinates. -/
lemma trivializationAt_bilinearFormBundle_isLinear (x0 : M) :
    (trivializationAt BilF BilW x0).IsLinear ℝ where
  linear x hx := by
    have hxW : x ∈ (trivializationAt F W x0).baseSet := by
      simpa using hx
    refine ⟨?_, ?_⟩
    · intro B C
      ext u v
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW (B + C) u v]
      simp only [ContinuousLinearMap.add_apply]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW B u v]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW C u v]
    · intro c B
      ext u v
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW (c • B) u v]
      simp only [ContinuousLinearMap.smul_apply]
      rw [trivializationAt_bilinearFormBundle_apply_eq (F := F) (W := W)
        x0 x hxW B u v]

end BilinearFormCoordinates

end Bundle
