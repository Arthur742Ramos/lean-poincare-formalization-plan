import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

section CovariantDerivativeDefinitions

variable {𝕜 : Type*} [hField : NontriviallyNormedField 𝕜]
  {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace 𝕜 E]
  {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
  {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace 𝕜 F]
  {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
  [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module 𝕜 (V x)]
  [hVTop : ∀ x, TopologicalSpace (V x)] [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
  [hVSMul : ∀ x, ContinuousSMul 𝕜 (V x)] [hFiber : FiberBundle F V]
  [hVector : VectorBundle 𝕜 F V]

namespace CovariantDerivative

variable (cov : CovariantDerivative I F V)

def along (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

abbrev curvatureAux (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

end CovariantDerivative

end CovariantDerivativeDefinitions

namespace PoincareCurvature.Palomar

/- The raw form of the second Bianchi identity is kept local to the Palomar
surface so that Challenge and Solution expose the same small definition without
importing the implementation module. -/
def rawSecondBianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  cov.along X (cov.curvatureAux Y Z W) -
    cov.curvatureAux (cov.along X Y) Z W -
    cov.curvatureAux Y (cov.along X Z) W -
    cov.curvatureAux Y Z (cov.along X W)

/-- The pointwise first Bianchi identity for a torsion-free affine connection. -/
theorem first_bianchi_raw_of_torsion_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y))) :
    cov.curvatureAux X Y Z x + cov.curvatureAux Y Z X x + cov.curvatureAux Z X Y x = 0 := by
  sorry

/-- The pointwise raw differential second Bianchi identity for a torsion-free affine connection. -/
theorem second_bianchi_raw_of_torsion_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    [IsManifold I (minSmoothness ℝ 2) M]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I (minSmoothness ℝ 4) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [IsManifold I ((3 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (W y))) :
    rawSecondBianchi cov X Y Z W x + rawSecondBianchi cov Y Z X W x +
      rawSecondBianchi cov Z X Y W x = 0 := by
  sorry

end PoincareCurvature.Palomar
