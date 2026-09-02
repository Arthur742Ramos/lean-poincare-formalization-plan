import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Riemannian.Basic

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V I]

local notation "TM" => (TangentSpace I : M → Type _)

variable (cov : CovariantDerivative I F V) [cov.ContMDiffCovariantDerivative 1]

/-- The raw curvature commutator is pointwise linear in its left tangent-field slot. -/
theorem raw_curvature_left_tensoriality
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : MDiffAt f x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (f • X) Y σ x = f x • cov.curvatureAux X Y σ x := by
  sorry

/-- The raw curvature commutator is pointwise linear in its middle tangent-field slot. -/
theorem raw_curvature_middle_tensoriality
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : MDiffAt f x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (f • Y) σ x = f x • cov.curvatureAux X Y σ x := by
  sorry

/-- The raw curvature commutator is pointwise linear in its bundle-section slot. -/
theorem raw_curvature_right_tensoriality
    {f : M → ℝ} {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X Y (f • σ) x = f x • cov.curvatureAux X Y σ x := by
  sorry

set_option maxHeartbeats 1000000 in
/-- Metric compatibility makes the raw curvature commutator skew-adjoint. -/
theorem raw_curvature_metric_skew_adjointness
    [RiemannianBundle V] [IsContMDiffRiemannianBundle I 2 F V]
    (hmetric :
      ∀ {x : M} {σ τ : Π x : M, V x},
        MDiffAt (T% σ) x → MDiffAt (T% τ) x →
          ∀ u : TangentSpace I x,
            mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
              inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u))
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦ TotalSpace.mk' F y (τ y))) :
    inner ℝ (cov.curvatureAux X Y σ x) (τ x) +
      inner ℝ (σ x) (cov.curvatureAux X Y τ x) = 0 := by
  sorry

end PoincareCurvature.Palomar
