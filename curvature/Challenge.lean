import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorField.LieBracket

public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

section CovariantDerivativeDefinitions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

namespace CovariantDerivative

variable (cov : CovariantDerivative I F V)

def along (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

def curvatureAux (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

end CovariantDerivative

end CovariantDerivativeDefinitions

section StaticLeviCivita

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace CovariantDerivative

def IsTorsionFree (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0

def IsMetricCompatibleTangent (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        extDerivFun (fun y ↦ ⟪σ y, τ y⟫) x u =
          ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫

def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

end CovariantDerivative

end StaticLeviCivita

namespace PoincareCurvature.Palomar

theorem curvature_commutator_skew
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.curvatureAux X Y σ = -cov.curvatureAux Y X σ := by
  sorry

theorem levi_civita_uniqueness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita) :
    CovariantDerivative.difference cov cov' = 0 := by
  sorry

end PoincareCurvature.Palomar
