import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Riemannian.Basic

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

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

variable (cov : CovariantDerivative I F V)

def along (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

abbrev curvatureAux (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]

/-- An affine connection is torsion-free if its torsion tensor vanishes. -/
def IsTorsionFree (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.torsion = 0

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Metric compatibility for an affine connection on the tangent bundle. -/
def IsMetricCompatibleTangent
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

/-- A Levi–Civita connection is torsion-free and metric-compatible. -/
def IsLeviCivita (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

end CovariantDerivative

namespace CovariantDerivative

/-- The canonical bundled curvature tensor supplied by the solution. -/
noncomputable def curvatureTensor
    {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace ℝ E]
    {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
    [hT2 : T2Space M] [hFinite : FiniteDimensional ℝ E] [hComplete : CompleteSpace E]
    [hManifold : IsManifold I ∞ M]
    {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace ℝ F]
    {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
    [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module ℝ (V x)]
    [hVTop : ∀ x, TopologicalSpace (V x)]
    [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
    [hVSMul : ∀ x, ContinuousSMul ℝ (V x)] [hFiber : FiberBundle F V]
    [hVector : VectorBundle ℝ F V] [hContMDiff : ContMDiffVectorBundle 2 F V I]
    (cov : CovariantDerivative I F V)
    [hCovC1 : cov.ContMDiffCovariantDerivative 1] (x : M) :
    (TangentSpace I x) →ₗ[ℝ] (TangentSpace I x) →ₗ[ℝ] V x →ₗ[ℝ] V x := by
  let keepEGroup := hEGroup
  let keepESpace := hESpace
  let keepHTop := hHTop
  let keepMTop := hMTop
  let keepCharted := hCharted
  let keepT2 := hT2
  let keepFinite := hFinite
  let keepComplete := hComplete
  let keepManifold := hManifold
  let keepFGroup := hFGroup
  let keepFSpace := hFSpace
  let keepTotalTop := hTotalTop
  let keepVAdd := hVAdd
  let keepVModule := hVModule
  let keepVTop := hVTop
  let keepVAddTop := hVAddTop
  let keepVSMul := hVSMul
  let keepFiber := hFiber
  let keepVector := hVector
  let keepContMDiff := hContMDiff
  let keepCovC1 := hCovC1
  sorry

/-- Ricci curvature is the trace contraction of the bundled curvature tensor. -/
noncomputable def ricciCurvature
    {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace ℝ E]
    [hFinite : FiniteDimensional ℝ E] [hComplete : CompleteSpace E]
    {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
    [hT2 : T2Space M] [hManifold : IsManifold I ∞ M]
    [hContMDiff : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [hRiemannian : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hCovC1 : cov.ContMDiffCovariantDerivative 1] (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ := by
  let keepEGroup := hEGroup
  let keepESpace := hESpace
  let keepFinite := hFinite
  let keepComplete := hComplete
  let keepHTop := hHTop
  let keepMTop := hMTop
  let keepCharted := hCharted
  let keepT2 := hT2
  let keepManifold := hManifold
  let keepContMDiff := hContMDiff
  let keepRiemannian := hRiemannian
  let keepCovC1 := hCovC1
  sorry

/-- Scalar curvature is the orthonormal trace of Ricci curvature. -/
noncomputable def scalarCurvature
    {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace ℝ E]
    [hFinite : FiniteDimensional ℝ E] [hComplete : CompleteSpace E]
    {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
    [hT2 : T2Space M] [hManifold : IsManifold I ∞ M]
    [hContMDiff : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [hRiemannian : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hCovC1 : cov.ContMDiffCovariantDerivative 1] (x : M) : ℝ := by
  let keepEGroup := hEGroup
  let keepESpace := hESpace
  let keepFinite := hFinite
  let keepComplete := hComplete
  let keepHTop := hHTop
  let keepMTop := hMTop
  let keepCharted := hCharted
  let keepT2 := hT2
  let keepManifold := hManifold
  let keepContMDiff := hContMDiff
  let keepRiemannian := hRiemannian
  let keepCovC1 := hCovC1
  sorry

end CovariantDerivative

namespace PoincareCurvature.Palomar

open Bundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A smooth finite-dimensional Riemannian manifold admits a smooth Levi–Civita connection. -/
theorem exists_contMDiffLeviCivitaConnection
    [SigmaCompactSpace M]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I : M → Type _),
      cov.IsLeviCivita ∧ cov.ContMDiffCovariantDerivative 1 := by
  sorry

section CurvatureTensor

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative 1] [cov'.ContMDiffCovariantDerivative 1]

/-- The bundled curvature tensor is independent of the chosen Levi–Civita connection. -/
theorem curvatureTensor_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) (u v w : TangentSpace I x) :
    CovariantDerivative.curvatureTensor (cov := cov) x u v w =
      CovariantDerivative.curvatureTensor (cov := cov') x u v w := by
  sorry

end CurvatureTensor

section Ricci

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

/-- Ricci curvature of a Levi–Civita connection is symmetric. -/
theorem ricciCurvature_symm_of_isLeviCivita
    (hLevi : cov.IsLeviCivita)
    (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      CovariantDerivative.ricciCurvature (cov := cov) x w u := by
  sorry

section Invariance

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov'.ContMDiffCovariantDerivative 1]

/-- Ricci curvature depends only on the Riemannian metric, not on the chosen Levi–Civita connection. -/
theorem ricciCurvature_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      CovariantDerivative.ricciCurvature (cov := cov') x u w := by
  sorry

/-- Scalar curvature depends only on the Riemannian metric, not on the chosen Levi–Civita connection. -/
theorem scalarCurvature_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) :
    CovariantDerivative.scalarCurvature (cov := cov) x =
      CovariantDerivative.scalarCurvature (cov := cov') x := by
  sorry

end Invariance
end Ricci

end PoincareCurvature.Palomar
