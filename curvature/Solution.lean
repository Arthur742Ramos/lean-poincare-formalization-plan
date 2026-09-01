import PoincareCurvature.Basic

public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

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
  exact CovariantDerivative.curvatureAux_swap cov X Y σ

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
  exact CovariantDerivative.difference_eq_zero_of_isLeviCivita cov cov' hcov hcov'

end PoincareCurvature.Palomar
