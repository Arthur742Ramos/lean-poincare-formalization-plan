import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

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
  exact CovariantDerivative.curvatureAux_smul_fun_left_apply cov hf hX hY hσ

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
  exact CovariantDerivative.curvatureAux_smul_fun_middle_apply cov hf hX hY hσ

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
  exact CovariantDerivative.curvatureAux_smul_fun_right_apply cov hf hX hY hσ

set_option maxHeartbeats 1000000 in
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
  exact CovariantDerivative.curvatureAux_inner_add_eq_zero_of_metricCompatible
    cov hmetric hX hY hσ hτ

end PoincareCurvature.Palomar
