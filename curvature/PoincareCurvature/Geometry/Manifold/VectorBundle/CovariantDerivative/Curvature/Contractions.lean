module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Ricci and scalar curvature

This file contracts the bundled curvature tensor on the tangent bundle to produce
Ricci curvature and scalar curvature.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

/-- The endomorphism whose trace defines Ricci curvature. -/
noncomputable def ricciEndomorphism (x : M) (u w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := curvatureTensor (cov := cov) x v u w
  map_add' v v' := by
    simpa using congrArg (fun f => f u w) ((curvatureTensor (cov := cov) x).map_add v v')
  map_smul' c v := by
    simpa using congrArg (fun f => f u w) ((curvatureTensor (cov := cov) x).map_smul c v)

@[simp]
lemma ricciEndomorphism_apply (x : M) (u w v : TangentSpace I x) :
    ricciEndomorphism (cov := cov) x u w v = curvatureTensor (cov := cov) x v u w := rfl

@[simp]
lemma ricciEndomorphism_add_right (x : M) (u w w' : TangentSpace I x) :
    ricciEndomorphism (cov := cov) x u (w + w') =
      ricciEndomorphism (cov := cov) x u w + ricciEndomorphism (cov := cov) x u w' := by
  ext v
  simpa [ricciEndomorphism] using
    ((curvatureTensor (cov := cov) x v u).map_add w w')

@[simp]
lemma ricciEndomorphism_smul_right (x : M) (u w : TangentSpace I x) (c : ℝ) :
    ricciEndomorphism (cov := cov) x u (c • w) =
      c • ricciEndomorphism (cov := cov) x u w := by
  ext v
  simpa [ricciEndomorphism] using
    ((curvatureTensor (cov := cov) x v u).map_smul c w)

@[simp]
lemma ricciEndomorphism_add_left (x : M) (u u' w : TangentSpace I x) :
    ricciEndomorphism (cov := cov) x (u + u') w =
      ricciEndomorphism (cov := cov) x u w + ricciEndomorphism (cov := cov) x u' w := by
  ext v
  simpa [ricciEndomorphism] using
    congrArg (fun f => f w) ((curvatureTensor (cov := cov) x v).map_add u u')

@[simp]
lemma ricciEndomorphism_smul_left (x : M) (u w : TangentSpace I x) (c : ℝ) :
    ricciEndomorphism (cov := cov) x (c • u) w =
      c • ricciEndomorphism (cov := cov) x u w := by
  ext v
  simpa [ricciEndomorphism] using
    congrArg (fun f => f w) ((curvatureTensor (cov := cov) x v).map_smul c u)

/-- Ricci curvature obtained by tracing the first/output slots of the curvature tensor. -/
noncomputable def ricciCurvature (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ := by
  refine
    { toFun := fun u ↦
        { toFun := fun w ↦ LinearMap.trace ℝ (TangentSpace I x) (ricciEndomorphism (cov := cov) x u w)
          map_add' := by
            intro w w'
            simpa [ricciEndomorphism_add_right] using
              (LinearMap.trace ℝ (TangentSpace I x)).map_add
                (ricciEndomorphism (cov := cov) x u w)
                (ricciEndomorphism (cov := cov) x u w')
          map_smul' := by
            intro c w
            simpa [ricciEndomorphism_smul_right] using
              (LinearMap.trace ℝ (TangentSpace I x)).map_smul c
                (ricciEndomorphism (cov := cov) x u w) }
      map_add' := by
        intro u u'
        ext w
        simpa [ricciEndomorphism_add_left] using
          (LinearMap.trace ℝ (TangentSpace I x)).map_add
            (ricciEndomorphism (cov := cov) x u w)
            (ricciEndomorphism (cov := cov) x u' w)
      map_smul' := by
        intro c u
        ext w
        simpa [ricciEndomorphism_smul_left] using
          (LinearMap.trace ℝ (TangentSpace I x)).map_smul c
            (ricciEndomorphism (cov := cov) x u w) }

@[simp]
lemma ricciCurvature_apply (x : M) (u w : TangentSpace I x) :
    ricciCurvature (cov := cov) x u w =
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndomorphism (cov := cov) x u w) := rfl

/-- On a zero-dimensional tangent fiber, every Ricci component vanishes. -/
lemma ricciCurvature_eq_zero_of_subsingleton_tangent
    (x : M) [Subsingleton (TangentSpace I x)] (u w : TangentSpace I x) :
    ricciCurvature (cov := cov) x u w = 0 := by
  rw [ricciCurvature_apply]
  have hEnd : ricciEndomorphism (cov := cov) x u w = 0 := by
    ext v
    exact Subsingleton.elim _ _
  rw [hEnd]
  exact LinearMap.map_zero (LinearMap.trace ℝ (TangentSpace I x))

/-- Scalar curvature obtained by tracing Ricci curvature against an orthonormal basis. -/
noncomputable def scalarCurvature (x : M) : ℝ := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  exact
    ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
      ricciCurvature (cov := cov) x
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)

lemma scalarCurvature_eq_sum (x : M) :
    scalarCurvature (cov := cov) x =
      (by
        letI : FiniteDimensional ℝ (TangentSpace I x) :=
          VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
        exact
          ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
            ricciCurvature (cov := cov) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  rfl

/-- On a zero-dimensional tangent fiber, scalar curvature vanishes. -/
lemma scalarCurvature_eq_zero_of_subsingleton_tangent
    (x : M) [Subsingleton (TangentSpace I x)] :
    scalarCurvature (cov := cov) x = 0 := by
  rw [scalarCurvature_eq_sum]
  simp [ricciCurvature_eq_zero_of_subsingleton_tangent (cov := cov) x]

section LeviCivita

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov'.ContMDiffCovariantDerivative 1]

/-- Ricci curvature depends only on the Riemannian metric, not on the chosen Levi-Civita
connection used to compute it. -/
theorem ricciCurvature_eq_of_isLeviCivita
    (hcov : CovariantDerivative.IsLeviCivita cov)
    (hcov' : CovariantDerivative.IsLeviCivita cov')
    (x : M) (u w : TangentSpace I x) :
    ricciCurvature (cov := cov) x u w = ricciCurvature (cov := cov') x u w := by
  have hEnd :
      ricciEndomorphism (cov := cov) x u w =
        ricciEndomorphism (cov := cov') x u w := by
    ext v
    simpa [ricciEndomorphism_apply] using
      curvatureTensor_eq_of_isLeviCivita
        (I := I) (M := M) (cov := cov) (cov' := cov') hcov hcov' x v u w
  simpa [ricciCurvature_apply] using
    congrArg (LinearMap.trace ℝ (TangentSpace I x)) hEnd

/-- Scalar curvature depends only on the Riemannian metric, not on the chosen Levi-Civita
connection used to compute it. -/
theorem scalarCurvature_eq_of_isLeviCivita
    (hcov : CovariantDerivative.IsLeviCivita cov)
    (hcov' : CovariantDerivative.IsLeviCivita cov')
    (x : M) :
    scalarCurvature (cov := cov) x = scalarCurvature (cov := cov') x := by
  rw [scalarCurvature_eq_sum, scalarCurvature_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact ricciCurvature_eq_of_isLeviCivita
    (I := I) (M := M) (cov := cov) (cov' := cov') hcov hcov' x
    ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
    ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)

end LeviCivita

end CovariantDerivative
