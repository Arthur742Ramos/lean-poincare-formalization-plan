module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Intrinsic divergence of covariant tensors

This file defines the divergence of covectors and covariant two-tensors by
contracting their genuine induced covariant derivatives with the canonical
inverse metric tensor.  It also defines the double divergence of a covariant
two-tensor.  The definitions are basis independent; orthonormal-basis formulas
are proved as evaluation lemmas.

These operators are the geometric contractions required by the scalar
curvature first-variation formula and the contracted second Bianchi identity.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- The divergence of a covector is the metric trace of its induced
covariant derivative. -/
def covectorDivergence (cov : CovariantDerivative I E TM)
    (α : ∀ x : M, T₁ x) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := covectorCovariantDerivative cov α x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }
  TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Evaluation of covector divergence in any orthonormal basis. -/
theorem covectorDivergence_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (α : ∀ x : M, T₁ x) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    covectorDivergence cov α x =
      ∑ i, covectorCovariantDerivative cov α x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [covectorDivergence,
    InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The divergence of a covariant two-tensor, tracing the derivative
direction against its first tensor slot and retaining the second slot. -/
def covariantTwoTensorDivergence (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x) (x : M) : T₁ x :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := covariantTwoTensorCovariantDerivative cov h x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] T₁ x :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w z
        simp
      map_smul' := by
        intro c u
        ext w z
        simp }
  TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Evaluation of two-tensor divergence in any orthonormal basis. -/
theorem covariantTwoTensorDivergence_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    covariantTwoTensorDivergence cov h x =
      ∑ i, covariantTwoTensorCovariantDerivative cov h x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [covariantTwoTensorDivergence,
    InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem covariantTwoTensorDivergence_apply
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M)
    (v : TM x) :
    covariantTwoTensorDivergence cov h x v =
      letI : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let b := stdOrthonormalBasis ℝ (TM x)
      ∑ i : Fin (Module.finrank ℝ (TM x)),
        covariantTwoTensorCovariantDerivative cov h x (b i) (b i) v := by
  rw [covariantTwoTensorDivergence_eq_sum_orthonormalBasis cov h x
    (stdOrthonormalBasis ℝ (TM x))]
  simp

/-- The double divergence `div(div h)` of a covariant two-tensor. -/
def covariantTwoTensorDoubleDivergence
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M) : ℝ :=
  covectorDivergence cov (covariantTwoTensorDivergence cov h) x

/-- Orthonormal-basis formula for the outer contraction in the double
divergence. -/
theorem covariantTwoTensorDoubleDivergence_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    covariantTwoTensorDoubleDivergence cov h x =
      ∑ i, covectorCovariantDerivative cov
        (covariantTwoTensorDivergence cov h) x (b i) (b i) := by
  exact covectorDivergence_eq_sum_orthonormalBasis cov
    (covariantTwoTensorDivergence cov h) x b

end CovariantDerivative
