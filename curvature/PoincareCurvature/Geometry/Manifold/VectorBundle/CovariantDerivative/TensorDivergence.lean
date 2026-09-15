module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLeibniz
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian

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

/-- The Riemannian metric as a covariant two-tensor section. -/
def riemannianMetricCovariantTwoTensor : ∀ x : M, T₂ x :=
  fun x => (InnerProductSpace.toDual ℝ (TM x)).toContinuousLinearMap

@[simp] theorem riemannianMetricCovariantTwoTensor_apply
    (x : M) (u v : TM x) :
    riemannianMetricCovariantTwoTensor (I := I) (M := M) x u v = inner ℝ u v :=
  rfl

private theorem riemannianMetricCovariantTwoTensor_mdifferentiableAt
    [IsContMDiffRiemannianBundle I 1 E TM] (x : M) :
    MDiffAt (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y
      (riemannianMetricCovariantTwoTensor (I := I) (M := M) y)) x := by
  rcases (show IsContMDiffRiemannianBundle I 1 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have heq : g = riemannianMetricCovariantTwoTensor (I := I) (M := M) := by
    funext y
    ext u v
    exact (hinner y u v).symm
  rw [← heq]
  exact (hg x).mdifferentiableAt one_ne_zero

/-- Metric compatibility is exactly the statement that the induced
connection annihilates the Riemannian metric tensor. -/
theorem covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov
        (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x X u v = 0 := by
  rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt cov
    (riemannianMetricCovariantTwoTensor_mdifferentiableAt (I := I) (E := E) x)]
  have h := hmetric
    (x := x)
    (σ := smoothExtend (I := I) (F := E) (V := TM) x u)
    (τ := smoothExtend (I := I) (F := E) (V := TM) x v)
    (by
      exact ((smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u) x).mdifferentiableAt
        one_ne_zero)
    (by
      exact ((smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v) x).mdifferentiableAt
        one_ne_zero) X
  simp only [riemannianMetricCovariantTwoTensor_apply, smoothExtend_apply] at h ⊢
  linarith

/-- The metric trace of a covariant two-tensor, defined by contraction with
the canonical inverse metric tensor. -/
def covariantTwoTensorTrace
    (h : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun u => h x u
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }
  TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Evaluation of the metric trace in any orthonormal basis. -/
theorem covariantTwoTensorTrace_eq_sum_orthonormalBasis
    (h : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    covariantTwoTensorTrace h x = ∑ i, h x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [covariantTwoTensorTrace,
    InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The existing scalar curvature is exactly the intrinsic metric trace of
the Ricci tensor. -/
theorem covariantTwoTensorTrace_ricciCurvature_eq_scalarCurvature
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) :
    covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (ricciCurvature (cov := cov)) x =
      scalarCurvature (cov := cov) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [covariantTwoTensorTrace_eq_sum_orthonormalBasis (I := I) (E := E) (M := M)
    (ricciCurvature (cov := cov)) x (stdOrthonormalBasis ℝ (TM x)),
    scalarCurvature_eq_sum]

/-- The Ricci tensor packaged in the continuous-bilinear tensor bundle.
Finite dimensionality makes the existing fibrewise linear Ricci maps
continuous; no projection or symmetrization is used. -/
def ricciCovariantTwoTensor
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1] :
    ∀ x : M, T₂ x := fun x =>
  LinearMap.toContinuousLinearMap
    { toFun := fun u => LinearMap.toContinuousLinearMap (ricciCurvature (cov := cov) x u)
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }

@[simp] theorem ricciCovariantTwoTensor_apply
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u v : TM x) :
    ricciCovariantTwoTensor cov x u v = ricciCurvature (cov := cov) x u v :=
  rfl

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

/-- A metric-compatible connection has divergence-free metric tensor. -/
theorem covariantTwoTensorDivergence_riemannianMetric_eq_zero
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) :
    covariantTwoTensorDivergence cov
        (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x = 0 := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [covariantTwoTensorDivergence_eq_sum_orthonormalBasis cov
    (riemannianMetricCovariantTwoTensor (I := I) (M := M)) x
    (stdOrthonormalBasis ℝ (TM x))]
  apply Finset.sum_eq_zero
  intro i hi
  ext v
  exact covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero
    cov hmetric x _ _ v

/-- For a metric-compatible connection, `div(f g) = df`.  This is the
geometric Leibniz identity used to pass from contracted Bianchi to the
divergence-free Einstein tensor. -/
theorem covariantTwoTensorDivergence_smul_riemannianMetric
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (f : M → ℝ) (x : M) (hf : MDiffAt f x) :
    covariantTwoTensorDivergence cov
        (f • riemannianMetricCovariantTwoTensor (I := I) (M := M)) x =
      scalarDifferential (I := I) f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [covariantTwoTensorDivergence_eq_sum_orthonormalBasis cov
    (f • riemannianMetricCovariantTwoTensor (I := I) (M := M)) x b]
  rw [covariantTwoTensorCovariantDerivative_smul_function cov
    (riemannianMetricCovariantTwoTensor_mdifferentiableAt (I := I) (E := E) x) hf]
  ext v
  simp only [sum_apply, add_apply, smul_apply, scalarTensorLeibnizTerm,
    ContinuousLinearMap.smulRight_apply, riemannianMetricCovariantTwoTensor_apply,
    covariantTwoTensorCovariantDerivative_riemannianMetric_eq_zero cov hmetric,
    smul_zero, zero_add, scalarDifferential_apply]
  calc
    (∑ i, scalarDifferential (I := I) f x (b i) • inner ℝ (b i) v) =
        ∑ i, inner ℝ (b i) v • scalarDifferential (I := I) f x (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [smul_eq_mul, mul_comm]
    _ = scalarDifferential (I := I) f x
          (∑ i, inner ℝ (b i) v • b i) := by simp
    _ = scalarDifferential (I := I) f x v := by rw [b.sum_repr' v]

/-- The genuine divergence of the Ricci tensor, formed using the induced
connection and metric contraction. -/
def ricciDivergence
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) : T₁ x :=
  covariantTwoTensorDivergence cov (ricciCovariantTwoTensor cov) x

/-- Orthonormal-basis evaluation of the genuine Ricci divergence. -/
theorem ricciDivergence_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    ricciDivergence cov x =
      ∑ i, covariantTwoTensorCovariantDerivative cov
        (ricciCovariantTwoTensor cov) x (b i) (b i) := by
  exact covariantTwoTensorDivergence_eq_sum_orthonormalBasis cov
    (ricciCovariantTwoTensor cov) x b

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
