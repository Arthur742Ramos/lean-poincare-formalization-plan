module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLinear

/-!
# Leibniz and cutoff-commutator identities for the connection Laplacian

This file proves the geometric product calculation used by a localized
parametrix for the tensor heat equation.  If `g` is a scalar cutoff and `h` a
covariant two-tensor, the first induced connection satisfies the genuine
Leibniz rule

`∇(g h) = g ∇h + dg ⊗ h`.

Differentiating once more and tracing gives

`Δ(g h) = g Δh + [Δ, g]h`,

where the commutator is defined below as the trace of the two explicitly
lower-order terms `dg ⊗ ∇h` and `∇(dg ⊗ h)`.  Thus the identity does not hide
the localization error in a hypothesis or in an abstract operator.
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
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

-- Explicit names keep typeclass search for the nested operator bundles
-- deterministic in clean builds.
local instance leibnizTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance leibnizTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance leibnizThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance leibnizThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance leibnizTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance leibnizTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance leibnizThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance leibnizThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance
local instance leibnizOneFiberAddCommGroup (x : M) :
    AddCommGroup (T₁ x) := ContinuousLinearMap.addCommGroup
local instance leibnizOneFiberModule (x : M) :
    Module ℝ (T₁ x) := ContinuousLinearMap.module
local instance leibnizOneFiberContinuousAdd (x : M) :
    ContinuousAdd (T₁ x) := IsTopologicalAddGroup.toContinuousAdd
local instance leibnizTwoFiberAddCommGroup (x : M) :
    AddCommGroup (T₂ x) := ContinuousLinearMap.addCommGroup
local instance leibnizTwoFiberModule (x : M) :
    Module ℝ (T₂ x) := ContinuousLinearMap.module
local instance leibnizThreeFiberAddCommGroup (x : M) :
    AddCommGroup (T₃ x) := ContinuousLinearMap.addCommGroup
local instance leibnizThreeFiberModule (x : M) :
    Module ℝ (T₃ x) := ContinuousLinearMap.module

/-- The `dg ⊗ h` term in the first covariant derivative of `g h`. -/
def scalarTensorLeibnizTerm (g : M → ℝ) (h : ∀ x : M, T₂ x) :
    ∀ x : M, T₃ x :=
  fun x => (d% g x).smulRight (h x)

/-- The induced connection on covariant two-tensors obeys the scalar
Leibniz rule.  This is derived directly from the defining
`IsCovariantDerivativeOn.leibniz` field. -/
theorem covariantTwoTensorCovariantDerivative_smul_function
    (cov : CovariantDerivative I E TM) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    {x : M}
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (hg : MDiffAt g x) :
    covariantTwoTensorCovariantDerivative cov (g • h) x =
      g x • covariantTwoTensorCovariantDerivative cov h x +
        scalarTensorLeibnizTerm g h x := by
  exact (covariantTwoTensorCovariantDerivative cov).isCovariantDerivativeOn.leibniz hh hg

/-- The twice differentiated scalar product.  The three summands are,
respectively, `g ∇²h`, `dg ⊗ ∇h`, and `∇(dg ⊗ h)`. -/
theorem covariantHessianTwoTensor_smul_function
    (cov : CovariantDerivative I E TM) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    (hh : ∀ x, MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (hg : ∀ x, MDiffAt g x) {x : M}
    (hfirst : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hremainder : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (scalarTensorLeibnizTerm g h y)) x) :
    covariantHessianTwoTensor cov (g • h) x =
      g x • covariantHessianTwoTensor cov h x +
        (d% g x).smulRight
          (covariantTwoTensorCovariantDerivative cov h x) +
        covariantThreeTensorCovariantDerivative cov
          (scalarTensorLeibnizTerm g h) x := by
  have heq : covariantTwoTensorCovariantDerivative cov (g • h) =
      g • covariantTwoTensorCovariantDerivative cov h +
        scalarTensorLeibnizTerm g h := by
    funext y
    exact covariantTwoTensorCovariantDerivative_smul_function cov (hh y) (hg y)
  have hscaled : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      ((g • covariantTwoTensorCovariantDerivative cov h) y)) x :=
    (hg x).smul_section hfirst
  unfold covariantHessianTwoTensor
  rw [heq]
  rw [(covariantThreeTensorCovariantDerivative cov).isCovariantDerivativeOn.add
    hscaled hremainder]
  rw [(covariantThreeTensorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hfirst (hg x)]

/-- The explicit lower-order cutoff commutator `[Δ, g]h`, evaluated using an
orthonormal basis.  Its two terms
contain at most one derivative of `h`: `dg ⊗ ∇h` and `∇(dg ⊗ h)`.
The theorem below identifies it with the intrinsic difference, and hence also
proves that it is independent of this basis. -/
def connectionLaplacianCutoffCommutatorWithBasis {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I E TM) (g : M → ℝ)
    (h : ∀ x : M, T₂ x) (x : M) (b : OrthonormalBasis ι ℝ (TM x)) : T₂ x :=
  ∑ i, ((d% g x).smulRight
      (covariantTwoTensorCovariantDerivative cov h x) +
      covariantThreeTensorCovariantDerivative cov
        (scalarTensorLeibnizTerm g h) x) (b i) (b i)

/-- **Connection-Laplacian cutoff identity in an arbitrary orthonormal
basis.**  Multiplication by a smooth
scalar cutoff commutes with the principal second-order part, and the exact
failure to commute is the explicit lower-order term above. -/
theorem connectionLaplacian_smul_function_withBasis {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I E TM) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    (hh : ∀ x, MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (hg : ∀ x, MDiffAt g x) {x : M}
    (hfirst : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hremainder : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (scalarTensorLeibnizTerm g h y)) x) :
    ∀ (b : OrthonormalBasis ι ℝ (TM x)),
    connectionLaplacian cov (g • h) x =
      g x • connectionLaplacian cov h x +
        connectionLaplacianCutoffCommutatorWithBasis cov g h x b := by
  intro b
  rw [connectionLaplacian_eq_sum_orthonormalBasis cov (g • h) x b,
    connectionLaplacian_eq_sum_orthonormalBasis cov h x b]
  simp_rw [covariantHessianTwoTensor_smul_function cov hh hg hfirst hremainder]
  simp only [add_apply, smul_apply, Finset.sum_add_distrib, Finset.smul_sum]
  simp only [connectionLaplacianCutoffCommutatorWithBasis, add_apply,
    ContinuousLinearMap.smulRight_apply, Finset.sum_add_distrib]
  abel

/-- The basis-independent cutoff commutator, written with the canonical
standard orthonormal basis. -/
def connectionLaplacianCutoffCommutator
    (cov : CovariantDerivative I E TM) (g : M → ℝ)
    (h : ∀ x : M, T₂ x) (x : M) : T₂ x :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  connectionLaplacianCutoffCommutatorWithBasis cov g h x
    (stdOrthonormalBasis ℝ (TM x))

/-- **Canonical connection-Laplacian cutoff identity.** -/
theorem connectionLaplacian_smul_function
    (cov : CovariantDerivative I E TM) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    (hh : ∀ x, MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (hg : ∀ x, MDiffAt g x) {x : M}
    (hfirst : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hremainder : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
      (scalarTensorLeibnizTerm g h y)) x) :
    connectionLaplacian cov (g • h) x =
      g x • connectionLaplacian cov h x +
        connectionLaplacianCutoffCommutator cov g h x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  exact connectionLaplacian_smul_function_withBasis cov hh hg hfirst hremainder
    (stdOrthonormalBasis ℝ (TM x))

end CovariantDerivative
