module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteSum

/-!
# Local reconstruction of covariant two-tensors

This file gives the algebraic synthesis map used by the manifold tensor-heat
parametrix. A finite matrix of coefficients is first made into a continuous
bilinear form on the model space and then pulled back through the genuine
tangent-bundle trivialization. On the trivialization domain, evaluating the
reconstructed tensor on the actual local frame recovers the original matrix
entry exactly.

The reconstruction is totalized by zero outside the trivialization domain.
Later a partition-of-unity function whose topological support lies inside that
domain erases this arbitrary branch before differentiability is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Explicit names keep nested operator-space synthesis deterministic.
local instance reconstructionTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance reconstructionTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

/-- The continuous coordinate functional of a finite basis. -/
def basisCoordinateCLM (b : Module.Basis ι ℝ E) (i : ι) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem basisCoordinateCLM_apply_basis
    (b : Module.Basis ι ℝ E) (i j : ι) :
    basisCoordinateCLM b i (b j) = if j = i then 1 else 0 := by
  change (b.repr (b j)) i = if j = i then 1 else 0
  rw [b.repr_self, Finsupp.single_apply]

/-- A finite matrix, regarded as a continuous bilinear form in the chosen
basis. -/
def matrixBilinearCLM (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, (basisCoordinateCLM b i).smulRight
    (∑ j, q i j • basisCoordinateCLM b j)

@[simp]
theorem matrixBilinearCLM_apply_basis
    (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) (i j : ι) :
    matrixBilinearCLM b q (b i) (b j) = q i j := by
  classical
  simp [matrixBilinearCLM, basisCoordinateCLM, Finsupp.single_apply]

/-- The tangent-fibre coordinate isomorphism as a continuous linear map. -/
def tangentCoordCLM
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) : TM x →L[ℝ] E :=
  (e.linearEquivAt ℝ x hx).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem tangentCoordCLM_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) (v : TM x) :
    tangentCoordCLM e x hx v = (e (TotalSpace.mk' E x v)).2 := by
  exact e.linearEquivAt_apply (R := ℝ) x hx v

@[simp]
theorem tangentCoordCLM_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    tangentCoordCLM e x hx (e.localFrame b i x) = b i := by
  rw [tangentCoordCLM_apply e x hx,
    e.localFrame_apply_of_mem_baseSet b hx]
  exact congrArg Prod.snd (e.apply_mk_symm hx (b i))

/-- Reconstruct a covariant two-tensor from its matrix in the local tangent
frame. Outside the trivialization domain it is totalized by zero. -/
def localTensorOfMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) : ∀ x : M, T₂ x := by
  classical
  exact fun x => if hx : x ∈ e.baseSet then
    (matrixBilinearCLM b (q x)).bilinearComp
      (tangentCoordCLM e x hx) (tangentCoordCLM e x hx)
  else 0

@[simp]
theorem localTensorOfMatrix_apply_of_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {x : M} (hx : x ∈ e.baseSet)
    (v w : TM x) :
    localTensorOfMatrix e b q x v w =
      matrixBilinearCLM b (q x) (tangentCoordCLM e x hx v)
        (tangentCoordCLM e x hx w) := by
  classical
  simp [localTensorOfMatrix, hx]

/-- Evaluation on the genuine local tangent frame exactly recovers the input
coefficient matrix. -/
@[simp]
theorem localTensorOfMatrix_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    localTensorOfMatrix e b q x (e.localFrame b i x)
        (e.localFrame b j x) = q x i j := by
  rw [localTensorOfMatrix_apply_of_mem e b q hx]
  rw [tangentCoordCLM_localFrame e b hx i,
    tangentCoordCLM_localFrame e b hx j]
  exact matrixBilinearCLM_apply_basis b (q x) i j

/-- Symmetric coefficient matrices reconstruct symmetric covariant tensors. -/
theorem localTensorOfMatrix_isSymmetric
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) (hq : ∀ x i j, q x i j = q x j i) :
    ∀ x (v w : TM x), localTensorOfMatrix e b q x v w =
      localTensorOfMatrix e b q x w v := by
  intro x v w
  classical
  by_cases hx : x ∈ e.baseSet
  · simp only [localTensorOfMatrix, dif_pos hx,
      ContinuousLinearMap.bilinearComp_apply]
    simp only [matrixBilinearCLM, _root_.sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, _root_.smul_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hq x i j]
    ring
  · simp [localTensorOfMatrix, hx]

/-- Multiply the reconstructed local tensor by a global scalar cutoff. This is
the summand used in the finite partition-of-unity synthesis. -/
def cutoffLocalTensorOfMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ) : ∀ x : M, T₂ x :=
  fun x => ψ x • localTensorOfMatrix e b q x

/-- On the genuine local frame, cutoff reconstruction is exactly scalar
multiplication of the input matrix. -/
@[simp]
theorem cutoffLocalTensorOfMatrix_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    cutoffLocalTensorOfMatrix e b ψ q x (e.localFrame b i x)
        (e.localFrame b j x) = ψ x * q x i j := by
  simp only [cutoffLocalTensorOfMatrix, _root_.smul_apply,
    smul_eq_mul]
  rw [localTensorOfMatrix_localFrame e b q hx]

/-- Cutoff reconstruction preserves pointwise symmetry. -/
theorem cutoffLocalTensorOfMatrix_isSymmetric
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    (hq : ∀ x i j, q x i j = q x j i) :
    ∀ x (v w : TM x), cutoffLocalTensorOfMatrix e b ψ q x v w =
      cutoffLocalTensorOfMatrix e b ψ q x w v := by
  intro x v w
  simp only [cutoffLocalTensorOfMatrix, _root_.smul_apply,
    smul_eq_mul]
  rw [localTensorOfMatrix_isSymmetric e b q hq x v w]

/-- Reconstruction is additive in the coefficient matrix. -/
theorem localTensorOfMatrix_add
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q r : M → ι → ι → ℝ) :
    localTensorOfMatrix e b (q + r) =
      localTensorOfMatrix e b q + localTensorOfMatrix e b r := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  classical
  by_cases hx : x ∈ e.baseSet <;>
    simp [localTensorOfMatrix, matrixBilinearCLM, hx, add_mul]
  simp_rw [Finset.sum_add_distrib, mul_add]
  exact Finset.sum_add_distrib

/-- Reconstruction commutes with scalar multiplication of the coefficient
matrix. -/
theorem localTensorOfMatrix_smul
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (c : ℝ) (q : M → ι → ι → ℝ) :
    localTensorOfMatrix e b (c • q) = c • localTensorOfMatrix e b q := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  classical
  by_cases hx : x ∈ e.baseSet <;>
    simp [localTensorOfMatrix, matrixBilinearCLM, hx, mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end AnalyticPDE
end RicciFlow
