module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm

/-!
# Pointwise norm square of a covariant two-tensor

The Hilbert--Schmidt square is the sum of squared tensor components in a
fibrewise orthonormal basis. Its nonnegativity and definiteness are the
algebraic part of the tensor-heat maximum-principle argument. The Bochner
evolution identity remains a separate differential theorem.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- Pointwise Hilbert--Schmidt square of an arbitrary covariant two-tensor. -/
def covariantTwoTensorNormSq (h : ∀ x : M, T₂ x) (x : M) : ℝ := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, ∑ j, (h x (b i) (b j)) ^ 2

theorem covariantTwoTensorNormSq_eq_sum
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x =
      (by
        let _ : FiniteDimensional ℝ (TM x) :=
          VectorBundle.finiteDimensional ℝ E TM x
        let b := stdOrthonormalBasis ℝ (TM x)
        exact ∑ i, ∑ j, (h x (b i) (b j)) ^ 2) := by
  rfl

theorem covariantTwoTensorNormSq_nonneg
    (h : ∀ x : M, T₂ x) (x : M) :
    0 ≤ covariantTwoTensorNormSq h x := by
  rw [covariantTwoTensorNormSq_eq_sum]
  positivity

/-- The pointwise norm square vanishes exactly when the complete bilinear
form vanishes, including all off-diagonal tensor slots. -/
theorem covariantTwoTensorNormSq_eq_zero_iff
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x = 0 ↔ h x = 0 := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  constructor
  · intro hzero
    rw [covariantTwoTensorNormSq_eq_sum] at hzero
    have hrow (i : Fin (Module.finrank ℝ (TM x))) :
        (∑ j, (h x (b i) (b j)) ^ 2) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => by positivity)).1 hzero i (Finset.mem_univ i)
    have hcoeff (i j : Fin (Module.finrank ℝ (TM x))) :
        h x (b i) (b j) = 0 := by
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (h x (b i) (b k)))).1
          (hrow i) j (Finset.mem_univ j)
      nlinarith only [hsq]
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext (fun i => ?_)
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext (fun j => ?_)
    exact hcoeff i j
  · intro hzero
    rw [covariantTwoTensorNormSq_eq_sum]
    simp [hzero]

end CovariantDerivative
