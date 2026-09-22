module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TraceLaplacian

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
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
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

/-- The norm square is the intrinsic trace of the adjoint-square of the
raised tensor. In particular, the orthonormal-basis formula is independent of
the basis chosen at the point. -/
theorem covariantTwoTensorNormSq_eq_trace_adjoint_comp
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x =
      (by
        let _ : FiniteDimensional ℝ (TM x) :=
          VectorBundle.finiteDimensional ℝ E TM x
        let A : TM x →ₗ[ℝ] TM x :=
          (raisedCovariantTwoTensor (I := I) (E := E) h x).toLinearMap
        exact LinearMap.trace ℝ (TM x) (A.adjoint.comp A)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x :=
    (raisedCovariantTwoTensor (I := I) (E := E) h x).toLinearMap
  have hnorm : covariantTwoTensorNormSq h x =
      ∑ i, ‖A (b i)‖ ^ 2 := by
    rw [covariantTwoTensorNormSq_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hparse := b.sum_sq_inner_left (A (b i))
    calc
      ∑ j, (h x (b i) (b j)) ^ 2 =
          ∑ j, (inner ℝ (A (b i)) (b j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        change h x (b i) (b j) =
          inner ℝ (rieszMap (I := I) x (h x (b i))) (b j)
        exact (rieszMap_apply_inner (I := I) x (h x (b i)) (b j)).symm
      _ = ‖A (b i)‖ ^ 2 := hparse
  rw [hnorm, LinearMap.trace_eq_sum_inner (A.adjoint.comp A) b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm]
  change ‖A (b i)‖ ^ 2 =
    inner ℝ (LinearMap.adjoint A (A (b i))) (b i)
  rw [LinearMap.adjoint_inner_left]
  exact (real_inner_self_eq_norm_sq _).symm

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
