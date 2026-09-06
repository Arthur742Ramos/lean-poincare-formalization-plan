module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Tactic

/-!
# Basis-independent squared Hilbert–Schmidt norm

The norm needed for curvature tensors is not the operator norm. We define
its square intrinsically by the trace of the adjoint composite, and identify
it with the full double contraction in every orthonormal basis.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Squared Hilbert–Schmidt norm of an endomorphism. -/
def hilbertSchmidtSq (A : V →L[ℝ] V) : ℝ :=
  LinearMap.trace ℝ V (A.adjoint.comp A).toLinearMap

theorem hilbertSchmidtSq_eq_sum_norm_sq (A : V →L[ℝ] V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    hilbertSchmidtSq A = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [hilbertSchmidtSq, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (A.adjoint (A (b i))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Full tensor contraction in an arbitrary orthonormal basis. -/
theorem hilbertSchmidtSq_eq_sum_sq (A : V →L[ℝ] V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    hilbertSchmidtSq A = ∑ i, ∑ j, (inner ℝ (A (b i)) (b j)) ^ 2 := by
  rw [hilbertSchmidtSq_eq_sum_norm_sq A b]
  apply Finset.sum_congr rfl
  intro i _
  exact (b.sum_sq_inner_left (A (b i))).symm

theorem hilbertSchmidtSq_nonneg (A : V →L[ℝ] V) : 0 ≤ hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq_eq_sum_norm_sq A (stdOrthonormalBasis ℝ V)]
  positivity

/-- The trace-free part is defined only by intrinsic trace and dimension. -/
def traceFree (A : V →L[ℝ] V) : V →L[ℝ] V :=
  A - (LinearMap.trace ℝ V A.toLinearMap / Module.finrank ℝ V) •
    ContinuousLinearMap.id ℝ V

theorem trace_traceFree (A : V →L[ℝ] V) (hdim : Module.finrank ℝ V ≠ 0) :
    LinearMap.trace ℝ V (traceFree A).toLinearMap = 0 := by
  have hn : (Module.finrank ℝ V : ℝ) ≠ 0 := by exact_mod_cast hdim
  simp [traceFree, map_sub, map_smul, LinearMap.trace_id, hn]

/-- Orthogonal splitting into scalar and trace-free parts, before choosing the scalar. -/
theorem hilbertSchmidtSq_sub_smul_id (A : V →L[ℝ] V) (c : ℝ) :
    hilbertSchmidtSq (A - c • ContinuousLinearMap.id ℝ V) =
      hilbertSchmidtSq A - 2 * c * LinearMap.trace ℝ V A.toLinearMap +
        Module.finrank ℝ V * c ^ 2 := by
  let b := stdOrthonormalBasis ℝ V
  have hterm (i : Fin (Module.finrank ℝ V)) :
      ‖(A - c • ContinuousLinearMap.id ℝ V) (b i)‖ ^ 2 =
        ‖A (b i)‖ ^ 2 - 2 * c * inner ℝ (b i) (A (b i)) + c ^ 2 := by
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one, sq_abs]
    rw [real_inner_comm]
    ring
  rw [hilbertSchmidtSq_eq_sum_norm_sq _ b]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hilbertSchmidtSq_eq_sum_norm_sq A b, LinearMap.trace_eq_sum_inner A.toLinearMap b]
  rfl

/-- Exact trace-free Hilbert–Schmidt decomposition. -/
theorem hilbertSchmidtSq_traceFree (A : V →L[ℝ] V)
    (hdim : Module.finrank ℝ V ≠ 0) :
    hilbertSchmidtSq (traceFree A) = hilbertSchmidtSq A -
      (LinearMap.trace ℝ V A.toLinearMap) ^ 2 / Module.finrank ℝ V := by
  have hn : (Module.finrank ℝ V : ℝ) ≠ 0 := by exact_mod_cast hdim
  rw [traceFree, hilbertSchmidtSq_sub_smul_id]
  field_simp
  ring

end AlmostSchur
