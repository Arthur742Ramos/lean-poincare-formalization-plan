/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Metric contraction of vector-valued bilinear maps

The conventional DeTurck vector is the inverse-metric contraction of the two
covariant slots of a connection-difference tensor. It is not the Riesz lift of
the ordinary trace of `u ↦ D(u,w)`. This module constructs the former without
choosing a coordinate frame and proves its basis formulas. A two-dimensional
conformal-symbol regression separates the two contractions.
-/

open scoped TensorProduct BigOperators

namespace PoincareCurvature

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Contract both input slots with the canonical inverse-metric tensor. -/
noncomputable def metricBilinearContraction
    (D : V →ₗ[ℝ] V →ₗ[ℝ] V) : V :=
  TensorProduct.lift D (InnerProductSpace.canonicalCovariantTensor V)

/-- The metric contraction has the conventional diagonal formula in any
orthonormal basis. The definition itself is basis-independent. -/
theorem metricBilinearContraction_eq_sum_orthonormalBasis
    (D : V →ₗ[ℝ] V →ₗ[ℝ] V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    metricBilinearContraction D = ∑ i, D (b i) (b i) := by
  rw [metricBilinearContraction,
    InnerProductSpace.canonicalCovariantTensor_eq_sum V b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

@[simp] theorem metricBilinearContraction_zero :
    metricBilinearContraction (0 : V →ₗ[ℝ] V →ₗ[ℝ] V) = 0 := by
  rw [metricBilinearContraction_eq_sum_orthonormalBasis _
    (stdOrthonormalBasis ℝ V)]
  simp

/-- The Riesz dual of a basis covector, not an ordinary connection trace. -/
noncomputable def metricDualBasis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (i : ι) : V :=
  (InnerProductSpace.toDual ℝ V).symm
    (LinearMap.toContinuousLinearMap (b.coord i))

theorem inner_metricDualBasis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (i : ι) (v : V) :
    inner ℝ (metricDualBasis b i) v = b.repr v i := by
  exact InnerProductSpace.toDual_symm_apply

/-- In an arbitrary frame the inverse-metric tensor pairs the frame with its
metric dual. This is the basis-independent bridge to Gram-matrix coordinates. -/
theorem canonicalCovariantTensor_eq_sum_basis_metricDualBasis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) :
    InnerProductSpace.canonicalCovariantTensor V =
      ∑ i, b i ⊗ₜ[ℝ] metricDualBasis b i := by
  classical
  let o := stdOrthonormalBasis ℝ V
  have hdual (i : ι) :
      ∑ m, b.repr (o m) i • o m = metricDualBasis b i := by
    have hcoef (m) : b.repr (o m) i = inner ℝ (o m) (metricDualBasis b i) := by
      rw [real_inner_comm, inner_metricDualBasis]
    simp_rw [hcoef]
    exact o.sum_repr' _
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum V o]
  calc
    ∑ m, o m ⊗ₜ[ℝ] o m =
        ∑ m, (∑ i, b.repr (o m) i • b i) ⊗ₜ[ℝ] o m := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [b.sum_repr]
    _ = ∑ m, ∑ i, b i ⊗ₜ[ℝ] (b.repr (o m) i • o m) := by
      simp_rw [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
    _ = ∑ i, b i ⊗ₜ[ℝ] (∑ m, b.repr (o m) i • o m) := by
      rw [Finset.sum_comm]
      simp_rw [TensorProduct.tmul_sum]
    _ = ∑ i, b i ⊗ₜ[ℝ] metricDualBasis b i := by simp_rw [hdual]

theorem metricBilinearContraction_eq_sum_basis_metricDualBasis
    (D : V →ₗ[ℝ] V →ₗ[ℝ] V)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) :
    metricBilinearContraction D = ∑ i, D (b i) (metricDualBasis b i) := by
  rw [metricBilinearContraction,
    canonicalCovariantTensor_eq_sum_basis_metricDualBasis b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- Coordinates of the metric-dual frame are the inverse Gram matrix. -/
theorem metricDualBasis_repr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (i j : ι) :
    b.repr (metricDualBasis b i) j = (Matrix.gram ℝ b)⁻¹ j i := by
  let A := Matrix.gram ℝ b
  let v := metricDualBasis b i
  let c : ι → ℝ := b.repr v
  have hAc : A.mulVec c = Pi.single i 1 := by
    ext k
    calc
      (A.mulVec c) k = ∑ l, A k l * c l := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ l, c l * inner ℝ (b l) (b k) := by
        apply Finset.sum_congr rfl
        intro l hl
        simp [A, Matrix.gram_apply, real_inner_comm, mul_comm]
      _ = inner ℝ (∑ l, c l • b l) (b k) := by
        simp [sum_inner, real_inner_smul_left]
      _ = inner ℝ v (b k) := by rw [b.sum_repr v]
      _ = (Pi.single i (1 : ℝ) : ι → ℝ) k := by
        rw [show v = metricDualBasis b i from rfl, inner_metricDualBasis]
        simp [Pi.single_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hAunit : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hc : c = A⁻¹.mulVec (Pi.single i 1) := by
    calc
      c = (1 : Matrix ι ι ℝ).mulVec c := by simp
      _ = (A⁻¹ * A).mulVec c := by rw [Matrix.nonsing_inv_mul A hAunit]
      _ = A⁻¹.mulVec (A.mulVec c) := by rw [Matrix.mulVec_mulVec]
      _ = A⁻¹.mulVec (Pi.single i 1) := by rw [hAc]
  have hj := congrFun hc j
  simpa [c, v, A, Matrix.mulVec, dotProduct, Pi.single_apply] using hj

/-- The coordinate formula contracts the two input slots with the inverse
Gram matrix, rather than tracing an output slot against an input slot. -/
theorem metricBilinearContraction_eq_sum_inverseGram
    (D : V →ₗ[ℝ] V →ₗ[ℝ] V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) :
    metricBilinearContraction D =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • D (b i) (b j) := by
  have hsym : (Matrix.gram ℝ b).transpose = Matrix.gram ℝ b := by
    ext i j
    exact real_inner_comm _ _
  have hinv : ((Matrix.gram ℝ b)⁻¹).transpose = (Matrix.gram ℝ b)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  have hinv_entry (i j : ι) : (Matrix.gram ℝ b)⁻¹ j i = (Matrix.gram ℝ b)⁻¹ i j :=
    congrArg (fun A : Matrix ι ι ℝ => A i j) hinv
  rw [metricBilinearContraction_eq_sum_basis_metricDualBasis D b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← b.sum_repr (metricDualBasis b i)]
  simp_rw [map_sum, map_smul, metricDualBasis_repr, hinv_entry]

/-! ## A regression for the two different slot contractions -/

/-- The conventional contraction `g^{ab} D^k_{ab}` in coordinates. -/
def metricContractSymbol {n : ℕ} (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (D : Fin n → Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ a, ∑ b, Ginv a b * D k a b

/-- The current trace-raised contraction `g^{kb} D^a_{ab}` in coordinates. -/
def ordinaryTraceRaisedSymbol {n : ℕ} (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (D : Fin n → Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ b, Ginv k b * ∑ a, D a a b

/-- The Christoffel symbol of a conformal metric at a point where its value
is Euclidean and the differential of the conformal factor is `df`. -/
def conformalChristoffelSymbol {n : ℕ} (df : Fin n → ℝ)
    (k a b : Fin n) : ℝ :=
  (if k = b then 1 else 0) * df a +
    (if k = a then 1 else 0) * df b -
    (if a = b then 1 else 0) * df k

/-- In dimension two the conventional contraction of this conformal symbol
vanishes. This is an algebraic regression, not an assumed geometric bridge. -/
theorem metricContractSymbol_conformal_two_eq_zero (k : Fin 2) :
    metricContractSymbol (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (conformalChristoffelSymbol (fun i : Fin 2 => if i = 0 then 1 else 0)) k = 0 := by
  fin_cases k <;>
    norm_num [metricContractSymbol, conformalChristoffelSymbol, Fin.sum_univ_two]

/-- The trace-raised contraction of the same symmetric symbol is nonzero. -/
theorem ordinaryTraceRaisedSymbol_conformal_two_eq_two :
    ordinaryTraceRaisedSymbol (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (conformalChristoffelSymbol (fun i : Fin 2 => if i = 0 then 1 else 0)) 0 = 2 := by
  norm_num [ordinaryTraceRaisedSymbol, conformalChristoffelSymbol, Fin.sum_univ_two]

/-- A concrete regression prevents identification of the two contractions. -/
theorem metricContractSymbol_ne_ordinaryTraceRaisedSymbol_conformal_two :
    metricContractSymbol (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (conformalChristoffelSymbol (fun i : Fin 2 => if i = 0 then 1 else 0)) 0 ≠
    ordinaryTraceRaisedSymbol (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (conformalChristoffelSymbol (fun i : Fin 2 => if i = 0 then 1 else 0)) 0 := by
  rw [metricContractSymbol_conformal_two_eq_zero,
    ordinaryTraceRaisedSymbol_conformal_two_eq_two]
  norm_num

end PoincareCurvature
