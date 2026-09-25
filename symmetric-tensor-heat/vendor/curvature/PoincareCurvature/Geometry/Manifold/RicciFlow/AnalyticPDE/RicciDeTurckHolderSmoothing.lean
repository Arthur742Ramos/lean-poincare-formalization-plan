module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2

/-!
# Homogeneous linear C² → C²,α parabolic smoothing (Phase 2d-1)

For the flat (frozen-coefficient) Euclidean heat equation, bounded-C² initial
data evolves at every positive time into data whose Hessian entries are
C⁰,α.  The mechanism is commutation: each Hessian entry of the heat evolution
is itself the heat evolution of the corresponding bounded initial Hessian
entry (`EuclideanBoundedC2Data.heatHessianEntryConvolutionND_eq`), hence
inherits the whole-space C⁰,α gain of the heat semigroup on bounded data
(`heatSemigroupND_spatial_holder_seminorm_bound`).

The packaged estimate is
`‖u t‖_{C^{2,α}} ≤ (1 + 2·(πt)^{-α/2}) · ‖u₀‖_{C²}` for `0 ≤ α ≤ 1` and
`t > 0`, with the exact function spaces and norms stated below.  The
variable-coefficient upgrade (genuine Ricci–DeTurck linearization) is
explicitly future work; this file is flat heat equation only.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The `C²` norm of bounded Euclidean C² data: sup norms of the value,
gradient entries, and Hessian entries. -/
def EuclideanBoundedC2Data.c2Norm {n : ℕ} (D : EuclideanBoundedC2Data n) : ℝ :=
  ‖D.value‖ + ∑ k : Fin n, ‖D.first k‖
    + ∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖

/-- Bounded scalar `C^{2,α}` data on Euclidean space: bounded C² data plus an
explicit uniform Hölder modulus for every Hessian entry, in the
coordinate-sum seminorm form. -/
structure EuclideanBoundedC2AlphaData (n : ℕ) (α : ℝ) where
  base : EuclideanBoundedC2Data n
  hessianHolderConstant : ℝ
  hessianHolderConstant_nonneg : 0 ≤ hessianHolderConstant
  hessianHolder : ∀ j k x y,
    |base.second j k x - base.second j k y| ≤
      hessianHolderConstant * (∑ ell : Fin n, |(x - y) ell|) ^ α

/-- The `C^{2,α}` norm: the `C²` norm plus the Hessian Hölder constant. -/
def EuclideanBoundedC2AlphaData.c2alphaNorm {n : ℕ} {α : ℝ}
    (D : EuclideanBoundedC2AlphaData n α) : ℝ :=
  D.base.c2Norm + D.hessianHolderConstant

/-- **Hessian-entry Hölder gain for the homogeneous heat flow.**  For bounded-C²
initial data, each Hessian entry of the time-`t` heat evolution is the heat
evolution of the corresponding bounded initial Hessian entry, hence C⁰,α for
`t > 0` with the explicit Schauder constant
`(2‖D²_{jk}u₀‖)^{1-α}·(‖D²_{jk}u₀‖/√(πt))^α`. -/
theorem heatSemigroupND_hessianEntry_spatial_holder_bound
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t D.value j k x -
        heatHessianEntryConvolutionND t D.value j k y| ≤
      (2 * ‖D.second j k‖) ^ (1 - α) *
        (‖D.second j k‖ / Real.sqrt (π * t)) ^ α *
        (∑ i : Fin n, |(x - y) i|) ^ α := by
  rw [D.heatHessianEntryConvolutionND_eq ht j k x,
    D.heatHessianEntryConvolutionND_eq ht j k y]
  have h : |heatSemigroupND t ⇑(D.second j k) x -
        heatSemigroupND t ⇑(D.second j k) y| ≤
      (2 * ‖D.second j k‖) ^ (1 - α) *
        (‖D.second j k‖ / Real.sqrt (π * t)) ^ α *
        (∑ i : Fin n, |x i - y i|) ^ α :=
    heatSemigroupND_spatial_holder_seminorm_bound ht
      (D.second j k).continuous.aestronglyMeasurable
      (fun z ↦ (D.second j k).norm_coe_le_norm z) hα0 hα1 x y
  simpa only [Pi.sub_apply] using h

/-- The time-`t` heat evolution of bounded C² data, rebundled as bounded C²
data.  The first and second derivatives commute through the semigroup by
`hasDerivAt_heatSemigroupND_coord_of_bounded_deriv`. -/
def heatEvolvedBoundedC2Data {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ}
    (ht : 0 < t) : EuclideanBoundedC2Data n where
  value := heatSemigroupNDbcf ht D.value
  first := fun k ↦ heatSemigroupNDbcf ht (D.first k)
  second := fun j k ↦ heatSemigroupNDbcf ht (D.second j k)
  hasDeriv_value := by
    intro k x
    have h := hasDerivAt_heatSemigroupND_coord_of_bounded_deriv
      ht D.value (D.first k) k (D.hasDeriv_value k) x
    simpa only [heatSemigroupNDbcf_apply] using h
  hasDeriv_first := by
    intro j k x
    have h := hasDerivAt_heatSemigroupND_coord_of_bounded_deriv
      ht (D.first k) (D.second j k) j (D.hasDeriv_first j k) x
    simpa only [heatSemigroupNDbcf_apply] using h

@[simp] theorem heatEvolvedBoundedC2Data_value_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t) :
    (heatEvolvedBoundedC2Data D ht).value = heatSemigroupNDbcf ht D.value :=
  rfl

@[simp] theorem heatEvolvedBoundedC2Data_first_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t) (k : Fin n) :
    (heatEvolvedBoundedC2Data D ht).first k =
      heatSemigroupNDbcf ht (D.first k) := rfl

@[simp] theorem heatEvolvedBoundedC2Data_second_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t) (j k : Fin n) :
    (heatEvolvedBoundedC2Data D ht).second j k =
      heatSemigroupNDbcf ht (D.second j k) := rfl

/-- The `C²` norm is non-expansive under the homogeneous heat flow, by the
maximum principle applied to each bundled entry. -/
theorem heatEvolvedBoundedC2Data_c2Norm_le {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t) :
    (heatEvolvedBoundedC2Data D ht).c2Norm ≤ D.c2Norm := by
  show ‖heatSemigroupNDbcf ht D.value‖
      + ∑ k : Fin n, ‖heatSemigroupNDbcf ht (D.first k)‖
      + ∑ j : Fin n, ∑ k : Fin n, ‖heatSemigroupNDbcf ht (D.second j k)‖
      ≤ ‖D.value‖ + ∑ k : Fin n, ‖D.first k‖
      + ∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖
  exact add_le_add (add_le_add (norm_heatSemigroupNDbcf_le ht D.value)
    (Finset.sum_le_sum fun k _ => norm_heatSemigroupNDbcf_le ht (D.first k)))
    (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      norm_heatSemigroupNDbcf_le ht (D.second j k))

/-- Nonnegativity of the raw Schauder constant for each Hessian entry. -/
theorem holderSmoothingTerm_nonneg {n : ℕ} (D : EuclideanBoundedC2Data n)
    {t α : ℝ} (j k : Fin n) :
    0 ≤ (2 * ‖D.second j k‖) ^ (1 - α) *
      (‖D.second j k‖ / Real.sqrt (π * t)) ^ α :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) _)
    (Real.rpow_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) _)

/-- The time-`t` heat evolution of bounded-C² data as `C^{2,α}` data.  The
Hölder constant is the sum over all Hessian entries of the raw Schauder
constants from `heatSemigroupND_hessianEntry_spatial_holder_bound`. -/
def heatEvolvedC2AlphaData {n : ℕ} (D : EuclideanBoundedC2Data n) {t α : ℝ}
    (ht : 0 < t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    EuclideanBoundedC2AlphaData n α where
  base := heatEvolvedBoundedC2Data D ht
  hessianHolderConstant :=
    ∑ j : Fin n, ∑ k : Fin n,
      (2 * ‖D.second j k‖) ^ (1 - α) *
        (‖D.second j k‖ / Real.sqrt (π * t)) ^ α
  hessianHolderConstant_nonneg :=
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => holderSmoothingTerm_nonneg D j k
  hessianHolder := by
    intro j k x y
    have hmain :=
      heatSemigroupND_hessianEntry_spatial_holder_bound D ht hα0 hα1 j k x y
    rw [D.heatHessianEntryConvolutionND_eq ht j k x,
      D.heatHessianEntryConvolutionND_eq ht j k y] at hmain
    have hnn : (0:ℝ) ≤ (∑ ell : Fin n, |(x - y) ell|) ^ α :=
      Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _
    have hterm : (2 * ‖D.second j k‖) ^ (1 - α) *
          (‖D.second j k‖ / Real.sqrt (π * t)) ^ α ≤
        ∑ j' : Fin n, ∑ k' : Fin n, (2 * ‖D.second j' k'‖) ^ (1 - α) *
          (‖D.second j' k'‖ / Real.sqrt (π * t)) ^ α := by
      refine le_trans (Finset.single_le_sum
        (fun k' _ => holderSmoothingTerm_nonneg D j k') (Finset.mem_univ k)) ?_
      exact Finset.single_le_sum
        (fun j' _ => Finset.sum_nonneg fun k' _ =>
          holderSmoothingTerm_nonneg D j' k') (Finset.mem_univ j)
    have hmain' : |heatSemigroupND t ⇑(D.second j k) x -
          heatSemigroupND t ⇑(D.second j k) y| ≤
        (∑ j' : Fin n, ∑ k' : Fin n, (2 * ‖D.second j' k'‖) ^ (1 - α) *
          (‖D.second j' k'‖ / Real.sqrt (π * t)) ^ α) *
        (∑ ell : Fin n, |(x - y) ell|) ^ α :=
      le_trans hmain (mul_le_mul_of_nonneg_right hterm hnn)
    simpa only [heatEvolvedBoundedC2Data_second_eq,
      heatSemigroupNDbcf_apply] using hmain'

@[simp] theorem heatEvolvedC2AlphaData_base_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (heatEvolvedC2AlphaData D ht hα0 hα1).base =
      heatEvolvedBoundedC2Data D ht := rfl

@[simp] theorem heatEvolvedC2AlphaData_holderConstant_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (heatEvolvedC2AlphaData D ht hα0 hα1).hessianHolderConstant =
      ∑ j : Fin n, ∑ k : Fin n, (2 * ‖D.second j k‖) ^ (1 - α) *
        (‖D.second j k‖ / Real.sqrt (π * t)) ^ α := rfl

/-- Elementary `rpow` accounting: the raw Hölder constant
`(2C)^{1-α}·(C/√(πt))^α` is at most `2·(πt)^{-α/2}·C`. -/
theorem rpow_holder_smoothing_const_le {C t α : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (2 * C) ^ (1 - α) * (C / Real.sqrt (π * t)) ^ α ≤
      2 * (π * t) ^ (-(α / 2)) * C := by
  have hsqrt : (0:ℝ) < Real.sqrt (π * t) := Real.sqrt_pos.mpr (by positivity)
  have hpi : (0:ℝ) < π * t := by positivity
  rcases eq_or_ne C 0 with rfl | hCne
  · -- Both sides vanish when `C = 0`.
    have hLHS : (2 * (0:ℝ)) ^ (1 - α) *
        ((0:ℝ) / Real.sqrt (π * t)) ^ α = 0 := by
      rw [mul_zero, zero_div]
      rcases eq_or_lt_of_le hα0 with rfl | hapos
      · rw [show (1:ℝ) - 0 = 1 by ring, Real.zero_rpow (by norm_num),
          Real.rpow_zero, zero_mul]
      · rw [Real.zero_rpow (ne_of_gt hapos), mul_zero]
    rw [hLHS, mul_zero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCne)
    have e1 : (2 * C) ^ (1 - α) = 2 ^ (1 - α) * C ^ (1 - α) :=
      Real.mul_rpow (by norm_num) hC
    have e2 : (C / Real.sqrt (π * t)) ^ α
        = C ^ α / (Real.sqrt (π * t)) ^ α :=
      Real.div_rpow hC hsqrt.le α
    have e3 : (Real.sqrt (π * t)) ^ α = (π * t) ^ (α / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpi.le]
      congr 1
      ring
    have e4 : C ^ (1 - α) * C ^ α = C := by
      rw [← Real.rpow_add hCpos, show (1 - α) + α = 1 by ring, Real.rpow_one]
    have e5 : (2:ℝ) ^ (1 - α) ≤ 2 := by
      calc (2:ℝ) ^ (1 - α) ≤ (2:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have e6 : (π * t) ^ (-(α / 2)) = ((π * t) ^ (α / 2))⁻¹ :=
      Real.rpow_neg hpi.le _
    have hpos : (0:ℝ) < (π * t) ^ (α / 2) := Real.rpow_pos_of_pos hpi _
    rw [e1, e2, e3, e6]
    have lhs_eq : (2:ℝ) ^ (1 - α) * C ^ (1 - α) * (C ^ α / (π * t) ^ (α / 2))
        = (2 ^ (1 - α) * C) / (π * t) ^ (α / 2) := by
      have hstep : C ^ (1 - α) * (C ^ α / (π * t) ^ (α / 2))
          = C / (π * t) ^ (α / 2) := by
        rw [← mul_div_assoc, e4]
      rw [mul_assoc, hstep, ← mul_div_assoc]
    have rhs_eq : (2:ℝ) * ((π * t) ^ (α / 2))⁻¹ * C
        = (2 * C) / (π * t) ^ (α / 2) := by
      rw [div_eq_mul_inv]
      ring
    rw [lhs_eq, rhs_eq, div_le_div_iff_of_pos_right hpos]
    exact mul_le_mul_of_nonneg_right e5 hC

/-- **Homogeneous linear C² → C²,α smoothing estimate.**  The time-`t` heat
evolution of bounded-C² data satisfies
`‖u t‖_{C^{2,α}} ≤ (1 + 2·(πt)^{-α/2}) · ‖u₀‖_{C²}`
for `0 ≤ α ≤ 1` and `t > 0`: the `C²` part is non-expansive by the maximum
principle, and the Hessian Hölder constant gains `(πt)^{-α/2}`. -/
theorem heatEvolvedC2AlphaData_c2alphaNorm_le {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (heatEvolvedC2AlphaData D ht hα0 hα1).c2alphaNorm ≤
      (1 + 2 * (π * t) ^ (-(α / 2))) * D.c2Norm := by
  have hpi : (0:ℝ) < π * t := by positivity
  have hbase : (heatEvolvedC2AlphaData D ht hα0 hα1).base.c2Norm ≤ D.c2Norm := by
    rw [heatEvolvedC2AlphaData_base_eq]
    exact heatEvolvedBoundedC2Data_c2Norm_le D ht
  have hH : (heatEvolvedC2AlphaData D ht hα0 hα1).hessianHolderConstant ≤
      2 * (π * t) ^ (-(α / 2)) * D.c2Norm := by
    rw [heatEvolvedC2AlphaData_holderConstant_eq]
    have hterm : ∀ j k : Fin n, (2 * ‖D.second j k‖) ^ (1 - α) *
        (‖D.second j k‖ / Real.sqrt (π * t)) ^ α ≤
        2 * (π * t) ^ (-(α / 2)) * ‖D.second j k‖ :=
      fun j k => rpow_holder_smoothing_const_le (norm_nonneg _) ht hα0 hα1
    have hsum : ∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖ ≤ D.c2Norm := by
      rw [EuclideanBoundedC2Data.c2Norm]
      have hnn : (0:ℝ) ≤ ‖D.value‖ + ∑ k : Fin n, ‖D.first k‖ :=
        add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      linarith
    calc (∑ j : Fin n, ∑ k : Fin n, (2 * ‖D.second j k‖) ^ (1 - α) *
            (‖D.second j k‖ / Real.sqrt (π * t)) ^ α)
          ≤ ∑ j : Fin n, ∑ k : Fin n,
            2 * (π * t) ^ (-(α / 2)) * ‖D.second j k‖ :=
            Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => hterm j k
        _ = 2 * (π * t) ^ (-(α / 2)) *
            ∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
        _ ≤ 2 * (π * t) ^ (-(α / 2)) * D.c2Norm :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
  show (heatEvolvedC2AlphaData D ht hα0 hα1).base.c2Norm
      + (heatEvolvedC2AlphaData D ht hα0 hα1).hessianHolderConstant
      ≤ (1 + 2 * (π * t) ^ (-(α / 2))) * D.c2Norm
  calc (heatEvolvedC2AlphaData D ht hα0 hα1).base.c2Norm
        + (heatEvolvedC2AlphaData D ht hα0 hα1).hessianHolderConstant
      ≤ D.c2Norm + 2 * (π * t) ^ (-(α / 2)) * D.c2Norm := add_le_add hbase hH
    _ = (1 + 2 * (π * t) ^ (-(α / 2))) * D.c2Norm := by ring

end AnalyticPDE
end RicciFlow
