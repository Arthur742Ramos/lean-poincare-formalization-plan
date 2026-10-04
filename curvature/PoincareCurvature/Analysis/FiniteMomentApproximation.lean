module

public import Mathlib.Analysis.Normed.Module.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Approximation by positive normalized kernels with finite first moments -/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric Filter
open scoped BigOperators Topology

namespace PoincareCurvature
namespace FiniteMomentApproximation

/-- The sup norm on a finite Cartesian power is bounded by the sum of the
absolute coordinates, also in dimension zero. -/
lemma norm_le_sum_abs_coord {n : ℕ} (z : Fin n → ℝ) :
    ‖z‖ ≤ ∑ k : Fin n, |z k| := by
  classical
  have hn : 0 ≤ ∑ k : Fin n, |z k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg hn).mpr fun k => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (z i)) (Finset.mem_univ k)

/-- An arbitrary local continuity modulus and finite first moments control
a positive normalized convolution. All kernel hypotheses remain explicit;
the Gaussian instance discharges them with its proved integrals. -/
theorem abs_integral_sub_self_le_of_local_modulus
    {n : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (K : (Fin n → ℝ) → ℝ) (hKi : Integrable K)
    (hK : ∀ z, 0 ≤ K z) (hmass : (∫ z, K z) = 1)
    (hcoord : ∀ k : Fin n, Integrable (fun z => K z * |z k|))
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ)
    (hmod : ∀ y, ‖y - x‖ < δ → |f y - f x| ≤ ε) :
    |(∫ z, K z * f (x - z)) - f x| ≤
      ε + (2 * ‖f‖ / δ) * ∑ k : Fin n, ∫ z, K z * |z k| := by
  classical
  let L : ℝ := 2 * ‖f‖ / δ
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hfi : Integrable (fun z : Fin n → ℝ => K z * f (x - z)) :=
    hKi.mul_bdd
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => f.norm_coe_le_norm _)
  have hci : Integrable (fun z : Fin n → ℝ => K z * f x) :=
    hKi.mul_const _
  have hdom : Integrable (fun z : Fin n → ℝ =>
      K z * ε + L * ∑ k : Fin n, K z * |z k|) :=
    (hKi.mul_const ε).add
      ((integrable_finset_sum _ (fun k _ => hcoord k)).const_mul L)
  have hdiff : ∀ z : Fin n → ℝ,
      |f (x - z) - f x| ≤ ε + L * ∑ k : Fin n, |z k| := by
    intro z
    have hnorm : ‖(x - z) - x‖ = ‖z‖ := by
      rw [show (x - z) - x = -z by abel, norm_neg]
    by_cases hz : ‖z‖ < δ
    · exact (hmod (x - z) (by simpa only [hnorm] using hz)).trans
        (le_add_of_nonneg_right (mul_nonneg hL
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
    · have hb : |f (x - z) - f x| ≤ 2 * ‖f‖ := by
        calc
          |f (x - z) - f x| ≤ |f (x - z)| + |f x| := abs_sub _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
            (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (x - z))
            (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
          _ = 2 * ‖f‖ := by ring
      have htail : 2 * ‖f‖ ≤ L * ‖z‖ := by
        have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hz) hL
        have hc : L * δ = 2 * ‖f‖ := div_mul_cancel₀ _ hδ.ne'
        rwa [hc] at hm
      calc
        |f (x - z) - f x| ≤ L * ‖z‖ := hb.trans htail
        _ ≤ L * ∑ k : Fin n, |z k| :=
          mul_le_mul_of_nonneg_left (norm_le_sum_abs_coord z) hL
        _ ≤ ε + L * ∑ k : Fin n, |z k| := le_add_of_nonneg_left hε
  have hpoint : ∀ z : Fin n → ℝ,
      ‖K z * (f (x - z) - f x)‖ ≤
        K z * ε + L * ∑ k : Fin n, K z * |z k| := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK z)]
    calc
      K z * |f (x - z) - f x|
          ≤ K z * (ε + L * ∑ k : Fin n, |z k|) :=
        mul_le_mul_of_nonneg_left (hdiff z) (hK z)
      _ = _ := by
        simp only [mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
  have hzero : (∫ z, K z * f (x - z)) - f x =
      ∫ z : Fin n → ℝ, K z * (f (x - z) - f x) := by
    have heq : (fun z : Fin n → ℝ => K z * (f (x - z) - f x)) =
        (fun z => K z * f (x - z)) -
          (fun z => K z * f x) := by ext z; simp [mul_sub]
    rw [heq, integral_sub hfi hci, integral_mul_const, hmass, one_mul]
  rw [hzero, ← Real.norm_eq_abs]
  calc
    ‖∫ z : Fin n → ℝ, K z * (f (x - z) - f x)‖
        ≤ ∫ z : Fin n → ℝ,
          K z * ε + L * ∑ k : Fin n, K z * |z k| :=
      norm_integral_le_of_norm_le hdom (Eventually.of_forall hpoint)
    _ = ε + L * ∑ k : Fin n,
        ∫ z : Fin n → ℝ, K z * |z k| := by
      rw [integral_add (hKi.mul_const ε)
        ((integrable_finset_sum _ (fun k _ => hcoord k)).const_mul L),
        integral_mul_const, hmass, one_mul,
        integral_const_mul, integral_finset_sum _ (fun k _ => hcoord k)]
    _ = _ := rfl

end FiniteMomentApproximation
end PoincareCurvature
