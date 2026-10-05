module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A two-endpoint weighted time kernel

Source-only proof candidate, not compiled or verified against the pinned toolchain.
The proof splits the actual interval integral at its midpoint. Each singular
power is integrable; the other factor is continuous on the corresponding closed
half interval. The two integrated majorants cancel the interval scale exactly.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory
open scoped Real Interval

namespace RicciFlow
namespace AnalyticPDE

/-- The scalar time kernel underlying weighted Gaussian Hessian estimates. -/
def weightedTimeKernel (t₀ t a s : ℝ) : ℝ :=
  (t - s) ^ (a - 1) * (s - t₀) ^ (-a)

/-- Actual integrability and an interval-length-independent integral bound.
There is no integrability, solver, inverse, or operator-bound hypothesis. -/
theorem weightedTimeKernel_integrable_and_integral_le
    {t₀ t a : ℝ} (ht : t₀ < t) (ha : 0 < a) (ha1 : a < 1) :
    IntervalIntegrable (weightedTimeKernel t₀ t a) volume t₀ t ∧
      (∫ s in t₀..t, weightedTimeKernel t₀ t a s) ≤
        1 / a + 1 / (1 - a) := by
  let m : ℝ := (t₀ + t) / 2
  let h : ℝ := (t - t₀) / 2
  let f : ℝ → ℝ := weightedTimeKernel t₀ t a
  have ht₀m : t₀ < m := by dsimp [m]; linarith
  have hmt : m < t := by dsimp [m]; linarith
  have hh : 0 < h := by dsimp [h]; linarith
  have hleftLen : m - t₀ = h := by dsimp [m, h]; ring
  have hrightLen : t - m = h := by dsimp [m, h]; ring
  have hleftPow : IntervalIntegrable (fun s : ℝ => (s - t₀) ^ (-a))
      volume t₀ m := by
    have hb : IntervalIntegrable (fun z : ℝ => z ^ (-a)) volume 0 (m - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa only [zero_add, sub_add_cancel] using hb.comp_sub_right t₀
  have hrightPow : IntervalIntegrable (fun s : ℝ => (t - s) ^ (a - 1))
      volume m t := by
    have hb : IntervalIntegrable (fun z : ℝ => z ^ (a - 1)) volume 0 (t - m) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa only [sub_zero, sub_sub_cancel] using (hb.comp_sub_left t).symm
  have hleftRegular : ContinuousOn (fun s : ℝ => (t - s) ^ (a - 1))
      (uIcc t₀ m) := by
    rw [uIcc_of_le ht₀m.le]
    refine (continuous_const.sub continuous_id).continuousOn.rpow_const ?_
    intro s hs
    exact Or.inl (ne_of_gt (by linarith [hs.2] : 0 < t - s))
  have hrightRegular : ContinuousOn (fun s : ℝ => (s - t₀) ^ (-a))
      (uIcc m t) := by
    rw [uIcc_of_le hmt.le]
    refine (continuous_id.sub continuous_const).continuousOn.rpow_const ?_
    intro s hs
    exact Or.inl (ne_of_gt (by linarith [hs.1] : 0 < s - t₀))
  have hfleft : IntervalIntegrable f volume t₀ m := by
    exact hleftPow.continuousOn_mul hleftRegular
  have hfright : IntervalIntegrable f volume m t := by
    exact hrightPow.mul_continuousOn hrightRegular
  have hleftBound : (∫ s in t₀..m, f s) ≤ 1 / (1 - a) := by
    calc
      (∫ s in t₀..m, f s) ≤
          ∫ s in t₀..m, h ^ (a - 1) * (s - t₀) ^ (-a) := by
        apply intervalIntegral.integral_mono_on ht₀m.le hfleft
          (hleftPow.const_mul (h ^ (a - 1)))
        intro s hs
        change (t - s) ^ (a - 1) * (s - t₀) ^ (-a) ≤
          h ^ (a - 1) * (s - t₀) ^ (-a)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hh
            (by linarith [hs.2, hrightLen]) (by linarith))
          (Real.rpow_nonneg (sub_nonneg.mpr hs.1) _)
      _ = h ^ (a - 1) * (h ^ (1 - a) / (1 - a)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right (fun z : ℝ => z ^ (-a)) t₀,
          sub_self, integral_rpow (Or.inl (by linarith : -1 < -a)),
          Real.zero_rpow (by linarith : -a + 1 ≠ 0), sub_zero, hleftLen,
          show -a + 1 = 1 - a by ring]
      _ = 1 / (1 - a) := by
        rw [← mul_div_assoc, ← Real.rpow_add hh,
          show a - 1 + (1 - a) = 0 by ring, Real.rpow_zero]
  have hrightBound : (∫ s in m..t, f s) ≤ 1 / a := by
    calc
      (∫ s in m..t, f s) ≤
          ∫ s in m..t, h ^ (-a) * (t - s) ^ (a - 1) := by
        apply intervalIntegral.integral_mono_on hmt.le hfright
          (hrightPow.const_mul (h ^ (-a)))
        intro s hs
        change (t - s) ^ (a - 1) * (s - t₀) ^ (-a) ≤
          h ^ (-a) * (t - s) ^ (a - 1)
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hh
            (by linarith [hs.1, hleftLen]) (by linarith))
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)).trans_eq (by ring)
      _ = h ^ (-a) * (h ^ a / a) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_left (fun z : ℝ => z ^ (a - 1)) t,
          sub_self, integral_rpow (Or.inl (by linarith : -1 < a - 1)),
          Real.zero_rpow (by linarith : a - 1 + 1 ≠ 0), sub_zero, hrightLen,
          show a - 1 + 1 = a by ring]
      _ = 1 / a := by
        rw [← mul_div_assoc, ← Real.rpow_add hh,
          show -a + a = 0 by ring, Real.rpow_zero]
  refine ⟨hfleft.trans hfright, ?_⟩
  change (∫ s in t₀..t, f s) ≤ 1 / a + 1 / (1 - a)
  rw [← intervalIntegral.integral_add_adjacent_intervals hfleft hfright]
  linarith

/-- Both endpoint singularities are genuinely interval integrable. -/
theorem intervalIntegrable_weightedTimeKernel
    {t₀ t a : ℝ} (ht : t₀ < t) (ha : 0 < a) (ha1 : a < 1) :
    IntervalIntegrable (weightedTimeKernel t₀ t a) volume t₀ t :=
  (weightedTimeKernel_integrable_and_integral_le ht ha ha1).1

/-- The upper bound depends only on the exponent, not on `t - t₀`. -/
theorem integral_weightedTimeKernel_le
    {t₀ t a : ℝ} (ht : t₀ < t) (ha : 0 < a) (ha1 : a < 1) :
    (∫ s in t₀..t, weightedTimeKernel t₀ t a s) ≤
      1 / a + 1 / (1 - a) :=
  (weightedTimeKernel_integrable_and_integral_le ht ha ha1).2

end AnalyticPDE
end RicciFlow
