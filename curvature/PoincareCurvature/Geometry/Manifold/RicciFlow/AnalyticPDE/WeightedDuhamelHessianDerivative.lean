module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedDuhamelHessianIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Actual spatial derivatives of the weighted Gaussian Duhamel integral

Source-only candidate; no Lean elaboration or proof runtime has been run.
The forcing assumptions contain boundedness and positive-time weighted spatial
Hölder control only. The derivative and its integrable majorant are derived
from the actual Gaussian convolution and the scalar two-endpoint argument.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Genuine weighted differentiation under the time integral. The existing
Duhamel gradient coordinate has the existing integrated Hessian entry as its
actual coordinate derivative, including the diagonal case. -/
theorem hasDerivAt_heatDuhamelGradientCoordND_entry_of_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    HasDerivAt (fun a => heatDuhamelGradientCoordND t₀ t q k
      (Function.update x j a))
      (heatDuhamelHessianEntryND t₀ t q j k x) (x j) := by
  let F : ℝ → ℝ → ℝ := fun a s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x j a - y) *
      (-(Function.update x j a - y) k / (2 * (t - s)))) * q s y
  let F' : ℝ → ℝ → ℝ := fun a s =>
    heatHessianEntryConvolutionND (t - s) (q s) j k (Function.update x j a)
  let A : ℝ := L * heatHessianEntryHolderMoment n α j k
  let bound : ℝ → ℝ := fun s => A * weightedHessianTimeEnvelope t₀ t α s
  have hFmeas : ∀ᶠ a in 𝓝 (x j), AEStronglyMeasurable (F a)
      ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    filter_upwards with a
    exact (aestronglyMeasurable_gradient_heatKernelND_convolution_time
      (t := t) hq (Function.update x j a) k).restrict
  have hFint : IntervalIntegrable (F (x j)) volume t₀ t := by
    simpa only [F, Function.update_eq_self] using
      intervalIntegrable_gradient_heatKernelND_convolution ht.le hq hqb x k
  have hF'meas : AEStronglyMeasurable (F' (x j))
      ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    simpa only [F', Function.update_eq_self] using
      (aestronglyMeasurable_heatHessianEntryConvolution_time
        (t := t) hq x j k).restrict
  have hbint : IntervalIntegrable bound volume t₀ t :=
    (intervalIntegrable_weightedHessianTimeEnvelope
      ht hα (show α < 2 by linarith)).const_mul A
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hs]
    exact measure_singleton t
  -- The bound is simultaneous for all spatial parameters. It is proved
  -- pointwise from the Gaussian cancellation estimate, not obtained by
  -- interchanging an uncountable quantifier with an almost-everywhere one.
  have hbnd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), ‖F' a s‖ ≤ bound s := by
    filter_upwards [htne] with s hst hs a _
    rw [uIoc_of_le ht.le] at hs
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    rw [Real.norm_eq_abs]
    exact abs_heatHessianEntryConvolutionND_le_weighted_envelope
      hα.le hs.1 hst' hL q (hqb s)
      (hqholder s ⟨hs.1, hst'⟩) (Function.update x j a) j k
  have hdiff : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), HasDerivAt (fun a => F a s) (F' a s) a := by
    filter_upwards [htne] with s hst hs a _
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hupd : ∀ b : ℝ, Function.update (Function.update x j a) j b =
        Function.update x j b := by
      intro b
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [Function.update_of_ne hij]
    simpa only [F, F', heatHessianEntryConvolutionND, hupd,
      Function.update_self] using
        hasDerivAt_heatSemigroupND_coordGradient_entry hpos
          (Function.update x j a) j k (q s).continuous.aestronglyMeasurable (hqb s)
  have hout := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := t₀) (b := t) (F := F) (F' := F') (x₀ := x j)
    (s := Set.univ) Filter.univ_mem hFmeas hFint hF'meas hbnd hbint hdiff
  simpa only [heatDuhamelGradientCoordND, heatDuhamelHessianEntryND, F, F',
    Function.update_eq_self] using hout.2

/-- The weighted BCF entry is the actual iterated coordinate derivative of
the raw Duhamel potential. No distinction of the two indices is required. -/
theorem hasDerivAt_partial_heatDuhamelND_coord_entry_of_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    HasDerivAt
      (fun a => deriv (fun b => ∫ s in t₀..t,
        heatSemigroupND (t - s) (q s)
          (Function.update (Function.update x j a) k b))
        ((Function.update x j a) k))
      (weightedHeatDuhamelHessianEntryNDbcf
        ht hα hα1 hq hL hqb hqholder j k x) (x j) := by
  let P : (Fin n → ℝ) → ℝ := fun z => deriv (fun b => ∫ s in t₀..t,
    heatSemigroupND (t - s) (q s) (Function.update z k b)) (z k)
  have hP : P = heatDuhamelGradientCoordND t₀ t q k := by
    funext z
    have hd := hasDerivAt_heatDuhamelND_coord ht.le hq hqb z k
    simpa only [P, heatDuhamelGradientCoordND] using hd.deriv
  change HasDerivAt (fun a => P (Function.update x j a)) _ (x j)
  rw [hP]
  simpa only [weightedHeatDuhamelHessianEntryNDbcf_apply] using
    hasDerivAt_heatDuhamelGradientCoordND_entry_of_weighted
      ht hα hα1 hq hL hqb hqholder x j k

/-- Equality of the actual iterated coordinate derivative with the raw
Gaussian Hessian integral, for every pair of derivative indices. -/
theorem deriv_partial_heatDuhamelND_coord_entry_eq_of_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    deriv
      (fun a => deriv (fun b => ∫ s in t₀..t,
        heatSemigroupND (t - s) (q s)
          (Function.update (Function.update x j a) k b))
        ((Function.update x j a) k)) (x j) =
      heatDuhamelHessianEntryND t₀ t q j k x := by
  simpa only [weightedHeatDuhamelHessianEntryNDbcf_apply] using
    (hasDerivAt_partial_heatDuhamelND_coord_entry_of_weighted
      ht hα hα1 hq hL hqb hqholder x j k).deriv

end AnalyticPDE
end RicciFlow
