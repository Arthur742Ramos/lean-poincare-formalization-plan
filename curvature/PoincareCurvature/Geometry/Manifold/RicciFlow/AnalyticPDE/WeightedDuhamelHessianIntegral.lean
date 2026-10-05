module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedDuhamelIntegrand

/-!
# The actual time-integrated weighted Gaussian Hessian

Source-only candidate. No Lean compiler or proof runtime has been run.
The existing Gaussian integral and its cancellation estimate are unchanged.
The time majorant is proved integrable by the scalar two-endpoint argument,
not assumed integrable and not replaced by an abstract solver bound.

The spatial continuity and BCF bundle below are for the actual integral.
Actual second-derivative compatibility and the strong C² trace are separate
obligations; this file makes no assertion that they have been discharged.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The actual Gaussian cancellation estimate holds almost everywhere on the
integration interval. Only the terminal singleton is discarded; the initial
face is already excluded by `Ioc`. -/
lemma ae_norm_heatHessianEntryConvolution_le_weighted_envelope
    {n : ℕ} {t₀ t α L C : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc t₀ t →
      ‖heatHessianEntryConvolutionND (t - s) (q s) j k x‖ ≤
        (L * heatHessianEntryHolderMoment n α j k) *
          weightedHessianTimeEnvelope t₀ t α s := by
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hs]
    exact measure_singleton t
  filter_upwards [htne] with s hst hs
  have hst' : s < t := lt_of_le_of_ne hs.2 hst
  rw [Real.norm_eq_abs]
  exact abs_heatHessianEntryConvolutionND_le_weighted_envelope
    hα hs.1 hst' hL q (hqb s) (hqholder s ⟨hs.1, hst'⟩) x j k

/-- Positive-time spatial Hölder domination proves genuine interval
integrability of the existing Hessian convolution. The forcing need not have
a uniform unweighted Hölder constant, or a positive Hölder exponent at `t₀`.
-/
theorem intervalIntegrable_heatHessianEntryConvolution_of_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    IntervalIntegrable (fun s =>
      heatHessianEntryConvolutionND (t - s) (q s) j k x) volume t₀ t := by
  let A : ℝ := L * heatHessianEntryHolderMoment n α j k
  let g : ℝ → ℝ := fun s => A * weightedHessianTimeEnvelope t₀ t α s
  have hgint : IntervalIntegrable g volume t₀ t :=
    (intervalIntegrable_weightedHessianTimeEnvelope ht hα (by linarith)).const_mul A
  have hGm := aestronglyMeasurable_heatHessianEntryConvolution_time
    (t := t) hq x j k
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr ?_
  have hgOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hgint
  refine hgOn.mono' hGm.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact ae_norm_heatHessianEntryConvolution_le_weighted_envelope
    hα.le hL hqb hqholder x j k

/-- An interval-length-independent bound on the actual integrated Hessian
entry. The Gaussian moment and two-endpoint scalar integral are derived
dependencies, not hypotheses about a solution or inverse operator. -/
theorem abs_heatDuhamelHessianEntryND_le_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    |heatDuhamelHessianEntryND t₀ t q j k x| ≤
      heatHessianEntryHolderMoment n α j k * L *
        (1 / (α / 2) + 1 / (1 - α / 2)) := by
  let A : ℝ := L * heatHessianEntryHolderMoment n α j k
  let g : ℝ → ℝ := fun s => A * weightedHessianTimeEnvelope t₀ t α s
  have hA : 0 ≤ A := mul_nonneg hL (heatHessianEntryHolderMoment_nonneg n α j k)
  have hgint : IntervalIntegrable g volume t₀ t :=
    (intervalIntegrable_weightedHessianTimeEnvelope ht hα (by linarith)).const_mul A
  -- Establish actual integrability before estimating the totalized integral.
  have hGi := intervalIntegrable_heatHessianEntryConvolution_of_weighted
    ht hα hα1 hq hL hqb hqholder x j k
  have hae := ae_norm_heatHessianEntryConvolution_le_weighted_envelope
    hα.le hL hqb hqholder x j k
  have hm := intervalIntegral.norm_integral_le_of_norm_le ht.le hae hgint
  rw [Real.norm_eq_abs] at hm
  calc
    |heatDuhamelHessianEntryND t₀ t q j k x| ≤ ∫ s in t₀..t, g s := hm
    _ = A * (∫ s in t₀..t, weightedHessianTimeEnvelope t₀ t α s) := by
      exact intervalIntegral.integral_const_mul A _
    _ ≤ A * (1 / (α / 2) + 1 / (1 - α / 2)) :=
      mul_le_mul_of_nonneg_left
        (integral_weightedHessianTimeEnvelope_le ht hα (by linarith)) hA
    _ = heatHessianEntryHolderMoment n α j k * L *
        (1 / (α / 2) + 1 / (1 - α / 2)) := by dsimp [A]; ring

/-- Spatial continuity follows from the same integrable concrete time
majorant and continuity of the positive-time Gaussian convolution. -/
theorem continuous_heatDuhamelHessianEntryND_of_weighted
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (j k : Fin n) : Continuous (heatDuhamelHessianEntryND t₀ t q j k) := by
  let A : ℝ := L * heatHessianEntryHolderMoment n α j k
  let g : ℝ → ℝ := fun s => A * weightedHessianTimeEnvelope t₀ t α s
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc t₀ t)
  have hgintI : IntervalIntegrable g volume t₀ t :=
    (intervalIntegrable_weightedHessianTimeEnvelope ht hα (by linarith)).const_mul A
  have hgint : Integrable g μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hgintI
  have hmeas : ∀ x : Fin n → ℝ, AEStronglyMeasurable
      (fun s => heatHessianEntryConvolutionND (t - s) (q s) j k x) μ := by
    intro x
    exact (aestronglyMeasurable_heatHessianEntryConvolution_time
      (t := t) hq x j k).restrict
  have hbnd : ∀ x : Fin n → ℝ, ∀ᵐ s ∂μ,
      ‖heatHessianEntryConvolutionND (t - s) (q s) j k x‖ ≤ g s := by
    intro x
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_norm_heatHessianEntryConvolution_le_weighted_envelope
      hα.le hL hqb hqholder x j k
  have hcont : ∀ᵐ s ∂μ, Continuous (fun x : Fin n → ℝ =>
      heatHessianEntryConvolutionND (t - s) (q s) j k x) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
      rw [ae_iff, hs]
      exact measure_singleton t
    filter_upwards [htne] with s hst hs
    exact continuous_heatHessianEntryConvolutionND
      (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (q s).continuous
      (fun y => by simpa only [Real.norm_eq_abs] using hqb s y) j k
  have hc : Continuous (fun x : Fin n → ℝ =>
      ∫ s, heatHessianEntryConvolutionND (t - s) (q s) j k x ∂μ) :=
    continuous_of_dominated hmeas hbnd hgint hcont
  have heq : heatDuhamelHessianEntryND t₀ t q j k = fun x : Fin n → ℝ =>
      ∫ s, heatHessianEntryConvolutionND (t - s) (q s) j k x ∂μ := by
    funext x
    rw [heatDuhamelHessianEntryND, intervalIntegral.integral_of_le ht.le]
  rw [heq]
  exact hc

/-- BCF packaging of the actual weighted integral, without calling it an
actual derivative before derivative compatibility has been proved. -/
def weightedHeatDuhamelHessianEntryNDbcf
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (j k : Fin n) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatDuhamelHessianEntryND t₀ t q j k)
    (continuous_heatDuhamelHessianEntryND_of_weighted
      ht hα hα1 hq hL hqb hqholder j k)
    (heatHessianEntryHolderMoment n α j k * L *
      (1 / (α / 2) + 1 / (1 - α / 2)))
    (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_heatDuhamelHessianEntryND_le_weighted
        ht hα hα1 hq hL hqb hqholder x j k)

@[simp] theorem weightedHeatDuhamelHessianEntryNDbcf_apply
    {n : ℕ} {t₀ t α L C : ℝ} (ht : t₀ < t)
    (hα : 0 < α) (hα1 : α < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (hL : 0 ≤ L) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s ∈ Ioo t₀ t, ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (j k : Fin n) (x : Fin n → ℝ) :
    weightedHeatDuhamelHessianEntryNDbcf ht hα hα1 hq hL hqb hqholder j k x =
      heatDuhamelHessianEntryND t₀ t q j k x := rfl

end AnalyticPDE
end RicciFlow
