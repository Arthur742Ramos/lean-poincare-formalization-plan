module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp

/-!
# A uniformly continuous C0 datum gives a vanishing C2 heat regularizer

SOURCE ONLY, UNCOMPILED. For a bounded uniformly continuous scalar datum q,
the actual Gaussian heat Hessian entries multiplied by h tend uniformly to
zero as h tends to zero from the right. The proof uses zero kernel mass and
the actual first moments of an integrable positive Gaussian Hessian majorant.
It assumes neither C2 regularity of q nor a positive Holder modulus.

The quantitative estimate is 2 epsilon + L sqrt(h) C(n,j,k), where
L = 2 norm(q) / delta comes from an arbitrary uniform continuity modulus.
This is an epsilon/delta argument, not a claimed fixed positive h-power rate.
It is a linear Euclidean supporting leaf; canonical Point 4 remains OPEN.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000

open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The positive diagonal Gaussian Hessian majorant, with exact mass 1/h. -/
def heatHessianMajorantND {n : ℕ} (h : ℝ) (z : Fin n → ℝ) (k : Fin n) : ℝ :=
  heatKernelND h z * (z k ^ 2 / (4 * h ^ 2) + 1 / (2 * h))

lemma heatHessianMajorantND_nonneg {n : ℕ} {h : ℝ} (hh : 0 < h)
    (z : Fin n → ℝ) (k : Fin n) : 0 ≤ heatHessianMajorantND h z k := by
  unfold heatHessianMajorantND
  exact mul_nonneg (heatKernelND_nonneg hh z) (by positivity)

lemma integrable_heatHessianMajorantND {n : ℕ} {h : ℝ} (hh : 0 < h)
    (k : Fin n) : Integrable (fun z => heatHessianMajorantND h z k) :=
  integrable_heatKernelND_mul_sq_coord_add_inv hh k

lemma integral_heatHessianMajorantND {n : ℕ} {h : ℝ} (hh : 0 < h)
    (k : Fin n) : (∫ z : Fin n → ℝ, heatHessianMajorantND h z k) = 1 / h :=
  heatKernelND_mul_sq_coord_add_inv_integral_eq hh k

/-- One positive pair controls every actual mixed or diagonal Hessian entry. -/
lemma abs_heatHessianKernelEntryND_le_majorantPair
    {n : ℕ} {h : ℝ} (hh : 0 < h) (z : Fin n → ℝ) (j k : Fin n) :
    |heatHessianKernelEntryND h z j k| ≤
      heatHessianMajorantND h z j + heatHessianMajorantND h z k := by
  by_cases hjk : j = k
  · subst j
    rw [heatHessianKernelEntryND_diag, abs_mul,
      abs_of_nonneg (heatKernelND_nonneg hh z)]
    have hb := mul_le_mul_of_nonneg_left (sq_sub_inv_le_add h hh (z k))
      (heatKernelND_nonneg hh z)
    exact hb.trans (le_add_of_nonneg_right (heatHessianMajorantND_nonneg hh z k))
  · exact abs_heatHessianKernelEntryND_offdiag_le hh z hjk

/-- The fixed first moment of the positive majorant in one coordinate. -/
def heatHessianMajorantFirstMoment {n : ℕ} (ell k : Fin n) : ℝ :=
  if ell = k then gaussianAbsMoment 3 / 4 + gaussianAbsMoment 1 / 2
  else gaussianAbsMoment 1

/-- An explicit finite, time-independent Gaussian constant. -/
def heatHessianMajorantPairFirstMoment {n : ℕ} (j k : Fin n) : ℝ :=
  ∑ ell : Fin n,
    (heatHessianMajorantFirstMoment ell j + heatHessianMajorantFirstMoment ell k)

lemma integrable_abs_coord_mul_heatHessianMajorantND
    {n : ℕ} {h : ℝ} (hh : 0 < h) (ell k : Fin n) :
    Integrable (fun z : Fin n → ℝ => |z ell| * heatHessianMajorantND h z k) := by
  simpa only [Real.rpow_one, heatHessianMajorantND, mul_assoc] using
    integrable_abs_coord_rpow_secondDeriv_majorantND hh (by norm_num : (0 : ℝ) ≤ 1) ell k

/-- Genuine Gaussian moment scaling after multiplication by the time h.
The diagonal uses the first and third Gaussian moments, and transverse
coordinates use the first moment and the majorant's mass 1/h. -/
theorem time_mul_integral_abs_coord_heatHessianMajorantND
    {n : ℕ} {h : ℝ} (hh : 0 < h) (ell k : Fin n) :
    h * (∫ z : Fin n → ℝ, |z ell| * heatHessianMajorantND h z k) =
      Real.sqrt h * heatHessianMajorantFirstMoment ell k := by
  by_cases hell : ell = k
  · subst ell
    have hm := integral_abs_coord_rpow_secondDeriv_majorantND_diag_eq
      hh (by norm_num : (0 : ℝ) ≤ 1) k
    have hpow : (Real.sqrt h) ^ (3 : ℝ) = (Real.sqrt h) ^ (3 : ℕ) :=
      Real.rpow_natCast _ 3
    have hcube : (Real.sqrt h) ^ (3 : ℕ) = h * Real.sqrt h := by
      calc
        (Real.sqrt h) ^ (3 : ℕ) = (Real.sqrt h) ^ (2 : ℕ) * Real.sqrt h := by ring
        _ = h * Real.sqrt h := by rw [Real.sq_sqrt hh.le]
    have hm' : (∫ z : Fin n → ℝ, |z k| * heatHessianMajorantND h z k) =
        (1 / (4 * h ^ 2)) * (h * Real.sqrt h * gaussianAbsMoment 3) +
          (1 / (2 * h)) * (Real.sqrt h * gaussianAbsMoment 1) := by
      simpa only [show (1 : ℝ) + 2 = 3 by norm_num, Real.rpow_one,
        hpow, hcube, heatHessianMajorantND, mul_assoc] using hm
    rw [hm']
    simp only [heatHessianMajorantFirstMoment, if_pos rfl]
    field_simp [hh.ne']
    <;> ring
  · have hm := integral_abs_coord_rpow_secondDeriv_majorantND_offdiag_eq
      hh (by norm_num : (0 : ℝ) ≤ 1) ell k hell
    have hm' : (∫ z : Fin n → ℝ, |z ell| * heatHessianMajorantND h z k) =
        (Real.sqrt h * gaussianAbsMoment 1) * (1 / h) := by
      simpa only [Real.rpow_one, heatHessianMajorantND, mul_assoc] using hm
    rw [hm']
    simp only [heatHessianMajorantFirstMoment, if_neg hell]
    field_simp [hh.ne']
    <;> ring

/-- An arbitrary continuity modulus gives an affine coordinate increment
bound. The constant term can be arbitrarily small; the affine coefficient
may depend on that modulus. This is not a Holder assumption. -/
lemma abs_boundedContinuous_sub_le_affine_modulus
    {n : ℕ} {delta epsilon : ℝ} (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ)
    (hmod : ∀ y, ‖y - x‖ < delta → |q y - q x| ≤ epsilon)
    (y : Fin n → ℝ) :
    |q y - q x| ≤ epsilon + (2 * ‖q‖ / delta) * ∑ ell : Fin n, |(x - y) ell| := by
  classical
  let L : ℝ := 2 * ‖q‖ / delta
  have hL : 0 ≤ L := by dsimp [L]; positivity
  by_cases hnear : ‖y - x‖ < delta
  · exact (hmod y hnear).trans (le_add_of_nonneg_right
      (mul_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  · have hb : |q y - q x| ≤ 2 * ‖q‖ := by
      calc
        |q y - q x| ≤ |q y| + |q x| := abs_sub _ _
        _ ≤ ‖q‖ + ‖q‖ := add_le_add
          (by simpa only [Real.norm_eq_abs] using q.norm_coe_le_norm y)
          (by simpa only [Real.norm_eq_abs] using q.norm_coe_le_norm x)
        _ = 2 * ‖q‖ := by ring
    have htail : 2 * ‖q‖ ≤ L * ‖y - x‖ := by
      have ht := mul_le_mul_of_nonneg_left (le_of_not_gt hnear) hL
      have hc : L * delta = 2 * ‖q‖ := div_mul_cancel₀ _ hdelta.ne'
      rwa [hc] at ht
    calc
      |q y - q x| ≤ L * ‖y - x‖ := hb.trans htail
      _ = L * ‖x - y‖ := by rw [norm_sub_rev]
      _ ≤ L * ∑ ell : Fin n, |(x - y) ell| :=
        mul_le_mul_of_nonneg_left
          (PoincareCurvature.FiniteMomentApproximation.norm_le_sum_abs_coord (x - y)) hL
      _ ≤ epsilon + L * ∑ ell : Fin n, |(x - y) ell| :=
        le_add_of_nonneg_left hepsilon

/-- The key actual-kernel estimate. Cancellation removes the constant datum;
the positive majorant's mass and first moments supply the exact h scaling. -/
theorem abs_time_mul_heatHessianEntryConvolutionND_le_modulus
    {n : ℕ} {h delta epsilon : ℝ} (hh : 0 < h) (hdelta : 0 < delta)
    (hepsilon : 0 ≤ epsilon)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ)
    (hmod : ∀ y, ‖y - x‖ < delta → |q y - q x| ≤ epsilon)
    (j k : Fin n) :
    |h * heatHessianEntryConvolutionND h q j k x| ≤
      2 * epsilon + (2 * ‖q‖ / delta) * Real.sqrt h *
        heatHessianMajorantPairFirstMoment j k := by
  classical
  let M : (Fin n → ℝ) → ℝ := fun z =>
    heatHessianMajorantND h z j + heatHessianMajorantND h z k
  let L : ℝ := 2 * ‖q‖ / delta
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : Integrable M :=
    (integrable_heatHessianMajorantND hh j).add (integrable_heatHessianMajorantND hh k)
  have hMnonneg : ∀ z, 0 ≤ M z := fun z => add_nonneg
    (heatHessianMajorantND_nonneg hh z j) (heatHessianMajorantND_nonneg hh z k)
  have hWi : ∀ ell : Fin n, Integrable (fun z => |z ell| * M z) := by
    intro ell
    simpa only [M, mul_add] using
      (integrable_abs_coord_mul_heatHessianMajorantND hh ell j).add
        (integrable_abs_coord_mul_heatHessianMajorantND hh ell k)
  have hmass : h * (∫ z : Fin n → ℝ, M z) = 2 := by
    rw [integral_add (integrable_heatHessianMajorantND hh j)
      (integrable_heatHessianMajorantND hh k),
      integral_heatHessianMajorantND hh j, integral_heatHessianMajorantND hh k]
    field_simp [hh.ne']
    <;> ring
  have hmom : h * (∑ ell : Fin n, ∫ z : Fin n → ℝ, |z ell| * M z) =
      Real.sqrt h * heatHessianMajorantPairFirstMoment j k := by
    rw [Finset.mul_sum]
    rw [heatHessianMajorantPairFirstMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ell _
    simp only [M, mul_add]
    rw [integral_add (integrable_abs_coord_mul_heatHessianMajorantND hh ell j)
      (integrable_abs_coord_mul_heatHessianMajorantND hh ell k), mul_add,
      time_mul_integral_abs_coord_heatHessianMajorantND hh ell j,
      time_mul_integral_abs_coord_heatHessianMajorantND hh ell k]
    ring
  have htransWi : ∀ ell : Fin n,
      (∫ y : Fin n → ℝ, |(x - y) ell| * M (x - y)) =
        ∫ z : Fin n → ℝ, |z ell| * M z := fun ell =>
    integral_sub_left_eq_self (fun z : Fin n → ℝ => |z ell| * M z) volume x
  have hdom : Integrable (fun y : Fin n → ℝ =>
      M (x - y) * epsilon + L * ∑ ell : Fin n, |(x - y) ell| * M (x - y)) :=
    ((hM.comp_sub_left x).mul_const epsilon).add
      ((integrable_finset_sum _ (fun ell _ => (hWi ell).comp_sub_left x)).const_mul L)
  have hbound : |heatHessianEntryConvolutionND h q j k x| ≤
      epsilon * (∫ z : Fin n → ℝ, M z) +
        L * ∑ ell : Fin n, ∫ z : Fin n → ℝ, |z ell| * M z := by
    rw [heatHessianEntryConvolutionND,
      heatHessianKernelEntryND_convolution_eq_increment hh x j k
        q.continuous.aestronglyMeasurable (fun y => q.norm_coe_le_norm y),
      ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ y : Fin n → ℝ,
          M (x - y) * epsilon + L * ∑ ell : Fin n, |(x - y) ell| * M (x - y) := by
        refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have hi := abs_boundedContinuous_sub_le_affine_modulus
          hdelta hepsilon q x hmod y
        calc
          |heatHessianKernelEntryND h (x - y) j k| * |q y - q x| ≤
              M (x - y) * |q y - q x| :=
            mul_le_mul_of_nonneg_right
              (abs_heatHessianKernelEntryND_le_majorantPair hh (x - y) j k)
              (abs_nonneg _)
          _ ≤ M (x - y) * (epsilon + L * ∑ ell : Fin n, |(x - y) ell|) :=
            mul_le_mul_of_nonneg_left hi (hMnonneg _)
          _ = _ := by
            simp only [mul_add, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
        rw [integral_add ((hM.comp_sub_left x).mul_const epsilon)
          ((integrable_finset_sum _ (fun ell _ => (hWi ell).comp_sub_left x)).const_mul L),
          integral_mul_const, integral_const_mul,
          integral_finset_sum _ (fun ell _ => (hWi ell).comp_sub_left x),
          integral_sub_left_eq_self M volume x]
        simp only [htransWi]
        ring
  rw [abs_mul, abs_of_pos hh]
  calc
    h * |heatHessianEntryConvolutionND h q j k x| ≤
        h * (epsilon * (∫ z : Fin n → ℝ, M z) +
          L * ∑ ell : Fin n, ∫ z : Fin n → ℝ, |z ell| * M z) :=
      mul_le_mul_of_nonneg_left hbound hh.le
    _ = epsilon * (h * (∫ z : Fin n → ℝ, M z)) +
        L * (h * (∑ ell : Fin n, ∫ z : Fin n → ℝ, |z ell| * M z)) := by ring
    _ = _ := by rw [hmass, hmom]; dsimp [L]; ring

/-- The weighted actual Hessian is uniformly bounded for every bounded C0
datum. Unlike the trace theorem, this bound needs no uniform continuity. -/
theorem abs_time_mul_heatHessianEntryConvolutionND_le
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (j k : Fin n) (x : Fin n → ℝ) :
    |h * heatHessianEntryConvolutionND h q j k x| ≤ 2 * ‖q‖ := by
  let M : (Fin n → ℝ) → ℝ := fun z =>
    heatHessianMajorantND h z j + heatHessianMajorantND h z k
  have hM : Integrable M :=
    (integrable_heatHessianMajorantND hh j).add (integrable_heatHessianMajorantND hh k)
  have hmass : (∫ z : Fin n → ℝ, M z) = 1 / h + 1 / h := by
    rw [integral_add (integrable_heatHessianMajorantND hh j)
      (integrable_heatHessianMajorantND hh k),
      integral_heatHessianMajorantND hh j, integral_heatHessianMajorantND hh k]
  have hb : |heatHessianEntryConvolutionND h q j k x| ≤
      (1 / h + 1 / h) * ‖q‖ := by
    rw [heatHessianEntryConvolutionND, ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ y : Fin n → ℝ, M (x - y) * ‖q‖ := by
        refine norm_integral_le_of_norm_le ((hM.comp_sub_left x).mul_const ‖q‖)
          (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have hqb : |q y| ≤ ‖q‖ := by
          simpa only [Real.norm_eq_abs] using q.norm_coe_le_norm y
        exact mul_le_mul
          (abs_heatHessianKernelEntryND_le_majorantPair hh (x - y) j k)
          hqb (abs_nonneg _) (add_nonneg
            (heatHessianMajorantND_nonneg hh _ j) (heatHessianMajorantND_nonneg hh _ k))
      _ = _ := by rw [integral_mul_const, integral_sub_left_eq_self M volume x, hmass]
  rw [abs_mul, abs_of_pos hh]
  calc
    h * |heatHessianEntryConvolutionND h q j k x| ≤
        h * ((1 / h + 1 / h) * ‖q‖) := mul_le_mul_of_nonneg_left hb hh.le
    _ = 2 * ‖q‖ := by
      field_simp [hh.ne']
      <;> ring

/-- The actual weighted Hessian entry as a BCF, with no Holder constructor
and no fallback at positive time. Its value is literally the Gaussian integral. -/
def timeMulHeatHessianEntryNDbcf
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (j k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => h * heatHessianEntryConvolutionND h q j k x)
    (continuous_const.mul (continuous_heatHessianEntryConvolutionND (C := ‖q‖)
      hh q.continuous
      (fun y => by simpa only [Real.norm_eq_abs] using q.norm_coe_le_norm y) j k))
    (2 * ‖q‖) (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_time_mul_heatHessianEntryConvolutionND_le hh q j k x)

@[simp] theorem timeMulHeatHessianEntryNDbcf_apply
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (j k : Fin n) (x : Fin n → ℝ) :
    timeMulHeatHessianEntryNDbcf hh q j k x =
      h * heatHessianEntryConvolutionND h q j k x := rfl

/-- A globally defined path for expressing the strong zero trace. Only its
positive branch is used in the convergence proof. -/
def timeMulHeatHessianEntryPathBcf
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (j k : Fin n) (h : ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  if hh : 0 < h then timeMulHeatHessianEntryNDbcf hh q j k else 0

theorem timeMulHeatHessianEntryPathBcf_apply_of_pos
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (j k : Fin n) (x : Fin n → ℝ) :
    timeMulHeatHessianEntryPathBcf q j k h x =
      h * heatHessianEntryConvolutionND h q j k x := by
  rw [timeMulHeatHessianEntryPathBcf, dif_pos hh]
  rfl

/-- UC, bounded C0 data suffice for uniform vanishing of every actual heat
Hessian entry multiplied by h. No derivative of q occurs in the assumptions. -/
theorem tendstoUniformly_time_mul_heatHessianEntryConvolutionND_zero
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hq : UniformContinuous (q : (Fin n → ℝ) → ℝ)) (j k : Fin n) :
    TendstoUniformly (fun h x => h * heatHessianEntryConvolutionND h q j k x)
      (fun _ => 0) (𝓝[>] 0) := by
  apply Metric.tendstoUniformly_iff.2
  intro eta heta
  obtain ⟨delta, hdelta, hmod⟩ := Metric.uniformContinuous_iff.mp hq
    (eta / 4) (by positivity)
  let A : ℝ := (2 * ‖q‖ / delta) * heatHessianMajorantPairFirstMoment j k
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, A * Real.sqrt h < eta / 2 := by
    have hc : Continuous (fun h : ℝ => A * Real.sqrt h) :=
      continuous_const.mul Real.continuous_sqrt
    have ht : Tendsto (fun h : ℝ => A * Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero, mul_zero] using
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iio_mem_nhds (by positivity : 0 < eta / 2))
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hsmall hh
  intro x
  have hb := abs_time_mul_heatHessianEntryConvolutionND_le_modulus hh hdelta
    (by positivity : 0 ≤ eta / 4) q x (fun y hy => by
      have hm := hmod (show dist y x < delta by simpa only [dist_eq_norm] using hy)
      exact le_of_lt (by simpa only [Real.dist_eq] using hm)) j k
  have hA : (2 * ‖q‖ / delta) * Real.sqrt h *
      heatHessianMajorantPairFirstMoment j k = A * Real.sqrt h := by dsimp [A]; ring
  rw [hA] at hb
  rw [Real.dist_eq, zero_sub, abs_neg]
  linarith

/-- The same actual UC cancellation proves the Cb norm trace, which is the
negative-branch Hessian-norm leaf needed by a later two-sided integration. -/
theorem tendsto_timeMulHeatHessianEntryPathBcf_zero
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hq : UniformContinuous (q : (Fin n → ℝ) → ℝ)) (j k : Fin n) :
    Tendsto (timeMulHeatHessianEntryPathBcf q j k) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro eta heta
  have hraw := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_time_mul_heatHessianEntryConvolutionND_zero q hq j k)
    (eta / 2) (half_pos heta)
  filter_upwards [hraw, self_mem_nhdsWithin] with h hraw hh
  rw [dist_eq_norm, sub_zero]
  have hb : ‖timeMulHeatHessianEntryPathBcf q j k h‖ ≤ eta / 2 := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    rw [timeMulHeatHessianEntryPathBcf_apply_of_pos hh, Real.norm_eq_abs]
    exact le_of_lt (by simpa only [Real.dist_eq, zero_sub, abs_neg] using hraw x)
  exact hb.trans_lt (half_lt_self heta)

/-- The value jet needs only boundedness, by the genuine Gaussian contraction. -/
theorem tendstoUniformly_time_mul_heatSemigroupND_zero
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    TendstoUniformly (fun h x => h * heatSemigroupND h q x)
      (fun _ => 0) (𝓝[>] 0) := by
  apply Metric.tendstoUniformly_iff.2
  intro eta heta
  have hc : Continuous (fun h : ℝ => h * ‖q‖) := continuous_id.mul continuous_const
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h * ‖q‖ < eta := by
    have ht : Tendsto (fun h : ℝ => h * ‖q‖) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_mul] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iio_mem_nhds heta)
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hsmall hh
  intro x
  rw [Real.dist_eq, zero_sub, abs_neg, abs_mul, abs_of_pos hh]
  exact (mul_le_mul_of_nonneg_left (abs_heatSemigroupND_le hh x
    (fun y => by simpa only [Real.norm_eq_abs] using q.norm_coe_le_norm y)) hh.le).trans_lt hsmall

/-- The first coordinate jet is O(sqrt(h)) for bounded C0 data. -/
theorem tendstoUniformly_time_mul_heatSemigroupGradientCoordND_zero
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) :
    TendstoUniformly (fun h x => h * heatSemigroupGradientCoordND h q k x)
      (fun _ => 0) (𝓝[>] 0) := by
  apply Metric.tendstoUniformly_iff.2
  intro eta heta
  let A : ℝ := ‖q‖ / Real.sqrt π
  have hc : Continuous (fun h : ℝ => A * Real.sqrt h) :=
    continuous_const.mul Real.continuous_sqrt
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, A * Real.sqrt h < eta := by
    have ht : Tendsto (fun h : ℝ => A * Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero, mul_zero] using
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iio_mem_nhds heta)
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hsmall hh
  intro x
  have hb : |heatSemigroupGradientCoordND h q k x| ≤ ‖q‖ / Real.sqrt (π * h) :=
    heatSemigroupND_coord_deriv_integral_bound hh x k
      q.continuous.aestronglyMeasurable (fun y => q.norm_coe_le_norm y)
  have hscale : h * (‖q‖ / Real.sqrt (π * h)) = A * Real.sqrt h := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
    dsimp [A]
    have hs : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt hh.le
    have hsp : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hsh : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
    field_simp [hsp, hsh]
    nlinarith [congrArg (fun a : ℝ => a * ‖q‖) hs]
  rw [Real.dist_eq, zero_sub, abs_neg, abs_mul, abs_of_pos hh]
  exact ((mul_le_mul_of_nonneg_left hb hh.le).trans_eq hscale).trans_lt hsmall

/-- All value, first-coordinate and full mixed second-coordinate jets vanish
uniformly. The same datum has no assumed first or second derivatives. -/
theorem heatRegularizer_C0_C1_C2_uniform_zero
    {n : ℕ} (q : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hq : UniformContinuous (q : (Fin n → ℝ) → ℝ)) :
    TendstoUniformly (fun h x => h * heatSemigroupND h q x)
      (fun _ => 0) (𝓝[>] 0) ∧
    (∀ k : Fin n, TendstoUniformly
      (fun h x => h * heatSemigroupGradientCoordND h q k x)
      (fun _ => 0) (𝓝[>] 0)) ∧
    (∀ j k : Fin n, TendstoUniformly
      (fun h x => h * heatHessianEntryConvolutionND h q j k x)
      (fun _ => 0) (𝓝[>] 0)) := by
  exact ⟨tendstoUniformly_time_mul_heatSemigroupND_zero q,
    fun k => tendstoUniformly_time_mul_heatSemigroupGradientCoordND_zero q k,
    fun j k => tendstoUniformly_time_mul_heatHessianEntryConvolutionND_zero q hq j k⟩

/-- The stated first jet is the actual coordinate derivative of h H_h q. -/
theorem hasDerivAt_time_mul_heatSemigroupND_coord
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun a => h * heatSemigroupND h q (Function.update x k a))
      (h * heatSemigroupGradientCoordND h q k x) (x k) := by
  simpa only [smul_eq_mul, heatSemigroupGradientCoordND, Function.update_eq_self] using
    (hasDerivAt_heatSemigroupND_coord_update hh x k
      q.continuous.aestronglyMeasurable (fun y => q.norm_coe_le_norm y) (x k)).fun_const_smul h

/-- Every stated mixed second jet is an actual derivative of the first jet. -/
theorem hasDerivAt_time_mul_heatSemigroupGradientCoordND_entry
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : BoundedContinuousFunction (Fin n → ℝ) ℝ) (j k : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun a => h * heatSemigroupGradientCoordND h q k (Function.update x j a))
      (h * heatHessianEntryConvolutionND h q j k x) (x j) := by
  simpa only [smul_eq_mul, heatSemigroupGradientCoordND, heatHessianEntryConvolutionND] using
    (hasDerivAt_heatSemigroupND_coordGradient_entry hh x j k
      q.continuous.aestronglyMeasurable (fun y => q.norm_coe_le_norm y)).fun_const_smul h

end AnalyticPDE
end RicciFlow
