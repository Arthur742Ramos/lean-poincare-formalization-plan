module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelClassical

/-!
# Time differentiation of the Euclidean Duhamel potential

This module proves the generator identity for the Euclidean heat semigroup on
globally coordinatewise Hölder data and uses it to identify the time
derivative of the inhomogeneous Duhamel potential.  The endpoint singularity
is genuine: the heat-kernel Hessian is bounded by `u ^ (-1 + r / 2)`, which is
integrable precisely because `r > 0`.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-! ## The homogeneous heat generator -/

/-- Additivity of one bundled coordinate Hessian of the heat semigroup. -/
theorem heatHessianCoordNDbcf_add {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (f g : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDbcf ht (f + g) k =
      heatHessianCoordNDbcf ht f k + heatHessianCoordNDbcf ht g k := by
  ext x
  simp only [heatHessianCoordNDbcf_apply, BoundedContinuousFunction.add_apply]
  rw [heatHessianCoordConvolutionND]
  have hf := integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
    f.continuous.aestronglyMeasurable
    (fun y => le_trans (f.norm_coe_le_norm y) (le_max_left ‖f‖ ‖g‖))
  have hg := integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
    g.continuous.aestronglyMeasurable
    (fun y => le_trans (g.norm_coe_le_norm y) (le_max_right ‖f‖ ‖g‖))
  change (∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * (f + g) y) =
    (∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) +
    ∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * g y
  rw [← integral_add hf hg]
  apply integral_congr_ae
  filter_upwards with y
  rw [BoundedContinuousFunction.add_apply]
  ring

/-- Real-scalar homogeneity of one bundled coordinate Hessian. -/
theorem heatHessianCoordNDbcf_smul {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (c : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDbcf ht (c • f) k =
      c • heatHessianCoordNDbcf ht f k := by
  ext x
  simp only [heatHessianCoordNDbcf_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, heatHessianCoordConvolutionND]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Sup-norm operator estimate for a bundled heat Hessian coordinate. -/
theorem norm_heatHessianCoordNDbcf_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) :
    ‖heatHessianCoordNDbcf ht f k‖ ≤ ‖f‖ / t := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [heatHessianCoordNDbcf_apply, Real.norm_eq_abs]
  simpa only [heatHessianCoordConvolutionND] using
    heatSemigroupND_coord_second_deriv_integral_bound ht x k
      f.continuous.aestronglyMeasurable (fun y => f.norm_coe_le_norm y)

/-- One coordinate of the heat Hessian as a bounded linear operator on the
global sup-norm space. -/
noncomputable def heatHessianCoordNDclm {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ →L[ℝ]
      BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => heatHessianCoordNDbcf ht f k
      map_add' := heatHessianCoordNDbcf_add ht k
      map_smul' := fun (c : ℝ) f => by
        simpa using heatHessianCoordNDbcf_smul ht k c f }
    (1 / t)
    (fun f => by
      calc
        ‖heatHessianCoordNDbcf ht f k‖ ≤ ‖f‖ / t :=
          norm_heatHessianCoordNDbcf_le ht f k
        _ = (1 / t) * ‖f‖ := by ring)

@[simp] theorem heatHessianCoordNDclm_apply {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDclm ht k f = heatHessianCoordNDbcf ht f k := rfl

/-- At fixed positive heat time, a coordinate Hessian applied to a continuous
BCF-valued source varies continuously with the source time. -/
theorem continuous_heatHessianCoordConvolutionND_comp_sub_time
    {n : ℕ} {u : ℝ} (hu : 0 < u) (k : Fin n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (x : Fin n → ℝ) :
    Continuous (fun t => heatHessianCoordConvolutionND u (q (t - u)) k x) := by
  have hs : Continuous (fun t : ℝ => q (t - u)) :=
    hq.comp (continuous_id.sub continuous_const)
  have hop : Continuous (fun t : ℝ => heatHessianCoordNDclm hu k (q (t - u))) :=
    (heatHessianCoordNDclm hu k).continuous.comp hs
  have heval := (continuous_eval_const x).comp hop
  convert heval using 1
  funext t
  rfl

/-- The spatial Laplacian of a homogeneous Euclidean heat evolution, written
as the finite trace of its heat-kernel Hessian. -/
def heatSemigroupLaplacianND {n : ℕ} (t : ℝ)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, heatHessianCoordConvolutionND t w k x

/-- The actual positive-time derivative of the homogeneous heat semigroup is
its heat-kernel Laplacian. -/
theorem hasDerivAt_heatSemigroupND_time_eq_laplacian
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s => heatSemigroupND s (⇑w) x)
      (heatSemigroupLaplacianND t w x) t := by
  have htime := hasDerivAt_heatSemigroupND_time ht x
    w.continuous.aestronglyMeasurable (fun y => w.norm_coe_le_norm y)
  convert htime using 1
  rw [heatSemigroupLaplacianND]
  change (∑ k : Fin n, ∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * w y) = _
  calc
    _ = ∫ y : Fin n → ℝ, ∑ k : Fin n,
        (heatKernelND t (x - y) *
          ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * w y := by
      rw [integral_finsetSum]
      intro k _
      exact integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
        w.continuous.aestronglyMeasurable (fun y => w.norm_coe_le_norm y)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- For globally coordinatewise Hölder data, the positive-time heat
Laplacian is integrable all the way down to heat time zero. -/
theorem intervalIntegrable_heatSemigroupLaplacianND
    {n : ℕ} {T r : ℝ} (hT : 0 ≤ T) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    IntervalIntegrable (fun u => heatSemigroupLaplacianND u w x)
      volume 0 T := by
  have hk : ∀ k : Fin n, IntervalIntegrable
      (fun u => heatHessianCoordConvolutionND u w k x) volume 0 T := by
    intro k
    have hi := intervalIntegrable_hessian_heatKernelND_convolution
      (n := n) (t₀ := 0) (t := T) (r := r) hT hr0
      (q := fun _ => w) continuous_const hH
      (fun _ y => w.norm_coe_le_norm y) (fun _ a b => by
        calc
          |w b - w a| ≤ H * ∑ j : Fin n, |(b - a) j| ^ r := hholder b a
          _ = H * ∑ j : Fin n, |(a - b) j| ^ r := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            simp only [Pi.sub_apply, abs_sub_comm]) x k
    have hc := hi.comp_sub_left T
    simpa only [sub_zero, sub_self, sub_sub_cancel,
      heatHessianCoordConvolutionND] using hc.symm
  have hsum : IntervalIntegrable
      (∑ k : Fin n, fun u => heatHessianCoordConvolutionND u w k x)
      volume 0 T := IntervalIntegrable.sum Finset.univ (fun k _ => hk k)
  convert hsum using 1
  ext u
  rw [heatSemigroupLaplacianND, Finset.sum_apply]

/-- The extended heat-flow path is continuous on a compact interval starting
at zero when the datum has a positive Hölder modulus. -/
theorem continuousOn_heatFlowPathBcf_apply_Icc_of_coordHolder
    {n : ℕ} {T r : ℝ} (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    ContinuousOn (fun u => heatFlowPathBcf w u x) (Set.Icc 0 T) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · exact (continuous_eval_const x).continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_heatFlowPathBcf_zero_of_coordHolder
        hr0 w hH hholder).mono (Set.Icc_subset_Ici_self))
  · exact (continuous_eval_const x).continuousAt.comp_continuousWithinAt
      ((continuousAt_heatFlowPathBcf w hu0).continuousWithinAt)

/-- **Generator integral identity at heat time zero.**  For bounded globally
coordinatewise Hölder data, the increment of the heat semigroup is the time
integral of its actual spatial Laplacian.  The proof is an improper-endpoint
FTC: continuity at zero comes from the fractional approximate identity, while
the Hölder Hessian estimate supplies the integrable derivative. -/
theorem heatSemigroupND_sub_self_eq_integral_laplacian
    {n : ℕ} {T r : ℝ} (hT : 0 < T) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    heatSemigroupND T (⇑w) x - w x =
      ∫ u in (0 : ℝ)..T, heatSemigroupLaplacianND u w x := by
  let F : ℝ → ℝ := fun u => heatFlowPathBcf w u x
  have hcont : ContinuousOn F (Set.Icc 0 T) := by
    simpa only [F] using
      continuousOn_heatFlowPathBcf_apply_Icc_of_coordHolder
        (T := T) hr0 w hH hholder x
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt F (heatSemigroupLaplacianND u w x) (Set.Ioi u) u := by
    intro u hu
    have hd := hasDerivAt_heatSemigroupND_time_eq_laplacian hu.1 w x
    apply (hd.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Ioi_mem_nhds hu.1] with v hv
    have hvpos : 0 < v := hv
    rw [show F v = heatFlowPathBcf w v x by rfl,
      heatFlowPathBcf_of_pos w hvpos, heatSemigroupNDbcf_apply]
  have hint := intervalIntegrable_heatSemigroupLaplacianND
    hT.le hr0 w hH hholder x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hT.le hcont hderiv hint
  simpa [F, heatFlowPathBcf, hT, heatSemigroupNDbcf_apply] using hFTC.symm

/-! ## Positive-time continuity of the Duhamel Laplacian -/

/-- Reflection of the Duhamel Hessian time integral to heat time
`u = t - s`. -/
theorem heatDuhamelHessianCoordND_eq_comp_sub
    {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianCoordND t₀ t q k x =
      ∫ u in (0 : ℝ)..(t - t₀),
        heatHessianCoordConvolutionND u (q (t - u)) k x := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := t₀) (b := t)
    (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) t
  simpa only [heatDuhamelHessianCoordND, sub_sub_cancel, sub_self] using h

/-- Measurability in reflected heat time of a coordinate Hessian applied to a
continuous BCF-valued source. -/
theorem aestronglyMeasurable_heatHessianCoordConvolutionND_comp_sub
    {n : ℕ} (t : ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (k : Fin n) (x : Fin n → ℝ) :
    AEStronglyMeasurable
      (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) volume := by
  have hK : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatKernelND p.1 (x - p.2)) := by
    exact measurable_uncurry_heatKernelND.comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  have hc : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (x - p.2) k ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)) := by
    fun_prop
  have hQ : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (q (t - p.1)) p.2) := by
    exact (ContinuousEval.continuous_eval.comp
      ((hq.comp (continuous_const.sub continuous_fst)).prodMk continuous_snd)).measurable
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (heatKernelND p.1 (x - p.2) *
        ((x - p.2) k ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1))) *
          (q (t - p.1)) p.2) := (hK.mul hc).mul hQ
  simpa only [heatHessianCoordConvolutionND] using
    (hG.aestronglyMeasurable
      (μ := (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- A coordinate of the Duhamel Hessian is continuous in the final time at
every time strictly after the initial slice.  Reflection puts the singularity
at the fixed endpoint `u = 0`, where the integrable Hölder majorant
`u ^ (-1 + r / 2)` permits dominated convergence. -/
theorem continuousAt_heatDuhamelHessianCoordND_time
    {n : ℕ} {t₀ t₁ r : ℝ} (ht : t₀ < t₁) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    ContinuousAt (fun t => heatDuhamelHessianCoordND t₀ t q k x) t₁ := by
  let A : ℝ := H * heatHessianHolderMoment n r k
  let p : ℝ := -1 + r / 2
  have hA : 0 ≤ A := mul_nonneg hH (heatHessianHolderMoment_nonneg n r k)
  have hp : (-1 : ℝ) < p := by simp only [p]; linarith
  have hfun : (fun t => heatDuhamelHessianCoordND t₀ t q k x) =
      fun t => ∫ u in (0 : ℝ)..(t - t₀),
        heatHessianCoordConvolutionND u (q (t - u)) k x := by
    funext t
    exact heatDuhamelHessianCoordND_eq_comp_sub t₀ t q k x
  rw [hfun]
  have hEq : (fun t => ∫ u in (0 : ℝ)..(t - t₀),
      heatHessianCoordConvolutionND u (q (t - u)) k x) =ᶠ[nhds t₁]
      fun t => ∫ u, Set.indicator (Set.Ioc (0 : ℝ) (t - t₀))
        (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) u := by
    filter_upwards [Ioi_mem_nhds ht] with t htmem
    have hle : (0 : ℝ) ≤ t - t₀ := by linarith [Set.mem_Ioi.1 htmem]
    rw [intervalIntegral.integral_of_le hle,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine ContinuousAt.congr ?_ hEq.symm
  refine continuousAt_of_dominated
    (bound := fun u => Set.indicator
      (Set.Ioc (0 : ℝ) (t₁ - t₀ + 1)) (fun u => A * u ^ p) u) ?_ ?_ ?_ ?_
  · filter_upwards with t
    exact (aestronglyMeasurable_heatHessianCoordConvolutionND_comp_sub
      t hq k x).indicator measurableSet_Ioc
  · filter_upwards [Iio_mem_nhds (show t₁ < t₁ + 1 by linarith)] with t htmem
    filter_upwards with u
    by_cases hmem : u ∈ Set.Ioc (0 : ℝ) (t - t₀)
    · rw [Set.indicator_of_mem hmem]
      have hupos : (0 : ℝ) < u := hmem.1
      have htlt : t < t₁ + 1 := Set.mem_Iio.1 htmem
      rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hupos, by linarith [hmem.2]⟩),
        Real.norm_eq_abs]
      have hb := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
        hupos hr0.le hH x k (q (t - u)).continuous.aestronglyMeasurable
        (hqb (t - u)) (hqholder (t - u) x)
      calc
        |heatHessianCoordConvolutionND u (q (t - u)) k x| ≤
            H * u ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
          simpa only [heatHessianCoordConvolutionND] using hb
        _ = A * u ^ p := by simp only [A, p]; ring
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact Set.indicator_nonneg
        (fun u hu => mul_nonneg hA (Real.rpow_nonneg hu.1.le p)) u
  · have hB : (0 : ℝ) ≤ t₁ - t₀ + 1 := by linarith
    have hpow : IntervalIntegrable (fun u : ℝ => u ^ p) volume 0 (t₁ - t₀ + 1) :=
      intervalIntegral.intervalIntegrable_rpow' hp
    have hpowOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp hpow
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hpowOn.const_mul A)
  · have h0 : ∀ᵐ (u : ℝ), u ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ a ≠ 0} = {0} := by ext a; simp
      rw [hset]
      exact MeasureTheory.measure_singleton 0
    have hd : ∀ᵐ (u : ℝ), u ≠ t₁ - t₀ := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ a ≠ t₁ - t₀} = {t₁ - t₀} := by ext a; simp
      rw [hset]
      exact MeasureTheory.measure_singleton _
    filter_upwards [h0, hd] with u hu0 hud
    rcases lt_or_gt_of_ne hu0 with hult | hupos
    · have hzero : (fun t => Set.indicator (Set.Ioc (0 : ℝ) (t - t₀))
          (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) u) =
          fun _ => (0 : ℝ) := by
        funext t
        rw [Set.indicator_of_notMem
          (fun hm => absurd hm.1 (not_lt.2 hult.le))]
      rw [hzero]
      exact continuousAt_const
    · rcases lt_or_gt_of_ne hud with hulim | hulim
      · refine (continuous_heatHessianCoordConvolutionND_comp_sub_time
          hupos k hq x).continuousAt.congr ?_
        filter_upwards [Ioi_mem_nhds (show u + t₀ < t₁ by linarith)] with t htmem
        rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hupos, by linarith [Set.mem_Ioi.1 htmem]⟩)]
      · have hz : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t₁ := continuousAt_const
        refine hz.congr ?_
        filter_upwards [Iio_mem_nhds (show t₁ < u + t₀ by linarith)] with t htmem
        rw [Set.indicator_of_notMem
          (fun hm => absurd hm.2 (not_le.2 (by linarith [Set.mem_Iio.1 htmem])))]

/-- The full Duhamel Laplacian is continuous in positive final time. -/
theorem continuousAt_heatDuhamelLaplacianND_time
    {n : ℕ} {t₀ t₁ r : ℝ} (ht : t₀ < t₁) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    ContinuousAt (fun t => heatDuhamelLaplacianND t₀ t q x) t₁ := by
  classical
  rw [show (fun t => heatDuhamelLaplacianND t₀ t q x) =
      fun t => ∑ k : Fin n, heatDuhamelHessianCoordND t₀ t q k x by rfl]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t₁)
  | @insert k s hks ih =>
      have hadd := (continuousAt_heatDuhamelHessianCoordND_time
        ht hr0 hq hH hqb hqholder k x).add ih
      simp only [Finset.sum_insert hks]
      change ContinuousAt
        ((fun t => heatDuhamelHessianCoordND t₀ t q k x) +
          fun t => ∑ i ∈ s, heatDuhamelHessianCoordND t₀ t q i x) t₁
      exact hadd

end AnalyticPDE
end RicciFlow
