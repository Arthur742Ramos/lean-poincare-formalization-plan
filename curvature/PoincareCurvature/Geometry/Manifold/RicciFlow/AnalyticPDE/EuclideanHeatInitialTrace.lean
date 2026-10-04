import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelTime
import PoincareCurvature.Analysis.FiniteMomentApproximation
import PoincareCurvature.Analysis.CompactUniformModulus
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Initial traces for the heat evolution of genuine bounded C² data

The approximation estimate below uses an arbitrary continuity modulus, not a
positive-exponent Hölder modulus. On noncompact Euclidean space continuity
alone gives a local uniform trace; a global sup-norm trace additionally needs
uniform continuity of the Hessian entries. No backward heat evolution or
manifold localization is constructed here.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- An arbitrary local modulus gives a Gaussian approximate-identity bound,
using the actual normalized Gaussian and its coordinate first moments. -/
theorem abs_heatSemigroupND_sub_self_le_of_local_modulus
    {n : ℕ} {t δ ε : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ)
    (hmod : ∀ y, ‖y - x‖ < δ → |f y - f x| ≤ ε) :
    |heatSemigroupND t f x - f x| ≤
      ε + (2 * ‖f‖ / δ) * (n : ℝ) * (2 / Real.sqrt π * Real.sqrt t) := by
  classical
  rw [heatSemigroupND_eq_integral_kernel_mul_sub]
  have h := PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus
    hδ hε (heatKernelND t) (integrable_heatKernelND ht)
    (heatKernelND_nonneg ht) (integral_heatKernelND ht)
    (fun k => by simpa only [mul_comm] using integrable_abs_coord_mul_heatKernelND ht k)
    f x hmod
  have hm : ∀ k : Fin n,
      (∫ z : Fin n → ℝ, heatKernelND t z * |z k|) =
        2 / Real.sqrt π * Real.sqrt t := by
    intro k
    rw [show (fun z : Fin n → ℝ => heatKernelND t z * |z k|) =
      (fun z => |z k| * heatKernelND t z) by ext z; ring,
      integral_abs_coord_mul_heatKernelND_eq ht k,
      heatSemigroupND_timeModulus_eq_sqrt ht.le]
  simpa only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc] using h

/-- Global norm form of the arbitrary-modulus approximate identity. -/
theorem norm_heatSemigroupNDbcf_sub_self_le_of_modulus
    {n : ℕ} {t δ ε : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hmod : ∀ x y, ‖y - x‖ < δ → |f y - f x| ≤ ε) :
    ‖heatSemigroupNDbcf ht f - f‖ ≤
      ε + (2 * ‖f‖ / δ) * (n : ℝ) * (2 / Real.sqrt π * Real.sqrt t) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
  rw [BoundedContinuousFunction.sub_apply, heatSemigroupNDbcf_apply, Real.norm_eq_abs]
  exact abs_heatSemigroupND_sub_self_le_of_local_modulus ht hδ hε f x (hmod x)

/-- The zero-time heat path is strongly continuous for uniformly continuous
bounded data. The constant negative-time extension is used for continuity
only; this theorem makes no ordinary initial-derivative claim. -/
theorem continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    ContinuousAt (heatFlowPathBcf f) 0 := by
  have hzero : heatFlowPathBcf f 0 = f := dif_neg (lt_irrefl 0)
  show Tendsto (heatFlowPathBcf f) (𝓝 0) (𝓝 (heatFlowPathBcf f 0))
  rw [hzero]
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  let M : ℝ := (2 * ‖f‖ / δ) * (n : ℝ) * (2 / Real.sqrt π)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, M * Real.sqrt t < ε / 2 := by
    have hlim : Tendsto (fun t : ℝ => M * Real.sqrt t) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => M * Real.sqrt t) :=
        continuous_const.mul Real.continuous_sqrt
      simpa only [Real.sqrt_zero, mul_zero] using hcont.tendsto (0 : ℝ)
    exact hlim.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hsmall] with t ht
  by_cases htpos : 0 < t
  · rw [heatFlowPathBcf_of_pos f htpos, dist_eq_norm]
    have hb := norm_heatSemigroupNDbcf_sub_self_le_of_modulus
      htpos hδ (le_of_lt (half_pos hε)) f (fun x y hxy => by
        have hh := hmod (show dist y x < δ by simpa only [dist_eq_norm] using hxy)
        exact le_of_lt (by simpa only [Real.dist_eq] using hh))
    have hm : (2 * ‖f‖ / δ) * (n : ℝ) *
        (2 / Real.sqrt π * Real.sqrt t) = M * Real.sqrt t := by dsimp [M]; ring
    rw [hm] at hb
    linarith
  · rw [heatFlowPathBcf, dif_neg htpos, dist_self]
    exact hε

/-- Bounded continuous initial data have a locally uniform Gaussian trace on
every compact spatial set, without global uniform continuity. -/
theorem tendstoUniformlyOn_heatSemigroupND_zero
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => heatSemigroupND t f x) f (𝓝[>] 0) K := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous
      hK f (half_pos hε)
  let M : ℝ := (2 * ‖f‖ / δ) * (n : ℝ) * (2 / Real.sqrt π)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, M * Real.sqrt t < ε / 2 := by
    have hlim : Tendsto (fun t : ℝ => M * Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => M * Real.sqrt t) :=
        continuous_const.mul Real.continuous_sqrt
      have hlim0 : Tendsto (fun t : ℝ => M * Real.sqrt t) (𝓝 0) (𝓝 0) := by
        simpa only [Real.sqrt_zero, mul_zero] using hcont.tendsto (0 : ℝ)
      exact hlim0.mono_left nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht htpos
  intro x hx
  have hb := abs_heatSemigroupND_sub_self_le_of_local_modulus
    htpos hδ (le_of_lt (half_pos hε)) f x (fun y hxy =>
      hmod x hx y (by simpa only [norm_sub_rev] using hxy))
  have hm : (2 * ‖f‖ / δ) * (n : ℝ) *
      (2 / Real.sqrt π * Real.sqrt t) = M * Real.sqrt t := by dsimp [M]; ring
  rw [hm] at hb
  rw [Real.dist_eq, abs_sub_comm]
  linarith

namespace EuclideanBoundedC2Data

/-- Any bounded scalar field with continuous bounded actual coordinate
first derivatives is globally Lipschitz. -/
theorem abs_sub_le_of_bounded_coordinate_derivatives
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (g : Fin n → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hg : ∀ k x, HasDerivAt (fun a => f (Function.update x k a)) (g k x) (x k))
    (x y : Fin n → ℝ) :
    |f x - f y| ≤ (∑ k : Fin n, ‖g k‖) * ‖x - y‖ := by
  classical
  let G : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun z => coordinateLinearFunctional (fun k => g k z)
  have hGcont : Continuous G := by
    dsimp [G]
    unfold coordinateLinearFunctional
    apply continuous_finsetSum
    intro k _
    exact (g k).continuous.smul continuous_const
  have hderiv : ∀ z, HasFDerivAt f (G z) z :=
    hasFDerivAt_of_continuous_coordinate_derivatives f G hGcont (fun z k => by
      dsimp [G]
      rw [coordinateLinearFunctional_single]
      exact (hg k z).hasFDerivAt)
  have hGnorm : ∀ z, ‖G z‖ ≤ ∑ k : Fin n, ‖g k‖ := by
    intro z
    refine (norm_coordinateLinearFunctional_le _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    simpa only [Real.norm_eq_abs] using (g k).norm_coe_le_norm z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := (Set.univ : Set (Fin n → ℝ)))
    (f := fun z => f z) (C := ∑ k : Fin n, ‖g k‖) (x := y) (y := x)
    (fun z _ => (hderiv z).differentiableAt)
    (fun z _ => by rw [(hderiv z).fderiv]; exact hGnorm z)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using h

/-- The value's uniform continuity is derived from its bounded actual first
derivatives, rather than added as an initial-data premise. -/
theorem uniformContinuous_value {n : ℕ} (D : EuclideanBoundedC2Data n) :
    UniformContinuous (D.value : (Fin n → ℝ) → ℝ) := by
  have hlip : LipschitzWith ⟨∑ k : Fin n, ‖D.first k‖,
      Finset.sum_nonneg fun _ _ => norm_nonneg _⟩ D.value := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using
      abs_sub_le_of_bounded_coordinate_derivatives D.value D.first D.hasDeriv_value x y
  exact hlip.uniformContinuous

/-- Each actual first derivative is uniformly continuous because its
successive coordinate derivatives are the bounded actual Hessian entries. -/
theorem uniformContinuous_first {n : ℕ} (D : EuclideanBoundedC2Data n)
    (k : Fin n) : UniformContinuous (D.first k : (Fin n → ℝ) → ℝ) := by
  have hlip : LipschitzWith ⟨∑ j : Fin n, ‖D.second j k‖,
      Finset.sum_nonneg fun _ _ => norm_nonneg _⟩ (D.first k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using
      abs_sub_le_of_bounded_coordinate_derivatives (D.first k)
        (fun j => D.second j k) (fun j x => D.hasDeriv_first j k x) x y
  exact hlip.uniformContinuous

/-- Locally uniform trace of the actual homogeneous heat gradient. -/
theorem tendstoUniformlyOn_heatGradient_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) (k : Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => heatSemigroupGradientCoordND t D.value k x)
      (D.first k) (𝓝[>] 0) K := by
  apply (tendstoUniformlyOn_heatSemigroupND_zero (D.first k) hK).congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _
  exact (D.heatSemigroupGradientCoordND_eq ht k x).symm

/-- Locally uniform trace of every actual mixed homogeneous heat Hessian
entry for arbitrary bounded C² data, with no Hessian Hölder premise. -/
theorem tendstoUniformlyOn_heatHessian_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) (j k : Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => heatHessianEntryConvolutionND t D.value j k x)
      (D.second j k) (𝓝[>] 0) K := by
  apply (tendstoUniformlyOn_heatSemigroupND_zero (D.second j k) hK).congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _
  exact (D.heatHessianEntryConvolutionND_eq ht j k x).symm

/-- Global sup-norm C² trace, expressed in the product of bounded-continuous
component spaces. Uniform continuity is assumed only for initial Hessian
entries; it is proved above for the value and the first derivatives. -/
theorem continuousAt_heatC2Trace_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)) :
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf D.value t,
        (fun k => heatFlowPathBcf (D.first k) t),
        (fun j k => heatFlowPathBcf (D.second j k) t))) 0 := by
  have hv := continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
    D.value D.uniformContinuous_value
  have hfirst := continuousAt_pi.2 (fun k =>
    continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
      (D.first k) (D.uniformContinuous_first k))
  have hsecond' := continuousAt_pi.2 (fun j => continuousAt_pi.2 (fun k =>
    continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
      (D.second j k) (hsecond j k)))
  exact hv.prodMk (hfirst.prodMk hsecond')

/-- The initial generator is the finite trace of the actual initial Hessian.
This is a right derivative of the closed heat path, requiring only the
bounded C² witnesses. It does not assert an ordinary derivative for the
constant negative-time continuation. -/
theorem hasDerivWithinAt_heatFlowPathBcf_apply_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t => heatFlowPathBcf D.value t x)
      (∑ k : Fin n, D.second k k x) (Ici 0) 0 := by
  let F : ℝ → ℝ := fun t => heatFlowPathBcf D.value t x
  have hderiv : ∀ t, 0 < t →
      HasDerivAt F (heatSemigroupLaplacianND t D.value x) t := by
    intro t ht
    apply (hasDerivAt_heatSemigroupND_time_eq_laplacian ht D.value x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [F, heatFlowPathBcf_of_pos D.value hs]
    exact heatSemigroupNDbcf_apply hs D.value x
  have hcont : ContinuousWithinAt F (Ioi 0) 0 :=
    ((continuous_eval_const x).continuousAt.comp
      (continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
        D.value D.uniformContinuous_value)).continuousWithinAt
  have hentry : ∀ k : Fin n, Tendsto
      (fun t => heatHessianEntryConvolutionND t D.value k k x)
      (𝓝[>] 0) (𝓝 (D.second k k x)) := by
    intro k
    exact (D.tendstoUniformlyOn_heatHessian_zero k k (K := {x}) isCompact_singleton).tendsto_at
      (mem_singleton x)
  have hlim : Tendsto (fun t => heatSemigroupLaplacianND t D.value x)
      (𝓝[>] 0) (𝓝 (∑ k : Fin n, D.second k k x)) := by
    have hsum := tendsto_finset_sum Finset.univ (fun k _ => hentry k)
    simpa only [heatSemigroupLaplacianND, heatHessianCoordConvolutionND,
      heatHessianEntryConvolutionND, heatHessianKernelEntryND_diag] using hsum
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    hcont self_mem_nhdsWithin
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hderiv t ht).deriv.symm

end EuclideanBoundedC2Data

end AnalyticPDE
end RicciFlow
