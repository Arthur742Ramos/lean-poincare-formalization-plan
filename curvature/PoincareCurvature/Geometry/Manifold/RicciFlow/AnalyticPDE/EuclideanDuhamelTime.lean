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

end AnalyticPDE
end RicciFlow
