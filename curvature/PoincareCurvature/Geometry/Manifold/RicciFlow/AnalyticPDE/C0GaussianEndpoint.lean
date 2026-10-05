import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatFrechet
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Ordinary endpoint jets from genuine C0 Gaussian smoothing

SOURCE CANDIDATE, UNCOMPILED. No backward heat equation is asserted. The
Gaussian time is sqrt(abs h), and multiplication by the signed h restores
the prescribed ordinary two-sided derivative at zero. Each nonzero slice
is C2; the datum itself needs only boundedness and uniform continuity.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology ContDiff

namespace RicciFlow.AnalyticPDE.C0Endpoint

def smoothingTime (h : ℝ) : ℝ := Real.sqrt |h|

lemma smoothingTime_zero : smoothingTime 0 = 0 := by simp [smoothingTime]

lemma smoothingTime_pos {h : ℝ} (hh : h ≠ 0) : 0 < smoothingTime h :=
  Real.sqrt_pos.2 (abs_pos.2 hh)

lemma continuous_smoothingTime : Continuous smoothingTime :=
  Real.continuous_sqrt.comp continuous_abs

def gaussianPath {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (h : ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  heatFlowPathBcf f (smoothingTime h)

@[simp] lemma gaussianPath_zero {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) : gaussianPath f 0 = f := by
  simp [gaussianPath, smoothingTime, heatFlowPathBcf]

lemma gaussianPath_of_ne_zero {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) {h : ℝ} (hh : h ≠ 0) :
    gaussianPath f h = heatSemigroupNDbcf (smoothingTime_pos hh) f :=
  heatFlowPathBcf_of_pos f (smoothingTime_pos hh)

lemma continuousAt_gaussianPath_zero {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    ContinuousAt (gaussianPath f) 0 := by
  have h := continuousAt_heatFlowPathBcf_zero_of_uniformContinuous f hf
  have ht : ContinuousAt smoothingTime 0 := continuous_smoothingTime.continuousAt
  have houter : ContinuousAt (heatFlowPathBcf f) (smoothingTime 0) := by
    simpa only [smoothingTime_zero] using h
  simpa only [gaussianPath] using houter.comp ht

lemma norm_gaussianPath_le {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (h : ℝ) :
    ‖gaussianPath f h‖ ≤ ‖f‖ := by
  by_cases hh : h = 0
  · simp [hh]
  · rw [gaussianPath_of_ne_zero f hh]
    exact norm_heatSemigroupNDbcf_le (smoothingTime_pos hh) f

lemma abs_gaussianPath_apply_le {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (h : ℝ) (z : Fin n → ℝ) :
    |gaussianPath f h z| ≤ ‖f‖ := by
  exact (by simpa only [Real.norm_eq_abs] using
    (gaussianPath f h).norm_coe_le_norm z).trans (norm_gaussianPath_le f h)

lemma contDiff_two_gaussianPath {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ 2 (gaussianPath f h : (Fin n → ℝ) → ℝ) := by
  rw [gaussianPath_of_ne_zero f hh]
  simpa only [heatSemigroupNDbcf_apply] using
    contDiff_two_heatSemigroupND (smoothingTime_pos hh) f

/-- A mere continuous coefficient multiplied by its signed time variable
has the expected ordinary derivative. No derivative of the coefficient is
used, and no right/within derivative is substituted. -/
lemma hasDerivAt_time_mul_of_continuousAt {a : ℝ → ℝ}
    (ha : ContinuousAt a 0) :
    HasDerivAt (fun h : ℝ => h * a h) (a 0) 0 := by
  apply hasDerivAt_iff_tendsto.mpr
  have hlim : Tendsto (fun h : ℝ => ‖a h - a 0‖) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (ha.sub continuousAt_const).norm.tendsto
  apply squeeze_zero (fun h => mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (norm_nonneg _))
    (fun h => ?_) hlim
  by_cases hh : h = 0
  · simp [hh]
  · have heq : h * a h - 0 * a 0 - (h - 0) • a 0 = h * (a h - a 0) := by
      simp only [smul_eq_mul]
      ring
    rw [heq, sub_zero, norm_mul]
    simp only [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul]

lemma hasDerivAt_time_mul_gaussianPath {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) (z : Fin n → ℝ) :
    HasDerivAt (fun h : ℝ => h * gaussianPath f h z) (f z) 0 := by
  have ha : ContinuousAt (fun h => gaussianPath f h z) 0 :=
    (BoundedContinuousFunction.lipschitz_eval_const z).continuous.continuousAt.comp
      (continuousAt_gaussianPath_zero f hf)
  simpa only [gaussianPath_zero] using hasDerivAt_time_mul_of_continuousAt ha

end RicciFlow.AnalyticPDE.C0Endpoint
