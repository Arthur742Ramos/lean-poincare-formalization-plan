import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Actual Gaussian Laplace resolvent and its strong right-generator range witness.
This is a Source candidate: native elaboration is UNRUN. The semigroup law,
integrability, tail identity and derivative are proved from the actual heat
path. Uniform continuity of the input is the sole analytic regularity premise.
No abstract generator identity or differentiability witness is supplied.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology

namespace RicciFlow.AnalyticPDE

/-- The actual exponentially weighted Gaussian heat path, with the closed
zero-time value and the existing constant negative-time continuation. -/
def actualHeatResolventIntegrand {n : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (t : ℝ) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  Real.exp (-lam * t) • heatFlowPathBcf f t

/-- A Bochner integral of the actual heat path over nonnegative time. -/
def actualGaussianHeatResolvent {n : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∫ t in Ici (0 : ℝ), actualHeatResolventIntegrand lam f t

private theorem actualGaussianHeatResolvent_eq_Ioi {n : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    actualGaussianHeatResolvent lam f =
      ∫ t in Ioi (0 : ℝ), actualHeatResolventIntegrand lam f t := by
  exact integral_Ici_eq_integral_Ioi

private theorem norm_closedHeatPath_le {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (t : ℝ) :
    ‖heatFlowPathBcf f t‖ ≤ ‖f‖ := by
  by_cases ht : 0 < t
  · rw [heatFlowPathBcf_of_pos f ht]
    exact norm_heatSemigroupNDbcf_le ht f
  · simp only [heatFlowPathBcf, dif_neg ht]
    exact le_rfl

private theorem continuous_closedHeatPath {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    Continuous (heatFlowPathBcf f) := by
  apply continuous_iff_continuousAt.2
  intro t
  by_cases ht : 0 < t
  · exact continuousAt_heatFlowPathBcf f ht
  by_cases ht0 : t = 0
  · subst t
    exact continuousAt_heatFlowPathBcf_zero_of_uniformContinuous f hf
  have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp ht) ht0
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ => f) t).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hneg] with s hs
  exact dif_neg (not_lt.mpr hs.le)

private theorem continuous_actualHeatResolventIntegrand {n : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    Continuous (actualHeatResolventIntegrand lam f) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (continuous_closedHeatPath f hf)

private theorem norm_actualHeatResolventIntegrand_le {n : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (t : ℝ) :
    ‖actualHeatResolventIntegrand lam f t‖ ≤ Real.exp (-lam * t) * ‖f‖ := by
  rw [actualHeatResolventIntegrand, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_closedHeatPath_le f t) (Real.exp_pos _).le

/-- The Laplace-weighted actual BCF heat path is Bochner integrable. -/
theorem integrableOn_actualHeatResolventIntegrand {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    IntegrableOn (actualHeatResolventIntegrand lam f) (Ici (0 : ℝ)) := by
  apply Iff.mpr (integrableOn_Ici_iff_integrableOn_Ioi
    (f := actualHeatResolventIntegrand lam f) (b := (0 : ℝ))
    (μ := volume) (by finiteness))
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-lam * t) * ‖f‖) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hlam) 0).mul_const ‖f‖
  exact hdom.mono' (continuous_actualHeatResolventIntegrand lam f hf).aestronglyMeasurable
    (Eventually.of_forall (norm_actualHeatResolventIntegrand_le lam f))

/-- The actual Gaussian resolvent has the sharp contraction bound. -/
theorem norm_actualGaussianHeatResolvent_le {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ‖actualGaussianHeatResolvent lam f‖ ≤ ‖f‖ / lam := by
  rw [actualGaussianHeatResolvent_eq_Ioi]
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-lam * t) * ‖f‖) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hlam) 0).mul_const ‖f‖
  calc
    ‖∫ t in Ioi (0 : ℝ), actualHeatResolventIntegrand lam f t‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * ‖f‖ :=
      norm_integral_le_of_norm_le hdom
        (Eventually.of_forall (norm_actualHeatResolventIntegrand_le lam f))
    _ = ‖f‖ / lam := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr hlam)]
      simp only [mul_zero, Real.exp_zero]
      ring

private theorem closedHeatPath_comp {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    heatFlowPathBcf (heatFlowPathBcf f t) h = heatFlowPathBcf f (h + t) := by
  by_cases hh0 : h = 0
  · subst h
    simp [heatFlowPathBcf]
  by_cases ht0 : t = 0
  · subst t
    simp [heatFlowPathBcf]
  have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  rw [heatFlowPathBcf_of_pos f htp, heatFlowPathBcf_of_pos _ hhp,
    heatFlowPathBcf_of_pos f (add_pos hhp htp)]
  exact heatSemigroupNDbcf_comp h t hhp htp f

private theorem integral_Ioi_comp_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (h : ℝ) :
    (∫ t in Ioi (0 : ℝ), F (t + h)) = ∫ t in Ioi h, F t := by
  have A : MeasurableEmbedding (fun t : ℝ => t + h) :=
    (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
  have hpre : (fun t : ℝ => t + h) ⁻¹' Ioi h = Ioi (0 : ℝ) := by
    ext t
    change (h < t + h) ↔ 0 < t
    constructor <;> intro ht <;> linarith
  calc
    (∫ t in Ioi (0 : ℝ), F (t + h)) =
        ∫ t in Ioi h, F t ∂Measure.map (fun t : ℝ => t + h) volume := by
      simpa only [hpre] using (A.setIntegral_map F (Ioi h)).symm
    _ = ∫ t in Ioi h, F t := by rw [map_add_right_eq_self]

/-- Actual semigroup action on the resolvent, obtained by CLM-integral
interchange and translation of the Bochner tail. -/
theorem heatFlowPathBcf_actualGaussianHeatResolvent_shift {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) {h : ℝ} (hh : 0 ≤ h) :
    heatFlowPathBcf (actualGaussianHeatResolvent lam f) h =
      Real.exp (lam * h) • (actualGaussianHeatResolvent lam f -
        ∫ t in (0 : ℝ)..h, actualHeatResolventIntegrand lam f t) := by
  by_cases hh0 : h = 0
  · subst h
    simp [heatFlowPathBcf]
  have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have hint : IntegrableOn (actualHeatResolventIntegrand lam f) (Ioi (0 : ℝ)) :=
    Iff.mp (integrableOn_Ici_iff_integrableOn_Ioi
      (f := actualHeatResolventIntegrand lam f) (b := (0 : ℝ))
      (μ := volume) (by finiteness))
      (integrableOn_actualHeatResolventIntegrand hlam f hf)
  have hsplit : actualGaussianHeatResolvent lam f -
      (∫ t in Ioi h, actualHeatResolventIntegrand lam f t) =
      ∫ t in (0 : ℝ)..h, actualHeatResolventIntegrand lam f t := by
    rw [actualGaussianHeatResolvent_eq_Ioi]
    exact intervalIntegral.integral_Ioi_sub_Ioi hint hh
  have htail : (∫ t in Ioi h, actualHeatResolventIntegrand lam f t) =
      actualGaussianHeatResolvent lam f -
        ∫ t in (0 : ℝ)..h, actualHeatResolventIntegrand lam f t := by
    apply (eq_sub_iff_add_eq).2
    simpa only [add_comm] using ((sub_eq_iff_eq_add).1 hsplit).symm
  let L := heatSemigroupNDclm (n := n) hhp
  calc
    heatFlowPathBcf (actualGaussianHeatResolvent lam f) h =
        L (∫ t in Ioi (0 : ℝ), actualHeatResolventIntegrand lam f t) := by
      rw [heatFlowPathBcf_of_pos _ hhp, actualGaussianHeatResolvent_eq_Ioi]
      rfl
    _ = ∫ t in Ioi (0 : ℝ), L (actualHeatResolventIntegrand lam f t) :=
      (L.integral_comp_comm hint).symm
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (lam * h) •
        actualHeatResolventIntegrand lam f (t + h) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change L (Real.exp (-lam * t) • heatFlowPathBcf f t) = _
      rw [map_smul]
      have hL : L (heatFlowPathBcf f t) =
          heatFlowPathBcf (heatFlowPathBcf f t) h := by
        rw [heatFlowPathBcf_of_pos _ hhp]
        rfl
      rw [hL, closedHeatPath_comp f hh ht.le, add_comm h t]
      unfold actualHeatResolventIntegrand
      change Real.exp (-lam * t) • heatFlowPathBcf f (t + h) =
        Real.exp (lam * h) • (Real.exp (-lam * (t + h)) •
          heatFlowPathBcf f (t + h))
      rw [smul_smul]
      have hscalar : Real.exp (lam * h) * Real.exp (-lam * (t + h)) =
          Real.exp (-lam * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hscalar]
    _ = Real.exp (lam * h) •
        (∫ t in Ioi (0 : ℝ), actualHeatResolventIntegrand lam f (t + h)) :=
      integral_smul _ _
    _ = Real.exp (lam * h) •
        (∫ t in Ioi h, actualHeatResolventIntegrand lam f t) := by
      rw [integral_Ioi_comp_add]
    _ = _ := by rw [htail]

/-- A true BCF-norm right derivative of the actual heat path of the
resolvent, with its resolvent range value derived rather than assumed. -/
theorem hasDerivWithinAt_actualGaussianHeatResolvent_zero {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    HasDerivWithinAt (heatFlowPathBcf (actualGaussianHeatResolvent lam f))
      (lam • actualGaussianHeatResolvent lam f - f) (Ici 0) 0 := by
  let G := actualHeatResolventIntegrand lam f
  have hG : Continuous G := continuous_actualHeatResolventIntegrand lam f hf
  have hG0 : G 0 = f := by simp [G, actualHeatResolventIntegrand, heatFlowPathBcf]
  have hI : HasDerivAt (fun h : ℝ => ∫ t in (0 : ℝ)..h, G t) f 0 :=
    (intervalIntegral.integral_hasDerivAt_right
      (hG.intervalIntegrable 0 0) hG.stronglyMeasurable.stronglyMeasurableAtFilter
      hG.continuousAt).congr_deriv hG0
  have hE : HasDerivAt (fun h : ℝ => Real.exp (lam * h)) lam 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul lam).exp
  have hV : HasDerivAt (fun h : ℝ => actualGaussianHeatResolvent lam f -
      ∫ t in (0 : ℝ)..h, G t) (-f) 0 := by
    convert! (hasDerivAt_const (0 : ℝ)
      (actualGaussianHeatResolvent lam f)).sub hI using 1 <;>
      simp only [zero_sub]
  have hP : HasDerivAt (fun h : ℝ => Real.exp (lam * h) •
      (actualGaussianHeatResolvent lam f - ∫ t in (0 : ℝ)..h, G t))
      (lam • actualGaussianHeatResolvent lam f - f) 0 := by
    convert! hE.smul hV using 1 <;>
      simp only [intervalIntegral.integral_same, mul_zero, Real.exp_zero,
        one_smul, sub_eq_add_neg, neg_zero, add_zero, add_comm]
  apply hP.hasDerivWithinAt.congr
  · intro h hh
    exact heatFlowPathBcf_actualGaussianHeatResolvent_shift hlam f hf hh
  · exact heatFlowPathBcf_actualGaussianHeatResolvent_shift hlam f hf (le_refl 0)

private theorem uniformContinuous_of_closedHeatPath_right_continuous {n : ℕ}
    (u : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hu : ContinuousWithinAt (heatFlowPathBcf u) (Ici 0) 0) :
    UniformContinuous (u : (Fin n → ℝ) → ℝ) := by
  apply Metric.uniformContinuous_iff.2
  intro ε hε
  obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.mp hu (ε / 3) (by positivity)
  let h := r / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hn : ‖heatFlowPathBcf u h - u‖ < ε / 3 := by
    have H := hnear (show h ∈ Ici (0 : ℝ) from hh.le)
      (show dist h 0 < r by rw [Real.dist_eq, sub_zero, abs_of_pos hh]; dsimp [h]; linarith)
    simpa only [dist_eq_norm, heatFlowPathBcf, dif_neg (lt_irrefl (0 : ℝ))] using H
  let v := heatFlowPathBcf u h
  let K : ℝ := (n : ℝ) * (‖u‖ / Real.sqrt (Real.pi * h))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlip : LipschitzWith ⟨K, hK⟩ (v : (Fin n → ℝ) → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    change |v x - v y| ≤ K * ‖x - y‖
    simpa only [v, K, heatFlowPathBcf_of_pos u hh, heatSemigroupNDbcf_apply] using
      heatSemigroupND_spatial_lipschitz_sqrt_rate_norm hh u.continuous.aestronglyMeasurable
        (fun y => u.norm_coe_le_norm y) x y
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hlip.uniformContinuous
    (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hpoint : ∀ z, |v z - u z| < ε / 3 := by
    intro z
    have hb := (v - u).norm_coe_le_norm z
    have hab : |v z - u z| ≤ ‖v - u‖ := by
      simpa only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] using hb
    exact hab.trans_lt hn
  have h1 : dist (u x) (v x) < ε / 3 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hpoint x
  have h2 : dist (v x) (v y) < ε / 3 := hmod hxy
  have h3 : dist (v y) (u y) < ε / 3 := by rw [Real.dist_eq]; exact hpoint y
  have ht1 := dist_triangle (u x) (v x) (u y)
  have ht2 := dist_triangle (v x) (v y) (u y)
  linarith

/-- The resolvent output is genuinely uniformly continuous: its derived
right continuity makes it a uniform limit of actual positive-time Gaussian
regularizations, each spatially Lipschitz. -/
theorem uniformContinuous_actualGaussianHeatResolvent {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    UniformContinuous (actualGaussianHeatResolvent lam f : (Fin n → ℝ) → ℝ) :=
  uniformContinuous_of_closedHeatPath_right_continuous _
    (hasDerivWithinAt_actualGaussianHeatResolvent_zero hlam f hf).continuousWithinAt

/-- Actual Gaussian generator range witness on bounded uniformly continuous
data. This asserts the resolvent range inclusion, not a characterization of
the generator domain or a nonlinear Ricci-flow solution. -/
theorem exists_actualGaussianHeat_generator_range_witness {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    ∃ u : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      u = actualGaussianHeatResolvent lam f ∧
      UniformContinuous (u : (Fin n → ℝ) → ℝ) ∧ ‖u‖ ≤ ‖f‖ / lam ∧
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 := by
  exact ⟨actualGaussianHeatResolvent lam f, rfl,
    uniformContinuous_actualGaussianHeatResolvent hlam f hf,
    norm_actualGaussianHeatResolvent_le hlam f,
    hasDerivWithinAt_actualGaussianHeatResolvent_zero hlam f hf⟩

end RicciFlow.AnalyticPDE
