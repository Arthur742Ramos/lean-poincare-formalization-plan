import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianHeatResolvent

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace RicciFlow.AnalyticPDE

private theorem actualHeatPath_sub {n : ℕ}
    (u v : BoundedContinuousFunction (Fin n → ℝ) ℝ) (t : ℝ) :
    heatFlowPathBcf (u - v) t = heatFlowPathBcf u t - heatFlowPathBcf v t := by
  by_cases ht : 0 < t
  · rw [heatFlowPathBcf_of_pos _ ht, heatFlowPathBcf_of_pos _ ht,
      heatFlowPathBcf_of_pos _ ht]
    change (heatSemigroupNDclm (n := n) ht) (u - v) =
      (heatSemigroupNDclm (n := n) ht) u - (heatSemigroupNDclm (n := n) ht) v
    exact (heatSemigroupNDclm (n := n) ht).map_sub u v
  · simp only [heatFlowPathBcf, dif_neg ht]

/-- Actual Gaussian contraction excludes positive strong right-generator eigenvalues. -/
theorem eq_zero_of_actualHeat_right_generator_positive_eigenvalue {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (u : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hu : HasDerivWithinAt (heatFlowPathBcf u) (lam • u) (Ici 0) 0) : u = 0 := by
  by_contra hune
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hune
  have hzero : heatFlowPathBcf u 0 = u := by
    simp only [heatFlowPathBcf, dif_neg (lt_irrefl (0 : ℝ))]
  have hright : HasDerivWithinAt (heatFlowPathBcf u) (lam • u) (Ioi 0) 0 :=
    hu.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from by
      intro t ht
      change (0 : ℝ) < t at ht
      change (0 : ℝ) ≤ t
      exact le_of_lt ht)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Ioi (0 : ℝ)] 0,
      ‖heatFlowPathBcf u t - u - t • (lam • u)‖ ≤ (lam * ‖u‖ / 2) * |t| := by
    simpa only [hzero, sub_zero, Real.norm_eq_abs] using
      hright.isLittleO.bound (show 0 < lam * ‖u‖ / 2 by positivity)
  haveI : NeBot (𝓝[Ioi (0 : ℝ)] 0) := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  have hpositive : ∀ᶠ t : ℝ in 𝓝[Ioi (0 : ℝ)] 0, t ∈ Ioi 0 :=
    eventually_mem_nhdsWithin
  obtain ⟨t, ht, he⟩ := (hpositive.and hsmall).exists
  have htpos : 0 < t := ht
  have hc : ‖heatFlowPathBcf u t‖ ≤ ‖u‖ := by
    rw [heatFlowPathBcf_of_pos _ htpos]
    exact norm_heatSemigroupNDbcf_le htpos u
  have hsplit : (1 + t * lam) • u =
      heatFlowPathBcf u t - (heatFlowPathBcf u t - u - t • (lam • u)) := by
    rw [add_smul, one_smul, mul_smul]
    abel
  have hgrowth : ‖(1 + t * lam) • u‖ ≤
      ‖u‖ + (lam * ‖u‖ / 2) * t := by
    calc
      ‖(1 + t * lam) • u‖ =
          ‖heatFlowPathBcf u t - (heatFlowPathBcf u t - u - t • (lam • u))‖ := by
        rw [hsplit]
      _ ≤ ‖heatFlowPathBcf u t‖ + ‖heatFlowPathBcf u t - u - t • (lam • u)‖ :=
        norm_sub_le _ _
      _ ≤ ‖u‖ + (lam * ‖u‖ / 2) * t := by
        rw [abs_of_pos htpos] at he
        exact add_le_add hc he
  have hscalar : ‖(1 + t * lam) • u‖ = (1 + t * lam) * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 1 + t * lam by positivity)]
  rw [hscalar] at hgrowth
  have hstrict : 0 < t * lam * ‖u‖ := mul_pos (mul_pos htpos hlam) hnorm
  nlinarith

/-- Uniqueness on the literal actual heat-path strong right-generator domain.
The two hypotheses are the actual domain equations; no abstract generator is supplied. -/
theorem actualHeat_right_generator_equation_unique {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f u v : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hu : HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0)
    (hv : HasDerivWithinAt (heatFlowPathBcf v) (lam • v - f) (Ici 0) 0) : u = v := by
  have hd : HasDerivWithinAt (fun t : ℝ => heatFlowPathBcf u t - heatFlowPathBcf v t)
      (lam • (u - v)) (Ici 0) 0 := by
    convert! hu.sub hv using 1 <;> simp only [Pi.sub_apply, smul_sub] <;> abel
  have hdiff : HasDerivWithinAt (heatFlowPathBcf (u - v))
      (lam • (u - v)) (Ici 0) 0 := by
    have hfun : heatFlowPathBcf (u - v) =
        (fun t : ℝ => heatFlowPathBcf u t - heatFlowPathBcf v t) :=
      funext (actualHeatPath_sub u v)
    rw [hfun]
    exact hd
  exact sub_eq_zero.mp (eq_zero_of_actualHeat_right_generator_positive_eigenvalue hlam (u - v) hdiff)

/-- Every literal actual right-domain solution for a BUC source equals its Gaussian integral. -/
theorem eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation
    {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ))
    (u : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hu : HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0) :
    u = actualGaussianHeatResolvent lam f := by
  exact actualHeat_right_generator_equation_unique hlam f u (actualGaussianHeatResolvent lam f)
    hu (hasDerivWithinAt_actualGaussianHeatResolvent_zero hlam f hf)

/-- Existence and uniqueness of the actual strong right-generator resolvent equation.
The witness is the actual Bochner Gaussian integral, with no solver premise. -/
theorem existsUnique_actualHeat_right_generator_equation {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    ∃! u : BoundedContinuousFunction (Fin n → ℝ) ℝ,
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 := by
  refine ⟨actualGaussianHeatResolvent lam f,
    hasDerivWithinAt_actualGaussianHeatResolvent_zero hlam f hf, ?_⟩
  intro u hu
  exact eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation hlam f hf u hu

end RicciFlow.AnalyticPDE
