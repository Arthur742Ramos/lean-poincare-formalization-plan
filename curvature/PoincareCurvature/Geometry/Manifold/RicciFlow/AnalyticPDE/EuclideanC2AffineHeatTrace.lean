import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffinePullback

/-!
# Actual initial heat traces after certified scalar affine pullback

Source candidate, uncompiled. Affine scalar transport is a Source dependency
until its separate native qualification succeeds. Existing uniform continuity
of the actual initial second slots is transported by the affine map and finite
constant-coefficient sums. The heat traces then follow from the actual bounded
C2 certificates, with no supplied heat-trace oracle.

The dimensions remain independent. This does not conjugate the time generator
back to the original coordinates or identify it with a frozen metric operator.
-/

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace RicciFlow.AnalyticPDE.EuclideanBoundedC2Data

/-- An arbitrary affine CLM pullback preserves the uniform continuity of
the actual second slots. The premise is the existing initial Hessian evidence. -/
theorem uniformContinuous_precompAffine_second {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ))
    (k l : Fin m) :
    UniformContinuous ((D.precompAffine a L).second k l : (Fin m → ℝ) → ℝ) := by
  classical
  have hmap : UniformContinuous (fun x : Fin m → ℝ => a + L x) :=
    uniformContinuous_const.add L.uniformContinuous
  have hrepr : ((D.precompAffine a L).second k l : (Fin m → ℝ) → ℝ) =
      (fun x => ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x)) := by
    funext x
    exact D.precompAffine_second_apply a L k l x
  rw [hrepr]
  apply Finset.uniformContinuous_sum
  intro p _
  apply Finset.uniformContinuous_sum
  intro q _
  exact ((hsecond p q).comp hmap).const_mul'
    (L (Pi.single k 1) p * L (Pi.single l 1) q)

/-- Genuine global BCF value/gradient/Hessian heat trace for the pulled data.
The value and first-slot uniform continuity are derived by the existing API. -/
theorem continuousAt_heatC2Trace_precompAffine_zero {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ)) :
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf (D.precompAffine a L).value t,
        (fun k => heatFlowPathBcf ((D.precompAffine a L).first k) t),
        (fun k l => heatFlowPathBcf ((D.precompAffine a L).second k l) t))) 0 :=
  (D.precompAffine a L).continuousAt_heatC2Trace_zero
    (fun k l => D.uniformContinuous_precompAffine_second a L hsecond k l)

/-- The actual mixed Gaussian Hessian convolution tends locally uniformly
to the explicit affine-transformed initial Hessian, without a trace premise. -/
theorem tendstoUniformlyOn_heatHessian_precompAffine_zero {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k l : Fin m)
    {K : Set (Fin m → ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun t x => heatHessianEntryConvolutionND t (D.precompAffine a L).value k l x)
      (fun x => ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x))
      (𝓝[>] 0) K := by
  have h := (D.precompAffine a L).tendstoUniformlyOn_heatHessian_zero k l hK
  have hrepr : ((D.precompAffine a L).second k l : (Fin m → ℝ) → ℝ) =
      (fun x => ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x)) := by
    funext x
    exact D.precompAffine_second_apply a L k l x
  rw [hrepr] at h
  exact h

/-- The right initial time derivative of the actual heat path is the trace
of its pulled Hessian. No identification with an original-coordinate frozen
metric operator is asserted. -/
theorem hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ) :
    HasDerivWithinAt (fun t => heatFlowPathBcf (D.precompAffine a L).value t x)
      (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) * D.second p q (a + L x))
      (Ici 0) 0 := by
  simpa only [EuclideanBoundedC2Data.precompAffine_second_apply] using
    (D.precompAffine a L).hasDerivWithinAt_heatFlowPathBcf_apply_zero x

end RicciFlow.AnalyticPDE.EuclideanBoundedC2Data
