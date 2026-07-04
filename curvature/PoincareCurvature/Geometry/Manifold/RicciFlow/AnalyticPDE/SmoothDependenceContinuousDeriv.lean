module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk

set_option linter.unusedSectionVars false

/-!
# `C¹` dependence of the flow on initial data from a *merely continuous* spatial derivative

This module closes the "general (non-Lipschitz) modulus" step flagged as remaining in the
`C¹` layer of the smooth-dependence tower (`SmoothDependenceCk`).  The practical
`C¹`-dependence entry point proved there, `hasFDerivAt_flow_of_lipschitz_deriv_eventually`,
requires the field's spatial derivative `Dv` to be *Lipschitz* on the trajectory chords.  A
genuine `C^1` field only supplies a *jointly continuous* derivative — no Lipschitz constant.

Here we remove the Lipschitz hypothesis for a **finite-dimensional** state space (the manifold
model space), extracting a monotone modulus of continuity `ω → 0` from the joint continuity of
`Dv` via Heine–Cantor uniform continuity on the compact trajectory tube.  The self-contained
analytic core is `exists_monotone_modulus_of_continuousOn_tube`: a continuous function that
vanishes along the anchor of a compact tube admits a monotone, `0⁺`-vanishing modulus dominating
it on the tube.  Feeding it to `hasFDerivAt_flow_of_uniform_deriv_modulus_eventually` yields the
unconditional `C¹` flow-dependence theorem `hasFDerivAt_flow_of_continuous_deriv` for any field
with a globally-defined, jointly continuous spatial derivative.

Everything is proved sorry-free from Mathlib and the `SmoothDependenceCk` tower; no PDE or
manifold content is used.
-/

open Set Filter Topology
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

@[expose] public noncomputable section

/-- **Monotone modulus of continuity on a compact tube.**  Let `E` be a proper (e.g. finite
dimensional) normed space, `T ⊆ ℝ` compact, and `f : ℝ → E → ℝ` a function whose uncurrying is
continuous, nonnegative, and vanishes at the origin over `T` (`f s 0 = 0` for `s ∈ T`).  Then
there is a modulus `ω : ℝ → ℝ` which is nonnegative, monotone, tends to `0` as its argument
tends to `0⁺`, and dominates `f` on the radius-`R` tube: `f s w ≤ ω ‖w‖` whenever `s ∈ T` and
`‖w‖ ≤ R`.

The witness is `ω r = ⨆` (sup) of `f` over the sub-tube of radius `min r R`; boundedness comes
from compactness, monotonicity from the nested tubes, and the `0⁺` limit from Heine–Cantor
uniform continuity of `f` on the full compact tube. -/
theorem exists_monotone_modulus_of_continuousOn_tube
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {T : Set ℝ} (hT : IsCompact T) (R : ℝ)
    {f : ℝ → E → ℝ} (hf : Continuous fun p : ℝ × E => f p.1 p.2)
    (hf0 : ∀ s ∈ T, f s 0 = 0) (hfnn : ∀ s w, 0 ≤ f s w) :
    ∃ ω : ℝ → ℝ, (∀ r, 0 ≤ ω r) ∧ Monotone ω ∧
      Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0) ∧
      (∀ s ∈ T, ∀ w : E, ‖w‖ ≤ R → f s w ≤ ω ‖w‖) := by
  set F : ℝ × E → ℝ := fun p => f p.1 p.2 with hF
  set box : ℝ → Set (ℝ × E) := fun r => T ×ˢ Metric.closedBall (0 : E) (min r R) with hbox
  have hcompactFull : IsCompact (T ×ˢ Metric.closedBall (0 : E) R) :=
    hT.prod (isCompact_closedBall 0 R)
  have hbddFull : BddAbove (F '' (T ×ˢ Metric.closedBall (0 : E) R)) :=
    hcompactFull.bddAbove_image hf.continuousOn
  have hsub : ∀ r, box r ⊆ T ×ˢ Metric.closedBall (0 : E) R := fun r =>
    Set.prod_mono (le_refl T) (Metric.closedBall_subset_closedBall (min_le_right r R))
  have hbdd : ∀ r, BddAbove (F '' box r) := fun r => hbddFull.mono (Set.image_mono (hsub r))
  refine ⟨fun r => sSup (F '' box r), ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro r
    exact Real.sSup_nonneg (by rintro x ⟨p, _, rfl⟩; exact hfnn p.1 p.2)
  · -- monotonicity
    intro a b hab
    have hboxsub : box a ⊆ box b :=
      Set.prod_mono (le_refl T) (Metric.closedBall_subset_closedBall (min_le_min hab le_rfl))
    rcases (F '' box a).eq_empty_or_nonempty with he | hne
    · show sSup (F '' box a) ≤ sSup (F '' box b)
      rw [he, Real.sSup_empty]
      exact Real.sSup_nonneg (by rintro x ⟨p, _, rfl⟩; exact hfnn p.1 p.2)
    · exact csSup_le_csSup (hbdd b) hne (Set.image_mono hboxsub)
  · -- `0⁺` limit
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have huc : UniformContinuousOn F (T ×ˢ Metric.closedBall (0 : E) R) :=
      hcompactFull.uniformContinuousOn_of_continuous hf.continuousOn
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
    refine ⟨δ, hδpos, ?_⟩
    intro r hr hrδ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Set.mem_Ici.mp hr)] at hrδ
    have hωr_le : sSup (F '' box r) ≤ ε / 2 := by
      rcases (F '' box r).eq_empty_or_nonempty with he | hne
      · rw [he, Real.sSup_empty]; positivity
      · refine csSup_le hne ?_
        rintro x ⟨⟨s, w⟩, hmem, rfl⟩
        obtain ⟨hsT, hwmem⟩ := hmem
        have hwle : ‖w‖ ≤ min r R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hwmem
        have hRnn : 0 ≤ R := le_trans (le_trans (norm_nonneg w) hwle) (min_le_right r R)
        have hmemW : (s, w) ∈ T ×ˢ Metric.closedBall (0 : E) R := by
          refine ⟨hsT, ?_⟩
          simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
          exact le_trans hwle (min_le_right r R)
        have hmem0 : (s, (0 : E)) ∈ T ×ˢ Metric.closedBall (0 : E) R := by
          refine ⟨hsT, ?_⟩
          simp only [Metric.mem_closedBall, dist_self]; exact hRnn
        have hdistlt : dist ((s, w) : ℝ × E) (s, (0 : E)) < δ := by
          have hwδ : ‖w‖ < δ := lt_of_le_of_lt (le_trans hwle (min_le_left r R)) hrδ
          rw [Prod.dist_eq]
          refine max_lt ?_ ?_
          · simpa using hδpos
          · rw [dist_eq_norm, sub_zero]; exact hwδ
        have hFlt := hδ (s, w) hmemW (s, (0 : E)) hmem0 hdistlt
        rw [hF] at hFlt
        simp only [hf0 s hsT, Real.dist_eq, sub_zero] at hFlt
        exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hFlt)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.sSup_nonneg (by rintro x ⟨p, _, rfl⟩; exact hfnn p.1 p.2))]
    exact lt_of_le_of_lt hωr_le (by linarith)
  · -- domination on the tube
    intro s hsT w hwR
    refine le_csSup (hbdd ‖w‖) ⟨(s, w), ?_, rfl⟩
    refine ⟨hsT, ?_⟩
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, min_eq_left hwR, le_refl]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
variable {Φ : E → ℝ → E}

/-- **`C¹` dependence of the flow from a jointly continuous spatial derivative.**  For a
finite-dimensional state space, if the field `v s` has a globally-defined Fréchet derivative
`Dv s ξ` at every point with `(s, ξ) ↦ Dv s ξ` jointly continuous, and the linearisation
coefficient `A` agrees with the derivative along the anchor trajectory (`A s = Dv s (Φ x₀ s)`),
then the time-`t` flow map `z ↦ Φ z t` is Fréchet differentiable at `x₀` with derivative the
resolvent `fundamentalSolution … t = D_x Φ_t`.

No Lipschitz constant for `Dv` is needed: the modulus of continuity is furnished by
`exists_monotone_modulus_of_continuousOn_tube` applied to the derivative oscillation
`(s, w) ↦ ‖Dv s (Φ x₀ s + w) - Dv s (Φ x₀ s)‖` on the compact trajectory tube `Icc t₀ t`, which
is uniformly continuous by Heine–Cantor.  This is the unconditional `C¹` flow-dependence theorem
for every `C^1` field on a finite-dimensional space. -/
theorem hasFDerivAt_flow_of_continuous_deriv [FiniteDimensional ℝ E]
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hAeq : ∀ s, A s = Dv s (Φ x₀ s)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set γ : ℝ → E := fun s => Φ x₀ s with hγ
  have hγc : Continuous γ := (hΦ x₀).continuous
  -- the derivative oscillation around the anchor trajectory
  set f : ℝ → E → ℝ := fun s w => ‖Dv s (γ s + w) - Dv s (γ s)‖ with hf
  have hfc : Continuous fun p : ℝ × E => f p.1 p.2 := by
    have hg1 : Continuous fun p : ℝ × E => Dv p.1 (γ p.1 + p.2) :=
      hDvc.comp (continuous_fst.prodMk ((hγc.comp continuous_fst).add continuous_snd))
    have hg2 : Continuous fun p : ℝ × E => Dv p.1 (γ p.1) :=
      hDvc.comp (continuous_fst.prodMk (hγc.comp continuous_fst))
    exact (hg1.sub hg2).norm
  have hf0 : ∀ s ∈ Set.Icc t₀ t, f s 0 = 0 := by
    intro s _; simp [hf]
  have hfnn : ∀ s w, 0 ≤ f s w := fun s w => norm_nonneg _
  obtain ⟨ω, hωnn, hωmono, hω0, hωbd⟩ :=
    exists_monotone_modulus_of_continuousOn_tube (T := Set.Icc t₀ t) isCompact_Icc 1 hfc hf0 hfnn
  -- the neighbourhood of `x₀` on which the chords stay inside the unit tube
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hnbhd : ∀ᶠ z in 𝓝 x₀, c * ‖z - x₀‖ < 1 := by
    have hcont : Continuous fun z : E => c * ‖z - x₀‖ :=
      continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const))
    have h0lt : c * ‖x₀ - x₀‖ < 1 := by simp
    exact (hcont.tendsto x₀).eventually (Iio_mem_nhds h0lt)
  refine hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    (Filter.Eventually.of_forall
      (fun z s _ ξ _ => (hDv s ξ).hasFDerivWithinAt)) hωnn hωmono hω0 ?_
  filter_upwards [hnbhd] with z hz
  intro s hs ξ hξ
  -- bound the chord displacement `‖ξ - γ s‖ ≤ c ‖z - x₀‖ < 1`
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
  have hq1 : q ≤ 1 := by linarith
  have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
    have hp1 : p = 1 - q := by linarith
    rw [hp1, sub_smul, one_smul, smul_sub]; abel
  have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
    have h := dist_flow_apply_le hv hΦ h0 z x₀ s
    rwa [dist_eq_norm, dist_eq_norm] at h
  have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
    rw [hc]
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    exact sub_le_sub_right hs.2.le t₀
  have hxi : ‖(p • Φ x₀ s + q • Φ z s) - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
    calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
          mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
      _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
      _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
      _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = c * ‖z - x₀‖ := mul_comm _ _
  have hxi1 : ‖(p • Φ x₀ s + q • Φ z s) - Φ x₀ s‖ ≤ (1 : ℝ) := le_trans hxi (le_of_lt hz)
  -- rewrite the oscillation as `f` and dominate by the modulus
  have hsIcc : s ∈ Set.Icc t₀ t := ⟨hs.1, hs.2.le⟩
  have hbd := hωbd s hsIcc ((p • Φ x₀ s + q • Φ z s) - Φ x₀ s) hxi1
  have hfeval : f s ((p • Φ x₀ s + q • Φ z s) - Φ x₀ s)
      = ‖Dv s (p • Φ x₀ s + q • Φ z s) - A s‖ := by
    rw [hAeq s]
    simp only [hf, hγ, add_sub_cancel]
  rw [hfeval] at hbd
  exact hbd

/-- **The flow map is differentiable at the base point** from a jointly continuous spatial
derivative (consumer-facing corollary of `hasFDerivAt_flow_of_continuous_deriv`):
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_continuous_deriv [FiniteDimensional ℝ E]
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hAeq : ∀ s, A s = Dv s (Φ x₀ s)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_continuous_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hDv hDvc hAeq).differentiableAt

/-- **The Fréchet derivative of the flow map is the resolvent** from a jointly continuous spatial
derivative: `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_continuous_deriv [FiniteDimensional ℝ E]
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hAeq : ∀ s, A s = Dv s (Φ x₀ s)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_continuous_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hDv hDvc hAeq).fderiv

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
