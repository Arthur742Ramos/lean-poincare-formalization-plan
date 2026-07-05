module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder

/-!
# Parabolic `C^{0,1}` membership of the model mild solution

The model heat-kernel theory in `HeatKernel1D.lean` proves, for the genuine mild solution `z`
(any fixed point of `heatMildSelfMap`), a full parabolic space-time regularity suite away from the
initial time `t₀`:

* spatial `C¹` (Lipschitz) modulus `lipschitzWith_heatMildFixedPoint_apply`, and
* time `Hölder-1/2` modulus `heatMildFixedPoint_apply_time_holder_bound`.

The parabolic Hölder framework in `ParabolicHolder.lean` packages both moduli into a single class:
`ParabolicC0AlphaOn 1` (parabolic-Lipschitz `C^{0,1}`) uses the parabolic distance
`max (√|Δt|) (dist x x')`, so a spatial-Lipschitz bound and a time-`Hölder-1/2` bound combine
exactly into the exponent-`1` parabolic Hölder estimate.

This module bridges the two files: on any interior parabolic slab `Icc t_lo T ×ˢ univ` with
`t₀ < t_lo`, the model mild solution belongs to `ParabolicC0AlphaOn 1`.  This is the canonical
parabolic Hölder-class membership that the Schauder / smooth-realization side of the Ricci–DeTurck
chart closure consumes (GAP 2 analytic core: the assembled space-time modulus in parabolic-class
form).  The uniform constants are obtained by bounding the interior-time coefficients over
`[t_lo, T]`.
-/

@[expose] public noncomputable section

open Real
open scoped Real NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-- **Parabolic `C^{0,1}` (parabolic-Lipschitz) membership of the model mild solution.**  For the
genuine model mild solution `z` (any fixed point of `heatMildSelfMap` for an `L`-Lipschitz initial
datum `u₀` and a `CQ`-bounded continuous reaction nonlinearity `Q`), on any interior parabolic slab
`Icc t_lo T ×ˢ univ` bounded away from the initial time (`t₀ < t_lo ≤ T`), the time-space function
`(t, x) ↦ z(t)(x)` (clamped in time by `Set.IccExtend`) belongs to the parabolic `C^{0,α}` class with
exponent `α = 1`.

The membership assembles the two interior regularity moduli of the mild solution into the parabolic
distance `parabolicDistance p q = max (√|Δt|) (dist x x')`:

* the spatial Lipschitz modulus `lipschitzWith_heatMildFixedPoint_apply` controls the `dist x x'`
  direction with a coefficient uniformly bounded over `[t_lo, T]` by
  `Ksp_max = n·‖u₀‖/√(π(t_lo−t₀)) + 2n·CQ·√(T−t₀)/√π`;
* the `Hölder-1/2` time modulus `heatMildFixedPoint_apply_time_holder_bound` controls the `√|Δt|`
  direction with a coefficient uniformly bounded over `[t_lo, T]` by `Ktm_coef` (the interior-time
  coefficients bounded by their endpoint values, absorbing the linear `|Δt|` term into `√|Δt|` via
  `|Δt| ≤ √(T−t_lo)·√|Δt|`).

The sup part is the a-priori bound `norm_heatMildFixedPoint_le` (`‖u₀‖ + CQ·(T − t₀)`). -/
theorem heatMildFixedPoint_parabolicC0AlphaOn {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T) :
    ParabolicC0AlphaOn 1
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
      (Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  have hlo_pos : 0 < t_lo - t₀ := by linarith
  have hsqrt_lo_pos : 0 < Real.sqrt (π * (t_lo - t₀)) :=
    Real.sqrt_pos.mpr (mul_pos Real.pi_pos hlo_pos)
  set Ksp_max : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
      + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π with hKsp_def
  set Ktm_coef : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
      + CQ * Real.sqrt (T - t_lo)
      + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) with hKtm_def
  set H : ℝ := Ksp_max + Ktm_coef with hH_def
  set B : ℝ := ‖u₀‖ + CQ * (T - t₀) with hB_def
  have hKsp_max_nonneg : 0 ≤ Ksp_max := by
    rw [hKsp_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by positivity
    have h2 : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (T - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hKtm_coef_nonneg : 0 ≤ Ktm_coef := by
    rw [hKtm_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π) := by
      positivity
    have h2 : 0 ≤ CQ * Real.sqrt (T - t_lo) := mul_nonneg hCQ (Real.sqrt_nonneg _)
    have h3 : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
      rw [show 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)
          = (4 * (n : ℝ) ^ 2 / π * Real.sqrt (T - t₀)) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hH_nonneg : 0 ≤ H := by rw [hH_def]; linarith
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]; exact add_nonneg (norm_nonneg _) (mul_nonneg hCQ (by linarith))
  -- Spatial Lipschitz modulus with a uniform interior constant.
  have hspace_le : ∀ (a : ℝ) (ha_mem : a ∈ Set.Icc t₀ T), t_lo ≤ a → a ≤ T →
      ∀ y y' : Fin n → ℝ, |z ⟨a, ha_mem⟩ y - z ⟨a, ha_mem⟩ y'| ≤ Ksp_max * dist y y' := by
    intro a ha_mem hla haT y y'
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hlip_a : LipschitzWith
        (((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))).toNNReal
          + (2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π).toNNReal)
        (⇑(z ⟨a, ha_mem⟩)) :=
      lipschitzWith_heatMildFixedPoint_apply hT u₀ hLnn hlip Q hQcont hQb z hz
        (t := ⟨a, ha_mem⟩) ht₀a
    have hd := hlip_a.dist_le_mul y y'
    rw [Real.dist_eq] at hd
    refine le_trans hd (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    have hA_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) := by positivity
    have hBc_nonneg : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (a - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    rw [NNReal.coe_add, Real.coe_toNNReal _ hA_nonneg, Real.coe_toNNReal _ hBc_nonneg, hKsp_def]
    have hA_le : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
        (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
    have hB_le : 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
        ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have h2nCQ : 0 ≤ 2 * (n : ℝ) * CQ := by
        rw [show 2 * (n : ℝ) * CQ = (2 * (n : ℝ)) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) h2nCQ
    linarith
  -- Time `Hölder-1/2` modulus with a uniform interior coefficient.
  have htime_le : ∀ (a b : ℝ) (ha_mem : a ∈ Set.Icc t₀ T) (hb_mem : b ∈ Set.Icc t₀ T),
      t_lo ≤ a → b ≤ T → a < b → ∀ y : Fin n → ℝ,
      |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤ Ktm_coef * Real.sqrt (b - a) := by
    intro a b ha_mem hb_mem hla hbT hab y
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hba_nonneg : 0 ≤ b - a := by linarith
    have hmod : |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤
        (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + (CQ * (b - a)
              + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)) :=
      heatMildFixedPoint_apply_time_holder_bound hT u₀ hLnn hlip Q hQcont hQb z hz
        (t₁ := ⟨a, ha_mem⟩) (t₂ := ⟨b, hb_mem⟩) ht₀a hab y
    refine le_trans hmod ?_
    have hsqrt_ba_le : Real.sqrt (b - a) ≤ Real.sqrt (T - t_lo) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt_a_le : Real.sqrt (a - t₀) ≤ Real.sqrt (T - t₀) :=
      Real.sqrt_le_sqrt (by linarith)
    have hB1 : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a)) := by
      have hdiv : ‖u₀‖ / Real.sqrt (π * (a - t₀)) ≤ ‖u₀‖ / Real.sqrt (π * (t_lo - t₀)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
          (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
      have hcoef : 0 ≤ (n : ℝ) * (n : ℝ) * (2 / Real.sqrt π * Real.sqrt (b - a)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdiv hcoef]
    have hB2a : CQ * (b - a) ≤ CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a) := by
      have h1 : CQ * Real.sqrt (b - a) ≤ CQ * Real.sqrt (T - t_lo) :=
        mul_le_mul_of_nonneg_left hsqrt_ba_le hCQ
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
      rwa [mul_assoc CQ (Real.sqrt (b - a)) (Real.sqrt (b - a)), Real.mul_self_sqrt hba_nonneg] at h2
    have hB2b : 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)
        ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      have hc : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π := by
        rw [show 4 * (n : ℝ) ^ 2 * CQ / π = (4 * (n : ℝ) ^ 2 / π) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      have h1 := mul_le_mul_of_nonneg_left hsqrt_a_le hc
      exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
    have hEq : Ktm_coef * Real.sqrt (b - a)
        = (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a)
          + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      rw [hKtm_def]; ring
    rw [hEq]
    linarith [hB1, hB2a, hB2b]
  -- Assemble the parabolic `C^{0,1}` class membership.
  refine ⟨B, hB_nonneg, H, hH_nonneg, ?_, ?_⟩
  · -- Sup (`C^0`) part.
    intro p hp
    rw [Set.mem_prod, Set.mem_Icc] at hp
    obtain ⟨⟨hlo_p, hhi_p⟩, -⟩ := hp
    have hp_mem : p.1 ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_p), hhi_p⟩
    show ‖Set.IccExtend hT (⇑z) p.1 p.2‖ ≤ B
    rw [Set.IccExtend_of_mem hT (⇑z) hp_mem, hB_def]
    exact le_trans ((z ⟨p.1, hp_mem⟩).norm_coe_le_norm p.2)
      (le_trans (z.norm_coe_le_norm ⟨p.1, hp_mem⟩)
        (norm_heatMildFixedPoint_le hT u₀ hLnn hlip Q hQcont hQb z hz))
  · -- Parabolic Hölder (exponent `1`) part.
    intro p hp q hq
    obtain ⟨t, x⟩ := p
    obtain ⟨t', x'⟩ := q
    rw [Set.mem_prod, Set.mem_Icc] at hp hq
    obtain ⟨⟨hlo_t, hhi_t⟩, -⟩ := hp
    obtain ⟨⟨hlo_t', hhi_t'⟩, -⟩ := hq
    have ht_mem : t ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t), hhi_t⟩
    have ht'_mem : t' ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t'), hhi_t'⟩
    show ‖Set.IccExtend hT (⇑z) t x - Set.IccExtend hT (⇑z) t' x'‖
      ≤ H * (parabolicDistance (t, x) (t', x')) ^ (1 : ℝ)
    rw [Set.IccExtend_of_mem hT (⇑z) ht_mem, Set.IccExtend_of_mem hT (⇑z) ht'_mem,
      Real.norm_eq_abs, Real.rpow_one]
    have hspace : |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| ≤ Ksp_max * dist x x' :=
      hspace_le t ht_mem hlo_t hhi_t x x'
    have htime : |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'|
        ≤ Ktm_coef * Real.sqrt |t - t'| := by
      rcases lt_trichotomy t t' with h | h | h
      · have hle := htime_le t t' ht_mem ht'_mem hlo_t hhi_t' h x'
        rw [abs_sub_comm, show |t - t'| = t' - t by rw [abs_of_neg (by linarith)]; ring]
        exact hle
      · subst h
        simp
      · have hle := htime_le t' t ht'_mem ht_mem hlo_t' hhi_t h x'
        rw [show |t - t'| = t - t' by rw [abs_of_pos (by linarith)]]
        exact hle
    calc |z ⟨t, ht_mem⟩ x - z ⟨t', ht'_mem⟩ x'|
        ≤ |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| + |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'| :=
          abs_sub_le _ _ _
      _ ≤ Ksp_max * dist x x' + Ktm_coef * Real.sqrt |t - t'| := add_le_add hspace htime
      _ ≤ Ksp_max * parabolicDistance (t, x) (t', x')
            + Ktm_coef * parabolicDistance (t, x) (t', x') := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (parabolicDistance.space_dist_le (t, x) (t', x')) hKsp_max_nonneg
          · exact mul_le_mul_of_nonneg_left
              (parabolicDistance.sqrt_time_le (t, x) (t', x')) hKtm_coef_nonneg
      _ = H * parabolicDistance (t, x) (t', x') := by rw [hH_def]; ring

end AnalyticPDE
end RicciFlow
