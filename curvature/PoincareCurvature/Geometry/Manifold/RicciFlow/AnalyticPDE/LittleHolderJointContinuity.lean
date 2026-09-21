import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel

/-!
# Joint time-space continuity of the little-Hölder heat propagator (Point 4 PDE milestone)

This module proves the missing analytic ingredient for an honest `DuhamelData`
instance on the little-Hölder space: joint continuity `DuhamelData.hSjoint` of
`(t, f) ↦ S t f` in the Hölder norm.

## Why little-Hölder

On the full Hölder space `C^α`, strong continuity of the heat semigroup at
`t = 0` in the `C^α` norm is **false** at the same exponent (high-frequency
modes decay too slowly in the seminorm).  The little-Hölder space
`LittleHolder n α = {f : HolderBCF α n | IsGoodHolder f}` consists exactly of
those `f` for which `S t f → f` in `C^α` as `t → 0⁺`; on it, the propagator is
jointly continuous.

## Proof strategy

* `propagator_val_eq_total` : for `t > 0`, the little-Hölder propagator acts as
  the total heat propagator `heatPropagatorTotal`.
* `norm_heatSemigroupHolderFun_le` : the Hölder heat semigroup is a contraction.
* `norm_heatPropagatorTotal_sub_le` : the key commutativity estimate
  `‖S(a+b) f - S a f‖ ≤ ‖S b f - f‖` for `a, b > 0`, via
  `S(a+b) = S a ∘ S b` (semigroup property) and contraction.  This avoids any
  circularity: both one-sided limits at `t₀ > 0` reduce to the `IsGoodHolder`
  property of `f₀` itself.
* `tendsto_propagator_nhdsWithin_zero` : `S t f → f` as `t → 0⁺` in little-Hölder
  norm, directly from `f.property : IsGoodHolder f.val`.
* `tendsto_propagator_time` : time continuity at every `t₀ ≥ 0`.
  - At `t₀ = 0`: left side is the identity, right side is `IsGoodHolder`.
  - At `t₀ > 0`: for `t > t₀`, `‖S t f₀ - S t₀ f₀‖ ≤ ‖S (t-t₀) f₀ - f₀‖`;
    for `t < t₀`, `‖S t₀ f₀ - S t f₀‖ ≤ ‖S (t₀-t) f₀ - f₀‖`.
* `littleHolderPropagator_hSjoint` : joint continuity on `Icc 0 T ×ˢ univ`,
  the exact `DuhamelData.hSjoint` statement, via the triangle inequality
  (contraction in space + time continuity).
* `littleHolderPropagator_hSbound` : the exact `DuhamelData.hSbound` statement
  with `M = 1`.

All results are `sorry`-free and use only the honest PDE ingredients above.
-/

namespace RicciFlow
namespace AnalyticPDE
namespace LittleHolder

open Filter Topology Set

variable {n : ℕ} {α : ℝ}

/-- For `t > 0`, the little-Hölder propagator acts as the total heat propagator
on the underlying Hölder function. -/
theorem propagator_val_eq_total {t : ℝ} (ht : 0 < t) (f : LittleHolder n α) :
    (littleHolderPropagator (n := n) (α := α) t f).val
      = heatPropagatorTotal (n := n) (α := α) t f.val := by
  have h : ((littleHolderPropagatorCLM (n := n) (α := α) ht) f).val
      = heatSemigroupHolderFun (n := n) (α := α) ht f.val := rfl
  rw [littleHolderPropagator_of_pos (n := n) (α := α) ht,
      heatPropagatorTotal_of_pos (n := n) (α := α) ht, h]

/-- The Hölder heat semigroup is a contraction. -/
theorem norm_heatSemigroupHolderFun_le {t : ℝ} (ht : 0 < t) (g : HolderBCF α n) :
    ‖heatSemigroupHolderFun (n := n) (α := α) ht g‖ ≤ ‖g‖ := by
  have h : (heatSemigroupHolderCLM (α := α) (n := n) ht) g
      = heatSemigroupHolderFun (n := n) (α := α) ht g := rfl
  rw [← h]
  calc ‖(heatSemigroupHolderCLM (α := α) (n := n) ht) g‖
      ≤ ‖heatSemigroupHolderCLM (α := α) (n := n) ht‖ * ‖g‖ :=
        (heatSemigroupHolderCLM (α := α) (n := n) ht).le_opNorm g
    _ ≤ 1 * ‖g‖ := by
        apply mul_le_mul_of_nonneg_right
          (norm_heatSemigroupHolderCLM_le (α := α) (n := n) ht)
        exact norm_nonneg _
    _ = ‖g‖ := one_mul _

/-- Key commutativity estimate: for `a, b > 0`,
`‖S (a+b) f - S a f‖ ≤ ‖S b f - f‖`.

Proof: `S (a+b) f = S a (S b f)` by the semigroup property, so
`S (a+b) f - S a f = S a (S b f - f)`, and `‖S a‖ ≤ 1`. -/
theorem norm_heatPropagatorTotal_sub_le {f : HolderBCF α n} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ‖heatPropagatorTotal (n := n) (α := α) (a + b) f
      - heatPropagatorTotal (n := n) (α := α) a f‖
    ≤ ‖heatPropagatorTotal (n := n) (α := α) b f - f‖ := by
  rw [heatPropagatorTotal_of_pos (n := n) (α := α) (add_pos ha hb) f,
      heatPropagatorTotal_of_pos (n := n) (α := α) ha f,
      heatPropagatorTotal_of_pos (n := n) (α := α) hb f]
  have hcomp : heatSemigroupHolderFun (n := n) (α := α) (add_pos ha hb) f
      = heatSemigroupHolderFun (n := n) (α := α) ha
        (heatSemigroupHolderFun (n := n) (α := α) hb f) :=
    (heatSemigroupHolderFun_comp (n := n) (α := α) ha hb f).symm
  rw [hcomp]
  have hlin : heatSemigroupHolderFun (n := n) (α := α) ha
        (heatSemigroupHolderFun (n := n) (α := α) hb f)
      - heatSemigroupHolderFun (n := n) (α := α) ha f
      = heatSemigroupHolderFun (n := n) (α := α) ha
        (heatSemigroupHolderFun (n := n) (α := α) hb f - f) := by
    have h1 : ∀ x : HolderBCF α n,
        heatSemigroupHolderFun (n := n) (α := α) ha x
        = (heatSemigroupHolderCLM (α := α) (n := n) ha) x := fun x => rfl
    rw [h1, h1, h1, map_sub]
  rw [hlin]
  exact norm_heatSemigroupHolderFun_le (n := n) (α := α) ha _

/-- Right-hand time continuity at `0`: `S t f → f` as `t → 0⁺` in little-Hölder
norm.  This is exactly the defining property `IsGoodHolder`. -/
theorem tendsto_propagator_nhdsWithin_zero (f : LittleHolder n α) :
    Filter.Tendsto (fun t : ℝ ↦ littleHolderPropagator (n := n) (α := α) t f)
      (𝓝[Ioi 0] (0:ℝ)) (𝓝 f) := by
  have hfT : Filter.Tendsto
      (fun t : ℝ ↦ heatPropagatorTotal (n := n) (α := α) t f.val)
      (𝓝[>] (0:ℝ)) (𝓝 f.val) := f.property
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hfT) ε hε
  refine ⟨δ, hδpos, fun t ht hdist => ?_⟩
  have htpos : 0 < t := ht
  rw [Subtype.dist_eq, propagator_val_eq_total (n := n) (α := α) htpos f]
  exact hδ ht hdist

/-- Time continuity of the little-Hölder propagator at every `t₀ ≥ 0`.

At `t₀ = 0`: the propagator is the identity for `t ≤ 0`, and `IsGoodHolder`
gives the right-hand limit.  At `t₀ > 0`: both one-sided limits reduce to
`IsGoodHolder f₀` via the commutativity estimate
`norm_heatPropagatorTotal_sub_le`. -/
theorem tendsto_propagator_time {f₀ : LittleHolder n α} {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t : ℝ ↦ littleHolderPropagator (n := n) (α := α) t f₀)
      (𝓝 t₀) (𝓝 (littleHolderPropagator (n := n) (α := α) t₀ f₀)) := by
  rcases eq_or_lt_of_le ht₀ with rfl | ht₀pos
  · -- Case t₀ = 0.
    have hP0 : littleHolderPropagator (n := n) (α := α) 0 f₀ = f₀ := by
      rw [littleHolderPropagator_of_nonpos (n := n) (α := α) (by norm_num)]
      rfl
    show ContinuousAt (fun t ↦ littleHolderPropagator (n := n) (α := α) t f₀) 0
    rw [Metric.continuousAt_iff]
    intro ε hε
    have h0 := tendsto_propagator_nhdsWithin_zero (n := n) (α := α) f₀
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h0) ε hε
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    by_cases htpos : 0 < t
    · rw [hP0]
      exact hδ htpos ht
    · have hPt : littleHolderPropagator (n := n) (α := α) t f₀ = f₀ := by
        rw [littleHolderPropagator_of_nonpos (n := n) (α := α)
          (by push_neg; exact le_of_not_gt htpos)]
        rfl
      rw [hPt, hP0]
      simpa using hε
  · -- Case t₀ > 0.
    show ContinuousAt (fun t ↦ littleHolderPropagator (n := n) (α := α) t f₀) t₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hfT : Filter.Tendsto
        (fun s : ℝ ↦ heatPropagatorTotal (n := n) (α := α) s f₀.val)
        (𝓝[>] (0:ℝ)) (𝓝 f₀.val) := f₀.property
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp hfT) (ε / 2) (by linarith)
    set δ := min δ₁ (t₀ / 2) with hδdef
    have hδpos : 0 < δ := lt_min hδ₁pos (by linarith)
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    have htpos : 0 < t := by
      have h1 : dist t t₀ < t₀ / 2 := lt_of_lt_of_le ht (min_le_right _ _)
      rw [Real.dist_eq] at h1
      have h2 := abs_lt.mp h1
      linarith
    rw [Subtype.dist_eq,
        propagator_val_eq_total (n := n) (α := α) htpos f₀,
        propagator_val_eq_total (n := n) (α := α) ht₀pos f₀,
        dist_eq_norm]
    have hδ₁le : dist t t₀ < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
    rcases lt_trichotomy t t₀ with hlt | heq | hgt
    · -- t < t₀: write t₀ = t + (t₀ - t), factor out S t.
      have hb : 0 < t₀ - t := by linarith
      have hb_lt : t₀ - t < δ₁ := by
        rw [Real.dist_eq] at hδ₁le
        have h2 := abs_lt.mp hδ₁le
        linarith
      have hdist : dist (t₀ - t) 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hb]
        exact hb_lt
      have hle := norm_heatPropagatorTotal_sub_le (n := n) (α := α)
        (f := f₀.val) htpos hb
      have heq2 : t + (t₀ - t) = t₀ := by ring
      rw [heq2] at hle
      have hgood := hδ₁ hb hdist
      rw [dist_eq_norm] at hgood
      rw [← norm_neg, neg_sub]
      calc ‖heatPropagatorTotal (n := n) (α := α) t₀ f₀.val
            - heatPropagatorTotal (n := n) (α := α) t f₀.val‖
          ≤ ‖heatPropagatorTotal (n := n) (α := α) (t₀ - t) f₀.val - f₀.val‖ :=
            hle
        _ < ε / 2 := hgood
        _ < ε := by linarith
    · -- t = t₀: trivial.
      rw [heq]
      simpa using hε
    · -- t > t₀: write t = t₀ + (t - t₀), factor out S t₀.
      have hb : 0 < t - t₀ := by linarith
      have hb_lt : t - t₀ < δ₁ := by
        rw [Real.dist_eq] at hδ₁le
        have h2 := abs_lt.mp hδ₁le
        linarith
      have hdist : dist (t - t₀) 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hb]
        exact hb_lt
      have hle := norm_heatPropagatorTotal_sub_le (n := n) (α := α)
        (f := f₀.val) ht₀pos hb
      have heq2 : t₀ + (t - t₀) = t := by ring
      rw [heq2] at hle
      have hgood := hδ₁ hb hdist
      rw [dist_eq_norm] at hgood
      calc ‖heatPropagatorTotal (n := n) (α := α) t f₀.val
            - heatPropagatorTotal (n := n) (α := α) t₀ f₀.val‖
          ≤ ‖heatPropagatorTotal (n := n) (α := α) (t - t₀) f₀.val - f₀.val‖ :=
            hle
        _ < ε / 2 := hgood
        _ < ε := by linarith

/-- Joint time-space continuity of the little-Hölder heat propagator on
`Icc 0 T`: the exact `DuhamelData.hSjoint` statement.

Proof: triangle inequality.  The space increment is controlled by contraction
(`‖S t‖ ≤ 1`), the time increment by `tendsto_propagator_time`. -/
theorem littleHolderPropagator_hSjoint {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun p : ℝ × LittleHolder n α ↦
      littleHolderPropagator (n := n) (α := α) p.1 p.2)
      (Icc 0 T ×ˢ univ) := by
  intro p hp
  obtain ⟨t₀, f₀⟩ := p
  simp only [mem_prod, mem_Icc, mem_univ, and_true] at hp
  obtain ⟨ht₀lo, ht₀hi⟩ := hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have htimeC : ContinuousAt
      (fun t ↦ littleHolderPropagator (n := n) (α := α) t f₀) t₀ :=
    tendsto_propagator_time (n := n) (α := α) (f₀ := f₀) ht₀lo
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    (Metric.continuousAt_iff.mp htimeC) (ε / 2) (by linarith)
  refine ⟨min δ₁ (ε / 2), lt_min hδ₁pos (by linarith), fun q hq hdist => ?_⟩
  obtain ⟨t, f⟩ := q
  simp only [mem_prod, mem_Icc, mem_univ, and_true] at hq
  obtain ⟨htlo, hthi⟩ := hq
  have htf : dist t t₀ < δ₁ := by
    have h1 : dist t t₀ ≤ dist (t, f) (t₀, f₀) := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    calc dist t t₀ ≤ dist (t, f) (t₀, f₀) := h1
      _ < min δ₁ (ε / 2) := hdist
      _ ≤ δ₁ := min_le_left _ _
  have hff : dist f f₀ < ε / 2 := by
    have h1 : dist f f₀ ≤ dist (t, f) (t₀, f₀) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    calc dist f f₀ ≤ dist (t, f) (t₀, f₀) := h1
      _ < min δ₁ (ε / 2) := hdist
      _ ≤ ε / 2 := min_le_right _ _
  have hspace : dist (littleHolderPropagator (n := n) (α := α) t f)
      (littleHolderPropagator (n := n) (α := α) t f₀)
      ≤ dist f f₀ := by
    by_cases htpos : 0 < t
    · rw [littleHolderPropagator_of_pos (n := n) (α := α) htpos]
      have hnorm := norm_littleHolderPropagatorCLM_le (n := n) (α := α) htpos
      calc dist ((littleHolderPropagatorCLM (n := n) (α := α) htpos) f)
            ((littleHolderPropagatorCLM (n := n) (α := α) htpos) f₀)
          = ‖(littleHolderPropagatorCLM (n := n) (α := α) htpos) (f - f₀)‖ := by
            rw [dist_eq_norm, map_sub]
        _ ≤ ‖littleHolderPropagatorCLM (n := n) (α := α) htpos‖ * ‖f - f₀‖ :=
            (littleHolderPropagatorCLM (n := n) (α := α) htpos).le_opNorm _
        _ ≤ 1 * ‖f - f₀‖ := by
            apply mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = dist f f₀ := by rw [one_mul, dist_eq_norm]
    · rw [littleHolderPropagator_of_nonpos (n := n) (α := α)
        (by push_neg; exact le_of_not_gt htpos)]
      simp
  have hspace_lt : dist (littleHolderPropagator (n := n) (α := α) t f)
      (littleHolderPropagator (n := n) (α := α) t f₀) < ε / 2 :=
    lt_of_le_of_lt hspace hff
  have htime_lt : dist (littleHolderPropagator (n := n) (α := α) t f₀)
      (littleHolderPropagator (n := n) (α := α) t₀ f₀) < ε / 2 := hδ₁ htf
  calc dist (littleHolderPropagator (n := n) (α := α) t f)
        (littleHolderPropagator (n := n) (α := α) t₀ f₀)
      ≤ dist (littleHolderPropagator (n := n) (α := α) t f)
          (littleHolderPropagator (n := n) (α := α) t f₀)
        + dist (littleHolderPropagator (n := n) (α := α) t f₀)
          (littleHolderPropagator (n := n) (α := α) t₀ f₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hspace_lt htime_lt
    _ = ε := by ring

/-- The `DuhamelData.hSbound` bound for the little-Hölder propagator, with
`M = 1`: uniform operator-norm bound on `Icc 0 T`. -/
theorem littleHolderPropagator_hSbound {T : ℝ} (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0:ℝ) T,
      ‖littleHolderPropagator (n := n) (α := α) t‖ ≤ M := by
  refine ⟨1, zero_le_one, fun t ht => ?_⟩
  by_cases htpos : 0 < t
  · rw [littleHolderPropagator_of_pos (n := n) (α := α) htpos]
    exact norm_littleHolderPropagatorCLM_le (n := n) (α := α) htpos
  · rw [littleHolderPropagator_of_nonpos (n := n) (α := α) htpos]
    exact ContinuousLinearMap.norm_id_le

end LittleHolder
end AnalyticPDE
end RicciFlow
