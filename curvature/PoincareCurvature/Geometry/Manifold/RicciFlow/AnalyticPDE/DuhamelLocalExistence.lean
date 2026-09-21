import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.DuhamelContraction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamelInstance

set_option linter.unusedSectionVars false

/-!
# Local Duhamel existence for locally Lipschitz nonlinearities (Point 4 PDE milestone)

## Mathematical context

`DuhamelContraction.lean` proves existence/uniqueness of mild solutions when the
nonlinearity `N : X → X` is **globally** Lipschitz. The genuine Ricci–DeTurck
nonlinearity `N_RD` is only **locally** Lipschitz (it is a smooth function of the
2-jet, hence Lipschitz on bounded sets). This file bridges the gap via the
standard radial-retraction trick:

1. **Radial retraction** (`radialRetract`): For `R > 0`, the map
   `ρ(x) = c + (R / max(‖x - c‖, R)) • (x - c)` retracts `X` onto
   `closedBall c R`, fixes the ball pointwise, and is 2-Lipschitz.
2. **Globally Lipschitz extension** (`retractN`): If `N` is `L`-Lipschitz on
   `closedBall c R`, then `Ñ = N ∘ ρ` is `2L`-Lipschitz globally and agrees
   with `N` on the ball.
3. **Local existence** (`LocalDuhamelData.exists_local_mild_solution`): Apply
   the global Duhamel theorem to `Ñ`, then show the solution stays in the ball
   for small time, hence is a genuine mild solution for `N`.

This is the exact bridge needed for the Ricci–DeTurck PDE: once the local
Lipschitz estimate for the genuine `N_RD` on `C^{2,α}` balls is available, this
theorem yields local-in-time mild existence and uniqueness.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## 1. Radial retraction onto a closed ball -/

/-- **Radial retraction onto `closedBall c R`.**

`ρ(x) = c + (R / max(‖x - c‖, R)) • (x - c)`. This is the identity on the ball
and projects radially onto the sphere outside. -/
noncomputable def radialRetract (c : X) (R : ℝ≥0) : X → X :=
  fun x => c + ((R : ℝ) / max ‖x - c‖ (R : ℝ)) • (x - c)

/-- The retraction fixes points in the ball (for `R > 0`). -/
theorem radialRetract_eq_self {c : X} {R : ℝ≥0} (hR : 0 < R)
    {x : X} (hx : ‖x - c‖ ≤ (R : ℝ)) :
    radialRetract c R x = x := by
  unfold radialRetract
  have hmax : max ‖x - c‖ (R : ℝ) = (R : ℝ) := max_eq_right hx
  rw [hmax]
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hR)
  rw [div_self hRne, one_smul, add_sub_cancel]

/-- The retraction maps into the closed ball. -/
theorem radialRetract_mem_closedBall (c : X) {R : ℝ≥0} (hR : 0 < R)
    (x : X) : radialRetract c R x ∈ closedBall c (R : ℝ≥0) := by
  unfold radialRetract
  rw [mem_closedBall, dist_eq_norm]
  have h1 : c + ((R : ℝ) / max ‖x - c‖ (R : ℝ)) • (x - c) - c =
      ((R : ℝ) / max ‖x - c‖ (R : ℝ)) • (x - c) := by abel
  rw [h1, norm_smul]
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := R.coe_nonneg
  have hmax_pos : (0 : ℝ) < max ‖x - c‖ (R : ℝ) :=
    lt_max_of_lt_right (by exact_mod_cast hR)
  have hfrac_nn : (0 : ℝ) ≤ (R : ℝ) / max ‖x - c‖ (R : ℝ) :=
    div_nonneg hRnn (le_of_lt hmax_pos)
  rw [Real.norm_eq_abs, abs_of_nonneg hfrac_nn]
  -- `(R / max) * ‖x - c‖ ≤ R`
  have hle : (R : ℝ) / max ‖x - c‖ (R : ℝ) * ‖x - c‖ ≤ (R : ℝ) := by
    have hmax_le : ‖x - c‖ ≤ max ‖x - c‖ (R : ℝ) := le_max_left _ _
    calc (R : ℝ) / max ‖x - c‖ (R : ℝ) * ‖x - c‖
        ≤ (R : ℝ) / max ‖x - c‖ (R : ℝ) * max ‖x - c‖ (R : ℝ) :=
          mul_le_mul_of_nonneg_left hmax_le hfrac_nn
      _ = (R : ℝ) := div_mul_cancel₀ (R : ℝ) (ne_of_gt hmax_pos)
  exact hle

/-- Auxiliary: the scalar radial map `ψ(y) = (R / max(‖y‖, R)) • y` is 2-Lipschitz
in the norm sense. -/
theorem norm_radialScalar_sub_le {R : ℝ} (hR : 0 < R) (a b : X) :
    ‖(R / max ‖a‖ R) • a - (R / max ‖b‖ R) • b‖ ≤ 2 * ‖a - b‖ := by
  have hRnn : (0 : ℝ) ≤ R := le_of_lt hR
  have hRne : R ≠ 0 := ne_of_gt hR
  -- Case split on whether ‖a‖, ‖b‖ ≤ R
  by_cases ha : ‖a‖ ≤ R <;> by_cases hb : ‖b‖ ≤ R
  · -- Both inside: ψ is the identity
    have h1 : max ‖a‖ R = R := max_eq_right ha
    have h2 : max ‖b‖ R = R := max_eq_right hb
    rw [h1, h2, div_self hRne, one_smul, one_smul]
    have hnn := norm_nonneg (a - b)
    linarith
  · -- a inside, b outside
    have h1 : max ‖a‖ R = R := max_eq_right ha
    have h2 : R < max ‖b‖ R := lt_max_of_lt_left (lt_of_not_ge hb)
    have hbR : R < ‖b‖ := by
      have := lt_max_iff.mp h2
      rcases this with h | h
      · exact h
      · linarith
    rw [h1, div_self hRne, one_smul]
    -- `‖a - (R/‖b‖) • b‖ ≤ ‖a - b‖ + (‖b‖ - R) ≤ 2‖a - b‖`
    have hfrac : (0 : ℝ) ≤ R / ‖b‖ := div_nonneg hRnn (le_of_lt (lt_trans hR hbR))
    have hfrac_lt : R / ‖b‖ < 1 := by
      rw [div_lt_one (lt_trans hR hbR)]
      exact hbR
    have hdiff : ‖b - (R / ‖b‖) • b‖ = ‖b‖ - R := by
      have h : b - (R / ‖b‖) • b = (1 - R / ‖b‖) • b := by
        rw [sub_smul, one_smul]
      rw [h, norm_smul, Real.norm_eq_abs]
      have habs : |1 - R / ‖b‖| = 1 - R / ‖b‖ := abs_of_nonneg (by linarith)
      rw [habs]
      have hbn : ‖b‖ ≠ 0 := ne_of_gt (lt_trans hR hbR)
      field_simp
    have hnorm_le : ‖b‖ - R ≤ ‖a - b‖ := by
      have h1 : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
        calc ‖b‖ - ‖a‖ ≤ ‖b - a‖ := norm_sub_norm_le _ _
          _ = ‖a - b‖ := norm_sub_rev _ _
      linarith
    calc ‖a - (R / max ‖b‖ R) • b‖
        = ‖a - (R / ‖b‖) • b‖ := by rw [max_eq_left (le_of_lt hbR)]
      _ ≤ ‖a - b‖ + ‖b - (R / ‖b‖) • b‖ := by
          have h_eq : a - (R / ‖b‖) • b = (a - b) + (b - (R / ‖b‖) • b) := by abel
          rw [h_eq]
          exact norm_add_le _ _
      _ = ‖a - b‖ + (‖b‖ - R) := by rw [hdiff]
      _ ≤ ‖a - b‖ + ‖a - b‖ := by linarith
      _ = 2 * ‖a - b‖ := by ring
  · -- a outside, b inside: symmetric
    have h1 : R < max ‖a‖ R := lt_max_of_lt_left (lt_of_not_ge ha)
    have h2 : max ‖b‖ R = R := max_eq_right hb
    have haR : R < ‖a‖ := by
      have := lt_max_iff.mp h1
      rcases this with h | h
      · exact h
      · linarith
    rw [h2, div_self hRne, one_smul]
    have hdiff : ‖a - (R / ‖a‖) • a‖ = ‖a‖ - R := by
      have h : a - (R / ‖a‖) • a = (1 - R / ‖a‖) • a := by
        rw [sub_smul, one_smul]
      rw [h, norm_smul, Real.norm_eq_abs]
      have hfrac_lt : R / ‖a‖ < 1 := by
        rw [div_lt_one (lt_trans hR haR)]
        exact haR
      have habs : |1 - R / ‖a‖| = 1 - R / ‖a‖ := abs_of_nonneg (by linarith)
      rw [habs]
      have han : ‖a‖ ≠ 0 := ne_of_gt (lt_trans hR haR)
      field_simp
    have hnorm_le : ‖a‖ - R ≤ ‖a - b‖ := by
      have h1 : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le _ _
      linarith
    calc ‖(R / max ‖a‖ R) • a - b‖
        = ‖(R / ‖a‖) • a - b‖ := by rw [max_eq_left (le_of_lt haR)]
      _ ≤ ‖(R / ‖a‖) • a - a‖ + ‖a - b‖ := by
          have h_eq : (R / ‖a‖) • a - b = ((R / ‖a‖) • a - a) + (a - b) := by abel
          rw [h_eq]
          exact norm_add_le _ _
      _ = (‖a‖ - R) + ‖a - b‖ := by
          have : ‖(R / ‖a‖) • a - a‖ = ‖a - (R / ‖a‖) • a‖ := by rw [norm_sub_rev]
          rw [this, hdiff]
      _ ≤ ‖a - b‖ + ‖a - b‖ := by linarith
      _ = 2 * ‖a - b‖ := by ring
  · -- Both outside
    have haR : R < ‖a‖ := lt_of_not_ge ha
    have hbR : R < ‖b‖ := lt_of_not_ge hb
    have h1 : max ‖a‖ R = ‖a‖ := max_eq_left (le_of_lt haR)
    have h2 : max ‖b‖ R = ‖b‖ := max_eq_left (le_of_lt hbR)
    rw [h1, h2]
    -- `‖(R/‖a‖)•a - (R/‖b‖)•b‖ = R * ‖a/‖a‖ - b/‖b‖‖ ≤ 2‖a - b‖`
    have han : (0:ℝ) < ‖a‖ := lt_trans hR haR
    have hbn : (0:ℝ) < ‖b‖ := lt_trans hR hbR
    have key : ‖(R / ‖a‖) • a - (R / ‖b‖) • b‖ ≤ 2 * ‖a - b‖ := by
      have hsmul : (R / ‖a‖) • a - (R / ‖b‖) • b
          = R • ((1 / ‖a‖) • a - (1 / ‖b‖) • b) := by
        rw [smul_sub]
        congr 1 <;> rw [smul_smul] <;> ring_nf
      rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hRnn]
      -- `‖(1/‖a‖)•a - (1/‖b‖)•b‖ ≤ 2‖a-b‖/R`
      have hunit : ‖(1 / ‖a‖) • a - (1 / ‖b‖) • b‖ ≤ 2 * ‖a - b‖ / R := by
        have hdecomp : (1 / ‖a‖) • a - (1 / ‖b‖) • b
            = (1 / ‖a‖) • (a - b) + ((1 / ‖a‖) - (1 / ‖b‖)) • b := by
          rw [smul_sub, sub_smul]
          abel
        rw [hdecomp]
        have hterm1 : ‖(1 / ‖a‖) • (a - b)‖ ≤ ‖a - b‖ / R := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have h1a : 1 / ‖a‖ ≤ 1 / R := by
            apply one_div_le_one_div_of_le hR (le_of_lt haR)
          calc (1 / ‖a‖) * ‖a - b‖ ≤ (1 / R) * ‖a - b‖ :=
                mul_le_mul_of_nonneg_right h1a (norm_nonneg _)
            _ = ‖a - b‖ / R := by ring
        have hterm2 : ‖((1 / ‖a‖) - (1 / ‖b‖)) • b‖ ≤ ‖a - b‖ / R := by
          have han_ne : ‖a‖ ≠ 0 := ne_of_gt han
          have hbn_ne : ‖b‖ ≠ 0 := ne_of_gt hbn
          rw [norm_smul, Real.norm_eq_abs]
          have hdiff : |1 / ‖a‖ - 1 / ‖b‖| = |‖b‖ - ‖a‖| / (‖a‖ * ‖b‖) := by
            have h1 : (1:ℝ) / ‖a‖ - 1 / ‖b‖ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by
              field_simp
            rw [h1, abs_div, abs_mul, abs_of_pos han, abs_of_pos hbn]
          rw [hdiff]
          have hle1 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
            rw [abs_sub_comm]
            have h1 : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le _ _
            have h2 : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
              calc ‖b‖ - ‖a‖ ≤ ‖b - a‖ := norm_sub_norm_le _ _
                _ = ‖a - b‖ := norm_sub_rev _ _
            exact abs_le.mpr ⟨by linarith, h1⟩
          have h_eq : |‖b‖ - ‖a‖| / (‖a‖ * ‖b‖) * ‖b‖ = |‖b‖ - ‖a‖| / ‖a‖ := by
            field_simp
          rw [h_eq]
          have h_le_a : |‖b‖ - ‖a‖| / ‖a‖ ≤ ‖a - b‖ / ‖a‖ := by gcongr
          have h_le_b : ‖a - b‖ / ‖a‖ ≤ ‖a - b‖ / R := by gcongr
          exact le_trans h_le_a h_le_b
        calc ‖(1 / ‖a‖) • (a - b) + ((1 / ‖a‖) - (1 / ‖b‖)) • b‖
            ≤ ‖(1 / ‖a‖) • (a - b)‖ + ‖((1 / ‖a‖) - (1 / ‖b‖)) • b‖ := norm_add_le _ _
          _ ≤ ‖a - b‖ / R + ‖a - b‖ / R := add_le_add hterm1 hterm2
          _ = 2 * ‖a - b‖ / R := by ring
      calc R * ‖(1 / ‖a‖) • a - (1 / ‖b‖) • b‖
          ≤ R * (2 * ‖a - b‖ / R) := mul_le_mul_of_nonneg_left hunit hRnn
        _ = 2 * ‖a - b‖ := by field_simp
    exact key

/-- The radial retraction is 2-Lipschitz. -/
theorem lipschitzWith_radialRetract {c : X} {R : ℝ≥0} (hR : 0 < R) :
    LipschitzWith 2 (radialRetract c R) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  unfold radialRetract
  have hR' : (0:ℝ) < (R : ℝ) := by exact_mod_cast hR
  -- `‖(c + α•(x-c)) - (c + β•(y-c))‖ = ‖α•(x-c) - β•(y-c)‖`
  have h_eq : (c + ((R : ℝ) / max ‖x - c‖ (R : ℝ)) • (x - c)) -
      (c + ((R : ℝ) / max ‖y - c‖ (R : ℝ)) • (y - c)) =
      ((R : ℝ) / max ‖x - c‖ (R : ℝ)) • (x - c) -
      ((R : ℝ) / max ‖y - c‖ (R : ℝ)) • (y - c) := by abel
  rw [h_eq]
  have h := norm_radialScalar_sub_le hR' (x - c) (y - c)
  have h2 : (x - c) - (y - c) = x - y := by abel
  rw [h2] at h
  calc ‖((R : ℝ) / max ‖x - c‖ ↑R) • (x - c) - ((R : ℝ) / max ‖y - c‖ ↑R) • (y - c)‖
      ≤ 2 * ‖x - y‖ := h
    _ = 2 * ‖x - y‖ := rfl

/-! ## 2. Globally Lipschitz extension of a locally Lipschitz nonlinearity -/

/-- **The retracted nonlinearity.** If `N` is `L`-Lipschitz on `closedBall c R`,
then `Ñ = N ∘ ρ` is globally defined. -/
noncomputable def retractN (N : X → X) (c : X) (R : ℝ≥0) : X → X :=
  N ∘ radialRetract c R

/-- `Ñ` agrees with `N` on the ball. -/
theorem retractN_eq_on_ball {N : X → X} {c : X} {R : ℝ≥0} (hR : 0 < R)
    {x : X} (hx : x ∈ closedBall c (R : ℝ≥0)) :
    retractN N c R x = N x := by
  unfold retractN
  simp only [Function.comp_apply]
  have hmem : ‖x - c‖ ≤ (R : ℝ) := by
    rw [mem_closedBall, dist_eq_norm] at hx
    exact hx
  rw [radialRetract_eq_self hR hmem]

/-- `Ñ` is globally `(2L)`-Lipschitz. -/
theorem lipschitzWith_retractN {N : X → X} {c : X} {R L : ℝ≥0} (hR : 0 < R)
    (hN : LipschitzOnWith L N (closedBall c (R : ℝ≥0))) :
    LipschitzWith (2 * L) (retractN N c R) := by
  have hρ := lipschitzWith_radialRetract (c := c) (R := R) hR
  intro x y
  unfold retractN
  simp only [Function.comp_apply]
  -- Both `ρ x`, `ρ y` are in the ball
  have hxmem : radialRetract c R x ∈ closedBall c (R : ℝ≥0) :=
    radialRetract_mem_closedBall c hR x
  have hymem : radialRetract c R y ∈ closedBall c (R : ℝ≥0) :=
    radialRetract_mem_closedBall c hR y
  -- `edist (N (ρx)) (N (ρy)) ≤ L * edist (ρx) (ρy) ≤ L * (2 * edist x y)`
  have h1 := hN hxmem hymem
  have h2 := hρ x y
  calc edist (N (radialRetract c R x)) (N (radialRetract c R y))
      ≤ (L : ℝ≥0∞) * edist (radialRetract c R x) (radialRetract c R y) := h1
    _ ≤ (L : ℝ≥0∞) * (((2 : ℝ≥0) : ℝ≥0∞) * edist x y) := by gcongr
    _ = (((2 * L : ℝ≥0)) : ℝ≥0∞) * edist x y := by push_cast; ring

/-! ## 3. Local Duhamel existence theorem -/

/-- **Local Duhamel data.** Like `DuhamelData`, but the nonlinearity `N` is only
assumed locally Lipschitz on `closedBall c R`, and `u₀` starts strictly inside. -/
structure LocalDuhamelData where
  T₀ : ℝ
  hT₀ : 0 < T₀
  S : ℝ → X →L[ℝ] X
  hS0 : S 0 = ContinuousLinearMap.id ℝ X
  M : ℝ≥0
  hSbound : ∀ t ∈ Icc (0:ℝ) T₀, ‖S t‖ ≤ (M : ℝ)
  hSjoint : ContinuousOn (fun p : ℝ × X ↦ S p.1 p.2) (Icc (0:ℝ) T₀ ×ˢ univ)
  N : X → X
  c : X
  R : ℝ≥0
  hR : 0 < R
  L : ℝ≥0
  hN : LipschitzOnWith L N (closedBall c (R : ℝ≥0))
  u₀ : X
  hu₀ : dist u₀ c < (R : ℝ)

namespace LocalDuhamelData

variable (D : LocalDuhamelData (X := X))

/-- The `DuhamelData` for the retracted (globally Lipschitz) nonlinearity. -/
noncomputable def toDuhamelData (T : ℝ) (hT : 0 < T) (hle : T ≤ D.T₀) :
    DuhamelData (X := X) where
  T := T
  hT := hT
  S := D.S
  M := D.M
  hSbound := fun t ht => D.hSbound t ⟨ht.1, le_trans ht.2 hle⟩
  hSjoint := by
    apply ContinuousOn.mono D.hSjoint
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true] at hp ⊢
    exact ⟨hp.1, le_trans hp.2 hle⟩
  N := retractN D.N D.c D.R
  L := 2 * D.L
  hN := lipschitzWith_retractN D.hR D.hN
  u₀ := D.u₀

/-- Restriction of a curve from `[0,T₁]` to `[0,T₂]` (for `T₂ ≤ T₁`). -/
noncomputable def restrictCurve (D : LocalDuhamelData (X := X)) {T₁ T₂ : ℝ}
    (hle : T₂ ≤ T₁) (u : C(Icc (0:ℝ) T₁, X)) : C(Icc (0:ℝ) T₂, X) where
  toFun t := u ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩
  continuous_toFun := by
    apply Continuous.comp u.continuous
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- The restriction agrees with the original on `[0,T₂]`. -/
theorem restrictCurve_apply (D : LocalDuhamelData (X := X)) {T₁ T₂ : ℝ}
    (hle : T₂ ≤ T₁) (u : C(Icc (0:ℝ) T₁, X)) (t : Icc (0:ℝ) T₂) :
    D.restrictCurve hle u t = u ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ :=
  rfl

/-- Helper: `t * r ∈ [0,T₂]` for `t ∈ [0,T₂]`, `r ∈ [0,1]`.
(This is `DuhamelData.mul_mem_Icc` for the restricted time.) -/
theorem mul_mem_Icc' {T₂ : ℝ} (hT₂ : 0 ≤ T₂)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T₂) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    t * r ∈ Icc (0:ℝ) T₂ := by
  constructor
  · exact mul_nonneg ht.1 hr.1
  · calc t * r ≤ T₂ * 1 :=
          mul_le_mul ht.2 hr.2 hr.1 hT₂
      _ = T₂ := mul_one _

/-- Key lemma: the Duhamel map is local in time. If `u₁` is a fixed point on
`[0,T₁]`, its restriction to `[0,T₂]` is a fixed point of the `T₂`-Duhamel map. -/
theorem duhamelMap_restrict {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hle : T₂ ≤ T₁) (hle1 : T₁ ≤ D.T₀)
    (u₁ : C(Icc (0:ℝ) T₁, X))
    (hfix : (D.toDuhamelData T₁ hT₁ hle1).duhamelMap u₁ = u₁) :
    (D.toDuhamelData T₂ hT₂ (le_trans hle hle1)).duhamelMap
      (D.restrictCurve hle u₁) = D.restrictCurve hle u₁ := by
  apply ContinuousMap.ext
  intro t
  have hle2 : T₂ ≤ D.T₀ := le_trans hle hle1
  -- The integrands agree because both Duhamel maps use the same S, Ñ, u₀,
  -- and the curves agree on [0,T₂].
  have h_eq_integrand : ∀ r : ℝ,
      (D.toDuhamelData T₂ hT₂ hle2).duhamelIntegrand (D.restrictCurve hle u₁) t r =
      (D.toDuhamelData T₁ hT₁ hle1).duhamelIntegrand u₁
        ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ r := by
    intro r
    unfold DuhamelData.duhamelIntegrand
    by_cases hr : r ∈ Icc (0:ℝ) 1
    · rw [dif_pos hr, dif_pos hr]
      unfold DuhamelData.duhamelIntegrandSub LocalDuhamelData.toDuhamelData
        LocalDuhamelData.restrictCurve
      rfl
    · rw [dif_neg hr, dif_neg hr]
  have h_integral : (D.toDuhamelData T₂ hT₂ hle2).duhamelIntegral
        (D.restrictCurve hle u₁) t =
      (D.toDuhamelData T₁ hT₁ hle1).duhamelIntegral u₁
        ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ := by
    unfold DuhamelData.duhamelIntegral
    apply intervalIntegral.integral_congr
    intro r _
    exact h_eq_integrand r
  -- Unfold both Duhamel maps (keeping toDuhamelData folded) and use the integral agreement
  -- The Duhamel map applied at t is definitionally S(t)u₀ + t • integral
  have hLHS : ((D.toDuhamelData T₂ hT₂ hle2).duhamelMap (D.restrictCurve hle u₁)) t =
      D.S t.val D.u₀ + t.val •
        (D.toDuhamelData T₂ hT₂ hle2).duhamelIntegral (D.restrictCurve hle u₁) t := rfl
  have hRHS : (D.restrictCurve hle u₁) t =
      u₁ ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ :=
    D.restrictCurve_apply hle u₁ t
  rw [hLHS, h_integral]
  have hfix_t := ContinuousMap.congr_fun hfix
    ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩
  have hfix_t' : D.S t.val D.u₀ + t.val •
        (D.toDuhamelData T₁ hT₁ hle1).duhamelIntegral u₁
          ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ =
      u₁ ⟨t.val, ⟨t.property.1, le_trans t.property.2 hle⟩⟩ := hfix_t
  exact hfix_t'.trans hRHS.symm

/-- The solution at time 0 equals the initial data. -/
theorem fixedPoint_at_zero {T : ℝ} (hT : 0 < T) (hle : T ≤ D.T₀)
    (u : C(Icc (0:ℝ) T, X))
    (hfix : (D.toDuhamelData T hT hle).duhamelMap u = u) :
    u ⟨0, ⟨le_refl (0:ℝ), hT.le⟩⟩ = D.u₀ := by
  have h := ContinuousMap.congr_fun hfix ⟨0, ⟨le_refl (0:ℝ), hT.le⟩⟩
  -- Unfold: duhamelMap u at 0 = S(0)u₀ + 0 • integral = u₀
  have hS : (D.toDuhamelData T hT hle).S = D.S := rfl
  have hu₀ : (D.toDuhamelData T hT hle).u₀ = D.u₀ := rfl
  have h0 : ((D.toDuhamelData T hT hle).duhamelMap u) ⟨0, ⟨le_refl (0:ℝ), hT.le⟩⟩ =
      D.u₀ := by
    -- By definition: duhamelMap u at 0 = S(0)u₀ + 0 • integral
    have hdef : ((D.toDuhamelData T hT hle).duhamelMap u) ⟨0, ⟨le_refl (0:ℝ), hT.le⟩⟩ =
        D.S 0 D.u₀ + (0:ℝ) • (D.toDuhamelData T hT hle).duhamelIntegral u
          ⟨0, ⟨le_refl (0:ℝ), hT.le⟩⟩ := rfl
    rw [hdef, D.hS0]
    simp
  rw [h0] at h
  exact h.symm

/-- **Local Duhamel existence theorem.** For locally Lipschitz `N`, there exists
`T > 0` and a mild solution `u` on `[0,T]` that stays in `ball c R`
(where the retracted nonlinearity agrees with `N`). -/
theorem exists_local_mild_solution :
    ∃ (T : ℝ) (hT : 0 < T) (hle : T ≤ D.T₀),
      ∃ u : C(Icc (0:ℝ) T, X),
        (D.toDuhamelData T hT hle).duhamelMap u = u ∧
        ∀ t : Icc (0:ℝ) T, dist (u t) D.c < (D.R : ℝ) := by
  -- Step 1: Choose T₁ with contraction
  set K : ℝ := (D.M : ℝ) * (2 * (D.L : ℝ)) with hK
  have hK_nonneg : 0 ≤ K := by
    apply mul_nonneg
    · exact NNReal.coe_nonneg D.M
    · apply mul_nonneg (by norm_num)
      exact NNReal.coe_nonneg D.L
  -- T₁ = min (T₀/2) (1/(2*K+1)) ensures 0 < T₁ ≤ T₀ and K*T₁ < 1
  set T₁ : ℝ := min (D.T₀ / 2) (1 / (2 * K + 1)) with hT₁
  have hT₁_pos : 0 < T₁ := by
    apply lt_min
    · linarith [D.hT₀]
    · apply div_pos (by norm_num)
      linarith
  have hT₁_le : T₁ ≤ D.T₀ := by
    calc T₁ ≤ D.T₀ / 2 := min_le_left _ _
      _ ≤ D.T₀ := by linarith [D.hT₀]
  have hcontract : K * T₁ < 1 := by
    have h1 : T₁ ≤ 1 / (2 * K + 1) := min_le_right _ _
    have h2 : (0:ℝ) < 2 * K + 1 := by linarith
    calc K * T₁ ≤ K * (1 / (2 * K + 1)) := by
            apply mul_le_mul_of_nonneg_left h1 hK_nonneg
        _ < 1 := by
            rw [div_eq_mul_inv, ← mul_assoc]
            have : K * (2 * K + 1)⁻¹ < 1 := by
              rw [mul_inv_lt_iff₀ h2]
              linarith
            linarith
  -- Step 2: Get u₁ from global theorem
  have hMLT : ((D.toDuhamelData T₁ hT₁_pos hT₁_le).M *
      (D.toDuhamelData T₁ hT₁_pos hT₁_le).L * T₁ : ℝ) < 1 := by
    have hM : ((D.toDuhamelData T₁ hT₁_pos hT₁_le).M : ℝ) = (D.M : ℝ) := rfl
    have hL : ((D.toDuhamelData T₁ hT₁_pos hT₁_le).L : ℝ) = 2 * (D.L : ℝ) := by
      simp [LocalDuhamelData.toDuhamelData, NNReal.coe_mul]
    have h_eq : ((D.toDuhamelData T₁ hT₁_pos hT₁_le).M *
        (D.toDuhamelData T₁ hT₁_pos hT₁_le).L * T₁ : ℝ) = K * T₁ := by
      rw [hM, hL, hK]
    rw [h_eq]
    exact hcontract
  obtain ⟨u₁, hu₁_fix, hu₁_unique⟩ :=
    DuhamelData.exists_unique_mild_solution
      (D := D.toDuhamelData T₁ hT₁_pos hT₁_le) hMLT
  -- Step 3: u₁(0) = u₀ ∈ ball c R
  have hu₁0 : u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩ = D.u₀ :=
    D.fixedPoint_at_zero hT₁_pos hT₁_le u₁ hu₁_fix
  have hmem0 : dist (u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩) D.c < (D.R : ℝ) := by
    rw [hu₁0]
    exact D.hu₀
  -- Step 4: Find T₂ where u₁ stays in ball c R, by continuity at 0
  -- The function t ↦ dist (u₁ t) c is continuous and < R at 0
  have hcont : Continuous (fun t : Icc (0:ℝ) T₁ ↦ dist (u₁ t) D.c) :=
    (continuous_id.dist continuous_const).comp u₁.continuous
  rw [Metric.continuous_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩
    (((D.R : ℝ) - dist (u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩) D.c) / 2)
    (by linarith [hmem0])
  -- T₂ = min T₁ (δ/2)
  set T₂ : ℝ := min T₁ (δ / 2) with hT₂
  have hT₂_pos : 0 < T₂ := lt_min hT₁_pos (by linarith)
  have hT₂_le : T₂ ≤ T₁ := min_le_left _ _
  have hT₂_le0 : T₂ ≤ D.T₀ := le_trans hT₂_le hT₁_le
  -- For t ∈ [0,T₂], dist (u₁ ⟨t,_⟩) c < R
  have hstay : ∀ t : Icc (0:ℝ) T₂,
      dist (u₁ ⟨t.val, ⟨t.property.1, le_trans t.property.2 hT₂_le⟩⟩) D.c < (D.R : ℝ) := by
    intro t
    have hdist : dist (⟨t.val, ⟨t.property.1, le_trans t.property.2 hT₂_le⟩⟩ : Icc (0:ℝ) T₁)
        ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩ < δ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      have h1 : ‖t.val - (0:ℝ)‖ = t.val := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      rw [h1]
      calc t.val ≤ T₂ := t.property.2
        _ ≤ δ / 2 := min_le_right _ _
        _ < δ := by linarith
    have h := hδ _ hdist
    rw [Real.dist_eq] at h
    -- h : |dist (u₁ x) c - dist (u₁ 0) c| < (R - dist (u₁ 0) c)/2
    have h_lt : dist (u₁ ⟨t.val, ⟨t.property.1, le_trans t.property.2 hT₂_le⟩⟩) D.c -
        dist (u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩) D.c <
        ((D.R:ℝ) - dist (u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩) D.c)/2 :=
      (abs_lt.mp h).2
    -- Therefore dist (u₁ x) c < (R + dist (u₁ 0) c)/2 < R
    have h_R : (dist (u₁ ⟨0, ⟨le_refl (0:ℝ), hT₁_pos.le⟩⟩) D.c + (D.R:ℝ))/2 < (D.R:ℝ) := by
      linarith [hmem0]
    linarith
  -- Step 5: Restrict u₁ to [0,T₂], get u₂ which is a fixed point
  set u₂ : C(Icc (0:ℝ) T₂, X) := D.restrictCurve hT₂_le u₁ with hu₂
  have hu₂_fix : (D.toDuhamelData T₂ hT₂_pos hT₂_le0).duhamelMap u₂ = u₂ :=
    D.duhamelMap_restrict hT₁_pos hT₂_pos hT₂_le hT₁_le u₁ hu₁_fix
  -- Step 6: u₂ stays in ball c R
  have hu₂_stay : ∀ t : Icc (0:ℝ) T₂, dist (u₂ t) D.c < (D.R : ℝ) := by
    intro t
    have : u₂ t = u₁ ⟨t.val, ⟨t.property.1, le_trans t.property.2 hT₂_le⟩⟩ := rfl
    rw [this]
    exact hstay t
  exact ⟨T₂, hT₂_pos, hT₂_le0, u₂, hu₂_fix, hu₂_stay⟩

end LocalDuhamelData

end AnalyticPDE
end RicciFlow
