module

public import LichnerowiczObata.RoundPolarCoordinates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Recovering polar data from a point away from the poles -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Off the two poles, the height of a unit sphere point is strictly
between minus one and one. -/
theorem unit_sphere_height_strict (p y : E) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1)
    (hn : y ≠ p) (hs : y ≠ -p) : -1 < inner ℝ p y ∧ inner ℝ p y < 1 := by
  have hsub := norm_sub_sq_real y p
  have hadd := norm_add_sq_real y p
  rw [hy, hp, real_inner_comm p y] at hsub hadd
  have hsubpos : 0 < ‖y - p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  have haddne : y + p ≠ 0 := by
    intro he
    exact hs (eq_neg_of_add_eq_zero_left he)
  have haddpos : 0 < ‖y + p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr haddne)
  constructor <;> nlinarith

/-- An explicit angular direction and arccosine angle reconstruct every
non-polar unit sphere point. -/
theorem unit_sphere_polar_decomposition (p y : E) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1)
    (hn : y ≠ p) (hs : y ≠ -p) :
    ∃ q : E, ‖q‖ = 1 ∧ inner ℝ p q = 0 ∧
      Real.arccos (inner ℝ p y) ∈ Set.Ioo 0 Real.pi ∧
      y = Real.cos (Real.arccos (inner ℝ p y)) • p +
        Real.sin (Real.arccos (inner ℝ p y)) • q := by
  let c := inner ℝ p y
  let θ := Real.arccos c
  let v := y - c • p
  have hc := unit_sphere_height_strict p y hp hy hn hs
  have hθ : θ ∈ Set.Ioo 0 Real.pi :=
    ⟨Real.arccos_pos.mpr hc.2, Real.arccos_lt_pi.mpr hc.1⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcos : Real.cos θ = c := Real.cos_arccos hc.1.le hc.2.le
  have hperp : inner ℝ p v = 0 := by
    simp [v, inner_sub_right, real_inner_smul_right, hp, c]
  have hnorm : ‖v‖ ^ 2 = 1 - c ^ 2 := by
    dsimp only [v]
    rw [norm_sub_sq_real]
    simp only [hy, norm_smul, Real.norm_eq_abs, hp, mul_one, sq_abs,
      real_inner_smul_right]
    rw [real_inner_comm p y]
    dsimp only [c]
    ring
  have hvnorm : ‖v‖ = Real.sin θ := by
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    nlinarith [norm_nonneg v]
  refine ⟨(Real.sin θ)⁻¹ • v, ?_, ?_, hθ, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsin), hvnorm]
    exact inv_mul_cancel₀ hsin.ne'
  · rw [real_inner_smul_right, hperp, mul_zero]
  · change y = Real.cos θ • p + Real.sin θ • ((Real.sin θ)⁻¹ • v)
    rw [hcos, smul_smul, mul_inv_cancel₀ hsin.ne', one_smul]
    dsimp only [v]
    abel

/-- Every actual sphere point other than the two poles has polar coordinates. -/
theorem roundPolarMap_surjective_off_poles {R : ℝ} (hR : 0 < R) (p : E)
    (hp : ‖p‖ = 1) (x : Metric.sphere (0 : E) R)
    (hn : (x : E) ≠ R • p) (hs : (x : E) ≠ -(R • p)) :
    ∃ a, roundPolarMap hR p hp a = x := by
  let y : E := R⁻¹ • (x : E)
  have hxnorm : ‖(x : E)‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖y‖ = 1 := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hxnorm]
    exact inv_mul_cancel₀ hR.ne'
  have hscale : R • y = (x : E) := by
    simp only [y, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hyn : y ≠ p := by
    intro he
    exact hn (by rw [← hscale, he])
  have hys : y ≠ -p := by
    intro he
    exact hs (by rw [← hscale, he, smul_neg])
  obtain ⟨q, hq, hpq, hθ, he⟩ := unit_sphere_polar_decomposition p y hp hy hyn hys
  let θ := Real.arccos (inner ℝ p y)
  have hrange : R * θ ∈ Set.Ioo 0 (Real.pi * R) := by
    exact ⟨mul_pos hR hθ.1, by nlinarith [hθ.2]⟩
  refine ⟨(⟨q, hq, hpq⟩, ⟨R * θ, hrange⟩), ?_⟩
  apply Subtype.ext
  change roundPolarCurve R p q (R * θ) = (x : E)
  have harg : R * θ / R = θ := by field_simp
  rw [roundPolarCurve, harg, ← he]
  exact hscale

end LichnerowiczObata
