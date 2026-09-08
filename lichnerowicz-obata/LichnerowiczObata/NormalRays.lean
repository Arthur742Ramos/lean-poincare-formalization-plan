module

public import LichnerowiczObata.NormalMetricLimit

/-! # Chain rules for rays in a normal coordinate map -/

@[expose] public noncomputable section

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time velocity of a ray in a differentiable normal map. -/
theorem hasDerivAt_normal_ray {F : E → E} {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) :
    HasDerivAt (fun r : ℝ => F (r • u)) (fderiv ℝ F (s • u) u) s := by
  have hi : HasDerivAt (fun r : ℝ => r • u) u s := by
    convert (hasDerivAt_id s).smul_const u using 1 <;> simp
  exact hF.hasFDerivAt.comp_hasDerivAt s hi

/-- Spatial variations of the ray family carry one factor of the ray parameter. -/
theorem fderiv_normal_ray_spatial {F : E → E} {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (w : E) :
    fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (w, 0) =
      s • fderiv ℝ F (s • u) w := by
  have hi := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, s))).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, s)))
  have hd := hF.hasFDerivAt.comp (u, s) hi
  have he := congrArg (fun L : E × ℝ →L[ℝ] E => L (w, 0)) hd.fderiv
  simpa [Function.comp_def] using he

/-- The metric of spatial ray variations is parameter squared times the
normal-map pullback metric. This includes zero parameter. -/
theorem normal_ray_spatial_metric {F : E → E}
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (w v : E) :
    g (F (s • u))
      (fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (w, 0))
      (fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (v, 0)) =
    s ^ 2 * g (F (s • u)) (fderiv ℝ F (s • u) w) (fderiv ℝ F (s • u) v) := by
  rw [fderiv_normal_ray_spatial hF, fderiv_normal_ray_spatial hF]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- A radial derivative identity becomes the constant-speed ray equation
after cancelling the nonzero ray parameter. -/
theorem hasDerivAt_normal_ray_of_radial {F : E → E} {u N : E} {s σ : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (hs : s ≠ 0)
    (hrad : fderiv ℝ F (s • u) (s • u) = (s * σ) • N) :
    HasDerivAt (fun r : ℝ => F (r • u)) (σ • N) s := by
  have he : fderiv ℝ F (s • u) u = σ • N := by
    apply (smul_right_injective E hs)
    simpa only [map_smul, mul_smul] using hrad
  simpa only [he] using hasDerivAt_normal_ray hF

end LichnerowiczObata
