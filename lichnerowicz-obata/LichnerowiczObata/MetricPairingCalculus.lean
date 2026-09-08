module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

/-! # Differentiation of a moving metric pairing -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All three derivative terms of a varying bilinear pairing. -/
theorem hasDerivAt_moving_metric_pairing
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t : ℝ}
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => g s (u s) (w s))
      (g' (u t) (w t) + g t u' (w t) + g t (u t) w') t := by
  convert (hg.clm_apply hu).clm_apply hw using 1 <;> rfl

/-- For a metric connection, its two coefficient terms combine with the
ordinary derivatives to give the two covariant variation terms. -/
theorem hasDerivAt_metric_pairing_connection
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t : ℝ} (A : E →L[ℝ] E)
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hcompat : g' (u t) (w t) = g t (A (u t)) (w t) + g t (u t) (A (w t))) :
    HasDerivAt (fun s => g s (u s) (w s))
      (g t (u' + A (u t)) (w t) + g t (u t) (w' + A (w t))) t := by
  convert hasDerivAt_moving_metric_pairing hg hu hw using 1
  simp only [map_add, add_apply, hcompat]
  ring

/-- Equal scalar covariant evolution of two variations gives the scalar
metric evolution equation. The geometric identities must be supplied by
the actual metric connection and shape operator. -/
theorem hasDerivAt_metric_pairing_scaling
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t c : ℝ} (A : E →L[ℝ] E)
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hcompat : g' (u t) (w t) = g t (A (u t)) (w t) + g t (u t) (A (w t)))
    (hshapeU : u' + A (u t) = c • u t) (hshapeW : w' + A (w t) = c • w t) :
    HasDerivAt (fun s => g s (u s) (w s)) (2 * c * g t (u t) (w t)) t := by
  convert hasDerivAt_metric_pairing_connection A hg hu hw hcompat using 1
  rw [hshapeU, hshapeW]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end LichnerowiczObata
