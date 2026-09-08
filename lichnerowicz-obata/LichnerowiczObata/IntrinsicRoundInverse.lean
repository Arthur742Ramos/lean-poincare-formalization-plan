module

public import LichnerowiczObata.RoundAmbientDirections
public import LichnerowiczObata.RoundPolarInverseSmooth

/-! # Smooth inverse round coordinates in intrinsic angular variables -/

@[expose] public noncomputable section
open scoped ContDiff Manifold
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

def intrinsicRoundInverseCoordinates (R : ℝ) (x : RoundAmbient P) : P × ℝ :=
  ((WithLp.ofLp (roundInverseCoordinates R roundNorth x).1).1,
    (roundInverseCoordinates R roundNorth x).2)

theorem intrinsicRoundInverseCoordinates_apply {K : ℝ} (hK : 0 < K)
    (q : Metric.sphere (0 : P) 1 × Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt K)) :
    intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
      ((curvatureRoundPolarHomeomorph hK q).1 : RoundAmbient P) = ((q.1 : P), (q.2 : ℝ)) := by
  let hR := one_div_pos.mpr (Real.sqrt_pos.mpr hK)
  let qR : RoundPolarDirections (roundNorth : RoundAmbient P) ×
      Set.Ioo (0 : ℝ) (Real.pi * (1 / Real.sqrt K)) :=
    (roundAngularHomeomorph q.1, ⟨q.2, by simpa only [mul_one_div] using q.2.property⟩)
  have hx : curvatureRoundPolarHomeomorph hK q =
      roundPolarEquiv hR roundNorth roundNorth_norm qR := rfl
  have hh := roundInverseCoordinates_eq_inverse hR
    (roundNorth : RoundAmbient P) roundNorth_norm (curvatureRoundPolarHomeomorph hK q)
  rw [hx, Equiv.symm_apply_apply] at hh
  unfold intrinsicRoundInverseCoordinates
  rw [hx, hh]
  rfl

theorem intrinsicRoundInverseCoordinates_eq_inverse {K : ℝ} (hK : 0 < K)
    (x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P)) :
    intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P) =
      ((((curvatureRoundPolarHomeomorph hK).symm x).1 : P),
        (((curvatureRoundPolarHomeomorph hK).symm x).2 : ℝ)) := by
  obtain ⟨q, rfl⟩ := (curvatureRoundPolarHomeomorph hK).surjective x
  rw [Homeomorph.symm_apply_apply]
  exact intrinsicRoundInverseCoordinates_apply hK q

theorem contDiffAt_intrinsicRoundInverseCoordinates {K : ℝ} (hK : 0 < K)
    (x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P)) :
    ContDiffAt ℝ ∞ (intrinsicRoundInverseCoordinates (P := P) (1 / Real.sqrt K))
      (x.1 : RoundAmbient P) := by
  let A : RoundAmbient P × ℝ →L[ℝ] P × ℝ :=
    (WithLp.fstL 2 ℝ P ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hi := contDiffAt_roundInverseCoordinates
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK)) (roundNorth : RoundAmbient P) roundNorth_norm x
  exact A.contDiff.contDiffAt.comp (x.1 : RoundAmbient P) hi

end LichnerowiczObata
