import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalizedCoefficientScaling

/-!
# Quantitative smooth normalized cutoffs

The manifold bump-function construction is augmented with the three concrete
bounds used by normalized parabolic localization: `|χ| ≤ 1`, a global
Lipschitz constant, and a radius containing the support.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

/-- Quantitative data attached to a smooth compactly supported cutoff on a
finite-dimensional real normed space. -/
structure NormalizedCutoffControl (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  cutoff : X → ℝ
  lipschitzBound : ℝ
  supportRadius : ℝ
  contDiff_three : ContDiff ℝ 3 cutoff
  compactSupport : HasCompactSupport cutoff
  lipschitzBound_nonneg : 0 ≤ lipschitzBound
  supportRadius_pos : 0 < supportRadius
  abs_le_one : ∀ x, |cutoff x| ≤ 1
  norm_sub_le : ∀ x y,
    ‖cutoff x - cutoff y‖ ≤ lipschitzBound * dist x y
  support_norm_le : ∀ x, cutoff x ≠ 0 → ‖x‖ ≤ supportRadius

namespace NormalizedCutoffControl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem supportRadius_nonneg (χ : NormalizedCutoffControl X) :
    0 ≤ χ.supportRadius := χ.supportRadius_pos.le

theorem abs_sub_le (χ : NormalizedCutoffControl X) (x y : X) :
    |χ.cutoff x - χ.cutoff y| ≤ χ.lipschitzBound * dist x y := by
  simpa [Real.norm_eq_abs] using χ.norm_sub_le x y

end NormalizedCutoffControl

/-- A compact set inside an open set admits a smooth normalized cutoff with
all quantitative constants required by coefficient scaling.  It equals one
on a neighborhood of the compact set and its support stays inside the given
open set. -/
theorem exists_normalizedCutoffControl_one_nhdsSet_of_isCompact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : NormalizedCutoffControl X,
      tsupport χ.cutoff ⊆ U ∧
      (∀ᶠ x in nhdsSet K, χ.cutoff x = 1) ∧
      ∀ x, χ.cutoff x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hf, hfc, hfsupp, hfOne, hfIcc⟩ :=
    SmoothDependenceCk.exists_contDiff_cutoff_one_nhdsSet_of_isCompact
      (n := 3) hK hU hKU
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨L, hL0, hL⟩ :=
    exists_nonneg_lipschitz_bound_of_contDiff_one_hasCompactSupport hf1 hfc
  obtain ⟨R, hR, hRsupp⟩ :=
    exists_pos_support_radius_of_hasCompactSupport hfc
  let χ : NormalizedCutoffControl X :=
    { cutoff := f
      lipschitzBound := L
      supportRadius := R
      contDiff_three := hf
      compactSupport := hfc
      lipschitzBound_nonneg := hL0
      supportRadius_pos := hR
      abs_le_one := fun x => by
        rw [abs_of_nonneg (hfIcc x).1]
        exact (hfIcc x).2
      norm_sub_le := hL
      support_norm_le := hRsupp }
  exact ⟨χ, hfsupp, hfOne, hfIcc⟩

end AnalyticPDE
end RicciFlow
