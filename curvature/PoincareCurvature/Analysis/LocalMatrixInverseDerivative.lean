/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.MatrixInverseDerivative

/-!
# Local derivative of the actual nonsingular matrix inverse

The globally nonsingular curve theorem is localized at an invertible value.
Continuity of the determinant supplies a neighborhood of invertibility. Outside
that neighborhood, replace the curve by its value at the selected time. The
resulting globally nonsingular curve agrees locally with the actual curve, so
ordinary derivative congruence transfers the already proved inverse formula.
-/

noncomputable section

open Filter Matrix
open scoped Topology

namespace PoincareCurvature

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual matrix inverse derivative needs invertibility only at the
selected time. No inverse derivative or global invertibility is assumed. -/
theorem hasDerivAt_nonsing_inv_entry_of_det_ne_zero
    {A : ℝ → Matrix ι ι ℝ} {Adot : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (Adot i j) t)
    (hdet : (A t).det ≠ 0) (i j : ι) :
    HasDerivAt (fun s => ((A s : Matrix ι ι ℝ)⁻¹) i j)
      ((-((A t : Matrix ι ι ℝ)⁻¹ * Adot * (A t : Matrix ι ι ℝ)⁻¹) :
        Matrix ι ι ℝ) i j) t := by
  have hentries : DifferentiableAt ℝ (fun s => fun k l => A s k l) t :=
    differentiableAt_pi'' fun k => differentiableAt_pi'' fun l =>
      (hA k l).differentiableAt
  have hdetcont : ContinuousAt (fun s => (A s).det) t :=
    (((MatrixSmoothness.contDiff_det (ι := ι) (n := 1)).differentiable
      (by norm_num) (A t)).comp t hentries).continuousAt
  have hnear : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 := hdetcont.eventually_ne hdet
  let B : ℝ → Matrix ι ι ℝ := fun s => if (A s).det ≠ 0 then A s else A t
  have heq : B =ᶠ[𝓝 t] A := by
    filter_upwards [hnear] with s hs
    simp only [B, if_pos hs]
  have hB : ∀ k l, HasDerivAt (fun s => B s k l) (Adot k l) t := by
    intro k l
    exact (hA k l).congr_of_eventuallyEq (heq.mono fun _ hs => congrArg (fun C => C k l) hs)
  have hBdet : ∀ s, (B s).det ≠ 0 := by
    intro s
    by_cases hs : (A s).det ≠ 0
    · simpa only [B, if_pos hs] using hs
    · simpa only [B, if_neg hs] using hdet
  have hBinv := hasDerivAt_nonsing_inv_entry hB hBdet i j
  have heqInv : (fun s => ((A s : Matrix ι ι ℝ)⁻¹) i j) =ᶠ[𝓝 t]
      (fun s => ((B s : Matrix ι ι ℝ)⁻¹) i j) := by
    filter_upwards [heq] with s hs
    rw [hs]
  simpa only [B, if_pos hdet] using hBinv.congr_of_eventuallyEq heqInv

end PoincareCurvature
