/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixConnection
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateJetPrincipalRemainder

/-!
# Actual inverse and Christoffel derivatives discharge the coordinate jet formulas

The old algebraic inverse and Christoffel derivative expressions are identified
here with genuine derivatives of the actual C² coordinate field. Metric
invertibility is required only at the selected point. This establishes the
coordinate differentiation bridge without claiming a manifold Levi--Civita or
Ricci/Lie-derivative identification or a quasilinear PDE solution.
-/

noncomputable section

open Matrix PoincareCurvature.CoordinateMatrixJet

namespace RicciFlow.AnalyticPDE.GenuinePhiRD

variable {d : ℕ} {g : (Fin d → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- The actual jet inverse is the genuine nonsingular coordinate matrix inverse. -/
theorem invMetricOfJet_coordinateJet_eq_inverse (i k : Fin d) :
    invMetricOfJet (coordinateJet g x) i k = inverse g x i k := by
  simp only [invMetricOfJet, coordinateJet, inverse, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

/-- The existing algebraic inverse derivative equals the actual computed
coordinate inverse derivative, rather than serving as its assumption. -/
theorem derivInvMetricOfJet_coordinateJet_eq_inverseFirst (m i k : Fin d) :
    derivInvMetricOfJet (coordinateJet g x) m i k = inverseFirst g x m i k := by
  rw [inverseFirst_eq_sum]
  simp only [derivInvMetricOfJet, invMetricOfJet_coordinateJet_eq_inverse,
    deriv1Comp, coordinateJet_deriv1]

/-- Actual Fréchet differentiation produces the legacy finite-jet inverse formula. -/
theorem fderiv_invMetricOfJet_coordinateJet_apply
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (m i k : Fin d) :
    fderiv ℝ (fun y => invMetricOfJet (coordinateJet g y) i k) x (coordinateVector m) =
      derivInvMetricOfJet (coordinateJet g x) m i k := by
  simp_rw [invMetricOfJet_coordinateJet_eq_inverse]
  rw [fderiv_inverse_apply hU hg hx hdet]
  exact (derivInvMetricOfJet_coordinateJet_eq_inverseFirst m i k).symm

/-- The finite-jet Christoffel expression is the actual coordinate metric expression. -/
theorem christoffelOfJet_coordinateJet_eq_christoffel (k i j : Fin d) :
    christoffelOfJet (coordinateJet g x) k i j = christoffel g x k i j := by
  simp only [christoffelOfJet, christoffel, invMetricOfJet_coordinateJet_eq_inverse,
    deriv1Comp, coordinateJet_deriv1]

/-- Identification of the old algebraic Christoffel derivative with the produced
coordinate product-rule expression. -/
theorem derivChristoffelOfJet_coordinateJet_eq_christoffelFirst (m k i j : Fin d) :
    derivChristoffelOfJet (coordinateJet g x) m k i j = christoffelFirst g x m k i j := by
  simp only [derivChristoffelOfJet, christoffelFirst,
    derivInvMetricOfJet_coordinateJet_eq_inverseFirst,
    invMetricOfJet_coordinateJet_eq_inverse, deriv1Comp, deriv2Comp,
    coordinateJet_deriv1, coordinateJet_deriv2]

/-- Actual Fréchet differentiation produces the finite-jet Christoffel formula. -/
theorem fderiv_christoffelOfJet_coordinateJet_apply
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (m k i j : Fin d) :
    fderiv ℝ (fun y => christoffelOfJet (coordinateJet g y) k i j) x (coordinateVector m) =
      derivChristoffelOfJet (coordinateJet g x) m k i j := by
  simp_rw [christoffelOfJet_coordinateJet_eq_christoffel]
  rw [fderiv_christoffel_apply hU hg hx hdet]
  exact (derivChristoffelOfJet_coordinateJet_eq_christoffelFirst m k i j).symm

end RicciFlow.AnalyticPDE.GenuinePhiRD
