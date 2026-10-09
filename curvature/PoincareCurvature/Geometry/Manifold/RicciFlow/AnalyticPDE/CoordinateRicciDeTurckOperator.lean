/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixOperator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateJetConnectionDerivative

/-!
# Corrected spatial-operator identity for actual coordinate fields

The coordinate Ricci/Lie readouts use actual component Fréchet derivatives.
The varying background first jet is produced directly from its component
Fréchet differential. These identities connect the genuine coordinate operator
to the corrected algebraic jet RHS and its principal/frozen-remainder split.
No manifold curvature, tensor heat-generator, or PDE identification is claimed.
-/

noncomputable section

open Matrix PoincareCurvature.CoordinateMatrixJet

namespace RicciFlow.AnalyticPDE.GenuinePhiRD

variable {d : ℕ} {g : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    {B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- The actual positive vector equals its produced-jet value. -/
theorem deTurck_eq_coordinateJet (k : Fin d) :
    deTurck g B x k = deTurckVectorOfJet (B x) (coordinateJet g x) k := by
  simp only [deTurck, deTurckVectorOfJet, invMetricOfJet_coordinateJet_eq_inverse,
    christoffelOfJet_coordinateJet_eq_christoffel]

/-- Actual differentiation produces the corrected, varying-background jet formula. -/
theorem deTurckFirst_eq_coordinateJet
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (m k : Fin d) :
    deTurckFirst g B x m k = derivDeTurckVectorWithBackgroundJetOfJet
      (B x) (backgroundFirst B x) (coordinateJet g x) m k := by
  rw [deTurckFirst_eq_productRule hU hg hB hx hdet]
  unfold derivDeTurckVectorWithBackgroundJetOfJet derivDeTurckVectorOfJet
  simp only [derivInvMetricOfJet_coordinateJet_eq_inverseFirst,
    invMetricOfJet_coordinateJet_eq_inverse, christoffelOfJet_coordinateJet_eq_christoffel,
    derivChristoffelOfJet_coordinateJet_eq_christoffelFirst,
    mul_sub, ← add_sub_assoc, Finset.sum_sub_distrib]

/-- The actual Christoffel differentials give the finite-jet coordinate Ricci formula. -/
theorem coordinateRicci_eq_coordinateJet
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i j : Fin d) :
    coordinateRicci g x i j = ricciOfJet (coordinateJet g x) i j := by
  simp only [coordinateRicci, ricciOfJet, fderiv_christoffel_apply hU hg hx hdet,
    derivChristoffelOfJet_coordinateJet_eq_christoffelFirst,
    christoffelOfJet_coordinateJet_eq_christoffel]

/-- All three actual coordinate Lie contributions equal the corrected jet formula. -/
theorem coordinateLie_eq_coordinateJet
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (i j : Fin d) :
    coordinateLie g B x i j = deTurckCorrectionWithBackgroundJetOfJet
      (B x) (backgroundFirst B x) (coordinateJet g x) i j := by
  simp only [coordinateLie, deTurckCorrectionWithBackgroundJetOfJet,
    deTurckFirst_eq_coordinateJet hU hg hB hx hdet, deTurck_eq_coordinateJet,
    valComp, deriv1Comp, coordinateJet_val, coordinateJet_deriv1]

/-- Complete corrected coordinate spatial-operator identity, without a derivative oracle. -/
theorem coordinateRD_eq_correctedJet
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (i j : Fin d) :
    coordinateRD g B x i j = phiRDWithBackgroundJetOfJet
      (B x) (backgroundFirst B x) (coordinateJet g x) i j := by
  rw [coordinateRD, phiRDWithBackgroundJetOfJet,
    coordinateRicci_eq_coordinateJet hU hg hx hdet,
    coordinateLie_eq_coordinateJet hU hg hB hx hdet]

/-- The actual symmetric C² coordinate operator has the inverse-metric principal part. -/
theorem coordinateRD_eq_principal_add_lowerOrder
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i j : Fin d) :
    coordinateRD g B x i j =
      (∑ p : Fin d, ∑ q : Fin d, inverse g x p q * second g x p q i j) +
        lowerOrderRDWithBackgroundJetOfJet (B x) (backgroundFirst B x)
          (coordinateJet g x) i j := by
  rw [coordinateRD_eq_correctedJet hU hg hB hx hdet]
  simpa only [jetPrincipalContraction, invMetricOfJet_coordinateJet_eq_inverse,
    coordinateJet_deriv2] using
    phiRDWithBackgroundJet_coordinateJet_eq_principal_add_lowerOrder
      (B x) (backgroundFirst B x) hU hg hx hsymm hdet i j

/-- Freeze at arbitrary A, retaining the actual quasilinear Hessian coefficient error.
Identifying A with a tensor heat generator remains a separate obligation. -/
theorem coordinateRD_eq_frozenPrincipal_add_remainder
    (A : Fin d → Fin d → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hsymm : ∀ y ∈ U, ∀ i j : Fin d, g y i j = g y j i)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i j : Fin d) :
    coordinateRD g B x i j = (∑ p : Fin d, ∑ q : Fin d, A p q * second g x p q i j) +
      ((∑ p : Fin d, ∑ q : Fin d, (inverse g x p q - A p q) * second g x p q i j) +
        lowerOrderRDWithBackgroundJetOfJet (B x) (backgroundFirst B x)
          (coordinateJet g x) i j) := by
  rw [coordinateRD_eq_correctedJet hU hg hB hx hdet]
  simpa only [frozenCoefficientRemainderOfJet, jetPrincipalContraction,
    invMetricOfJet_coordinateJet_eq_inverse, coordinateJet_deriv2] using
    phiRDWithBackgroundJet_coordinateJet_eq_frozenPrincipal_add_remainder A
      (B x) (backgroundFirst B x) hU hg hx hsymm hdet i j

end RicciFlow.AnalyticPDE.GenuinePhiRD
