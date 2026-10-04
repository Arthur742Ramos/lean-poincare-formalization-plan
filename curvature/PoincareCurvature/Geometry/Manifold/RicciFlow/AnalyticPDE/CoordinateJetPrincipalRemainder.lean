/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixJet
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckPrincipalRemainder

/-!
# Principal cancellation for actual C² coordinate jets

`coordinateJet` constructs the existing `Jet2` carrier from the actual value,
first component derivatives, and iterated component derivatives. The following
reaction identities obtain both required Hessian symmetries from open-domain C²
regularity and matrix symmetry. Metric invertibility is an independent premise.
These are identities for the algebraic jet reaction, not identifications of that
reaction with chartwise manifold curvature or an existence theorem.
-/

noncomputable section

open Matrix
open PoincareCurvature.CoordinateMatrixJet

namespace RicciFlow.AnalyticPDE

variable {n d : ℕ}

/-- An actual coordinate 2-jet, rather than freely supplied independent slots.
Derivative existence at the selected point is proved below from open-domain C²
regularity; the definition itself uses Mathlib's total derivative operators. -/
def coordinateJet (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin n → ℝ) : Jet2 n d :=
  ⟨g x, first g x, second g x⟩

@[simp] theorem coordinateJet_val
    (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ)) (x : Fin n → ℝ) :
    (coordinateJet g x).val = g x := rfl

@[simp] theorem coordinateJet_deriv1
    (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ)) (x : Fin n → ℝ) :
    (coordinateJet g x).deriv1 = first g x := rfl

@[simp] theorem coordinateJet_deriv2
    (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ)) (x : Fin n → ℝ) :
    (coordinateJet g x).deriv2 = second g x := rfl

variable {g : (Fin d → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- The produced Hessian has Schwarz symmetry, with no holonomy-certificate premise. -/
theorem coordinateJet_deriv2_derivative_symm
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (a b i k : Fin d) :
    ((coordinateJet g x).deriv2 a b) i k =
      ((coordinateJet g x).deriv2 b a) i k :=
  second_derivative_symm hU hg hx a b i k

/-- The produced Hessian preserves the actual field's local tensor symmetry. -/
theorem coordinateJet_deriv2_tensor_symm
    (hU : IsOpen U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (a b i k : Fin d) :
    ((coordinateJet g x).deriv2 a b) i k =
      ((coordinateJet g x).deriv2 a b) k i :=
  second_tensor_symm hU hx hsymm a b i k

namespace GenuinePhiRD

/-- The original finite-jet reaction's principal split on actual C² matrix data.
The background derivative is held constant in this original reaction. -/
theorem phiRD_coordinateJet_eq_principal_add_lowerOrder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i k : Fin d) :
    phiRDOfJet Γbg (coordinateJet g x) i k =
      jetPrincipalContraction (invMetricOfJet (coordinateJet g x))
        (coordinateJet g x) i k + lowerOrderRDOfJet Γbg (coordinateJet g x) i k := by
  exact phiRDOfJet_eq_principal_add_lowerOrder Γbg (coordinateJet g x)
    hdet (hsymm x hx) (coordinateJet_deriv2_derivative_symm hU hg hx)
    (coordinateJet_deriv2_tensor_symm hU hx hsymm) i k

/-- The corrected reaction split, preserving the explicit varying-background
first-jet terms and their signs. No background derivative producer is asserted. -/
theorem phiRDWithBackgroundJet_coordinateJet_eq_principal_add_lowerOrder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg Γbg1 (coordinateJet g x) i k =
      jetPrincipalContraction (invMetricOfJet (coordinateJet g x))
        (coordinateJet g x) i k +
        lowerOrderRDWithBackgroundJetOfJet Γbg Γbg1 (coordinateJet g x) i k := by
  exact phiRDWithBackgroundJetOfJet_eq_principal_add_lowerOrder Γbg Γbg1
    (coordinateJet g x) hdet (hsymm x hx)
    (coordinateJet_deriv2_derivative_symm hU hg hx)
    (coordinateJet_deriv2_tensor_symm hU hx hsymm) i k

/-- Frozen coefficient split on actual produced jets. The frozen coefficient
matrix remains arbitrary; identifying it with a heat generator is separate. -/
theorem phiRDWithBackgroundJet_coordinateJet_eq_frozenPrincipal_add_remainder
    (A : Fin d → Fin d → ℝ)
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0) (i k : Fin d) :
    phiRDWithBackgroundJetOfJet Γbg Γbg1 (coordinateJet g x) i k =
      jetPrincipalContraction A (coordinateJet g x) i k +
        frozenCoefficientRemainderOfJet A Γbg Γbg1 (coordinateJet g x) i k := by
  exact phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder A Γbg Γbg1
    (coordinateJet g x) hdet (hsymm x hx)
    (coordinateJet_deriv2_derivative_symm hU hg hx)
    (coordinateJet_deriv2_tensor_symm hU hx hsymm) i k

end GenuinePhiRD
end RicciFlow.AnalyticPDE
