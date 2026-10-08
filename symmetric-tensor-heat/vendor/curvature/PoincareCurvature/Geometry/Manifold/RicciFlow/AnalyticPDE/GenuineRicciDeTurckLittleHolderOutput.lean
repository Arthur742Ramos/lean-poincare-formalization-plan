/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckLittleHolderDuhamel

/-!
# Little-Hölder packaging of the genuine Ricci--DeTurck output

The geometric source already has a valid big-Hölder package.  This file adds
the next honest preservation result: if the extracted 2-jet has an explicit
global Lipschitz certificate, then every component of the actual
Ricci--DeTurck output is little-Hölder.

The proof uses the genuine compact-domain Nemytskii estimate twice.  The
existing `α`-Hölder estimate supplies the `HolderBCF` output, while the same
fiber-map theorem at exponent `1` supplies the Lipschitz certificate.  The
new Lipschitz-data lemma then proves strong heat continuity in the full
`HolderBCF` norm and packages the result into `LittleHolder`.

This is a real nonlinear output theorem, but its hypothesis is deliberately
visible: arbitrary little-Hölder sections need not be globally Lipschitz, so
this does not yet provide an endomap on all of `Jet2Section`.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open GenuinePhiRD

variable {d : ℕ} {α : ℝ}

/-- The genuine geometric output has a Lipschitz Hölder certificate when the
extracted jet is globally Lipschitz. -/
theorem isHolderConst_geometricNRDHolder_of_isHolderNorm_one
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α) {H₁ : ℝ}
    (hjet1 : IsHolderNorm (1 : ℝ) (jet2OfSection s) H₁)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (i j : Fin d) :
    IsHolderConst (1 : ℝ)
      (geometricNRDHolder Γbg s hα hrange i j).toBCF
      ((phiRDNemytskiiData (d := d) Γbg).B * H₁) := by
  have hgeom1 : IsHolderNorm (1 : ℝ) (geometricNRD Γbg s)
      ((phiRDNemytskiiData (d := d) Γbg).B * H₁) :=
    GenuinePhiRD.isHolderNorm_genuineNRD Γbg hjet1 hrange
  refine ⟨hgeom1.1, fun x y => ?_⟩
  simp only [geometricNRDHolder_apply]
  calc
    |geometricNRD Γbg s x i j - geometricNRD Γbg s y i j| =
        ‖(geometricNRD Γbg s x - geometricNRD Γbg s y) i j‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤ ‖(geometricNRD Γbg s x - geometricNRD Γbg s y) i‖ :=
      pi_entry_norm_le _ _
    _ ≤ ‖geometricNRD Γbg s x - geometricNRD Γbg s y‖ :=
      pi_entry_norm_le _ _
    _ ≤ ((phiRDNemytskiiData (d := d) Γbg).B * H₁) *
        ∑ k : Fin d, |(x - y) k| ^ (1 : ℝ) := hgeom1.2 x y

/-- The actual geometric 0-jet output, packaged componentwise in the
little-Hölder space under the explicit Lipschitz certificate. -/
noncomputable def geometricNRDLittleHolder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α) (hα1 : α < 1) {H₁ : ℝ}
    (hjet1 : IsHolderNorm (1 : ℝ) (jet2OfSection s) H₁)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    MatrixLittleHolder d d α :=
  Matrix.of fun i j =>
    (⟨geometricNRDHolder Γbg s hα hrange i j,
      isGoodHolder_of_isHolderConst_one hα hα1
        (isHolderConst_geometricNRDHolder_of_isHolderNorm_one
          Γbg s hα hjet1 hrange i j)⟩ : LittleHolder d α)

@[simp] theorem geometricNRDLittleHolder_toHolder_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α) (hα1 : α < 1) {H₁ : ℝ}
    (hjet1 : IsHolderNorm (1 : ℝ) (jet2OfSection s) H₁)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNRDLittleHolder Γbg s hα hα1 hjet1 hrange i j).toHolder).toBCF x =
      geometricNRD Γbg s x i j := by
  change (geometricNRDHolder Γbg s hα hrange i j).toBCF x = _
  exact geometricNRDHolder_apply Γbg s hα hrange x i j

/-- The little-Hölder section-shaped source with the genuine output in its
0-jet slot and zero derivative slots, under the same explicit certificate. -/
noncomputable def geometricNLittleHolder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α) (hα1 : α < 1) {H₁ : ℝ}
    (hjet1 : IsHolderNorm (1 : ℝ) (jet2OfSection s) H₁)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    Jet2Section d d α :=
  (geometricNRDLittleHolder Γbg s hα hα1 hjet1 hrange, 0, 0)

@[simp] theorem geometricNLittleHolder_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α) (hα1 : α < 1) {H₁ : ℝ}
    (hjet1 : IsHolderNorm (1 : ℝ) (jet2OfSection s) H₁)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNLittleHolder Γbg s hα hα1 hjet1 hrange).val i j).toHolder.toBCF x =
      geometricNRD Γbg s x i j := by
  exact geometricNRDLittleHolder_toHolder_apply
    Γbg s hα hα1 hjet1 hrange x i j

end AnalyticPDE
end RicciFlow
