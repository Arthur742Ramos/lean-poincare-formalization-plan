/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricDuhamelData
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HrangeDischarge

/-!
# Hölder-seminorm difference estimate for the genuine Ricci--DeTurck source

This file records the quantitative part of the nonlinear PDE estimate that is
already justified by the current formalization.  On a set of sections whose
extracted jets remain in the compact Ricci--DeTurck domain, the fiber-map
chain rule gives a difference estimate for the Hölder seminorm of
`N_RD(s) - N_RD(t)`.

The result is deliberately stated for the Hölder seminorm (`IsHolderNorm`).
It is not a claim that the full normed-space Nemytskii operator is locally
Lipschitz: the supremum component and the complete Duhamel data package still
require separate work.

No `sorry`, `admit`, or axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open GenuinePhiRD

variable {d : ℕ} {α : ℝ}

/-! ## The genuine source difference -/

/-! The Hölder-seminorm difference bound for the genuine Ricci--DeTurck
source.  The first term uses the pointwise jet difference bound `hM`; the
second uses the Hölder seminorm of the extracted jet difference. -/
theorem isHolderNorm_geometricNRD_sub
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s t : Jet2Section d d α)
    (hs : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (ht : ∀ x, jet2OfSection t x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    {M : ℝ}
    (hM : ∀ x, ‖jet2OfSection s x - jet2OfSection t x‖ ≤ M) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s * M +
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2SectionHolderConst s + jet2SectionHolderConst t)) := by
  have hsHolder : IsHolderNorm α (jet2OfSection s)
      (jet2SectionHolderConst s) :=
    isHolderNorm_jet2OfSection s
  have htHolder : IsHolderNorm α (jet2OfSection t)
      (jet2SectionHolderConst t) :=
    isHolderNorm_jet2OfSection t
  have hdiffHolder : IsHolderNorm α
      (fun x => jet2OfSection s x - jet2OfSection t x)
      (jet2SectionHolderConst s + jet2SectionHolderConst t) := by
    refine ⟨add_nonneg hsHolder.1 htHolder.1, fun x y => ?_⟩
    calc
      ‖(jet2OfSection s x - jet2OfSection t x) -
          (jet2OfSection s y - jet2OfSection t y)‖
          = ‖(jet2OfSection s x - jet2OfSection s y) -
              (jet2OfSection t x - jet2OfSection t y)‖ := by
                congr 1
                abel
      _ ≤ ‖jet2OfSection s x - jet2OfSection s y‖ +
          ‖jet2OfSection t x - jet2OfSection t y‖ := norm_sub_le _ _
      _ ≤ jet2SectionHolderConst s *
            ∑ j : Fin d, |(x - y) j| ^ α +
          jet2SectionHolderConst t *
            ∑ j : Fin d, |(x - y) j| ^ α :=
          add_le_add (hsHolder.2 x y) (htHolder.2 x y)
      _ = (jet2SectionHolderConst s + jet2SectionHolderConst t) *
            ∑ j : Fin d, |(x - y) j| ^ α := by ring
  have h := isHolderNorm_comp_sub
    (phiRDNemytskiiData (d := d) Γbg).hconv
    (phiRDNemytskiiData (d := d) Γbg).hderiv
    (phiRDNemytskiiData (d := d) Γbg).hB_nonneg
    (phiRDNemytskiiData (d := d) Γbg).hB
    (phiRDNemytskiiData (d := d) Γbg).hL
    hsHolder hdiffHolder hs ht hM
  simpa [geometricNRD, GenuinePhiRD.genuineNRD,
    NemytskiiData.nemytskii] using h

/-! ## Small-ball specialization -/

/-! On the Euclidean small-data ball, the range hypotheses needed by the
source estimate are discharged by the explicit `hrange` certificate. -/
theorem isHolderNorm_geometricNRD_sub_of_mem_closedBall
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (c : Jet2Section d d α)
    (hc : ∀ x : Fin d → ℝ, jet2OfSection c x = (euclideanJet2 : Jet2 d d))
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall c R)
    (ht : t ∈ Metric.closedBall c R)
    {M : ℝ}
    (hM : ∀ x, ‖jet2OfSection s x - jet2OfSection t x‖ ≤ M) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s * M +
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2SectionHolderConst s + jet2SectionHolderConst t)) := by
  apply isHolderNorm_geometricNRD_sub Γbg s t
  · exact hrange_of_mem_closedBall Γbg c hc hR hRsmall hs
  · exact hrange_of_mem_closedBall Γbg c hc hR hRsmall ht
  · exact hM

/-! The preceding estimate can use the explicit Lipschitz constant for the
2-jet extraction, so no separate pointwise bound has to be supplied. -/
theorem isHolderNorm_geometricNRD_sub_of_mem_closedBall_norm
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (c : Jet2Section d d α)
    (hc : ∀ x : Fin d → ℝ, jet2OfSection c x = (euclideanJet2 : Jet2 d d))
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall c R)
    (ht : t ∈ Metric.closedBall c R) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s *
            (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2SectionHolderConst s + jet2SectionHolderConst t)) := by
  refine isHolderNorm_geometricNRD_sub_of_mem_closedBall Γbg c hc hR hRsmall hs ht
    (M := jet2LipConst d d * ‖s - t‖) ?_
  intro x
  exact jet2OfSection_lipschitz s t x

end AnalyticPDE
end RicciFlow
