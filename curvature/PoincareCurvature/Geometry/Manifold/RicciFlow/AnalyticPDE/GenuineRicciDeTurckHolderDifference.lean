/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricDuhamelData
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HrangeDischarge
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanSection

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

open Filter
open GenuinePhiRD
open Topology

variable {d : ℕ} {α : ℝ}

/-! A larger Hölder constant preserves an `IsHolderNorm` certificate. -/
theorem isHolderNorm_mono
    {E : Type*} [NormedAddCommGroup E]
    {f : (Fin d → ℝ) → E} {H H' : ℝ}
    (hf : IsHolderNorm α f H) (hHH' : H ≤ H') :
    IsHolderNorm α f H' := by
  refine ⟨le_trans hf.1 hHH', fun x y => ?_⟩
  have hsum : 0 ≤ ∑ j : Fin d, |(x - y) j| ^ α := by
    exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _
  exact le_trans (hf.2 x y) (mul_le_mul_of_nonneg_right hHH' hsum)

/-! A positive-exponent `IsHolderNorm` certificate supplies continuity. -/
theorem isHolderNorm_continuous
    {E : Type*} [NormedAddCommGroup E]
    {f : (Fin d → ℝ) → E} {H : ℝ} (hα : 0 < α)
    (hf : IsHolderNorm α f H) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hsum : Tendsto
      (fun y : Fin d → ℝ => ∑ j : Fin d, |(y - x) j| ^ α)
      (𝓝 x) (𝓝 0) := by
    have hterm : ∀ j : Fin d, Tendsto
        (fun y : Fin d → ℝ => |(y - x) j| ^ α)
        (𝓝 x) (𝓝 0) := by
      intro j
      have harg : Tendsto
          (fun y : Fin d → ℝ => |(y - x) j|)
          (𝓝 x) (𝓝 0) := by
        have hcont : Continuous (fun y : Fin d → ℝ => |(y - x) j|) :=
          continuous_abs.comp ((continuous_apply j).sub continuous_const)
        have hcontAt : ContinuousAt (fun y : Fin d → ℝ => |(y - x) j|) x :=
          hcont.continuousAt
        change Tendsto (fun y : Fin d → ℝ => |(y - x) j|)
          (𝓝 x) (𝓝 ((fun y : Fin d → ℝ => |(y - x) j|) x)) at hcontAt
        simpa using hcontAt
      have hpow := harg.rpow_const (Or.inr hα.le)
      simpa [Real.zero_rpow hα.ne'] using hpow
    have hsum' := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun j _ => hterm j)
    simpa using hsum'
  have hmod : Tendsto
      (fun y : Fin d → ℝ => H * ∑ j : Fin d, |(y - x) j| ^ α)
      (𝓝 x) (𝓝 0) := by
    have h := (tendsto_const_nhds (x := H)).mul hsum
    simpa using h
  obtain ⟨δ, hδ, hδmod⟩ := Metric.tendsto_nhds_nhds.1 hmod ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hsum_nonneg : 0 ≤ ∑ j : Fin d, |(y - x) j| ^ α := by
    exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _
  have hmod_nonneg : 0 ≤ H * ∑ j : Fin d, |(y - x) j| ^ α :=
    mul_nonneg hf.1 hsum_nonneg
  have hδmod' : dist
      (H * ∑ j : Fin d, |(y - x) j| ^ α) (0 : ℝ) < ε := hδmod hy
  have hmod_lt : H * ∑ j : Fin d, |(y - x) j| ^ α < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hmod_nonneg] at hδmod'
    exact hδmod'
  rw [dist_eq_norm]
  calc
    _ ≤ H * ∑ j : Fin d, |(y - x) j| ^ α := hf.2 y x
    _ < ε := hmod_lt

/-! Package a scalar Hölder function as a `HolderBCF` element. -/
noncomputable def holderBCFOfIsHolderNorm
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hcont : Continuous f)
    {B H : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hf : IsHolderNorm α f H) : HolderBCF α n :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hcont B (fun x => by
      simpa only [Real.norm_eq_abs] using hB x),
    ⟨H, by
      refine ⟨hf.1, fun x y => ?_⟩
      change |f x - f y| ≤ H * ∑ j : Fin n, |(x - y) j| ^ α
      simpa only [Real.norm_eq_abs] using hf.2 x y⟩⟩

@[simp] theorem holderBCFOfIsHolderNorm_apply
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hcont : Continuous f)
    {B H : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hf : IsHolderNorm α f H) (x : Fin n → ℝ) :
    (holderBCFOfIsHolderNorm hcont hB hf).toBCF x = f x := rfl

/-! Package a matrix-valued Hölder function entrywise. -/
noncomputable def matrixHolderBCFOfIsHolderNorm
    {n : ℕ} {f : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    (hcont : Continuous f) {B H : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hf : IsHolderNorm α f H) : MatrixHolderBCF n d α :=
  Matrix.of fun i j =>
    holderBCFOfIsHolderNorm
      ((continuous_apply j).comp ((continuous_apply i).comp hcont))
      (fun x => le_trans
        (by
          rw [← Real.norm_eq_abs]
          exact le_trans (pi_entry_norm_le (f x i) j) (pi_entry_norm_le (f x) i))
        (hB x))
      ⟨hf.1, fun x y => by
        calc
          |f x i j - f y i j| ≤ ‖f x - f y‖ := by
            rw [← Real.norm_eq_abs]
            change ‖(f x - f y) i j‖ ≤ ‖f x - f y‖
            exact le_trans (pi_entry_norm_le ((f x - f y) i) j)
              (pi_entry_norm_le (f x - f y) i)
          _ ≤ H * ∑ k : Fin n, |(x - y) k| ^ α := hf.2 x y⟩

@[simp] theorem matrixHolderBCFOfIsHolderNorm_apply
    {n : ℕ} {f : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    (hcont : Continuous f) {B H : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (hf : IsHolderNorm α f H) (x : Fin n → ℝ) (i j : Fin d) :
    (matrixHolderBCFOfIsHolderNorm hcont hB hf i j).toBCF x = f x i j := rfl

/-! ## Genuine output packaging

The compact fiber domain gives a finite output bound.  Together with the
positive-exponent continuity bridge above, this turns the genuine source
from a plain function into the repository's big-Hölder output type. -/

noncomputable def phiRDBoundData
    (Γbg : Fin d → Fin d → Fin d → ℝ) :
    {B : ℝ // 0 ≤ B ∧ ∀ x ∈ phiRDK (d := d),
      ‖phiRDMatrix (d := d) Γbg x‖ ≤ B} :=
  GenuinePhiRD.norm_bound_of_continuousOn
    (isCompact_phiRDK (d := d))
    ((contDiffOn_phiRDMatrix (d := d) Γbg).continuousOn.mono
      (phiRDK_subset_locus (d := d)))

noncomputable def phiRDBound
    (Γbg : Fin d → Fin d → Fin d → ℝ) : ℝ :=
  (phiRDBoundData Γbg).1

theorem phiRDBound_nonneg
    (Γbg : Fin d → Fin d → Fin d → ℝ) :
    0 ≤ phiRDBound Γbg :=
  (phiRDBoundData Γbg).2.1

theorem phiRDBound_spec
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    {x : Jet2 d d} (hx : x ∈ phiRDK (d := d)) :
    ‖phiRDMatrix (d := d) Γbg x‖ ≤ phiRDBound Γbg :=
  (phiRDBoundData Γbg).2.2 x hx

theorem norm_geometricNRD_le_phiRDBound
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) :
    ‖geometricNRD Γbg s x‖ ≤ phiRDBound Γbg := by
  have hx := phiRDBound_spec Γbg (hrange x)
  change ‖phiRDMatrix (d := d) Γbg (jet2OfSection s x)‖ ≤
    phiRDBound Γbg
  exact hx

/-! The genuine 0-jet source as a matrix of big-Hölder functions. -/
noncomputable def geometricNRDHolder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    MatrixHolderBCF d d α :=
  matrixHolderBCFOfIsHolderNorm
    (f := geometricNRD Γbg s)
    (hcont := isHolderNorm_continuous hα
      (isHolderNorm_geometricNRD Γbg s hrange))
    (B := phiRDBound Γbg)
    (H := (phiRDNemytskiiData (d := d) Γbg).B *
      jet2SectionHolderConst s)
    (hB := fun x => norm_geometricNRD_le_phiRDBound Γbg s hrange x)
    (hf := isHolderNorm_geometricNRD Γbg s hrange)

@[simp] theorem geometricNRDHolder_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    (geometricNRDHolder Γbg s hα hrange i j).toBCF x =
      geometricNRD Γbg s x i j := by
  exact matrixHolderBCFOfIsHolderNorm_apply
    (f := geometricNRD Γbg s)
    (hcont := isHolderNorm_continuous hα
      (isHolderNorm_geometricNRD Γbg s hrange))
    (hB := fun x => norm_geometricNRD_le_phiRDBound Γbg s hrange x)
    (hf := isHolderNorm_geometricNRD Γbg s hrange) x i j

/-! Package the source in the full section-space shape used by the Duhamel
formulation.  The derivative slots remain zero, as in `geometricN₀`; the
genuine nonlinear output is now present in the 0-jet component itself. -/
noncomputable def geometricNHolder
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    Jet2HolderSection d α :=
  (geometricNRDHolder Γbg s hα hrange, 0, 0)

@[simp] theorem geometricNHolder_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα : 0 < α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNHolder Γbg s hα hrange).1 i j).toBCF x =
      geometricNRD Γbg s x i j := by
  exact geometricNRDHolder_apply Γbg s hα hrange x i j

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

/-! The corresponding pointwise estimate controls the supremum component of
the full Hölder norm. -/
theorem norm_geometricNRD_sub
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s t : Jet2Section d d α)
    (hs : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (ht : ∀ x, jet2OfSection t x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    ∀ x, ‖geometricNRD Γbg s x - geometricNRD Γbg t x‖ ≤
      (phiRDNemytskiiData (d := d) Γbg).B *
        (jet2LipConst d d * ‖s - t‖) := by
  intro x
  have hMVT := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (phiRDNemytskiiData (d := d) Γbg).hderiv
    (phiRDNemytskiiData (d := d) Γbg).hB
    (phiRDNemytskiiData (d := d) Γbg).hconv
    (hs x) (ht x)
  have hbound :
      ‖(phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection s x) -
          (phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection t x)‖ ≤
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2LipConst d d * ‖s - t‖) := by
    calc
      ‖(phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection s x) -
            (phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection t x)‖ =
          ‖(phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection t x) -
            (phiRDNemytskiiData (d := d) Γbg).Φ (jet2OfSection s x)‖ :=
        norm_sub_rev _ _
      _ ≤ (phiRDNemytskiiData (d := d) Γbg).B *
            ‖jet2OfSection t x - jet2OfSection s x‖ := hMVT
      _ = (phiRDNemytskiiData (d := d) Γbg).B *
            ‖jet2OfSection s x - jet2OfSection t x‖ := by
        rw [norm_sub_rev]
      _ ≤ (phiRDNemytskiiData (d := d) Γbg).B *
            (jet2LipConst d d * ‖s - t‖) := by
        apply mul_le_mul_of_nonneg_left
          (jet2OfSection_lipschitz s t x)
          (phiRDNemytskiiData (d := d) Γbg).hB_nonneg
  simpa [geometricNRD, GenuinePhiRD.genuineNRD,
    NemytskiiData.nemytskii] using hbound

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

/-! The pointwise estimate has the same explicit small-ball range discharge. -/
theorem norm_geometricNRD_sub_of_mem_closedBall
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (c : Jet2Section d d α)
    (hc : ∀ x : Fin d → ℝ, jet2OfSection c x = (euclideanJet2 : Jet2 d d))
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall c R)
    (ht : t ∈ Metric.closedBall c R) :
    ∀ x, ‖geometricNRD Γbg s x - geometricNRD Γbg t x‖ ≤
      (phiRDNemytskiiData (d := d) Γbg).B *
        (jet2LipConst d d * ‖s - t‖) := by
  apply norm_geometricNRD_sub Γbg s t
  · exact hrange_of_mem_closedBall Γbg c hc hR hRsmall hs
  · exact hrange_of_mem_closedBall Γbg c hc hR hRsmall ht

/-! The Euclidean section discharges the constant-section hypothesis, so the
combined seminorm certificate is directly usable on the canonical small ball. -/
theorem isHolderNorm_geometricNRD_sub_of_euclidean_closedBall_norm
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (ht : t ∈ Metric.closedBall (euclideanSection d α) R) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s *
            (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2SectionHolderConst s + jet2SectionHolderConst t)) := by
  exact isHolderNorm_geometricNRD_sub_of_mem_closedBall_norm Γbg
    (euclideanSection d α)
    (fun x => jet2OfSection_euclideanSection d α x)
    hR hRsmall hs ht

/-! The sharp Hölder estimate uses the extracted jet of `s - t` itself.  Its
seminorm therefore vanishes with the section difference; the earlier coarse
certificate is retained for callers that only have separate section bounds. -/
theorem isHolderNorm_geometricNRD_sub_sharp
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s t : Jet2Section d d α)
    (hs : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (ht : ∀ x, jet2OfSection t x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s *
            (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          jet2SectionHolderConst (s - t)) := by
  have hsHolder : IsHolderNorm α (jet2OfSection s)
      (jet2SectionHolderConst s) :=
    isHolderNorm_jet2OfSection s
  have hdiffHolder : IsHolderNorm α
      (fun x => jet2OfSection s x - jet2OfSection t x)
      (jet2SectionHolderConst (s - t)) := by
    have h := isHolderNorm_jet2OfSection (s - t)
    have heq : (fun x => jet2OfSection s x - jet2OfSection t x) =
        jet2OfSection (s - t) := by
      funext x
      rfl
    rw [heq]
    exact h
  have hM : ∀ x, ‖jet2OfSection s x - jet2OfSection t x‖ ≤
      jet2LipConst d d * ‖s - t‖ := by
    intro x
    exact jet2OfSection_lipschitz s t x
  have h := isHolderNorm_comp_sub
    (phiRDNemytskiiData (d := d) Γbg).hconv
    (phiRDNemytskiiData (d := d) Γbg).hderiv
    (phiRDNemytskiiData (d := d) Γbg).hB_nonneg
    (phiRDNemytskiiData (d := d) Γbg).hB
    (phiRDNemytskiiData (d := d) Γbg).hL
    hsHolder hdiffHolder hs ht hM
  simpa [geometricNRD, GenuinePhiRD.genuineNRD,
    NemytskiiData.nemytskii] using h

/-! The extracted-jet norm bound turns the sharp certificate into a linear
Hölder-seminorm Lipschitz bound in the section norm. -/
theorem isHolderNorm_geometricNRD_sub_linear
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s t : Jet2Section d d α)
    (hs : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (ht : ∀ x, jet2OfSection t x ∈
      (phiRDNemytskiiData (d := d) Γbg).K) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      ((((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
            jet2SectionHolderConst s * jet2LipConst d d +
          (phiRDNemytskiiData (d := d) Γbg).B * jet2LipConst d d) *
        ‖s - t‖) := by
  have hsharp := isHolderNorm_geometricNRD_sub_sharp Γbg s t hs ht
  have hdiff : jet2SectionHolderConst (s - t) ≤
      jet2LipConst d d * ‖s - t‖ := by
    simpa [jet2LipConst] using jet2SectionHolderConst_le_norm (s - t)
  have hHs : 0 ≤ jet2SectionHolderConst s :=
    (isHolderNorm_jet2OfSection s).1
  have hL : 0 ≤ (phiRDNemytskiiData (d := d) Γbg).L :=
    (phiRDNemytskiiData (d := d) Γbg).L.coe_nonneg
  have hB : 0 ≤ (phiRDNemytskiiData (d := d) Γbg).B :=
    (phiRDNemytskiiData (d := d) Γbg).hB_nonneg
  have hC : 0 ≤ jet2LipConst d d := jet2LipConst_nonneg d d
  have hnorm : 0 ≤ ‖s - t‖ := norm_nonneg _
  refine isHolderNorm_mono
    (f := fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
    (H := (phiRDNemytskiiData (d := d) Γbg).L *
      jet2SectionHolderConst s * (jet2LipConst d d * ‖s - t‖) +
      (phiRDNemytskiiData (d := d) Γbg).B * jet2SectionHolderConst (s - t))
    (H' := (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s * jet2LipConst d d +
        (phiRDNemytskiiData (d := d) Γbg).B * jet2LipConst d d) *
      ‖s - t‖)
    hsharp ?_
  calc
    (phiRDNemytskiiData (d := d) Γbg).L * jet2SectionHolderConst s *
          (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          jet2SectionHolderConst (s - t) ≤
      (phiRDNemytskiiData (d := d) Γbg).L * jet2SectionHolderConst s *
          (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          (jet2LipConst d d * ‖s - t‖) := by
            gcongr
    _ = (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
            jet2SectionHolderConst s * jet2LipConst d d +
          (phiRDNemytskiiData (d := d) Γbg).B * jet2LipConst d d) *
        ‖s - t‖ := by ring

theorem isHolderNorm_geometricNRD_sub_of_euclidean_closedBall_sharp
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (ht : t ∈ Metric.closedBall (euclideanSection d α) R) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      (((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
          jet2SectionHolderConst s *
            (jet2LipConst d d * ‖s - t‖) +
        (phiRDNemytskiiData (d := d) Γbg).B *
          jet2SectionHolderConst (s - t)) := by
  apply isHolderNorm_geometricNRD_sub_sharp Γbg s t
  · exact hrange_of_mem_closedBall Γbg (euclideanSection d α)
      (fun x => jet2OfSection_euclideanSection d α x) hR hRsmall hs
  · exact hrange_of_mem_closedBall Γbg (euclideanSection d α)
      (fun x => jet2OfSection_euclideanSection d α x) hR hRsmall ht

theorem isHolderNorm_geometricNRD_sub_of_euclidean_closedBall_linear
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s t : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (ht : t ∈ Metric.closedBall (euclideanSection d α) R) :
    IsHolderNorm α (fun x => geometricNRD Γbg s x - geometricNRD Γbg t x)
      ((((phiRDNemytskiiData (d := d) Γbg).L : ℝ) *
            jet2SectionHolderConst s * jet2LipConst d d +
          (phiRDNemytskiiData (d := d) Γbg).B * jet2LipConst d d) *
        ‖s - t‖) := by
  apply isHolderNorm_geometricNRD_sub_linear Γbg s t
  · exact hrange_of_mem_closedBall Γbg (euclideanSection d α)
      (fun x => jet2OfSection_euclideanSection d α x) hR hRsmall hs
  · exact hrange_of_mem_closedBall Γbg (euclideanSection d α)
      (fun x => jet2OfSection_euclideanSection d α x) hR hRsmall ht

end AnalyticPDE
end RicciFlow
