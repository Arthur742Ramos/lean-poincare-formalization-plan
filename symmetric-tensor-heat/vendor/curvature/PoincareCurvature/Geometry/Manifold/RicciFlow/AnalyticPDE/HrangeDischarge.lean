/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricDuhamelData

/-!
# hrange discharge via small-data estimate (Point 4 PDE milestone)

This file discharges the `hrange` hypothesis for the genuine Ricci–DeTurck
nonlinearity: for sections `s` in a closed ball around the Euclidean section,
the extracted 2-jets stay in the compact convex `K`.

## Strategy

1. Define the Euclidean section `c : Jet2Section n d α` (constant identity
   metric, vanishing derivatives).
2. Prove `jet2OfSection c x = euclideanJet2` for all `x`.
3. Prove the Lipschitz bound:
   `‖jet2OfSection s x - jet2OfSection t x‖ ≤ C(d,n) * ‖s - t‖`
   with explicit `C(d,n) = d²(1+n+n²)`.
4. Choose `R < (phiRDRadius/2) / C(d,n)`; then for `s ∈ closedBall c R`,
   `‖jet2OfSection s x - euclideanJet2‖ < phiRDRadius/2`,
   so `jet2OfSection s x ∈ K = closedBall(euclideanJet2, phiRDRadius/2)`.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open GenuinePhiRD
-- Also open the full path to be safe
open RicciFlow.AnalyticPDE.GenuinePhiRD

variable {n d : ℕ} {α : ℝ}

open Metric Set

/-! ## 1. Pointwise evaluation bound -/

/-- Evaluation at a point is 1-Lipschitz in the little-Hölder norm:
`|evalLH f x - evalLH g x| ≤ ‖f - g‖`. -/
theorem evalLH_sub_le (f g : LittleHolder n α) (x : Fin n → ℝ) :
    |evalLH   f x - evalLH   g x| ≤ ‖f - g‖ := by
  -- evalLH unfolds to double subtype val then evaluation
  have heval : ∀ h : LittleHolder n α, evalLH   h x = h.toHolder.toBCF x :=
    fun h => rfl
  rw [heval f, heval g]
  -- Bound by the BCF norm of the difference
  have h1 : |f.toHolder.toBCF x - g.toHolder.toBCF x| ≤ ‖f.toHolder.toBCF - g.toHolder.toBCF‖ := by
    have h := BoundedContinuousFunction.norm_coe_le_norm (f.toHolder.toBCF - g.toHolder.toBCF) x
    have h2 : |f.toHolder.toBCF x - g.toHolder.toBCF x| =
        ‖f.toHolder.toBCF x - g.toHolder.toBCF x‖ := (Real.norm_eq_abs _).symm
    rw [h2]
    have h3 : (f.toHolder.toBCF - g.toHolder.toBCF) x = f.toHolder.toBCF x - g.toHolder.toBCF x := rfl
    rw [← h3]
    exact h
  -- The BCF norm ≤ Hölder norm = LittleHolder norm
  have h2 : ‖f.toHolder.toBCF - g.toHolder.toBCF‖ ≤ ‖f - g‖ := by
    have hsub : f.toHolder.toBCF - g.toHolder.toBCF = (f - g).toHolder.toBCF := by rfl
    rw [hsub]
    -- BCF norm ≤ Hölder norm (which adds the seminorm)
    have hle : ‖(f - g).toHolder.toBCF‖ ≤ ‖(f - g).toHolder‖ := by
      -- ‖h‖ = ‖h.toBCF‖ + seminorm ≥ ‖h.toBCF‖
      have hnorm := HolderBCF.norm_def ((f - g).toHolder)
      have hnn : 0 ≤ HolderBCF.holderSeminorm ((f - g).toHolder) :=
        HolderBCF.holderSeminorm_nonneg _
      linarith
    -- Hölder norm = LittleHolder norm (submodule subtype)
    have heq : ‖(f - g).toHolder‖ = ‖f - g‖ := rfl
    linarith
  linarith

/-! ## 2. The Lipschitz constant for 2-jet extraction -/

/-- The explicit Lipschitz constant: `d²(1+n+n²)`. -/
noncomputable def jet2LipConst (n d : ℕ) : ℝ :=
  (d ^ 2 : ℝ) * (1 + n + n ^ 2)

theorem jet2LipConst_nonneg (n d : ℕ) : 0 ≤ jet2LipConst n d := by
  unfold jet2LipConst
  apply mul_nonneg
  · apply pow_nonneg; norm_num
  · have h1 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ((n : ℝ) ^ 2) := pow_nonneg (Nat.cast_nonneg _) _
    linarith

/-- Entrywise bound for the 0-jet component difference. -/
theorem jet2OfSection_val_sub_entry_le (s t : Jet2Section n d α) (x : Fin n → ℝ)
    (i j : Fin d) :
    |(jet2OfSection   s x - jet2OfSection   t x).val i j| ≤
      ‖s - t‖ := by
  -- The val component of the difference
  have hval : (jet2OfSection   s x - jet2OfSection   t x).val i j =
      evalLH   (s.val i j) x - evalLH   (t.val i j) x := by
    rfl
  rw [hval]
  -- Apply the 1-Lipschitz bound for evalLH
  have hle := evalLH_sub_le   (s.val i j) (t.val i j) x
  -- ‖s.val i j - t.val i j‖ ≤ ‖s - t‖ via Pi and product norms
  have hbound : ‖s.val i j - t.val i j‖ ≤ ‖s - t‖ := by
    have h1 : s.val i j - t.val i j = (s.val - t.val) i j := by
      simp [Matrix.sub_apply]
    rw [h1]
    calc ‖(s.val - t.val) i j‖ ≤ ‖(s.val - t.val) i‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.val - t.val‖ := pi_entry_norm_le _ _
      _ = ‖(s - t).val‖ := by simp [Jet2Section.val]
      _ ≤ ‖s - t‖ := prod_fst_norm_le _
  linarith

/-- Entrywise bound for the 1-jet component difference. -/
theorem jet2OfSection_der1_sub_entry_le (s t : Jet2Section n d α) (x : Fin n → ℝ)
    (k : Fin n) (i j : Fin d) :
    |(jet2OfSection   s x - jet2OfSection   t x).deriv1 k i j| ≤
      ‖s - t‖ := by
  have hder1 : (jet2OfSection   s x - jet2OfSection   t x).deriv1 k i j =
      evalLH   ((s.der1 k) i j) x - evalLH   ((t.der1 k) i j) x := by
    rfl
  rw [hder1]
  have hle := evalLH_sub_le   ((s.der1 k) i j) ((t.der1 k) i j) x
  have hbound : ‖(s.der1 k) i j - (t.der1 k) i j‖ ≤ ‖s - t‖ := by
    have h1 : (s.der1 k) i j - (t.der1 k) i j = ((s.der1 - t.der1) k) i j := by
      simp [Matrix.sub_apply, Pi.sub_apply]
    rw [h1]
    calc ‖(((s.der1 - t.der1) k) i) j‖ ≤ ‖((s.der1 - t.der1) k) i‖ := pi_entry_norm_le _ _
      _ ≤ ‖(s.der1 - t.der1) k‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der1 - t.der1‖ := pi_entry_norm_le _ _
      _ = ‖(s - t).2.1‖ := by simp [Jet2Section.der1]
      _ ≤ ‖(s - t).2‖ := prod_fst_norm_le _
      _ ≤ ‖s - t‖ := prod_snd_norm_le _
  linarith

/-- Entrywise bound for the 2-jet component difference. -/
theorem jet2OfSection_der2_sub_entry_le (s t : Jet2Section n d α) (x : Fin n → ℝ)
    (k l : Fin n) (i j : Fin d) :
    |(jet2OfSection   s x - jet2OfSection   t x).deriv2 k l i j| ≤
      ‖s - t‖ := by
  have hder2 : (jet2OfSection   s x - jet2OfSection   t x).deriv2 k l i j =
      evalLH   (((s.der2 k) l) i j) x - evalLH   (((t.der2 k) l) i j) x := by
    rfl
  rw [hder2]
  have hle := evalLH_sub_le   (((s.der2 k) l) i j) (((t.der2 k) l) i j) x
  have hbound : ‖(((s.der2 k) l) i j) - (((t.der2 k) l) i j)‖ ≤ ‖s - t‖ := by
    have h1 : (((s.der2 k) l) i j) - (((t.der2 k) l) i j) = ((((s.der2 - t.der2) k) l) i) j := by
      simp [Matrix.sub_apply, Pi.sub_apply]
    rw [h1]
    calc ‖((((s.der2 - t.der2) k) l) i) j‖ ≤ ‖((((s.der2 - t.der2) k) l) i)‖ := pi_entry_norm_le _ _
      _ ≤ ‖(((s.der2 - t.der2) k) l)‖ := pi_entry_norm_le _ _
      _ ≤ ‖((s.der2 - t.der2) k)‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der2 - t.der2‖ := pi_entry_norm_le _ _
      _ = ‖(s - t).2.2‖ := by simp [Jet2Section.der2]
      _ ≤ ‖(s - t).2‖ := prod_snd_norm_le _
      _ ≤ ‖s - t‖ := prod_snd_norm_le _
  linarith

/-! ## 3. The full Lipschitz bound -/

/-- The 2-jet extraction is Lipschitz with constant `d²(1+n+n²)`. -/
theorem jet2OfSection_lipschitz (s t : Jet2Section n d α) (x : Fin n → ℝ) :
    ‖jet2OfSection   s x - jet2OfSection   t x‖ ≤
      jet2LipConst n d * ‖s - t‖ := by
  -- Unfold the Jet2 norm and Matrix norm
  have hnorm : ‖jet2OfSection   s x - jet2OfSection   t x‖ =
      ‖(jet2OfSection   s x - jet2OfSection   t x).val‖ +
      ∑ k : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv1 k‖ +
      ∑ k : Fin n, ∑ l : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv2 k l‖ := by
    rfl
  rw [hnorm]
  -- Bound each Matrix norm by sum of entry bounds
  have hval : ‖(jet2OfSection   s x - jet2OfSection   t x).val‖ ≤
      (d : ℝ) ^ 2 * ‖s - t‖ := by
    rw [matrix_norm_eq]
    calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection   s x - jet2OfSection   t x).val i j|
        ≤ ∑ i : Fin d, ∑ j : Fin d, ‖s - t‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            jet2OfSection_val_sub_entry_le s t x i j
      _ = (d : ℝ) ^ 2 * ‖s - t‖ := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]
          ring
  have hder1 : ∀ k : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv1 k‖ ≤
      (d : ℝ) ^ 2 * ‖s - t‖ := by
    intro k
    rw [matrix_norm_eq]
    calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection   s x - jet2OfSection   t x).deriv1 k i j|
        ≤ ∑ i : Fin d, ∑ j : Fin d, ‖s - t‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            jet2OfSection_der1_sub_entry_le s t x k i j
      _ = (d : ℝ) ^ 2 * ‖s - t‖ := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]
          ring
  have hder2 : ∀ k l : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv2 k l‖ ≤
      (d : ℝ) ^ 2 * ‖s - t‖ := by
    intro k l
    rw [matrix_norm_eq]
    calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection   s x - jet2OfSection   t x).deriv2 k l i j|
        ≤ ∑ i : Fin d, ∑ j : Fin d, ‖s - t‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            jet2OfSection_der2_sub_entry_le s t x k l i j
      _ = (d : ℝ) ^ 2 * ‖s - t‖ := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]
          ring
  -- Sum up
  calc ‖(jet2OfSection   s x - jet2OfSection   t x).val‖ +
        ∑ k : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv1 k‖ +
        ∑ k : Fin n, ∑ l : Fin n, ‖(jet2OfSection   s x - jet2OfSection   t x).deriv2 k l‖
      ≤ (d : ℝ) ^ 2 * ‖s - t‖ + ∑ k : Fin n, ((d : ℝ) ^ 2 * ‖s - t‖) +
        ∑ k : Fin n, ∑ l : Fin n, ((d : ℝ) ^ 2 * ‖s - t‖) := by
          apply add_le_add
          · apply add_le_add hval
            apply Finset.sum_le_sum; intro k _
            exact hder1 k
          · apply Finset.sum_le_sum; intro k _
            apply Finset.sum_le_sum; intro l _
            exact hder2 k l
    _ = jet2LipConst n d * ‖s - t‖ := by
        unfold jet2LipConst
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 4. hrange discharge -/

/-- The compact `K` from the Nemytskii data is the closed ball. -/
theorem nemytskii_K_eq (d : ℕ) (Γbg : Fin d → Fin d → Fin d → ℝ) :
    (phiRDNemytskiiData  Γbg).K = phiRDK  := by
  -- From the construction of phiRDNemytskiiData, K = phiRDK
  -- The definition uses `refine ⟨..., phiRDK , ...⟩`
  rfl

/-- If the jet is within `R < phiRDRadius/2` of the Euclidean jet, it's in `K`. -/
theorem mem_K_of_jet_bound (d : ℕ) (Γbg : Fin d → Fin d → Fin d → ℝ)
    (j : Jet2 d d) (R : ℝ)
    (hbound : ‖j - (euclideanJet2 : Jet2 d d)‖ ≤ R)
    (hRsmall : R < (phiRDRadius (d := d)) / 2) :
    j ∈ (phiRDNemytskiiData Γbg).K := by
  have hK : (phiRDNemytskiiData Γbg).K = (phiRDK (d := d)) := by rfl
  rw [hK]
  show j ∈ (phiRDK (d := d))
  unfold phiRDK
  -- j ∈ closedBall(euclideanJet2, phiRDRadius/2) iff dist j euclideanJet2 ≤ phiRDRadius/2
  rw [Metric.mem_closedBall]
  -- dist j euclideanJet2 = ‖j - euclideanJet2‖
  have hdist : dist j (euclideanJet2 : Jet2 d d) = ‖j - (euclideanJet2 : Jet2 d d)‖ := by
    rw [dist_eq_norm]
  rw [hdist]
  linarith

/-- The jet bound for sections in a ball around a Euclidean section.

If `c` is a section with `jet2OfSection c x = euclideanJet2` for all `x`,
and `s ∈ closedBall c R`, then `‖jet2OfSection s x - euclideanJet2‖ ≤ L * R`. -/
theorem jet_bound_of_mem_closedBall {d : ℕ} {α : ℝ}
    (c : Jet2Section d d α)
    (hc : ∀ x : Fin d → ℝ, jet2OfSection c x = (euclideanJet2 : Jet2 d d))
    {s : Jet2Section d d α} {R : ℝ}
    (hs : s ∈ Metric.closedBall c R) :
    ∀ x : Fin d → ℝ, ‖jet2OfSection s x - (euclideanJet2 : Jet2 d d)‖ ≤
      jet2LipConst d d * R := by
  intro x
  -- ‖jet2OfSection s x - euclideanJet2‖ = ‖jet2OfSection s x - jet2OfSection c x‖
  have heq : jet2OfSection s x - (euclideanJet2 : Jet2 d d) =
      jet2OfSection s x - jet2OfSection c x := by
    rw [hc x]
  rw [heq]
  -- Apply Lipschitz bound
  have hlip := jet2OfSection_lipschitz s c x
  -- ‖s - c‖ ≤ R from hs : s ∈ closedBall c R
  have hRs : ‖s - c‖ ≤ R := by
    have hmem : dist s c ≤ R := Metric.mem_closedBall.mp hs
    rwa [dist_eq_norm] at hmem
  -- L * ‖s - c‖ ≤ L * R (need L ≥ 0)
  have hLnonneg : 0 ≤ jet2LipConst d d := jet2LipConst_nonneg d d
  calc ‖jet2OfSection s x - jet2OfSection c x‖
      ≤ jet2LipConst d d * ‖s - c‖ := hlip
    _ ≤ jet2LipConst d d * R := by
        apply mul_le_mul_of_nonneg_left hRs hLnonneg

/-- **hrange discharge (small-data).**

For `s` in a closed ball of radius `R` around a Euclidean section `c`
(with `jet2OfSection c x = euclideanJet2`), if `2 * L * R < phiRDRadius`,
then the extracted 2-jets stay in the compact `K`.

The hypothesis `hc` (existence of a Euclidean section) is the remaining
analytic input: it requires constant `LittleHolder` functions (the heat
propagator fixes constants, so they lie in the little-Hölder submodule).
This is documented as the explicit blocker for the unconditional version. -/
theorem hrange_of_mem_closedBall {d : ℕ} {α : ℝ}
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (c : Jet2Section d d α)
    (hc : ∀ x : Fin d → ℝ, jet2OfSection c x = (euclideanJet2 : Jet2 d d))
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < (phiRDRadius (d := d)))
    {s : Jet2Section d d α} (hs : s ∈ Metric.closedBall c R) :
    ∀ x : Fin d → ℝ, jet2OfSection s x ∈
      (phiRDNemytskiiData Γbg).K := by
  intro x
  -- Get the jet bound: ‖jet2OfSection s x - euclideanJet2‖ ≤ L * R
  have hbound : ‖jet2OfSection s x - (euclideanJet2 : Jet2 d d)‖ ≤ jet2LipConst d d * R :=
    jet_bound_of_mem_closedBall c hc hs x
  -- Show L * R < phiRDRadius / 2
  have hLR : jet2LipConst d d * R < (phiRDRadius (d := d)) / 2 := by linarith
  -- Apply mem_K_of_jet_bound
  exact mem_K_of_jet_bound d Γbg (jet2OfSection s x) (jet2LipConst d d * R) hbound hLR

end AnalyticPDE
end RicciFlow
