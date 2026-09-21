/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckNemytskii
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ConcreteRicciDeTurck

/-!
# Genuine C^{2,α} domain with bounded 2-jet extraction (Point 4 PDE milestone)

This file builds the real function space in which the Ricci–DeTurck PDE is
posed, together with the genuine (non-model) 2-jet extraction map.

## The space

A `C^{2,α}` metric section is represented by its 2-jet data in the Whitney
jet formalism:
- `val`: the 0-jet (metric value), a matrix-valued little-Hölder function,
- `der1`: the 1-jet (first derivatives), `n` matrix-valued little-Hölder functions,
- `der2`: the 2-jet (second derivatives), `n × n` matrix-valued little-Hölder functions.

`Jet2Section n d α` is this product, hence a Banach space
(`NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace` are all inferred).

## The extraction

`jet2OfSection s x : Jet2 n d` packages the three jet components of the
section `s` at the point `x`. Unlike the model `extract2JetModel` (which
zeroes the derivative slots), this uses the genuine 1-jet and 2-jet data
carried by the section.

Main results:
- `isHolderNorm_jet2OfSection`: the extracted jet map `x ↦ jet2OfSection s x`
  is Hölder with explicit constant `jet2SectionHolderConst s` (the sum of
  the Hölder seminorms of all scalar components).
- `jet2SectionHolderConst_le_norm`: that constant is `≤ d²(1+n+n²) * ‖s‖`,
  so the extraction is bounded in the section norm.
- `geometricNRD`: the genuine Ricci–DeTurck nonlinearity on sections,
  `geometricNRD Γbg s = genuineNRD (jet2OfSection s)`.
- `isHolderNorm_geometricNRD`: it preserves Hölder regularity with constant
  `B * jet2SectionHolderConst s`, via the packaged Nemytskii data.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

variable {n d : ℕ} {α : ℝ}

/-! ## 1. The C^{2,α} 2-jet section space -/

/-- **C^{2,α} 2-jet sections** (genuine).

The Whitney-jet model of `C^{2,α}` metric sections: the 0-jet, 1-jet, and
2-jet as little-Hölder matrix-valued functions. A product of Banach
spaces, hence a Banach space. -/
abbrev Jet2Section (n d : ℕ) (α : ℝ) : Type :=
  MatrixLittleHolder n d α × (Fin n → MatrixLittleHolder n d α) ×
    (Fin n → Fin n → MatrixLittleHolder n d α)

noncomputable instance : NormedAddCommGroup (Jet2Section n d α) :=
  inferInstanceAs (NormedAddCommGroup
    (MatrixLittleHolder n d α × (Fin n → MatrixLittleHolder n d α) ×
      (Fin n → Fin n → MatrixLittleHolder n d α)))

noncomputable instance : NormedSpace ℝ (Jet2Section n d α) :=
  inferInstanceAs (NormedSpace ℝ
    (MatrixLittleHolder n d α × (Fin n → MatrixLittleHolder n d α) ×
      (Fin n → Fin n → MatrixLittleHolder n d α)))

instance : CompleteSpace (Jet2Section n d α) :=
  inferInstanceAs (CompleteSpace
    (MatrixLittleHolder n d α × (Fin n → MatrixLittleHolder n d α) ×
      (Fin n → Fin n → MatrixLittleHolder n d α)))

/-- The 0-jet (metric value). -/
def Jet2Section.val (s : Jet2Section n d α) : MatrixLittleHolder n d α := s.1

/-- The 1-jet (first derivatives). -/
def Jet2Section.der1 (s : Jet2Section n d α) :
    Fin n → MatrixLittleHolder n d α := s.2.1

/-- The 2-jet (second derivatives). -/
def Jet2Section.der2 (s : Jet2Section n d α) :
    Fin n → Fin n → MatrixLittleHolder n d α := s.2.2

/-! ## 2. Genuine bounded 2-jet extraction -/

/-- Pointwise evaluation of a little-Hölder scalar function. -/
noncomputable def evalLH (f : LittleHolder n α) (x : Fin n → ℝ) : ℝ :=
  f.toHolder.toBCF x

/-- **Genuine 2-jet extraction.**

Packages the 0-jet, 1-jet, and 2-jet data of the section at the point `x`
into a `Jet2 n d` fiber element. This is the real extraction map: unlike
`extract2JetModel`, the derivative slots carry the section's genuine jet
data. -/
noncomputable def jet2OfSection (s : Jet2Section n d α) (x : Fin n → ℝ) :
    Jet2 n d :=
  ⟨fun i j => evalLH (s.val i j) x,
   fun k i j => evalLH ((s.der1 k) i j) x,
   fun k l i j => evalLH (((s.der2 k) l) i j) x⟩

/-- Explicit Hölder constant for the extracted jet map: the sum of the
Hölder seminorms of all scalar components. -/
noncomputable def jet2SectionHolderConst (s : Jet2Section n d α) : ℝ :=
  (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)) +
  (∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d,
    HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)) +
  (∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
    HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder))

/-- Entrywise Hölder bound for the 0-jet component of the extracted jet. -/
theorem jet2OfSection_val_entry_le (s : Jet2Section n d α) (x y : Fin n → ℝ)
    (i j : Fin d) :
    |(jet2OfSection s x - jet2OfSection s y).val i j| ≤
      HolderBCF.holderSeminorm ((s.val i j).toHolder) * ∑ k : Fin n, |(x - y) k| ^ α := by
  have hsub : (jet2OfSection s x - jet2OfSection s y).val i j =
      evalLH (s.val i j) x - evalLH (s.val i j) y := rfl
  rw [hsub]
  exact HolderBCF.abs_sub_le_holderSeminorm_mul _ x y

/-- Entrywise Hölder bound for the 1-jet component of the extracted jet. -/
theorem jet2OfSection_der1_entry_le (s : Jet2Section n d α) (x y : Fin n → ℝ)
    (k : Fin n) (i j : Fin d) :
    |(jet2OfSection s x - jet2OfSection s y).deriv1 k i j| ≤
      HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder) * ∑ k : Fin n, |(x - y) k| ^ α := by
  have hsub : (jet2OfSection s x - jet2OfSection s y).deriv1 k i j =
      evalLH ((s.der1 k) i j) x - evalLH ((s.der1 k) i j) y := rfl
  rw [hsub]
  exact HolderBCF.abs_sub_le_holderSeminorm_mul _ x y

/-- Entrywise Hölder bound for the 2-jet component of the extracted jet. -/
theorem jet2OfSection_der2_entry_le (s : Jet2Section n d α) (x y : Fin n → ℝ)
    (k l : Fin n) (i j : Fin d) :
    |(jet2OfSection s x - jet2OfSection s y).deriv2 k l i j| ≤
      HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder) *
        ∑ k : Fin n, |(x - y) k| ^ α := by
  have hsub : (jet2OfSection s x - jet2OfSection s y).deriv2 k l i j =
      evalLH (((s.der2 k) l) i j) x - evalLH (((s.der2 k) l) i j) y := rfl
  rw [hsub]
  exact HolderBCF.abs_sub_le_holderSeminorm_mul _ x y

/-! ## 3. The extracted jet map is Hölder -/

/-- **The extracted 2-jet map is Hölder.**

The map `x ↦ jet2OfSection s x` satisfies `IsHolderNorm` with the
explicit constant `jet2SectionHolderConst s`. This is the boundedness of
the 2-jet extraction that the Nemytskii machine needs. -/
theorem isHolderNorm_jet2OfSection (s : Jet2Section n d α) :
    IsHolderNorm α (jet2OfSection s) (jet2SectionHolderConst s) := by
  refine ⟨?_, fun x y => ?_⟩
  · -- The constant is nonnegative: a sum of seminorms.
    unfold jet2SectionHolderConst
    apply add_nonneg
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        HolderBCF.holderSeminorm_nonneg _
    · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => HolderBCF.holderSeminorm_nonneg _
    · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        HolderBCF.holderSeminorm_nonneg _
  · -- The Hölder estimate, component by component.
    have hval : ‖(jet2OfSection s x - jet2OfSection s y).val‖ ≤
        (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)) *
          ∑ k : Fin n, |(x - y) k| ^ α := by
      rw [matrix_norm_eq]
      calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection s x - jet2OfSection s y).val i j|
          ≤ ∑ i : Fin d, ∑ j : Fin d,
              (HolderBCF.holderSeminorm ((s.val i j).toHolder) * ∑ k : Fin n, |(x - y) k| ^ α) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              jet2OfSection_val_entry_le s x y i j
        _ = (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    have hder1 : ∀ k : Fin n, ‖(jet2OfSection s x - jet2OfSection s y).deriv1 k‖ ≤
        (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)) *
          ∑ k : Fin n, |(x - y) k| ^ α := by
      intro k
      rw [matrix_norm_eq]
      calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection s x - jet2OfSection s y).deriv1 k i j|
          ≤ ∑ i : Fin d, ∑ j : Fin d,
              (HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder) *
                ∑ k : Fin n, |(x - y) k| ^ α) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              jet2OfSection_der1_entry_le s x y k i j
        _ = (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    have hder2 : ∀ k l : Fin n,
        ‖(jet2OfSection s x - jet2OfSection s y).deriv2 k l‖ ≤
        (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)) *
          ∑ k : Fin n, |(x - y) k| ^ α := by
      intro k l
      rw [matrix_norm_eq]
      calc ∑ i : Fin d, ∑ j : Fin d, |(jet2OfSection s x - jet2OfSection s y).deriv2 k l i j|
          ≤ ∑ i : Fin d, ∑ j : Fin d,
              (HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder) *
                ∑ k : Fin n, |(x - y) k| ^ α) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              jet2OfSection_der2_entry_le s x y k l i j
        _ = (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    have hsum1 : ∑ k : Fin n, ‖(jet2OfSection s x - jet2OfSection s y).deriv1 k‖ ≤
        (∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d,
          HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)) *
          ∑ k : Fin n, |(x - y) k| ^ α := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k _ => hder1 k
    have hsum2 : ∑ k : Fin n, ∑ l : Fin n,
        ‖(jet2OfSection s x - jet2OfSection s y).deriv2 k l‖ ≤
        (∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
          HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)) *
          ∑ k : Fin n, |(x - y) k| ^ α := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun l _ => hder2 k l
    -- Assemble via the Jet2 norm.
    rw [Jet2.jet2_norm_eq]
    calc ‖(jet2OfSection s x - jet2OfSection s y).val‖ +
            ∑ k : Fin n, ‖(jet2OfSection s x - jet2OfSection s y).deriv1 k‖ +
            ∑ k : Fin n, ∑ l : Fin n, ‖(jet2OfSection s x - jet2OfSection s y).deriv2 k l‖
        ≤ (∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α +
            (∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d,
              HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α +
            (∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
              HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)) *
              ∑ k : Fin n, |(x - y) k| ^ α :=
          add_le_add (add_le_add hval hsum1) hsum2
      _ = jet2SectionHolderConst s * ∑ k : Fin n, |(x - y) k| ^ α := by
          unfold jet2SectionHolderConst
          ring

/-! ## 4. Boundedness in the section norm -/

/-- A little-Hölder function's seminorm is bounded by its norm. -/
theorem holderSeminorm_toHolder_le (f : LittleHolder n α) :
    HolderBCF.holderSeminorm (f.toHolder) ≤ ‖f‖ := by
  have h := HolderBCF.holderSeminorm_le_norm (f.toHolder)
  rwa [show ‖f.toHolder‖ = ‖f‖ from rfl] at h

/-- A Pi-type entry norm is bounded by the Pi norm. -/
theorem pi_entry_norm_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] (f : ∀ i, E i) (i : ι) :
    ‖f i‖ ≤ ‖f‖ :=
  norm_le_pi_norm _ i

/-- Product first-component norm bound. -/
theorem prod_fst_norm_le {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (p : E × F) : ‖p.1‖ ≤ ‖p‖ := by
  rw [Prod.norm_def]
  exact le_max_left _ _

/-- Product second-component norm bound. -/
theorem prod_snd_norm_le {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (p : E × F) : ‖p.2‖ ≤ ‖p‖ := by
  rw [Prod.norm_def]
  exact le_max_right _ _

/-- **The extraction is bounded in the section norm.**

The Hölder constant of the extracted jet map is at most
`d²(1 + n + n²) * ‖s‖`: each of the `d² + n·d² + n²·d²` scalar components
has seminorm `≤ ‖s‖`. -/
theorem jet2SectionHolderConst_le_norm (s : Jet2Section n d α) :
    jet2SectionHolderConst s ≤ (d : ℝ) ^ 2 * (1 + n + n ^ 2) * ‖s‖ := by
  have h0 : ∀ i : Fin d, ∀ j : Fin d,
      HolderBCF.holderSeminorm ((s.val i j).toHolder) ≤ ‖s‖ := by
    intro i j
    calc HolderBCF.holderSeminorm ((s.val i j).toHolder) ≤ ‖(s.val i) j‖ :=
          holderSeminorm_toHolder_le _
      _ ≤ ‖s.val i‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.val‖ := pi_entry_norm_le _ _
      _ ≤ ‖s‖ := prod_fst_norm_le _
  have h1 : ∀ k : Fin n, ∀ i : Fin d, ∀ j : Fin d,
      HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder) ≤ ‖s‖ := by
    intro k i j
    calc HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder) ≤ ‖((s.der1 k) i) j‖ :=
          holderSeminorm_toHolder_le _
      _ ≤ ‖(s.der1 k) i‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der1 k‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der1‖ := pi_entry_norm_le _ _
      _ ≤ ‖s‖ := le_trans (prod_fst_norm_le _) (prod_snd_norm_le _)
  have h2 : ∀ k l : Fin n, ∀ i : Fin d, ∀ j : Fin d,
      HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder) ≤ ‖s‖ := by
    intro k l i j
    calc HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder) ≤ ‖(((s.der2 k) l) i) j‖ :=
          holderSeminorm_toHolder_le _
      _ ≤ ‖((s.der2 k) l) i‖ := pi_entry_norm_le _ _
      _ ≤ ‖(s.der2 k) l‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der2 k‖ := pi_entry_norm_le _ _
      _ ≤ ‖s.der2‖ := pi_entry_norm_le _ _
      _ ≤ ‖s‖ := le_trans (prod_snd_norm_le _) (prod_snd_norm_le _)
  have hsum0 : ∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)
      ≤ (d : ℝ) ^ 2 * ‖s‖ := by
    calc ∑ i : Fin d, ∑ j : Fin d, HolderBCF.holderSeminorm ((s.val i j).toHolder)
        ≤ ∑ i : Fin d, ∑ j : Fin d, ‖s‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h0 i j
      _ = (d : ℝ) ^ 2 * ‖s‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum1 : ∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d,
        HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder) ≤ (n : ℝ) * (d : ℝ) ^ 2 * ‖s‖ := by
    calc ∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d,
            HolderBCF.holderSeminorm (((s.der1 k) i j).toHolder)
        ≤ ∑ k : Fin n, ∑ i : Fin d, ∑ j : Fin d, ‖s‖ :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => h1 k i j
      _ = (n : ℝ) * (d : ℝ) ^ 2 * ‖s‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum2 : ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
        HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)
        ≤ (n : ℝ) ^ 2 * (d : ℝ) ^ 2 * ‖s‖ := by
    calc ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
            HolderBCF.holderSeminorm ((((s.der2 k) l) i j).toHolder)
        ≤ ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d, ‖s‖ :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 k l i j
      _ = (n : ℝ) ^ 2 * (d : ℝ) ^ 2 * ‖s‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  unfold jet2SectionHolderConst
  have h := add_le_add (add_le_add hsum0 hsum1) hsum2
  refine le_trans h (le_of_eq ?_)
  ring

/-! ## 5. The geometric Ricci–DeTurck nonlinearity on sections -/

/-- **The genuine Ricci–DeTurck nonlinearity on C^{2,α} sections.**

For a `d`-dimensional manifold, the metric section lives over a
`d`-dimensional domain, so we use `Jet2Section d d α`. The nonlinearity
is the genuine fiber map `Φ_RD` applied to the extracted 2-jet:
`geometricNRD Γbg s x = Φ_RD (jet2OfSection s x)`. -/
noncomputable def geometricNRD (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α) : (Fin d → ℝ) → (Fin d → Fin d → ℝ) :=
  GenuinePhiRD.genuineNRD (d := d) Γbg (jet2OfSection s)

/-- **The geometric nonlinearity preserves Hölder regularity.**

If the extracted 2-jet stays in the compact convex set `K` (where the
fiber map is smooth with derivative bound `B`), then
`geometricNRD Γbg s` is Hölder with constant `B * jet2SectionHolderConst s`.
This is the genuine geometric `N_RD` for the Duhamel equation. -/
theorem isHolderNorm_geometricNRD (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hrange : ∀ x, jet2OfSection s x ∈
      (GenuinePhiRD.phiRDNemytskiiData (d := d) Γbg).K) :
    IsHolderNorm α (geometricNRD Γbg s)
      ((GenuinePhiRD.phiRDNemytskiiData (d := d) Γbg).B *
        jet2SectionHolderConst s) :=
  GenuinePhiRD.isHolderNorm_genuineNRD Γbg (isHolderNorm_jet2OfSection s) hrange

end AnalyticPDE
end RicciFlow
