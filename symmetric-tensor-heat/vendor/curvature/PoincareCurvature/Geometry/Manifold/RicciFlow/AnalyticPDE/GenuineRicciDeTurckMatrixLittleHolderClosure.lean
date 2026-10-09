/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckLittleHolderOutput

/-!
# Matrix-valued little-Hölder closure for the genuine reaction

This file lifts the scalar little-Hölder carrier argument to the actual
matrix-valued Ricci--DeTurck reaction.  The approximants are the genuine
componentwise little-Hölder heat flow, not a placeholder nonlinearity:

* the section heat path converges in the full `Jet2Section` norm;
* every positive-time jet component has a proved spatial Lipschitz bound;
* the genuine matrix output has full-Hölder difference control; and
* closedness of the scalar little-Hölder carrier is applied entry by entry.

The compact jet-range condition along the heat path remains an explicit
hypothesis.  It is the geometric invariant-region gate and is not silently
replaced by a componentwise estimate.  Consequently the result closes the
matrix-valued Nemytskii carrier once that range lemma is supplied, without
claiming the local Duhamel endomap or the PDE invariant-region argument.

No `sorry`, `admit`, or axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology Metric
open scoped NNReal ENNReal Interval
open GenuinePhiRD

variable {d : ℕ} {α : ℝ}

/-! ## Positive-time Lipschitz certificates -/

private theorem isHolderConst_one_of_lipschitzWith_heat
    {g : BoundedContinuousFunction (Fin d → ℝ) ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K (fun x => g x)) :
    IsHolderConst (1 : ℝ) g (K : ℝ) := by
  refine ⟨K.coe_nonneg, fun x y => ?_⟩
  have hxy := hg.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hxy
  have hsum : 0 ≤ ∑ k : Fin d, |(x - y) k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg ((x - y) k))
  have hnorm_le_sum : ‖x - y‖ ≤ ∑ k : Fin d, |(x - y) k| := by
    refine (pi_norm_le_iff_of_nonneg hsum).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun k _ => abs_nonneg ((x - y) k))
      (Finset.mem_univ i)
  calc
    |g x - g y| ≤ (K : ℝ) * ‖x - y‖ := hxy
    _ ≤ (K : ℝ) * ∑ k : Fin d, |(x - y) k| :=
      mul_le_mul_of_nonneg_left hnorm_le_sum K.coe_nonneg
    _ = (K : ℝ) * ∑ k : Fin d, |(x - y) k| ^ (1 : ℝ) := by
      simp [Real.rpow_one]

private theorem heatLittleHolder_isHolderConst_one
    {f : LittleHolder d α} {t : ℝ} (ht : 0 < t) :
    IsHolderConst (1 : ℝ)
      (LittleHolder.littleHolderPropagator (n := d) (α := α) t f).toHolder.toBCF
      (((d : ℝ) * (‖f.val.toBCF‖ / Real.sqrt (Real.pi * t))).toNNReal : ℝ) := by
  have heq :
      (LittleHolder.littleHolderPropagator (n := d) (α := α) t f).toHolder.toBCF =
        heatSemigroupNDbcf ht f.val.toBCF := by
    ext x
    rw [LittleHolder.littleHolderPropagator_of_pos ht]
    change (heatSemigroupHolderFun (n := d) (α := α) ht f.val).toBCF x = _
    rw [heatSemigroupHolderFun_toBCF ht]
  rw [heq]
  let K : ℝ≥0 :=
    ((d : ℝ) * (‖f.val.toBCF‖ / Real.sqrt (Real.pi * t))).toNNReal
  have hC : ∀ y : Fin d → ℝ, ‖f.val.toBCF y‖ ≤ ‖f.val.toBCF‖ := fun y =>
    BoundedContinuousFunction.norm_coe_le_norm f.val.toBCF y
  have hspatial : LipschitzWith K
      (fun x : Fin d → ℝ => heatSemigroupND t f.val.toBCF x) := by
    dsimp [K]
    exact heatSemigroupND_lipschitzWith_spatial ht
      f.val.toBCF.continuous.aestronglyMeasurable hC
  have hspatial_bcf : LipschitzWith K
      (fun x : Fin d → ℝ => heatSemigroupNDbcf ht f.val.toBCF x) := by
    simpa only [heatSemigroupNDbcf_apply] using hspatial
  dsimp [K]
  exact isHolderConst_one_of_lipschitzWith_heat hspatial_bcf

/-! ## The vector-valued heat path -/

/-- The componentwise little-Hölder heat path converges at time zero in the
full product norm.  This is the vector-valued convergence needed by the
matrix-valued carrier argument below. -/
theorem jet2SectionLittleHolderPropagator_tendsto_nhdsWithin_zero
    (s : Jet2Section d d α) :
    Filter.Tendsto
      (fun t : ℝ =>
        jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 s) := by
  have hcont := jet2SectionLittleHolderPropagator_hSjoint
    (d := d) (α := α) (T := (1 : ℝ)) (by norm_num)
  have hp : (0, s) ∈
      Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Jet2Section d d α)) := by
    simp
  have hwithin : ContinuousWithinAt
      (fun p : ℝ × Jet2Section d d α ↦
        jet2SectionLittleHolderPropagator (d := d) (α := α) p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Jet2Section d d α))) (0, s) :=
    hcont (0, s) hp
  have hcurve : Filter.Tendsto (fun t : ℝ => (t, s))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (0, s)) := by
    have ht : Filter.Tendsto (fun t : ℝ => t)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (0 : ℝ)) :=
      tendsto_id'.2 nhdsWithin_le_nhds
    convert ht.prodMk (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => s) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 s)) using 1
    simp only [nhds_prod_eq]
  have hcurve' : Filter.Tendsto (fun t : ℝ => (t, s))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝[(Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Jet2Section d d α)))] (0, s)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcurve, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht hsmall
    simp only [mem_prod, mem_Icc, mem_univ, and_true]
    exact ⟨le_of_lt ht, hsmall.le⟩
  have hout := hwithin.tendsto.comp hcurve'
  simpa [Function.comp_def, jet2SectionLittleHolderPropagator_apply,
    matrixLittleHolderPropagator_zero,
    jet2SectionLittleHolderPropagator_zero] using hout

/-! ## A Lipschitz certificate for every positive-time extracted jet -/

/-- Positive-time heat smoothing gives a genuine exponent-one Hölder
certificate for the complete extracted jet, with no component hidden in an
abstract regularity assumption. -/
theorem isHolderNorm_one_jet2SectionLittleHolderPropagator
    (s : Jet2Section d d α) {t : ℝ} (ht : 0 < t) :
    ∃ H : ℝ, IsHolderNorm (1 : ℝ)
      (jet2OfSection
        (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)) H := by
  let P := jet2SectionLittleHolderPropagator (d := d) (α := α) t s
  have h0 : ∀ i j : Fin d, ∃ H : ℝ,
      IsHolderConst (1 : ℝ) (P.1 i j).toHolder.toBCF H := by
    intro i j
    simpa [P, Jet2Section.val, Jet2Section.der1, Jet2Section.der2,
      jet2SectionLittleHolderPropagator_apply,
      matrixLittleHolderPropagator_apply] using
      (⟨_, heatLittleHolder_isHolderConst_one (f := s.val i j) ht⟩ :
        ∃ H : ℝ, IsHolderConst (1 : ℝ)
          (LittleHolder.littleHolderPropagator (n := d) (α := α) t (s.val i j)).toHolder.toBCF H)
  have h1 : ∀ k : Fin d, ∀ i j : Fin d, ∃ H : ℝ,
      IsHolderConst (1 : ℝ) (P.2.1 k i j).toHolder.toBCF H := by
    intro k i j
    simpa [P, Jet2Section.val, Jet2Section.der1, Jet2Section.der2,
      jet2SectionLittleHolderPropagator_apply,
      matrixLittleHolderPropagator_apply] using
      (⟨_, heatLittleHolder_isHolderConst_one (f := s.der1 k i j) ht⟩ :
        ∃ H : ℝ, IsHolderConst (1 : ℝ)
          (LittleHolder.littleHolderPropagator (n := d) (α := α) t (s.der1 k i j)).toHolder.toBCF H)
  have h2 : ∀ k l : Fin d, ∀ i j : Fin d, ∃ H : ℝ,
      IsHolderConst (1 : ℝ) (P.2.2 k l i j).toHolder.toBCF H := by
    intro k l i j
    simpa [P, Jet2Section.val, Jet2Section.der1, Jet2Section.der2,
      jet2SectionLittleHolderPropagator_apply,
      matrixLittleHolderPropagator_apply] using
      (⟨_, heatLittleHolder_isHolderConst_one (f := s.der2 k l i j) ht⟩ :
        ∃ H : ℝ, IsHolderConst (1 : ℝ)
          (LittleHolder.littleHolderPropagator (n := d) (α := α) t (s.der2 k l i j)).toHolder.toBCF H)
  choose H0 hH0 using h0
  choose H1 hH1 using h1
  choose H2 hH2 using h2
  let H : ℝ :=
    (∑ i : Fin d, ∑ j : Fin d, H0 i j) +
      (∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, H1 k i j) +
      ∑ k : Fin d, ∑ l : Fin d, ∑ i : Fin d, ∑ j : Fin d, H2 k l i j
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    apply add_nonneg
    · apply add_nonneg
      · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hH0 i j).1
      · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => (hH1 k i j).1
    · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (hH2 k l i j).1
  refine ⟨H, ⟨hHnonneg, fun x y => ?_⟩⟩
  have hval : ‖(jet2OfSection P x - jet2OfSection P y).val‖ ≤
      (∑ i : Fin d, ∑ j : Fin d, H0 i j) *
        ∑ k : Fin d, |(x - y) k| ^ (1 : ℝ) := by
    rw [matrix_norm_eq]
    calc
      ∑ i : Fin d, ∑ j : Fin d,
          |(jet2OfSection P x - jet2OfSection P y).val i j| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (H0 i j) * ∑ k : Fin d, |(x - y) k| ^ (1 : ℝ) := by
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (hH0 i j).2 x y
      _ = (∑ i : Fin d, ∑ j : Fin d, H0 i j) *
          ∑ k : Fin d, |(x - y) k| ^ (1 : ℝ) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hder1 : ∀ k : Fin d,
      ‖(jet2OfSection P x - jet2OfSection P y).deriv1 k‖ ≤
      (∑ i : Fin d, ∑ j : Fin d, H1 k i j) *
        ∑ l : Fin d, |(x - y) l| ^ (1 : ℝ) := by
    intro k
    rw [matrix_norm_eq]
    calc
      ∑ i : Fin d, ∑ j : Fin d,
          |(jet2OfSection P x - jet2OfSection P y).deriv1 k i j| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (H1 k i j) * ∑ l : Fin d, |(x - y) l| ^ (1 : ℝ) := by
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (hH1 k i j).2 x y
      _ = (∑ i : Fin d, ∑ j : Fin d, H1 k i j) *
          ∑ l : Fin d, |(x - y) l| ^ (1 : ℝ) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hder2 : ∀ k l : Fin d,
      ‖(jet2OfSection P x - jet2OfSection P y).deriv2 k l‖ ≤
      (∑ i : Fin d, ∑ j : Fin d, H2 k l i j) *
        ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) := by
    intro k l
    rw [matrix_norm_eq]
    calc
      ∑ i : Fin d, ∑ j : Fin d,
          |(jet2OfSection P x - jet2OfSection P y).deriv2 k l i j| ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (H2 k l i j) * ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) := by
            exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (hH2 k l i j).2 x y
      _ = (∑ i : Fin d, ∑ j : Fin d, H2 k l i j) *
          ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  rw [Jet2.jet2_norm_eq]
  calc
    ‖(jet2OfSection P x - jet2OfSection P y).val‖ +
        ∑ k : Fin d, ‖(jet2OfSection P x - jet2OfSection P y).deriv1 k‖ +
        ∑ k : Fin d, ∑ l : Fin d,
          ‖(jet2OfSection P x - jet2OfSection P y).deriv2 k l‖ ≤
      (∑ i : Fin d, ∑ j : Fin d, H0 i j) *
          ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) +
        (∑ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, H1 k i j) *
          ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) +
        (∑ k : Fin d, ∑ l : Fin d, ∑ i : Fin d, ∑ j : Fin d, H2 k l i j) *
          ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) := by
      exact add_le_add (add_le_add hval (by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k _ => hder1 k)) (by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun l _ => hder2 k l)
    _ = H * ∑ m : Fin d, |(x - y) m| ^ (1 : ℝ) := by
      dsimp [H]
      ring

/-! ## Closed-carrier transfer for the genuine matrix reaction -/

/-- Each component of the genuine matrix-valued Ricci--DeTurck reaction is
little-Hölder when its positive-time heat approximants stay in the compact
jet domain.

The proof is a vector-valued lift of the scalar carrier argument.  The
positive-time output is little-Hölder because the smoothed extracted jet has
an actual exponent-one certificate; convergence in the full `HolderBCF` norm
comes from the proved genuine matrix difference estimate. -/
theorem isGoodHolder_geometricNRDHolder_of_heat_path
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (hrange_heat : ∀ {t : ℝ}, 0 < t → ∀ x,
      jet2OfSection
          (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K)
    (i j : Fin d) :
    IsGoodHolder (geometricNRDHolder Γbg s hα0 hrange i j) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let f₀ : HolderBCF α d := geometricNRDHolder Γbg s hα0 hrange i j
  let f : ℝ → HolderBCF α d := fun t =>
    if ht : 0 < t then
      geometricNRDHolder Γbg
        (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
        hα0 (hrange_heat ht) i j
    else f₀
  have hP : Filter.Tendsto
      (fun t : ℝ =>
        jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
      l (𝓝 s) := by
    simpa [l] using jet2SectionLittleHolderPropagator_tendsto_nhdsWithin_zero
      (d := d) (α := α) s
  have hnorm : Filter.Tendsto
      (fun t : ℝ => ‖s -
        jet2SectionLittleHolderPropagator (d := d) (α := α) t s‖)
      l (𝓝 0) := by
    have h := (hP.const_sub s).norm
    simpa only [sub_self, norm_zero] using h
  have hnorm_out : Filter.Tendsto
      (fun t : ℝ => ‖f t - f₀‖) l (𝓝 0) := by
    let C : ℝ := geometricNRDHolderLipschitzConst Γbg s
    apply squeeze_zero' (g := fun t : ℝ => C * ‖s -
      jet2SectionLittleHolderPropagator (d := d) (α := α) t s‖)
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      dsimp [f, f₀]
      rw [dif_pos ht']
      calc
        ‖geometricNRDHolder Γbg
              (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
              hα0 (hrange_heat ht') i j -
            geometricNRDHolder Γbg s hα0 hrange i j‖ =
          ‖geometricNRDHolder Γbg s hα0 hrange i j -
              geometricNRDHolder Γbg
                (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
                hα0 (hrange_heat ht') i j‖ := norm_sub_rev _ _
        _ ≤ ‖geometricNRDHolder Γbg s hα0 hrange -
              geometricNRDHolder Γbg
                (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
                hα0 (hrange_heat ht')‖ := by
          change ‖(geometricNRDHolder Γbg s hα0 hrange -
              geometricNRDHolder Γbg
                (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
                hα0 (hrange_heat ht')) i j‖ ≤ _
          exact le_trans (pi_entry_norm_le _ j) (pi_entry_norm_le _ i)
        _ ≤ C * ‖s -
            jet2SectionLittleHolderPropagator (d := d) (α := α) t s‖ := by
          exact norm_geometricNRDHolder_sub_le Γbg s
            (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
            hα0 hrange (hrange_heat ht')
    · simpa [C] using hnorm.const_mul C
  have hpath : Filter.Tendsto f l (𝓝 f₀) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_out
  have hmem : ∀ᶠ t in l,
      f t ∈ (littleHolderSubmodule (n := d) (α := α)).carrier := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    change IsGoodHolder (f t)
    dsimp [f, f₀]
    rw [dif_pos ht']
    obtain ⟨H, hjet⟩ :=
      isHolderNorm_one_jet2SectionLittleHolderPropagator
        (d := d) (α := α) s ht'
    exact isGoodHolder_of_isHolderConst_one hα0 hα1
      (isHolderConst_geometricNRDHolder_of_isHolderNorm_one
        Γbg (jet2SectionLittleHolderPropagator (d := d) (α := α) t s)
        hα0 hjet (hrange_heat ht') i j)
  have hclosed : IsClosed
      (littleHolderSubmodule (n := d) (α := α)).carrier :=
    isClosed_littleHolderSubmodule
  change f₀ ∈ (littleHolderSubmodule (n := d) (α := α)).carrier
  exact hclosed.mem_of_tendsto hpath hmem

/-- The genuine matrix reaction, now packaged entrywise in the
little-Hölder space after the heat-path closure argument. -/
noncomputable def geometricNRDLittleHolderOfHeat
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (hrange_heat : ∀ {t : ℝ}, 0 < t → ∀ x,
      jet2OfSection
          (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K) :
    MatrixLittleHolder d d α :=
  Matrix.of fun i j =>
    (⟨geometricNRDHolder Γbg s hα0 hrange i j,
      isGoodHolder_geometricNRDHolder_of_heat_path
        Γbg s hα0 hα1 hrange hrange_heat i j⟩ : LittleHolder d α)

@[simp] theorem geometricNRDLittleHolderOfHeat_toHolder_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (hrange_heat : ∀ {t : ℝ}, 0 < t → ∀ x,
      jet2OfSection
          (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNRDLittleHolderOfHeat Γbg s hα0 hα1 hrange hrange_heat i j).toHolder).toBCF x =
      geometricNRD Γbg s x i j := by
  change (geometricNRDHolder Γbg s hα0 hrange i j).toBCF x = _
  exact geometricNRDHolder_apply Γbg s hα0 hrange x i j

/-- The corresponding genuine source section, with the matrix reaction in
the 0-jet slot and zero derivative slots. -/
noncomputable def geometricNLittleHolderOfHeat
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (hrange_heat : ∀ {t : ℝ}, 0 < t → ∀ x,
      jet2OfSection
          (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K) :
    Jet2Section d d α :=
  (geometricNRDLittleHolderOfHeat Γbg s hα0 hα1 hrange hrange_heat, 0, 0)

@[simp] theorem geometricNLittleHolderOfHeat_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (s : Jet2Section d d α)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hrange : ∀ x, jet2OfSection s x ∈
      (phiRDNemytskiiData (d := d) Γbg).K)
    (hrange_heat : ∀ {t : ℝ}, 0 < t → ∀ x,
      jet2OfSection
          (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNLittleHolderOfHeat Γbg s hα0 hα1 hrange hrange_heat).val i j).toHolder.toBCF x =
      geometricNRD Γbg s x i j := by
  exact geometricNRDLittleHolderOfHeat_toHolder_apply
    Γbg s hα0 hα1 hrange hrange_heat x i j

end AnalyticPDE
end RicciFlow
