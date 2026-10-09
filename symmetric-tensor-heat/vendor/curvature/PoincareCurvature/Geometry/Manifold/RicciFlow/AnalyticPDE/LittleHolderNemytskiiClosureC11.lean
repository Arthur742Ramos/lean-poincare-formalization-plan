import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderNemytskiiPath

/-!
# Little-Hölder closure for a scalar `C^{1,1}` Nemytskii map (Point 4 PDE milestone)

This file closes the scalar composition step left open by the earlier
commutator interface.  At every positive heat time, the Euclidean heat
semigroup is globally Lipschitz in space.  A globally Lipschitz fiber map
therefore sends that smoothed datum to a globally Lipschitz, hence
little-Hölder, datum.  The `C^{1,1}` path theorem gives convergence in the
full `HolderBCF` norm as the heat time tends to zero, and the closedness of the
little-Hölder carrier passes the limit to the unsmoothed composition.

The result is scalar and global.  It does not claim the corresponding
tensorial Ricci--DeTurck endomap or the parabolic estimates needed to obtain
the geometric hypotheses.

No `sorry`, `admit`, or axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Spatial smoothing gives a coordinatewise Lipschitz certificate -/

/-- A spatially Lipschitz bounded continuous function is `IsHolderConst` with
exponent one.  The domain norm is bounded by the coordinatewise `ℓ¹` sum used
by the repository's Hölder predicate. -/
private theorem isHolderConst_one_of_lipschitzWith
    {g : BoundedContinuousFunction (Fin n → ℝ) ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K (fun x => g x)) :
    IsHolderConst (1 : ℝ) g (K : ℝ) := by
  refine ⟨K.coe_nonneg, fun x y => ?_⟩
  have hxy := hg.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hxy
  have hsum : 0 ≤ ∑ k : Fin n, |(x - y) k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg ((x - y) k))
  have hnorm_le_sum : ‖x - y‖ ≤ ∑ k : Fin n, |(x - y) k| := by
    refine (pi_norm_le_iff_of_nonneg hsum).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun k _ => abs_nonneg ((x - y) k))
      (Finset.mem_univ i)
  calc
    |g x - g y| ≤ (K : ℝ) * ‖x - y‖ := hxy
    _ ≤ (K : ℝ) * ∑ k : Fin n, |(x - y) k| :=
      mul_le_mul_of_nonneg_left hnorm_le_sum K.coe_nonneg
    _ = (K : ℝ) * ∑ k : Fin n, |(x - y) k| ^ (1 : ℝ) := by
      simp [Real.rpow_one]

/-! ## 2. Closedness transfers the smoothed little-Hölder approximation -/

/-- **A global `C^{1,1}` scalar Nemytskii map preserves little Hölder data.**

The proof uses only positive-time heat smoothing, the full-norm path theorem
`tendsto_holderBCF_comp_heatPropagator_of_c11`, and the closed little-Hölder
submodule.  Thus the theorem supplies the scalar closure statement without
assuming a separate heat/Nemytskii commutator estimate. -/
theorem isGoodHolder_comp_of_c11
    (hα0 : 0 < α) (hα1 : α < 1)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {Φ' : ℝ → ℝ →L[ℝ] ℝ} {B : ℝ}
    (hderiv : ∀ x, HasFDerivAt F (Φ' x) x)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ x, ‖Φ' x‖ ≤ B)
    {M : ℝ≥0} (hΦLip : LipschitzWith M Φ')
    (f : LittleHolder n α) :
    IsGoodHolder (holderBCF_comp hF f.val) := by
  have hclosed : IsClosed (littleHolderSubmodule (n := n) (α := α)).carrier :=
    isClosed_littleHolderSubmodule
  have hpath := tendsto_holderBCF_comp_heatPropagator_of_c11
    hF hderiv hB_nonneg hB hΦLip f
  have hmem : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f.val) ∈
        (littleHolderSubmodule (n := n) (α := α)).carrier := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    change IsGoodHolder (holderBCF_comp hF
      (heatPropagatorHolderCLM (n := n) (α := α) t f.val))
    rw [heatPropagatorHolderCLM_of_pos ht']
    change IsGoodHolder (holderBCF_comp hF
      (heatSemigroupHolderFun (n := n) (α := α) ht' f.val))
    let K : ℝ :=
      (((n : ℝ) * (‖f.val.toBCF‖ / Real.sqrt (Real.pi * t))).toNNReal : ℝ)
    have hC : ∀ y : Fin n → ℝ,
        ‖f.val.toBCF y‖ ≤ ‖f.val.toBCF‖ := fun y =>
      BoundedContinuousFunction.norm_coe_le_norm f.val.toBCF y
    have hspatial : LipschitzWith
        (((n : ℝ) * (‖f.val.toBCF‖ / Real.sqrt (Real.pi * t))).toNNReal)
        (fun x : Fin n → ℝ => heatSemigroupND t f.val.toBCF x) :=
      heatSemigroupND_lipschitzWith_spatial ht'
        f.val.toBCF.continuous.aestronglyMeasurable hC
    have hspatial_bcf : LipschitzWith
        (((n : ℝ) * (‖f.val.toBCF‖ / Real.sqrt (Real.pi * t))).toNNReal)
        (fun x : Fin n → ℝ => heatSemigroupNDbcf ht' f.val.toBCF x) := by
      simpa only [heatSemigroupNDbcf_apply] using hspatial
    have hholder : IsHolderConst (1 : ℝ)
        (heatSemigroupNDbcf ht' f.val.toBCF)
        K := by
      dsimp [K]
      exact isHolderConst_one_of_lipschitzWith hspatial_bcf
    refine isGoodHolder_of_isHolderConst_one
      (L₁ := (L : ℝ) * K) hα0 hα1 ?_
    change IsHolderConst (1 : ℝ)
      ((heatSemigroupHolderFun (n := n) (α := α) ht' f.val).toBCF.comp F hF)
        ((L : ℝ) * K)
    apply isHolderConst_comp_of_lipschitz (α := (1 : ℝ)) hF
    rw [heatSemigroupHolderFun_toBCF ht']
    exact hholder
  change holderBCF_comp hF f.val ∈
    (littleHolderSubmodule (n := n) (α := α)).carrier
  exact hclosed.mem_of_tendsto hpath hmem

end AnalyticPDE
end RicciFlow
