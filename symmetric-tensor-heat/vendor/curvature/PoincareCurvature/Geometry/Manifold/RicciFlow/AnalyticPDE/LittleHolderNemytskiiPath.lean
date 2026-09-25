import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderNemytskiiClosure
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.NemytskiiChainRule

/-!
# Full Hölder continuity of a `C^{1,1}` Nemytskii heat path (Point 4 PDE milestone)

`LittleHolderNemytskiiClosure` isolates the two inputs needed to preserve
little Hölder regularity under a nonlinear map.  This file discharges the
full-`HolderBCF` path input under explicit global `C^{1,1}` hypotheses on a
scalar fiber map.

The proof uses the repository's quantitative Nemytskii estimate
`isHolderNorm_comp_sub`.  The heat path is little Hölder, so both the
sup-norm error and the Hölder seminorm of `S(t) f - f` tend to zero.  The
Nemytskii difference estimate then makes the corresponding full Hölder norm
tend to zero.  The derivative bound and derivative Lipschitz bound are
parameters: this records exactly what a tensor-valued Ricci--DeTurck fiber
map must later provide, without claiming that the geometric map has already
been discharged.

No `sorry`, `admit`, or axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-- Convert the scalar `HolderBCF` Hölder predicate to the normed-fiber
`IsHolderNorm` predicate used by the Nemytskii chain rule. -/
private theorem isHolderNorm_of_isHolderConst
    {u : BoundedContinuousFunction (Fin n → ℝ) ℝ} {H : ℝ}
    (hu : IsHolderConst α u H) :
    IsHolderNorm α (fun x : Fin n → ℝ => u x) H := by
  refine ⟨hu.1, fun x y => ?_⟩
  simpa [Real.norm_eq_abs] using hu.2 x y

/-- **A globally `C^{1,1}` scalar Nemytskii map is continuous along a
little-Hölder heat path in the full Hölder norm.**

The hypotheses are intentionally global.  `hF` controls the supremum
component, while `hderiv`, `hB`, and `hΦLip` feed the quantitative Hölder
difference estimate on the entire fiber. -/
theorem tendsto_holderBCF_comp_heatPropagator_of_c11
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {Φ' : ℝ → ℝ →L[ℝ] ℝ} {B : ℝ}
    (hderiv : ∀ x, HasFDerivAt F (Φ' x) x)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ x, ‖Φ' x‖ ≤ B)
    {M : ℝ≥0} (hΦLip : LipschitzWith M Φ')
    (f : LittleHolder n α) :
    Filter.Tendsto
      (fun t : ℝ => holderBCF_comp hF
        (heatPropagatorHolderCLM (n := n) (α := α) t f.val))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (holderBCF_comp hF f.val)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hprop : ∀ t : ℝ,
      heatPropagatorTotal (n := n) (α := α) t f.val =
        heatPropagatorHolderCLM (n := n) (α := α) t f.val := by
    intro t
    by_cases ht : 0 < t
    · rw [heatPropagatorTotal_of_pos ht, heatPropagatorHolderCLM_of_pos ht]
      apply Subtype.ext
      rfl
    · have htle : t ≤ 0 := le_of_not_gt ht
      rw [heatPropagatorTotal_of_nonpos ht,
        heatPropagatorHolderCLM_of_nonpos htle]
      apply Subtype.ext
      rfl
  have htotal : Filter.Tendsto
      (fun t : ℝ => heatPropagatorTotal (n := n) (α := α) t f.val)
      l (𝓝 f.val) := by
    simpa [IsGoodHolder, l] using LittleHolder.mem_iff f
  have hclm : Filter.Tendsto
      (fun t : ℝ => heatPropagatorHolderCLM (n := n) (α := α) t f.val)
      l (𝓝 f.val) :=
    htotal.congr' (Filter.Eventually.of_forall hprop)
  have hnorm : Filter.Tendsto
      (fun t : ℝ => ‖heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val‖)
      l (𝓝 0) := by
    have h := (hclm.sub_const f.val).norm
    simpa using h
  have hM : Filter.Tendsto
      (fun t : ℝ =>
        ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
          f.val.toBCF‖)
      l (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ =>
      ‖heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val‖)
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
    · filter_upwards with t
      simpa only [HolderBCF.sub_toBCF] using
        HolderBCF.norm_toBCF_le
          (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val)
    · exact hnorm
  have hsemi_input : Filter.Tendsto
      (fun t : ℝ => HolderBCF.holderSeminorm
        (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val))
      l (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun t =>
        HolderBCF.holderSeminorm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t =>
        HolderBCF.holderSeminorm_le_norm _)
    · exact hnorm
  have hsemi_heat_le : ∀ᶠ t in l,
      HolderBCF.holderSeminorm
        (heatPropagatorHolderCLM (n := n) (α := α) t f.val) ≤
        HolderBCF.holderSeminorm f.val := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [heatPropagatorHolderCLM_of_pos ht]
    exact holderSeminorm_heatSemigroupHolderFun_le ht f.val
  have hcomp_sup : Filter.Tendsto
      (fun t : ℝ => ‖(holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
        holderBCF_comp hF f.val).toBCF‖)
      l (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ =>
      (L : ℝ) * ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
        f.val.toBCF‖)
    · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
    · filter_upwards with t
      simpa only [HolderBCF.sub_toBCF] using
        norm_holderBCF_comp_sub_le hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f.val) f.val
    · simpa using hM.const_mul (L : ℝ)
  have hsemi_comp : Filter.Tendsto
      (fun t : ℝ => HolderBCF.holderSeminorm
        (holderBCF_comp hF
            (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
          holderBCF_comp hF f.val))
      l (𝓝 0) := by
    let Hf : ℝ := HolderBCF.holderSeminorm f.val
    have hbound : ∀ᶠ t in l,
        HolderBCF.holderSeminorm
          (holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
            holderBCF_comp hF f.val) ≤
          (M : ℝ) * Hf *
              ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
                f.val.toBCF‖ +
            B * HolderBCF.holderSeminorm
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val) := by
      filter_upwards [self_mem_nhdsWithin, hsemi_heat_le] with t ht hheat
      have hcomp := isHolderNorm_comp_sub
        (Φ := F) (Φ' := Φ') (K := (Set.univ : Set ℝ))
        (convex_univ : Convex ℝ (Set.univ : Set ℝ))
        (fun x _ => (hderiv x).hasFDerivWithinAt)
        hB_nonneg (fun x _ => hB x) hΦLip.lipschitzOnWith
        (isHolderNorm_of_isHolderConst
          (HolderBCF.isHolderConst_holderSeminorm
            (heatPropagatorHolderCLM (n := n) (α := α) t f.val)))
        (isHolderNorm_of_isHolderConst
          (HolderBCF.isHolderConst_holderSeminorm
            (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val)))
        (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _)
        (fun x => by
          have hx := BoundedContinuousFunction.norm_coe_le_norm
            ((heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
              f.val.toBCF) x
          simpa [BoundedContinuousFunction.sub_apply] using hx)
      have hcomp_const : IsHolderConst α
          (holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
            holderBCF_comp hF f.val).toBCF
          ((M : ℝ) *
              HolderBCF.holderSeminorm
                (heatPropagatorHolderCLM (n := n) (α := α) t f.val) *
              ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
                f.val.toBCF‖ +
            B * HolderBCF.holderSeminorm
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val)) := by
        refine ⟨hcomp.1, fun x y => ?_⟩
        have hxy := hcomp.2 x y
        change |F ((heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF x) -
            F (f.val.toBCF x) -
          (F ((heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF y) -
            F (f.val.toBCF y))| ≤ _
        exact hxy
      have hsemi_exact := csInf_le
        (HolderBCF.bddBelow_holderSet
          (holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
            holderBCF_comp hF f.val)) hcomp_const
      calc
        HolderBCF.holderSeminorm
            (holderBCF_comp hF
                (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
              holderBCF_comp hF f.val) ≤
            (M : ℝ) *
                HolderBCF.holderSeminorm
                  (heatPropagatorHolderCLM (n := n) (α := α) t f.val) *
                ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
                  f.val.toBCF‖ +
              B * HolderBCF.holderSeminorm
                (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val) :=
          hsemi_exact
        _ ≤ (M : ℝ) * Hf *
              ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
                f.val.toBCF‖ +
            B * HolderBCF.holderSeminorm
              (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hheat (NNReal.coe_nonneg M)
            · exact norm_nonneg _
          · exact le_rfl
    have hbound_limit : Filter.Tendsto
        (fun t : ℝ => (M : ℝ) * Hf *
            ‖(heatPropagatorHolderCLM (n := n) (α := α) t f.val).toBCF -
              f.val.toBCF‖ +
          B * HolderBCF.holderSeminorm
            (heatPropagatorHolderCLM (n := n) (α := α) t f.val - f.val))
        l (𝓝 0) := by
      have h₁ := hM.const_mul ((M : ℝ) * Hf)
      have h₂ := hsemi_input.const_mul B
      simpa [mul_assoc] using h₁.add h₂
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun t =>
        HolderBCF.holderSeminorm_nonneg _)
    · exact hbound
    · exact hbound_limit
  have hcomp_full : Filter.Tendsto
      (fun t : ℝ => ‖holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f.val) -
        holderBCF_comp hF f.val‖)
      l (𝓝 0) := by
    have hsum := hcomp_sup.add hsemi_comp
    simpa [HolderBCF.norm_def] using hsum
  change Filter.Tendsto
    (fun t : ℝ => holderBCF_comp hF
      (heatPropagatorHolderCLM (n := n) (α := α) t f.val))
    l (𝓝 (holderBCF_comp hF f.val))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hcomp_full

/-- **Little-Hölder closure for a global `C^{1,1}` scalar map, conditional only
on the commutator seminorm estimate.**

This is the direct composition of the full-norm path theorem above with
`isGoodHolder_comp_of_commutator_seminorm`.  It isolates the one estimate
that is still genuinely nonlinear-parabolic: vanishing of the heat/Nemytskii
commutator in the `C^α` seminorm. -/
theorem isGoodHolder_comp_of_commutator_seminorm_of_c11
    (hα : 0 < α)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {Φ' : ℝ → ℝ →L[ℝ] ℝ} {B : ℝ}
    (hderiv : ∀ x, HasFDerivAt F (Φ' x) x)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ x, ‖Φ' x‖ ≤ B)
    {M : ℝ≥0} (hΦLip : LipschitzWith M Φ')
    (f : LittleHolder n α)
    (hcomm : Filter.Tendsto
      (fun t : ℝ => HolderBCF.holderSeminorm
        (heatPropagatorHolderCLM (n := n) (α := α) t
            (holderBCF_comp hF f.val) -
          holderBCF_comp hF
            (heatPropagatorHolderCLM (n := n) (α := α) t f.val)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    IsGoodHolder (holderBCF_comp hF f.val) := by
  apply isGoodHolder_comp_of_commutator_seminorm hα hF f.val
  · exact tendsto_holderBCF_comp_heatPropagator_of_c11
      hF hderiv hB_nonneg hB hΦLip f
  · exact hcomm

end AnalyticPDE
end RicciFlow
