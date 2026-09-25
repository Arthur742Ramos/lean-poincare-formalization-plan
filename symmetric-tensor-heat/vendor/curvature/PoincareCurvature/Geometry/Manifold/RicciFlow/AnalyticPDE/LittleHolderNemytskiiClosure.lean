import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatSemigroupCommutator

/-!
# Little-Hölder closure contract for a Nemytskii map (Point 4 PDE milestone)

The heat-semigroup definition of little Hölder regularity makes the nonlinear
closure step completely explicit.  For a scalar Lipschitz map `F`, write

`S t (F ∘ f) - F ∘ (S t f)`

for the heat/Nemytskii commutator.  The identity

`S t (F ∘ f) - F ∘ f`
`= (S t (F ∘ f) - F ∘ (S t f)) + (F ∘ (S t f) - F ∘ f)`

shows that two estimates are sufficient:

* the commutator must converge to zero in the Hölder seminorm, and
* the Nemytskii path `F ∘ (S t f)` must converge to `F ∘ f` in the full
  Hölder norm.

This file proves the resulting closure theorem, including the full norm
decomposition.  It deliberately keeps both analytic inputs as hypotheses:
`HeatSemigroupCommutator` currently proves only the commutator's sup-norm
vanishing, while the full `C^α` seminorm estimate is the next analytic gate.
Likewise, the theorem does not silently turn a merely Lipschitz map into a
`C^{1,1}` Nemytskii estimate; the full-norm path continuity is supplied by
the eventual composition module.

No `sorry`, `admit`, or axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-- **Little-Hölder Nemytskii closure from the two exact analytic inputs.**

For a Lipschitz scalar map `F`, assume that the composed heat path is
continuous in the full `HolderBCF` norm and that the heat/Nemytskii
commutator has vanishing `C^α` seminorm.  Together with the already proved
sup-norm commutator convergence, these hypotheses imply that `F ∘ f` is
little Hölder.

The statement exposes the actual remaining PDE obligations rather than
assuming an endomorphism of `LittleHolder` outright. -/
theorem isGoodHolder_comp_of_commutator_seminorm
    (hα : 0 < α)
    {F : ℝ → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (f : HolderBCF α n)
    (hcomp : Filter.Tendsto
      (fun t : ℝ => holderBCF_comp hF
        (heatPropagatorHolderCLM (n := n) (α := α) t f))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (holderBCF_comp hF f)))
    (hcomm : Filter.Tendsto
      (fun t : ℝ => HolderBCF.holderSeminorm
        (heatPropagatorHolderCLM (n := n) (α := α) t
            (holderBCF_comp hF f) -
          holderBCF_comp hF
            (heatPropagatorHolderCLM (n := n) (α := α) t f)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    IsGoodHolder (holderBCF_comp hF f) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hsup : Filter.Tendsto
      (fun t : ℝ => ‖(heatPropagatorHolderCLM (n := n) (α := α) t
          (holderBCF_comp hF f) -
        holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f)).toBCF‖)
      l (𝓝 0) := by
    have h := commutator_sup_tendsto_zero hα hF f
    simpa [l] using h.congr' (Filter.Eventually.of_forall (fun t => by
      rw [← HolderBCF.sub_toBCF]
      rfl))
  have hcomm_norm : Filter.Tendsto
      (fun t : ℝ => ‖heatPropagatorHolderCLM (n := n) (α := α) t
          (holderBCF_comp hF f) -
        holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f)‖)
      l (𝓝 0) := by
    have hcomm' : Filter.Tendsto
        (fun t : ℝ => HolderBCF.holderSeminorm
          (heatPropagatorHolderCLM (n := n) (α := α) t
              (holderBCF_comp hF f) -
            holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f)))
        l (𝓝 0) := by
      simpa [l] using hcomm
    have hsum := hsup.add hcomm'
    simpa [HolderBCF.norm_def] using hsum
  have hcomp_norm : Filter.Tendsto
      (fun t : ℝ => ‖holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f) -
        holderBCF_comp hF f‖)
      l (𝓝 0) := by
    have hcomp' : Filter.Tendsto
        (fun t : ℝ => holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f))
        l (𝓝 (holderBCF_comp hF f)) := by
      simpa [l] using hcomp
    have h := hcomp'.sub_const (holderBCF_comp hF f)
    have hnorm := h.norm
    simpa using hnorm
  have htotal : Filter.Tendsto
      (fun t : ℝ => ‖heatPropagatorHolderCLM (n := n) (α := α) t
          (holderBCF_comp hF f) - holderBCF_comp hF f‖)
      l (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ =>
      ‖heatPropagatorHolderCLM (n := n) (α := α) t
          (holderBCF_comp hF f) -
        holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f)‖ +
      ‖holderBCF_comp hF
          (heatPropagatorHolderCLM (n := n) (α := α) t f) -
        holderBCF_comp hF f‖)
    · exact Filter.Eventually.of_forall (fun t =>
      norm_nonneg (heatPropagatorHolderCLM (n := n) (α := α) t
        (holderBCF_comp hF f) - holderBCF_comp hF f))
    · filter_upwards with t
      have heq : heatPropagatorHolderCLM (n := n) (α := α) t
            (holderBCF_comp hF f) - holderBCF_comp hF f =
          (heatPropagatorHolderCLM (n := n) (α := α) t
              (holderBCF_comp hF f) -
            holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f)) +
          (holderBCF_comp hF
              (heatPropagatorHolderCLM (n := n) (α := α) t f) -
            holderBCF_comp hF f) := by
        abel
      rw [heq]
      exact norm_add_le _ _
    · simpa only [add_zero] using hcomm_norm.add hcomp_norm
  have hCLM : Filter.Tendsto
      (fun t : ℝ => heatPropagatorHolderCLM (n := n) (α := α) t
        (holderBCF_comp hF f))
      l (𝓝 (holderBCF_comp hF f)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using htotal)
  have hprop : ∀ t : ℝ,
      heatPropagatorTotal (n := n) (α := α) t (holderBCF_comp hF f) =
        heatPropagatorHolderCLM (n := n) (α := α) t
          (holderBCF_comp hF f) := by
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
  unfold IsGoodHolder
  change Filter.Tendsto
    (fun t : ℝ => heatPropagatorTotal (n := n) (α := α) t
      (holderBCF_comp hF f)) l (𝓝 (holderBCF_comp hF f))
  exact hCLM.congr' (Filter.Eventually.of_forall (fun t => (hprop t).symm))

end AnalyticPDE
end RicciFlow
