module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Differentiability of an existing manifold inverse -/

@[expose] public noncomputable section
open scoped Manifold Topology
open Set
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [I.Boundaryless] [J.Boundaryless]

/-- An existing homeomorphic inverse is differentiable wherever the forward
map has an invertible manifold derivative. No extra smoothness is assumed. -/
theorem mdifferentiableAt_homeomorph_symm_of_equiv
    (f : M ≃ₜ N) (x : M) (e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (hf : HasMFDerivAt I J f x (e : _ →L[ℝ] _)) :
    MDifferentiableAt J I f.symm (f x) := by
  change E ≃L[ℝ] E' at e
  let F := writtenInExtChartAt I J x f
  let G := (extChartAt I x) ∘ f.symm ∘ (extChartAt J (f x)).symm
  let a := extChartAt J (f x) (f x)
  have h0 : (extChartAt J (f x)).symm a = f x :=
    (extChartAt J (f x)).left_inv (mem_extChartAt_source (f x))
  have hg0 : G a = extChartAt I x x := by
    simp only [G, Function.comp_apply, h0, f.symm_apply_apply]
  have hmid : ContinuousAt (f.symm ∘ (extChartAt J (f x)).symm) a :=
    f.symm.continuous.continuousAt.comp (continuousAt_extChartAt_symm (f x))
  have hG : ContinuousAt G a := by
    have hc : ContinuousAt (extChartAt I x)
        ((f.symm ∘ (extChartAt J (f x)).symm) a) := by
      simpa only [Function.comp_apply, h0, f.symm_apply_apply] using
        (continuousAt_extChartAt (I := I) x)
    exact hc.comp hmid
  have he : HasFDerivAt F (e : E →L[ℝ] E') (extChartAt I x x) := by
    simpa only [I.range_eq_univ, hasFDerivWithinAt_univ] using hf.2
  have he' : HasFDerivAt F (e : E →L[ℝ] E') (G a) := by rw [hg0]; exact he
  have ht : ∀ᶠ y in 𝓝 a, y ∈ (extChartAt J (f x)).target :=
    extChartAt_target_mem_nhds (f x)
  have hm : ∀ᶠ y in 𝓝 a, f.symm ((extChartAt J (f x)).symm y) ∈
      (extChartAt I x).source := by
    have hh := hmid.preimage_mem_nhds (t := (extChartAt I x).source)
    apply hh
    simpa only [Function.comp_apply, h0, f.symm_apply_apply] using extChartAt_source_mem_nhds (I := I) x
  have hfg : ∀ᶠ y in 𝓝 a, F (G y) = y := by
    filter_upwards [ht, hm] with y hy hm
    change (extChartAt J (f x)) (f ((extChartAt I x).symm
      ((extChartAt I x) (f.symm ((extChartAt J (f x)).symm y))))) = y
    rw [(extChartAt I x).left_inv hm, f.apply_symm_apply,
      (extChartAt J (f x)).right_inv hy]
  have hi := HasFDerivAt.of_local_left_inverse (f' := (e : E ≃L[ℝ] E')) hG he' hfg
  apply (mdifferentiableAt_iff _ _).mpr
  refine ⟨f.symm.continuous.continuousAt, ?_⟩
  simpa only [J.range_eq_univ, differentiableWithinAt_univ,
    writtenInExtChartAt, f.symm_apply_apply] using hi.differentiableAt

end LichnerowiczObata
