module

public import LichnerowiczObata.UniformChartODE
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-! # Uniform local manifold ODE intervals

The chart-lifting calculation follows Mathlib's
`exists_isMIntegralCurveAt_of_contMDiffAt`, by Winston Yin, at Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Here the chart-domain control and
time interval hold uniformly for nearby initial points.
-/

@[expose] public noncomputable section
open Function Manifold Set
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]

set_option backward.isDefEq.respectTransparency false in
/-- A common existence interval for all initial points in a neighborhood. -/
theorem exists_uniform_manifold_ode {v : Π x : M, TangentSpace I x} {x : M}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)) x) :
    ∃ V ∈ 𝓝 x, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ V, ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Metric.ball 0 δ) := by
  let φ := extChartAt I x
  let w : E → E := fun z => tangentCoordChange I (φ.symm z) x (φ.symm z) (v (φ.symm z))
  rw [contMDiffAt_iff] at hv
  have hw : ContDiffAt ℝ 1 w (φ x) := by
    exact (hv.2.contDiffAt (by simp [I.range_eq_univ])).snd
  have htarget : φ.target ∈ 𝓝 (φ x) :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds (φ.map_source (mem_extChartAt_source x))
  obtain ⟨W, hW, δ, hδ, hsol⟩ := exists_uniform_chart_ode hw htarget
  let V := φ.source ∩ φ ⁻¹' W
  have hV : V ∈ 𝓝 x :=
    Filter.inter_mem ((isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x))
      ((continuousAt_extChartAt (I := I) x) hW)
  refine ⟨V, hV, δ, hδ, ?_⟩
  intro y hy
  obtain ⟨f, hf0, hf⟩ := hsol (φ y) hy.2
  refine ⟨φ.symm ∘ f, ?_, ?_⟩
  · simp only [Function.comp_apply, hf0, φ.left_inv hy.1]
  · intro t ht
    let z : M := φ.symm (f t)
    have h : HasDerivAt f (tangentCoordChange I z x z (v z)) t := (hf t ht).2
    have hf3' : f t ∈ φ.target := (hf t ht).1
    have hft1 : z ∈ φ.source := φ.map_target hf3'
    have hft2 := mem_extChartAt_source (I := I) z
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I z ∘ φ.symm) ∘ f) (v z) t
    rw [← tangentCoordChange_self (I := I) (x := z) (z := z) (v := v z) hft2,
      ← tangentCoordChange_comp (x := x) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by simp [I.range_eq_univ])
    rw [← φ.right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- Compactness turns local uniform intervals into one interval valid for
every initial point of the manifold. -/
theorem exists_uniform_compact_manifold_ode [CompactSpace M]
    {v : Π x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : M, ∃ γ : ℝ → M,
      γ 0 = y ∧ IsMIntegralCurveOn γ v (Metric.ball 0 δ) := by
  classical
  choose V hV δ hδ hsol using fun x => exists_uniform_manifold_ode (hv x)
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover V hV
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε ≤ δ x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨ε, hε, he⟩ := ih
      refine ⟨min ε (δ x), lt_min hε (hδ x), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he y hy)
  obtain ⟨ε, hε, he⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro y
  have hy : y ∈ ⋃ x ∈ s, V x := by rw [hs]; trivial
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp hy
  obtain ⟨γ, hγ0, hγ⟩ := hsol x y hyx
  exact ⟨γ, hγ0, hγ.mono (Metric.ball_subset_ball (he x hxs))⟩

/-- Every C1 vector field on a compact boundaryless Hausdorff manifold is
complete. The uniform time bound is proved above, not an extra hypothesis. -/
theorem exists_global_integralCurve_compact [CompactSpace M] [T2Space M]
    {v : Π x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨δ, hδ, hsol⟩ := exists_uniform_compact_manifold_ode hv
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hδ _ x
  intro y
  obtain ⟨γ, hγ0, hγ⟩ := hsol y
  refine ⟨γ, hγ0, ?_⟩
  simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hγ

end LichnerowiczObata
