import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCompactFlowCutoffComparison
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Compact gauge-flow existence from a jointly regular geometric field

This module composes the existing finite chart-ball globalization with the
compact raw inverse flow and the paired cutoff/model comparison gluer.  The
ordinary chart field is always `coherentCoordinateField X`, the canonical view
of the one dependent field `X` used by the compact flow.

The result is deliberately conditional on the genuine joint intrinsic
space-time smoothness of that field.  It does not infer this premise from
slicewise metric or connection families, and it does not assert the Ricci-flow
PDE or the geometric construction of `X`.
-/

open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow
open RicciFlow.AnalyticPDE.SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Construct the compact `C³` gauge flow from one jointly smooth dependent
geometric field.

All chart, cutoff, model-flow, orbit-confinement, and inverse-slice data are
constructed by the existing finite-cover and cutoff globalization theorems.
The only field-level premise is the displayed joint intrinsic smoothness. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_joint_coherent_field
    [I.Boundaryless] [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hXfield : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun r : ℝ × M =>
        (⟨r.2, coherentCoordinateField (I := I) X r.1 r.2⟩ : TangentBundle I M))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) X
        (Set.Ioo (-ε) ε) 0) := by
  have hXrawCoord :
      ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
        (fun q : ℝ × M => (⟨q, ((1 : ℝ),
          coherentCoordinateField (I := I) X q.1 q.2)⟩ :
          TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) :=
    PoincareCurvature.ManifoldFlow.contMDiff_spaceTimeField_of_contMDiff_tangentSection
      (hXfield.of_le (by exact_mod_cast le_top))
  have hXraw :
      ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
        (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
          TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) := by
    simpa [coherentCoordinateField] using hXrawCoord
  obtain ⟨ι, hιfin, p, U, Q_M, ρ, hopen, hcover, hU, hUQ, hQ_M,
      hQ_M_src, hρpos, hball, hQ_ball⟩ :=
    exists_finite_chart_ball_cover_compact (I := I) (M := M)
  haveI : Finite ι := hιfin
  have hXchart : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun r : ℝ × M =>
        (⟨r.2, coherentCoordinateField (I := I) X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I (p i)).source) := by
    intro i
    exact hXfield.contMDiffOn
  have hwinex : ∀ i, ∃ Kwin : Set (ℝ × E), IsCompact Kwin ∧
      Kwin ⊆ Set.univ ×ˢ (extChartAt I (p i)).target ∧
      (∀ x ∈ Q_M i, ((0 : ℝ), extChartAt I (p i) x) ∈ interior Kwin) := by
    intro i
    exact exists_compact_window_of_compact_patch (hQ_M i) (hQ_M_src i)
  choose Kwin hKwinCpt hKwinSub hplaceWin using hwinex
  have hcutex : ∀ i, ∃ χ : ℝ × E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Set.univ ×ˢ (extChartAt I (p i)).target ∧
      (∀ᶠ r in 𝓝ˢ (Kwin i), χ r = 1) ∧ ∀ r, χ r ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact exists_contDiff_cutoff_one_nhdsSet_of_isCompact (n := (⊤ : ℕ∞))
      (hKwinCpt i) (isOpen_univ.prod (isOpen_extChartAt_target (I := I) (p i)))
      (hKwinSub i)
  choose χ hχC hχc hsub hcut _hχIcc using hcutex
  let state₀ : ι → Set E := fun i =>
    Metric.ball (extChartAt I (p i) (p i)) (ρ i)
  have hstate : ∀ i, IsOpen (state₀ i) := fun i => Metric.isOpen_ball
  have hplaceState : ∀ i, ∀ x ∈ Q_M i, extChartAt I (p i) x ∈ state₀ i := by
    intro i x hx
    exact hQ_ball i x hx
  have hlipex : ∀ i, ∃ K : NNReal, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      LipschitzOnWith K
        (chartPushforwardField I
          (coherentCoordinateField (I := I) X) (p i) t) (state₀ i) := by
    intro i
    exact exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball
        (I := I) (M := M) (X := coherentCoordinateField (I := I) X)
        (p := p i) (a := -1) (b := 1) (hXfield.contMDiffOn) (by simp)
        (hball i)
  choose K hK using hlipex
  refine exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3
    (I := I) (M := M) (X := X) hXraw ?_
  intro ε hε Φ G hΦ0 hderiv hleft hright
  have hrawex : ∀ i, ∃ a₁ b₁ : ℝ, (0 : ℝ) ∈ Set.Ioo a₁ b₁ ∧
      (∀ x ∈ Q_M i, ∀ τ ∈ Set.Ioo a₁ b₁,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x)
          (Set.Ioo a₁ b₁) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x)))) ∧
      (∀ τ ∈ Set.Ioo a₁ b₁,
        (∀ x ∈ Q_M i, Φ τ x ∈ (extChartAt I (p i)).source) ∧
        (∀ x ∈ Q_M i,
          ((τ, extChartAt I (p i) (Φ τ x)) : ℝ × E) ∈
            (Set.univ ×ˢ state₀ i))) := by
    intro i
    exact exists_timeDependent_flow_compact_extChartAt_source_and_mem_of_flow
      (I := I) (M := M) (X := X) hXraw hε hΦ0 hderiv
      (Q := Q_M i) (p := p i) (W := Set.univ ×ˢ state₀ i)
      (hQ_M i) (hQ_M_src i) (isOpen_univ.prod (hstate i))
      (fun x hx => ⟨Set.mem_univ _, hplaceState i x hx⟩)
  choose a₁ b₁ hraw0 hraw hrawConf using hrawex
  have hmodelex : ∀ i, ∃ (Gmodel :
      RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
        (X := fun τ q => χ i (τ, q) •
          chartPushforwardField I
            (coherentCoordinateField (I := I) X) (p i) τ q) Set.univ 0),
      ∃ a₂ b₂ : ℝ, (0 : ℝ) ∈ Set.Ioo a₂ b₂ ∧
        (∀ q ∈ extChartAt I (p i) '' Q_M i, ∀ τ ∈ Set.Ioo a₂ b₂,
          χ i (τ, (Gmodel.maps3 τ) q) = 1) ∧
        (∀ q ∈ extChartAt I (p i) '' Q_M i, ∀ τ ∈ Set.Ioo a₂ b₂,
          (Gmodel.maps3 τ) q ∈ state₀ i) := by
    intro i
    exact exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem
      (I := I) (M := M)
      (X := coherentCoordinateField (I := I) X) (p := p i)
      (hXchart i) (hχC i) (hχc i) (hsub i)
      (by
        exact WithTop.coe_le_coe.2 (le_top : (4 : ℕ∞) ≤ (⊤ : ℕ∞))) (0 : ℝ)
      (isCompact_extChartAt_image (hQ_M i) (hQ_M_src i)) (hcut i)
      (hstate i)
      (fun q hq => by
        obtain ⟨x, hx, rfl⟩ := hq
        exact hplaceWin i x hx)
      (fun q hq => by
        obtain ⟨x, hx, rfl⟩ := hq
        exact hplaceState i x hx)
  choose Gmodel a₂ b₂ hmodel0 hχmodel hgmodel using hmodelex
  let a : ι → ℝ := fun i => max (max (max (a₁ i) (a₂ i)) (-1)) (-ε)
  let b : ι → ℝ := fun i => min (min (min (b₁ i) (b₂ i)) 1) ε
  let t₀ : ι → ℝ := fun _ => 0
  let state : ι → ℝ → Set E := fun i _ => state₀ i
  let Ψ : ι → ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E) := fun i τ =>
    (Gmodel i).maps3 τ
  have hab0 : ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i) := by
    intro i
    dsimp [a, b]
    exact ⟨max_lt (max_lt (max_lt (hraw0 i).1 (hmodel0 i).1) (by norm_num))
        (neg_lt_zero.mpr hε),
      lt_min (lt_min (lt_min (hraw0 i).2 (hmodel0 i).2) (by norm_num)) hε⟩
  have ht₀ : ∀ i, t₀ i ∈ Set.Ioo (a i) (b i) := by
    simpa [t₀] using hab0
  have hsubRaw : ∀ i, Set.Ioo (a i) (b i) ⊆ Set.Ioo (a₁ i) (b₁ i) := by
    intro i
    dsimp [a, b]
    exact Set.Ioo_subset_Ioo
      ((le_max_left (a₁ i) (a₂ i)).trans
        ((le_max_left _ _).trans (le_max_left _ _)))
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsubModel : ∀ i, Set.Ioo (a i) (b i) ⊆ Set.Ioo (a₂ i) (b₂ i) := by
    intro i
    dsimp [a, b]
    exact Set.Ioo_subset_Ioo
      ((le_max_right (a₁ i) (a₂ i)).trans
        ((le_max_left _ _).trans (le_max_left _ _)))
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsubBound : ∀ i, Set.Ioo (a i) (b i) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro i
    dsimp [a, b]
    intro τ hτ
    have hlow : (-1 : ℝ) ≤
        max (max (max (a₁ i) (a₂ i)) (-1)) (-ε) :=
      (le_max_right (max (a₁ i) (a₂ i)) (-1)).trans
        (le_max_left (max (max (a₁ i) (a₂ i)) (-1)) (-ε))
    have hupp : min (min (min (b₁ i) (b₂ i)) 1) ε ≤ (1 : ℝ) :=
      (min_le_left (min (min (b₁ i) (b₂ i)) 1) ε).trans
        (min_le_right (min (b₁ i) (b₂ i)) 1)
    exact ⟨hlow.trans (le_of_lt hτ.1), (le_of_lt hτ.2).trans hupp⟩
  have hsubFlow : ∀ i, Set.Ioo (a i) (b i) ⊆ Set.Ioo (-ε) ε := by
    intro i
    dsimp [a, b]
    exact Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hΦsurj : ∀ t ∈ Set.Ioo (-ε) ε, Function.Surjective (Φ t) := by
    intro t ht
    exact (hright t ht).surjective
  have hGleft : ∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t) :=
    hleft
  have hGleftPatch : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), ∀ x ∈ U i,
      G t (Φ t x) = x := by
    intro i t ht x hx
    exact hleft t (hsubFlow i ht) x
  have hΦU : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i),
      Set.MapsTo (Φ t) (U i) (chartAt H (p i)).source := by
    intro i t ht x hx
    have hsrc := (hrawConf i t (hsubRaw i ht)).1 x (hUQ i hx)
    rw [extChartAt_source] at hsrc
    exact hsrc
  have hlip : ∀ i, ∀ τ ∈ Set.Ioo (a i) (b i),
      LipschitzOnWith (K i)
        (chartPushforwardField I (coherentCoordinateField (I := I) X) (p i) τ)
        (state i τ) := by
    intro i τ hτ
    exact hK i τ (hsubBound i hτ)
  have hrawCmp : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x)
        (Set.Ioo (a i) (b i)) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (coherentCoordinateField (I := I) X τ (Φ τ x))) := by
    intro i x hx τ hτ
    exact (hraw i x (hUQ i hx) τ (hsubRaw i hτ)).mono (hsubRaw i)
  have hsrcCmp : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      Φ τ x ∈ (extChartAt I (p i)).source := by
    intro i x hx τ hτ
    exact (hrawConf i τ (hsubRaw i hτ)).1 x (hUQ i hx)
  have hg' : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasDerivAt (fun τ : ℝ => (Ψ i τ : E → E) (extChartAt I (p i) x))
        (chartPushforwardField I (coherentCoordinateField (I := I) X) (p i) τ
          ((Ψ i τ : E → E) (extChartAt I (p i) x))) τ := by
    intro i x hx τ hτ
    have hq : extChartAt I (p i) x ∈ extChartAt I (p i) '' Q_M i :=
      ⟨x, hUQ i hx, rfl⟩
    exact hasDerivAt_maps3_eval_of_cutoff_eqOne (Gmodel i)
      Filter.univ_mem (Set.mem_univ τ) (extChartAt I (p i) x)
      (hχmodel i (extChartAt I (p i) x) hq τ (hsubModel i hτ))
  have hγmem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      extChartAt I (p i) (Φ τ x) ∈ state i τ := by
    intro i x hx τ hτ
    exact ((hrawConf i τ (hsubRaw i hτ)).2 x (hUQ i hx)).2
  have hgmem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      (Ψ i τ : E → E) (extChartAt I (p i) x) ∈ state i τ := by
    intro i x hx τ hτ
    have hq : extChartAt I (p i) x ∈ extChartAt I (p i) '' Q_M i :=
      ⟨x, hUQ i hx, rfl⟩
    exact hgmodel i (extChartAt I (p i) x) hq τ (hsubModel i hτ)
  have heq₀ : ∀ i, ∀ x ∈ U i,
      extChartAt I (p i) (Φ (t₀ i) x) =
        (Ψ i (t₀ i) : E → E) (extChartAt I (p i) x) := by
    intro i x hx
    exact extChartAt_flow_eq_maps3_at_zero (I := I) (Gmodel i) hΦ0 x
  exact exists_flowSlicesC3Pair_of_comparison_finite_cover_of_flow_of_surj_left
    (I := I) (M := M) (Φ := Φ) (G := G) (Ψ := Ψ) (p := p)
    (X := coherentCoordinateField (I := I) X) (a := a) (b := b) (t₀ := t₀)
    (K := K) (state := state) (U := U) (lo := -ε) (hi := ε)
    ⟨neg_lt_zero.mpr hε, hε⟩ hopen hcover hΦsurj hGleft hab0 ht₀ hU hΦU
    hlip hrawCmp hsrcCmp hg' hγmem hgmem heq₀ hGleftPatch

end PoincareCurvature.GaugeFlowAssembly
