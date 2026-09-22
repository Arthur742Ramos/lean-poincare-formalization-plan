import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCompactFlowCoherentModelComparison
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Compact gauge-flow assembly from native cutoff comparisons

The analytic-PDE module already packages the concrete model-side data produced
by cutoff globalization.  This module is the adapter from that native package
to the coherent compact-flow comparison interface: the model field is the
canonical view of the same dependent geometric field, and the model
`Diffeomorph3GaugeFlowOn` supplies the `C³` comparison family and its integral
curve derivative.

The cutoff construction and orbit-graph confinement remain hypotheses.  This
separates the conversion of an existing native cutoff package from the still
open task of constructing such packages from the geometric Ricci--DeTurck
field on every compact chart patch.
-/

open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow
open RicciFlow.AnalyticPDE.SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Convert native cutoff/model-flow packages into the coherent compact-flow
comparison premise. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_coherent_cutoffComparison
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hcutoff : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x)
          (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      ∀ t ∈ Set.Ioo (-ε) ε, ∀ x : M,
        ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
          (Gmodel : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
            (X := fun τ q => χ (τ, q) •
              chartPushforwardField I
                (coherentCoordinateField (I := I) X) p τ q) sTime t₀')
          (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E)
          (Kwin : Set (ℝ × E)) (U : Set M),
        U ∈ 𝓝 x ∧ U ⊆ (chartAt H p).source ∧
        t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
        (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
        (∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) ∧
        (∀ τ ∈ Set.Ioo a b,
          LipschitzOnWith K
            (chartPushforwardField I
              (coherentCoordinateField (I := I) X) p τ) (state τ)) ∧
        (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
          HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ ↦ Φ σ y)
            (Set.Ioo a b) τ
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (coherentCoordinateField (I := I) X τ (Φ τ y)))) ∧
        (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
          Φ τ y ∈ (extChartAt I p).source) ∧
        (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
          ((τ, (Gmodel.maps3 τ) (extChartAt I p y)) : ℝ × E) ∈ Kwin) ∧
        (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
          extChartAt I p (Φ τ y) ∈ state τ) ∧
        (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
          (Gmodel.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
        (∀ y ∈ U,
          extChartAt I p (Φ t₀ y) =
            (Gmodel.maps3 t₀) (extChartAt I p y))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) X
        (Set.Ioo (-ε) ε) 0) := by
  apply exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_coherent_modelComparison
    (I := I) (M := M) (X := X) hX
  intro ε hε Φ G hΦ0 hderiv hleft hright t ht
  have hnative := hcutoff ε hε Φ G hΦ0 hderiv hleft hright t ht
  have hforward : ContMDiff I I 3 (Φ t) :=
    contMDiff_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset
      (I := I) (M := M)
      (X := coherentCoordinateField (I := I) X) (Φ := Φ) (t := t)
      hnative
  refine ⟨hforward.continuous, ?_⟩
  intro x
  obtain ⟨p, χ, sTime, t₀', Gmodel, a, b, t₀, K, state, Kwin, U,
    hUmem, hU, ht, ht₀, hnhds, hχK, hlip, hraw, hsrc, hgraph,
    hγmem, hgmem, heq₀⟩ := hnative x
  refine ⟨p, (fun τ => (Gmodel.maps3 τ : E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)),
    a, b, t₀, K, state, U, hUmem, hU, ?_, ht, ht₀, hlip, hraw, hsrc, ?_,
    hγmem, hgmem, heq₀⟩
  · intro y hy
    have hsrc' := hsrc y hy t ht
    rw [extChartAt_source] at hsrc'
    exact hsrc'
  · intro y hy τ hτ
    exact hasDerivAt_maps3_eval_of_cutoff_eqOne Gmodel (hnhds τ hτ)
      (mem_of_mem_nhds (hnhds τ hτ)) (extChartAt I p y)
      ((cutoff_eqOne_along_curve_of_graph_subset hχK (hgraph y hy)) τ hτ)

end PoincareCurvature.GaugeFlowAssembly
