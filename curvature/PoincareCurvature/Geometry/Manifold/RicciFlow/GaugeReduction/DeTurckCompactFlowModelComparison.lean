import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.GaugeFlowAssembly

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Compact gauge-flow assembly from local model comparisons

This module closes the composition boundary immediately after the chart-transfer
capstone in `GaugeFlowAssembly.lean`.  The compact-manifold ODE supplies the raw
forward and inverse slices; local model-diffeomorph comparisons supply their
spatial `C³` regularity through the existing gluing theorem.  The resulting
`Diffeomorph3GaugeFlowOn` is therefore conditional on exactly the remaining
comparison data, including continuity of each raw time slice.

No model comparison is manufactured from a `VariationalLocalFlowSolution`: the
comparison premise below asks for the stronger genuine `C³` model
diffeomorphisms and keeps the compact-flow identification explicit.
-/

open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Assemble the compact-manifold `C³` gauge flow from the raw compact flow and
the local model-diffeomorph comparison data used by the chart-transfer
capstone.

The raw flow's slice continuity and surjectivity are intentionally explicit:
they are topological inputs to the inverse-slice gluing argument, while the
model comparison package is the analytic input that produces both forward and
inverse spatial `C³` regularity. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_modelComparison
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {Xcoord : ℝ → M → E}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hcomparison : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x)
          (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      ∀ t ∈ Set.Ioo (-ε) ε,
        Continuous (Φ t) ∧
        (∀ x : M, ∃ (p : M)
          (Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E))
          (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (U : Set M),
          U ∈ 𝓝 x ∧ U ⊆ (chartAt H p).source ∧
          Set.MapsTo (Φ t) U (chartAt H p).source ∧
          t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
          (∀ τ ∈ Set.Ioo a b,
            LipschitzOnWith K (chartPushforwardField I Xcoord p τ) (state τ)) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I
              (fun σ : ℝ ↦ Φ σ y) (Set.Ioo a b) τ
              ((1 : ℝ →L[ℝ] ℝ).smulRight (Xcoord τ (Φ τ y)))) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            Φ τ y ∈ (extChartAt I p).source) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            HasDerivAt
              (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p y))
              (chartPushforwardField I Xcoord p τ
                ((Ψ τ : E → E) (extChartAt I p y))) τ) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            extChartAt I p (Φ τ y) ∈ state τ) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            (Ψ τ : E → E) (extChartAt I p y) ∈ state τ) ∧
          (∀ y ∈ U,
            extChartAt I p (Φ t₀ y) =
              (Ψ t₀ : E → E) (extChartAt I p y)))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) X
        (Set.Ioo (-ε) ε) 0) := by
  refine exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3 hX ?_
  intro ε hε Φ G hΦ0 hderiv hleft hright
  have hcomp := hcomparison ε hε Φ G hΦ0 hderiv hleft hright
  constructor
  · intro t ht
    have hmodel := (hcomp t ht).2
    exact (contMDiff_flowSlice_and_symm_of_forall_rawFlow_modelFlow_eqOn
      (I := I) (M := M) (Φ := Φ) (Gt := G t) (X := Xcoord) (t := t)
      (hcomp t ht).1 (hright t ht).surjective (hleft t ht)
      (by
        intro x
        obtain ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
          hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩ := hmodel x
        exact ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
          hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩)).1
  · intro t ht
    have hmodel := (hcomp t ht).2
    exact (contMDiff_flowSlice_and_symm_of_forall_rawFlow_modelFlow_eqOn
      (I := I) (M := M) (Φ := Φ) (Gt := G t) (X := Xcoord) (t := t)
      (hcomp t ht).1 (hright t ht).surjective (hleft t ht)
      (by
        intro x
        obtain ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
          hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩ := hmodel x
        exact ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
          hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩)).2

end PoincareCurvature.GaugeFlowAssembly
