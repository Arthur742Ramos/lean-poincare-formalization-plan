import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCompactFlowModelComparison

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Compact gauge-flow assembly with one coherent geometric field

`DeTurckCompactFlowModelComparison.lean` deliberately exposes the compact-flow
field and the chart/model field separately so that its remaining comparison
premise cannot hide an identification.  At the repository's tangent-space
boundary, however, the model field is canonically the same field: each
`TangentSpace I x` has model fiber `E`.  This module packages that canonical
specialization, removing the possibility of supplying unrelated fields while
retaining every analytic and global comparison premise from the preceding
assembly theorem.
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

/-- The ordinary coordinate-field view of the same dependent geometric field.

This is a type-level view change, not an independently supplied vector field:
the value at `(t, x)` is the value of `X` at that same `(t, x)`, viewed in the
model fiber `E`. -/
def coherentCoordinateField
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)) :
    ℝ → M → E :=
  fun t x => X t x

@[simp] theorem coherentCoordinateField_apply
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (t : ℝ) (x : M) :
    coherentCoordinateField (I := I) X t x = X t x :=
  rfl

/-- Assemble the compact `C³` gauge flow using one coherent geometric field.

The model-comparison data are still explicit: this theorem does not construct
the compact flow's chart comparisons or the genuine model diffeomorphisms.  It
does ensure that their raw-flow derivative and Lipschitz field use the very
same `X` that drives the compact manifold flow. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_coherent_modelComparison
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
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
            LipschitzOnWith K
              (chartPushforwardField I (coherentCoordinateField (I := I) X) p τ)
              (state τ)) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I
              (fun σ : ℝ ↦ Φ σ y) (Set.Ioo a b) τ
              ((1 : ℝ →L[ℝ] ℝ).smulRight
                (coherentCoordinateField (I := I) X τ (Φ τ y)))) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            Φ τ y ∈ (extChartAt I p).source) ∧
          (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
            HasDerivAt
              (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p y))
              (chartPushforwardField I
                (coherentCoordinateField (I := I) X) p τ
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
  exact exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_modelComparison
    (I := I) (M := M) (X := X)
    (Xcoord := coherentCoordinateField (I := I) X) hX hcomparison

end PoincareCurvature.GaugeFlowAssembly
