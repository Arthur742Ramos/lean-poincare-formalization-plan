/-
Gauge-flow assembly toward the compact-manifold C³ gauge-flow existence
(roadmap point 4, Item 2).

This module re-exposes the project's raw `C³` gauge-flow adapter
`Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt` in a clean form,
isolating the exact data needed to inhabit `Diffeomorph3GaugeFlowOn`:

* mutually inverse, spatially-`C³` time-slice maps `F`, `G : ℝ → M → M`
  (`G t` is the spatial inverse of the diffeomorphism `F t`, NOT a backward
  time-flow — confirmed by the adapter's per-slice `LeftInverse`/`RightInverse`
  hypotheses);
* anchoring `F t₀ = id`;
* the forward family `τ ↦ F τ x` solving the gauge ODE
  (`HasMFDerivWithinAt … ((1).smulRight (X t (F t x)))`).

The `hderiv` field is exactly the manifold time-derivative that the autonomization
bridge in `ManifoldFlowExistence.lean`
(`isTimeDependentIntegralCurve_of_autonomous`) produces from an integral curve of
`(1, X)` on `ℝ × M`. The mutual-inverse data follows from the flow group law
(`flow_inverse_package`). The single genuinely-remaining analytic obligation is the
**spatial `C³` regularity of the flow map** `x ↦ F t x` (smooth dependence of the
ODE flow on the initial condition, `hF`/`hG`) — the project's `ModelGaugeFlowODE.lean`
already proves spatial `C¹` (Fréchet) differentiability, so this is a `C¹ → C³`
bootstrap, not a from-scratch development.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence

open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- **Gauge-flow from flow data.** Given mutually inverse spatially-`C³` time-slice
maps `F`, `G`, anchoring at `t₀`, and the pointwise within-time-set manifold ODE
derivative equation for the forward family, the raw `C³` DeTurck gauge-flow
`Diffeomorph3GaugeFlowOn` is inhabited.

This is the reduction target for Item 2: with the autonomization bridge supplying
`hderiv` and the flow group law supplying the mutual inverses, the only remaining
input is the spatial-`C³` regularity `hF`/`hG` of the flow map. -/
theorem gaugeFlow_of_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hderiv

/-- **Global-`ℝ` extension of a windowed inverse flow to the `C³` gauge-flow datum.**

The compact-manifold time-dependent flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`) produces mutually inverse, anchored
slice maps `Φ`, `G` solving the gauge ODE only on a *window* `Ioo (-ε) ε`, whereas the adapter
`gaugeFlow_of_inverse_flow` wants the mutual-inverse / spatial-`C³` data for *every* `t : ℝ`.
Extending both families by the identity outside the window closes that `∀ t`-gap: the extended
slices stay mutually inverse (`id` is its own inverse), spatially `C³` (`id` is smooth), anchored,
and — since the extension agrees with `Φ` on the window — solve the *same* gauge ODE on
`Ioo (-ε) ε` (`HasMFDerivWithinAt.congr_mono`).  This is the pure windowed → global assembly step
in the compact-manifold gauge-flow lift; the only remaining Item-2 analytic input is the
spatial-`C³` regularity `hΦC3`/`hGC3` of the *windowed* slices (the `C¹ → C³` bootstrap). -/
theorem exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {ε : ℝ} (hε : 0 < ε)
    (Φ G : ℝ → M → M)
    (hanchor : ∀ x : M, Φ 0 x = x)
    (hΦC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (Φ t))
    (hGC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (G t))
    (hleft : ∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t))
    (hright : ∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t))
    (hderiv : ∀ x : M, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  classical
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  refine gaugeFlow_of_inverse_flow (X := X) (s := Set.Ioo (-ε) ε) (t₀ := 0)
    (fun t => if t ∈ Set.Ioo (-ε) ε then Φ t else id)
    (fun t => if t ∈ Set.Ioo (-ε) ε then G t else id)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hleft t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hright t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hΦC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hGC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro x
    simp only [if_pos h0mem]; exact hanchor x
  · intro t ht x
    simp only []
    rw [if_pos ht]
    refine (hderiv x t ht).congr_mono ?_ ?_ (subset_refl _)
    · intro τ hτ; simp only [if_pos hτ]
    · simp only [if_pos ht]

end PoincareCurvature.GaugeFlowAssembly
