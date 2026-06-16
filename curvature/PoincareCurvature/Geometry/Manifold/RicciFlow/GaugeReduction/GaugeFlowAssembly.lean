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

end PoincareCurvature.GaugeFlowAssembly
