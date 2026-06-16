/-
Manifold integral-curve existence scaffolding toward the compact-manifold
gauge-flow construction (roadmap point 4, Item 2).

This module assembles the mathlib integral-curve API into the exact shapes the
gauge-flow construction consumes:

* `exists_local_integralCurve_Ioo` — per-point local existence of an integral
  curve on an open interval `Ioo (-ε) ε`, in the precise shape the globalization
  lemma wants;
* `exists_perpoint_integralCurve_time` — the per-point existence time on a
  compact boundaryless manifold (each point gets its own `εₓ`);
* `exists_global_integralCurve_of_uniform` — globalization: a *uniform* existence
  time immediately yields a global integral curve through every point.

The remaining gap to a *uniform* existence time (a single `ε` for all start
points) is the manifold "flow box" — continuous dependence of integral curves on
the initial point. Mathlib v4.29.1 provides this only at the Banach-space level
(`PicardLindelof`), not lifted to the manifold `IsMIntegralCurveOn` API; supplying
that neighborhood-uniform local existence lemma is the precise next increment.
-/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Topology.Compactness.Compact

open scoped Manifold Topology
open Set Filter

namespace PoincareCurvature.ManifoldFlow

/-- **Per-point local integral curve in `Ioo` shape.** For a `C¹` vector field `v`
on a boundaryless complete manifold, every point `x₀` admits some `ε > 0` and an
integral curve through `x₀` (at time `0`) on `Ioo (-ε) ε`. This is the exact shape
the globalization lemma `exists_isMIntegralCurve_of_isMIntegralCurveOn` consumes. -/
theorem exists_local_integralCurve_Ioo {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  obtain ⟨γ, hγ0, hγat⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) (x₀ := x₀) hv.contMDiffAt
  obtain ⟨ε, hε, hon⟩ := (isMIntegralCurveAt_iff').mp hγat
  refine ⟨ε, hε, γ, hγ0, ?_⟩
  rw [show Set.Ioo (-ε) ε = Metric.ball (0 : ℝ) ε by rw [Real.ball_eq_Ioo]; simp]
  exact hon

/-- **Per-point existence time on a compact boundaryless manifold.** Each point of
a compact boundaryless manifold admits an integral curve through it on its *own*
interval `Ioo (-εₓ) εₓ`. This is the strongest statement mathlib's local-existence
API supports directly; promoting it to a *uniform* `ε` requires the manifold flow
box (see the module docstring). -/
theorem exists_perpoint_integralCurve_time {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∀ x : M, ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) :=
  fun x => exists_local_integralCurve_Ioo hv x

/-- **Globalization.** A *uniform* existence time (a single `ε > 0` working for
every start point) immediately yields a global integral curve through every point,
by mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`. This isolates the
remaining obligation: prove the uniform-time hypothesis. -/
theorem exists_global_integralCurve_of_uniform {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (ε : ℝ) (hε : 0 < ε)
    (huniform : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
  exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε huniform x

end PoincareCurvature.ManifoldFlow
