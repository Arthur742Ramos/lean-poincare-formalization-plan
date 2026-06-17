/-
Concrete spatial-`C¹` packaging of the project's variational ODE flow
(roadmap point 4, Item 2).

The Banach-model flow in `ModelGaugeFlowODE` supplies, on a Picard cylinder, the two
ingredients needed for the base case of the smooth-dependence bootstrap:

* the per-point spatial Fréchet derivative of each fixed-time slice
  `y ↦ flow (y, t)` (the `ofProduct_flow_timeSlice_hasFDerivAt_*` family), whose
  derivative is the variational tangent map `tangent x t`;
* joint continuity of the base-flow/tangent pair on the initial-data ball
  (`ofProduct_flow_tangent_continuousOn_initialBall_time`).

This module wires those through the abstract open-set packaging lemma
`PoincareCurvature.VariationalSmoothness.contDiffOn_one_of_hasFDerivAt_continuousOn_isOpen`
to obtain the concrete statement `ContDiffOn ℝ 1 (fun y => flow (y, t)) (ball x₀ r)` —
the spatial-`C¹` base case that the `C¹ → C³` recursion lifts. -/
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODE
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.VariationalSmoothness

open Metric Set
open scoped NNReal Topology

namespace PoincareCurvature.FlowSpatialC1

open RicciFlow RicciFlow.ModelGaugeFlowODE
  RicciFlow.ModelGaugeFlowODE.VariationalLocalFlowSolution
  PoincareCurvature.VariationalSmoothness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}

/-- **Spatial `C¹` flow slice (structure-level).** From the per-point spatial Fréchet
derivative of a variational flow time slice on the open ball and continuity of the
tangent map there, the slice `y ↦ flow (y, t)` is `ContDiffOn ℝ 1` on `ball x₀ r`. -/
theorem flow_timeSlice_contDiffOn_one_ball
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (hder : ∀ x ∈ ball x₀ r,
      HasFDerivAt (fun y : V => α.flow (y, t)) (α.tangent x t) x)
    (hcont : ContinuousOn (fun x : V => α.tangent x t) (ball x₀ r)) :
    ContDiffOn ℝ 1 (fun y : V => α.flow (y, t)) (ball x₀ r) :=
  contDiffOn_one_of_hasFDerivAt_continuousOn_isOpen isOpen_ball hder hcont

/-- **Spatial `C¹` flow slice (product Picard).** For the product-derived variational
flow, the tangent-continuity hypothesis is supplied automatically by
`ofProduct_flow_tangent_continuousOn_initialBall_time`, so only the per-point spatial
derivative remains an input. The result is the concrete spatial-`C¹` base case of the
bootstrap on the open initial-data ball. -/
theorem ofProduct_flow_timeSlice_contDiffOn_one_ball
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    (hder : ∀ x ∈ ball x₀ r,
      HasFDerivAt
        (fun y : V =>
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t))
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        x) :
    ContDiffOn ℝ 1
      (fun y : V =>
        (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t))
      (ball x₀ r) := by
  set β := ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball with hβ
  have hpair :
      ContinuousOn (fun x : V => (β.flow (x, t), β.tangent x t)) (closedBall x₀ r) := by
    simpa [hβ] using ofProduct_flow_tangent_continuousOn_initialBall_time α hball ht
  have hcont : ContinuousOn (fun x : V => β.tangent x t) (ball x₀ r) :=
    (continuous_snd.comp_continuousOn hpair).mono ball_subset_closedBall
  exact flow_timeSlice_contDiffOn_one_ball β hder hcont

end PoincareCurvature.FlowSpatialC1
