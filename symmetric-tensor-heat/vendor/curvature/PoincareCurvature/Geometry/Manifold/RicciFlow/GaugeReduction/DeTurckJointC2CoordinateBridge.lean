import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckFixedTimeC2CoordinateBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# The jointly `C²` chart bridge for the geometric DeTurck field

The fixed-time bridge proves the exact coordinate identification one slice at
a time.  This file transports the same identification through the product
chart-pushforward theorem: a jointly `C²` intrinsic DeTurck tangent-bundle
section gives jointly `C²` regularity of the genuine coordinate field.

The premise is intentionally stronger than the current `MetricFamily` and
`ConnectionFamily` interfaces.  It records the missing time--space regularity
as a geometric section premise rather than manufacturing it from slicewise
data, and it does not assert the remaining derivative-continuity or Ricci-flow
existence conclusions.
-/

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-! The exact product-domain coordinate identity. -/

theorem chartPushforwardField_eq_deTurckGaugeCoordinateField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ x : M) (t : ℝ)
    {y : E} (hx : x ∈ (extChartAt I p₀).source)
    (hxy : extChartAt I p₀ x = y) :
    PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
        p₀ t y =
      deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t y := by
  change PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      p₀ t y =
    NormedSpace.fromTangentSpace
      ((extChartAt I p₀) ((extChartAt I p₀).symm y))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) ((extChartAt I p₀).symm y)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          ((extChartAt I p₀).symm y)))
  rw [← hxy]
  rw [(extChartAt I p₀).left_inv hx]
  exact chartPushforwardField_extChartAt_eq_fromTangentSpace_mfderiv
    (intrinsicDeTurckGaugeField (I := I) (M := M) g background) p₀ x t hx

/-! **The actual jointly `C²` coordinate theorem.** -/

/-- Transport a jointly `C²` intrinsic DeTurck tangent-bundle section through
the fixed-center chart and identify it with the genuine coordinate field. -/
theorem deTurckGaugeCoordinateField_contDiffOn_prod_of_intrinsic_contMDiffOn_two
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun r : ℝ × M =>
        (⟨r.2, intrinsicDeTurckGaugeField (I := I) (M := M) g background r.1 r.2⟩ :
          TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p₀).source)) :
    ContDiffOn ℝ (2 : ℕ∞)
      (fun r : ℝ × E =>
        deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ r.1 r.2)
      (Set.univ ×ˢ (extChartAt I p₀).target) := by
  have hchart :=
    PoincareCurvature.GaugeFlowAssembly.contDiffOn_prod_chartPushforwardField
      (I := I) (M := M) (n := (2 : ℕ∞))
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (p := p₀) hX
  refine hchart.congr (fun r hr => ?_)
  have hy : r.2 ∈ (extChartAt I p₀).target := hr.2
  have hx : (extChartAt I p₀).symm r.2 ∈ (extChartAt I p₀).source :=
    (extChartAt I p₀).map_target hy
  symm
  exact chartPushforwardField_eq_deTurckGaugeCoordinateField
    (I := I) (M := M) g background p₀
    ((extChartAt I p₀).symm r.2) r.1 hx
    ((extChartAt I p₀).right_inv hy)

end RicciFlow
