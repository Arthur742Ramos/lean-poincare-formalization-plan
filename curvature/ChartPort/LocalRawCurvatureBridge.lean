import ChartPort.ChosenSliceSmoothness
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Evaluation of the actual upstream chart connection along a vector field. -/
def chartAlong (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (X σ : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun y => DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) g α σ y (X y)

/-- The raw nested commutator of the actual chart formula; no tensor is asserted. -/
def chartCurvatureCommutator
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (X Y σ : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  chartAlong g α X (chartAlong g α Y σ) - chartAlong g α Y (chartAlong g α X σ) -
    chartAlong g α (VectorField.mlieBracket I X Y) σ

/-- Genuine chosen-slice regularity gives a smooth along derivative of smooth sections. -/
theorem timeFamilyChosen_along_contMDiff
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    {X σ : Π y : M, TangentSpace I y}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% ((timeFamilyChosen g t).along X σ)) := by
  letI := timeFamilyChosen_contMDiffCovariantDerivative g t
  apply CovariantDerivative.contMDiff_along hX
  simpa only [ENat.coe_top_add_one] using hσ

/-- Chart spatial regularity applies to sections smooth on its actual good set. -/
theorem chartAlong_contMDiffOn_goodSet
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    {Y σ : Π y : M, TangentSpace I y}
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (chartAlong g α Y σ))
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α) := by
    simpa only [ENat.coe_top_add_one] using hσ
  have hcov :=
    (DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
      (I := I) g α).contMDiff hσ'
  exact hcov.clm_bundle_apply hY

/-- The two inner along derivatives agree as germs, using only differentiable sections. -/
theorem eventually_timeFamilyChosen_along_eq_chartAlong
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    ∀ᶠ y in 𝓝 x, (timeFamilyChosen g t).along Y σ y = chartAlong (g t) α Y σ y := by
  have hopen := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen (I := I) α
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hσy := (hσ.contMDiffAt (hopen.mem_nhds hy)).mdifferentiableAt (by simp)
  exact timeFamilyChosen_eq_chartLeviCivita g t α hy hσy (Y y)

/-- Transport an outer derivative through the genuine differentiable inner germs. -/
theorem timeFamilyChosen_nestedAlong_eq_chartAlong
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    (timeFamilyChosen g t).along X ((timeFamilyChosen g t).along Y σ) x =
      chartAlong (g t) α X (chartAlong (g t) α Y σ) x := by
  have hopen := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen (I := I) α
  have hchartInner :=
    ((chartAlong_contMDiffOn_goodSet (g t) α hY hσ).contMDiffAt
      (hopen.mem_nhds hx)).mdifferentiableAt (by simp)
  have heq := eventually_timeFamilyChosen_along_eq_chartAlong g t α (Y := Y) hx hσ
  have htotal : (T% ((timeFamilyChosen g t).along Y σ)) =ᶠ[𝓝 x]
      (T% (chartAlong (g t) α Y σ)) := by
    filter_upwards [heq] with y hy
    exact congrArg (fun v => (⟨y, v⟩ : TotalSpace E (TangentSpace I))) hy
  have hchosenInner := hchartInner.congr_of_eventuallyEq htotal
  have hlocal := (timeFamilyChosen g t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hchosenInner hchartInner (Filter.univ_mem) heq
  calc
    (timeFamilyChosen g t).along X ((timeFamilyChosen g t).along Y σ) x =
        (timeFamilyChosen g t).along X (chartAlong (g t) α Y σ) x :=
      congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) hlocal
    _ = chartAlong (g t) α X (chartAlong (g t) α Y σ) x :=
      timeFamilyChosen_eq_chartLeviCivita g t α hx hchartInner (X x)

/-- Local raw curvature agreement on the genuine chart good set, for smooth sections there.
The conclusion is a section commutator, not coordinate curvature or a Ricci contraction. -/
theorem timeFamilyChosen_curvatureAux_eq_chartCommutator
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    (timeFamilyChosen g t).curvatureAux X Y σ x =
      chartCurvatureCommutator (g t) α X Y σ x := by
  have hopen := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen (I := I) α
  have hσx := (hσ.contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt (by simp)
  have hbracket := timeFamilyChosen_eq_chartLeviCivita g t α hx hσx
    (VectorField.mlieBracket I X Y x)
  change (timeFamilyChosen g t).along X ((timeFamilyChosen g t).along Y σ) x -
      (timeFamilyChosen g t).along Y ((timeFamilyChosen g t).along X σ) x -
      (timeFamilyChosen g t).along (VectorField.mlieBracket I X Y) σ x = _
  rw [timeFamilyChosen_nestedAlong_eq_chartAlong g t α hx hY hσ,
    timeFamilyChosen_nestedAlong_eq_chartAlong g t α hx hX hσ]
  exact congrArg (fun w => chartAlong (g t) α X (chartAlong (g t) α Y σ) x -
    chartAlong (g t) α Y (chartAlong (g t) α X σ) x - w) hbracket

end ChartPort
