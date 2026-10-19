import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointMetricDefectComponentC1
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import PoincareCurvature.Geometry.Manifold.RicciFlow.InitialValueProblemBackground

/-!
# Joint C¹ background-frame regularity for a fixed initial-value problem

A spatially C¹ connection applied to a C² local frame gives a spatially C¹
endomorphism section. Its time-independent extension is jointly C¹ by
composition with `Prod.snd`. This discharges both background-frame hypotheses
of the joint metric-defect component theorem for a fixed background.

The fixed-IVP specialization chooses the actual Levi-Civita connection of the
initial C² metric. No joint regularity of an arbitrary time-dependent
connection is inferred from slicewise regularity. No nonlinear solution or
Point-4 completion is constructed.

Verification status: proof source awaiting exact Lean 4.33 compilation.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature.GaugeFlowAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

local instance fixedBackgroundFrameTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance fixedBackgroundFrameTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

/-- A fixed spatially C¹ connection has jointly C¹ values on every C² local
frame section, as an endomorphism-valued section over the spatial projection.
The basis index need not be inhabited. -/
theorem contMDiffOn_const_background_localFrame
    (cov₀ : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) (i : ι) :
    ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x) p.2
        (cov₀ (e.localFrame bas i) p.2)) (Set.univ ×ˢ e.baseSet) := by
  have hcov : ContMDiffCovariantDerivativeOn E 1 cov₀.toFun e.baseSet :=
    CovariantDerivative.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (I := I) (F := E) (V := TM) e.open_baseSet
  have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 + 1)
      (fun x : M => TotalSpace.mk' E x (e.localFrame bas i x)) e.baseSet := by
    convert e.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞)) bas i
      using 1 <;> norm_num
  have hspatial : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TM y →L[ℝ] TM y) x
        (cov₀ (e.localFrame bas i) x)) e.baseSet :=
    hcov.contMDiff hframe
  exact hspatial.comp contMDiff_snd.contMDiffOn (fun p hp => hp.2)

/-- With a fixed spatially C¹ background, joint C² metric regularity suffices
for the actual metric-defect scalar. Neither background-frame joint
regularity assumption is supplied by the caller. -/
theorem contMDiffOn_joint_metricDefect_component_of_joint_metric_and_fixed_background
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) (a b c : ι)
    (hmetric : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ e.baseSet)) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 1
      (fun p : ℝ × M =>
        letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
        cov₀.metricDefect p.2
          (e.localFrame bas a p.2) (e.localFrame bas b p.2)
          (e.localFrame bas c p.2)) (Set.univ ×ˢ e.baseSet) := by
  exact contMDiffOn_joint_metricDefect_component_of_joint_metric_and_backgroundFrame
    g (fun _ => cov₀) e bas a b c hmetric
    (contMDiffOn_const_background_localFrame cov₀ e bas a)
    (contMDiffOn_const_background_localFrame cov₀ e bas b)

end PoincareCurvature.GaugeFlowAssembly

namespace RicciFlow.InitialValueProblem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The two background-frame assumptions of the metric-defect component
theorem are discharged for the actual fixed-IVP Levi-Civita background.
Only joint C² regularity of the evolving metric is an analytic premise. -/
theorem contMDiffOn_joint_metricDefect_component_fixedLeviCivitaBackground
    (ivp : RicciFlow.InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) (a b c : ι)
    (hmetric : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ e.baseSet)) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 1
      (fun p : ℝ × M =>
        letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
        ((ivp.fixedLeviCivitaBackground).constantConnection p.1).metricDefect p.2
          (e.localFrame bas a p.2) (e.localFrame bas b p.2)
          (e.localFrame bas c p.2)) (Set.univ ×ˢ e.baseSet) := by
  let background := ivp.fixedLeviCivitaBackground
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      background.covariantDerivative 1 := background.contMDiff
  exact PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_fixed_background
    g background.covariantDerivative e bas a b c hmetric

end RicciFlow.InitialValueProblem
