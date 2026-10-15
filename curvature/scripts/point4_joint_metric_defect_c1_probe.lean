import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointMetricDefectComponentC1

noncomputable section

set_option autoImplicit false
set_option pp.proofs false
set_option pp.universes true
set_option pp.fullNames true
set_option format.width 120

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

universe u v w z

local instance probeTangentFiberBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    FiberBundle E (TangentSpace I : M → Type _) := TangentSpace.fiberBundle

local instance probeTangentVectorBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    VectorBundle ℝ E (TangentSpace I : M → Type _) := TangentSpace.vectorBundle

/-- Independent whole-function signature: the only joint analytic inputs are
the actual C² metric section and the two actual C¹ background-frame sections. -/
abbrev ExpectedJointMetricDefectComponentC1 :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    {ι : Type z} (bas : Module.Basis ι ℝ E) (a b c : ι),
    ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ e.baseSet) →
    ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2
        ((background p.1) (e.localFrame bas a) p.2)) (Set.univ ×ˢ e.baseSet) →
    ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2
        ((background p.1) (e.localFrame bas b) p.2)) (Set.univ ×ˢ e.baseSet) →
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 1
      (fun p : ℝ × M =>
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(g p.1).toRiemannianMetric⟩
        (background p.1).metricDefect p.2
          (e.localFrame bas a p.2) (e.localFrame bas b p.2)
          (e.localFrame bas c p.2)) (Set.univ ×ˢ e.baseSet)

def jointMetricDefectComponentC1FullSignatureAssignment :
    ExpectedJointMetricDefectComponentC1.{u,v,w,z} :=
  @PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_backgroundFrame

section ZeroModel

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin 0 → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ (Fin 0 → ℝ)] [CompleteSpace (Fin 0 → ℝ)]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 (Fin 0 → ℝ) (TangentSpace I : M → Type _) I]

-- A genuine zero-dimensional specialization of the actual metric-defect
-- scalar, without any nonempty-manifold or nonzero-rank premise.
example (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (p : ℝ × M) (u v w : TangentSpace I p.2) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g p.1).toRiemannianMetric⟩
    (background p.1).metricDefect p.2 u v w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g p.1).toRiemannianMetric⟩
  have hz : w = 0 := Subsingleton.elim _ _
  simp only [hz, map_zero]

end ZeroModel

#eval IO.println "JOINT_METRIC_DEFECT_C1_TYPES_BEGIN"
#print ExpectedJointMetricDefectComponentC1
#print jointMetricDefectComponentC1FullSignatureAssignment
#print PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_backgroundFrame
#eval IO.println "JOINT_METRIC_DEFECT_C1_TYPES_END"

#print axioms jointMetricDefectComponentC1FullSignatureAssignment
#print axioms PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_backgroundFrame
