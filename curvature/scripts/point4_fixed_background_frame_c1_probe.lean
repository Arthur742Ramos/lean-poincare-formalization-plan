import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointBackgroundFrameC1

noncomputable section

set_option autoImplicit false
set_option pp.proofs false
set_option pp.universes true
set_option pp.fullNames true
set_option format.width 120

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

universe u v w z

local instance probeFixedBackgroundTangentFiberBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    FiberBundle E (TangentSpace I : M → Type _) := TangentSpace.fiberBundle

local instance probeFixedBackgroundTangentVectorBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    VectorBundle ℝ E (TangentSpace I : M → Type _) := TangentSpace.vectorBundle

/-- The independent whole-function type requires only spatial C¹ background
regularity. Joint regularity of its frame values is the conclusion. -/
abbrev ExpectedFixedBackgroundFrameC1 :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov₀ : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    {ι : Type z} (bas : Module.Basis ι ℝ E) (i : ι),
    ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.2
        (cov₀ (e.localFrame bas i) p.2)) (Set.univ ×ˢ e.baseSet)

def fixedBackgroundFrameC1FullSignatureAssignment :
    ExpectedFixedBackgroundFrameC1.{u,v,w,z} :=
  @PoincareCurvature.GaugeFlowAssembly.contMDiffOn_const_background_localFrame

/-- The actual-IVP whole-function type has only the joint C² metric premise;
neither background-frame joint-regularity hypothesis is an argument. -/
abbrev ExpectedFixedIVPMetricDefectC1 :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (ivp : RicciFlow.InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    {ι : Type z} (bas : Module.Basis ι ℝ E) (a b c : ι),
    ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ e.baseSet) →
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 1
      (fun p : ℝ × M =>
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(g p.1).toRiemannianMetric⟩
        ((ivp.fixedLeviCivitaBackground).constantConnection p.1).metricDefect p.2
          (e.localFrame bas a p.2) (e.localFrame bas b p.2)
          (e.localFrame bas c p.2)) (Set.univ ×ˢ e.baseSet)

def fixedIVPMetricDefectC1FullSignatureAssignment :
    ExpectedFixedIVPMetricDefectC1.{u,v,w,z} :=
  @RicciFlow.InitialValueProblem.contMDiffOn_joint_metricDefect_component_fixedLeviCivitaBackground

section ZeroModel

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Fin 0 → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ (Fin 0 → ℝ)] [CompleteSpace (Fin 0 → ℝ)]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 (Fin 0 → ℝ) (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- A genuine zero-dimensional endomorphism statement, not quantification
over a nonexistent frame index. The actual fixed-IVP connection is used. -/
theorem fixedBackgroundFin0EndomorphismZero
    (ivp : RicciFlow.InitialValueProblem (E := Fin 0 → ℝ) (H := H) (I := I) (M := M))
    (σ : ∀ x : M, TangentSpace I x) (x : M) :
    (ivp.fixedLeviCivitaBackground).covariantDerivative σ x = 0 := by
  ext v
  exact Subsingleton.elim _ _

/-- The actual fixed-background metric defect is zero in genuine dimension
zero. No empty-manifold or positive-rank premise is introduced. -/
theorem fixedBackgroundFin0MetricDefectZero
    (ivp : RicciFlow.InitialValueProblem (E := Fin 0 → ℝ) (H := H) (I := I) (M := M))
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (p : ℝ × M) (u v w : TangentSpace I p.2) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g p.1).toRiemannianMetric⟩
    ((ivp.fixedLeviCivitaBackground).constantConnection p.1).metricDefect p.2 u v w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g p.1).toRiemannianMetric⟩
  have hz : w = 0 := Subsingleton.elim _ _
  simp only [hz, map_zero]

end ZeroModel

#eval IO.println "FIXED_BACKGROUND_FRAME_C1_TYPES_BEGIN"
#print ExpectedFixedBackgroundFrameC1
#print fixedBackgroundFrameC1FullSignatureAssignment
#print ExpectedFixedIVPMetricDefectC1
#print fixedIVPMetricDefectC1FullSignatureAssignment
#print PoincareCurvature.GaugeFlowAssembly.contMDiffOn_const_background_localFrame
#print PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_fixed_background
#print RicciFlow.InitialValueProblem.contMDiffOn_joint_metricDefect_component_fixedLeviCivitaBackground
#print fixedBackgroundFin0EndomorphismZero
#print fixedBackgroundFin0MetricDefectZero
#eval IO.println "FIXED_BACKGROUND_FRAME_C1_TYPES_END"

#print axioms fixedBackgroundFrameC1FullSignatureAssignment
#print axioms fixedIVPMetricDefectC1FullSignatureAssignment
#print axioms PoincareCurvature.GaugeFlowAssembly.contMDiffOn_const_background_localFrame
#print axioms PoincareCurvature.GaugeFlowAssembly.contMDiffOn_joint_metricDefect_component_of_joint_metric_and_fixed_background
#print axioms RicciFlow.InitialValueProblem.contMDiffOn_joint_metricDefect_component_fixedLeviCivitaBackground
#print axioms fixedBackgroundFin0EndomorphismZero
#print axioms fixedBackgroundFin0MetricDefectZero
