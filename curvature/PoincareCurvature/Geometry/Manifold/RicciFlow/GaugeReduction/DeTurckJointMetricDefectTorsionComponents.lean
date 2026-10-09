import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointCorrectionFunctionalComponentsSliceRegularity

set_option linter.unusedSectionVars false
set_option linter.all false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold Topology ContDiff
open Bundle Set

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance jointMetricDefectTorsionComponentsTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance jointMetricDefectTorsionComponentsTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

local notation "TStar" => fun y : M => TM y →L[ℝ] ℝ
local notation "TBi" => fun y : M => TM y →L[ℝ] TStar y
local notation "TTri" => fun y : M => TM y →L[ℝ] TBi y

-- The nested continuous-linear-map bundles are built explicitly.  In
-- particular, the outer trilinear topology cannot be found by typeclass
-- search until the intermediate bilinear topology and additive-group
-- structure have been named.
local instance jointMetricDefectTorsionComponentsCovectorTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) TStar) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (fun _ : M => ℝ)
local instance jointMetricDefectTorsionComponentsCovectorFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) TStar :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (fun _ : M => ℝ)
local instance jointMetricDefectTorsionComponentsCovectorVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) TStar :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (fun _ : M => ℝ)

local instance jointMetricDefectTorsionComponentsBilinearTopologicalSpace
    (y : M) : TopologicalSpace (TM y →L[ℝ] TStar y) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := TM y) (F := TStar y)
local instance jointMetricDefectTorsionComponentsBilinearAddCommGroup
    (y : M) : AddCommGroup (TM y →L[ℝ] TStar y) :=
  ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ)
    (M := TM y) (M₂ := TStar y) (σ₁₂ := RingHom.id ℝ)
local instance jointMetricDefectTorsionComponentsBilinearTopologicalAddGroup
    (y : M) : IsTopologicalAddGroup (TM y →L[ℝ] TStar y) :=
  ContinuousLinearMap.topologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := TM y) (F := TStar y)

local instance jointMetricDefectTorsionComponentsBilinearTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) TBi) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) TStar
local instance jointMetricDefectTorsionComponentsBilinearFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) TBi :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) TStar
local instance jointMetricDefectTorsionComponentsBilinearVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) TBi :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) TStar

local instance jointMetricDefectTorsionComponentsModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := by
  exact @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ E
    (E →L[ℝ] ℝ) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance
local instance jointMetricDefectTorsionComponentsModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := by
  exact @ContinuousLinearMap.toNormedSpace ℝ ℝ E
    (E →L[ℝ] ℝ) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance ℝ inferInstance
        inferInstance inferInstance

local instance jointMetricDefectTorsionComponentsTrilinearTopologicalSpace
    (y : M) : TopologicalSpace (TM y →L[ℝ] TBi y) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := TM y) (F := TBi y)
local instance jointMetricDefectTorsionComponentsTrilinearAddCommGroup
    (y : M) : AddCommGroup (TM y →L[ℝ] TBi y) :=
  ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ)
    (M := TM y) (M₂ := TBi y) (σ₁₂ := RingHom.id ℝ)
local instance jointMetricDefectTorsionComponentsTrilinearTopologicalAddGroup
    (y : M) : IsTopologicalAddGroup (TM y →L[ℝ] TBi y) :=
  ContinuousLinearMap.topologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := TM y) (F := TBi y)

local instance jointMetricDefectTorsionComponentsTrilinearTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) TTri) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) TBi
local instance jointMetricDefectTorsionComponentsTrilinearFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) TTri :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) TBi
local instance jointMetricDefectTorsionComponentsTrilinearVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) TTri :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) TBi

-- The operator-norm instance for a model-space trilinear continuous linear
-- map needs the scalar actions on its bilinear codomain to be registered.
local instance jointMetricDefectTorsionComponentsBilinearSmulCommClass
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    SMulCommClass ℝ ℝ (V →L[ℝ] (V →L[ℝ] ℝ)) where
  smul_comm r s f := by
    ext x y
    simp only [ContinuousLinearMap.smul_apply]
    exact smul_comm r s ((f x) y)

local instance jointMetricDefectTorsionComponentsTrilinearNormedAddCommGroup
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ))) := by
  exact @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ V
    (V →L[ℝ] (V →L[ℝ] ℝ)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance

local instance jointMetricDefectTorsionComponentsTrilinearNormedSpace
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] (V →L[ℝ] (V →L[ℝ] ℝ))) := by
  exact @ContinuousLinearMap.toNormedSpace ℝ ℝ V
    (V →L[ℝ] (V →L[ℝ] ℝ)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance ℝ inferInstance inferInstance inferInstance

local instance jointMetricDefectTorsionComponentsModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := by
  exact @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ E
    (E →L[ℝ] (E →L[ℝ] ℝ)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance
local instance jointMetricDefectTorsionComponentsModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := by
  exact @ContinuousLinearMap.toNormedSpace ℝ ℝ E
    (E →L[ℝ] (E →L[ℝ] ℝ)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) inferInstance ℝ inferInstance inferInstance
        inferInstance

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Joint scalar components from genuine geometric sections.**

If the actual metric-defect and torsion-inner trilinear sections are jointly
`C^∞`, then their evaluations on any fixed local frame have the joint scalar
regularity required by the correction-functional lowering bridge.  The theorem
does not manufacture this section regularity from the `MetricFamily` or
`ConnectionFamily` abbreviations; those are kept only in the displayed
formula for the sections being assumed.
-/
theorem contMDiffOn_joint_metricDefect_torsion_components_of_joint_sections
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hmetricDefect :
      ContMDiff (𝓘(ℝ).prod I)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
            ((background p.1).metricDefect p.2)))
    (htorsionInner :
      ContMDiff (𝓘(ℝ).prod I)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
            (CovariantDerivative.torsionInnerFunctional (I := I) (background p.1) p.2))) :
    (∀ (x₀ : M) (i j k : ι),
      ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          (background p.1).metricDefect p.2
            ((trivializationAt E TM x₀).localFrame bas i p.2)
            ((trivializationAt E TM x₀).localFrame bas j p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) ∧
    (∀ (x₀ : M) (i j k : ι),
      ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          (CovariantDerivative.torsionInnerFunctional (I := I) (background p.1) p.2)
            ((trivializationAt E TM x₀).localFrame bas i p.2)
            ((trivializationAt E TM x₀).localFrame bas j p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) := by
  have scalar_of_section :
      ∀ (x₀ : M) (S : Set (ℝ × M)) (s : ℝ × M → ℝ),
        IsOpen S →
        ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × M => TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) p.2 (s p)) S →
        ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ s S := by
    intro x₀ S s hS hs
    let eLine : Trivialization ℝ
        (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
      Bundle.Trivial.trivialization M ℝ
    letI : MemTrivializationAtlas eLine := by
      constructor
      change Bundle.Trivial.trivialization M ℝ ∈
        ({Bundle.Trivial.trivialization M ℝ} : Set _)
      simp [eLine]
    have hmaps : MapsTo
        (fun p : ℝ × M => TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) p.2 (s p))
          S eLine.source := by
      intro p hp
      apply eLine.mem_source.mpr
      simp [eLine]
    have hcoord :=
      ((eLine.contMDiffOn_iff (IB := I) (n := (∞ : WithTop ℕ∞)) hmaps).mp hs).2
    refine ContMDiffOn.congr hcoord ?_
    intro p hp
    simp [eLine, Bundle.Trivial.eq_trivialization]
  constructor
  · intro x₀ i j k
    let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
      trivializationAt E TM x₀
    let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
    have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
    have hframe (l : ι) :
        ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
          (fun p : ℝ × M => TotalSpace.mk' E p.2 (e.localFrame bas l p.2)) S := by
      have hspatial : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E x (e.localFrame bas l x)) e.baseSet :=
        e.contMDiffOn_localFrame_baseSet (I := I) (n := ∞) bas l
      exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp => hp.2)
    let s : ℝ × M → ℝ := fun p =>
      letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
      (background p.1).metricDefect p.2
        (e.localFrame bas i p.2) (e.localFrame bas j p.2) (e.localFrame bas k p.2)
    have hsection :
        ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × M => TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) p.2 (s p)) S := by
      have h0 := hmetricDefect.contMDiffOn.mono (Set.subset_univ S)
      have h1 := h0.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := E →L[ℝ] (E →L[ℝ] ℝ)) (E₁ := TM) (E₂ := TBi) (hframe i)
      have h2 := h1.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := E →L[ℝ] ℝ) (E₁ := TM) (E₂ := TStar) (hframe j)
      have h3 := h2.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := ℝ) (E₁ := TM) (E₂ := fun _ : M => ℝ) (hframe k)
      simpa [s, e, S] using h3
    exact scalar_of_section x₀ S s hSopen hsection
  · intro x₀ i j k
    let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
      trivializationAt E TM x₀
    let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
    have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
    have hframe (l : ι) :
        ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
          (fun p : ℝ × M => TotalSpace.mk' E p.2 (e.localFrame bas l p.2)) S := by
      have hspatial : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E x (e.localFrame bas l x)) e.baseSet :=
        e.contMDiffOn_localFrame_baseSet (I := I) (n := ∞) bas l
      exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp => hp.2)
    let s : ℝ × M → ℝ := fun p =>
      letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
      (CovariantDerivative.torsionInnerFunctional (I := I) (background p.1) p.2)
        (e.localFrame bas i p.2) (e.localFrame bas j p.2) (e.localFrame bas k p.2)
    have hsection :
        ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × M => TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) p.2 (s p)) S := by
      have h0 := htorsionInner.contMDiffOn.mono (Set.subset_univ S)
      have h1 := h0.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := E →L[ℝ] (E →L[ℝ] ℝ)) (E₁ := TM) (E₂ := TBi) (hframe i)
      have h2 := h1.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := E →L[ℝ] ℝ) (E₁ := TM) (E₂ := TStar) (hframe j)
      have h3 := h2.clm_bundle_apply (b := Prod.snd) (F₁ := E)
        (F₂ := ℝ) (E₁ := TM) (E₂ := fun _ : M => ℝ) (hframe k)
      simpa [s, e, S] using h3
    exact scalar_of_section x₀ S s hSopen hsection

end PoincareCurvature.GaugeFlowAssembly
