import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointCorrectionFunctionalComponentsLowering

set_option linter.unusedSectionVars false
set_option linter.all false

noncomputable section

open scoped Manifold Topology ContDiff
open Bundle

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

local instance sliceComponentsTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance sliceComponentsTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Fixed-time metric-defect components.**

At a fixed time, the `C²` metric slice and a `C¹` background connection slice
give the actual metric-defect component on every local-frame triple at spatial
regularity `C¹`.  This is only a slicewise result: it supplies no derivative in
the time parameter.
-/
theorem contMDiffOn_slice_metricDefect_component
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x₀ : M)
    {ι : Type*} (bas : Module.Basis ι ℝ E) (a b c : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ContMDiffOn I 𝓘(ℝ) 1
      (fun x : M =>
        (background t).metricDefect x
          ((trivializationAt E TM x₀).localFrame bas a x)
          ((trivializationAt E TM x₀).localFrame bas b x)
          ((trivializationAt E TM x₀).localFrame bas c x))
      (trivializationAt E TM x₀).baseSet := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  letI : MemTrivializationAtlas e := by infer_instance
  have hcov :
      ContMDiffCovariantDerivativeOn E 1 (background t).toFun e.baseSet := by
    letI : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1 :=
      hbackground
    exact
      CovariantDerivative.contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
        (I := I) (E := E) (u := e.baseSet) e.open_baseSet
  have hframe (k : ι) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x : M => TotalSpace.mk' E x (e.localFrame bas k x)) e.baseSet :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
      (I := I) (e := e) (n := (2 : WithTop ℕ∞)) (b := bas) k).mono
      (Set.Subset.rfl)
  have hsection :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun y : M => TM y →L[ℝ] ℝ)
          x ((background t).metricDefect x (e.localFrame bas a x)
            (e.localFrame bas b x))) e.baseSet :=
    CovariantDerivative.contMDiffOn_metricDefect_section
      (I := I) (E := E) e.open_baseSet hcov (hframe a) (hframe b)
  have hscalar :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x : M => TotalSpace.mk' ℝ x
          ((background t).metricDefect x (e.localFrame bas a x)
            (e.localFrame bas b x) (e.localFrame bas c x))) e.baseSet := by
    simpa using hsection.clm_bundle_apply ((hframe c).of_le (by norm_num))
  let eLine : Trivialization ℝ
      (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈
      ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  refine ContMDiffOn.congr
    ((eLine.contMDiffOn_section_iff (IB := I) (n := (1 : WithTop ℕ∞))
      (s := fun x : M => (background t).metricDefect x
        (e.localFrame bas a x) (e.localFrame bas b x) (e.localFrame bas c x))
      (a := e.baseSet) e.open_baseSet
      (by
        intro x hx
        change x ∈ (Bundle.Trivial.trivialization M ℝ).baseSet
        simp [eLine])).mp hscalar) ?_
  intro x hx
  simp [eLine, Bundle.Trivial.eq_trivialization, e]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Fixed-time torsion-inner components.**

The same fixed-time hypotheses make the scalar pairing of the actual torsion
with three local-frame vectors spatially `C¹`.  The theorem is intentionally
silent about joint time--space regularity, which remains the open premise in
the Point 4 construction.
-/
theorem contMDiffOn_slice_torsionInner_component
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x₀ : M)
    {ι : Type*} (bas : Module.Basis ι ℝ E) (a b c : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ContMDiffOn I 𝓘(ℝ) 1
      (fun x : M =>
        Inner.inner ℝ
          ((background t).torsion x
            ((trivializationAt E TM x₀).localFrame bas a x)
            ((trivializationAt E TM x₀).localFrame bas b x))
          ((trivializationAt E TM x₀).localFrame bas c x))
      (trivializationAt E TM x₀).baseSet := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  letI : MemTrivializationAtlas e := by infer_instance
  have hcov :
      ContMDiffCovariantDerivativeOn E 1 (background t).toFun e.baseSet := by
    letI : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1 :=
      hbackground
    exact
      CovariantDerivative.contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
        (I := I) (E := E) (u := e.baseSet) e.open_baseSet
  have hframe (k : ι) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x : M => TotalSpace.mk' E x (e.localFrame bas k x)) e.baseSet :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
      (I := I) (e := e) (n := (2 : WithTop ℕ∞)) (b := bas) k).mono
      (Set.Subset.rfl)
  have hsection :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TM y →L[ℝ] ℝ) x
          (CovariantDerivative.torsionInnerFunctional (I := I) (background t) x
            (e.localFrame bas a x) (e.localFrame bas b x))) e.baseSet :=
    CovariantDerivative.contMDiffOn_torsionInner_section
      (I := I) (E := E) e.open_baseSet hcov (hframe a) (hframe b)
  have hscalar :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 1
        (fun x : M => TotalSpace.mk' ℝ x
          (CovariantDerivative.torsionInnerFunctional (I := I) (background t) x
            (e.localFrame bas a x) (e.localFrame bas b x) (e.localFrame bas c x)))
        e.baseSet := by
    simpa using hsection.clm_bundle_apply ((hframe c).of_le (by norm_num))
  let eLine : Trivialization ℝ
      (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈
      ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  refine ContMDiffOn.congr
    ((eLine.contMDiffOn_section_iff (IB := I) (n := (1 : WithTop ℕ∞))
      (s := fun x : M =>
        Inner.inner ℝ ((background t).torsion x
          (e.localFrame bas a x) (e.localFrame bas b x))
          (e.localFrame bas c x))
      (a := e.baseSet) e.open_baseSet
      (by
        intro x hx
        change x ∈ (Bundle.Trivial.trivialization M ℝ).baseSet
        simp [eLine])).mp hscalar) ?_
  intro x hx
  simp [eLine, Bundle.Trivial.eq_trivialization, e,
    CovariantDerivative.torsionInnerFunctional_apply]

end PoincareCurvature.GaugeFlowAssembly
