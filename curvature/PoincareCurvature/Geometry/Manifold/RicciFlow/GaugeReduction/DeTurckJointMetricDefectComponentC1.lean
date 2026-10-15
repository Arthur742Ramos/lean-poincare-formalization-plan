import PoincareCurvature.Analysis.JointSpatialMVFDeriv
import PoincareCurvature.Analysis.TimeDependentGram
import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
# Joint C¹ regularity of an actual metric-defect component

The derivative of a jointly C² metric pairing along a fixed local frame is
jointly C¹. Subtracting the two actual background-connection terms gives the
metric defect, in its metric-slot, metric-slot, derivative-direction order.

Joint C¹ regularity of the background applied to the two frame sections is
explicit input. It is not inferred from the slicewise connection family.
The metric is only C²; no C³ upgrade, orthonormality or metric-defect regularity
is assumed. This local supporting theorem constructs no Ricci-flow solution.
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

local instance jointMetricDefectComponentTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance jointMetricDefectComponentTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

/-- The actual metric-defect component in a fixed local frame is jointly C¹
when the actual metric is jointly C² and the background applied to each of
the two metric-slot frame sections is jointly C¹. The last frame index is
the derivative direction. No regularity of the metric defect is an input. -/
theorem contMDiffOn_joint_metricDefect_component_of_joint_metric_and_backgroundFrame
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ E) (a b c : ι)
    (hmetric : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ e.baseSet))
    (hbackground_a : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x) p.2
        ((background p.1) (e.localFrame bas a) p.2)) (Set.univ ×ˢ e.baseSet))
    (hbackground_b : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x) p.2
        ((background p.1) (e.localFrame bas b) p.2)) (Set.univ ×ˢ e.baseSet)) :
    ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 1
      (fun p : ℝ × M =>
        letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
        (background p.1).metricDefect p.2
          (e.localFrame bas a p.2) (e.localFrame bas b p.2)
          (e.localFrame bas c p.2)) (Set.univ ×ˢ e.baseSet) := by
  let G : ℝ → M → ℝ := fun t x =>
    (g t).inner x (e.localFrame bas a x) (e.localFrame bas b x)
  have hG : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => G p.1 p.2) (Set.univ ×ˢ e.baseSet) := by
    exact ParametrizedInner.contMDiffOn_timeDependentInner_localFrame
      (IB := I) (n := (2 : WithTop ℕ∞)) g e bas (Set.Subset.rfl) hmetric a b
  have hderiv := PoincareCurvature.contMDiffOn_mvfderiv_apply_localFrame_of_joint
    (I := I) e bas c hG
  have hframe (i : ι) : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E)) 1
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (e.localFrame bas i p.2))
      (Set.univ ×ˢ e.baseSet) := by
    exact (ParametrizedInner.contMDiffOn_frameSection_prodSnd
      (IB := I) (n := (2 : WithTop ℕ∞)) e bas (Set.Subset.rfl) i).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hcov_a : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 1
      (fun p : ℝ × M => TotalSpace.mk' E p.2
        ((background p.1) (e.localFrame bas a) p.2 (e.localFrame bas c p.2)))
      (Set.univ ×ˢ e.baseSet) := by
    exact hbackground_a.clm_bundle_apply (b := Prod.snd)
      (F₁ := E) (F₂ := E) (E₁ := TM) (E₂ := TM) (hframe c)
  have hcov_b : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 1
      (fun p : ℝ × M => TotalSpace.mk' E p.2
        ((background p.1) (e.localFrame bas b) p.2 (e.localFrame bas c p.2)))
      (Set.univ ×ˢ e.baseSet) := by
    exact hbackground_b.clm_bundle_apply (b := Prod.snd)
      (F₁ := E) (F₂ := E) (E₁ := TM) (E₂ := TM) (hframe c)
  have hmetric_one := hmetric.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hterm_a := ParametrizedInner.contMDiffOn_paramBilin_apply₂
    (b := Prod.snd) (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    hmetric_one hcov_a (hframe b)
  have hterm_b := ParametrizedInner.contMDiffOn_paramBilin_apply₂
    (b := Prod.snd) (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    hmetric_one (hframe a) hcov_b
  refine ContMDiffOn.congr ((hderiv.sub hterm_a).sub hterm_b) ?_
  intro p hp
  letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle p.1
  have hFa : MDiffAt (T% (e.localFrame bas a)) p.2 :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := bas)
      (n := 1) (i := a) (hx := hp.2)).mdifferentiableAt one_ne_zero
  have hFb : MDiffAt (T% (e.localFrame bas b)) p.2 :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := bas)
      (n := 1) (i := b) (hx := hp.2)).mdifferentiableAt one_ne_zero
  have hformula := congrArg (fun L : TM p.2 →L[ℝ] ℝ => L (e.localFrame bas c p.2))
    ((background p.1).metricDefect_apply_sections hFa hFb)
  rw [CovariantDerivative.metricDefectAux_apply] at hformula
  simpa only [G] using hformula

end PoincareCurvature.GaugeFlowAssembly
