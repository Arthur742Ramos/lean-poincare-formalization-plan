import PoincareCurvature.Analysis.TimeDependentGram
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointOneFormRegularity
import PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

set_option linter.unusedSectionVars false
set_option linter.all false

noncomputable section

open scoped Manifold Topology ContDiff
open Bundle

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow
open PoincareCurvature.ParametrizedInner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance jointCorrectionTangentFiberBundle : FiberBundle E TM := TangentSpace.fiberBundle
local instance jointCorrectionTangentVectorBundle : VectorBundle ℝ E TM := TangentSpace.vectorBundle

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Joint correction tensor from the actual correction functional.**

The preceding gauge-flow adapter assumed joint smoothness of the entire explicit
Levi--Civita correction tensor.  This theorem lowers that premise by one
geometric layer.  A jointly smooth metric representative supplies the local
Gram raising map, while the hypothesis supplies jointly smooth covector
sections obtained by applying the actual `correctionFunctional` to every
pair of local-frame sections.  The existing time-dependent Gram solver then
raises each local-frame value and finite-dimensional hom-bundle reconstruction
reassembles the full tensor.

The metric agreement hypothesis is intentional: `g` is the `C²` metric family
used by the intrinsic correction, while `gSmooth` is the smooth representative
used by the compact flow interface.  No joint regularity is inferred from the
slicewise `MetricFamily` or `ConnectionFamily` abbreviations. -/
theorem contMDiff_joint_explicitLeviCivitaCorrection_of_joint_correctionFunctional
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
          ((gSmooth p.1).inner p.2)))
    (hfunctional : ∀ (x₀ : M) (i j : ι),
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) p.2
            ((CovariantDerivative.correctionFunctional (background p.1) p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2)))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) :
    ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
          (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
          (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  letI : FiberBundle E TM := TangentSpace.fiberBundle
  letI : VectorBundle ℝ E TM := TangentSpace.vectorBundle
  let x₀ := p₀.2
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  letI : MemTrivializationAtlas e := by infer_instance
  let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
  have hp₀ : p₀ ∈ S := by
    exact ⟨Set.mem_univ _, FiberBundle.mem_baseSet_trivializationAt E TM x₀⟩
  have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
  apply contMDiffAt_clm_of_forall_apply_basis bas
  intro i
  apply contMDiffAt_clm_of_forall_apply_basis bas
  intro j
  let omega : ℝ → ∀ y : M, TM y →L[ℝ] ℝ := fun t y =>
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (CovariantDerivative.correctionFunctional (background t) y)
      (e.localFrame bas i y) (e.localFrame bas j y)
  have hω : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TM x →L[ℝ] ℝ) p.2 (omega p.1 p.2)) S := by
    simpa [omega, e, x₀, S] using hfunctional x₀ i j
  let raised : ∀ p : ℝ × M, TM p.2 := fun p =>
    ∑ i, (show ι → ℝ from
        ((show Matrix ι ι ℝ from
            (fun a b => (gSmooth p.1).inner p.2
              (e.localFrame bas a p.2) (e.localFrame bas b p.2)))⁻¹ :
          Matrix ι ι ℝ).mulVec
          (fun j => omega p.1 p.2 (e.localFrame bas j p.2))) i •
      e.localFrame bas i p.2
  have hraised : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (raised p)) S := by
    have h := @contMDiffOn_timeDependentRaisedSection
      E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
      (by exact instTopologicalSpaceTangentBundle) (fun _ => by exact inferInstance)
      (fun _ => by exact inferInstance) (by exact ‹FiberBundle E TM›)
      (by exact ‹VectorBundle ℝ E TM›)
      (by exact ‹ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I›)
      gSmooth omega e (by exact ‹MemTrivializationAtlas e›) ι
      (by infer_instance) (by infer_instance)
      bas (u := e.baseSet) (subset_rfl)
      (hmetric.contMDiffOn.mono (Set.subset_univ S)) hω
    convert h using 1 <;> rfl
  have hraisedAt : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (raised p)) p₀ :=
    (hraised p₀ hp₀).contMDiffAt (hSopen.mem_nhds hp₀)
  have hcoordRaised : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => (e (TotalSpace.mk' E p.2 (raised p))).2) p₀ := by
    simpa [e, x₀] using (Bundle.contMDiffAt_totalSpace.mp hraisedAt).2
  refine hcoordRaised.congr_of_eventuallyEq ?_
  filter_upwards [hSopen.mem_nhds hp₀] with p hp
  have hraised_eq : raised p =
      explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2
        (e.localFrame bas i p.2) (e.localFrame bas j p.2) := by
    let t := p.1
    let x := p.2
    have hraise_inner : ∀ w : TM x,
        (gSmooth t).inner x (raised p) w = omega t x w := by
      intro w
      dsimp [t, x]
      have h := @raisedVector_inner_eq
          E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
          (by exact inferInstance) (fun _ => by exact inferInstance)
          (fun _ => by exact inferInstance) (by exact ‹FiberBundle E TM›)
          (by exact ‹VectorBundle ℝ E TM›)
          (gSmooth t) (omega t) e (by exact ‹MemTrivializationAtlas e›) ι
          (by infer_instance)
          (by infer_instance) bas x hp.2 w
      dsimp [t, x] at h
      convert h using 1 <;> rfl
    have hcorrection_inner : ∀ w : TM x,
        (gSmooth t).inner x
            (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (e.localFrame bas i x) (e.localFrame bas j x)) w = omega t x w := by
      intro w
      rw [← hinner t x _ w]
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      change (g t).inner x
          ((background t).leviCivitaCorrection x
            (e.localFrame bas i x) (e.localFrame bas j x)) w = _
      rw [CovariantDerivative.leviCivitaCorrection_apply]
      change inner ℝ (CovariantDerivative.rieszMap x
          ((CovariantDerivative.correctionFunctional (background t) x)
            (e.localFrame bas i x) (e.localFrame bas j x))) w = _
      rw [CovariantDerivative.rieszMap_apply_inner]
    exact @eq_of_forall_inner_eq
      E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
      (by exact instTopologicalSpaceTangentBundle)
      (fun _ => by exact inferInstance) (fun _ => by exact inferInstance)
      (by exact ‹FiberBundle E TM›) (by exact ‹VectorBundle ℝ E TM›)
      (gSmooth t) x (raised p)
      (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
        (e.localFrame bas i x) (e.localFrame bas j x)) (fun w =>
          (hraise_inner w).trans (hcorrection_inner w).symm)
  have hpbase : p.2 ∈ (trivializationAt E TM x₀).baseSet := by
    simpa [e] using hp.2
  have hpchart : p.2 ∈ (chartAt H p₀.2).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hpbase
  rw [hom_trivializationAt_apply]
  calc
    _ = ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] E)
          (fun x : M => TM x →L[ℝ] TM x) x₀ p.2 x₀ p.2
          (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2)
          (bas i) (bas j) := by
      simp [ContinuousLinearMap.inCoordinates, e, x₀, hp.2, hpbase,
        Bundle.Trivialization.basisAt, Module.Basis.map_apply,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.symmL_apply]
    _ = (e (TotalSpace.mk' E p.2
          (((explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2)
            (e.localFrame bas i p.2)) (e.localFrame bas j p.2)))).2 := by
      have hbilin :=
        inCoordinates_apply_eq₂ (𝕜 := ℝ) (F₁ := E) (E₁ := TM)
          (F₂ := E) (E₂ := TM) (F₃ := E) (E₃ := TM)
          (x₀ := x₀) (x := p.2)
          (ϕ := explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2)
          (v := bas i) (w := bas j) hp.2 hp.2 hp.2
      rw [Bundle.Trivialization.linearMapAt_apply] at hbilin
      simpa [e, x₀, hp.2, hpbase, hpchart, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, Module.Basis.map_apply,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.symmL_apply] using hbilin
    _ = (e (TotalSpace.mk' E p.2 (raised p))).2 := by
      exact (congrArg (fun v => (e (TotalSpace.mk' E p.2 v)).2) hraised_eq).symm

end PoincareCurvature.GaugeFlowAssembly
