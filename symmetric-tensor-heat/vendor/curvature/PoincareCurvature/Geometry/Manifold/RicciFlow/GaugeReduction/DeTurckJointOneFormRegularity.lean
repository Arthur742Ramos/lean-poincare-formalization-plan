import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckRaisedCompactGaugeFlow
import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity
import PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

set_option linter.unusedSectionVars false
set_option linter.all false

noncomputable section

/-!
# Joint regularity of the intrinsic DeTurck one-form from the correction tensor

The compact gauge-flow adapter consumes joint `(t, x)` smoothness of the traced
intrinsic DeTurck one-form.  This file lowers that input to the actual geometric
correction tensor: after applying the correction to two local-frame sections, its
finite trace formula gives the one-form components.  The resulting theorem is
still conditional on the genuine joint smoothness of the correction tensor; it
does not infer time regularity from slicewise `MetricFamily` or
`ConnectionFamily` data.
-/

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

local instance tangentFiberBundle : FiberBundle E TM := TangentSpace.fiberBundle
local instance tangentVectorBundle : VectorBundle ℝ E TM := TangentSpace.vectorBundle

set_option maxHeartbeats 1000000 in
theorem contMDiff_intrinsicDeTurckOneForm_of_joint_explicitLeviCivitaCorrection
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hcorrection : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E))
      ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
          (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
          (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2))) :
    ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TM x →L[ℝ] ℝ) p.2
          (-intrinsicDeTurckOneForm (I := I) (M := M) g background p.1 p.2)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  letI : FiberBundle E TM := TangentSpace.fiberBundle
  letI : VectorBundle ℝ E TM := TangentSpace.vectorBundle
  let x₀ := p₀.2
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
  have hp₀ : p₀ ∈ S := by
    exact ⟨Set.mem_univ _, FiberBundle.mem_baseSet_trivializationAt E TM x₀⟩
  have hframe : ∀ i : ι,
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M =>
          TotalSpace.mk' E p.2 (e.localFrame bas i p.2)) S := by
    intro i
    have hspatial : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (e.localFrame bas i x)) e.baseSet :=
      e.contMDiffOn_localFrame_baseSet (I := I) (n := ∞) bas i
    exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp => hp.2)
  have hC : ∀ j : ι, ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TM x →L[ℝ] TM x) p.2
          (explicitLeviCivitaCorrection g background p.1 p.2
            (e.localFrame bas j p.2))) S := by
    intro j
    simpa using hcorrection.contMDiffOn.clm_bundle_apply
      (b := Prod.snd) (F₁ := E) (hframe j)
  have hCC : ∀ j i : ι, ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' E p.2
          ((explicitLeviCivitaCorrection g background p.1 p.2
            (e.localFrame bas j p.2)) (e.localFrame bas i p.2))) S := by
    intro j i
    simpa using (hC j).clm_bundle_apply
      (b := Prod.snd) (F₁ := E) (hframe i)
  apply contMDiffAt_clm_of_forall_apply_basis bas
  intro i
  have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
  have hcoeffC : ∀ j : ι,
      ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          e.localFrameCoeff I bas j p.2
            ((explicitLeviCivitaCorrection g background p.1 p.2
              (e.localFrame bas j p.2)) (e.localFrame bas i p.2))) p₀ := by
    intro j
    have hCji : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M =>
          TotalSpace.mk' E p.2
            ((explicitLeviCivitaCorrection g background p.1 p.2
              (e.localFrame bas j p.2)) (e.localFrame bas i p.2))) p₀ :=
      (hCC j i).contMDiffAt (hSopen.mem_nhds hp₀)
    have hcoordC : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun p : ℝ × M =>
          (e (TotalSpace.mk' E p.2
            ((explicitLeviCivitaCorrection g background p.1 p.2
              (e.localFrame bas j p.2)) (e.localFrame bas i p.2)))).2) p₀ := by
      simpa [e, x₀] using (Bundle.contMDiffAt_totalSpace.mp hCji).2
    let breprl : E →ₗ[ℝ] ℝ :=
      { toFun := fun v => bas.repr v j
        map_add' := by intro v w; simp
        map_smul' := by intro c v; simp }
    have hrepr : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => breprl.toContinuousLinearMap
          ((e (TotalSpace.mk' E p.2
            ((explicitLeviCivitaCorrection g background p.1 p.2
              (e.localFrame bas j p.2)) (e.localFrame bas i p.2)))).2)) p₀ := by
      exact (contMDiffAt_const.clm_apply hcoordC)
    refine hrepr.congr_of_eventuallyEq ?_
    filter_upwards [hSopen.mem_nhds hp₀] with p hp
    let sji : ∀ y : M, TM y := fun y =>
      (explicitLeviCivitaCorrection g background p.1 y
        (e.localFrame bas j y)) (e.localFrame bas i y)
    rw [e.localFrameCoeff_eq_coeff (I := I) (b := bas) (s := sji) hp.2]
    rfl
  have hsum : ∀ s : Finset ι,
      ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => s.sum (fun j =>
          e.localFrameCoeff I bas j p.2
            ((explicitLeviCivitaCorrection g background p.1 p.2
              (e.localFrame bas j p.2)) (e.localFrame bas i p.2)))) p₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (contMDiffAt_const :
          ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun _ : ℝ × M => (0 : ℝ)) p₀)
    | @insert j s hj hs =>
        convert (hcoeffC j).add hs using 1 <;> ext p <;>
          simp only [Finset.sum_insert, hj, not_false_eq_true, Pi.add_apply]
  have hframeForm : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => intrinsicDeTurckOneForm
        (I := I) (M := M) g background p.1 p.2 (e.localFrame bas i p.2)) p₀ := by
    refine (hsum Finset.univ).congr_of_eventuallyEq ?_
    filter_upwards [hSopen.mem_nhds hp₀] with p hp
    exact intrinsicDeTurckOneForm_apply_localFrame_eq_sum_leviCivitaCorrection
      (I := I) (M := M) g background p.1 e bas hp.2 i
  refine hframeForm.neg.congr_of_eventuallyEq ?_
  filter_upwards [hSopen.mem_nhds hp₀] with p hp
  rw [hom_trivializationAt_apply]
  simp [ContinuousLinearMap.inCoordinates, e, x₀, hp.2]
  rw [e.localFrame_apply_of_mem_baseSet bas hp.2]
  simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply]
  rw [Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt E TM x₀) hp.2]

/- The correction-tensor form of the compact gauge-flow adapter.  This is the
   composition point for the geometric trace regularity theorem above and the
   compact assembly already delivered in the preceding stack. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_joint_explicitLeviCivitaCorrection
    [I.Boundaryless] [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
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
    (hcorrection : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
          (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
          (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
        (Set.Ioo (-ε) ε) 0) := by
  exact exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_raised_intrinsicDeTurckGaugeField
    (I := I) (M := M) g gSmooth background bas hinner hmetric
    (contMDiff_intrinsicDeTurckOneForm_of_joint_explicitLeviCivitaCorrection
      (I := I) (M := M) g background bas hcorrection)
end PoincareCurvature.GaugeFlowAssembly
