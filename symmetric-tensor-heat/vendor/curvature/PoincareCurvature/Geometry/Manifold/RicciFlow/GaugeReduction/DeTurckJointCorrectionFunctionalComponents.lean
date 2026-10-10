import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCorrectionFunctionalSliceRegularity

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

local instance jointCorrectionComponentsTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance jointCorrectionComponentsTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Joint correction functional from scalar local-frame evaluations.**

The tensor bridge in `DeTurckJointCorrectionTensorRegularity` consumes a
jointly smooth covector section for every pair of local-frame inputs.  This
theorem reconstructs that section from the scalar evaluations on a third
local-frame vector.  The reconstruction is finite-dimensional and uses the
actual induced cotangent coordinates; no smoothness of the scalar evaluations
is inferred here.  Consequently the remaining analytic obligation is exposed
as scalar time--space regularity of the correction functional itself.
-/
theorem contMDiffOn_joint_correctionFunctional_of_joint_localFrame_evaluations
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hfunctional : ∀ (x₀ : M) (i j k : ι),
      ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          (CovariantDerivative.correctionFunctional (background p.1) p.2)
            ((trivializationAt E TM x₀).localFrame bas i p.2)
            ((trivializationAt E TM x₀).localFrame bas j p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) :
    ∀ (x₀ : M) (i j : ι),
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) p.2
            ((CovariantDerivative.correctionFunctional (background p.1) p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2)))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet) := by
  intro x₀ i j
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
  have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
  let omega : ℝ × M → ∀ y : M, TM y →L[ℝ] ℝ := fun p y =>
    letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
    (CovariantDerivative.correctionFunctional (background p.1) y)
      (e.localFrame bas i y) (e.localFrame bas j y)
  have hω : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TM x →L[ℝ] ℝ) p.2 (omega p p.2)) S := by
    intro p hp
    let eLine : Trivialization ℝ
        (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
      Bundle.Trivial.trivialization M ℝ
    letI : MemTrivializationAtlas eLine := by
      constructor
      change Bundle.Trivial.trivialization M ℝ ∈
        ({Bundle.Trivial.trivialization M ℝ} : Set _)
      simp [eLine]
    let eStar :
        Trivialization (E →L[ℝ] ℝ)
          (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) (fun x : M => TM x →L[ℝ] ℝ) → M) :=
      e.continuousLinearMap (σ := RingHom.id ℝ) eLine
    have hpStar :
        TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) p.2 (omega p p.2) ∈ eStar.source := by
      apply eStar.mem_source.mpr
      rw [Bundle.Trivialization.baseSet_continuousLinearMap]
      exact ⟨hp.2, by simp [eLine]⟩
    have hpAt : ContMDiffAt (𝓘(ℝ).prod I)
        (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun q : ℝ × M =>
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) q.2 (omega q q.2)) p := by
      rw [Bundle.Trivialization.contMDiffAt_iff (e := eStar)
        (f := fun q : ℝ × M =>
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) q.2 (omega q q.2))
        (x₀ := p) hpStar]
      refine ⟨contMDiffAt_snd, ?_⟩
      apply contMDiffAt_clm_of_forall_apply_basis bas
      intro k
      have hk : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × M => omega q q.2 (e.localFrame bas k q.2)) p := by
        simpa [omega, e] using
          ((hfunctional x₀ i j k p hp).contMDiffAt (hSopen.mem_nhds hp))
      refine hk.congr_of_eventuallyEq ?_
      filter_upwards [hSopen.mem_nhds hp] with q hq
      have hframe (l : ι) :
          e.localFrame bas l q.2 = e.symmL ℝ q.2 (bas l) := by
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
          (e := e) (b := bas) hq.2]
        simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
        rw [Bundle.Trivialization.linearEquivAt_symm_apply]
        rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hq.2]
      simp_rw [hframe]
      simp [omega, eStar, eLine, e, hq.2,
        Bundle.Trivialization.continuousLinearMap_apply,
        Bundle.Trivialization.basisAt]
    exact hpAt.contMDiffWithinAt
  simpa [omega, e, S] using hω

end PoincareCurvature.GaugeFlowAssembly
