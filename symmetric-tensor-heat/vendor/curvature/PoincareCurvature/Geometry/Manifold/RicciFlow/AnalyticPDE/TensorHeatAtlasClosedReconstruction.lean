import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasInitial
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorNormSqLocalFrame
import PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSectionCore

/-!
# Canonical closed-time tensor reconstruction from atlas coefficients

The finite-cylinder coefficient carrier is totalized arbitrarily outside its
positive-time domain. This file reconstructs from the canonical completed
coefficient value instead, so the initial tensor is determined by the actual
parabolic trace.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

local instance closedAtlasCovectorVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)

local instance closedAtlasTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁

@[reducible] local instance closedAtlasTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x

@[reducible] local instance closedAtlasTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x

local instance closedAtlasTwoFiberAddCommMonoid (x : M) :
    AddCommMonoid (T₂ x) :=
  (closedAtlasTwoFiberNormedAddCommGroup x).toAddCommMonoid

local instance closedAtlasTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

local instance closedAtlasTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem continuous_add_tensorSections
    (f g : ∀ p : ℝ × M, T₂ p.2)
    (hf : Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2 (f p)))
    (hg : Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2 (g p))) :
    Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2 (f p + g p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) T₂ p.2
  have hlin : e.IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear
      (F := E) (W := TM) p.2
  letI : e.IsLinear ℝ := hlin
  have hp : p.2 ∈ e.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' p.2
  have hfAt := (e.tendsto_nhds_iff (e.mem_source.mpr hp)).1
    (hf.continuousAt (x := p))
  have hgAt := (e.tendsto_nhds_iff (e.mem_source.mpr hp)).1
    (hg.continuousAt (x := p))
  have hsum := hfAt.2.add hgAt.2
  have hcoord : ContinuousAt (fun q : ℝ × M =>
      (e (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) q.2 (f q + g q))).2) p := by
    have hpoint := (e.linear ℝ hp).1 (f p) (g p)
    change Filter.Tendsto (fun q : ℝ × M =>
      (e (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) q.2 (f q + g q))).2) (𝓝 p)
      (𝓝 ((e (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) p.2 (f p + g p))).2))
    rw [hpoint]
    apply hsum.congr'
    have hopen : IsOpen ((fun q : ℝ × M => q.2) ⁻¹' e.baseSet) :=
      e.open_baseSet.preimage continuous_snd
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact ((e.linear ℝ hq).1 (f q) (g q)).symm
  refine (e.tendsto_nhds_iff (e.mem_source.mpr hp)).2 ?_
  exact ⟨continuous_snd.continuousAt, hcoord⟩

private theorem continuous_finset_sum_tensorSections
    {ι : Type*} (s : Finset ι) (f : ι → ∀ p : ℝ × M, T₂ p.2)
    (hf : ∀ i, Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2 (f i p))) :
    Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2
        (∑ i ∈ s, f i p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, zeroSection, Function.comp_def] using
        ((Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_snd :
          Continuous (fun p : ℝ × M =>
            zeroSection (E →L[ℝ] E →L[ℝ] ℝ) T₂ p.2))
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      exact continuous_add_tensorSections (f i)
        (fun p => ∑ j ∈ s, f j p) (hf i) ih

/-- The completed local coefficient matrix is jointly continuous on its
genuine coordinate patch. -/
theorem continuousOn_closedHigherCoefficient_on_patch
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    ContinuousOn
      (fun p : ℝ × M =>
        FiniteParabolicC2AlphaBanach.completedValue
          A.time_lt A.alpha_pos (normalizedHigherSolution u)
          (FiniteClassicalTensorHeatField.normalizedTime t₀
            (A.radius (i : M)) p.1,
           normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) p.2))
      (Set.univ ×ˢ actualLocalTensorHeatPatch (I := I)
        (i : M) (A.radius (i : M))) := by
  let U := actualLocalTensorHeatPatch (I := I)
    (i : M) (A.radius (i : M))
  have hcoord : ContinuousOn
      (normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M))) U := by
    unfold normalizedTensorHeatCoordinate
    exact (((continuousOn_extChartAt (I := I) (i : M)).mono
      (actualLocalTensorHeatPatch_subset_chartSource (I := I)
        (i : M) (A.radius (i : M)))).sub continuousOn_const).const_smul _
  have hpair : ContinuousOn
      (fun p : ℝ × M =>
        (FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) p.1,
         normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) p.2))
      (Set.univ ×ˢ U) := by
    have htime : Continuous (fun t : ℝ =>
        FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t) := by
      unfold FiniteClassicalTensorHeatField.normalizedTime
      fun_prop
    apply (htime.comp continuous_fst).continuousOn.prodMk
    exact hcoord.comp continuousOn_snd (by
      intro p hp
      exact hp.2)
  exact (FiniteParabolicC2AlphaBanach.continuous_completedValue
    A.time_lt A.alpha_pos (normalizedHigherSolution u)).continuousOn.comp
      hpair (by intro p _hp; exact Set.mem_univ _)

/-- Reconstruct a local tensor from the completed coefficient value at every
physical time. The positive-time restriction is the existing classical field. -/
def closedLocalFieldOfHigher
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i)
    (fun y => FiniteParabolicC2AlphaBanach.completedValue
      A.time_lt A.alpha_pos (normalizedHigherSolution u)
      (FiniteClassicalTensorHeatField.normalizedTime t₀
        (A.radius (i : M)) t,
       normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) y))

theorem continuousOn_closedLocalField_totalSpace_on_patch
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    ContinuousOn
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := T₂) p.2 (closedLocalFieldOfHigher cov A i u p.1 p.2))
      (Set.univ ×ˢ actualLocalTensorHeatPatch (I := I)
        (i : M) (A.radius (i : M))) := by
  let q : ℝ × M → Fin d → Fin d → ℝ := fun p =>
    FiniteParabolicC2AlphaBanach.completedValue
      A.time_lt A.alpha_pos (normalizedHigherSolution u)
      (FiniteClassicalTensorHeatField.normalizedTime t₀
        (A.radius (i : M)) p.1,
       normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) p.2)
  have hq : ContinuousOn q
      (Set.univ ×ˢ actualLocalTensorHeatPatch (I := I)
        (i : M) (A.radius (i : M))) :=
    A.continuousOn_closedHigherCoefficient_on_patch cov i u
  have hψ : Continuous (A.cover.partition i) :=
    (A.cover.partition i).contMDiff.continuous
  have h := continuousOn_cutoffLocalTensorOfMatrix_on_patch
    (I := I) (p := (i : M))
    (trivializationAt E TM (i : M)) b
    (A.cover.partition i) hψ
    (A.patch_subset_trivialization (i : M)) q hq
  exact h

/-- The cutoff erases the arbitrary local-frame branch outside its support,
so the completed local tensor is jointly continuous globally as a section. -/
theorem continuous_closedLocalField_totalSpace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) p.2 (closedLocalFieldOfHigher cov A i u p.1 p.2)) := by
  let U := actualLocalTensorHeatPatch (I := I)
    (i : M) (A.radius (i : M))
  let ψ := A.cover.partition i
  let F : ℝ × M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
    fun p => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := T₂) p.2 (closedLocalFieldOfHigher cov A i u p.1 p.2)
  let Z : ℝ × M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
    fun p => zeroSection (E →L[ℝ] E →L[ℝ] ℝ) T₂ p.2
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ U) :=
    isOpen_univ.prod (isOpen_actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)))
  have hFpatch : ContinuousOn F ((Set.univ : Set ℝ) ×ˢ U) :=
    A.continuousOn_closedLocalField_totalSpace_on_patch cov i u
  have hZ : Continuous Z :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_snd
  have hZset : IsOpen
      ((Set.univ : Set ℝ) ×ˢ (tsupport ψ)ᶜ) :=
    isOpen_univ.prod (isClosed_tsupport ψ).isOpen_compl
  have hFzero : EqOn F Z ((Set.univ : Set ℝ) ×ˢ (tsupport ψ)ᶜ) := by
    intro p hp
    have hψzero : ψ p.2 = 0 := by
      by_contra hne
      have hsupport : p.2 ∈ Function.support ψ := by
        simpa [Function.mem_support] using hne
      exact hp.2 (subset_tsupport ψ hsupport)
    simp [F, Z, closedLocalFieldOfHigher, cutoffLocalTensorOfMatrix,
      ψ, hψzero, zeroSection]
  change Continuous F
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hpU : p.2 ∈ U
  · exact hFpatch.continuousAt
      (hU.mem_nhds ⟨Set.mem_univ _, hpU⟩)
  · have hpZ : p ∈ (Set.univ : Set ℝ) ×ˢ (tsupport ψ)ᶜ := by
      refine ⟨Set.mem_univ _, ?_⟩
      intro hsupport
      exact hpU (A.cover.pieces_subset_domain i hsupport)
    have hev : F =ᶠ[𝓝 p] Z := by
      filter_upwards [hZset.mem_nhds hpZ] with z hz
      exact hFzero hz
    exact hZ.continuousAt.congr_of_eventuallyEq hev

theorem closedLocalFieldOfHigher_eq_localFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) (ht : t ∈ Ioc t₀ A.commonTerminalTime) :
    closedLocalFieldOfHigher cov A i u t =
      (localFieldOfHigher cov A i u).toFun t := by
  have hr : A.radius (i : M) ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  have htPhysical : t ∈ Ioc t₀
      (FiniteClassicalTensorHeatField.physicalTerminalTime
        t₀ T (A.radius (i : M))) :=
    ⟨ht.1, ht.2.trans (A.commonTerminalTime_le cov i)⟩
  have htNormalized : FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (i : M)) t ∈ Ioc t₀ T :=
    FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr htPhysical
  have hcoeff : (fun y : M => FiniteParabolicC2AlphaBanach.completedValue
        A.time_lt A.alpha_pos (normalizedHigherSolution u)
        (FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t,
         normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y)) =
      normalizedTensorHeatCoefficientSlice (I := I)
        (i : M) (A.radius (i : M)) (normalizedHigherSolution u)
        (FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t) := by
    funext y
    exact FiniteParabolicC2AlphaBanach.completedValue_of_mem
      A.time_lt A.alpha_pos (normalizedHigherSolution u)
      _ ⟨htNormalized, Set.mem_univ _⟩
  change cutoffLocalTensorOfMatrix (I := I)
      (trivializationAt E TM (i : M)) b (A.cover.partition i)
      (fun y => FiniteParabolicC2AlphaBanach.completedValue
        A.time_lt A.alpha_pos (normalizedHigherSolution u)
        (FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t,
         normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y)) =
      cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M)) (normalizedHigherSolution u)
          (FiniteClassicalTensorHeatField.normalizedTime t₀
            (A.radius (i : M)) t))
  rw [hcoeff]

theorem closedLocalFieldOfHigher_initial
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    closedLocalFieldOfHigher cov A i u t₀ =
      localInitialTrace cov A i u := by
  unfold closedLocalFieldOfHigher localInitialTrace
  congr 1
  funext y
  simp only [FiniteClassicalTensorHeatField.normalizedTime, sub_self,
    mul_zero, add_zero]
  rw [FiniteParabolicC2AlphaBanach.completedValue_initial]
  unfold normalizedHigherSolution
  rw [FiniteParabolicC2AlphaBanach.initialTraceL_fiberPostcompL]
  rfl

/-- At a fixed manifold point, completed local reconstruction is continuous
in physical time as a path in the genuine tensor fibre. -/
theorem continuous_closedLocalFieldOfHigher_at
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (x : M) :
    Continuous (fun t : ℝ => closedLocalFieldOfHigher cov A i u t x) := by
  let S := cutoffLocalTensorSynthesisAt (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i) x
  have hinput : Continuous (fun t : ℝ =>
      FiniteParabolicC2AlphaBanach.completedValue
        A.time_lt A.alpha_pos (normalizedHigherSolution u)
        (FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t,
         normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)) := by
    apply (FiniteParabolicC2AlphaBanach.continuous_completedValue
      A.time_lt A.alpha_pos (normalizedHigherSolution u)).comp
    have htime : Continuous (fun t : ℝ =>
        FiniteClassicalTensorHeatField.normalizedTime t₀
          (A.radius (i : M)) t) := by
      unfold FiniteClassicalTensorHeatField.normalizedTime
      fun_prop
    exact htime.prodMk continuous_const
  change Continuous (fun t : ℝ => S
    (FiniteParabolicC2AlphaBanach.completedValue
      A.time_lt A.alpha_pos (normalizedHigherSolution u)
      (FiniteClassicalTensorHeatField.normalizedTime t₀
        (A.radius (i : M)) t,
       normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x)))
  exact S.continuous.comp hinput

/-- Sum the canonically completed local fields in the same finite atlas as
the positive-time reconstruction. -/
def closedAtlasFieldOfHigher
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) : ∀ x : M, T₂ x :=
  fun x => ∑ i : A.cover.Index, closedLocalFieldOfHigher cov A i (u i) t x

theorem continuous_closedAtlasFieldOfHigher_totalSpace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    Continuous (fun p : ℝ × M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) p.2
        (closedAtlasFieldOfHigher cov A u p.1 p.2)) := by
  simpa only [closedAtlasFieldOfHigher] using
    (continuous_finset_sum_tensorSections (I := I)
      (s := Finset.univ)
      (f := fun i p => closedLocalFieldOfHigher cov A i (u i) p.1 p.2)
      (fun i => A.continuous_closedLocalField_totalSpace cov i (u i)))

theorem continuous_closedAtlasFieldOfHigher_at
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (x : M) :
    Continuous (fun t : ℝ => closedAtlasFieldOfHigher cov A u t x) := by
  change Continuous (fun t : ℝ =>
    ∑ i : A.cover.Index, closedLocalFieldOfHigher cov A i (u i) t x)
  apply continuous_finsetSum
  intro i _hi
  exact A.continuous_closedLocalFieldOfHigher_at cov i (u i) x

/-- At every fixed manifold point, the intrinsic Hilbert--Schmidt energy of
the completed atlas tensor is continuous across the canonical initial trace. -/
theorem continuous_closedAtlasFieldOfHigher_normSq_at
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (x : M) :
    Continuous (fun t : ℝ => covariantTwoTensorNormSq
      (closedAtlasFieldOfHigher cov A u t) x) := by
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let bₓ := stdOrthonormalBasis ℝ (TM x)
  change Continuous (fun t : ℝ =>
    ∑ i, ∑ j, (closedAtlasFieldOfHigher cov A u t x (bₓ i) (bₓ j)) ^ 2)
  apply continuous_finsetSum
  intro i _hi
  apply continuous_finsetSum
  intro j _hj
  have hfield := A.continuous_closedAtlasFieldOfHigher_at cov u x
  have hfirst : Continuous (fun t : ℝ =>
      closedAtlasFieldOfHigher cov A u t x (bₓ i)) :=
    (ContinuousLinearMap.apply ℝ (TM x →L[ℝ] ℝ) (bₓ i)).continuous.comp hfield
  have hscalar : Continuous (fun t : ℝ =>
      closedAtlasFieldOfHigher cov A u t x (bₓ i) (bₓ j)) :=
    (ContinuousLinearMap.apply ℝ ℝ (bₓ j)).continuous.comp hfirst
  exact hscalar.pow 2

/-- The completed atlas tensor has jointly continuous intrinsic energy on
space-time. The metric variation is handled by the inverse local Gram matrix,
so no regularity of a pointwise chosen orthonormal basis is presumed. -/
theorem continuous_closedAtlasFieldOfHigher_normSq
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    Continuous (fun p : ℝ × M => covariantTwoTensorNormSq
      (closedAtlasFieldOfHigher cov A u p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  classical
  let e := trivializationAt E TM p₀.2
  let bas : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hp : p₀.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p₀.2
  have hframe (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun p : ℝ × M =>
        TotalSpace.mk' E p.2 (e.localFrame bas i p.2)) p₀ := by
    have hs := (contMDiffAt_localFrame_of_mem
      (I := I) (n := 3) e bas i hp).continuousAt
    exact hs.comp continuous_snd.continuousAt
  have hfield :=
    (A.continuous_closedAtlasFieldOfHigher_totalSpace cov u).continuousAt (x := p₀)
  haveI : IsContinuousRiemannianBundle E TM := by
    obtain ⟨g, hg, hinner⟩ :=
      (inferInstance : IsContMDiffRiemannianBundle I 2 E TM).exists_contMDiff
    exact ⟨g, hg.continuous, hinner⟩
  have hcov (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) p.2
          (closedAtlasFieldOfHigher cov A u p.1 p.2
            (e.localFrame bas i p.2))) p₀ :=
    hfield.clm_bundle_apply (hframe i)
  have hriesz : ContinuousAt (fun p : ℝ × M =>
      TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun x : M => T₁ x →L[ℝ] TM x) p.2
        (rieszMap (I := I) p.2)) p₀ := by
    have hs := (rieszMap_mdifferentiableAt (I := I) (E := E) p₀.2).continuousAt
    exact hs.comp continuous_snd.continuousAt
  have hraised (i : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun p : ℝ × M =>
        TotalSpace.mk' E p.2
          (raisedCovariantTwoTensor (I := I) (E := E)
            (closedAtlasFieldOfHigher cov A u p.1) p.2
              (e.localFrame bas i p.2))) p₀ := by
    simpa only [raisedCovariantTwoTensor, ContinuousLinearMap.comp_apply] using
      hriesz.clm_bundle_apply (hcov i)
  have hinvSpace : ContinuousAt (fun x : M =>
      (show Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ from
          localFrameGramMatrix (I := I) e bas x)⁻¹) p₀.2 :=
    ((contMDiffOn_localFrameGramMatrix_inv (I := I) (E := E)
      e bas e.open_baseSet (Set.Subset.rfl)).continuousOn).continuousAt
      (e.open_baseSet.mem_nhds hp)
  have hinv := hinvSpace.comp continuous_snd.continuousAt
  have hentry (i j : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun p : ℝ × M =>
        ((show Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ from
            localFrameGramMatrix (I := I) e bas p.2)⁻¹) i j) p₀ :=
    (continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hinv)
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun p : ℝ × M =>
        ((show Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ from
            localFrameGramMatrix (I := I) e bas p.2)⁻¹) i j *
          inner ℝ
            (raisedCovariantTwoTensor (I := I) (E := E)
              (closedAtlasFieldOfHigher cov A u p.1) p.2
                (e.localFrame bas i p.2))
            (raisedCovariantTwoTensor (I := I) (E := E)
              (closedAtlasFieldOfHigher cov A u p.1) p.2
                (e.localFrame bas j p.2))) p₀ :=
    (hentry i j).mul ((hraised i).inner_bundle (hraised j))
  have hsum : ContinuousAt (fun p : ℝ × M =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((show Matrix (Fin (Module.finrank ℝ E))
            (Fin (Module.finrank ℝ E)) ℝ from
              localFrameGramMatrix (I := I) e bas p.2)⁻¹) i j *
            inner ℝ
              (raisedCovariantTwoTensor (I := I) (E := E)
                (closedAtlasFieldOfHigher cov A u p.1) p.2
                  (e.localFrame bas i p.2))
              (raisedCovariantTwoTensor (I := I) (E := E)
                (closedAtlasFieldOfHigher cov A u p.1) p.2
                  (e.localFrame bas j p.2))) p₀ := by
    apply tendsto_finsetSum Finset.univ
    intro i _hi
    apply tendsto_finsetSum Finset.univ
    intro j _hj
    exact hterm i j
  have heq (p : ℝ × M) (hp : p.2 ∈ e.baseSet) :
      covariantTwoTensorNormSq
        (closedAtlasFieldOfHigher cov A u p.1) p.2 =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((show Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ from
                localFrameGramMatrix (I := I) e bas p.2)⁻¹) i j *
              inner ℝ
                (raisedCovariantTwoTensor (I := I) (E := E)
                  (closedAtlasFieldOfHigher cov A u p.1) p.2
                    (e.localFrame bas i p.2))
                (raisedCovariantTwoTensor (I := I) (E := E)
                  (closedAtlasFieldOfHigher cov A u p.1) p.2
                    (e.localFrame bas j p.2)) :=
    covariantTwoTensorNormSq_eq_sum_inverseGram
      (I := I) (E := E) (closedAtlasFieldOfHigher cov A u p.1) e bas hp
  change Filter.Tendsto
    (fun p : ℝ × M => covariantTwoTensorNormSq
      (closedAtlasFieldOfHigher cov A u p.1) p.2)
    (𝓝 p₀)
    (𝓝 (covariantTwoTensorNormSq
      (closedAtlasFieldOfHigher cov A u p₀.1) p₀.2))
  rw [heq p₀ hp]
  apply hsum.congr'
  have hopen : IsOpen ((fun p : ℝ × M => p.2) ⁻¹' e.baseSet) :=
    e.open_baseSet.preimage continuous_snd
  filter_upwards [hopen.mem_nhds hp] with p hp
  exact (heq p hp).symm

theorem closedAtlasFieldOfHigher_eq_atlasFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioc t₀ A.commonTerminalTime) :
    closedAtlasFieldOfHigher cov A u t =
      (atlasFieldOfHigher cov A u).toFun t := by
  funext x
  simp only [closedAtlasFieldOfHigher, atlasFieldOfHigher_toFun]
  apply Finset.sum_congr rfl
  intro i _hi
  exact congrFun (A.closedLocalFieldOfHigher_eq_localFieldOfHigher
    cov i (u i) t ht) x

theorem closedAtlasFieldOfHigher_initial
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    closedAtlasFieldOfHigher cov A u t₀ = atlasInitialTrace cov A u := by
  funext x
  simp only [closedAtlasFieldOfHigher, atlasInitialTrace]
  apply Finset.sum_congr rfl
  intro i _hi
  exact congrFun (A.closedLocalFieldOfHigher_initial cov i (u i)) x

/-- For represented fields the canonical completed path carries interior
vanishing to the physical terminal time. -/
theorem atlasFieldOfHigher_terminal_zero_of_open_zero
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (hzero : ∀ t ∈ Ioo t₀ A.commonTerminalTime,
      (atlasFieldOfHigher cov A u).toFun t = 0) :
    (atlasFieldOfHigher cov A u).toFun A.commonTerminalTime = 0 := by
  have hT : t₀ < A.commonTerminalTime := A.lt_commonTerminalTime cov
  have hterminal : A.commonTerminalTime ∈ Ioc t₀ A.commonTerminalTime :=
    ⟨hT, le_rfl⟩
  rw [← A.closedAtlasFieldOfHigher_eq_atlasFieldOfHigher
    cov u A.commonTerminalTime hterminal]
  funext x
  have hcont : ContinuousOn
      (fun s : ℝ => closedAtlasFieldOfHigher cov A u s x)
      (Icc t₀ A.commonTerminalTime) :=
    (A.continuous_closedAtlasFieldOfHigher_at cov u x).continuousOn
  have hzeroOpen : EqOn
      (fun s : ℝ => closedAtlasFieldOfHigher cov A u s x)
      (fun _ => 0) (Ioo t₀ A.commonTerminalTime) := by
    intro s hs
    change closedAtlasFieldOfHigher cov A u s x = 0
    rw [A.closedAtlasFieldOfHigher_eq_atlasFieldOfHigher cov u s
      ⟨hs.1, hs.2.le⟩]
    exact congrFun (hzero s hs) x
  have hzeroClosed := hzeroOpen.of_subset_closure hcont
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])
  exact hzeroClosed ⟨hT.le, le_rfl⟩

theorem atlasFieldOfHigher_zero_on_Ioc_of_open_zero
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (hzero : ∀ t ∈ Ioo t₀ A.commonTerminalTime,
      (atlasFieldOfHigher cov A u).toFun t = 0) :
    ∀ t ∈ Ioc t₀ A.commonTerminalTime,
      (atlasFieldOfHigher cov A u).toFun t = 0 := by
  intro t ht
  by_cases hlt : t < A.commonTerminalTime
  · exact hzero t ⟨ht.1, hlt⟩
  · have htT : t = A.commonTerminalTime :=
      le_antisymm ht.2 (le_of_not_gt hlt)
    subst t
    exact A.atlasFieldOfHigher_terminal_zero_of_open_zero cov u hzero

end RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
