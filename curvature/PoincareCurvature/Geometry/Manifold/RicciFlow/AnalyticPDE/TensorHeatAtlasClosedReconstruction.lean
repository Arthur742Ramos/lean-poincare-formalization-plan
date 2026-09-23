import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasInitial
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace

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
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

@[reducible] local instance closedAtlasTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x

@[reducible] local instance closedAtlasTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x

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
