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

end RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
