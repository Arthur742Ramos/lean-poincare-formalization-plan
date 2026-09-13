import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteAtlas
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoordinateOperator

/-!
# Exact local equations for the finite tensor-heat atlas

This file starts the equation-level verification of the finite atlas.  It
records the pointwise consequence of each stored coordinate right inverse and
checks that the index convention used by geometric reconstruction recovers
the pair-indexed coordinate solution without a transpose.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Set
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative
open PoincareCurvature.Bundle.Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- Applying the stored normalized coordinate operator to one atlas inverse
returns its source exactly. -/
theorem coordinateCauchy_localInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach.coordinateCauchyL
        ((A.coefficients p).principalField A.alpha_pos A.alpha_lt_one
          (A.radius p))
        ((A.coefficients p).firstField A.alpha_pos A.alpha_lt_one
          (A.radius p))
        ((A.coefficients p).zeroField A.alpha_pos A.alpha_lt_one
          (A.radius p))
        (A.localInverse p q) = q := by
  have h := DFunLike.congr_fun (A.right_inverse p) q
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

/-- Pointwise evaluation of the exact coordinate equation. -/
theorem eval_coordinateCauchy_localInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL
          ((A.coefficients p).principalField A.alpha_pos A.alpha_lt_one
            (A.radius p))
          ((A.coefficients p).firstField A.alpha_pos A.alpha_lt_one
            (A.radius p))
          ((A.coefficients p).zeroField A.alpha_pos A.alpha_lt_one
            (A.radius p))
          (A.localInverse p q)) =
      ParabolicC0AlphaBanach.evalCLM z hz q := by
  rw [A.coordinateCauchy_localInverse cov p q]

/-- On the normalized unit ball, the atlas inverse satisfies the coordinate
equation whose coefficients are exactly those of the actual connection
Laplacian.  The factors `r` and `r²` are the genuine parabolic scaling
weights, not additional hypotheses. -/
theorem normalizedLocalEquation_on_unitBall
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (hzBall : z.2 ∈ Metric.closedBall (0 : E) 1) :
    FiniteParabolicC2AlphaBanach.timeDeriv
          (A.localInverse (i : M) q) z -
        (localTensorHeatPrincipalCoefficient (I := I) (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) (i : M) +
              A.radius (i : M) • z.2)
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv
              (A.localInverse (i : M) q) z) +
          A.radius (i : M) •
            localTensorHeatFirstCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.spaceDeriv
                (A.localInverse (i : M) q) z) +
          A.radius (i : M) ^ 2 •
            localTensorHeatZeroCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.value
                (A.localInverse (i : M) q) z)) =
      ParabolicC0AlphaBanach.evalCLM z hz q := by
  obtain ⟨_hzDomain, hA, hB, hC⟩ := A.fields_agree (i : M) z hzBall
  rw [← A.eval_coordinateCauchy_localInverse cov (i : M) q z hz]
  rw [FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL]
  rw [hA, hB, hC]
  simp only [smul_apply]

/-- The matrix used for intrinsic reconstruction has the exact orientation
needed to recover the original pair-indexed coordinate value. -/
@[simp] theorem normalizedLocalSolution_value
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (a c : Fin d) :
    FiniteParabolicC2AlphaBanach.value
        (A.normalizedLocalSolution cov i q) z a c =
      FiniteParabolicC2AlphaBanach.value
        (A.localInverse (i : M) q) z (c, a) := by
  rw [normalizedLocalSolution,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL (hz := hz)]
  rfl

/-- Before multiplication by the partition function, reading the
reconstructed tensor in the intrinsic chart-frame convention gives exactly
the pair-indexed normalized solution. -/
theorem localTensorCoordinates_normalized_reconstruction
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) {x : M}
    (hx : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M))) :
    localTensorCoordinates (I := I) (i : M)
        (trivializationAt E TM (i : M)) b
        (localTensorOfMatrix (I := I) (trivializationAt E TM (i : M)) b
          (normalizedTensorHeatCoefficientSlice (I := I)
            (i : M) (A.radius (i : M))
            (A.normalizedLocalSolution cov i q) s))
        ((extChartAt I (i : M)) x) =
      FiniteParabolicC2AlphaBanach.value
        (A.localInverse (i : M) q)
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x) := by
  funext out
  rcases out with ⟨a, c⟩
  have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
    A.patch_subset_trivialization (i : M) hx
  have hxChart : x ∈ (extChartAt I (i : M)).source := hx.1
  have hz : (s, normalizedTensorHeatCoordinate (I := I)
      (i : M) (A.radius (i : M)) x) ∈
      parabolicFiniteCylinder E t₀ T := by
    simpa using hs
  simp [localTensorCoordinates, localTwoTensorComponentInChart,
    writtenInExtChartAt]
  simp_all only [mfld_simps, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rw [localTwoTensorComponent_apply_of_mem
    (I := I) (trivializationAt E TM (i : M)) b _ hxFrame]
  rw [localTensorOfMatrix_localFrame
    (I := I) (trivializationAt E TM (i : M)) b _ hxFrame]
  exact A.normalizedLocalSolution_value cov i q _ hz c a

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
