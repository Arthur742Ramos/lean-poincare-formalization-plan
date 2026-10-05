import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.BoundarylessTensorHeatCoefficients
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoefficientLocalization

/-!
# Genuine local tensor-heat inversion with manifold boundarylessness

The original analytic `_of_contDiffOn_unitBall_zeroTrace` construction is
used unchanged. Coefficient regularity comes from the actual literal-metric
geometry, and domain openness from the proved preferred-chart target result.
No local chart, analytic solver or coefficient certificate is an input.
The historical model-boundaryless wrappers remain unchanged.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold Topology ContDiff

namespace RicciFlow.AnalyticPDE.ManifoldBoundaryless

open Bundle FiberBundle CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [BoundarylessManifold I M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

variable {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

/- Select the same model and fiber norms as the geometric regularity theorem,
so its induced-connection class hypotheses refer to definitionally identical
two- and three-covariant-tensor bundles. -/
@[reducible] local instance localizationTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance localizationTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance localizationTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance localizationTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance localizationThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance localizationThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance localizationThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance localizationThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x

/-- Point-centered, scale-correct local inversion for the genuine connection
Laplacian.  The returned radius is already small enough both for analytic
invertibility and for exact coefficient agreement throughout the normalized
closed unit ball. -/
theorem exists_radius_actualLocalTensorHeatUnitBall_zeroTrace
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
          (t₀ := t₀) (T := T)
          D (localTensorHeatPrincipalCoefficient (I := I) p e b)
          (localTensorHeatFirstCoefficient (I := I) cov p e b)
          (localTensorHeatZeroCoefficient (I := I) cov p e b)
          ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet)
          ((extChartAt I p) p) hα hα1 r ∧
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target (I := I) p) e.open_baseSet
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨mem_extChartAt_target p, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    RicciFlow.AnalyticPDE.ManifoldBoundaryless.contDiffOn_actualTensorHeatCoefficients
      (I := I) cov p e b
  obtain ⟨D, hDcenter, _hDA, _hDB, _hDC, hDcut, δ, hδ, hlocal⟩ :=
    exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace
      (I := I) cov p e b hpFrame (mem_extChartAt_source p)
        (K := K) (U := U) isCompact_singleton hU
        (by simpa [K] using hpU) (by simp [K])
        hA hB hC hT hα hα1
  exact ⟨D, hDcenter, hDcut, δ, hδ, hlocal⟩

end RicciFlow.AnalyticPDE.ManifoldBoundaryless
