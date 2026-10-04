import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoefficientLocalization
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity

/-!
# A fixed-background tensor-heat producer for arbitrary C² metrics

The metric is the supplied `g₀`, without smoothing or replacement. A single
auxiliary affine connection is constructed from the smooth manifold, before
any chart, basis, interval or source is chosen. Its induced regularity gives
actual C¹ coordinate coefficients and scale-correct bounded local right
inverses with zero initial trace.

This is local linear tensor heat in the existing unweighted Hölder source
space. It does not construct a Ricci--DeTurck solution, an arbitrary-C² initial
extension, or the canonical Point-4 theorem. The stronger model-boundaryless
hypothesis remains explicit.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

open Bundle FiberBundle Set Filter CovariantDerivative
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [I.Boundaryless]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

-- These orders come from the smooth manifold, never from metric smoothing.
local instance fixedBackgroundTangentThree : ContMDiffVectorBundle 3 E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by decide)
local instance fixedBackgroundTangentTwo : ContMDiffVectorBundle 2 E TM I :=
  ContMDiffVectorBundle.of_le (n := 3) (by norm_num)

-- The finite coefficient model has no ambient metric dependency.
@[reducible] local instance fixedBackgroundCoordinateNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup (Fin d × Fin d → ℝ) := tensorCoordinateNormedAddCommGroup
@[reducible] local instance fixedBackgroundCoordinateNormedSpace {d : ℕ} :
    NormedSpace ℝ (Fin d × Fin d → ℝ) := tensorCoordinateNormedSpace
@[reducible] local instance fixedBackgroundFirstNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup (E →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateFirstNormedAddCommGroup
@[reducible] local instance fixedBackgroundFirstNormedSpace {d : ℕ} :
    NormedSpace ℝ (E →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateFirstNormedSpace
@[reducible] local instance fixedBackgroundSecondNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateSecondNormedAddCommGroup
@[reducible] local instance fixedBackgroundSecondNormedSpace {d : ℕ} :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateSecondNormedSpace
@[reducible] local instance fixedBackgroundPrincipalNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ] (Fin d × Fin d → ℝ)) :=
  tensorCoordinatePrincipalNormedAddCommGroup
@[reducible] local instance fixedBackgroundPrincipalNormedSpace {d : ℕ} :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ] (Fin d × Fin d → ℝ)) :=
  tensorCoordinatePrincipalNormedSpace
@[reducible] local instance fixedBackgroundFirstCoefficientNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup ((E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ] (Fin d × Fin d → ℝ)) :=
  tensorCoordinateFirstCoefficientNormedAddCommGroup
@[reducible] local instance fixedBackgroundFirstCoefficientNormedSpace {d : ℕ} :
    NormedSpace ℝ ((E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ] (Fin d × Fin d → ℝ)) :=
  tensorCoordinateFirstCoefficientNormedSpace
@[reducible] local instance fixedBackgroundZeroNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup ((Fin d × Fin d → ℝ) →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateZeroNormedAddCommGroup
@[reducible] local instance fixedBackgroundZeroNormedSpace {d : ℕ} :
    NormedSpace ℝ ((Fin d × Fin d → ℝ) →L[ℝ] (Fin d × Fin d → ℝ)) := tensorCoordinateZeroNormedSpace

/-- One global auxiliary connection, its actual induced regularity, and
local coefficient/right-inverse data for the literal arbitrary C² metric.
No connection, induced-regularity, coefficient-regularity, or solver witness
is an input. All interval and Hölder-source restrictions are explicit. -/
theorem exists_fixedBackground_actualLocalTensorHeat
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM :=
      ⟨g₀.inner, g₀.contMDiff, fun _ _ _ => rfl⟩
    letI : IsContMDiffRiemannianBundle I 1 E TM :=
      IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
    letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
      CovariantDerivative.coordinateThreeModelNormedAddCommGroup
    letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
      CovariantDerivative.coordinateThreeModelNormedSpace
    letI : ∀ x : M, NormedAddCommGroup (T₃ x) :=
      fun x => CovariantDerivative.coordinateThreeFiberNormedAddCommGroup (I := I) x
    letI : ∀ x : M, NormedSpace ℝ (T₃ x) :=
      fun x => CovariantDerivative.coordinateThreeFiberNormedSpace (I := I) x
    letI : TopologicalSpace (TotalSpace
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
      Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
        (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
    letI : FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
      Bundle.ContinuousLinearMap.fiberBundle
        (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
    letI : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
      Bundle.ContinuousLinearMap.vectorBundle
        (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
    ∃ (cov : CovariantDerivative I E TM)
      (hcovTwo : ContMDiffCovariantDerivative cov 2)
      (hcovOne : ContMDiffCovariantDerivative cov 1)
      (htwoTwo : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 2)
      (htwoOne : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1)
      (hthreeOne : ContMDiffCovariantDerivative
        (covariantThreeTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1),
      letI : ContMDiffCovariantDerivative cov 2 := hcovTwo
      letI : ContMDiffCovariantDerivative cov 1 := hcovOne
      letI : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 2 := htwoTwo
      letI : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1 := htwoOne
      letI : ContMDiffCovariantDerivative
        (covariantThreeTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1 := hthreeOne
      ∀ {d : ℕ} (p : M)
        (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)),
        ∀ [MemTrivializationAtlas e], p ∈ e.baseSet →
        ∀ (b : Module.Basis (Fin d) ℝ E) {t₀ T α : ℝ},
        ∀ (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1),
        let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
        ContDiffOn ℝ 1
            (localTensorHeatPrincipalCoefficient (I := I) p e b) U ∧
          ContDiffOn ℝ 1
            (localTensorHeatFirstCoefficient (I := I) cov p e b) U ∧
          ContDiffOn ℝ 1
            (localTensorHeatZeroCoefficient (I := I) cov p e b) U ∧
          ∃ D : TensorHeatLocalizedCoefficientData E (Fin d × Fin d → ℝ),
            D.center = (extChartAt I p) p ∧
            (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
            ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
              TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
                (t₀ := t₀) (T := T)
                D (localTensorHeatPrincipalCoefficient (I := I) p e b)
                (localTensorHeatFirstCoefficient (I := I) cov p e b)
                (localTensorHeatZeroCoefficient (I := I) cov p e b)
                U ((extChartAt I p) p) hα hα1 r ∧
              ∃ Q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
                    (parabolicFiniteCylinder E t₀ T) →L[ℝ]
                  FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α,
                (FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r)
                  (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r)).comp Q =
                    ContinuousLinearMap.id ℝ
                      (ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
                        (parabolicFiniteCylinder E t₀ T)) ∧
                (FiniteParabolicC2AlphaBanach.initialTraceL
                  (X := E) (E := (Fin d × Fin d → ℝ)) hT hα).comp Q = 0 := by
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM :=
    ⟨g₀.inner, g₀.contMDiff, fun _ _ _ => rfl⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    CovariantDerivative.coordinateThreeModelNormedAddCommGroup
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    CovariantDerivative.coordinateThreeModelNormedSpace
  letI : ∀ x : M, NormedAddCommGroup (T₃ x) :=
    fun x => CovariantDerivative.coordinateThreeFiberNormedAddCommGroup (I := I) x
  letI : ∀ x : M, NormedSpace ℝ (T₃ x) :=
    fun x => CovariantDerivative.coordinateThreeFiberNormedSpace (I := I) x
  letI : TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
  letI : FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
    Bundle.ContinuousLinearMap.fiberBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
  letI : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
    Bundle.ContinuousLinearMap.vectorBundle
      (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
  obtain ⟨cov, hcovTwo⟩ :=
    CovariantDerivative.exists_contMDiffAffineConnection_two
      (I := I) (E := E) (M := M)
  letI : ContMDiffCovariantDerivative cov 2 := hcovTwo
  have hcovOne : ContMDiffCovariantDerivative cov 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_one_of_contMDiffCovariantDerivative_two
      (I := I) (F := E) (V := TM)
  letI : ContMDiffCovariantDerivative cov 1 := hcovOne
  have htwoTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_two cov
  letI : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 := htwoTwo
  have htwoOne : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_one cov
  letI : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := htwoOne
  have hthreeOne : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantThreeTensor_one cov
  letI : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := hthreeOne
  refine ⟨cov, hcovTwo, hcovOne, htwoTwo, htwoOne, hthreeOne, ?_⟩
  intro d p e _ hpFrame b t₀ T α hT hα hα1
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients
      (I := I) cov p e b
  refine ⟨hA, hB, hC, ?_⟩
  exact exists_radius_actualLocalTensorHeatUnitBall_zeroTrace
    (I := I) cov p e hpFrame b hT hα hα1

end AnalyticPDE
end RicciFlow
