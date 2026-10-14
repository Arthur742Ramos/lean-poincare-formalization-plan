import DifferentialGeometry.Geometry.Connection.LeviCivita.MetricCompatible
import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardRegularity
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem metric_alias : DifferentialGeometry.SmoothRiemannianMetric I M =
    RicciFlow.SmoothForward.Metric (I := I) (M := M) := rfl

def constantC2Family (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    CovariantDerivative.TimeDependentRiemannianMetric (I := I) (M := M) :=
  fun _ => RicciFlow.SmoothForward.toC2 g

@[simp] theorem constantC2Family_inner
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TangentSpace I x) :
    (constantC2Family g t).inner x u v = g.inner x u v :=
  RicciFlow.SmoothForward.toC2_inner g x u v

theorem metricCompatible_iff
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(RicciFlow.SmoothForward.toC2 g).toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) ↔
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible cov g := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 g).toRiemannianMetric⟩
  change cov.IsMetricCompatibleTangent ↔
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible cov g
  constructor
  · intro h Y Z x hY hZ _ v
    exact h hY hZ v
  · intro h x Y Z hY hZ v
    exact h hY hZ (Set.mem_univ x) v

def projectChosen (g : RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (t : ℝ) : CovariantDerivative I E (TangentSpace I : M → Type _) :=
  (constantC2Family g).someContMDiffLeviCivitaConnection t

theorem projectChosen_metricCompatible
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (projectChosen g t) g := by
  apply (metricCompatible_iff g (projectChosen g t)).mp
  exact ((constantC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t).2

theorem projectChosen_torsion
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    (projectChosen g t).torsion = 0 :=
  ((constantC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t).1

end ChartPort
