import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatCoercivity

-- SOURCE-only exact signature and actual-axiom probe, UNCOMPILED.
open Bundle
open scoped BigOperators Manifold ContDiff Topology
open PoincareCurvature.FiniteCoordinateBilinear

universe u v w

abbrev ExpectedInitialMetricHeatCoercivity :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (p : M),
    ∃ c > 0, ∃ D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        RicciFlow.AnalyticPDE.EuclideanBoundedC2Data (Module.finrank ℝ E),
      (∀ᶠ z in 𝓝 (RicciFlow.AnalyticPDE.initialMetricCoordinatePoint
          (I := I) p (Module.finBasis ℝ E)),
        ∀ i j, (D i j).value z = RicciFlow.AnalyticPDE.initialMetricCoordinates
          g₀ p (Module.finBasis ℝ E) z i j) ∧
      (∀ z i j, (D i j).value z = (D j i).value z) ∧
      (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) ∧
      (∀ t : ℝ, 0 < t → ∀ z v, c * ‖v‖ ^ 2 ≤
        ofMatrix (RicciFlow.AnalyticPDE.matrixHeatSemigroupND
          (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y i j => (D i j).value y) z) v v) ∧
      (∀ i j a b, UniformContinuous ((D i j).second a b :
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ))

def initialMetricHeatCoercivityFullSignatureAssignment :
    ExpectedInitialMetricHeatCoercivity.{u,v,w} :=
  @RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData_with_coercive_heat

#check @RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
#check @RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData_with_coercive_heat

#print axioms RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
#print axioms RicciFlow.AnalyticPDE.matrixHeatSemigroupND_pos_of_coercive
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData_with_coercive_heat
#print axioms RicciFlow.AnalyticPDE.localizedC2Data_weighted_heat_hessian_trace

example {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (c : ℝ)
    (hcoercive : ∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin d → ℝ) :
    c * ‖v‖ ^ 2 ≤ ofMatrix
      (RicciFlow.AnalyticPDE.matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v :=
  RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
    F c hcoercive ht x v

-- The lower-bound proof uses no selected nonzero vector or positive-rank premise.
example {n : ℕ}
    (F : Fin 0 → Fin 0 → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (c : ℝ)
    (hcoercive : ∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin 0 → ℝ) :
    c * ‖v‖ ^ 2 ≤ ofMatrix
      (RicciFlow.AnalyticPDE.matrixHeatSemigroupND n 0 t (fun y i j => F i j y) x) v v :=
  RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
    F c hcoercive ht x v
