import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MatrixHeatCoercivity

-- SOURCE-only whole-type and actual-axiom probe, UNCOMPILED.
open PoincareCurvature.FiniteCoordinateBilinear

abbrev ExpectedMatrixHeatCoercivity :=
  ∀ {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (c : ℝ),
    (∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v) →
    ∀ {t : ℝ}, 0 < t → ∀ (x : Fin n → ℝ) (v : Fin d → ℝ),
      c * ‖v‖ ^ 2 ≤ ofMatrix
        (RicciFlow.AnalyticPDE.matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v

def matrixHeatCoercivityFullSignatureAssignment : ExpectedMatrixHeatCoercivity :=
  @RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity

abbrev ExpectedMatrixHeatPositivity :=
  ∀ {n d : ℕ}
    (F : Fin d → Fin d → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {c : ℝ}, 0 < c →
    (∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v) →
    ∀ {t : ℝ}, 0 < t → ∀ (x : Fin n → ℝ) (v : Fin d → ℝ), v ≠ 0 →
      0 < ofMatrix
        (RicciFlow.AnalyticPDE.matrixHeatSemigroupND n d t (fun y i j => F i j y) x) v v

def matrixHeatPositivityFullSignatureAssignment : ExpectedMatrixHeatPositivity :=
  @RicciFlow.AnalyticPDE.matrixHeatSemigroupND_pos_of_coercive

#check @RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
#check @RicciFlow.AnalyticPDE.matrixHeatSemigroupND_pos_of_coercive

#print axioms RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
#print axioms RicciFlow.AnalyticPDE.matrixHeatSemigroupND_pos_of_coercive

-- No positive-rank or selected nonzero-vector premise enters the lower bound.
example {n : ℕ}
    (F : Fin 0 → Fin 0 → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (c : ℝ)
    (hcoercive : ∀ y v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => F i j y) v v)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (v : Fin 0 → ℝ) :
    c * ‖v‖ ^ 2 ≤ ofMatrix
      (RicciFlow.AnalyticPDE.matrixHeatSemigroupND n 0 t (fun y i j => F i j y) x) v v :=
  RicciFlow.AnalyticPDE.matrixHeatSemigroupND_preserves_coercivity
    F c hcoercive ht x v
