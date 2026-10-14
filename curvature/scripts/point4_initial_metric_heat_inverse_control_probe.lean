import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatInverseControl

-- Source-only whole-type and actual-axiom probe; native qualification pending.
open Bundle Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedCoerciveMatrixIsUnit :=
  ∀ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) {c : ℝ}, 0 < c →
    (∀ v : Fin d → ℝ, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) → IsUnit A

def coerciveMatrixIsUnitFullSignatureAssignment : ExpectedCoerciveMatrixIsUnit :=
  @isUnit_matrix_of_coercive

abbrev ExpectedCoerciveMatrixInverseBound :=
  ∀ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) {c : ℝ}, 0 < c →
    (∀ v : Fin d → ℝ, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) →
    ∀ i j : Fin d, |A⁻¹ i j| ≤ 1 / c

def coerciveMatrixInverseBoundFullSignatureAssignment : ExpectedCoerciveMatrixInverseBound :=
  @abs_matrix_inv_entry_le_of_coercive

abbrev ExpectedCoerciveMatrixInverseDifference :=
  ∀ {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) {c ε : ℝ}, 0 < c →
    (∀ v : Fin d → ℝ, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) →
    (∀ v : Fin d → ℝ, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => B i j) v v) →
    0 ≤ ε → (∀ p q, |A p q - B p q| ≤ ε) →
    ∀ i j : Fin d, |A⁻¹ i j - B⁻¹ i j| ≤ (d : ℝ) ^ 2 * (1 / c) ^ 2 * ε

def coerciveMatrixInverseDifferenceFullSignatureAssignment :
    ExpectedCoerciveMatrixInverseDifference :=
  @abs_matrix_inv_sub_inv_entry_le_of_coercive

abbrev ExpectedMatrixInitialHeatErrorLimit :=
  ∀ {n d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data n),
    Tendsto (matrixInitialHeatValueError D) (𝓝 0) (𝓝 0)

def matrixInitialHeatErrorLimitFullSignatureAssignment : ExpectedMatrixInitialHeatErrorLimit :=
  @tendsto_matrixInitialHeatValueError_zero

abbrev ExpectedMatrixInitialHeatInverseDifference :=
  ∀ {n d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    ∀ {t : ℝ}, 0 < t → ∀ (z : Fin n → ℝ) (i j : Fin d),
    |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
      (Matrix.of (fun a b => (D a b).value z))⁻¹ i j| ≤
      (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t

def matrixInitialHeatInverseDifferenceFullSignatureAssignment :
    ExpectedMatrixInitialHeatInverseDifference :=
  @abs_matrixInitialHeat_inv_sub_initial_inv_le

abbrev ExpectedInitialMetricHeatInverseControl :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)) (p : M),
    ∃ c > 0, ∃ D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        EuclideanBoundedC2Data (Module.finrank ℝ E),
      (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)),
        ∀ i j, (D i j).value z = initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j) ∧
      (∀ z i j, (D i j).value z = (D j i).value z) ∧
      (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) ∧
      (∀ t : ℝ, 0 < t → ∀ z v, c * ‖v‖ ^ 2 ≤
        ofMatrix (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y a b => (D a b).value y) z) v v) ∧
      (∀ i j a b, UniformContinuous ((D i j).second a b :
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ)) ∧
      (∀ t : ℝ, 0 < t → ∀ z i j,
        |(Matrix.of (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y a b => (D a b).value y) z))⁻¹ i j -
          (Matrix.of (fun a b => (D a b).value z))⁻¹ i j| ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t) ∧
      Tendsto (fun t : ℝ =>
        (Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t)
        (𝓝 0) (𝓝 0)

def initialMetricHeatInverseControlFullSignatureAssignment :
    ExpectedInitialMetricHeatInverseControl.{u,v,w} :=
  @exists_initialMetricLocalizedHeatData_with_inverse_control

-- Rank zero is accepted by the actual invertibility theorem.
example (A : Matrix (Fin 0) (Fin 0) ℝ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : Fin 0 → ℝ, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) :
    IsUnit A := isUnit_matrix_of_coercive A hc hcoer

-- The actual finite heat-error definition and limit include empty matrices.
example {n : ℕ} (D : Fin 0 → Fin 0 → EuclideanBoundedC2Data n) :
    Tendsto (matrixInitialHeatValueError D) (𝓝 0) (𝓝 0) :=
  tendsto_matrixInitialHeatValueError_zero D

set_option pp.universes false
set_option format.width 200
#check @isUnit_matrix_of_coercive
#check @abs_matrix_inv_entry_le_of_coercive
#check @abs_matrix_inv_sub_inv_entry_le_of_coercive
#check @tendsto_matrixInitialHeatValueError_zero
#check @abs_matrixInitialHeat_inv_sub_initial_inv_le
#check @exists_initialMetricLocalizedHeatData_with_inverse_control

-- Exactly the six new semantic theorem declarations, one actual AX record each.
#print axioms RicciFlow.AnalyticPDE.isUnit_matrix_of_coercive
#print axioms RicciFlow.AnalyticPDE.abs_matrix_inv_entry_le_of_coercive
#print axioms RicciFlow.AnalyticPDE.abs_matrix_inv_sub_inv_entry_le_of_coercive
#print axioms RicciFlow.AnalyticPDE.tendsto_matrixInitialHeatValueError_zero
#print axioms RicciFlow.AnalyticPDE.abs_matrixInitialHeat_inv_sub_initial_inv_le
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData_with_inverse_control
