import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatInverseFreezing

-- Source-only whole-type and actual-axiom probe. No native qualification claim.
open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedMatrixInitialHeatBasepointBound :=
  ∀ {n d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    ∀ {t : ℝ}, 0 < t → ∀ (z z₀ : Fin n → ℝ) (i j : Fin d),
      |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
        (Matrix.of (fun a b => (D a b).value z₀))⁻¹ i j| ≤
        (d : ℝ) ^ 2 * (1 / c) ^ 2 *
          (matrixInitialHeatValueError D t + matrixInitialSpatialValueError D z z₀)

def matrixInitialHeatBasepointBoundFullSignatureAssignment :
    ExpectedMatrixInitialHeatBasepointBound :=
  @abs_matrixInitialHeat_inv_sub_basepoint_inv_le

abbrev ExpectedMatrixInitialHeatCoefficientFreezing :=
  ∀ {n d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    ∀ (z₀ : Fin n → ℝ) {ε : ℝ}, 0 < ε →
      ∃ T > 0, ∃ U : Set (Fin n → ℝ), U ∈ 𝓝 z₀ ∧
        ∀ t : ℝ, 0 < t → t < T → ∀ z ∈ U, ∀ i j : Fin d,
          |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
            (Matrix.of (fun a b => (D a b).value z₀))⁻¹ i j| < ε

def matrixInitialHeatCoefficientFreezingFullSignatureAssignment :
    ExpectedMatrixInitialHeatCoefficientFreezing :=
  @matrixInitialHeat_inverse_coefficients_freeze

abbrev ExpectedLiteralInitialMetricCoefficientFreezing :=
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
      (∀ ε : ℝ, 0 < ε → ∃ T > 0,
        ∃ U : Set (Fin (Module.finrank ℝ E) → ℝ),
          U ∈ 𝓝 (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) ∧
          (∀ z ∈ U, ∀ i j, (D i j).value z =
            initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j) ∧
          ∀ t : ℝ, 0 < t → t < T → ∀ z ∈ U, ∀ i j,
            |(Matrix.of (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
              t (fun y a b => (D a b).value y) z))⁻¹ i j -
              (Matrix.of (fun a b => initialMetricCoordinates g₀ p (Module.finBasis ℝ E)
                (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) a b))⁻¹ i j| < ε)

def literalInitialMetricCoefficientFreezingFullSignatureAssignment :
    ExpectedLiteralInitialMetricCoefficientFreezing.{u,v,w} :=
  @exists_initialMetricLocalizedHeatData_with_frozen_inverse_coefficients

-- Empty matrix rank needs no selected index, nonzero vector, or positive rank.
example {n : ℕ} (D : Fin 0 → Fin 0 → EuclideanBoundedC2Data n)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    (z₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ U : Set (Fin n → ℝ), U ∈ 𝓝 z₀ ∧
      ∀ t : ℝ, 0 < t → t < T → ∀ z ∈ U, ∀ i j : Fin 0,
        |(Matrix.of (matrixHeatSemigroupND n 0 t (fun y a b => (D a b).value y) z))⁻¹ i j -
          (Matrix.of (fun a b => (D a b).value z₀))⁻¹ i j| < ε :=
  matrixInitialHeat_inverse_coefficients_freeze D hc hcoer z₀ hε

set_option pp.universes false
set_option format.width 200
#check @abs_matrixInitialHeat_inv_sub_basepoint_inv_le
#check @matrixInitialHeat_inverse_coefficients_freeze
#check @exists_initialMetricLocalizedHeatData_with_frozen_inverse_coefficients

-- Exactly the three new semantic theorem declarations, one actual AX record each.
#print axioms RicciFlow.AnalyticPDE.abs_matrixInitialHeat_inv_sub_basepoint_inv_le
#print axioms RicciFlow.AnalyticPDE.matrixInitialHeat_inverse_coefficients_freeze
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricLocalizedHeatData_with_frozen_inverse_coefficients
