import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianJetPrincipalError

-- Source-only whole-type/rank-zero/actual-axiom probe, native qualification pending.
open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedActualGaussianJetValue :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ),
    (actualGaussianMetricJet D ht z).val = Matrix.of
      (matrixHeatSemigroupND d d t (fun y i j => (D i j).value y) z)

def actualGaussianJetValueFullSignatureAssignment : ExpectedActualGaussianJetValue :=
  @actualGaussianMetricJet_val

abbrev ExpectedActualGaussianJetFirstDerivative :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (k i j : Fin d),
    HasDerivAt (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).val i j)
      ((actualGaussianMetricJet D ht z).deriv1 k i j) (z k)

def actualGaussianJetFirstDerivativeFullSignatureAssignment :
    ExpectedActualGaussianJetFirstDerivative :=
  @actualGaussianMetricJet_hasDeriv_value

abbrev ExpectedActualGaussianJetSecondDerivative :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (k l i j : Fin d),
    HasDerivAt (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).deriv1 l i j)
      ((actualGaussianMetricJet D ht z).deriv2 k l i j) (z k)

def actualGaussianJetSecondDerivativeFullSignatureAssignment :
    ExpectedActualGaussianJetSecondDerivative :=
  @actualGaussianMetricJet_hasDeriv_first

abbrev ExpectedActualGaussianJetInverseCoefficient :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (i j : Fin d),
    GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) i j =
      (Matrix.of (matrixHeatSemigroupND d d t (fun y a b => (D a b).value y) z))⁻¹ i j

def actualGaussianJetInverseCoefficientFullSignatureAssignment :
    ExpectedActualGaussianJetInverseCoefficient :=
  @invMetric_actualGaussianMetricJet_eq

abbrev ExpectedActualGaussianJetPrincipalErrorBound :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    ∀ (z₀ : Fin d → ℝ) {ε : ℝ}, 0 < ε →
      ∃ T > 0, ∃ U : Set (Fin d → ℝ), U ∈ 𝓝 z₀ ∧
        ∀ t : ℝ, ∀ ht : 0 < t, t < T → ∀ z ∈ U, ∀ i k : Fin d,
          |GenuinePhiRD.jetPrincipalContraction
            (fun p q => GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) p q -
              (Matrix.of (fun a b => (D a b).value z₀))⁻¹ p q)
            (actualGaussianMetricJet D ht z) i k| ≤
            ε * (∑ p : Fin d, ∑ q : Fin d, |(actualGaussianMetricJet D ht z).deriv2 p q i k|)

def actualGaussianJetPrincipalErrorBoundFullSignatureAssignment :
    ExpectedActualGaussianJetPrincipalErrorBound :=
  @exists_actualGaussianJet_frozenPrincipalError_bound

abbrev ExpectedLiteralInitialMetricGaussianJetPrincipalError :=
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
          ∀ t : ℝ, ∀ ht : 0 < t, t < T → ∀ z ∈ U, ∀ i k,
            |GenuinePhiRD.jetPrincipalContraction
              (fun a b => GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) a b -
                (Matrix.of (fun j l => initialMetricCoordinates g₀ p (Module.finBasis ℝ E)
                  (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) j l))⁻¹ a b)
              (actualGaussianMetricJet D ht z) i k| ≤
              ε * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                |(actualGaussianMetricJet D ht z).deriv2 a b i k|))

def literalInitialMetricGaussianJetPrincipalErrorFullSignatureAssignment :
    ExpectedLiteralInitialMetricGaussianJetPrincipalError.{u,v,w} :=
  @exists_initialMetricActualGaussianJet_frozenPrincipalError_bound

-- Actual construction and the principal bound include empty matrix rank.
example (D : Fin 0 → Fin 0 → EuclideanBoundedC2Data 0) {t : ℝ} (ht : 0 < t)
    (z : Fin 0 → ℝ) :
    (actualGaussianMetricJet D ht z).val = Matrix.of
      (matrixHeatSemigroupND 0 0 t (fun y i j => (D i j).value y) z) :=
  actualGaussianMetricJet_val D ht z

example (D : Fin 0 → Fin 0 → EuclideanBoundedC2Data 0) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    (z₀ : Fin 0 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ U : Set (Fin 0 → ℝ), U ∈ 𝓝 z₀ ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t < T → ∀ z ∈ U, ∀ i k : Fin 0,
        |GenuinePhiRD.jetPrincipalContraction
          (fun p q => GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) p q -
            (Matrix.of (fun a b => (D a b).value z₀))⁻¹ p q)
          (actualGaussianMetricJet D ht z) i k| ≤
          ε * (∑ p : Fin 0, ∑ q : Fin 0, |(actualGaussianMetricJet D ht z).deriv2 p q i k|) :=
  exists_actualGaussianJet_frozenPrincipalError_bound D hc hcoer z₀ hε

set_option pp.universes false
set_option format.width 200
#check @actualGaussianMetricJet_val
#check @actualGaussianMetricJet_hasDeriv_value
#check @actualGaussianMetricJet_hasDeriv_first
#check @invMetric_actualGaussianMetricJet_eq
#check @exists_actualGaussianJet_frozenPrincipalError_bound
#check @exists_initialMetricActualGaussianJet_frozenPrincipalError_bound

-- Six new semantic theorem declarations, one actual AX record each.
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_val
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_hasDeriv_value
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_hasDeriv_first
#print axioms RicciFlow.AnalyticPDE.invMetric_actualGaussianMetricJet_eq
#print axioms RicciFlow.AnalyticPDE.exists_actualGaussianJet_frozenPrincipalError_bound
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricActualGaussianJet_frozenPrincipalError_bound
