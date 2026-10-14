import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianJetSymmetry

-- Source-only whole-type/rank-zero/actual-axiom probe, native qualification pending.
open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear
open RicciFlow.AnalyticPDE

universe u v w

abbrev ExpectedGaussianHessianSwap :=
  ∀ {n : ℕ} (t : ℝ) (f : (Fin n → ℝ) → ℝ) (j k : Fin n) (z : Fin n → ℝ),
    heatHessianEntryConvolutionND t f j k z = heatHessianEntryConvolutionND t f k j z

def gaussianHessianSwapFullSignatureAssignment : ExpectedGaussianHessianSwap :=
  @heatHessianEntryConvolutionND_swap_indices

abbrev ExpectedActualGaussianJetValueSymmetry :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d),
    (∀ z i j, (D i j).value z = (D j i).value z) →
    ∀ {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i j : Fin d),
      (actualGaussianMetricJet D ht z).val i j = (actualGaussianMetricJet D ht z).val j i

def actualGaussianJetValueSymmetryFullSignatureAssignment : ExpectedActualGaussianJetValueSymmetry :=
  @actualGaussianMetricJet_val_metric_symm

abbrev ExpectedActualGaussianJetFirstSymmetry :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d),
    (∀ z i j, (D i j).value z = (D j i).value z) →
    ∀ {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k i j : Fin d),
      (actualGaussianMetricJet D ht z).deriv1 k i j =
        (actualGaussianMetricJet D ht z).deriv1 k j i

def actualGaussianJetFirstSymmetryFullSignatureAssignment : ExpectedActualGaussianJetFirstSymmetry :=
  @actualGaussianMetricJet_deriv1_metric_symm

abbrev ExpectedActualGaussianJetSecondMetricSymmetry :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d),
    (∀ z i j, (D i j).value z = (D j i).value z) →
    ∀ {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k l i j : Fin d),
      (actualGaussianMetricJet D ht z).deriv2 k l i j =
        (actualGaussianMetricJet D ht z).deriv2 k l j i

def actualGaussianJetSecondMetricSymmetryFullSignatureAssignment :
    ExpectedActualGaussianJetSecondMetricSymmetry :=
  @actualGaussianMetricJet_deriv2_metric_symm

abbrev ExpectedActualGaussianJetSecondSpatialSymmetry :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k l i j : Fin d),
      (actualGaussianMetricJet D ht z).deriv2 k l i j =
        (actualGaussianMetricJet D ht z).deriv2 l k i j

def actualGaussianJetSecondSpatialSymmetryFullSignatureAssignment :
    ExpectedActualGaussianJetSecondSpatialSymmetry :=
  @actualGaussianMetricJet_deriv2_spatial_symm

abbrev ExpectedActualGaussianJetDeterminant :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    ∀ {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ), (actualGaussianMetricJet D ht z).val.det ≠ 0

def actualGaussianJetDeterminantFullSignatureAssignment : ExpectedActualGaussianJetDeterminant :=
  @actualGaussianMetricJet_det_ne_zero

abbrev ExpectedActualGaussianJetPrincipalSplit :=
  ∀ {d : ℕ} (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ}, 0 < c →
    (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) →
    (∀ z i j, (D i j).value z = (D j i).value z) →
    ∀ (A : Fin d → Fin d → ℝ)
      (Γbg : Fin d → Fin d → Fin d → ℝ)
      (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
      {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i k : Fin d),
      GenuinePhiRD.phiRDWithBackgroundJetOfJet Γbg Γbg1 (actualGaussianMetricJet D ht z) i k =
        GenuinePhiRD.jetPrincipalContraction A (actualGaussianMetricJet D ht z) i k +
        GenuinePhiRD.frozenCoefficientRemainderOfJet A Γbg Γbg1 (actualGaussianMetricJet D ht z) i k

def actualGaussianJetPrincipalSplitFullSignatureAssignment : ExpectedActualGaussianJetPrincipalSplit :=
  @actualGaussianMetricJet_principal_split

abbrev ExpectedLiteralInitialMetricSymmetricGaussianSplit :=
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
      (∀ t : ℝ, ∀ ht : 0 < t, ∀ z,
        (∀ i j, (actualGaussianMetricJet D ht z).val i j =
          (actualGaussianMetricJet D ht z).val j i) ∧
        (∀ k i j, (actualGaussianMetricJet D ht z).deriv1 k i j =
          (actualGaussianMetricJet D ht z).deriv1 k j i) ∧
        (∀ k l i j, (actualGaussianMetricJet D ht z).deriv2 k l i j =
          (actualGaussianMetricJet D ht z).deriv2 l k i j) ∧
        (∀ k l i j, (actualGaussianMetricJet D ht z).deriv2 k l i j =
          (actualGaussianMetricJet D ht z).deriv2 k l j i) ∧
        (actualGaussianMetricJet D ht z).val.det ≠ 0 ∧
        ∀ A Γbg Γbg1 i k,
          GenuinePhiRD.phiRDWithBackgroundJetOfJet Γbg Γbg1 (actualGaussianMetricJet D ht z) i k =
            GenuinePhiRD.jetPrincipalContraction A (actualGaussianMetricJet D ht z) i k +
            GenuinePhiRD.frozenCoefficientRemainderOfJet A Γbg Γbg1 (actualGaussianMetricJet D ht z) i k)

def literalInitialMetricSymmetricGaussianSplitFullSignatureAssignment :
    ExpectedLiteralInitialMetricSymmetricGaussianSplit.{u,v,w} :=
  @exists_initialMetricActualGaussianJet_symmetricPrincipalSplit

-- The determinant producer works in matrix rank zero without a selected index.
example (D : Fin 0 → Fin 0 → EuclideanBoundedC2Data 0) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    {t : ℝ} (ht : 0 < t) (z : Fin 0 → ℝ) :
    (actualGaussianMetricJet D ht z).val.det ≠ 0 :=
  actualGaussianMetricJet_det_ne_zero D hc hcoer ht z

set_option pp.universes false
set_option format.width 200
#check @heatHessianEntryConvolutionND_swap_indices
#check @actualGaussianMetricJet_val_metric_symm
#check @actualGaussianMetricJet_deriv1_metric_symm
#check @actualGaussianMetricJet_deriv2_metric_symm
#check @actualGaussianMetricJet_deriv2_spatial_symm
#check @actualGaussianMetricJet_det_ne_zero
#check @actualGaussianMetricJet_principal_split
#check @exists_initialMetricActualGaussianJet_symmetricPrincipalSplit

-- Eight new semantic theorem declarations, one actual AX record each.
#print axioms RicciFlow.AnalyticPDE.heatHessianEntryConvolutionND_swap_indices
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_val_metric_symm
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_deriv1_metric_symm
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_deriv2_metric_symm
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_deriv2_spatial_symm
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_det_ne_zero
#print axioms RicciFlow.AnalyticPDE.actualGaussianMetricJet_principal_split
#print axioms RicciFlow.AnalyticPDE.exists_initialMetricActualGaussianJet_symmetricPrincipalSplit
