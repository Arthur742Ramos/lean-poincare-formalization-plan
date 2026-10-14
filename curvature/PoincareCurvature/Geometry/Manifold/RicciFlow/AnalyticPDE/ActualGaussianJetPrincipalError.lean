import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatInverseFreezing
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckPrincipalRemainder

/-!
# Actual Gaussian coordinate jets and the frozen principal-error estimate

Source candidate, uncompiled. Spatial freezing is a Source dependency until
its separate native qualification succeeds. Each jet slot below is read from
the actual bounded C2 Gaussian heat evolution. Its two coordinate derivative
witnesses are retained, rather than supplying independent derivative slots.

The coefficient-closeness hypothesis of the existing principal-error theorem
is derived from the constructed initial heat path. This is an estimate on
that path; it does not construct a nonlinear Ricci-DeTurck solution, identify
a manifold Levi-Civita jet, or identify a Banach-space Cauchy generator.
-/

noncomputable section

open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

/-- The value and both actual coordinate derivative slots of the positive-time
Gaussian evolution of the initial metric components. -/
def actualGaussianMetricJet {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) : Jet2 d d where
  val := Matrix.of (fun i j => (heatEvolvedBoundedC2Data (D i j) ht).value z)
  deriv1 := fun k => Matrix.of (fun i j => (heatEvolvedBoundedC2Data (D i j) ht).first k z)
  deriv2 := fun k l => Matrix.of
    (fun i j => (heatEvolvedBoundedC2Data (D i j) ht).second k l z)

/-- The jet value is precisely the matrix path whose inverse coefficients were
controlled by the coercivity and spatial-freezing theorems. -/
theorem actualGaussianMetricJet_val {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) :
    (actualGaussianMetricJet D ht z).val = Matrix.of
      (matrixHeatSemigroupND d d t (fun y i j => (D i j).value y) z) := by
  ext i j
  rfl

/-- The first slot is an actual coordinate derivative of the value slot. -/
theorem actualGaussianMetricJet_hasDeriv_value {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (k i j : Fin d) :
    HasDerivAt (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).val i j)
      ((actualGaussianMetricJet D ht z).deriv1 k i j) (z k) := by
  change HasDerivAt
    (fun r => (heatEvolvedBoundedC2Data (D i j) ht).value (Function.update z k r))
    ((heatEvolvedBoundedC2Data (D i j) ht).first k z) (z k)
  exact (heatEvolvedBoundedC2Data (D i j) ht).hasDeriv_value k z

/-- The second slot is an actual coordinate derivative of the first slot. -/
theorem actualGaussianMetricJet_hasDeriv_first {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (k l i j : Fin d) :
    HasDerivAt (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).deriv1 l i j)
      ((actualGaussianMetricJet D ht z).deriv2 k l i j) (z k) := by
  change HasDerivAt
    (fun r => (heatEvolvedBoundedC2Data (D i j) ht).first l (Function.update z k r))
    ((heatEvolvedBoundedC2Data (D i j) ht).second k l z) (z k)
  exact (heatEvolvedBoundedC2Data (D i j) ht).hasDeriv_first k l z

/-- The inverse coefficient appearing in the actual jet principal contraction
is the nonsingular inverse coefficient of the actual Gaussian matrix path. -/
theorem invMetric_actualGaussianMetricJet_eq {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) (i j : Fin d) :
    GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) i j =
      (Matrix.of (matrixHeatSemigroupND d d t (fun y a b => (D a b).value y) z))⁻¹ i j := by
  calc
    GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) i j =
        ((actualGaussianMetricJet D ht z).val)⁻¹ i j := by
      unfold GenuinePhiRD.invMetricOfJet
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    _ = _ := by rw [actualGaussianMetricJet_val D ht z]

/-- The existing frozen principal-error bound applies to the actual Gaussian
jet, with its coefficient-closeness premise derived rather than supplied. -/
theorem exists_actualGaussianJet_frozenPrincipalError_bound {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    (z₀ : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ U : Set (Fin d → ℝ), U ∈ 𝓝 z₀ ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t < T → ∀ z ∈ U, ∀ i k : Fin d,
        |GenuinePhiRD.jetPrincipalContraction
          (fun p q => GenuinePhiRD.invMetricOfJet (actualGaussianMetricJet D ht z) p q -
            (Matrix.of (fun a b => (D a b).value z₀))⁻¹ p q)
          (actualGaussianMetricJet D ht z) i k| ≤
          ε * (∑ p : Fin d, ∑ q : Fin d, |(actualGaussianMetricJet D ht z).deriv2 p q i k|) := by
  obtain ⟨T, hT, U, hU, hfrozen⟩ :=
    matrixInitialHeat_inverse_coefficients_freeze D hc hcoer z₀ hε
  refine ⟨T, hT, U, hU, ?_⟩
  intro t ht htT z hz i k
  refine GenuinePhiRD.abs_frozenPrincipalError_le
    (fun p q => (Matrix.of (fun a b => (D a b).value z₀))⁻¹ p q)
    (actualGaussianMetricJet D ht z) ε ?_ i k
  intro p q
  rw [invMetric_actualGaussianMetricJet_eq D ht z p q]
  exact (hfrozen t ht htT z hz p q).le

section LiteralInitialMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A literal C2 initial metric constructs actual coordinate Gaussian jets and
their frozen principal-error bound at the initial chart point. No inverse
coefficient-closeness, derivative-compatibility, or solver oracle is assumed. -/
theorem exists_initialMetricActualGaussianJet_frozenPrincipalError_bound
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (p : M) :
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
                |(actualGaussianMetricJet D ht z).deriv2 a b i k|)) := by
  obtain ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, hfreeze⟩ :=
    exists_initialMetricLocalizedHeatData_with_frozen_inverse_coefficients g₀ p
  refine ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, ?_⟩
  intro ε hε
  obtain ⟨T, hT, U, hU, hagree, hfrozen⟩ := hfreeze ε hε
  refine ⟨T, hT, U, hU, hagree, ?_⟩
  intro t ht htT z hz i k
  refine GenuinePhiRD.abs_frozenPrincipalError_le
    (fun a b => (Matrix.of (fun j l => initialMetricCoordinates g₀ p (Module.finBasis ℝ E)
      (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) j l))⁻¹ a b)
    (actualGaussianMetricJet D ht z) ε ?_ i k
  intro a b
  rw [invMetric_actualGaussianMetricJet_eq D ht z a b]
  exact (hfrozen t ht htT z hz a b).le

end LiteralInitialMetric

end RicciFlow.AnalyticPDE
