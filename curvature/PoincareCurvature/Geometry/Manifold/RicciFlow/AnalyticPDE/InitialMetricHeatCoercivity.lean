import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MatrixHeatCoercivity
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.BoundarylessInitialMetricLocalization
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatWeightedInitialHolder

/-!
# Genuine Gaussian matrix heat preserves the initial coercivity reserve

SOURCE CANDIDATE, UNCOMPILED. The heat path uses the actual scalar Gaussian
integral in every matrix entry. A uniform lower bound for its quadratic form
survives at every positive time. The geometric corollary constructs that lower
bound from the literal initial C2 metric, using the existing localization.

This is a positive local initial heat path and weighted initial-face estimate.
No nonlinear interval equation, manifold gluing, uniqueness or Point 4 closure
is asserted.
-/

noncomputable section

open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

section LiteralInitialMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A literal initial C2 metric produces actual local Gaussian heat data
whose positive coercivity reserve survives for every positive time. The
basis, localization and reserve are constructed, not supplied hypotheses. -/
theorem exists_initialMetricLocalizedHeatData_with_coercive_heat
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (p : M) :
    ∃ c > 0, ∃ D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        EuclideanBoundedC2Data (Module.finrank ℝ E),
      (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)),
        ∀ i j, (D i j).value z = initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j) ∧
      (∀ z i j, (D i j).value z = (D j i).value z) ∧
      (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) ∧
      (∀ t : ℝ, 0 < t → ∀ z v, c * ‖v‖ ^ 2 ≤
        ofMatrix (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y i j => (D i j).value y) z) v v) ∧
      (∀ i j a b, UniformContinuous ((D i j).second a b :
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ)) := by
  classical
  obtain ⟨χ, c, hc, hχ, hχcompact, hχdomain, D, hformula, hnear,
      hexterior, hsymm, hcoercive, hsecond⟩ :=
    exists_initialMetricLocalizedHeatData_in_basis (I := I) (M := M)
      g₀ p (Module.finBasis ℝ E)
  refine ⟨c, hc, D, hnear, hsymm, hcoercive, ?_, hsecond⟩
  intro t ht z v
  exact matrixHeatSemigroupND_preserves_coercivity
    (fun i j => (D i j).value) c hcoercive ht z v

end LiteralInitialMetric

/-- The same actual localized data retain the existing weighted initial
Hessian estimate. No positive-exponent regularity is assumed at time zero. -/
theorem localizedC2Data_weighted_heat_hessian_trace {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n)
    (hsecond : ∀ i j a b, UniformContinuous ((D i j).second a b :
      (Fin n → ℝ) → ℝ)) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (i j : Fin d) :
    Tendsto (fun t : ℝ => t ^ (α / 2) *
      (if ht : 0 < t then
        (heatEvolvedWeightedC2AlphaData (D i j) ht hα.le hα1).hessianHolderConstant
      else 0)) (𝓝[>] 0) (𝓝 0) :=
  (D i j).tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero
    (hsecond i j) hα hα1

end RicciFlow.AnalyticPDE
