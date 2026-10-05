/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.PreferredCoordinateFrame
import PoincareCurvature.Analysis.TimeDependentGram
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.PositiveFrozenC2Localization

/-!
# Literal C² metric localization under manifold boundarylessness

An actual C² Riemannian metric is read in the actual preferred tangent frame
and inverse chart. Manifold boundarylessness supplies the open model domain.
The metric Gram positivity and C² regularity are proved internally, then the
cutoff and bounded heat data are constructed with a positive frozen exterior.
No globally boundaryless model, higher metric regularity or positive-rank
assumption is used. This supporting endpoint does not construct Ricci flow.
-/

noncomputable section

open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow.AnalyticPDE

open PoincareCurvature.PreferredCoordinateFrame
open PoincareCurvature.FiniteCoordinateBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [completeE : CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [hausdorffM : T2Space M]
    [manifoldM : IsManifold I ∞ M] [boundarylessM : BoundarylessManifold I M]
    [smoothTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [sigmaM : SigmaCompactSpace M] {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual preferred-chart target after the finite basis change. -/
def initialMetricCoordinateDomain (p : M) (b : Module.Basis (Fin d) ℝ E) :
    Set (Fin d → ℝ) := (toModel b) ⁻¹' (extChartAt I p).target

/-- Finite coordinates of the selected initial point in its own chart. -/
def initialMetricCoordinatePoint (p : M) (b : Module.Basis (Fin d) ℝ E) : Fin d → ℝ :=
  (toModel b).symm (extChartAt I p p)

/-- Genuine scalar Gram coefficients in the actual preferred tangent frame. -/
def initialMetricComponent (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i k : Fin d) (x : M) : ℝ :=
  g₀.inner x (frame (I := I) p b i x) (frame (I := I) p b k x)

/-- Literal initial metric coordinates, not a supplied matrix certificate. -/
def initialMetricCoordinates (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (z : Fin d → ℝ) (i k : Fin d) : ℝ :=
  scalarReadout (I := I) p (initialMetricComponent g₀ p b i k) (toModel b z)

theorem isOpen_initialMetricCoordinateDomain (p : M) (b : Module.Basis (Fin d) ℝ E) :
    IsOpen (initialMetricCoordinateDomain (I := I) p b) :=
  (PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target (I := I) p).preimage
    (toModel b).continuous

theorem initialMetricCoordinatePoint_mem (p : M) (b : Module.Basis (Fin d) ℝ E) :
    initialMetricCoordinatePoint (I := I) p b ∈ initialMetricCoordinateDomain (I := I) p b := by
  simpa only [initialMetricCoordinateDomain, initialMetricCoordinatePoint,
    Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using
    (extChartAt I p).map_source (mem_extChartAt_source p)

theorem contMDiffOn_initialMetricComponent
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i k : Fin d) :
    ContMDiffOn I 𝓘(ℝ) 2 (initialMetricComponent g₀ p b i k)
      (trivialization (I := I) p).baseSet := by
  letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  exact CovariantDerivative.contMDiffOn_inner_localFrame_localFrame
    (I := I) (E := E) (trivialization (I := I) p) b
    (trivialization (I := I) p).open_baseSet subset_rfl i k

theorem contDiffOn_initialMetricCoordinates
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) :
    ContDiffOn ℝ 2 (initialMetricCoordinates g₀ p b)
      (initialMetricCoordinateDomain (I := I) p b) := by
  rw [contDiffOn_pi]
  intro i
  rw [contDiffOn_pi]
  intro k
  have hmap : Set.MapsTo (extChartAt I p).symm (extChartAt I p).target
      (trivialization (I := I) p).baseSet := by
    intro z hz
    have hx := (extChartAt I p).map_target hz
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  have hscalar : ContDiffOn ℝ 2
      (scalarReadout (I := I) p (initialMetricComponent g₀ p b i k))
      (extChartAt I p).target :=
    ((contMDiffOn_initialMetricComponent g₀ p b i k).comp
      (contMDiffOn_extChartAt_symm (I := I) (n := 2) p) hmap).contDiffOn
  exact hscalar.comp (toModel b).contDiff.contDiffOn (fun _ hz => hz)

theorem initialMetricCoordinates_at_point
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i k : Fin d) :
    initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k =
      g₀.inner p (frame (I := I) p b i p) (frame (I := I) p b k p) := by
  simp only [initialMetricCoordinates, initialMetricCoordinatePoint, scalarReadout,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
  rfl

theorem initialMetricCoordinates_pos_at_point
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < ofMatrix (initialMetricCoordinates g₀ p b
      (initialMetricCoordinatePoint (I := I) p b)) v v := by
  have hp : p ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (mem_extChartAt_source (I := I) p)
  have h := PoincareCurvature.ParametrizedInner.timeDependentGram_pos
    g₀ (trivialization (I := I) p) b hp hv
  rw [ofMatrix_apply]
  simp only [initialMetricCoordinates_at_point]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every literal C² metric yields genuine bounded C² Euclidean heat data in
the actual preferred coordinates, equal to the metric near the point and
uniformly positive even outside the chart. All cutoff and derivative data are
constructed; initial Hessian Hölder regularity is unnecessary. -/
theorem exists_initialMetricLocalizedHeatData_in_basis
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) :
    ∃ χ : (Fin d → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ initialMetricCoordinateDomain (I := I) p b ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data d,
        (∀ i k z, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k +
            χ z * (initialMetricCoordinates g₀ p b z i k -
              initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k)) ∧
        (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p b),
          ∀ i k, (D i k).value z = initialMetricCoordinates g₀ p b z i k) ∧
        (∀ z ∉ tsupport χ, ∀ i k, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k) ∧
        (∀ z i k, (D i k).value z = (D k i).value z) ∧
        (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i k => (D i k).value z) v v) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin d → ℝ) → ℝ)) := by
  apply exists_positiveFrozenC2MatrixHeatData
    (isOpen_initialMetricCoordinateDomain p b) (initialMetricCoordinatePoint_mem p b)
    (contDiffOn_initialMetricCoordinates g₀ p b)
    (initialMetricCoordinates_pos_at_point g₀ p b)
  intro z hz i k
  exact g₀.symm _ _ _

include completeE hausdorffM manifoldM boundarylessM smoothTangent sigmaM in
/-- Literal all-C² local metric endpoint: the finite basis is selected internally.
The precise current local geometric classes are kept in the public signature;
compactness is not needed for the localization itself. -/
theorem exists_initialMetricLocalizedHeatData
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) :
    let d := Module.finrank ℝ E
    let b := Module.finBasis ℝ E
    ∃ χ : (Fin d → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ initialMetricCoordinateDomain (I := I) p b ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data d,
        (∀ i k z, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k +
            χ z * (initialMetricCoordinates g₀ p b z i k -
              initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k)) ∧
        (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p b),
          ∀ i k, (D i k).value z = initialMetricCoordinates g₀ p b z i k) ∧
        (∀ z ∉ tsupport χ, ∀ i k, (D i k).value z =
          initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) i k) ∧
        (∀ z i k, (D i k).value z = (D k i).value z) ∧
        (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i k => (D i k).value z) v v) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin d → ℝ) → ℝ)) := by
  exact exists_initialMetricLocalizedHeatData_in_basis g₀ p (Module.finBasis ℝ E)

end RicciFlow.AnalyticPDE
