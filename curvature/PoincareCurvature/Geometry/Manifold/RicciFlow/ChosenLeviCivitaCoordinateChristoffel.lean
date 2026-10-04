/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.PreferredCoordinateFrame
import PoincareCurvature.Analysis.CoordinateMatrixConnection
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivitaKoszulAt
import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck

/-!
# Actual chosen Levi--Civita Christoffel coefficients in one fixed chart

Metric matrix data are produced from the actual C² metric and the preferred
coordinate frame. Symmetry and invertibility follow from the metric, while
actual ordinary derivatives follow from the open chart patch. Localized
Koszul and proved frame commutation produce the actual connection coefficients.
No Christoffel identification or derivative formula is assumed.
-/

noncomputable section

open Bundle FiberBundle Matrix
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow

open PoincareCurvature.PreferredCoordinateFrame
open PoincareCurvature.CoordinateMatrixJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [I.Boundaryless]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M] {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)

/-- The open coordinate patch after the actual finite-basis change of model. -/
def chosenLCCoordinateDomain (p : M) (b : Module.Basis (Fin d) ℝ E) : Set (Fin d → ℝ) :=
  (toModel b) ⁻¹' (extChartAt I p).target

/-- Actual scalar metric components in the fixed preferred tangent frame. -/
def chosenLCMetricComponent (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) (x : M) : ℝ :=
  (g t).inner x (frame (I := I) p b i x) (frame (I := I) p b j x)

/-- The actual metric-coordinate matrix field used by the finite-jet calculus. -/
def chosenLCMetricCoordinates (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (z : Fin d → ℝ) (i j : Fin d) : ℝ :=
  scalarReadout (I := I) p (chosenLCMetricComponent g t p b i j) (toModel b z)

/-- Actual finite coordinates of a point in the one fixed chart. -/
def chosenLCCoordinatePoint (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M) : Fin d → ℝ :=
  (toModel b).symm (extChartAt I p x)

theorem isOpen_chosenLCCoordinateDomain (p : M) (b : Module.Basis (Fin d) ℝ E) :
    IsOpen (chosenLCCoordinateDomain (I := I) p b) :=
  (isOpen_extChartAt_target p).preimage (toModel b).continuous

theorem chosenLCCoordinatePoint_mem {p x : M} (b : Module.Basis (Fin d) ℝ E)
    (hx : x ∈ (extChartAt I p).source) :
    chosenLCCoordinatePoint (I := I) p b x ∈ chosenLCCoordinateDomain (I := I) p b := by
  simpa only [chosenLCCoordinateDomain, chosenLCCoordinatePoint,
    Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using
    (extChartAt I p).map_source hx

theorem chosenLCMetricCoordinates_symm
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (z : Fin d → ℝ) (i j : Fin d) :
    chosenLCMetricCoordinates g t p b z i j = chosenLCMetricCoordinates g t p b z j i := by
  exact (g t).symm _ _ _

/-- Metric C² regularity produces actual C² scalar components on the frame patch. -/
theorem contMDiffOn_chosenLCMetricComponent
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) :
    ContMDiffOn I 𝓘(ℝ) 2 (chosenLCMetricComponent g t p b i j)
      (trivialization (I := I) p).baseSet := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  exact CovariantDerivative.contMDiffOn_inner_localFrame_localFrame
    (I := I) (E := E) (trivialization (I := I) p) b
    (trivialization (I := I) p).open_baseSet subset_rfl i j

/-- Scalar readouts are genuinely C² throughout the fixed open chart target. -/
theorem contDiffOn_scalarReadout_chosenLCMetricComponent
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) :
    ContDiffOn ℝ 2 (scalarReadout (I := I) p (chosenLCMetricComponent g t p b i j))
      (extChartAt I p).target := by
  have hmap : Set.MapsTo (extChartAt I p).symm (extChartAt I p).target
      (trivialization (I := I) p).baseSet := by
    intro z hz
    have hx := (extChartAt I p).map_target hz
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  exact ((contMDiffOn_chosenLCMetricComponent g t p b i j).comp
    (contMDiffOn_extChartAt_symm (I := I) (n := 2) p) hmap).contDiffOn

/-- The actual coordinate matrix field is C² on its actual open domain. -/
theorem contDiffOn_chosenLCMetricCoordinates
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) :
    ContDiffOn ℝ 2 (chosenLCMetricCoordinates g t p b)
      (chosenLCCoordinateDomain (I := I) p b) := by
  rw [contDiffOn_pi]
  intro i
  rw [contDiffOn_pi]
  intro j
  exact (contDiffOn_scalarReadout_chosenLCMetricComponent g t p b i j).comp
    (toModel b).contDiff.contDiffOn (fun _ hz => hz)

/-- Coordinate metric values are precisely the positive Gram matrix of the actual frame. -/
theorem chosenLCMetricCoordinates_eq_Gram
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M} (hx : x ∈ (extChartAt I p).source) :
    chosenLCMetricCoordinates g t p b (chosenLCCoordinatePoint (I := I) p b x) =
      (fun i j => (g t).inner x (frame (I := I) p b i x) (frame (I := I) p b j x)) := by
  funext i j
  simp only [chosenLCMetricCoordinates, chosenLCCoordinatePoint, scalarReadout,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  change chosenLCMetricComponent g t p b i j ((extChartAt I p).symm (extChartAt I p x)) =
    chosenLCMetricComponent g t p b i j x
  exact congrArg (chosenLCMetricComponent g t p b i j) ((extChartAt I p).left_inv hx)

/-- Point invertibility is produced from positive definiteness, not assumed. -/
theorem chosenLCMetricCoordinates_det_ne_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M} (hx : x ∈ (extChartAt I p).source) :
    (show Matrix (Fin d) (Fin d) ℝ from chosenLCMetricCoordinates g t p b
      (chosenLCCoordinatePoint (I := I) p b x)).det ≠ 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  rw [chosenLCMetricCoordinates_eq_Gram g t p b hx]
  apply CovariantDerivative.localFrameGramMatrix_det_ne_zero
    (I := I) (E := E) (trivialization (I := I) p) b
  simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
    extChartAt_source] using hx

/-- Actual first metric derivatives agree with manifold differentiation along
this same fixed coordinate frame. -/
theorem first_chosenLCMetricCoordinates_eq_mvfderiv
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M} (hx : x ∈ (extChartAt I p).source)
    (m i j : Fin d) :
    first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) m i j =
      mvfderiv (I := I) (chosenLCMetricComponent g t p b i j) x (frame (I := I) p b m x) := by
  have hz := (extChartAt I p).map_source hx
  have hreadout : DifferentiableAt ℝ
      (scalarReadout (I := I) p (chosenLCMetricComponent g t p b i j)) (extChartAt I p x) :=
    ((contDiffOn_scalarReadout_chosenLCMetricComponent g t p b i j) _ hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz) |>.differentiableAt (by norm_num)
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  have hcomp : MDiffAt (chosenLCMetricComponent g t p b i j) x :=
    ((contMDiffOn_chosenLCMetricComponent g t p b i j) _ hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase) |>.mdifferentiableAt (by norm_num)
  change fderiv ℝ ((scalarReadout (I := I) p (chosenLCMetricComponent g t p b i j)) ∘
    toModel b) ((toModel b).symm (extChartAt I p x)) (Pi.single m 1) = _
  rw [fderiv_comp_toModel_coordinateVector b hreadout]
  exact (mvfderiv_frame_eq_fderiv (I := I) p b hx hcomp m).symm

/-- Actual localized Koszul pairings in a proved commuting fixed chart frame. -/
theorem chosenLC_inner_coordinateFrame_eq_first_metric
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M} (hx : x ∈ (extChartAt I p).source)
    (i j l : Fin d) :
    2 * (g t).inner x
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (frame (I := I) p b j) x (frame (I := I) p b i x)) (frame (I := I) p b l x) =
      first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) i j l +
        first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) j i l -
        first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) l i j := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞))
      (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hmd (k : Fin d) : MDiffAt (T% (frame (I := I) p b k)) x :=
    (((trivialization (I := I) p).contMDiffOn_localFrame_baseSet
      (I := I) (n := 2) b k) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase) |>.mdifferentiableAt (by norm_num)
  have hLevi := chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g t
  have h := CovariantDerivative.koszul_formula_at
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t) hLevi (hmd i) (hmd j) (hmd l)
  simp only [mlieBracket_frame_eq_zero (I := I) p b hx, inner_zero_right,
    inner_zero_left, sub_zero, add_zero, CovariantDerivative.along] at h
  simp only [first_chosenLCMetricCoordinates_eq_mvfderiv g t p b hx,
    chosenLCMetricComponent]
  exact h

/-- The chosen LC frame coefficients are the actual metric-coordinate Christoffel
formula. All derivative, commutation and metric-matrix data are produced above. -/
theorem chosenLC_coordinateFrameCoeff_eq_christoffel
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M} (hx : x ∈ (extChartAt I p).source)
    (k i j : Fin d) :
    (trivialization (I := I) p).localFrameCoeff I b k x
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (frame (I := I) p b j) x (frame (I := I) p b i x)) =
      christoffel (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) k i j := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  let v : ∀ y : M, TM y := fun y =>
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
      (frame (I := I) p b j) y (frame (I := I) p b i y)
  let omega : ∀ y : M, TM y →L[ℝ] ℝ := fun y => InnerProductSpace.toDual ℝ (TM y) (v y)
  have hriesz : CovariantDerivative.rieszMap (I := I) x (omega x) = v x :=
    (InnerProductSpace.toDual ℝ (TM x)).symm_apply_apply (v x)
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  change (trivialization (I := I) p).localFrameCoeff I b k x (v x) = _
  rw [← hriesz, CovariantDerivative.localFrameCoeff_rieszMap
    (I := I) (E := E) (trivialization (I := I) p) b hbase k]
  unfold christoffel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hpair := chosenLC_inner_coordinateFrame_eq_first_metric g t p b hx i j l
  have hhalf : omega x (frame (I := I) p b l x) = (1/2 : ℝ) *
      (first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) i j l +
        first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) j i l -
        first (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) l i j) := by
    change (g t).inner x (v x) (frame (I := I) p b l x) = _
    change 2 * (g t).inner x (v x) (frame (I := I) p b l x) = _ at hpair
    linarith
  rw [hhalf]
  have hinverse :
      ((show Matrix (Fin d) (Fin d) ℝ from CovariantDerivative.localFrameGramMatrix
        (I := I) (trivialization (I := I) p) b x)⁻¹) k l =
      inverse (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) k l := by
    rw [inverse, chosenLCMetricCoordinates_eq_Gram g t p b hx]
    rfl
  rw [hinverse]
  ring

/-- Actual chosen-connection coefficients, pulled back through this one fixed chart. -/
def chosenLCConnectionCoordinates
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (z : Fin d → ℝ) (k i j : Fin d) : ℝ :=
  let x : M := (extChartAt I p).symm (toModel b z)
  (trivialization (I := I) p).localFrameCoeff I b k x
    (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
      (frame (I := I) p b j) x (frame (I := I) p b i x))

/-- The identification holds throughout the fixed coordinate domain. -/
theorem chosenLCConnectionCoordinates_eq_christoffel
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {z : Fin d → ℝ}
    (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k i j : Fin d) :
    chosenLCConnectionCoordinates g t p b z k i j =
      christoffel (chosenLCMetricCoordinates g t p b) z k i j := by
  have hz' : toModel b z ∈ (extChartAt I p).target := hz
  have hx := (extChartAt I p).map_target hz'
  have hpoint : chosenLCCoordinatePoint (I := I) p b
      ((extChartAt I p).symm (toModel b z)) = z := by
    unfold chosenLCCoordinatePoint
    rw [(extChartAt I p).right_inv hz', ContinuousLinearEquiv.symm_apply_apply]
  simpa only [chosenLCConnectionCoordinates, hpoint] using
    chosenLC_coordinateFrameCoeff_eq_christoffel g t p b hx k i j

/-- The actual metric matrix is invertible everywhere in the fixed coordinate domain. -/
theorem chosenLCMetricCoordinates_det_ne_zero_on_domain
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {z : Fin d → ℝ}
    (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) :
    (show Matrix (Fin d) (Fin d) ℝ from chosenLCMetricCoordinates g t p b z).det ≠ 0 := by
  have hz' : toModel b z ∈ (extChartAt I p).target := hz
  have hx := (extChartAt I p).map_target hz'
  have hpoint : chosenLCCoordinatePoint (I := I) p b
      ((extChartAt I p).symm (toModel b z)) = z := by
    unfold chosenLCCoordinatePoint
    rw [(extChartAt I p).right_inv hz', ContinuousLinearEquiv.symm_apply_apply]
  simpa only [hpoint] using chosenLCMetricCoordinates_det_ne_zero g t p b hx

/-- A genuine fixed-chart germ, suitable for differentiating the identification. -/
theorem chosenLCConnectionCoordinates_eventuallyEq_christoffel
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {z : Fin d → ℝ}
    (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k i j : Fin d) :
    (fun y => chosenLCConnectionCoordinates g t p b y k i j) =ᶠ[nhds z]
      (fun y => christoffel (chosenLCMetricCoordinates g t p b) y k i j) := by
  filter_upwards [(isOpen_chosenLCCoordinateDomain (I := I) p b).mem_nhds hz] with y hy
  exact chosenLCConnectionCoordinates_eq_christoffel g t p b hy k i j

/-- Actual differentiability of the chosen-connection component readout follows
from the produced C² metric and the proved fixed-chart identification. -/
theorem differentiableAt_chosenLCConnectionCoordinates
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {z : Fin d → ℝ}
    (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k i j : Fin d) :
    DifferentiableAt ℝ (fun y => chosenLCConnectionCoordinates g t p b y k i j) z := by
  exact (differentiableAt_christoffel (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b) hz
    (chosenLCMetricCoordinates_det_ne_zero_on_domain g t p b hz) k i j).congr_of_eventuallyEq
      (chosenLCConnectionCoordinates_eventuallyEq_christoffel g t p b hz k i j)

/-- Actual spatial differentiation of the chosen LC coefficients yields the
existing Christoffel first-jet expression, without a derivative oracle. -/
theorem fderiv_chosenLCConnectionCoordinates_apply
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {z : Fin d → ℝ}
    (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (m k i j : Fin d) :
    fderiv ℝ (fun y => chosenLCConnectionCoordinates g t p b y k i j) z
      (coordinateVector m) = christoffelFirst (chosenLCMetricCoordinates g t p b) z m k i j := by
  rw [(chosenLCConnectionCoordinates_eventuallyEq_christoffel g t p b hz k i j).fderiv_eq]
  exact fderiv_christoffel_apply (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b) hz
    (chosenLCMetricCoordinates_det_ne_zero_on_domain g t p b hz) m k i j

end RicciFlow
