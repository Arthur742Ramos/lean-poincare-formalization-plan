/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.ActualBackgroundCoordinateCoefficients
import PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckRegularity

/-!
# Actual conventional DeTurck coordinates and their derivatives

The baseline two-input inverse-Gram contraction supplies the conventional
positive W. Its actual scalar coefficients agree on an open chart germ with
the coordinate expression. Genuine C¹ certificates are kept separate from
neighborhood equalities of total Fréchet derivative readouts.
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

/-- Actual scalar coefficient of the conventional positive DeTurck vector. -/
def standardDeTurckFrameCoeff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E) (k : Fin d) (x : M) : ℝ :=
  (trivialization (I := I) p).localFrameCoeff I b k x
    (standardDeTurckVectorField (I := I) (M := M) g background t x)

/-- The actual conventional vector's scalar readout in the same fixed chart. -/
def standardDeTurckCoordinates
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)
    (z : Fin d → ℝ) (k : Fin d) : ℝ :=
  scalarReadout (I := I) p (standardDeTurckFrameCoeff g background t p b k) (toModel b z)

variable (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)

/-- The actual conventional vector is the positive inverse-metric contraction
of the actual chosen-LC/background connection difference, in arbitrary rank. -/
theorem standardDeTurck_coordinateFrameCoeff_eq_deTurck
    {x : M} (hx : x ∈ (extChartAt I p).source) (k : Fin d) :
    (trivialization (I := I) p).localFrameCoeff I b k x
        (standardDeTurckVectorField (I := I) (M := M) g background t x) =
      deTurck (chosenLCMetricCoordinates g t p b) (actualBackgroundCoordinates background t p b)
        (chosenLCCoordinatePoint (I := I) p b x) k := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hmd (q : Fin d) : MDiffAt (T% (frame (I := I) p b q)) x :=
    (((trivialization (I := I) p).contMDiffOn_localFrame_baseSet
      (I := I) (n := 2) b q) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase)
      |>.mdifferentiableAt (by norm_num)
  rw [standardDeTurckVectorField_eq_sum_localFrame_inverseGram g background t
    (trivialization (I := I) p) b hbase]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold deTurck
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hinverse : CovariantDerivative.localFrameInverseGramMatrix (I := I)
      (trivialization (I := I) p) b x i j =
      inverse (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) i j := by
    rw [CovariantDerivative.localFrameInverseGramMatrix, inverse,
      chosenLCMetricCoordinates_eq_Gram g t p b hx]
    rfl
  rw [hinverse]
  change _ * (trivialization (I := I) p).localFrameCoeff I b k x
    ((CovariantDerivative.difference (chosenLeviCivitaFamily (I := I) (M := M) g t)
      (background t) x (frame (I := I) p b j x)) (frame (I := I) p b i x)) = _
  rw [CovariantDerivative.difference_apply_tm _ _ (hmd j)]
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [chosenLC_coordinateFrameCoeff_eq_christoffel g t p b hx,
    actualBackgroundCoordinates_eq_frameCoeff background t p b hx]

/-- Actual conventional W agrees throughout the fixed open coordinate domain. -/
theorem standardDeTurckCoordinates_eq_deTurck
    {z : Fin d → ℝ} (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k : Fin d) :
    standardDeTurckCoordinates g background t p b z k =
      deTurck (chosenLCMetricCoordinates g t p b) (actualBackgroundCoordinates background t p b) z k := by
  have hz' : toModel b z ∈ (extChartAt I p).target := hz
  have hx := (extChartAt I p).map_target hz'
  have hpoint : chosenLCCoordinatePoint (I := I) p b
      ((extChartAt I p).symm (toModel b z)) = z := by
    unfold chosenLCCoordinatePoint
    rw [(extChartAt I p).right_inv hz', ContinuousLinearEquiv.symm_apply_apply]
  simpa only [standardDeTurckCoordinates, standardDeTurckFrameCoeff,
    scalarReadout, Function.comp_apply, hpoint] using
    standardDeTurck_coordinateFrameCoeff_eq_deTurck g background t p b hx k

/-- A genuine neighborhood identification, rather than merely a pointwise value. -/
theorem standardDeTurckCoordinates_eventuallyEq_deTurck
    {z : Fin d → ℝ} (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k : Fin d) :
    (fun y => standardDeTurckCoordinates g background t p b y k) =ᶠ[nhds z]
      (fun y => deTurck (chosenLCMetricCoordinates g t p b)
        (actualBackgroundCoordinates background t p b) y k) := by
  filter_upwards [(isOpen_chosenLCCoordinateDomain (I := I) p b).mem_nhds hz] with y hy
  exact standardDeTurckCoordinates_eq_deTurck g background t p b hy k

/-- Genuine ordinary differentiability of W, from actual C²/C¹ slices. -/
theorem differentiableAt_standardDeTurckCoordinates
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {z : Fin d → ℝ} (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (k : Fin d) :
    DifferentiableAt ℝ (fun y => standardDeTurckCoordinates g background t p b y k) z := by
  exact (differentiableAt_deTurck (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b)
    (contDiffOn_actualBackgroundCoordinates background t p b hbackground) hz
    (chosenLCMetricCoordinates_det_ne_zero_on_domain g t p b hz) k).congr_of_eventuallyEq
      (standardDeTurckCoordinates_eventuallyEq_deTurck g background t p b hz k)

/-- Equality of total Fréchet derivative readouts follows from the genuine germ.
The separate theorem above supplies their differentiability interpretation. -/
theorem fderiv_standardDeTurckCoordinates_apply
    {z : Fin d → ℝ} (hz : z ∈ chosenLCCoordinateDomain (I := I) p b) (m k : Fin d) :
    fderiv ℝ (fun y => standardDeTurckCoordinates g background t p b y k) z
        (coordinateVector m) =
      deTurckFirst (chosenLCMetricCoordinates g t p b)
        (actualBackgroundCoordinates background t p b) z m k := by
  rw [(standardDeTurckCoordinates_eventuallyEq_deTurck g background t p b hz k).fderiv_eq]
  rfl

/-- Actual C¹ regularity of the scalar W coefficient on the preferred patch. -/
theorem contMDiffOn_standardDeTurckFrameCoeff
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (k : Fin d) :
    ContMDiffOn I 𝓘(ℝ) 1 (standardDeTurckFrameCoeff g background t p b k)
      (trivialization (I := I) p).baseSet := by
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  exact contMDiffOn_localFrameCoeff (I := I) (e := trivialization (I := I) p)
    (b := b) (trivialization (I := I) p).open_baseSet subset_rfl
    (standardDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
      g background t hbackground).contMDiffOn k

/-- The actual scalar W readout is C¹ on the fixed model chart target. -/
theorem contDiffOn_scalarReadout_standardDeTurckFrameCoeff
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (k : Fin d) :
    ContDiffOn ℝ 1 (scalarReadout (I := I) p (standardDeTurckFrameCoeff g background t p b k))
      (extChartAt I p).target := by
  have hmap : Set.MapsTo (extChartAt I p).symm (extChartAt I p).target
      (trivialization (I := I) p).baseSet := by
    intro z hz
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using (extChartAt I p).map_target hz
  exact ((contMDiffOn_standardDeTurckFrameCoeff g background t p b hbackground k).comp
    (contMDiffOn_extChartAt_symm (I := I) (n := 1) p) hmap).contDiffOn

/-- The genuine manifold derivative of the actual scalar W coefficient is the
coordinate derivative of the same W germ. -/
theorem standardDeTurck_coordinateFrameCoeff_mvfderiv_eq_deTurckFirst
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (m k : Fin d) :
    mvfderiv (I := I) (standardDeTurckFrameCoeff g background t p b k)
        x (frame (I := I) p b m x) =
      deTurckFirst (chosenLCMetricCoordinates g t p b)
        (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x) m k := by
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hW : MDiffAt (T% (standardDeTurckVectorField (I := I) (M := M) g background t)) x :=
    (standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
      g background t hbackground x).mdifferentiableAt one_ne_zero
  have hcoeff : MDiffAt (standardDeTurckFrameCoeff g background t p b k) x :=
    mdifferentiableAt_localFrameCoeff (I := I) (e := trivialization (I := I) p)
      (b := b) hbase hW k
  have hz := (extChartAt I p).map_source hx
  have hreadout : DifferentiableAt ℝ
      (scalarReadout (I := I) p (standardDeTurckFrameCoeff g background t p b k)) (extChartAt I p x) :=
    ((contDiffOn_scalarReadout_standardDeTurckFrameCoeff g background t p b hbackground k)
      _ hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)
      |>.differentiableAt (by norm_num)
  rw [mvfderiv_frame_eq_fderiv (I := I) p b hx hcoeff m,
    ← fderiv_comp_toModel_coordinateVector b hreadout]
  exact fderiv_standardDeTurckCoordinates_apply g background t p b
    (chosenLCCoordinatePoint_mem (I := I) b hx) m k

/-- Actual chosen-LC differentiation of W in the same coordinate frame. -/
theorem standardDeTurck_coordinateFrameCoeff_covariantDerivative_eq
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (m k : Fin d) :
    (trivialization (I := I) p).localFrameCoeff I b k x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (standardDeTurckVectorField (I := I) (M := M) g background t)
          x (frame (I := I) p b m x)) =
      deTurckFirst (chosenLCMetricCoordinates g t p b)
        (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x) m k +
      ∑ q : Fin d, deTurck (chosenLCMetricCoordinates g t p b)
          (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x) q *
        christoffel (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) k m q := by
  classical
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hW : MDiffAt (T% (standardDeTurckVectorField (I := I) (M := M) g background t)) x :=
    (standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
      g background t hbackground x).mdifferentiableAt one_ne_zero
  rw [CovariantDerivative.TangentFrame.localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
    (trivialization (I := I) p) b (chosenLeviCivitaFamily (I := I) (M := M) g t)
    hbase hW (frame (I := I) p b m x) k]
  change
    mvfderiv (I := I) (standardDeTurckFrameCoeff g background t p b k)
        x (frame (I := I) p b m x) +
      (∑ q : Fin d, standardDeTurckFrameCoeff g background t p b q x *
        (trivialization (I := I) p).localFrameCoeff I b k x
          ((chosenLeviCivitaFamily (I := I) (M := M) g t)
            (frame (I := I) p b q) x (frame (I := I) p b m x))) = _
  rw [standardDeTurck_coordinateFrameCoeff_mvfderiv_eq_deTurckFirst
    g background t p b hbackground hx]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [standardDeTurckFrameCoeff,
    standardDeTurck_coordinateFrameCoeff_eq_deTurck g background t p b hx,
    chosenLC_coordinateFrameCoeff_eq_christoffel g t p b hx]

end RicciFlow
