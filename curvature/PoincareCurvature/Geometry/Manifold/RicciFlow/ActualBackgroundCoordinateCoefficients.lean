/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateCurvature
import PoincareCurvature.Analysis.CoordinateMatrixOperator

/-!
# Actual background connection coordinates

The same preferred frame and actual background connection produce the values,
C¹ coefficients, and actual first derivative. Regularity is an explicit
hypothesis on the actual background slice, never a coordinate oracle.
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

/-- The actual background derivative in direction i of frame vector j. -/
def actualBackgroundFrameDerivative
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) : ∀ x : M, TM x :=
  fun x => (background t) (frame (I := I) p b j) x (frame (I := I) p b i x)

/-- Scalar coefficient of the actual background derivative, with direction first. -/
def actualBackgroundFrameCoeff
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)
    (k i j : Fin d) (x : M) : ℝ :=
  (trivialization (I := I) p).localFrameCoeff I b k x
    (actualBackgroundFrameDerivative background t p b i j x)

/-- Actual background coefficients read in the fixed finite coordinate model. -/
def actualBackgroundCoordinates
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)
    (z : Fin d → ℝ) (k i j : Fin d) : ℝ :=
  scalarReadout (I := I) p (actualBackgroundFrameCoeff background t p b k i j)
    (toModel b z)

variable (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)

/-- C² local frames and the actual C¹ connection give a genuine C¹ section. -/
theorem contMDiffOn_actualBackgroundFrameDerivative
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (i j : Fin d) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (actualBackgroundFrameDerivative background t p b i j))
      (trivialization (I := I) p).baseSet := by
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI := hbackground
  have hcov : ContMDiffCovariantDerivativeOn E 1 (background t).toFun
      (trivialization (I := I) p).baseSet :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (trivialization (I := I) p).open_baseSet
  have hframe (q : Fin d) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (frame (I := I) p b q)) (trivialization (I := I) p).baseSet :=
    (trivialization (I := I) p).contMDiffOn_localFrame_baseSet (I := I) (n := 2) b q
  exact (hcov.contMDiff (hframe j)).clm_bundle_apply
    ((hframe i).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num))

/-- Actual scalar background coefficients are C¹ on the open frame patch. -/
theorem contMDiffOn_actualBackgroundFrameCoeff
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (k i j : Fin d) :
    ContMDiffOn I 𝓘(ℝ) 1 (actualBackgroundFrameCoeff background t p b k i j)
      (trivialization (I := I) p).baseSet := by
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  exact contMDiffOn_localFrameCoeff (I := I) (e := trivialization (I := I) p)
    (b := b) (trivialization (I := I) p).open_baseSet subset_rfl
    (contMDiffOn_actualBackgroundFrameDerivative background t p b hbackground i j) k

/-- C¹ chart readout of each actual scalar background coefficient. -/
theorem contDiffOn_scalarReadout_actualBackgroundFrameCoeff
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (k i j : Fin d) :
    ContDiffOn ℝ 1
      (scalarReadout (I := I) p (actualBackgroundFrameCoeff background t p b k i j))
      (extChartAt I p).target := by
  have hmap : Set.MapsTo (extChartAt I p).symm (extChartAt I p).target
      (trivialization (I := I) p).baseSet := by
    intro z hz
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using (extChartAt I p).map_target hz
  exact ((contMDiffOn_actualBackgroundFrameCoeff background t p b hbackground k i j).comp
    (contMDiffOn_extChartAt_symm (I := I) (n := 1) p) hmap).contDiffOn

/-- The background array is genuinely C¹ in the same finite coordinate model. -/
theorem contDiffOn_actualBackgroundCoordinates
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContDiffOn ℝ 1 (actualBackgroundCoordinates background t p b)
      (chosenLCCoordinateDomain (I := I) p b) := by
  rw [contDiffOn_pi]
  intro k
  rw [contDiffOn_pi]
  intro i
  rw [contDiffOn_pi]
  intro j
  exact (contDiffOn_scalarReadout_actualBackgroundFrameCoeff background t p b hbackground k i j).comp
    (toModel b).contDiff.contDiffOn (fun _ hz => hz)

/-- Actual chart values are exactly the coefficients of the background connection. -/
theorem actualBackgroundCoordinates_eq_frameCoeff
    {x : M} (hx : x ∈ (extChartAt I p).source) (k i j : Fin d) :
    actualBackgroundCoordinates background t p b (chosenLCCoordinatePoint (I := I) p b x) k i j =
      (trivialization (I := I) p).localFrameCoeff I b k x
        ((background t) (frame (I := I) p b j) x (frame (I := I) p b i x)) := by
  simp only [actualBackgroundCoordinates, chosenLCCoordinatePoint, scalarReadout,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  change actualBackgroundFrameCoeff background t p b k i j
      ((extChartAt I p).symm (extChartAt I p x)) = actualBackgroundFrameCoeff background t p b k i j x
  exact congrArg (actualBackgroundFrameCoeff background t p b k i j)
    ((extChartAt I p).left_inv hx)

/-- Genuine scalar manifold differentiation transports to the produced background jet. -/
theorem backgroundFirst_actualBackgroundCoordinates_eq_mvfderiv
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (m k i j : Fin d) :
    backgroundFirst (actualBackgroundCoordinates background t p b)
        (chosenLCCoordinatePoint (I := I) p b x) m k i j =
      mvfderiv (I := I) (actualBackgroundFrameCoeff background t p b k i j)
        x (frame (I := I) p b m x) := by
  have hz := (extChartAt I p).map_source hx
  have hreadout : DifferentiableAt ℝ
      (scalarReadout (I := I) p (actualBackgroundFrameCoeff background t p b k i j))
      (extChartAt I p x) :=
    ((contDiffOn_scalarReadout_actualBackgroundFrameCoeff background t p b hbackground k i j)
      _ hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)
      |>.differentiableAt (by norm_num)
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hcoeff : MDiffAt (actualBackgroundFrameCoeff background t p b k i j) x :=
    ((contMDiffOn_actualBackgroundFrameCoeff background t p b hbackground k i j) _ hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase)
      |>.mdifferentiableAt one_ne_zero
  change fderiv ℝ ((scalarReadout (I := I) p
    (actualBackgroundFrameCoeff background t p b k i j)) ∘ toModel b)
      ((toModel b).symm (extChartAt I p x)) (Pi.single m 1) = _
  rw [fderiv_comp_toModel_coordinateVector b hreadout]
  exact (mvfderiv_frame_eq_fderiv (I := I) p b hx hcoeff m).symm

end RicciFlow
