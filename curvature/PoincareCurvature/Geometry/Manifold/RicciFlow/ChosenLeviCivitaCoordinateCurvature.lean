/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateChristoffel
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TangentFrameCoordinate
import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity
import PoincareCurvature.Analysis.CoordinateMatrixCurvature

/-!
# Actual chosen Levi--Civita curvature and intrinsic Ricci coordinates

C² local frame fields and the constructed C¹ chosen connection supply the
regularity of the actual covariant-derivative section. Scalar chart transport
then differentiates its coefficients. The existing local-to-tensor curvature
theorem identifies the raw commutator with actual bundled curvature.

The ordinary basis trace first gives Ricci(F_j,F_i). Lower Christoffel-slot
symmetry is differentiated on an open neighborhood before tracing; the final
index order is obtained separately from intrinsic Levi--Civita Ricci symmetry.
No geometric identification, derivative identity, or global frame smoothness
is supplied as an additional premise. This is a fixed-time spatial result.
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

/-- The actual section ∇_(F_i) F_j in the fixed preferred chart. -/
def chosenLCCoordinateFrameDerivative
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) : ∀ x : M, TM x :=
  fun x => (chosenLeviCivitaFamily (I := I) (M := M) g t)
    (frame (I := I) p b j) x (frame (I := I) p b i x)

/-- Actual local C¹ regularity of ∇_(F_i) F_j follows from the C² frame
and the chosen slice's constructed C¹ connection, without fiber-norm premises. -/
theorem contMDiffOn_chosenLCCoordinateFrameDerivative
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (chosenLCCoordinateFrameDerivative g t p b i j))
      (trivialization (I := I) p).baseSet := by
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  have hcov : ContMDiffCovariantDerivativeOn E 1
      (chosenLeviCivitaFamily (I := I) (M := M) g t).toFun
      (trivialization (I := I) p).baseSet :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (trivialization (I := I) p).open_baseSet
  have hframe (q : Fin d) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (frame (I := I) p b q)) (trivialization (I := I) p).baseSet :=
    (trivialization (I := I) p).contMDiffOn_localFrame_baseSet (I := I) (n := 2) b q
  exact (hcov.contMDiff (hframe j)).clm_bundle_apply
    ((hframe i).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num))

/-- Scalar coefficients of that actual section are C¹ on the open frame patch. -/
theorem contMDiffOn_chosenLCCoordinateFrameDerivativeCoeff
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (k i j : Fin d) :
    ContMDiffOn I 𝓘(ℝ) 1
      (fun y => (trivialization (I := I) p).localFrameCoeff I b k y
        (chosenLCCoordinateFrameDerivative g t p b i j y))
      (trivialization (I := I) p).baseSet := by
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  exact contMDiffOn_localFrameCoeff (I := I) (e := trivialization (I := I) p)
    (b := b) (trivialization (I := I) p).open_baseSet subset_rfl
    (contMDiffOn_chosenLCCoordinateFrameDerivative g t p b i j) k

/-- The actual scalar coefficient readout is C¹ on the actual chart target. -/
theorem contDiffOn_scalarReadout_chosenLCCoordinateFrameDerivativeCoeff
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) (k i j : Fin d) :
    ContDiffOn ℝ 1
      (scalarReadout (I := I) p (fun y =>
        (trivialization (I := I) p).localFrameCoeff I b k y
          (chosenLCCoordinateFrameDerivative g t p b i j y)))
      (extChartAt I p).target := by
  have hmap : Set.MapsTo (extChartAt I p).symm (extChartAt I p).target
      (trivialization (I := I) p).baseSet := by
    intro z hz
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using (extChartAt I p).map_target hz
  exact ((contMDiffOn_chosenLCCoordinateFrameDerivativeCoeff g t p b k i j).comp
    (contMDiffOn_extChartAt_symm (I := I) (n := 1) p) hmap).contDiffOn

/-- Transport of the genuine scalar manifold derivative along the actual frame
produces the actual Christoffel differential, with its direction m explicit. -/
theorem chosenLC_coordinateFrameCoeff_mvfderiv_eq_christoffelFirst
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (m k i j : Fin d) :
    mvfderiv (I := I)
      (fun y => (trivialization (I := I) p).localFrameCoeff I b k y
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (frame (I := I) p b j) y (frame (I := I) p b i y)))
      x (frame (I := I) p b m x) =
      christoffelFirst (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) m k i j := by
  let C : M → ℝ := fun y => (trivialization (I := I) p).localFrameCoeff I b k y
    (chosenLCCoordinateFrameDerivative g t p b i j y)
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  have hC : MDiffAt C x :=
    ((contMDiffOn_chosenLCCoordinateFrameDerivativeCoeff g t p b k i j) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase) |>.mdifferentiableAt one_ne_zero
  have hz := (extChartAt I p).map_source hx
  have hreadout : DifferentiableAt ℝ (scalarReadout (I := I) p C) (extChartAt I p x) :=
    ((contDiffOn_scalarReadout_chosenLCCoordinateFrameDerivativeCoeff g t p b k i j)
      _ hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz) |>.differentiableAt (by norm_num)
  change mvfderiv (I := I) C x (frame (I := I) p b m x) = _
  rw [mvfderiv_frame_eq_fderiv (I := I) p b hx hC m,
    ← fderiv_comp_toModel_coordinateVector b hreadout]
  exact fderiv_chosenLCConnectionCoordinates_apply g t p b
    (chosenLCCoordinatePoint_mem (I := I) b hx) m k i j

/-- Actual bundled curvature coefficients in the fixed preferred frame.
The chosen C¹ connection instance is constructed, rather than assumed. -/
theorem chosenLC_coordinateFrameCoeff_curvatureTensor_eq
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (k a b' c : Fin d) :
    letI : CovariantDerivative.ContMDiffCovariantDerivative
        (chosenLeviCivitaFamily (I := I) (M := M) g t) 1 :=
      g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
    (trivialization (I := I) p).localFrameCoeff I b k x
      (CovariantDerivative.curvatureTensor
        (cov := chosenLeviCivitaFamily (I := I) (M := M) g t) x
        (frame (I := I) p b a x) (frame (I := I) p b b' x)
        (frame (I := I) p b c x)) =
      christoffelFirst (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) a k b' c -
      christoffelFirst (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) b' k a c +
      ∑ q : Fin d,
        (christoffel (chosenLCMetricCoordinates g t p b)
            (chosenLCCoordinatePoint (I := I) p b x) k a q *
          christoffel (chosenLCMetricCoordinates g t p b)
            (chosenLCCoordinatePoint (I := I) p b x) q b' c -
        christoffel (chosenLCMetricCoordinates g t p b)
            (chosenLCCoordinatePoint (I := I) p b x) k b' q *
          christoffel (chosenLCMetricCoordinates g t p b)
            (chosenLCCoordinatePoint (I := I) p b x) q a c) := by
  classical
  letI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  let cov := chosenLeviCivitaFamily (I := I) (M := M) g t
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  have hframe (q : Fin d) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (frame (I := I) p b q)) (trivialization (I := I) p).baseSet :=
    (trivialization (I := I) p).contMDiffOn_localFrame_baseSet (I := I) (n := 2) b q
  have hactual := curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    (cov := cov) (trivialization (I := I) p).open_baseSet hbase
    (hframe a) (hframe b') (hframe c)
  have hmd (i j : Fin d) : MDiffAt (T% (chosenLCCoordinateFrameDerivative g t p b i j)) x :=
    ((contMDiffOn_chosenLCCoordinateFrameDerivative g t p b i j) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase) |>.mdifferentiableAt one_ne_zero
  have hcoeff (m i j : Fin d) :=
    CovariantDerivative.TangentFrame.localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
      (trivialization (I := I) p) b cov hbase (hmd i j)
      (frame (I := I) p b m x) k
  simp only [chosenLCCoordinateFrameDerivative, cov,
    chosenLC_coordinateFrameCoeff_mvfderiv_eq_christoffelFirst g t p b hx,
    chosenLC_coordinateFrameCoeff_eq_christoffel g t p b hx] at hcoeff
  rw [← hactual]
  simp only [CovariantDerivative.curvatureAux_apply, CovariantDerivative.along,
    mlieBracket_frame_eq_zero (I := I) p b hx, map_zero, sub_zero, map_sub]
  rw [hcoeff a b' c, hcoeff b' a c, Finset.sum_sub_distrib]
  simp only [mul_comm]
  ring

/-- The ordinary frame trace gives the transpose Ricci order before using
intrinsic Ricci symmetry. There is no inverse-Gram weight in this trace. -/
theorem coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor_transpose
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    coordinateRicci (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) i j =
      intrinsicRicciTensor (I := I) (M := M) g t x
        (frame (I := I) p b j x) (frame (I := I) p b i x) := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  rw [coordinateRicci_eq_christoffel_curvature_trace
    (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b)
    (chosenLCCoordinatePoint_mem (I := I) b hx)
    (chosenLCMetricCoordinates_det_ne_zero g t p b hx)
    (fun z _ => chosenLCMetricCoordinates_symm g t p b z) i j]
  change _ = CovariantDerivative.ricciCurvature
    (cov := chosenLeviCivitaFamily (I := I) (M := M) g t) x
    (frame (I := I) p b j x) (frame (I := I) p b i x)
  rw [ricciCurvature_eq_sum_localFrameCoeff b p hbase]
  apply Finset.sum_congr rfl
  intro k _
  exact (chosenLC_coordinateFrameCoeff_curvatureTensor_eq g t p b hx k k j i).symm

/-- The intended-index coordinate Ricci identity, using actual chosen-LC
Ricci symmetry separately from lower connection-slot symmetry. -/
theorem coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    coordinateRicci (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) i j =
      intrinsicRicciTensor (I := I) (M := M) g t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    have hsmooth : minSmoothness ℝ 3 ≤ (∞ : WithTop ℕ∞) := by
      simpa [minSmoothness] using
        (show (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)
    exact IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞)) hsmooth
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞))
      (by exact_mod_cast (show ((2 : ℕ∞) + 1) ≤ (⊤ : ℕ∞) from le_top))
  rw [coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor_transpose g t p b hx i j]
  exact intrinsicRicciTensor_symm g t x _ _

end RicciFlow
