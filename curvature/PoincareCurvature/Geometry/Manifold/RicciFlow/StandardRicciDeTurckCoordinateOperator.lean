/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckCoordinateIdentification
import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateMetricCompatibility
import PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckEquation
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.CoordinateRicciDeTurckOperator

/-!
# Actual standard Ricci--DeTurck spatial operator

Actual chosen-LC differentiation of conventional W, actual torsion/metric
compatibility, and actual intrinsic Ricci identify the standard geometric RHS.
The corrected first background jet has both negative Lie contributions. The
frozen remainder retains the Hessian coefficient error. This is only a spatial
identity: there is no tensor heat-generator, analytic estimate, PDE solution,
time regularity, or Point-4 completion theorem here.
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

open AnalyticPDE.GenuinePhiRD

variable (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (p : M) (b : Module.Basis (Fin d) ℝ E)

/-- The actual conventional correction is the coordinate Lie expression.
Actual torsion and metric compatibility supply its metric transport term. -/
theorem standardDeTurckCorrection_coordinateFrame_eq_coordinateLie
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    standardDeTurckCorrection (I := I) (M := M) g background t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) =
      coordinateLie (chosenLCMetricCoordinates g t p b) (actualBackgroundCoordinates background t p b)
        (chosenLCCoordinatePoint (I := I) p b x) i j := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  let W := standardDeTurckVectorField (I := I) (M := M) g background t
  let cov := chosenLeviCivitaFamily (I := I) (M := M) g t
  let G := chosenLCMetricCoordinates g t p b
  let B := actualBackgroundCoordinates background t p b
  let z := chosenLCCoordinatePoint (I := I) p b x
  let F := frame (I := I) p b
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hW : MDiffAt (T% W) x :=
    (standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
      g background t hbackground x).mdifferentiableAt one_ne_zero
  have hdecomp (m : Fin d) :
      cov W x (F m x) =
        (∑ k : Fin d, mvfderiv (I := I) (standardDeTurckFrameCoeff g background t p b k)
          x (F m x) • F k x) +
        ∑ k : Fin d, standardDeTurckFrameCoeff g background t p b k x • cov (F k) x (F m x) := by
    have hCoeffFun (k : Fin d) :
        (LinearMap.piApply ((trivialization (I := I) p).localFrameCoeff I b k)) W =
          standardDeTurckFrameCoeff g background t p b k := by
      funext y
      rfl
    have h :=
      CovariantDerivative.TangentFrame.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
        (I := I) (trivialization (I := I) p) b cov hbase hW (F m x)
    simp_rw [hCoeffFun] at h
    simpa only [F, frame] using h
  have hgram (a c : Fin d) : G z a c = (g t).inner x (F a x) (F c x) :=
    congrFun (congrFun (chosenLCMetricCoordinates_eq_Gram g t p b hx) a) c
  have hcoeff (k : Fin d) : standardDeTurckFrameCoeff g background t p b k x = deTurck G B z k :=
    standardDeTurck_coordinateFrameCoeff_eq_deTurck g background t p b hx k
  have hderiv (m k : Fin d) :
      mvfderiv (I := I) (standardDeTurckFrameCoeff g background t p b k) x (F m x) =
        deTurckFirst G B z m k :=
    standardDeTurck_coordinateFrameCoeff_mvfderiv_eq_deTurckFirst g background t p b hbackground hx m k
  have hinner (u v : TM x) : inner ℝ u v = (g t).inner x u v := rfl
  have hleft : (g t).inner x (cov W x (F i x)) (F j x) =
      ∑ k : Fin d, (G z k j * deTurckFirst G B z i k +
        deTurck G B z k * (g t).inner x (cov (F k) x (F i x)) (F j x)) := by
    rw [hdecomp i]
    rw [← hinner]
    simp only [inner_add_left, sum_inner, real_inner_smul_left, hderiv, hcoeff]
    simp only [hinner]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hgram k j]
    change _ * _ + _ * _ = _ * _ + _ * _
    ring
  have hright : (g t).inner x (F i x) (cov W x (F j x)) =
      ∑ k : Fin d, (G z i k * deTurckFirst G B z j k +
        deTurck G B z k * (g t).inner x (F i x) (cov (F k) x (F j x))) := by
    rw [hdecomp j]
    rw [← hinner]
    simp only [inner_add_right, inner_sum, real_inner_smul_right, hderiv, hcoeff]
    simp only [hinner]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hgram i k]
    change _ * _ + _ * _ = _ * _ + _ * _
    ring
  rw [standardDeTurckCorrection_apply]
  change (g t).inner x (cov W x (F i x)) (F j x) +
    (g t).inner x (F i x) (cov W x (F j x)) = coordinateLie G B z i j
  rw [hleft, hright, ← Finset.sum_add_distrib]
  unfold coordinateLie
  apply Finset.sum_congr rfl
  intro k _
  have hmetric : (g t).inner x (cov (F k) x (F i x)) (F j x) +
      (g t).inner x (F i x) (cov (F k) x (F j x)) = first G z k i j :=
    chosenLC_coordinateFrame_metricCompatibility g t p b hx k i j
  calc
    (G z k j * deTurckFirst G B z i k +
        deTurck G B z k * (g t).inner x (cov (F k) x (F i x)) (F j x)) +
      (G z i k * deTurckFirst G B z j k +
        deTurck G B z k * (g t).inner x (F i x) (cov (F k) x (F j x))) =
        G z k j * deTurckFirst G B z i k + G z i k * deTurckFirst G B z j k +
          deTurck G B z k * ((g t).inner x (cov (F k) x (F i x)) (F j x) +
            (g t).inner x (F i x) (cov (F k) x (F j x))) := by ring
    _ = _ := by rw [hmetric]

/-- Actual intrinsic Ricci and conventional Lie correction give the coordinate RHS. -/
theorem standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) =
      coordinateRD (chosenLCMetricCoordinates g t p b) (actualBackgroundCoordinates background t p b)
        (chosenLCCoordinatePoint (I := I) p b x) i j := by
  rw [standardRicciDeTurckRHS_apply,
    standardDeTurckCorrection_coordinateFrame_eq_coordinateLie g background t p b hbackground hx]
  change (-2 : ℝ) * intrinsicRicciTensor (I := I) (M := M) g t x
    (frame (I := I) p b i x) (frame (I := I) p b j x) + _ = _
  rw [← coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor g t p b hx]
  rfl

/-- Actual conventional geometric RHS equals the corrected produced-jet RHS. -/
theorem standardRicciDeTurckRHS_coordinateFrame_eq_correctedJet
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) =
      phiRDWithBackgroundJetOfJet
        (actualBackgroundCoordinates background t p b (chosenLCCoordinatePoint (I := I) p b x))
        (backgroundFirst (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x))
        (AnalyticPDE.coordinateJet (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x)) i j := by
  rw [standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD g background t p b hbackground hx]
  exact coordinateRD_eq_correctedJet (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b)
    (contDiffOn_actualBackgroundCoordinates background t p b hbackground)
    (chosenLCCoordinatePoint_mem (I := I) b hx)
    (chosenLCMetricCoordinates_det_ne_zero g t p b hx) i j

/-- The actual geometric operator has the inverse-metric Hessian principal part.
The corrected lower-order expression retains both negative background-first-jet terms. -/
theorem standardRicciDeTurckRHS_coordinateFrame_eq_principal_add_lowerOrder
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) =
      (∑ a : Fin d, ∑ c : Fin d,
        inverse (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) a c *
          second (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) a c i j) +
      lowerOrderRDWithBackgroundJetOfJet
        (actualBackgroundCoordinates background t p b (chosenLCCoordinatePoint (I := I) p b x))
        (backgroundFirst (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x))
        (AnalyticPDE.coordinateJet (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x)) i j := by
  rw [standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD g background t p b hbackground hx]
  exact coordinateRD_eq_principal_add_lowerOrder (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b)
    (contDiffOn_actualBackgroundCoordinates background t p b hbackground)
    (chosenLCCoordinatePoint_mem (I := I) b hx)
    (fun z _ => chosenLCMetricCoordinates_symm g t p b z)
    (chosenLCMetricCoordinates_det_ne_zero g t p b hx) i j

/-- Freezing at arbitrary A retains the genuine Hessian-dependent coefficient error.
No identification of A with a manifold tensor heat generator is assumed or asserted. -/
theorem standardRicciDeTurckRHS_coordinateFrame_eq_frozenPrincipal_add_remainder
    (A : Fin d → Fin d → ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {x : M} (hx : x ∈ (extChartAt I p).source) (i j : Fin d) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x
        (frame (I := I) p b i x) (frame (I := I) p b j x) =
      (∑ a : Fin d, ∑ c : Fin d, A a c *
        second (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) a c i j) +
      ((∑ a : Fin d, ∑ c : Fin d,
        (inverse (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) a c - A a c) *
          second (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x) a c i j) +
        lowerOrderRDWithBackgroundJetOfJet
          (actualBackgroundCoordinates background t p b (chosenLCCoordinatePoint (I := I) p b x))
          (backgroundFirst (actualBackgroundCoordinates background t p b) (chosenLCCoordinatePoint (I := I) p b x))
          (AnalyticPDE.coordinateJet (chosenLCMetricCoordinates g t p b) (chosenLCCoordinatePoint (I := I) p b x)) i j) := by
  rw [standardRicciDeTurckRHS_coordinateFrame_eq_coordinateRD g background t p b hbackground hx]
  exact coordinateRD_eq_frozenPrincipal_add_remainder A (isOpen_chosenLCCoordinateDomain (I := I) p b)
    (contDiffOn_chosenLCMetricCoordinates g t p b)
    (contDiffOn_actualBackgroundCoordinates background t p b hbackground)
    (chosenLCCoordinatePoint_mem (I := I) b hx)
    (fun z _ => chosenLCMetricCoordinates_symm g t p b z)
    (chosenLCMetricCoordinates_det_ne_zero g t p b hx) i j

end RicciFlow
