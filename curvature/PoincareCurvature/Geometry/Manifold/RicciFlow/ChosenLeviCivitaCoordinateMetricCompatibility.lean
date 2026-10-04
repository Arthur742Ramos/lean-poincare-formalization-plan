/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateCurvature

/-!
# Actual chosen Levi--Civita metric compatibility in the preferred frame

The actual torsion-free predicate and proved coordinate-frame commutation
interchange the differentiated and direction slots. Actual metric compatibility
then identifies the resulting pairings with the genuine first metric derivative.
No connection symmetry or metric-derivative identity is assumed.
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

/-- The actual chosen connection differentiates the metric in the commuting
coordinate frame, after actual torsion cancellation exchanges its two slots. -/
theorem chosenLC_coordinateFrame_metricCompatibility
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (p : M)
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (q i j : Fin d) :
    (g t).inner x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (frame (I := I) p b q) x (frame (I := I) p b i x))
        (frame (I := I) p b j x) +
      (g t).inner x (frame (I := I) p b i x)
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (frame (I := I) p b q) x (frame (I := I) p b j x)) =
      first (chosenLCMetricCoordinates g t p b)
        (chosenLCCoordinatePoint (I := I) p b x) q i j := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞))
      (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)
  let cov : CovariantDerivative I E TM :=
    chosenLeviCivitaFamily (I := I) (M := M) g t
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet,
      extChartAt_source] using hx
  have hmd (r : Fin d) : MDiffAt (T% (frame (I := I) p b r)) x :=
    (((trivialization (I := I) p).contMDiffOn_localFrame_baseSet
      (I := I) (n := 2) b r) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase)
      |>.mdifferentiableAt (by norm_num)
  have hLevi : cov.IsLeviCivita :=
    chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g t
  have hswap (r : Fin d) :
      cov (frame (I := I) p b q) x (frame (I := I) p b r x) =
        cov (frame (I := I) p b r) x (frame (I := I) p b q x) := by
    apply sub_eq_zero.mp
    simpa only [CovariantDerivative.along,
      mlieBracket_frame_eq_zero (I := I) p b hx] using
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hLevi.1
        (X := frame (I := I) p b r) (Y := frame (I := I) p b q)
        (x := x) (hmd r) (hmd q)
  have hinner (y : M) (u v : TM y) : inner ℝ u v = (g t).inner y u v := rfl
  have hcomponent :
      (fun y => inner ℝ (frame (I := I) p b i y) (frame (I := I) p b j y)) =
        chosenLCMetricComponent g t p b i j := by
    funext y
    exact hinner y _ _
  have hmetric := hLevi.2 (hmd i) (hmd j) (frame (I := I) p b q x)
  rw [hcomponent, hinner x, hinner x] at hmetric
  change
    (g t).inner x (cov (frame (I := I) p b q) x (frame (I := I) p b i x))
        (frame (I := I) p b j x) +
      (g t).inner x (frame (I := I) p b i x)
        (cov (frame (I := I) p b q) x (frame (I := I) p b j x)) = _
  rw [hswap i, hswap j, first_chosenLCMetricCoordinates_eq_mvfderiv g t p b hx]
  exact hmetric.symm

end RicciFlow
