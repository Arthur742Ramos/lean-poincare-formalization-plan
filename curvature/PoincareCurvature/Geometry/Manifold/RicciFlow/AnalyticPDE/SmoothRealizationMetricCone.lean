module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealizationGaugeRoutes

set_option linter.unusedSectionVars false
set_option linter.all false
set_option synthInstance.maxHeartbeats 100000

/-!
# Metric-cone handoffs for smooth Ricci-DeTurck realization routes

This module keeps the heavy gauge-route layer unchanged and packages one more proof-level handoff:
positive-radius ambient interval closure data selects the standard metric-cone shrink, and the
existing terminal-fit compatibility for reverse encodings then produces the genuine symmetric-carrier
closure datum together with the chosen-background, intrinsic, and ordinary theorem packages.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance metricConeRoutesBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance metricConeRoutesBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))

section GlobalClosure

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]

/-- A positive-radius ambient interval closure package selects the standard metric-cone shrink and,
once reverse-encoded candidates are known to fit in that selected interval, produces both the
genuine symmetric-carrier closure datum and the chosen-background, intrinsic, and ordinary theorem
packages.  This is the fully bundled version of the metric-cone shrink handoff. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_symmetricCarrier_theoremPackages
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        ((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_⟩
  intro hencode_terminal
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart' :=
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime hball hencode_terminal
  refine ⟨Dsym, ?_, ?_, ?_⟩
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

end GlobalClosure

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
