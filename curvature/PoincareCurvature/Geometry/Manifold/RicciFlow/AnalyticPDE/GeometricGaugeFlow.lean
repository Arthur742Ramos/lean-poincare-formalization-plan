module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EndpointGaugeFlow

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Geometric endpoint gauge-flow reductions

This extension module packages endpoint Ricci-DeTurck chart data whose gauge input
is the geometric `SatisfiesGaugeFlowOn` formulation.  It projects to the
derivative-level endpoint bundles via the reusable `C^3` gauge-flow derivative
bridge, keeping the larger analytic endpoint file stable.
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
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

set_option maxHeartbeats 1000000

/-- Bundled global endpoint data whose non-identity gauge input is a geometric
`C^3` intrinsic DeTurck gauge-flow family. -/
structure EndpointGeometricGaugeFlowFamilyData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F] where
  T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ
  a : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  L : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kpic : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kstate : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
      (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp)
  metric :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      MetricFamily (I := I) (M := M)
  background :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ConnectionFamily (I := I) (M := M)
  metric_eq_curve :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v
  initial_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime
  terminal_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime
  chartRHS_eq_intrinsic :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          (chart ivp).A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric ivp sol) (background ivp sol) t x u v
  hbackground :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      background ivp sol = chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol)
  encode :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp),
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) (chart ivp) candidate.1
  gaugeFlow : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
    (E := F) (H := H) (I := I) (M := M)
  hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((gaugeFlow.maps3 ivp sol) τ) x)
                (((gaugeFlow.maps3 ivp sol) τ).pushforwardTangent x u)
                (((gaugeFlow.maps3 ivp sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gaugeFlow.gauge ivp sol) t x u v) t

/-- Convert geometric global endpoint gauge-flow data to the derivative-level
endpoint bundle. -/
def EndpointGeometricGaugeFlowFamilyData.toEndpointDerivativeGaugeFlowFamilyData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  maps3 := D.gaugeFlow.maps3
  anchored := D.gaugeFlow.anchored
  hflowDeriv := D.gaugeFlow.derivativeFamily
  hderiv := by
    intro ivp sol t ht x u v
    simpa using D.hderiv ivp sol ht x u v

/-- Geometric global endpoint gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toInnerDerivativeGaugeReducibleFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toEndpointDerivativeGaugeFlowFamilyData.toInnerDerivativeGaugeReducibleFamily

/-- Geometric global endpoint gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toIntrinsicLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Geometric global endpoint gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

/-- Bundled interval endpoint data whose non-identity gauge input is a geometric
`C^3` intrinsic DeTurck gauge-flow family. -/
structure EndpointGeometricGaugeFlowFamilyDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F] where
  T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ
  a : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  L : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kpic : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kstate : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
      (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp)
  metric :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      MetricFamily (I := I) (M := M)
  background :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ConnectionFamily (I := I) (M := M)
  metric_eq_curve :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v
  initial_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime
  terminal_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime
  chartRHS_eq_intrinsic :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          (chart ivp).A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric ivp sol) (background ivp sol) t x u v
  hbackground :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      background ivp sol = chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol)
  encode :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) (chart ivp) candidate.1
  gaugeFlow : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
    (E := F) (H := H) (I := I) (M := M)
  hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((gaugeFlow.maps3 ivp sol) τ) x)
                (((gaugeFlow.maps3 ivp sol) τ).pushforwardTangent x u)
                (((gaugeFlow.maps3 ivp sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gaugeFlow.gauge ivp sol) t x u v) t

/-- Convert geometric interval endpoint gauge-flow data to the derivative-level
endpoint bundle. -/
def EndpointGeometricGaugeFlowFamilyDataOnIcc.toEndpointDerivativeGaugeFlowFamilyDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  maps3 := D.gaugeFlow.maps3
  anchored := D.gaugeFlow.anchored
  hflowDeriv := D.gaugeFlow.derivativeFamily
  hderiv := by
    intro ivp sol t ht x u v
    simpa using D.hderiv ivp sol ht x u v

/-- Geometric interval endpoint gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toInnerDerivativeGaugeReducibleFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toEndpointDerivativeGaugeFlowFamilyDataOnIcc.toInnerDerivativeGaugeReducibleFamily

/-- Geometric interval endpoint gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toIntrinsicLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Geometric interval endpoint gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
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
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
