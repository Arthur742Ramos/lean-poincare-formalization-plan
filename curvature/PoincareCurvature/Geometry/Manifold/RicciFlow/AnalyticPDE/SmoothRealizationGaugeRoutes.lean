module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative

set_option linter.unusedSectionVars false
set_option linter.all false
set_option synthInstance.maxHeartbeats 100000

/-!
# Raw-gauge routes from smooth Ricci-DeTurck realizations

This thin module keeps the heavy smooth-realization construction unchanged and
adds endpoint projections that explicitly pass through the raw identity `C^3`
gauge-flow and named scalar time-derivative interfaces.
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

local instance gaugeRoutesBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance gaugeRoutesBilFNormedSpace : NormedSpace ℝ BilF :=
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

/-- The Banach chart right-hand side differentiates the named
`metricBilinearCoordinateField` at the chart center for a smooth intrinsic
DeTurck realization.

This is the centered model-slot form of the finite-cover readout derivative
needed before a raw `C³` gauge-flow argument moves the base point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
      (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
        (M := M) (F := F) (I := I) x0 het ht)
      p uE vE

/-- Tangent-vector-slot version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

This exposes the same Banach chart right-hand side in the scalar shape used by
geometric gauge-pullback calculations. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
       (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
         (M := M) (F := F) (I := I) x0 het ht)
       p u v

/-- One-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

At every time in the closed-left/open-right Banach interval, the centered
metric-coordinate field has the Banach chart right-hand side as its right
derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE))
      (Ici t) t := by
  have hmetric :=
    realization.metric_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE) =ᶠ[𝓝[Ici t] t]
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) := by
    filter_upwards with τ
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  have hEq_t :
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) p) uE vE =
        metricTensor (I := I) (M := M) realization.metric t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE) := by
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  exact hmetric.congr_of_eventuallyEq hEq hEq_t

/-- Tangent-vector-slot one-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) (Ici t) t := by
  simpa using
    realization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v)

/-- The smooth realization supplies the raw identity-gauge scalar derivative
obligation on the open Banach interval, with the Banach chart right-hand side
as the metric velocity. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) realization.metric
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  exact
    SmoothSelfDiffeomorph3Family.id_pullbackMetricInnerDerivativeOn
      (I := I) (M := M)
      (realization.hasTimeDerivativeOn_Ioo_chartRHS
        (M := M) (F := F) (I := I) x0 het)

/-- The tensor time-derivative form of
`id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS`: the identity raw `C^3`
gauge-pullback of a smooth Banach realization is differentiated by the Banach
chart right-hand side on the open interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricFamily_hasTimeDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
        realization.metric)
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  simpa [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily] using
    (realization.hasTimeDerivativeOn_Ioo_chartRHS
      (M := M) (F := F) (I := I) x0 het)

/-- Global chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
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
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
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
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Global chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge
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
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_localExistenceUniqueness_viaRawIdentityGauge
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
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Interval chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Interval chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness_viaRawIdentityGauge
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Proof-level chosen-background theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_chosenIntrinsicDeTurckLocalExistenceUniqueness
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
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩

/-- Proof-level intrinsic theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness
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
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness⟩

/-- Proof-level ordinary theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness
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
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness⟩

end GlobalClosure

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow

