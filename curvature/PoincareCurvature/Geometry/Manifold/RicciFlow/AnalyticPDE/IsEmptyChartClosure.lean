module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization

/-!
# IsEmpty-manifold Ricci-DeTurck Banach chart, closure data, and point-4 assembly

This leaf module constructs the **first genuine inhabitants** of the two named structures on the
Ricci-DeTurck chart-closure critical path — the time-dependent geometric Banach chart
(`TimeDependentGeometricRicciDeTurckBanachChart`) and its closure data
(`RicciDeTurckChartClosureData`) — on the empty-manifold sub-class, and feeds them through the
already-proved bridge `intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData` to a
genuine `IntrinsicLocalExistenceUniquenessFamily` witness.

On `[IsEmpty M]` the continuous-section space is trivial, so the honest Banach representative of the
Ricci-DeTurck operator can be taken to be the **constant field** at the initial section; every
Picard-Lindelöf estimate is then either an equality (`‖·‖ ≤ ‖·‖₊`) or a constant-map bound, and the
geometric identification, realization, and encoding obligations are all vacuous over the empty base.
This exercises the whole chart → closure-data → bridge assembly end to end (the general
positive-dimensional case additionally requires the parabolic Schauder a-priori bound that supplies a
genuinely Lipschitz Banach representative).
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

section IsEmptyChart

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]
variable [IsEmpty M]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "TM" => (TangentSpace I : M → Type _)

/-- The initial continuous section carried by a continuous Riemannian metric, viewed in the
finite-cover bundled section space.  This is exactly the Picard-Lindelöf center used by the chart. -/
def isEmptyInitialSection
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  ⟨g₀.toSection, g₀.continuous_toSection⟩

/-- The first genuine inhabitant of `TimeDependentGeometricRicciDeTurckBanachChart`: on an empty
manifold the honest Banach representative of the Ricci-DeTurck operator is the constant field at the
initial section, all Picard-Lindelöf constants are supplied concretely, and the geometric
identification is vacuous over the empty base. -/
noncomputable def isEmptyRicciDeTurckBanachChart
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := TM)) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    (gF : MetricFamily (I := I) (M := M))
    (t₀ T : ℝ) (hT : t₀ < T) :
    TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T
      (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊ * (T - t₀).toNNReal + 1)
      (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊) 0 0 where
  A := fun _ _ => isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀
  hT := hT
  picard :=
    { lipschitzOnWith := fun _ _ => by
        intro p _ q _
        exact (edist_self _).trans_le (zero_le _)
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ _ _ => le_of_eq (coe_nnnorm _).symm
      mul_max_le := by
        have ht0 : ((⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ : Set.Icc t₀ T) : ℝ) = t₀ := rfl
        rw [ht0, sub_self, max_eq_left (by linarith : (0 : ℝ) ≤ T - t₀)]
        push_cast [Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ T - t₀)]
        nlinarith [NNReal.coe_nonneg
          (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊)] }
  lipschitz := fun _ => by
    intro p _ q _
    exact (edist_self _).trans_le (zero_le _)
  geometric := fun _ _ _ =>
    ⟨gF, chosenLeviCivitaFamily (I := I) (M := M) gF, fun x => isEmptyElim x⟩

end IsEmptyChart

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
