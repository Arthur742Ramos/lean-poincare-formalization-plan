import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.InverseLocalization

public noncomputable section

open Set
open scoped Topology NNReal BigOperators

namespace PoincareCurvature.Palomar

theorem parabolicDistance_dilation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : ℝ) (p q : ℝ × X) :
    RicciFlow.AnalyticPDE.parabolicDistance
        (r ^ 2 * p.1, r • p.2) (r ^ 2 * q.1, r • q.2) =
      |r| * RicciFlow.AnalyticPDE.parabolicDistance p q :=
  RicciFlow.AnalyticPDE.parabolicDistance_dilation r p q

theorem parabolicClosedBall_zero_mapsTo_dilation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r ρ : ℝ} :
    Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2))
      (RicciFlow.AnalyticPDE.parabolicClosedBall (0 : ℝ × X) ρ)
      (RicciFlow.AnalyticPDE.parabolicClosedBall (0 : ℝ × X) (|r| * ρ)) :=
  RicciFlow.AnalyticPDE.parabolicClosedBall_zero_mapsTo_dilation

theorem parabolicBall_exists_finset_cover_closedBall_subset_open_of_isCompact
    {X : Type*} [PseudoMetricSpace X] {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Finset (ℝ × X),
      (∀ x ∈ N, x ∈ K) ∧
      ∃ R : (ℝ × X) → ℝ,
        (∀ x ∈ N, 0 < R x) ∧
        (∀ x ∈ N, RicciFlow.AnalyticPDE.parabolicClosedBall x (R x) ⊆ U) ∧
        K ⊆ ⋃ x ∈ N, RicciFlow.AnalyticPDE.parabolicBall x (R x) :=
  RicciFlow.AnalyticPDE.parabolicBall.exists_finset_cover_closedBall_subset_open_of_isCompact
    hK hUopen hKU

theorem parabolicC0AlphaWith_comp_parabolicDistanceLe
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {B H α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : RicciFlow.AnalyticPDE.ParabolicC0AlphaWith B H α u s)
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      RicciFlow.AnalyticPDE.parabolicDistance (φ p) (φ q) ≤
        L * RicciFlow.AnalyticPDE.parabolicDistance p q) :
    RicciFlow.AnalyticPDE.ParabolicC0AlphaWith B (H * L ^ α) α
      (fun p => u (φ p)) t :=
  RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.comp_parabolicDistanceLe
    hu hH hα hL hmaps hφ

theorem parabolicC0AlphaWith_inv_sub_inv
    {X : Type*} [PseudoMetricSpace X]
    {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ}
    {a b : ℝ × X → 𝕜} {Ba Ha Bb Hb Bd Hd α : ℝ} {s : Set (ℝ × X)}
    (ha : RicciFlow.AnalyticPDE.ParabolicC0AlphaWith Ba Ha α a s)
    (hb : RicciFlow.AnalyticPDE.ParabolicC0AlphaWith Bb Hb α b s)
    (hdiff : RicciFlow.AnalyticPDE.ParabolicC0AlphaWith Bd Hd α
      (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖)
    (hBd : 0 ≤ Bd) :
    RicciFlow.AnalyticPDE.ParabolicC0AlphaWith
      (RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.invSubBoundConst δ Bd)
      (RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.invSubHolderConst
        δ Ha Hb Bd Hd) α
      (fun z => (a z)⁻¹ - (b z)⁻¹) s :=
  RicciFlow.AnalyticPDE.ParabolicC0AlphaWith.inv_sub_inv
    ha hb hdiff hδpos hδa hδb hBd

theorem parabolicC0AlphaOn_of_finset_parabolicBall_cover_closedBall
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {α : ℝ} {u : ℝ × X → E} {r : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hα : 0 < α) (hr : 0 < r)
    (hcover : K ⊆ ⋃ y ∈ N, RicciFlow.AnalyticPDE.parabolicBall y r)
    (hlocal : ∀ y ∈ N, RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α u
      (RicciFlow.AnalyticPDE.parabolicClosedBall y (2 * r))) :
    RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α u K :=
  RicciFlow.AnalyticPDE.ParabolicC0AlphaOn.of_finset_parabolicBall_cover_closedBall
    N hα hr hcover hlocal

theorem parabolicC0AlphaOn_inverse_difference_of_finset_parabolicBall_cover_closedBall
    {X : Type*} [PseudoMetricSpace X]
    {𝕜 : Type*} [NormedField 𝕜] {α δ r : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hα : 0 < α) (hr : 0 < r)
    {a b : ℝ × X → 𝕜}
    (hcover : K ⊆ ⋃ y ∈ N, RicciFlow.AnalyticPDE.parabolicBall y r)
    (hlocal_a : ∀ y ∈ N, RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α a
      (RicciFlow.AnalyticPDE.parabolicClosedBall y (2 * r)))
    (hlocal_b : ∀ y ∈ N, RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α b
      (RicciFlow.AnalyticPDE.parabolicClosedBall y (2 * r)))
    (hlocal_diff : ∀ y ∈ N,
      RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α (fun z => a z - b z)
        (RicciFlow.AnalyticPDE.parabolicClosedBall y (2 * r)))
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ K → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ K → δ ≤ ‖b p‖) :
    RicciFlow.AnalyticPDE.ParabolicC0AlphaOn α
      (fun z => (a z)⁻¹ - (b z)⁻¹) K :=
  RicciFlow.AnalyticPDE.ParabolicC0AlphaOn.inverse_difference_of_finset_parabolicBall_cover_closedBall
    N hα hr hcover hlocal_a hlocal_b hlocal_diff hδpos hδa hδb

end PoincareCurvature.Palomar
