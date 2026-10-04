/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckMatrixLittleHolderClosure

/-!
# Heat-invariant little-Hölder reaction closure

The componentwise heat flow fixes the Euclidean section and preserves every
closed ball centered there. The existing compact-jet estimate therefore supplies
the heat-path range hypothesis in the matrix-valued little-Hölder closure proof.
The resulting reaction is locally Lipschitz in the full little-Hölder norm.

`Jet2Section` is an auxiliary product of independent component fields. These
results do not assert derivative compatibility of its slots, a Ricci--DeTurck
PDE solution, or the canonical Point-4 local existence/uniqueness theorem.
-/

namespace RicciFlow.AnalyticPDE

open Set Filter Topology Metric
open scoped NNReal ENNReal Interval
open GenuinePhiRD

variable {d : ℕ} {α : ℝ}

/-- The little-Hölder heat flow fixes constant scalar fields, at every time. -/
theorem littleHolderPropagator_constLittleHolder
    (n : ℕ) (α : ℝ) (t c : ℝ) :
    LittleHolder.littleHolderPropagator (n := n) (α := α) t
      (constLittleHolder n α c) = constLittleHolder n α c := by
  by_cases ht : 0 < t
  · rw [LittleHolder.littleHolderPropagator_of_pos ht]
    apply Subtype.ext
    change heatSemigroupHolderFun ht (constHolderBCF n α c) =
      constHolderBCF n α c
    exact heatSemigroupHolderFun_constHolderBCF ht c
  · rw [LittleHolder.littleHolderPropagator_of_nonpos ht]
    rfl

/-- Heat flow fixes the Euclidean metric section, including all zero slots. -/
theorem jet2SectionLittleHolderPropagator_euclideanSection (t : ℝ) :
    jet2SectionLittleHolderPropagator (d := d) (α := α) t
      (euclideanSection d α) = euclideanSection d α := by
  rw [jet2SectionLittleHolderPropagator_apply]
  apply Prod.ext
  · funext i j
    change LittleHolder.littleHolderPropagator t
      (constLittleHolder d α (if i = j then 1 else 0)) =
        constLittleHolder d α (if i = j then 1 else 0)
    exact littleHolderPropagator_constLittleHolder d α t _
  · apply Prod.ext
    · funext k i j
      change LittleHolder.littleHolderPropagator t
        (constLittleHolder d α 0) = constLittleHolder d α 0
      exact littleHolderPropagator_constLittleHolder d α t 0
    · funext k l i j
      change LittleHolder.littleHolderPropagator t
        (constLittleHolder d α 0) = constLittleHolder d α 0
      exact littleHolderPropagator_constLittleHolder d α t 0

/-- The Euclidean-centered section ball is invariant under componentwise heat. -/
theorem jet2SectionLittleHolderPropagator_mem_euclidean_closedBall
    (t : ℝ) {R : ℝ} {s : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R) :
    jet2SectionLittleHolderPropagator (d := d) (α := α) t s ∈
      Metric.closedBall (euclideanSection d α) R := by
  let P := jet2SectionLittleHolderPropagator (d := d) (α := α) t
  have hfix : P (euclideanSection d α) = euclideanSection d α :=
    jet2SectionLittleHolderPropagator_euclideanSection t
  have hnorm : ‖P‖ ≤ 1 := norm_jet2SectionLittleHolderPropagator_le t
  rw [Metric.mem_closedBall, dist_eq_norm] at hs ⊢
  calc
    ‖P s - euclideanSection d α‖ =
        ‖P (s - euclideanSection d α)‖ := by rw [map_sub, hfix]
    _ ≤ ‖P‖ * ‖s - euclideanSection d α‖ := P.le_opNorm _
    _ ≤ 1 * ‖s - euclideanSection d α‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ ≤ R := by simpa only [one_mul] using hs

/-- The compact fiber range along the heat path is derived from small data. -/
theorem jet2OfSection_heat_mem_phiRDNemytskiiData
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (t : ℝ) (x : Fin d → ℝ) :
    jet2OfSection
      (jet2SectionLittleHolderPropagator (d := d) (α := α) t s) x ∈
        (phiRDNemytskiiData (d := d) Γbg).K := by
  exact hrange_of_mem_closedBall Γbg (euclideanSection d α)
    (jet2OfSection_euclideanSection d α) hR hRsmall
    (jet2SectionLittleHolderPropagator_mem_euclidean_closedBall t hs) x

/-- The actual coordinate reaction is little-Hölder on the small-data ball,
without any separately supplied heat-path range certificate. -/
theorem isGoodHolder_geometricNRDHolder_of_euclidean_closedBall
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (i j : Fin d) :
    IsGoodHolder (geometricNRDHolder Γbg s hα0
      (hrange_of_mem_closedBall Γbg (euclideanSection d α)
        (jet2OfSection_euclideanSection d α) hR hRsmall hs) i j) := by
  apply isGoodHolder_geometricNRDHolder_of_heat_path Γbg s hα0 hα1
  intro t ht x
  exact jet2OfSection_heat_mem_phiRDNemytskiiData Γbg hR hRsmall hs t x

/-- The little-Hölder-valued coordinate reaction on the closed ball. Outside
the ball this total extension is zero; no global Lipschitz claim is made. -/
noncomputable def geometricNRDLittleHolderOnEuclideanClosedBall
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    (s : Jet2Section d d α) : MatrixLittleHolder d d α := by
  classical
  exact if hs : s ∈ Metric.closedBall (euclideanSection d α) R then
    fun i j => ⟨geometricNRDHolder Γbg s hα0
      (hrange_of_mem_closedBall Γbg (euclideanSection d α)
        (jet2OfSection_euclideanSection d α) hR hRsmall hs) i j,
      isGoodHolder_geometricNRDHolder_of_euclidean_closedBall
        Γbg hα0 hα1 hR hRsmall hs i j⟩
  else 0

/-- On the ball the total extension is exactly the packaged coordinate map. -/
theorem geometricNRDLittleHolderOnEuclideanClosedBall_eq
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R) :
    geometricNRDLittleHolderOnEuclideanClosedBall Γbg hα0 hα1 hR hRsmall s =
      fun i j => ⟨geometricNRDHolder Γbg s hα0
        (hrange_of_mem_closedBall Γbg (euclideanSection d α)
          (jet2OfSection_euclideanSection d α) hR hRsmall hs) i j,
        isGoodHolder_geometricNRDHolder_of_euclidean_closedBall
          Γbg hα0 hα1 hR hRsmall hs i j⟩ := by
  classical
  unfold geometricNRDLittleHolderOnEuclideanClosedBall
  split_ifs with h
  · rfl
  · exact (h hs).elim

/-- On the ball the packaged reaction evaluates to the actual coordinate map. -/
theorem geometricNRDLittleHolderOnEuclideanClosedBall_apply
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d))
    {s : Jet2Section d d α}
    (hs : s ∈ Metric.closedBall (euclideanSection d α) R)
    (x : Fin d → ℝ) (i j : Fin d) :
    ((geometricNRDLittleHolderOnEuclideanClosedBall Γbg hα0 hα1 hR hRsmall s
      i j).toHolder).toBCF x = geometricNRD Γbg s x i j := by
  rw [geometricNRDLittleHolderOnEuclideanClosedBall_eq Γbg hα0 hα1 hR hRsmall hs]
  exact geometricNRDHolder_apply Γbg s hα0 _ x i j

set_option maxHeartbeats 800000 in
/-- The matrix reaction obeys the full-norm local Lipschitz bound in the
little-Hölder carrier, whose norm is inherited from the ambient Hölder space. -/
theorem lipschitzOnWith_geometricNRDLittleHolderOnEuclideanClosedBall
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R)
    (hRsmall : 2 * jet2LipConst d d * R < phiRDRadius (d := d)) :
    LipschitzOnWith
      ⟨geometricNRDHolderBallLipschitzConst Γbg (euclideanSection d α) R,
        geometricNRDHolderBallLipschitzConst_nonneg Γbg (euclideanSection d α) hR⟩
      (geometricNRDLittleHolderOnEuclideanClosedBall Γbg hα0 hα1 hR hRsmall)
      (Metric.closedBall (euclideanSection d α) R) := by
  classical
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro s hs t ht
  rw [geometricNRDLittleHolderOnEuclideanClosedBall_eq Γbg hα0 hα1 hR hRsmall hs,
    geometricNRDLittleHolderOnEuclideanClosedBall_eq Γbg hα0 hα1 hR hRsmall ht]
  rw [dist_eq_norm, dist_eq_norm]
  let C := geometricNRDHolderBallLipschitzConst Γbg (euclideanSection d α) R
  have hnonneg : 0 ≤ C * ‖s - t‖ := mul_nonneg
    (geometricNRDHolderBallLipschitzConst_nonneg Γbg (euclideanSection d α) hR)
    (norm_nonneg _)
  have hfull : ‖geometricNRDHolder Γbg s hα0
      (hrange_of_mem_closedBall Γbg (euclideanSection d α)
        (jet2OfSection_euclideanSection d α) hR hRsmall hs) -
      geometricNRDHolder Γbg t hα0
        (hrange_of_mem_closedBall Γbg (euclideanSection d α)
          (jet2OfSection_euclideanSection d α) hR hRsmall ht)‖ ≤ C * ‖s - t‖ :=
    le_trans (norm_geometricNRDHolder_sub_le Γbg s t hα0 _ _)
      (mul_le_mul_of_nonneg_right
        (geometricNRDHolderLipschitzConst_le_ball Γbg (euclideanSection d α) s hs)
        (norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro j
  change ‖geometricNRDHolder Γbg s hα0 _ i j -
      geometricNRDHolder Γbg t hα0 _ i j‖ ≤ C * ‖s - t‖
  exact le_trans (le_trans (pi_entry_norm_le _ j) (pi_entry_norm_le _ i)) hfull

end RicciFlow.AnalyticPDE
