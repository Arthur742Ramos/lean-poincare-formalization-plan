/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ConcreteRicciDeTurck
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckHolderDifference

/-!
# Little-Hölder section Duhamel interface for Point 4

The genuine Ricci--DeTurck estimates in
`GenuineRicciDeTurckHolderDifference` are now estimates for a map whose
domain is the little-Hölder `Jet2Section` but whose packaged output is in the
ambient big-Hölder `Jet2HolderSection`. The actual contraction theorem,
however, needs an endomap of one complete state space.

This file closes the type-correct linear/interface side of that gap:

* the componentwise little-Hölder heat propagator is lifted to the complete
  `Jet2Section` space;
* its identity, contraction bound, and joint time-space continuity are proved;
* a parameterized `LocalDuhamelData` constructor is provided for any genuine
  little-Hölder endomap satisfying the explicit local Lipschitz estimate.

The constructor deliberately does not coerce the existing big-Hölder output
into `Jet2Section`. The remaining nonlinear gate is therefore explicit:
prove that the genuine Ricci--DeTurck Nemytskii output has little-Hölder
components (and then instantiate the constructor with that endomap). No PDE
existence theorem is claimed here.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology Metric
open scoped NNReal ENNReal Interval

variable {d : ℕ} {α : ℝ}

/-! ## 1. The componentwise section propagator -/

/-- The matrix little-Hölder propagator at time zero is the identity. -/
theorem matrixLittleHolderPropagator_zero :
    matrixLittleHolderPropagator (n := d) (d := d) (α := α) 0 =
      ContinuousLinearMap.id ℝ (MatrixLittleHolder d d α) := by
  ext F i j
  rw [matrixLittleHolderPropagator_apply]
  rw [LittleHolder.littleHolderPropagator_of_nonpos (n := d) (α := α)
    (by norm_num)]
  rfl

/-- Joint continuity of the matrix little-Hölder heat propagator. -/
theorem matrixLittleHolderPropagator_hSjoint {T : ℝ} (hT : 0 < T) :
    ContinuousOn
      (fun p : ℝ × MatrixLittleHolder d d α ↦
        matrixLittleHolderPropagator (n := d) (d := d) (α := α) p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
  have hscalar := LittleHolder.littleHolderPropagator_hSjoint
    (n := d) (α := α) (T := T) hT
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hcomp : ContinuousOn
      (fun p : ℝ × MatrixLittleHolder d d α ↦
        LittleHolder.littleHolderPropagator (n := d) (α := α)
          p.1 (p.2 i j))
      (Icc (0 : ℝ) T ×ˢ univ) := by
    have hproj : ContinuousOn
        (fun p : ℝ × MatrixLittleHolder d d α ↦ (p.1, p.2 i j))
        (Icc (0 : ℝ) T ×ˢ univ) := by
      apply ContinuousOn.prodMk
      · exact continuousOn_fst
      · have hrow : Continuous (fun p : ℝ × MatrixLittleHolder d d α ↦ p.2 i) :=
          (continuous_apply i).comp continuous_snd
        exact ((continuous_apply j).comp hrow).continuousOn
    apply hscalar.comp hproj
    intro p hp
    simp only [mem_prod, mem_Icc, mem_univ, and_true] at hp ⊢
    exact hp
  have heq :
      (fun p : ℝ × MatrixLittleHolder d d α ↦
        matrixLittleHolderPropagator (n := d) (d := d) (α := α) p.1 p.2 i j) =
      (fun p : ℝ × MatrixLittleHolder d d α ↦
        LittleHolder.littleHolderPropagator (n := d) (α := α)
          p.1 (p.2 i j)) := by
    funext p
    rw [matrixLittleHolderPropagator_apply]
  rw [heq]
  exact hcomp

/-- Componentwise heat propagation on the genuine little-Hölder 2-jet space. -/
noncomputable def jet2SectionLittleHolderPropagator (t : ℝ) :
    Jet2Section d d α →L[ℝ] Jet2Section d d α :=
  let P := matrixLittleHolderPropagator (n := d) (d := d) (α := α) t
  { toFun := fun s =>
      (P s.1, fun k => P (s.2.1 k), fun k l => P (s.2.2 k l))
    map_add' := by
      intro s₁ s₂
      show (P (s₁ + s₂).1, _, _) = (P s₁.1, _, _) + (P s₂.1, _, _)
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
        simp only [Prod.fst_add, Prod.snd_add]
      · exact P.map_add _ _
      · funext k
        show P ((s₁ + s₂).2.1 k) = _
        have h : (s₁ + s₂).2.1 k = s₁.2.1 k + s₂.2.1 k := rfl
        rw [h]
        exact P.map_add _ _
      · funext k l
        show P ((s₁ + s₂).2.2 k l) = _
        have h : (s₁ + s₂).2.2 k l = s₁.2.2 k l + s₂.2.2 k l := rfl
        rw [h]
        exact P.map_add _ _
    map_smul' := by
      intro c s
      show (P (c • s).1, _, _) = c • (P s.1, _, _)
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only []
      · exact P.map_smul _ _
      · funext k
        show P ((c • s).2.1 k) = _
        have h : (c • s).2.1 k = c • s.2.1 k := rfl
        rw [h]
        exact P.map_smul _ _
      · funext k l
        show P ((c • s).2.2 k l) = _
        have h : (c • s).2.2 k l = c • s.2.2 k l := rfl
        rw [h]
        exact P.map_smul _ _
    cont := by
      show Continuous fun s : Jet2Section d d α =>
        (P s.1, (fun k => P (s.2.1 k), fun k l => P (s.2.2 k l)))
      apply Continuous.prodMk
      · exact P.continuous.comp continuous_fst
      · apply Continuous.prodMk
        · apply continuous_pi
          intro k
          exact P.continuous.comp
            ((continuous_apply k).comp (continuous_fst.comp continuous_snd))
        · apply continuous_pi
          intro k
          apply continuous_pi
          intro l
          exact P.continuous.comp
            ((continuous_apply l).comp
              ((continuous_apply k).comp (continuous_snd.comp continuous_snd))) }

@[simp] theorem jet2SectionLittleHolderPropagator_apply (t : ℝ)
    (s : Jet2Section d d α) :
    jet2SectionLittleHolderPropagator (d := d) (α := α) t s =
      (matrixLittleHolderPropagator (n := d) (d := d) (α := α) t s.1,
        fun k => matrixLittleHolderPropagator (n := d) (d := d) (α := α) t
          (s.2.1 k),
        fun k l => matrixLittleHolderPropagator (n := d) (d := d) (α := α) t
          (s.2.2 k l)) := by
  rfl

/-- The section propagator fixes the origin of time. -/
theorem jet2SectionLittleHolderPropagator_zero :
    jet2SectionLittleHolderPropagator (d := d) (α := α) 0 =
      ContinuousLinearMap.id ℝ (Jet2Section d d α) := by
  apply ContinuousLinearMap.ext
  intro s
  rw [jet2SectionLittleHolderPropagator_apply, matrixLittleHolderPropagator_zero]
  simp only [ContinuousLinearMap.id_apply]

/-- The section propagator is a contraction in the full product norm. -/
theorem norm_jet2SectionLittleHolderPropagator_le (t : ℝ) :
    ‖jet2SectionLittleHolderPropagator (d := d) (α := α) t‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
  intro s
  rw [jet2SectionLittleHolderPropagator_apply]
  have hP : ‖matrixLittleHolderPropagator (n := d) (d := d) (α := α) t‖ ≤ 1 :=
    norm_matrixLittleHolderPropagator_le (n := d) (d := d) (α := α) t
  have hentry (F : MatrixLittleHolder d d α) :
      ‖matrixLittleHolderPropagator (n := d) (d := d) (α := α) t F‖ ≤ ‖F‖ := by
    calc
      ‖matrixLittleHolderPropagator (n := d) (d := d) (α := α) t F‖ ≤
          ‖matrixLittleHolderPropagator (n := d) (d := d) (α := α) t‖ * ‖F‖ :=
        (matrixLittleHolderPropagator (n := d) (d := d) (α := α) t).le_opNorm F
      _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖F‖ := one_mul _
  rw [Prod.norm_def]
  simp only [one_mul]
  apply max_le
  · exact le_trans (hentry s.1) (prod_fst_norm_le s)
  · rw [Prod.norm_def]
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro k
      exact le_trans (hentry (s.2.1 k))
        (le_trans (norm_le_pi_norm _ k)
          (le_trans (prod_fst_norm_le s.2) (prod_snd_norm_le s)))
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro k
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro l
      exact le_trans (hentry (s.2.2 k l))
        (le_trans (norm_le_pi_norm _ l)
          (le_trans (norm_le_pi_norm _ k)
            (le_trans (prod_snd_norm_le s.2) (prod_snd_norm_le s))))

/-! ## 2. Joint continuity on the section space -/

theorem jet2SectionLittleHolderPropagator_hSjoint {T : ℝ} (hT : 0 < T) :
    ContinuousOn
      (fun p : ℝ × Jet2Section d d α ↦
        jet2SectionLittleHolderPropagator (d := d) (α := α) p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
  have hmatrix := matrixLittleHolderPropagator_hSjoint
    (d := d) (α := α) (T := T) hT
  apply ContinuousOn.prodMk
  · have hproj : ContinuousOn
        (fun p : ℝ × Jet2Section d d α ↦ (p.1, p.2.1))
        (Icc (0 : ℝ) T ×ˢ univ) := by
      apply ContinuousOn.prodMk
      · exact continuousOn_fst
      · exact (continuous_fst.comp continuous_snd).continuousOn
    simpa [Function.comp_def, jet2SectionLittleHolderPropagator_apply] using
      hmatrix.comp hproj (by
        intro p hp
        simp only [mem_prod, mem_Icc, mem_univ, and_true] at hp ⊢
        exact hp)
  · apply ContinuousOn.prodMk
    · apply continuousOn_pi.mpr
      intro k
      have hproj : ContinuousOn
          (fun p : ℝ × Jet2Section d d α ↦ (p.1, p.2.2.1 k))
          (Icc (0 : ℝ) T ×ˢ univ) := by
        apply ContinuousOn.prodMk
        · exact continuousOn_fst
        · have hs : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2) :=
            continuous_snd
          have hbc : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2.2) :=
            continuous_snd.comp hs
          have hrow : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2.2.1) :=
            continuous_fst.comp hbc
          exact ((continuous_apply k).comp hrow).continuousOn
      simpa [Function.comp_def, jet2SectionLittleHolderPropagator_apply] using
        hmatrix.comp hproj (by
          intro p hp
          simp only [mem_prod, mem_Icc, mem_univ, and_true] at hp ⊢
          exact hp)
    · apply continuousOn_pi.mpr
      intro k
      apply continuousOn_pi.mpr
      intro l
      have hproj : ContinuousOn
          (fun p : ℝ × Jet2Section d d α ↦ (p.1, p.2.2.2 k l))
          (Icc (0 : ℝ) T ×ˢ univ) := by
        apply ContinuousOn.prodMk
        · exact continuousOn_fst
        · have hs : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2) :=
            continuous_snd
          have hbc : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2.2) :=
            continuous_snd.comp hs
          have hc : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2.2.2) :=
            continuous_snd.comp hbc
          have hrow : Continuous (fun p : ℝ × Jet2Section d d α ↦ p.2.2.2 k) :=
            (continuous_apply k).comp hc
          have hentry : Continuous (fun p : ℝ × Jet2Section d d α ↦
              p.2.2.2 k l) := (continuous_apply l).comp hrow
          exact hentry.continuousOn
      simpa [Function.comp_def, jet2SectionLittleHolderPropagator_apply] using
        hmatrix.comp hproj (by
          intro p hp
          simp only [mem_prod, mem_Icc, mem_univ, and_true] at hp ⊢
          exact hp)

/-! ## 3. The honest local-Duhamel constructor -/

/-- Assemble local Duhamel data on the genuine little-Hölder 2-jet space.

The nonlinear endomap and its local Lipschitz estimate are explicit inputs.
This is the intended consumption point for the future theorem that the
genuine Ricci--DeTurck Nemytskii output has little-Hölder components. -/
noncomputable def littleHolderJet2LocalDuhamelData
    (T₀ : ℝ) (hT₀ : 0 < T₀)
    (N : Jet2Section d d α → Jet2Section d d α)
    (c : Jet2Section d d α) (R : ℝ≥0) (hR : 0 < R)
    (L : ℝ≥0)
    (hN : LipschitzOnWith L N (Metric.closedBall c (R : ℝ≥0)))
    (u₀ : Jet2Section d d α)
    (hu₀ : dist u₀ c < (R : ℝ)) :
    LocalDuhamelData (X := Jet2Section d d α) where
  T₀ := T₀
  hT₀ := hT₀
  S := jet2SectionLittleHolderPropagator (d := d) (α := α)
  hS0 := jet2SectionLittleHolderPropagator_zero (d := d) (α := α)
  M := 1
  hSbound := by
    intro t ht
    have h := norm_jet2SectionLittleHolderPropagator_le
      (d := d) (α := α) t
    simpa using h
  hSjoint := jet2SectionLittleHolderPropagator_hSjoint
    (d := d) (α := α) hT₀
  N := N
  c := c
  R := R
  hR := hR
  L := L
  hN := hN
  u₀ := u₀
  hu₀ := hu₀

/-- The abstract local mild-solution theorem applied to the little-Hölder
section interface. -/
theorem exists_local_mild_solution_of_littleHolderJet2
    (T₀ : ℝ) (hT₀ : 0 < T₀)
    (N : Jet2Section d d α → Jet2Section d d α)
    (c : Jet2Section d d α) (R : ℝ≥0) (hR : 0 < R)
    (L : ℝ≥0)
    (hN : LipschitzOnWith L N (Metric.closedBall c (R : ℝ≥0)))
    (u₀ : Jet2Section d d α)
    (hu₀ : dist u₀ c < (R : ℝ)) :
    ∃ (T : ℝ) (hT : 0 < T) (hle : T ≤ T₀),
      ∃ u : C(Icc (0 : ℝ) T, Jet2Section d d α),
        ((littleHolderJet2LocalDuhamelData T₀ hT₀ N c R hR L hN u₀ hu₀).toDuhamelData
            T hT hle).duhamelMap u = u ∧
        ∀ t : Icc (0 : ℝ) T, dist (u t) c < (R : ℝ) := by
  exact LocalDuhamelData.exists_local_mild_solution
    (littleHolderJet2LocalDuhamelData T₀ hT₀ N c R hR L hN u₀ hu₀)

end AnalyticPDE
end RicciFlow
