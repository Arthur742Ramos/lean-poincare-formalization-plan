module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Basic

set_option linter.unusedSectionVars false

/-!
# Parabolic Holder primitives

This file starts the parabolic-analysis vocabulary needed by the Ricci-DeTurck
Banach-chart program.  It does not assert Schauder estimates; it names the
parabolic distance and the corresponding Holder control predicate that those
future estimates should use.
-/

@[expose] public noncomputable section

open Set

namespace RicciFlow
namespace AnalyticPDE

/-- Parabolic distance on time-space: time has weight two and space has weight one. -/
def parabolicDistance {X : Type*} [PseudoMetricSpace X] (p q : ℝ × X) : ℝ :=
  max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)

namespace parabolicDistance

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X}

theorem nonneg (p q : ℝ × X) : 0 ≤ parabolicDistance p q :=
  le_max_of_le_left (Real.sqrt_nonneg _)

@[simp] theorem self (p : ℝ × X) : parabolicDistance p p = 0 := by
  simp [parabolicDistance]

theorem comm (p q : ℝ × X) : parabolicDistance p q = parabolicDistance q p := by
  simp [parabolicDistance, abs_sub_comm, dist_comm]

theorem sqrt_time_le (p q : ℝ × X) :
    Real.sqrt |p.1 - q.1| ≤ parabolicDistance p q :=
  le_max_left _ _

theorem space_dist_le (p q : ℝ × X) :
    dist p.2 q.2 ≤ parabolicDistance p q :=
  le_max_right _ _

/-- A parabolic ball bound controls the spatial distance. -/
theorem space_dist_le_of_le {R : ℝ} (h : parabolicDistance p q ≤ R) :
    dist p.2 q.2 ≤ R :=
  (space_dist_le p q).trans h

/-- A parabolic ball bound controls the time separation quadratically. -/
theorem time_abs_le_sq_of_le {R : ℝ} (hR : 0 ≤ R) (h : parabolicDistance p q ≤ R) :
    |p.1 - q.1| ≤ R ^ 2 := by
  have hsqrt : Real.sqrt |p.1 - q.1| ≤ R :=
    (sqrt_time_le p q).trans h
  calc
    |p.1 - q.1| = (Real.sqrt |p.1 - q.1|) ^ 2 := by
      rw [Real.sq_sqrt (abs_nonneg _)]
    _ ≤ R ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 hsqrt

end parabolicDistance

/-- Open parabolic ball in time-space. -/
def parabolicBall {X : Type*} [PseudoMetricSpace X] (p : ℝ × X) (R : ℝ) :
    Set (ℝ × X) :=
  {q | parabolicDistance p q < R}

/-- Closed parabolic ball in time-space.  This is the standard local cylinder shape for parabolic
estimates: spatial radius `R`, time radius `R^2`. -/
def parabolicClosedBall {X : Type*} [PseudoMetricSpace X] (p : ℝ × X) (R : ℝ) :
    Set (ℝ × X) :=
  {q | parabolicDistance p q ≤ R}

namespace parabolicBall

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X} {R R' : ℝ}

@[simp] theorem mem : q ∈ parabolicBall p R ↔ parabolicDistance p q < R := Iff.rfl

theorem mono (hR : R ≤ R') : parabolicBall p R ⊆ parabolicBall p R' := by
  intro q hq
  exact lt_of_lt_of_le hq hR

theorem subset_closedBall : parabolicBall p R ⊆ parabolicClosedBall p R := by
  intro q hq
  exact le_of_lt (show parabolicDistance p q < R from hq)

theorem mem_comm : q ∈ parabolicBall p R ↔ p ∈ parabolicBall q R := by
  rw [mem, mem, parabolicDistance.comm]

theorem center_mem (hR : 0 < R) : p ∈ parabolicBall p R := by
  simpa using hR

theorem space_dist_lt_of_mem (hq : q ∈ parabolicBall p R) : dist p.2 q.2 < R :=
  lt_of_le_of_lt (parabolicDistance.space_dist_le p q) hq

theorem time_abs_lt_sq_of_mem (hR : 0 ≤ R) (hq : q ∈ parabolicBall p R) :
    |p.1 - q.1| < R ^ 2 := by
  have hsqrt : Real.sqrt |p.1 - q.1| < R :=
    lt_of_le_of_lt (parabolicDistance.sqrt_time_le p q) hq
  calc
    |p.1 - q.1| = (Real.sqrt |p.1 - q.1|) ^ 2 := by
      rw [Real.sq_sqrt (abs_nonneg _)]
    _ < R ^ 2 := (sq_lt_sq₀ (Real.sqrt_nonneg _) hR).2 hsqrt

end parabolicBall

namespace parabolicClosedBall

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X} {R R' : ℝ}

@[simp] theorem mem : q ∈ parabolicClosedBall p R ↔ parabolicDistance p q ≤ R := Iff.rfl

theorem mono (hR : R ≤ R') : parabolicClosedBall p R ⊆ parabolicClosedBall p R' := by
  intro q hq
  exact le_trans hq hR

theorem mem_comm : q ∈ parabolicClosedBall p R ↔ p ∈ parabolicClosedBall q R := by
  rw [mem, mem, parabolicDistance.comm]

theorem center_mem (hR : 0 ≤ R) : p ∈ parabolicClosedBall p R := by
  simpa using hR

theorem space_dist_le_of_mem (hq : q ∈ parabolicClosedBall p R) : dist p.2 q.2 ≤ R :=
  parabolicDistance.space_dist_le_of_le hq

theorem time_abs_le_sq_of_mem (hR : 0 ≤ R) (hq : q ∈ parabolicClosedBall p R) :
    |p.1 - q.1| ≤ R ^ 2 :=
  parabolicDistance.time_abs_le_sq_of_le hR hq

end parabolicClosedBall

/-- Parabolic Holder control with exponent `α` and constant `C` on a set of time-space points. -/
def ParabolicHolderWith {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (C α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
    ‖u p - u q‖ ≤ C * (parabolicDistance p q) ^ α

/-- A function is parabolic Holder on `s` when it satisfies the Holder estimate with some
nonnegative constant. -/
def ParabolicHolderOn {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ C ≥ 0, ParabolicHolderWith C α u s

namespace ParabolicHolderWith

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {C C₁ C₂ α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem mono_set (h : ParabolicHolderWith C α u s) (hst : t ⊆ s) :
    ParabolicHolderWith C α u t := by
  intro p hp q hq
  exact h (hst hp) (hst hq)

theorem const (c : E) (hC : 0 ≤ C) :
    ParabolicHolderWith C α (fun _ : ℝ × X => c) s := by
  intro p _hp q _hq
  have hpow : 0 ≤ (parabolicDistance p q) ^ α :=
    Real.rpow_nonneg (parabolicDistance.nonneg p q) α
  simpa using mul_nonneg hC hpow

theorem add (hu : ParabolicHolderWith C₁ α u s) (hv : ParabolicHolderWith C₂ α v s) :
    ParabolicHolderWith (C₁ + C₂) α (fun z => u z + v z) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsub : (u p + v p) - (u q + v q) = (u p - u q) + (v p - v q) := by
    abel
  calc
    ‖(u p + v p) - (u q + v q)‖
        = ‖(u p - u q) + (v p - v q)‖ := by rw [hsub]
    _ ≤ ‖u p - u q‖ + ‖v p - v q‖ := norm_add_le _ _
    _ ≤ C₁ * dα + C₂ * dα := add_le_add (hu hp hq) (hv hp hq)
    _ = (C₁ + C₂) * dα := by ring

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicHolderWith C α u s) :
    ParabolicHolderWith (‖c‖ * C) α (fun z => c • u z) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsub : c • u p - c • u q = c • (u p - u q) := by
    rw [smul_sub]
  calc
    ‖c • u p - c • u q‖ = ‖c • (u p - u q)‖ := by rw [hsub]
    _ = ‖c‖ * ‖u p - u q‖ := norm_smul c (u p - u q)
    _ ≤ ‖c‖ * (C * dα) := mul_le_mul_of_nonneg_left (hu hp hq) (norm_nonneg c)
    _ = (‖c‖ * C) * dα := by ring

end ParabolicHolderWith

namespace ParabolicHolderOn

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem mono_set (h : ParabolicHolderOn α u s) (hst : t ⊆ s) :
    ParabolicHolderOn α u t := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.mono_set hst⟩

theorem const (c : E) : ParabolicHolderOn α (fun _ : ℝ × X => c) s :=
  ⟨0, le_rfl, ParabolicHolderWith.const c le_rfl⟩

theorem add (hu : ParabolicHolderOn α u s) (hv : ParabolicHolderOn α v s) :
    ParabolicHolderOn α (fun z => u z + v z) s := by
  rcases hu with ⟨C₁, hC₁, hCu⟩
  rcases hv with ⟨C₂, hC₂, hCv⟩
  exact ⟨C₁ + C₂, add_nonneg hC₁ hC₂, hCu.add hCv⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => c • u z) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, hCu.smul c⟩

end ParabolicHolderOn

end AnalyticPDE
end RicciFlow

