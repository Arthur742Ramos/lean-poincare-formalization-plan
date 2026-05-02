module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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

@[simp] theorem same_time (t : ℝ) (x y : X) :
    parabolicDistance (t, x) (t, y) = dist x y := by
  rw [parabolicDistance, sub_self, abs_zero, Real.sqrt_zero]
  exact max_eq_right (dist_nonneg)

@[simp] theorem same_space (t τ : ℝ) (x : X) :
    parabolicDistance (t, x) (τ, x) = Real.sqrt |t - τ| := by
  rw [parabolicDistance, dist_self]
  exact max_eq_left (Real.sqrt_nonneg _)

theorem same_space_rpow (t τ : ℝ) (x : X) (α : ℝ) :
    (parabolicDistance (t, x) (τ, x)) ^ α = |t - τ| ^ (α / 2) := by
  rw [same_space, Real.rpow_div_two_eq_sqrt α (abs_nonneg _)]

theorem continuous_fixed_left (p : ℝ × X) : Continuous fun q : ℝ × X =>
    parabolicDistance p q := by
  unfold parabolicDistance
  exact ((continuous_const.sub continuous_fst).abs.sqrt).max
    (continuous_const.dist continuous_snd)

theorem continuous_fixed_right (q : ℝ × X) : Continuous fun p : ℝ × X =>
    parabolicDistance p q := by
  unfold parabolicDistance
  exact ((continuous_fst.sub continuous_const).abs.sqrt).max
    (continuous_snd.dist continuous_const)

theorem continuous : Continuous fun pq : (ℝ × X) × (ℝ × X) =>
    parabolicDistance pq.1 pq.2 := by
  unfold parabolicDistance
  exact ((continuous_fst.fst.sub continuous_snd.fst).abs.sqrt).max
    (continuous_fst.snd.dist continuous_snd.snd)

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

/-- Small product-metric distance implies small parabolic distance, after shrinking the product
radius quadratically in the time direction. -/
theorem lt_of_prod_dist_lt {R δ : ℝ} (hδ_space : δ ≤ R) (hδ_time : δ ≤ R ^ 2)
    (hR : 0 < R) (h : dist p q < δ) : parabolicDistance p q < R := by
  have htime_dist : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have htime_abs : |p.1 - q.1| < R ^ 2 := by
    have hlt : dist p.1 q.1 < R ^ 2 :=
      lt_of_le_of_lt htime_dist (lt_of_lt_of_le h hδ_time)
    simpa [Real.dist_eq] using hlt
  have hsqrt : Real.sqrt |p.1 - q.1| < R := by
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) hR.le).1 (by
      rwa [Real.sq_sqrt (abs_nonneg _)])
  have hspace_dist : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hspace : dist p.2 q.2 < R :=
    lt_of_le_of_lt hspace_dist (lt_of_lt_of_le h hδ_space)
  exact max_lt hsqrt hspace

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

/-- Product parabolic cylinder centered at a time-space point, with independent time and spatial
radii.  The isotropic parabolic cylinder uses `timeRadius = R ^ 2` and `spaceRadius = R`. -/
def parabolicCylinder {X : Type*} [PseudoMetricSpace X] (p : ℝ × X)
    (timeRadius spaceRadius : ℝ) : Set (ℝ × X) :=
  {q | |p.1 - q.1| < timeRadius ∧ dist p.2 q.2 < spaceRadius}

/-- Closed product parabolic cylinder centered at a time-space point, with independent time and
spatial radii. -/
def parabolicClosedCylinder {X : Type*} [PseudoMetricSpace X] (p : ℝ × X)
    (timeRadius spaceRadius : ℝ) : Set (ℝ × X) :=
  {q | |p.1 - q.1| ≤ timeRadius ∧ dist p.2 q.2 ≤ spaceRadius}

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

/-- A parabolic ball is contained in the product cylinder with time radius `R^2` and spatial
radius `R`. -/
theorem subset_cylinder (hR : 0 ≤ R) :
    parabolicBall p R ⊆ parabolicCylinder p (R ^ 2) R := by
  intro q hq
  exact ⟨time_abs_lt_sq_of_mem hR hq, space_dist_lt_of_mem hq⟩

theorem isOpen (p : ℝ × X) (R : ℝ) : IsOpen (parabolicBall p R) := by
  simpa [parabolicBall] using
    (parabolicDistance.continuous_fixed_left p).isOpen_preimage (Iio R) isOpen_Iio

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

/-- A closed parabolic ball is contained in the closed product cylinder with time radius `R^2`
and spatial radius `R`. -/
theorem subset_closedCylinder (hR : 0 ≤ R) :
    parabolicClosedBall p R ⊆ parabolicClosedCylinder p (R ^ 2) R := by
  intro q hq
  exact ⟨time_abs_le_sq_of_mem hR hq, space_dist_le_of_mem hq⟩

theorem isClosed (p : ℝ × X) (R : ℝ) : IsClosed (parabolicClosedBall p R) := by
  simpa [parabolicClosedBall] using
    isClosed_Iic.preimage (parabolicDistance.continuous_fixed_left p)

end parabolicClosedBall

namespace parabolicCylinder

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X}
variable {timeRadius timeRadius' spaceRadius spaceRadius' R : ℝ}

@[simp] theorem mem :
    q ∈ parabolicCylinder p timeRadius spaceRadius ↔
      |p.1 - q.1| < timeRadius ∧ dist p.2 q.2 < spaceRadius :=
  Iff.rfl

theorem mono (ht : timeRadius ≤ timeRadius') (hs : spaceRadius ≤ spaceRadius') :
    parabolicCylinder p timeRadius spaceRadius ⊆
      parabolicCylinder p timeRadius' spaceRadius' := by
  intro q hq
  exact ⟨lt_of_lt_of_le hq.1 ht, lt_of_lt_of_le hq.2 hs⟩

theorem mem_comm :
    q ∈ parabolicCylinder p timeRadius spaceRadius ↔
      p ∈ parabolicCylinder q timeRadius spaceRadius := by
  constructor
  · intro hq
    exact ⟨by simpa [abs_sub_comm] using hq.1, by simpa [dist_comm] using hq.2⟩
  · intro hp
    exact ⟨by simpa [abs_sub_comm] using hp.1, by simpa [dist_comm] using hp.2⟩

theorem center_mem (ht : 0 < timeRadius) (hs : 0 < spaceRadius) :
    p ∈ parabolicCylinder p timeRadius spaceRadius := by
  simp [parabolicCylinder, ht, hs]

theorem time_abs_lt_of_mem (hq : q ∈ parabolicCylinder p timeRadius spaceRadius) :
    |p.1 - q.1| < timeRadius :=
  hq.1

theorem space_dist_lt_of_mem (hq : q ∈ parabolicCylinder p timeRadius spaceRadius) :
    dist p.2 q.2 < spaceRadius :=
  hq.2

/-- A product parabolic cylinder whose time radius is at most `R^2` and spatial radius is at most
`R` is contained in the parabolic ball of radius `R`. -/
theorem subset_ball_of_le_sq (hR : 0 < R) (ht : timeRadius ≤ R ^ 2)
    (hs : spaceRadius ≤ R) :
    parabolicCylinder p timeRadius spaceRadius ⊆ parabolicBall p R := by
  intro q hq
  change max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) < R
  exact max_lt ((Real.sqrt_lt' hR).2 (lt_of_lt_of_le hq.1 ht))
    (lt_of_lt_of_le hq.2 hs)

/-- The standard product cylinder with time radius `R^2` and spatial radius `R` is exactly small
enough to sit in the parabolic ball of radius `R`. -/
theorem subset_ball (hR : 0 < R) :
    parabolicCylinder p (R ^ 2) R ⊆ parabolicBall p R :=
  subset_ball_of_le_sq hR le_rfl le_rfl

end parabolicCylinder

namespace parabolicClosedCylinder

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X}
variable {timeRadius timeRadius' spaceRadius spaceRadius' R : ℝ}

@[simp] theorem mem :
    q ∈ parabolicClosedCylinder p timeRadius spaceRadius ↔
      |p.1 - q.1| ≤ timeRadius ∧ dist p.2 q.2 ≤ spaceRadius :=
  Iff.rfl

theorem mono (ht : timeRadius ≤ timeRadius') (hs : spaceRadius ≤ spaceRadius') :
    parabolicClosedCylinder p timeRadius spaceRadius ⊆
      parabolicClosedCylinder p timeRadius' spaceRadius' := by
  intro q hq
  exact ⟨le_trans hq.1 ht, le_trans hq.2 hs⟩

theorem mem_comm :
    q ∈ parabolicClosedCylinder p timeRadius spaceRadius ↔
      p ∈ parabolicClosedCylinder q timeRadius spaceRadius := by
  constructor
  · intro hq
    exact ⟨by simpa [abs_sub_comm] using hq.1, by simpa [dist_comm] using hq.2⟩
  · intro hp
    exact ⟨by simpa [abs_sub_comm] using hp.1, by simpa [dist_comm] using hp.2⟩

theorem center_mem (ht : 0 ≤ timeRadius) (hs : 0 ≤ spaceRadius) :
    p ∈ parabolicClosedCylinder p timeRadius spaceRadius := by
  simp [parabolicClosedCylinder, ht, hs]

theorem time_abs_le_of_mem (hq : q ∈ parabolicClosedCylinder p timeRadius spaceRadius) :
    |p.1 - q.1| ≤ timeRadius :=
  hq.1

theorem space_dist_le_of_mem (hq : q ∈ parabolicClosedCylinder p timeRadius spaceRadius) :
    dist p.2 q.2 ≤ spaceRadius :=
  hq.2

/-- A closed product parabolic cylinder whose time radius is at most `R^2` and spatial radius is at
most `R` is contained in the closed parabolic ball of radius `R`. -/
theorem subset_closedBall_of_le_sq (hR : 0 ≤ R) (ht : timeRadius ≤ R ^ 2)
    (hs : spaceRadius ≤ R) :
    parabolicClosedCylinder p timeRadius spaceRadius ⊆ parabolicClosedBall p R := by
  intro q hq
  change max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) ≤ R
  exact max_le ((Real.sqrt_le_left hR).2 (le_trans hq.1 ht)) (le_trans hq.2 hs)

/-- The standard closed product cylinder with time radius `R^2` and spatial radius `R` is exactly
small enough to sit in the closed parabolic ball of radius `R`. -/
theorem subset_closedBall (hR : 0 ≤ R) :
    parabolicClosedCylinder p (R ^ 2) R ⊆ parabolicClosedBall p R :=
  subset_closedBall_of_le_sq hR le_rfl le_rfl

end parabolicClosedCylinder

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

/-- Uniform sup-norm control on a time-space set.  This is the `C^0` part of the parabolic
`C^{0,α}` norm package. -/
def ParabolicBoundedWith {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (B : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∀ ⦃p : ℝ × X⦄, p ∈ s → ‖u p‖ ≤ B

/-- Parabolic `C^{0,α}` control with separately named sup and Holder constants. -/
def ParabolicC0AlphaWith {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (B H α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ParabolicBoundedWith B u s ∧ ParabolicHolderWith H α u s

/-- A function belongs to the parabolic `C^{0,α}` class on `s` when it has finite sup control and
finite parabolic Holder control. -/
def ParabolicC0AlphaOn {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ B ≥ 0, ∃ H ≥ 0, ParabolicC0AlphaWith B H α u s

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

/-- Restricting a parabolic Holder estimate to a fixed spatial point gives the weighted
time-slice estimate. -/
theorem time_slice (h : ParabolicHolderWith C α u s) {t τ : ℝ} {x : X}
    (ht : (t, x) ∈ s) (hτ : (τ, x) ∈ s) :
    ‖u (t, x) - u (τ, x)‖ ≤ C * (Real.sqrt |t - τ|) ^ α := by
  simpa using h ht hτ

/-- On fixed spatial points, parabolic `α`-Holder control is ordinary time Holder control with
exponent `α / 2`. -/
theorem time_slice_half_exponent (h : ParabolicHolderWith C α u s) {t τ : ℝ} {x : X}
    (ht : (t, x) ∈ s) (hτ : (τ, x) ∈ s) :
    ‖u (t, x) - u (τ, x)‖ ≤ C * |t - τ| ^ (α / 2) := by
  rw [Real.rpow_div_two_eq_sqrt α (abs_nonneg (t - τ))]
  exact h.time_slice ht hτ

/-- Restricting a parabolic Holder estimate to a fixed time gives the ordinary spatial Holder
estimate. -/
theorem space_slice (h : ParabolicHolderWith C α u s) {t : ℝ} {x y : X}
    (hx : (t, x) ∈ s) (hy : (t, y) ∈ s) :
    ‖u (t, x) - u (t, y)‖ ≤ C * (dist x y) ^ α := by
  simpa using h hx hy

/-- Positive-exponent parabolic Holder control implies continuity on the controlled set. -/
theorem continuousOn (h : ParabolicHolderWith C α u s) (hα : 0 < α) : ContinuousOn u s := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (f := fun q : ℝ × X => ‖u q - u p‖)
    (g := fun q : ℝ × X => C * (parabolicDistance q p) ^ α) ?_ ?_ ?_
  · filter_upwards with q
    exact norm_nonneg _
  · filter_upwards [eventually_mem_nhdsWithin] with q hq
    exact h hq hp
  · have hd : Filter.Tendsto (fun q : ℝ × X => parabolicDistance q p) (nhdsWithin p s)
        (nhds 0) := by
      have hd₀ : Filter.Tendsto (fun q : ℝ × X => parabolicDistance q p) (nhds p)
          (nhds 0) := by
        have hd₀' : ContinuousAt (fun q : ℝ × X => parabolicDistance q p) p :=
          (parabolicDistance.continuous_fixed_right p).continuousAt
        rw [← parabolicDistance.self p]
        exact hd₀'
      exact hd₀.mono_left nhdsWithin_le_nhds
    have hpow : Filter.Tendsto (fun q : ℝ × X => (parabolicDistance q p) ^ α)
        (nhdsWithin p s) (nhds (0 ^ α)) :=
      Filter.Tendsto.rpow_const hd (Or.inr hα.le)
    simpa [Real.zero_rpow hα.ne'] using tendsto_const_nhds.mul hpow

/-- Positive-exponent parabolic Holder control gives uniform continuity on the controlled
time-space set. -/
theorem uniformContinuousOn (h : ParabolicHolderWith C α u s) (hα : 0 < α) :
    UniformContinuousOn u s := by
  refine Metric.uniformContinuousOn_iff.2 fun ε hε => ?_
  have htend : Filter.Tendsto (fun d : ℝ => C * d ^ α) (nhds 0) (nhds 0) := by
    have hpow : Filter.Tendsto (fun d : ℝ => d ^ α) (nhds 0) (nhds (0 ^ α)) :=
      (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using tendsto_const_nhds.mul hpow
  rcases Metric.tendsto_nhds_nhds.1 htend ε hε with ⟨η, hη, hη_bound⟩
  refine ⟨min η (η ^ 2), lt_min hη (sq_pos_of_pos hη), ?_⟩
  intro p hp q hq hpq
  have hpq_par : parabolicDistance p q < η :=
    parabolicDistance.lt_of_prod_dist_lt (min_le_left _ _) (min_le_right _ _) hη hpq
  have hpd_dist : dist (parabolicDistance p q) 0 < η := by
    simpa [Real.dist_eq, abs_of_nonneg (parabolicDistance.nonneg p q)] using hpq_par
  have hupper_abs : dist (C * (parabolicDistance p q) ^ α) 0 < ε :=
    hη_bound hpd_dist
  have hupper : C * (parabolicDistance p q) ^ α < ε := by
    have habs : |C * (parabolicDistance p q) ^ α| < ε := by
      simpa [Real.dist_eq, sub_zero] using hupper_abs
    exact lt_of_le_of_lt (le_abs_self _) habs
  calc
    dist (u p) (u q) = ‖u p - u q‖ := dist_eq_norm _ _
    _ ≤ C * (parabolicDistance p q) ^ α := h hp hq
    _ < ε := hupper

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

/-- A parabolic Holder function has a weighted Holder estimate on every time slice through a
fixed spatial point. -/
theorem time_slice (h : ParabolicHolderOn α u s) :
    ∃ C ≥ 0, ∀ {t τ : ℝ} {x : X}, (t, x) ∈ s → (τ, x) ∈ s →
      ‖u (t, x) - u (τ, x)‖ ≤ C * (Real.sqrt |t - τ|) ^ α := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, fun {t τ x} ht hτ => hCu.time_slice (t := t) (τ := τ) (x := x) ht hτ⟩

/-- A parabolic Holder function has ordinary time Holder control with exponent `α / 2` on every
time slice through a fixed spatial point. -/
theorem time_slice_half_exponent (h : ParabolicHolderOn α u s) :
    ∃ C ≥ 0, ∀ {t τ : ℝ} {x : X}, (t, x) ∈ s → (τ, x) ∈ s →
      ‖u (t, x) - u (τ, x)‖ ≤ C * |t - τ| ^ (α / 2) := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC,
    fun {t τ x} ht hτ => hCu.time_slice_half_exponent (t := t) (τ := τ) (x := x) ht hτ⟩

/-- A parabolic Holder function has an ordinary Holder estimate on every spatial slice. -/
theorem space_slice (h : ParabolicHolderOn α u s) :
    ∃ C ≥ 0, ∀ {t : ℝ} {x y : X}, (t, x) ∈ s → (t, y) ∈ s →
      ‖u (t, x) - u (t, y)‖ ≤ C * (dist x y) ^ α := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, fun {t x y} hx hy => hCu.space_slice (t := t) (x := x) (y := y) hx hy⟩

/-- Positive-exponent parabolic Holder functions are continuous on their time-space domain. -/
theorem continuousOn (h : ParabolicHolderOn α u s) (hα : 0 < α) : ContinuousOn u s := by
  rcases h with ⟨_C, _hC, hCu⟩
  exact hCu.continuousOn hα

/-- Positive-exponent parabolic Holder functions are uniformly continuous on their time-space
domain. -/
theorem uniformContinuousOn (h : ParabolicHolderOn α u s) (hα : 0 < α) :
    UniformContinuousOn u s := by
  rcases h with ⟨_C, _hC, hCu⟩
  exact hCu.uniformContinuousOn hα

end ParabolicHolderOn

namespace ParabolicBoundedWith

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {B B₁ B₂ : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem mono_set (h : ParabolicBoundedWith B u s) (hst : t ⊆ s) :
    ParabolicBoundedWith B u t := by
  intro p hp
  exact h (hst hp)

theorem const (c : E) (hB : ‖c‖ ≤ B) :
    ParabolicBoundedWith B (fun _ : ℝ × X => c) s := by
  intro _p _hp
  exact hB

theorem add (hu : ParabolicBoundedWith B₁ u s) (hv : ParabolicBoundedWith B₂ v s) :
    ParabolicBoundedWith (B₁ + B₂) (fun z => u z + v z) s := by
  intro p hp
  calc
    ‖u p + v p‖ ≤ ‖u p‖ + ‖v p‖ := norm_add_le _ _
    _ ≤ B₁ + B₂ := add_le_add (hu hp) (hv hp)

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith (‖c‖ * B) (fun z => c • u z) s := by
  intro p hp
  calc
    ‖c • u p‖ = ‖c‖ * ‖u p‖ := norm_smul c (u p)
    _ ≤ ‖c‖ * B := mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg c)

end ParabolicBoundedWith

namespace ParabolicC0AlphaWith

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {B B₁ B₂ H H₁ H₂ α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem bounded (h : ParabolicC0AlphaWith B H α u s) : ParabolicBoundedWith B u s :=
  h.1

theorem holder (h : ParabolicC0AlphaWith B H α u s) : ParabolicHolderWith H α u s :=
  h.2

theorem mono_set (h : ParabolicC0AlphaWith B H α u s) (hst : t ⊆ s) :
    ParabolicC0AlphaWith B H α u t :=
  ⟨h.bounded.mono_set hst, h.holder.mono_set hst⟩

theorem const (c : E) (hB : ‖c‖ ≤ B) (hH : 0 ≤ H) :
    ParabolicC0AlphaWith B H α (fun _ : ℝ × X => c) s :=
  ⟨ParabolicBoundedWith.const c hB, ParabolicHolderWith.const c hH⟩

theorem add (hu : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s) :
    ParabolicC0AlphaWith (B₁ + B₂) (H₁ + H₂) α (fun z => u z + v z) s :=
  ⟨hu.bounded.add hv.bounded, hu.holder.add hv.holder⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith (‖c‖ * B) (‖c‖ * H) α (fun z => c • u z) s :=
  ⟨hu.bounded.smul c, hu.holder.smul c⟩

/-- The Holder component of positive-exponent parabolic `C^{0,α}` control gives continuity. -/
theorem continuousOn (h : ParabolicC0AlphaWith B H α u s) (hα : 0 < α) : ContinuousOn u s :=
  h.holder.continuousOn hα

/-- Positive-exponent parabolic `C^{0,α}` control gives uniform continuity. -/
theorem uniformContinuousOn (h : ParabolicC0AlphaWith B H α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.holder.uniformContinuousOn hα

end ParabolicC0AlphaWith

namespace ParabolicC0AlphaOn

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem mono_set (h : ParabolicC0AlphaOn α u s) (hst : t ⊆ s) :
    ParabolicC0AlphaOn α u t := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH, hBH.mono_set hst⟩

theorem boundedOn (h : ParabolicC0AlphaOn α u s) :
    ∃ B ≥ 0, ParabolicBoundedWith B u s := by
  rcases h with ⟨B, hB, _H, _hH, hBH⟩
  exact ⟨B, hB, hBH.bounded⟩

theorem holderOn (h : ParabolicC0AlphaOn α u s) : ParabolicHolderOn α u s := by
  rcases h with ⟨_B, _hB, H, hH, hBH⟩
  exact ⟨H, hH, hBH.holder⟩

theorem const (c : E) : ParabolicC0AlphaOn α (fun _ : ℝ × X => c) s :=
  ⟨‖c‖, norm_nonneg c, 0, le_rfl, ParabolicC0AlphaWith.const c le_rfl le_rfl⟩

theorem add (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => u z + v z) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ + B₂, add_nonneg hB₁ hB₂, H₁ + H₂, add_nonneg hH₁ hH₂, hBH₁.add hBH₂⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => c • u z) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB,
    ‖c‖ * H, mul_nonneg (norm_nonneg c) hH, hBH.smul c⟩

theorem time_slice_half_exponent (h : ParabolicC0AlphaOn α u s) :
    ∃ C ≥ 0, ∀ {t τ : ℝ} {x : X}, (t, x) ∈ s → (τ, x) ∈ s →
      ‖u (t, x) - u (τ, x)‖ ≤ C * |t - τ| ^ (α / 2) :=
  h.holderOn.time_slice_half_exponent

theorem space_slice (h : ParabolicC0AlphaOn α u s) :
    ∃ C ≥ 0, ∀ {t : ℝ} {x y : X}, (t, x) ∈ s → (t, y) ∈ s →
      ‖u (t, x) - u (t, y)‖ ≤ C * (dist x y) ^ α :=
  h.holderOn.space_slice

/-- Positive-exponent parabolic `C^{0,α}` functions are continuous on their time-space domain. -/
theorem continuousOn (h : ParabolicC0AlphaOn α u s) (hα : 0 < α) : ContinuousOn u s :=
  h.holderOn.continuousOn hα

/-- Positive-exponent parabolic `C^{0,α}` functions are uniformly continuous on their time-space
domain. -/
theorem uniformContinuousOn (h : ParabolicC0AlphaOn α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.holderOn.uniformContinuousOn hα

end ParabolicC0AlphaOn

end AnalyticPDE
end RicciFlow

