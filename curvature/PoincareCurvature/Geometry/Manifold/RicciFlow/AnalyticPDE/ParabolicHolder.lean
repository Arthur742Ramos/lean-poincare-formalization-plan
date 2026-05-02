module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.Topology.MetricSpace.ProperSpace

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
open scoped Topology NNReal BigOperators

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

/-- The parabolic distance satisfies the triangle inequality. -/
theorem triangle (p q r : ℝ × X) :
    parabolicDistance p r ≤ parabolicDistance p q + parabolicDistance q r := by
  change max (Real.sqrt |p.1 - r.1|) (dist p.2 r.2) ≤
    parabolicDistance p q + parabolicDistance q r
  have htime_abs : |p.1 - r.1| ≤ |p.1 - q.1| + |q.1 - r.1| := by
    calc
      |p.1 - r.1| = |(p.1 - q.1) + (q.1 - r.1)| := by ring_nf
      _ ≤ |p.1 - q.1| + |q.1 - r.1| := abs_add_le _ _
  have htime_sqrt :
      Real.sqrt |p.1 - r.1| ≤ Real.sqrt |p.1 - q.1| + Real.sqrt |q.1 - r.1| := by
    rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [htime_abs, Real.sq_sqrt (abs_nonneg (p.1 - q.1)),
      Real.sq_sqrt (abs_nonneg (q.1 - r.1)),
      Real.sqrt_nonneg |p.1 - q.1|, Real.sqrt_nonneg |q.1 - r.1|]
  have htime : Real.sqrt |p.1 - r.1| ≤ parabolicDistance p q + parabolicDistance q r :=
    htime_sqrt.trans (add_le_add (sqrt_time_le p q) (sqrt_time_le q r))
  have hspace : dist p.2 r.2 ≤ parabolicDistance p q + parabolicDistance q r :=
    (dist_triangle p.2 q.2 r.2).trans
      (add_le_add (space_dist_le p q) (space_dist_le q r))
  exact max_le htime hspace

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

/-- A small closed product-metric distance implies a small closed parabolic-distance bound, after
shrinking the product radius quadratically in the time direction. -/
theorem le_of_prod_dist_le {R δ : ℝ} (hδ_space : δ ≤ R) (hδ_time : δ ≤ R ^ 2)
    (hR : 0 ≤ R) (h : dist p q ≤ δ) : parabolicDistance p q ≤ R := by
  have htime_dist : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have htime_abs : |p.1 - q.1| ≤ R ^ 2 := by
    have hle : dist p.1 q.1 ≤ R ^ 2 :=
      htime_dist.trans (h.trans hδ_time)
    simpa [Real.dist_eq] using hle
  have hsqrt : Real.sqrt |p.1 - q.1| ≤ R := by
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hR).1 (by
      rwa [Real.sq_sqrt (abs_nonneg _)])
  have hspace_dist : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hspace : dist p.2 q.2 ≤ R :=
    hspace_dist.trans (h.trans hδ_space)
  exact max_le hsqrt hspace

/-- A small closed product-metric distance implies a small open parabolic-distance bound, after
strictly shrinking the product radius quadratically in the time direction. -/
theorem lt_of_prod_dist_le {R δ : ℝ} (hδ_space : δ < R) (hδ_time : δ < R ^ 2)
    (hR : 0 < R) (h : dist p q ≤ δ) : parabolicDistance p q < R := by
  have htime_dist : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have htime_abs : |p.1 - q.1| < R ^ 2 := by
    have hlt : dist p.1 q.1 < R ^ 2 :=
      lt_of_le_of_lt (htime_dist.trans h) hδ_time
    simpa [Real.dist_eq] using hlt
  have hsqrt : Real.sqrt |p.1 - q.1| < R := by
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) hR.le).1 (by
      rwa [Real.sq_sqrt (abs_nonneg _)])
  have hspace_dist : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hspace : dist p.2 q.2 < R :=
    lt_of_le_of_lt (hspace_dist.trans h) hδ_space
  exact max_lt hsqrt hspace

/-- A small parabolic distance bound gives a small ordinary product-metric bound once the time
radius has been squared. -/
theorem prod_dist_lt_of_lt {R ε : ℝ} (hR_space : R ≤ ε) (hR_time : R ^ 2 ≤ ε)
    (h : parabolicDistance p q < R) : dist p q < ε := by
  have hRpos : 0 < R := lt_of_le_of_lt (nonneg p q) h
  have hsqrt : Real.sqrt |p.1 - q.1| < R :=
    lt_of_le_of_lt (sqrt_time_le p q) h
  have htime_abs : |p.1 - q.1| < R ^ 2 := by
    calc
      |p.1 - q.1| = (Real.sqrt |p.1 - q.1|) ^ 2 := by
        rw [Real.sq_sqrt (abs_nonneg _)]
      _ < R ^ 2 := (sq_lt_sq₀ (Real.sqrt_nonneg _) hRpos.le).2 hsqrt
  have htime : dist p.1 q.1 < ε := by
    simpa [Real.dist_eq] using lt_of_lt_of_le htime_abs hR_time
  have hspace : dist p.2 q.2 < ε :=
    lt_of_lt_of_le (lt_of_le_of_lt (space_dist_le p q) h) hR_space
  rw [Prod.dist_eq]
  exact max_lt htime hspace

/-- A parabolic closed-ball bound gives an ordinary product-metric closed-ball bound once the
time radius has been squared. -/
theorem prod_dist_le_of_le {R ε : ℝ} (hR_space : R ≤ ε) (hR_time : R ^ 2 ≤ ε)
    (h : parabolicDistance p q ≤ R) : dist p q ≤ ε := by
  have hR : 0 ≤ R := (nonneg p q).trans h
  have htime_abs : |p.1 - q.1| ≤ R ^ 2 := time_abs_le_sq_of_le hR h
  have htime : dist p.1 q.1 ≤ ε := by
    simpa [Real.dist_eq] using le_trans htime_abs hR_time
  have hspace : dist p.2 q.2 ≤ ε :=
    le_trans (space_dist_le_of_le h) hR_space
  rw [Prod.dist_eq]
  exact max_le htime hspace

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

theorem subset_metric_ball {ε : ℝ} (hR_space : R ≤ ε) (hR_time : R ^ 2 ≤ ε) :
    parabolicBall p R ⊆ Metric.ball p ε := by
  intro q hq
  rw [Metric.mem_ball, dist_comm]
  exact parabolicDistance.prod_dist_lt_of_lt hR_space hR_time hq

theorem metric_closedBall_subset {δ : ℝ} (hδ_space : δ < R) (hδ_time : δ < R ^ 2)
    (hR : 0 < R) :
    Metric.closedBall p δ ⊆ parabolicBall p R := by
  intro q hq
  rw [Metric.mem_closedBall, dist_comm] at hq
  exact parabolicDistance.lt_of_prod_dist_le hδ_space hδ_time hR hq

theorem isOpen (p : ℝ × X) (R : ℝ) : IsOpen (parabolicBall p R) := by
  simpa [parabolicBall] using
    (parabolicDistance.continuous_fixed_left p).isOpen_preimage (Iio R) isOpen_Iio

theorem mem_nhds (hR : 0 < R) : parabolicBall p R ∈ 𝓝 p :=
  (isOpen p R).mem_nhds (center_mem hR)

/-- Parabolic balls form a local base for the ordinary product topology. -/
theorem exists_subset_of_mem_nhds {s : Set (ℝ × X)} (hs : s ∈ 𝓝 p) :
    ∃ R > 0, parabolicBall p R ⊆ s := by
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, hε, hεs⟩
  let R : ℝ := min (ε / 2) 1
  have hRpos : 0 < R := lt_min (half_pos hε) zero_lt_one
  have hR_space : R ≤ ε := by
    unfold R
    exact (min_le_left _ _).trans (by linarith)
  have hR_time : R ^ 2 ≤ ε := by
    have hRle1 : R ≤ 1 := by
      unfold R
      exact min_le_right _ _
    have hRsq_le : R ^ 2 ≤ R := by
      nlinarith [hRpos.le, hRle1]
    exact hRsq_le.trans hR_space
  exact ⟨R, hRpos, (subset_metric_ball (p := p) hR_space hR_time).trans hεs⟩

theorem exists_finite_cover_of_isCompact {K : Set (ℝ × X)} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R) :
    ∃ N ⊆ K, N.Finite ∧ K ⊆ ⋃ y ∈ N, parabolicBall y R := by
  let δ : ℝ := min R (R ^ 2) / 2
  have hδpos : 0 < δ := by
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    exact half_pos (lt_min hR hR2)
  have hδ_space : δ < R := by
    unfold δ
    exact (half_lt_self (lt_min hR (sq_pos_of_pos hR))).trans_le (min_le_left _ _)
  have hδ_time : δ < R ^ 2 := by
    unfold δ
    exact (half_lt_self (lt_min hR (sq_pos_of_pos hR))).trans_le (min_le_right _ _)
  let ε : ℝ≥0 := ⟨δ, hδpos.le⟩
  have hεne : ε ≠ 0 := by
    intro hε
    have hδ0 : δ = 0 := by
      simpa [ε] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hε
    linarith
  rcases Metric.exists_finite_isCover_of_isCompact (s := K) (ε := ε) hεne hK with
    ⟨N, hNK, hNfinite, hcover⟩
  refine ⟨N, hNK, hNfinite, ?_⟩
  have hcover' : K ⊆ ⋃ y ∈ N, Metric.closedBall y (ε : ℝ) :=
    hcover.subset_iUnion_closedBall
  intro z hz
  rcases mem_iUnion.1 (hcover' hz) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hzball⟩
  refine mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hyN, ?_⟩⟩
  exact (metric_closedBall_subset (p := y) (R := R) (δ := (ε : ℝ))
    (by simpa [ε] using hδ_space) (by simpa [ε] using hδ_time) hR) hzball

/-- A compact set covered by an open set has a finite parabolic-ball cover whose balls remain
inside that open set.  The radii may depend on the center. -/
theorem exists_finset_cover_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Finset (ℝ × X),
      (∀ x ∈ N, x ∈ K) ∧
      ∃ R : (ℝ × X) → ℝ,
        (∀ x ∈ N, 0 < R x) ∧
        (∀ x ∈ N, parabolicBall x (R x) ⊆ U) ∧
        K ⊆ ⋃ x ∈ N, parabolicBall x (R x) := by
  classical
  have hlocal : ∀ x ∈ K, ∃ R > 0, parabolicBall x R ⊆ U := by
    intro x hx
    exact exists_subset_of_mem_nhds (hUopen.mem_nhds (hKU hx))
  let R : ℝ × X → ℝ :=
    fun x => if hx : x ∈ K then Classical.choose (hlocal x hx) else 1
  have hRpos : ∀ x ∈ K, 0 < R x := by
    intro x hx
    dsimp [R]
    rw [dif_pos hx]
    exact (Classical.choose_spec (hlocal x hx)).1
  have hRsubset : ∀ x ∈ K, parabolicBall x (R x) ⊆ U := by
    intro x hx
    dsimp [R]
    rw [dif_pos hx]
    exact (Classical.choose_spec (hlocal x hx)).2
  rcases hK.elim_nhds_subcover (fun x => parabolicBall x (R x))
      (fun x hx => mem_nhds (p := x) (R := R x) (hRpos x hx)) with
    ⟨N, hNK, hcover⟩
  refine ⟨N, hNK, R, ?_, ?_, hcover⟩
  · intro x hx
    exact hRpos x (hNK x hx)
  · intro x hx
    exact hRsubset x (hNK x hx)

/-- A compact set inside an open set has a finite open parabolic-ball cover whose matching
closed parabolic balls remain inside that open set. -/
theorem exists_finset_cover_closedBall_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Finset (ℝ × X),
      (∀ x ∈ N, x ∈ K) ∧
      ∃ R : (ℝ × X) → ℝ,
        (∀ x ∈ N, 0 < R x) ∧
        (∀ x ∈ N, parabolicClosedBall x (R x) ⊆ U) ∧
        K ⊆ ⋃ x ∈ N, parabolicBall x (R x) := by
  classical
  have hlocal : ∀ x ∈ K, ∃ R > 0, parabolicBall x R ⊆ U := by
    intro x hx
    exact exists_subset_of_mem_nhds (hUopen.mem_nhds (hKU hx))
  let R : ℝ × X → ℝ :=
    fun x => if hx : x ∈ K then Classical.choose (hlocal x hx) / 2 else 1
  have hRpos : ∀ x ∈ K, 0 < R x := by
    intro x hx
    dsimp [R]
    rw [dif_pos hx]
    exact half_pos (Classical.choose_spec (hlocal x hx)).1
  have hclosed_subset : ∀ x ∈ K, parabolicClosedBall x (R x) ⊆ U := by
    intro x hx
    dsimp [R]
    rw [dif_pos hx]
    intro q hq
    exact (Classical.choose_spec (hlocal x hx)).2
      (lt_of_le_of_lt hq (half_lt_self (Classical.choose_spec (hlocal x hx)).1))
  rcases hK.elim_nhds_subcover (fun x => parabolicBall x (R x))
      (fun x hx => mem_nhds (p := x) (R := R x) (hRpos x hx)) with
    ⟨N, hNK, hcover⟩
  refine ⟨N, hNK, R, ?_, ?_, hcover⟩
  · intro x hx
    exact hRpos x (hNK x hx)
  · intro x hx
    exact hclosed_subset x (hNK x hx)

end parabolicBall

namespace parabolicClosedBall

variable {X : Type*} [PseudoMetricSpace X] {p q : ℝ × X} {R R' : ℝ}

@[simp] theorem mem : q ∈ parabolicClosedBall p R ↔ parabolicDistance p q ≤ R := Iff.rfl

theorem mono (hR : R ≤ R') : parabolicClosedBall p R ⊆ parabolicClosedBall p R' := by
  intro q hq
  exact le_trans hq hR

theorem subset_ball (hR : R < R') : parabolicClosedBall p R ⊆ parabolicBall p R' := by
  intro q hq
  exact lt_of_le_of_lt hq hR

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

theorem subset_metric_closedBall {ε : ℝ} (hR_space : R ≤ ε) (hR_time : R ^ 2 ≤ ε) :
    parabolicClosedBall p R ⊆ Metric.closedBall p ε := by
  intro q hq
  rw [Metric.mem_closedBall, dist_comm]
  exact parabolicDistance.prod_dist_le_of_le hR_space hR_time hq

theorem metric_closedBall_subset {δ : ℝ} (hδ_space : δ ≤ R) (hδ_time : δ ≤ R ^ 2)
    (hR : 0 ≤ R) :
    Metric.closedBall p δ ⊆ parabolicClosedBall p R := by
  intro q hq
  rw [Metric.mem_closedBall, dist_comm] at hq
  exact parabolicDistance.le_of_prod_dist_le hδ_space hδ_time hR hq

theorem isClosed (p : ℝ × X) (R : ℝ) : IsClosed (parabolicClosedBall p R) := by
  simpa [parabolicClosedBall] using
    isClosed_Iic.preimage (parabolicDistance.continuous_fixed_left p)

theorem isCompact [ProperSpace X] (p : ℝ × X) (R : ℝ) :
    IsCompact (parabolicClosedBall p R) := by
  exact (isCompact_closedBall p (max R (R ^ 2))).of_isClosed_subset (isClosed p R)
    (subset_metric_closedBall (p := p) (R := R) (le_max_left _ _) (le_max_right _ _))

theorem exists_finite_cover_of_isCompact {K : Set (ℝ × X)} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R) :
    ∃ N ⊆ K, N.Finite ∧ K ⊆ ⋃ y ∈ N, parabolicClosedBall y R := by
  let δ : ℝ := min R (R ^ 2) / 2
  have hδpos : 0 < δ := by
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    exact half_pos (lt_min hR hR2)
  have hδ_space : δ ≤ R := by
    unfold δ
    exact (half_le_self (le_of_lt (lt_min hR (sq_pos_of_pos hR)))).trans (min_le_left _ _)
  have hδ_time : δ ≤ R ^ 2 := by
    unfold δ
    exact (half_le_self (le_of_lt (lt_min hR (sq_pos_of_pos hR)))).trans (min_le_right _ _)
  let ε : ℝ≥0 := ⟨δ, hδpos.le⟩
  have hεne : ε ≠ 0 := by
    intro hε
    have hδ0 : δ = 0 := by
      simpa [ε] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hε
    linarith
  rcases Metric.exists_finite_isCover_of_isCompact (s := K) (ε := ε) hεne hK with
    ⟨N, hNK, hNfinite, hcover⟩
  refine ⟨N, hNK, hNfinite, ?_⟩
  have hcover' : K ⊆ ⋃ y ∈ N, Metric.closedBall y (ε : ℝ) :=
    hcover.subset_iUnion_closedBall
  intro z hz
  rcases mem_iUnion.1 (hcover' hz) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hzball⟩
  refine mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hyN, ?_⟩⟩
  exact (metric_closedBall_subset (p := y) (R := R) (δ := (ε : ℝ))
    (by simpa [ε] using hδ_space) (by simpa [ε] using hδ_time) hR.le) hzball

/-- A compact subset of an open set has one positive parabolic closed-ball radius around every
one of its points still contained in that open set. -/
theorem exists_uniform_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ R > 0, ∀ x ∈ K, parabolicClosedBall x R ⊆ U := by
  rcases hK.exists_cthickening_subset_open hUopen hKU with ⟨δ, hδ, hδU⟩
  let R : ℝ := min (δ / 2) 1
  have hRpos : 0 < R := lt_min (half_pos hδ) zero_lt_one
  have hR_space : R ≤ δ := by
    unfold R
    exact (min_le_left _ _).trans (by linarith)
  have hR_time : R ^ 2 ≤ δ := by
    have hRle1 : R ≤ 1 := by
      unfold R
      exact min_le_right _ _
    have hsquare : R ^ 2 ≤ R := by
      nlinarith [hRpos.le, hRle1]
    exact hsquare.trans hR_space
  refine ⟨R, hRpos, ?_⟩
  intro x hx q hq
  have hqmetric : q ∈ Metric.closedBall x δ :=
    (subset_metric_closedBall (p := x) (R := R) (ε := δ) hR_space hR_time) hq
  exact hδU (Metric.mem_cthickening_of_dist_le q x δ K hx
    (Metric.mem_closedBall.1 hqmetric))

theorem pair_parabolicDistance_le {c p q : ℝ × X}
    (hp : p ∈ parabolicClosedBall c R) (hq : q ∈ parabolicClosedBall c R) :
    parabolicDistance p q ≤ 2 * R := by
  calc
    parabolicDistance p q ≤ parabolicDistance p c + parabolicDistance c q :=
      parabolicDistance.triangle p c q
    _ = parabolicDistance c p + parabolicDistance c q := by
      rw [parabolicDistance.comm p c]
    _ ≤ R + R := add_le_add hp hq
    _ = 2 * R := by ring

theorem pair_parabolicDistance_le_one {c p q : ℝ × X}
    (hp : p ∈ parabolicClosedBall c R) (hq : q ∈ parabolicClosedBall c R)
    (hR : 2 * R ≤ 1) :
    parabolicDistance p q ≤ 1 :=
  (pair_parabolicDistance_le hp hq).trans hR

end parabolicClosedBall

namespace parabolicBall

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ × X} {R : ℝ}

theorem closure_subset_closedBall :
    closure (parabolicBall p R) ⊆ parabolicClosedBall p R :=
  closure_minimal subset_closedBall (parabolicClosedBall.isClosed p R)

end parabolicBall

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

theorem subset_closedCylinder :
    parabolicCylinder p timeRadius spaceRadius ⊆
      parabolicClosedCylinder p timeRadius spaceRadius := by
  intro q hq
  exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩

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

theorem isOpen (p : ℝ × X) (timeRadius spaceRadius : ℝ) :
    IsOpen (parabolicCylinder p timeRadius spaceRadius) := by
  simpa [parabolicCylinder] using
    (((continuous_const.sub continuous_fst).abs.isOpen_preimage (Iio timeRadius) isOpen_Iio).inter
      ((continuous_const.dist continuous_snd).isOpen_preimage (Iio spaceRadius) isOpen_Iio))

theorem mem_nhds (ht : 0 < timeRadius) (hs : 0 < spaceRadius) :
    parabolicCylinder p timeRadius spaceRadius ∈ 𝓝 p :=
  (isOpen p timeRadius spaceRadius).mem_nhds (center_mem ht hs)

theorem subset_metric_ball {ε : ℝ} (ht : timeRadius ≤ ε) (hs : spaceRadius ≤ ε) :
    parabolicCylinder p timeRadius spaceRadius ⊆ Metric.ball p ε := by
  intro q hq
  rw [Metric.mem_ball, Prod.dist_eq]
  exact max_lt
    (by simpa [Real.dist_eq, abs_sub_comm] using lt_of_lt_of_le hq.1 ht)
    (by simpa [dist_comm] using lt_of_lt_of_le hq.2 hs)

theorem metric_closedBall_subset {δ : ℝ}
    (ht : δ < timeRadius) (hs : δ < spaceRadius) :
    Metric.closedBall p δ ⊆ parabolicCylinder p timeRadius spaceRadius := by
  intro q hq
  rw [Metric.mem_closedBall, dist_comm, Prod.dist_eq] at hq
  exact ⟨lt_of_le_of_lt (by simpa [Real.dist_eq, abs_sub_comm] using
      (le_max_left (dist p.1 q.1) (dist p.2 q.2)).trans hq) ht,
    lt_of_le_of_lt (by simpa using
      (le_max_right (dist p.1 q.1) (dist p.2 q.2)).trans hq) hs⟩

/-- Product parabolic cylinders form a local base for the ordinary product topology. -/
theorem exists_subset_of_mem_nhds {s : Set (ℝ × X)} (hs : s ∈ 𝓝 p) :
    ∃ timeRadius > 0, ∃ spaceRadius > 0,
      parabolicCylinder p timeRadius spaceRadius ⊆ s := by
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, hε, hεs⟩
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := half_pos hε
  have hδle : δ ≤ ε := by
    unfold δ
    linarith
  exact ⟨δ, hδpos, δ, hδpos,
    (subset_metric_ball (p := p) (timeRadius := δ) (spaceRadius := δ) hδle hδle).trans hεs⟩

theorem exists_finite_cover_of_isCompact {K : Set (ℝ × X)} (hK : IsCompact K)
    (ht : 0 < timeRadius) (hs : 0 < spaceRadius) :
    ∃ N ⊆ K, N.Finite ∧ K ⊆ ⋃ y ∈ N, parabolicCylinder y timeRadius spaceRadius := by
  let δ : ℝ := min timeRadius spaceRadius / 2
  have hδpos : 0 < δ := half_pos (lt_min ht hs)
  have hδ_time : δ < timeRadius := by
    unfold δ
    exact (half_lt_self (lt_min ht hs)).trans_le (min_le_left _ _)
  have hδ_space : δ < spaceRadius := by
    unfold δ
    exact (half_lt_self (lt_min ht hs)).trans_le (min_le_right _ _)
  let ε : ℝ≥0 := ⟨δ, hδpos.le⟩
  have hεne : ε ≠ 0 := by
    intro hε
    have hδ0 : δ = 0 := by
      simpa [ε] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hε
    linarith
  rcases Metric.exists_finite_isCover_of_isCompact (s := K) (ε := ε) hεne hK with
    ⟨N, hNK, hNfinite, hcover⟩
  refine ⟨N, hNK, hNfinite, ?_⟩
  have hcover' : K ⊆ ⋃ y ∈ N, Metric.closedBall y (ε : ℝ) :=
    hcover.subset_iUnion_closedBall
  intro z hz
  rcases mem_iUnion.1 (hcover' hz) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hzball⟩
  refine mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hyN, ?_⟩⟩
  exact (metric_closedBall_subset (p := y) (timeRadius := timeRadius)
    (spaceRadius := spaceRadius) (δ := (ε : ℝ))
    (by simpa [ε] using hδ_time) (by simpa [ε] using hδ_space)) hzball

/-- A compact set covered by an open set has a finite product-parabolic-cylinder cover whose
cylinders remain inside that open set.  The time and spatial radii may depend on the center. -/
theorem exists_finset_cover_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Finset (ℝ × X),
      (∀ x ∈ N, x ∈ K) ∧
      ∃ timeRadius spaceRadius : (ℝ × X) → ℝ,
        (∀ x ∈ N, 0 < timeRadius x) ∧
        (∀ x ∈ N, 0 < spaceRadius x) ∧
        (∀ x ∈ N, parabolicCylinder x (timeRadius x) (spaceRadius x) ⊆ U) ∧
        K ⊆ ⋃ x ∈ N, parabolicCylinder x (timeRadius x) (spaceRadius x) := by
  classical
  have hlocal :
      ∀ x ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
        parabolicCylinder x timeRadius spaceRadius ⊆ U := by
    intro x hx
    exact exists_subset_of_mem_nhds (hUopen.mem_nhds (hKU hx))
  let timeRadius : ℝ × X → ℝ :=
    fun x => if hx : x ∈ K then Classical.choose (hlocal x hx) else 1
  let spaceRadius : ℝ × X → ℝ := fun x =>
    if hx : x ∈ K then Classical.choose (Classical.choose_spec (hlocal x hx)).2 else 1
  have htime_pos : ∀ x ∈ K, 0 < timeRadius x := by
    intro x hx
    dsimp [timeRadius]
    rw [dif_pos hx]
    exact (Classical.choose_spec (hlocal x hx)).1
  have hspace_pos : ∀ x ∈ K, 0 < spaceRadius x := by
    intro x hx
    dsimp [spaceRadius]
    rw [dif_pos hx]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal x hx)).2).1
  have hcylinder_subset :
      ∀ x ∈ K, parabolicCylinder x (timeRadius x) (spaceRadius x) ⊆ U := by
    intro x hx
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hx, dif_pos hx]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal x hx)).2).2
  rcases hK.elim_nhds_subcover (fun x => parabolicCylinder x (timeRadius x) (spaceRadius x))
      (fun x hx => mem_nhds (p := x) (timeRadius := timeRadius x)
        (spaceRadius := spaceRadius x) (htime_pos x hx) (hspace_pos x hx)) with
    ⟨N, hNK, hcover⟩
  refine ⟨N, hNK, timeRadius, spaceRadius, ?_, ?_, ?_, hcover⟩
  · intro x hx
    exact htime_pos x (hNK x hx)
  · intro x hx
    exact hspace_pos x (hNK x hx)
  · intro x hx
    exact hcylinder_subset x (hNK x hx)

/-- A compact set inside an open set has a finite open product-parabolic-cylinder cover whose
matching closed cylinders remain inside that open set. -/
theorem exists_finset_cover_closedCylinder_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Finset (ℝ × X),
      (∀ x ∈ N, x ∈ K) ∧
      ∃ timeRadius spaceRadius : (ℝ × X) → ℝ,
        (∀ x ∈ N, 0 < timeRadius x) ∧
        (∀ x ∈ N, 0 < spaceRadius x) ∧
        (∀ x ∈ N, parabolicClosedCylinder x (timeRadius x) (spaceRadius x) ⊆ U) ∧
        K ⊆ ⋃ x ∈ N, parabolicCylinder x (timeRadius x) (spaceRadius x) := by
  classical
  have hlocal :
      ∀ x ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
        parabolicCylinder x timeRadius spaceRadius ⊆ U := by
    intro x hx
    exact exists_subset_of_mem_nhds (hUopen.mem_nhds (hKU hx))
  let timeRadius : ℝ × X → ℝ :=
    fun x => if hx : x ∈ K then Classical.choose (hlocal x hx) / 2 else 1
  let spaceRadius : ℝ × X → ℝ := fun x =>
    if hx : x ∈ K then Classical.choose (Classical.choose_spec (hlocal x hx)).2 / 2 else 1
  have htime_pos : ∀ x ∈ K, 0 < timeRadius x := by
    intro x hx
    dsimp [timeRadius]
    rw [dif_pos hx]
    exact half_pos (Classical.choose_spec (hlocal x hx)).1
  have hspace_pos : ∀ x ∈ K, 0 < spaceRadius x := by
    intro x hx
    dsimp [spaceRadius]
    rw [dif_pos hx]
    exact half_pos (Classical.choose_spec (Classical.choose_spec (hlocal x hx)).2).1
  have hclosed_subset :
      ∀ x ∈ K, parabolicClosedCylinder x (timeRadius x) (spaceRadius x) ⊆ U := by
    intro x hx
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hx, dif_pos hx]
    intro q hq
    exact (Classical.choose_spec (Classical.choose_spec (hlocal x hx)).2).2
      ⟨lt_of_le_of_lt hq.1 (half_lt_self (Classical.choose_spec (hlocal x hx)).1),
        lt_of_le_of_lt hq.2
          (half_lt_self (Classical.choose_spec (Classical.choose_spec (hlocal x hx)).2).1)⟩
  rcases hK.elim_nhds_subcover (fun x => parabolicCylinder x (timeRadius x) (spaceRadius x))
      (fun x hx => mem_nhds (p := x) (timeRadius := timeRadius x)
        (spaceRadius := spaceRadius x) (htime_pos x hx) (hspace_pos x hx)) with
    ⟨N, hNK, hcover⟩
  refine ⟨N, hNK, timeRadius, spaceRadius, ?_, ?_, ?_, hcover⟩
  · intro x hx
    exact htime_pos x (hNK x hx)
  · intro x hx
    exact hspace_pos x (hNK x hx)
  · intro x hx
    exact hclosed_subset x (hNK x hx)

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

namespace parabolicBall

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ × X} {R : ℝ}

/-- The parabolic ball of radius `R` is the product cylinder with time radius `R^2` and
spatial radius `R`. -/
theorem eq_cylinder (hR : 0 < R) :
    parabolicBall p R = parabolicCylinder p (R ^ 2) R :=
  subset_antisymm (subset_cylinder hR.le) (parabolicCylinder.subset_ball hR)

end parabolicBall

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

theorem subset_cylinder (ht : timeRadius < timeRadius') (hs : spaceRadius < spaceRadius') :
    parabolicClosedCylinder p timeRadius spaceRadius ⊆
      parabolicCylinder p timeRadius' spaceRadius' := by
  intro q hq
  exact ⟨lt_of_le_of_lt hq.1 ht, lt_of_le_of_lt hq.2 hs⟩

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

theorem isClosed (p : ℝ × X) (timeRadius spaceRadius : ℝ) :
    IsClosed (parabolicClosedCylinder p timeRadius spaceRadius) := by
  simpa [parabolicClosedCylinder] using
    ((isClosed_Iic.preimage (continuous_const.sub continuous_fst).abs).inter
      (isClosed_Iic.preimage (continuous_const.dist continuous_snd)))

theorem subset_metric_closedBall {ε : ℝ} (ht : timeRadius ≤ ε) (hs : spaceRadius ≤ ε) :
    parabolicClosedCylinder p timeRadius spaceRadius ⊆ Metric.closedBall p ε := by
  intro q hq
  rw [Metric.mem_closedBall, Prod.dist_eq]
  exact max_le
    (by simpa [Real.dist_eq, abs_sub_comm] using le_trans hq.1 ht)
    (by simpa [dist_comm] using le_trans hq.2 hs)

theorem metric_closedBall_subset {δ : ℝ}
    (ht : δ ≤ timeRadius) (hs : δ ≤ spaceRadius) :
    Metric.closedBall p δ ⊆ parabolicClosedCylinder p timeRadius spaceRadius := by
  intro q hq
  rw [Metric.mem_closedBall, dist_comm, Prod.dist_eq] at hq
  exact ⟨(by simpa [Real.dist_eq, abs_sub_comm] using
      ((le_max_left (dist p.1 q.1) (dist p.2 q.2)).trans hq).trans ht),
    (by simpa using ((le_max_right (dist p.1 q.1) (dist p.2 q.2)).trans hq).trans hs)⟩

theorem isCompact [ProperSpace X] (p : ℝ × X) (timeRadius spaceRadius : ℝ) :
    IsCompact (parabolicClosedCylinder p timeRadius spaceRadius) := by
  exact (isCompact_closedBall p (max timeRadius spaceRadius)).of_isClosed_subset
    (isClosed p timeRadius spaceRadius)
    (subset_metric_closedBall (p := p) (timeRadius := timeRadius) (spaceRadius := spaceRadius)
      (le_max_left _ _) (le_max_right _ _))

theorem exists_finite_cover_of_isCompact {K : Set (ℝ × X)} (hK : IsCompact K)
    (ht : 0 < timeRadius) (hs : 0 < spaceRadius) :
    ∃ N ⊆ K, N.Finite ∧ K ⊆ ⋃ y ∈ N,
      parabolicClosedCylinder y timeRadius spaceRadius := by
  let δ : ℝ := min timeRadius spaceRadius / 2
  have hδpos : 0 < δ := half_pos (lt_min ht hs)
  have hδ_time : δ ≤ timeRadius := by
    unfold δ
    exact (half_le_self (le_of_lt (lt_min ht hs))).trans (min_le_left _ _)
  have hδ_space : δ ≤ spaceRadius := by
    unfold δ
    exact (half_le_self (le_of_lt (lt_min ht hs))).trans (min_le_right _ _)
  let ε : ℝ≥0 := ⟨δ, hδpos.le⟩
  have hεne : ε ≠ 0 := by
    intro hε
    have hδ0 : δ = 0 := by
      simpa [ε] using congrArg (fun x : ℝ≥0 => (x : ℝ)) hε
    linarith
  rcases Metric.exists_finite_isCover_of_isCompact (s := K) (ε := ε) hεne hK with
    ⟨N, hNK, hNfinite, hcover⟩
  refine ⟨N, hNK, hNfinite, ?_⟩
  have hcover' : K ⊆ ⋃ y ∈ N, Metric.closedBall y (ε : ℝ) :=
    hcover.subset_iUnion_closedBall
  intro z hz
  rcases mem_iUnion.1 (hcover' hz) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hzball⟩
  refine mem_iUnion.2 ⟨y, mem_iUnion.2 ⟨hyN, ?_⟩⟩
  exact (metric_closedBall_subset (p := y) (timeRadius := timeRadius)
    (spaceRadius := spaceRadius) (δ := (ε : ℝ))
    (by simpa [ε] using hδ_time) (by simpa [ε] using hδ_space)) hzball

/-- A compact subset of an open set has one positive product-parabolic closed-cylinder radius
around every one of its points still contained in that open set. -/
theorem exists_uniform_subset_open_of_isCompact {K U : Set (ℝ × X)}
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ∀ x ∈ K, parabolicClosedCylinder x timeRadius spaceRadius ⊆ U := by
  rcases hK.exists_cthickening_subset_open hUopen hKU with ⟨δ, hδ, hδU⟩
  let radius : ℝ := δ / 2
  have hradius_pos : 0 < radius := half_pos hδ
  have hradius_le : radius ≤ δ := by
    unfold radius
    linarith
  refine ⟨radius, hradius_pos, radius, hradius_pos, ?_⟩
  intro x hx q hq
  have hqmetric : q ∈ Metric.closedBall x δ :=
    (subset_metric_closedBall (p := x) (timeRadius := radius)
      (spaceRadius := radius) (ε := δ) hradius_le hradius_le) hq
  exact hδU (Metric.mem_cthickening_of_dist_le q x δ K hx
    (Metric.mem_closedBall.1 hqmetric))

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

/-- Two points in the same closed product parabolic cylinder are at controlled parabolic distance
from each other.  The time radius doubles before taking the parabolic square root, while the
spatial radius doubles linearly. -/
theorem pair_parabolicDistance_le {c p q : ℝ × X}
    (hp : p ∈ parabolicClosedCylinder c timeRadius spaceRadius)
    (hq : q ∈ parabolicClosedCylinder c timeRadius spaceRadius) :
    parabolicDistance p q ≤ max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) := by
  change max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2) ≤
    max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius)
  have htime_abs : |p.1 - q.1| ≤ 2 * timeRadius := by
    have hp_time : |p.1 - c.1| ≤ timeRadius := by
      simpa [abs_sub_comm] using hp.1
    calc
      |p.1 - q.1| = |(p.1 - c.1) + (c.1 - q.1)| := by ring_nf
      _ ≤ |p.1 - c.1| + |c.1 - q.1| := abs_add_le _ _
      _ ≤ timeRadius + timeRadius := add_le_add hp_time hq.1
      _ = 2 * timeRadius := by ring
  have htime : Real.sqrt |p.1 - q.1| ≤ Real.sqrt (2 * timeRadius) :=
    Real.sqrt_le_sqrt htime_abs
  have hspace : dist p.2 q.2 ≤ 2 * spaceRadius := by
    have hp_space : dist p.2 c.2 ≤ spaceRadius := by
      simpa [dist_comm] using hp.2
    calc
      dist p.2 q.2 ≤ dist p.2 c.2 + dist c.2 q.2 := dist_triangle _ _ _
      _ ≤ spaceRadius + spaceRadius := add_le_add hp_space hq.2
      _ = 2 * spaceRadius := by ring
  exact max_le (htime.trans (le_max_left _ _)) (hspace.trans (le_max_right _ _))

end parabolicClosedCylinder

namespace parabolicCylinder

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ × X} {timeRadius spaceRadius : ℝ}

theorem closure_subset_closedCylinder :
    closure (parabolicCylinder p timeRadius spaceRadius) ⊆
      parabolicClosedCylinder p timeRadius spaceRadius :=
  closure_minimal subset_closedCylinder
    (parabolicClosedCylinder.isClosed p timeRadius spaceRadius)

end parabolicCylinder

namespace parabolicClosedBall

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ × X} {R : ℝ}

/-- The closed parabolic ball of radius `R` is the closed product cylinder with time radius
`R^2` and spatial radius `R`. -/
theorem eq_closedCylinder (hR : 0 ≤ R) :
    parabolicClosedBall p R = parabolicClosedCylinder p (R ^ 2) R :=
  subset_antisymm (subset_closedCylinder hR) (parabolicClosedCylinder.subset_closedBall hR)

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

/-- Holder control on an open set localizes, with the same constant, to one uniform closed
parabolic-ball radius around every point of a compact subset. -/
theorem exists_uniform_closedBall_of_isCompact_subset_open
    {K U : Set (ℝ × X)} (h : ParabolicHolderWith C α u U)
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ R > 0, ∀ x ∈ K, ParabolicHolderWith C α u (parabolicClosedBall x R) := by
  rcases parabolicClosedBall.exists_uniform_subset_open_of_isCompact hK hUopen hKU with
    ⟨R, hR, hRU⟩
  exact ⟨R, hR, fun x hx => h.mono_set (hRU x hx)⟩

/-- Holder control on an open set localizes, with the same constant, to one uniform closed
product-parabolic-cylinder radius around every point of a compact subset. -/
theorem exists_uniform_closedCylinder_of_isCompact_subset_open
    {K U : Set (ℝ × X)} (h : ParabolicHolderWith C α u U)
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ∀ x ∈ K, ParabolicHolderWith C α u
        (parabolicClosedCylinder x timeRadius spaceRadius) := by
  rcases parabolicClosedCylinder.exists_uniform_subset_open_of_isCompact hK hUopen hKU with
    ⟨timeRadius, htimeRadius, spaceRadius, hspaceRadius, hRU⟩
  exact ⟨timeRadius, htimeRadius, spaceRadius, hspaceRadius,
    fun x hx => h.mono_set (hRU x hx)⟩

theorem mono_const (h : ParabolicHolderWith C α u s) (hCC' : C ≤ C₂) :
    ParabolicHolderWith C₂ α u s := by
  intro p hp q hq
  exact (h hp hq).trans
    (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (parabolicDistance.nonneg p q) α))

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

theorem sum {ι : Type*} (S : Finset ι) {C : ι → ℝ} {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicHolderWith (C i) α (u i) s) :
    ParabolicHolderWith (∑ i ∈ S, C i) α (fun z => ∑ i ∈ S, u i z) s := by
  classical
  revert h
  refine Finset.induction_on S ?base ?step
  · intro _h
    simpa using (ParabolicHolderWith.const (s := s) (C := 0) (α := α) (0 : E) le_rfl)
  · intro a S ha ih h
    have ha_holder : ParabolicHolderWith (C a) α (u a) s := h a (by simp [ha])
    have htail : ParabolicHolderWith (∑ i ∈ S, C i) α (fun z => ∑ i ∈ S, u i z) s :=
      ih fun i hi => h i (by simp [hi])
    simpa [Finset.sum_insert ha, add_comm, add_left_comm, add_assoc] using ha_holder.add htail

theorem neg (hu : ParabolicHolderWith C α u s) :
    ParabolicHolderWith C α (fun z => -u z) s := by
  intro p hp q hq
  have hsub : (-u p) - (-u q) = -(u p - u q) := by
    abel
  calc
    ‖(-u p) - (-u q)‖ = ‖u p - u q‖ := by rw [hsub, norm_neg]
    _ ≤ C * (parabolicDistance p q) ^ α := hu hp hq

theorem sub (hu : ParabolicHolderWith C₁ α u s) (hv : ParabolicHolderWith C₂ α v s) :
    ParabolicHolderWith (C₁ + C₂) α (fun z => u z - v z) s := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem norm (hu : ParabolicHolderWith C α u s) :
    ParabolicHolderWith C α (fun z => ‖u z‖) s := by
  intro p hp q hq
  calc
    ‖‖u p‖ - ‖u q‖‖ ≤ ‖u p - u q‖ := by
      simpa [Real.norm_eq_abs] using abs_norm_sub_norm_le (u p) (u q)
    _ ≤ C * (parabolicDistance p q) ^ α := hu hp hq

theorem prod {F : Type*} [NormedAddCommGroup F] {D : ℝ} {v : ℝ × X → F}
    (hu : ParabolicHolderWith C α u s) (hv : ParabolicHolderWith D α v s) :
    ParabolicHolderWith (max C D) α (fun z => (u z, v z)) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hdα : 0 ≤ dα := Real.rpow_nonneg (parabolicDistance.nonneg p q) α
  change ‖(u p - u q, v p - v q)‖ ≤ max C D * dα
  rw [Prod.norm_mk]
  exact max_le
    ((hu hp hq).trans (mul_le_mul_of_nonneg_right (le_max_left C D) hdα))
    ((hv hp hq).trans (mul_le_mul_of_nonneg_right (le_max_right C D) hdα))

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

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicHolderWith C α u s)
    (hφ : LipschitzOnWith K φ (u '' s)) :
    ParabolicHolderWith ((K : ℝ) * C) α (fun z => φ (u z)) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hpim : u p ∈ u '' s := ⟨p, hp, rfl⟩
  have hqim : u q ∈ u '' s := ⟨q, hq, rfl⟩
  calc
    ‖φ (u p) - φ (u q)‖ = dist (φ (u p)) (φ (u q)) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (u p) (u q) := hφ.dist_le_mul (u p) hpim (u q) hqim
    _ = (K : ℝ) * ‖u p - u q‖ := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * (C * dα) :=
      mul_le_mul_of_nonneg_left (hu hp hq) (NNReal.coe_nonneg K)
    _ = ((K : ℝ) * C) * dα := by ring

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

/-- Local-to-global parabolic Holder control from a parabolic ball cover.  If `K` is covered by
radius-`r` parabolic balls, `u` is bounded on `K`, and each doubled closed ball carries the same
local Holder constant, then `u` has a global Holder constant on `K`. -/
theorem of_parabolicBall_cover_closedBall {B r : ℝ} {K N : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α) (hr : 0 < r)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y r)
    (hlocal : ∀ y ∈ N, ParabolicHolderWith C α u (parabolicClosedBall y (2 * r))) :
    ParabolicHolderWith (max C (2 * B / r ^ α)) α u K := by
  intro p hp q hq
  let d : ℝ := parabolicDistance p q
  let D : ℝ := max C (2 * B / r ^ α)
  change ‖u p - u q‖ ≤ D * d ^ α
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  by_cases hsmall : d < r
  · rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
    have hr_le_two : r ≤ 2 * r := by nlinarith [hr]
    have hpclosed : p ∈ parabolicClosedBall y (2 * r) :=
      (le_of_lt hpball).trans hr_le_two
    have hqclosed : q ∈ parabolicClosedBall y (2 * r) := by
      have hlt : parabolicDistance y q < 2 * r := by
        calc
          parabolicDistance y q ≤ parabolicDistance y p + parabolicDistance p q :=
            parabolicDistance.triangle y p q
          _ < r + r := by
            exact add_lt_add hpball hsmall
          _ = 2 * r := by ring
      exact le_of_lt hlt
    have hlocalpq : ‖u p - u q‖ ≤ C * d ^ α := by
      simpa [d] using hlocal y hyN hpclosed hqclosed
    exact hlocalpq.trans
      (mul_le_mul_of_nonneg_right (le_max_left C (2 * B / r ^ α))
        (Real.rpow_nonneg hd0 α))
  · have hfar : r ≤ d := le_of_not_gt hsmall
    have hBnonneg : 0 ≤ B := (norm_nonneg (u p)).trans (hbounded hp)
    have hrpow_pos : 0 < r ^ α := Real.rpow_pos_of_pos hr α
    have hrpow_le_dpow : r ^ α ≤ d ^ α :=
      Real.rpow_le_rpow hr.le hfar hα.le
    have hcoef_nonneg : 0 ≤ 2 * B / r ^ α :=
      div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
    have hdiff : ‖u p - u q‖ ≤ 2 * B := by
      calc
        ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hbounded hp) (hbounded hq)
        _ = 2 * B := by ring
    have hfar_bound : 2 * B ≤ D * d ^ α := by
      calc
        2 * B = (2 * B / r ^ α) * r ^ α := by
          rw [div_mul_cancel₀ _ hrpow_pos.ne']
        _ ≤ (2 * B / r ^ α) * d ^ α :=
          mul_le_mul_of_nonneg_left hrpow_le_dpow hcoef_nonneg
        _ ≤ D * d ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right C (2 * B / r ^ α))
            (Real.rpow_nonneg hd0 α)
    exact hdiff.trans hfar_bound

/-- Compact local-to-global parabolic Holder control from uniform local closed-ball estimates. -/
theorem of_isCompact_of_uniform_local_closedBall {B r : ℝ} {K : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hK : IsCompact K)
    (hα : 0 < α) (hr : 0 < r)
    (hlocal : ∀ y ∈ K, ParabolicHolderWith C α u (parabolicClosedBall y (2 * r))) :
    ParabolicHolderWith (max C (2 * B / r ^ α)) α u K := by
  rcases parabolicBall.exists_finite_cover_of_isCompact hK hr with
    ⟨N, hNK, _hNfinite, hcover⟩
  exact of_parabolicBall_cover_closedBall hbounded hα hr hcover
    (fun y hy => hlocal y (hNK hy))

/-- A parabolic distance bound upgrades a Holder estimate to a fixed oscillation bound. -/
theorem norm_sub_le_of_parabolicDistance_le (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hα : 0 ≤ α) {p q : ℝ × X} (hp : p ∈ s) (hq : q ∈ s) {R : ℝ}
    (hpq : parabolicDistance p q ≤ R) :
    ‖u p - u q‖ ≤ C * R ^ α := by
  exact (h hp hq).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (parabolicDistance.nonneg p q) hpq hα) hC)

/-- Oscillation bound for two points lying in the same closed parabolic ball. -/
theorem norm_sub_le_on_closedBall (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hα : 0 ≤ α) {c p q : ℝ × X} {R : ℝ}
    (hp_s : p ∈ s) (hq_s : q ∈ s)
    (hp : p ∈ parabolicClosedBall c R) (hq : q ∈ parabolicClosedBall c R) :
    ‖u p - u q‖ ≤ C * (2 * R) ^ α :=
  h.norm_sub_le_of_parabolicDistance_le hC hα hp_s hq_s
    (parabolicClosedBall.pair_parabolicDistance_le hp hq)

/-- Oscillation bound for two points lying in the same closed product parabolic cylinder. -/
theorem norm_sub_le_on_closedCylinder (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hα : 0 ≤ α) {c p q : ℝ × X} {timeRadius spaceRadius : ℝ}
    (hp_s : p ∈ s) (hq_s : q ∈ s)
    (hp : p ∈ parabolicClosedCylinder c timeRadius spaceRadius)
    (hq : q ∈ parabolicClosedCylinder c timeRadius spaceRadius) :
    ‖u p - u q‖ ≤
      C * (max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius)) ^ α :=
  h.norm_sub_le_of_parabolicDistance_le hC hα hp_s hq_s
    (parabolicClosedCylinder.pair_parabolicDistance_le hp hq)

theorem mono_exponent_of_parabolicDistance_le_one {β : ℝ}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicHolderWith C β u s := by
  intro p hp q hq
  let d := parabolicDistance p q
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  have hd1 : d ≤ 1 := hdiam hp hq
  have hpow : d ^ α ≤ d ^ β :=
    Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hβ hβα
  exact (h hp hq).trans (mul_le_mul_of_nonneg_left hpow hC)

theorem mono_exponent_of_subset_closedBall {β R : ℝ} {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicHolderWith C β u s :=
  h.mono_exponent_of_parabolicDistance_le_one hC hβ hβα (by
    intro p hp q hq
    exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)

theorem mono_exponent_of_subset_closedCylinder {β timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicHolderWith C β u s :=
  h.mono_exponent_of_parabolicDistance_le_one hC hβ hβα (by
    intro p hp q hq
    exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)

theorem boundedWith_of_subset_closedBall {B₀ R : ℝ} {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hc : c ∈ s) (huc : ‖u c‖ ≤ B₀) :
    ParabolicBoundedWith (B₀ + C * R ^ α) u s := by
  have hR : 0 ≤ R := by
    simpa using hs hc
  intro p hp
  have hpc : parabolicDistance p c ≤ R := by
    simpa [parabolicDistance.comm] using hs hp
  have hpow : (parabolicDistance p c) ^ α ≤ R ^ α :=
    Real.rpow_le_rpow (parabolicDistance.nonneg p c) hpc hα
  have hdecomp : u p = (u p - u c) + u c := by
    abel
  calc
    ‖u p‖ = ‖(u p - u c) + u c‖ := congrArg (fun z : E => ‖z‖) hdecomp
    _ ≤ ‖u p - u c‖ + ‖u c‖ := norm_add_le _ _
    _ ≤ C * (parabolicDistance p c) ^ α + B₀ := add_le_add (h hp hc) huc
    _ ≤ C * R ^ α + B₀ :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hC) le_rfl
    _ = B₀ + C * R ^ α := by ring

theorem boundedWith_of_subset_closedCylinder {B₀ timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius) (hc : c ∈ s)
    (huc : ‖u c‖ ≤ B₀) :
    ParabolicBoundedWith
      (B₀ + C * (max (Real.sqrt timeRadius) spaceRadius) ^ α) u s := by
  intro p hp
  have hpc_cyl : p ∈ parabolicClosedCylinder c timeRadius spaceRadius := hs hp
  have hpc : parabolicDistance p c ≤ max (Real.sqrt timeRadius) spaceRadius := by
    have htime : Real.sqrt |p.1 - c.1| ≤ Real.sqrt timeRadius :=
      Real.sqrt_le_sqrt (by simpa [abs_sub_comm] using hpc_cyl.1)
    have hspace : dist p.2 c.2 ≤ spaceRadius := by
      simpa [dist_comm] using hpc_cyl.2
    change max (Real.sqrt |p.1 - c.1|) (dist p.2 c.2) ≤
      max (Real.sqrt timeRadius) spaceRadius
    exact max_le (htime.trans (le_max_left _ _)) (hspace.trans (le_max_right _ _))
  have hpow : (parabolicDistance p c) ^ α ≤
      (max (Real.sqrt timeRadius) spaceRadius) ^ α :=
    Real.rpow_le_rpow (parabolicDistance.nonneg p c) hpc hα
  have hdecomp : u p = (u p - u c) + u c := by
    abel
  calc
    ‖u p‖ = ‖(u p - u c) + u c‖ := congrArg (fun z : E => ‖z‖) hdecomp
    _ ≤ ‖u p - u c‖ + ‖u c‖ := norm_add_le _ _
    _ ≤ C * (parabolicDistance p c) ^ α + B₀ := add_le_add (h hp hc) huc
    _ ≤ C * (max (Real.sqrt timeRadius) spaceRadius) ^ α + B₀ :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hC) le_rfl
    _ = B₀ + C * (max (Real.sqrt timeRadius) spaceRadius) ^ α := by ring

theorem c0AlphaWith_of_subset_closedBall {B₀ R : ℝ} {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hc : c ∈ s) (huc : ‖u c‖ ≤ B₀) :
    ParabolicC0AlphaWith (B₀ + C * R ^ α) C α u s :=
  ⟨h.boundedWith_of_subset_closedBall hC hα hs hc huc, h⟩

theorem c0AlphaWith_of_subset_closedCylinder {B₀ timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius) (hc : c ∈ s)
    (huc : ‖u c‖ ≤ B₀) :
    ParabolicC0AlphaWith
      (B₀ + C * (max (Real.sqrt timeRadius) spaceRadius) ^ α) C α u s :=
  ⟨h.boundedWith_of_subset_closedCylinder hC hα hs hc huc, h⟩

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

theorem sum {ι : Type*} (S : Finset ι) {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicHolderOn α (u i) s) :
    ParabolicHolderOn α (fun z => ∑ i ∈ S, u i z) s := by
  classical
  let C : ι → ℝ := fun i => if hi : i ∈ S then Classical.choose (h i hi) else 0
  have hCnonneg : ∀ i ∈ S, 0 ≤ C i := by
    intro i hi
    dsimp [C]
    rw [dif_pos hi]
    exact (Classical.choose_spec (h i hi)).1
  have hC :
      ∀ i ∈ S, ParabolicHolderWith (C i) α (u i) s := by
    intro i hi
    dsimp [C]
    rw [dif_pos hi]
    exact (Classical.choose_spec (h i hi)).2
  refine ⟨∑ i ∈ S, C i, Finset.sum_nonneg hCnonneg, ?_⟩
  exact ParabolicHolderWith.sum S hC

theorem neg (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => -u z) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.neg⟩

theorem sub (hu : ParabolicHolderOn α u s) (hv : ParabolicHolderOn α v s) :
    ParabolicHolderOn α (fun z => u z - v z) s := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem norm (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => ‖u z‖) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.norm⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {v : ℝ × X → F}
    (hu : ParabolicHolderOn α u s) (hv : ParabolicHolderOn α v s) :
    ParabolicHolderOn α (fun z => (u z, v z)) s := by
  rcases hu with ⟨C, hC, hCu⟩
  rcases hv with ⟨D, hD, hDv⟩
  exact ⟨max C D, hC.trans (le_max_left C D), hCu.prod hDv⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => c • u z) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, hCu.smul c⟩

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicHolderOn α u s)
    (hφ : LipschitzOnWith K φ (u '' s)) :
    ParabolicHolderOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨(K : ℝ) * C, mul_nonneg (NNReal.coe_nonneg K) hC,
    hCu.comp_lipschitzOnWith hφ⟩

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

/-- Local-to-global parabolic Holder control from a finite parabolic ball cover, with local
Holder constants chosen automatically and summed over the finite cover. -/
theorem of_finset_parabolicBall_cover_closedBall {B r : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hbounded : ParabolicBoundedWith B u K)
    (hα : 0 < α) (hr : 0 < r)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y r)
    (hlocal : ∀ y ∈ N, ParabolicHolderOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicHolderOn α u K := by
  classical
  let Hc : ℝ × X → ℝ :=
    fun y => if hy : y ∈ N then Classical.choose (hlocal y hy) else 0
  have hHnonneg : ∀ y ∈ N, 0 ≤ Hc y := by
    intro y hy
    dsimp [Hc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hH :
      ∀ y ∈ N, ParabolicHolderWith (Hc y) α u (parabolicClosedBall y (2 * r)) := by
    intro y hy
    dsimp [Hc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  let Hsum : ℝ := ∑ y ∈ N, Hc y
  have hHsum_nonneg : 0 ≤ Hsum := by
    dsimp [Hsum]
    exact Finset.sum_nonneg hHnonneg
  have hH_le_sum : ∀ y ∈ N, Hc y ≤ Hsum := by
    intro y hy
    dsimp [Hsum]
    exact Finset.single_le_sum hHnonneg hy
  have hlocal_sum :
      ∀ y ∈ N, ParabolicHolderWith Hsum α u (parabolicClosedBall y (2 * r)) := by
    intro y hy
    exact (hH y hy).mono_const (hH_le_sum y hy)
  refine ⟨max Hsum (2 * B / r ^ α), hHsum_nonneg.trans (le_max_left _ _), ?_⟩
  exact ParabolicHolderWith.of_parabolicBall_cover_closedBall
    (B := B) (C := Hsum) hbounded hα hr hcover hlocal_sum

/-- Local-to-global parabolic Holder control from a finite cover by variable-radius parabolic
balls.  The local Holder constants and the far-pair boundedness constants are summed over the
finite cover. -/
theorem of_finset_parabolicBall_cover_closedBall_variable {B : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (R : ℝ × X → ℝ)
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (hRpos : ∀ y ∈ N, 0 < R y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y (R y))
    (hlocal : ∀ y ∈ N, ParabolicHolderOn α u (parabolicClosedBall y (2 * R y))) :
    ParabolicHolderOn α u K := by
  classical
  let C : ℝ × X → ℝ := fun y =>
    if hy : y ∈ N then Classical.choose (hlocal y hy) else 0
  have hCnonneg : ∀ y ∈ N, 0 ≤ C y := by
    intro y hy
    dsimp [C]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hC :
      ∀ y ∈ N, ParabolicHolderWith (C y) α u (parabolicClosedBall y (2 * R y)) := by
    intro y hy
    dsimp [C]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  let A : ℝ × X → ℝ := fun y =>
    if hy : y ∈ N then max (C y) (2 * B / (R y) ^ α) else 0
  have hAnonneg : ∀ y ∈ N, 0 ≤ A y := by
    intro y hy
    dsimp [A]
    rw [if_pos hy]
    exact (hCnonneg y hy).trans (le_max_left _ _)
  let D : ℝ := ∑ y ∈ N, A y
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg hAnonneg
  have hA_le_D : ∀ y ∈ N, A y ≤ D := by
    intro y hy
    dsimp [D]
    exact Finset.single_le_sum hAnonneg hy
  refine ⟨D, hDnonneg, ?_⟩
  intro p hp q hq
  let d : ℝ := parabolicDistance p q
  change ‖u p - u q‖ ≤ D * d ^ α
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
  have hRy : 0 < R y := hRpos y hyN
  have hAyD : A y ≤ D := hA_le_D y hyN
  have hRy_le_two : R y ≤ 2 * R y := by linarith
  have hpclosed : p ∈ parabolicClosedBall y (2 * R y) :=
    (le_of_lt hpball).trans hRy_le_two
  have hpoint : ‖u p - u q‖ ≤ A y * d ^ α := by
    by_cases hsmall : d < R y
    · have hqclosed : q ∈ parabolicClosedBall y (2 * R y) := by
        have hlt : parabolicDistance y q < 2 * R y := by
          calc
            parabolicDistance y q ≤ parabolicDistance y p + parabolicDistance p q :=
              parabolicDistance.triangle y p q
            _ < R y + R y := by
              exact add_lt_add hpball hsmall
            _ = 2 * R y := by ring
        exact le_of_lt hlt
      have hlocalpq : ‖u p - u q‖ ≤ C y * d ^ α := by
        simpa [d] using hC y hyN hpclosed hqclosed
      have hCA : C y ≤ A y := by
        dsimp [A]
        rw [if_pos hyN]
        exact le_max_left _ _
      exact hlocalpq.trans
        (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hd0 α))
    · have hfar : R y ≤ d := le_of_not_gt hsmall
      have hBnonneg : 0 ≤ B := (norm_nonneg (u p)).trans (hbounded hp)
      have hrpow_pos : 0 < (R y) ^ α := Real.rpow_pos_of_pos hRy α
      have hrpow_le_dpow : (R y) ^ α ≤ d ^ α :=
        Real.rpow_le_rpow hRy.le hfar hα.le
      have hcoef_nonneg : 0 ≤ 2 * B / (R y) ^ α :=
        div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
      have hdiff : ‖u p - u q‖ ≤ 2 * B := by
        calc
          ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hbounded hp) (hbounded hq)
          _ = 2 * B := by ring
      have hfar_bound : 2 * B ≤ A y * d ^ α := by
        calc
          2 * B = (2 * B / (R y) ^ α) * (R y) ^ α := by
            rw [div_mul_cancel₀ _ hrpow_pos.ne']
          _ ≤ (2 * B / (R y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_left hrpow_le_dpow hcoef_nonneg
          _ ≤ A y * d ^ α := by
            have hcoefA : 2 * B / (R y) ^ α ≤ A y := by
              dsimp [A]
              rw [if_pos hyN]
              exact le_max_right _ _
            exact mul_le_mul_of_nonneg_right hcoefA (Real.rpow_nonneg hd0 α)
      exact hdiff.trans hfar_bound
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right hAyD (Real.rpow_nonneg hd0 α))

/-- Compact local-to-global parabolic Holder control from point-dependent doubled closed-ball
estimates, with Holder constants and cover radii chosen on a finite compact subcover. -/
theorem of_isCompact_of_local_closedBall_variable {B : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (R : ℝ × X → ℝ) (hRpos : ∀ y ∈ K, 0 < R y)
    (hlocal : ∀ y ∈ K, ParabolicHolderOn α u (parabolicClosedBall y (2 * R y))) :
    ParabolicHolderOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicBall y (R y))
      (fun y hy => parabolicBall.mem_nhds (p := y) (R := R y) (hRpos y hy)) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicBall_cover_closedBall_variable N R hbounded hα
    (fun y hy => hRpos y (hNK y hy)) hcover
    (fun y hy => hlocal y (hNK y hy))

/-- Compact local-to-global parabolic Holder control from pointwise positive local radii,
with the radii, cover, and Holder constants chosen automatically. -/
theorem of_isCompact_of_exists_local_closedBall {B : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ r > 0,
      ParabolicHolderOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicHolderOn α u K := by
  classical
  let R : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  have hRpos : ∀ y ∈ K, 0 < R y := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hlocalR : ∀ y ∈ K, ParabolicHolderOn α u (parabolicClosedBall y (2 * R y)) := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  exact of_isCompact_of_local_closedBall_variable hK hbounded hα R hRpos hlocalR

/-- Compact local-to-global parabolic Holder control from local doubled closed-ball estimates,
with Holder constants chosen automatically from a finite compact subcover. -/
theorem of_isCompact_of_local_closedBall {B r : ℝ} {K : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hK : IsCompact K)
    (hα : 0 < α) (hr : 0 < r)
    (hlocal : ∀ y ∈ K, ParabolicHolderOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicHolderOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicBall y r)
      (fun y _hy => parabolicBall.mem_nhds (p := y) (R := r) hr) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicBall_cover_closedBall N hbounded hα hr hcover
    (fun y hy => hlocal y (hNK y hy))

theorem mono_exponent_of_parabolicDistance_le_one {β : ℝ}
    (h : ParabolicHolderOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicHolderOn β u s := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.mono_exponent_of_parabolicDistance_le_one hC hβ hβα hdiam⟩

theorem mono_exponent_of_subset_closedBall {β R : ℝ} {c : ℝ × X}
    (h : ParabolicHolderOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicHolderOn β u s := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.mono_exponent_of_subset_closedBall hC hβ hβα hs hR⟩

theorem mono_exponent_of_subset_closedCylinder {β timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicHolderOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicHolderOn β u s := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.mono_exponent_of_subset_closedCylinder hC hβ hβα hs hdiam⟩

theorem c0AlphaOn_of_subset_closedBall {B₀ R : ℝ} {c : ℝ × X}
    (h : ParabolicHolderOn α u s) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hc : c ∈ s) (huc : ‖u c‖ ≤ B₀) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨C, hC, hCu⟩
  have hR : 0 ≤ R := by
    simpa using hs hc
  have hB₀ : 0 ≤ B₀ := (norm_nonneg (u c)).trans huc
  exact ⟨B₀ + C * R ^ α,
    add_nonneg hB₀ (mul_nonneg hC (Real.rpow_nonneg hR α)), C, hC,
    hCu.c0AlphaWith_of_subset_closedBall hC hα hs hc huc⟩

theorem c0AlphaOn_of_subset_closedCylinder {B₀ timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicHolderOn α u s) (hα : 0 ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius) (hc : c ∈ s)
    (huc : ‖u c‖ ≤ B₀) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨C, hC, hCu⟩
  let ρ : ℝ := max (Real.sqrt timeRadius) spaceRadius
  have hρ : 0 ≤ ρ := by
    unfold ρ
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  have hB₀ : 0 ≤ B₀ := (norm_nonneg (u c)).trans huc
  exact ⟨B₀ + C * ρ ^ α,
    add_nonneg hB₀ (mul_nonneg hC (Real.rpow_nonneg hρ α)), C, hC, by
      simpa [ρ] using hCu.c0AlphaWith_of_subset_closedCylinder hC hα hs hc huc⟩

theorem c0AlphaOn_of_isCompact (h : ParabolicHolderOn α u s) (hα : 0 < α)
    (hs : IsCompact s) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨C, hC, hCu⟩
  rcases hs.exists_bound_of_continuousOn (hCu.continuousOn hα) with ⟨B, hB⟩
  exact ⟨max B 0, le_max_right _ _, C, hC,
    ⟨fun p hp => (hB p hp).trans (le_max_left _ _), hCu⟩⟩

theorem c0AlphaOn_of_closedBall [ProperSpace X] {c : ℝ × X} {R : ℝ}
    (h : ParabolicHolderOn α u (parabolicClosedBall c R)) (hα : 0 < α) :
    ParabolicC0AlphaOn α u (parabolicClosedBall c R) :=
  h.c0AlphaOn_of_isCompact hα (parabolicClosedBall.isCompact c R)

theorem c0AlphaOn_of_closedCylinder [ProperSpace X] {c : ℝ × X}
    {timeRadius spaceRadius : ℝ}
    (h : ParabolicHolderOn α u (parabolicClosedCylinder c timeRadius spaceRadius))
    (hα : 0 < α) :
    ParabolicC0AlphaOn α u (parabolicClosedCylinder c timeRadius spaceRadius) :=
  h.c0AlphaOn_of_isCompact hα
    (parabolicClosedCylinder.isCompact c timeRadius spaceRadius)

end ParabolicHolderOn

namespace ParabolicBoundedWith

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {B B₁ B₂ : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem mono_set (h : ParabolicBoundedWith B u s) (hst : t ⊆ s) :
    ParabolicBoundedWith B u t := by
  intro p hp
  exact h (hst hp)

theorem mono_const (h : ParabolicBoundedWith B₁ u s) (hBB' : B₁ ≤ B₂) :
    ParabolicBoundedWith B₂ u s := by
  intro p hp
  exact (h hp).trans hBB'

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

theorem sum {ι : Type*} (S : Finset ι) {B : ι → ℝ} {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicBoundedWith (B i) (u i) s) :
    ParabolicBoundedWith (∑ i ∈ S, B i) (fun z => ∑ i ∈ S, u i z) s := by
  classical
  revert h
  refine Finset.induction_on S ?base ?step
  · intro _h
    simpa using (ParabolicBoundedWith.const (s := s) (B := 0) (0 : E) (by simp))
  · intro a S ha ih h
    have ha_bounded : ParabolicBoundedWith (B a) (u a) s := h a (by simp [ha])
    have htail : ParabolicBoundedWith (∑ i ∈ S, B i) (fun z => ∑ i ∈ S, u i z) s :=
      ih fun i hi => h i (by simp [hi])
    simpa [Finset.sum_insert ha, add_comm, add_left_comm, add_assoc] using ha_bounded.add htail

theorem neg (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith B (fun z => -u z) s := by
  intro p hp
  simpa using hu hp

theorem sub (hu : ParabolicBoundedWith B₁ u s) (hv : ParabolicBoundedWith B₂ v s) :
    ParabolicBoundedWith (B₁ + B₂) (fun z => u z - v z) s := by
  intro p hp
  calc
    ‖u p - v p‖ ≤ ‖u p‖ + ‖v p‖ := norm_sub_le _ _
    _ ≤ B₁ + B₂ := add_le_add (hu hp) (hv hp)

theorem norm (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith B (fun z => ‖u z‖) s := by
  intro p hp
  simpa [Real.norm_of_nonneg (norm_nonneg (u p))] using hu hp

theorem prod {F : Type*} [NormedAddCommGroup F] {D : ℝ} {v : ℝ × X → F}
    (hu : ParabolicBoundedWith B u s) (hv : ParabolicBoundedWith D v s) :
    ParabolicBoundedWith (max B D) (fun z => (u z, v z)) s := by
  intro p hp
  change ‖(u p, v p)‖ ≤ max B D
  rw [Prod.norm_mk]
  exact max_le ((hu hp).trans (le_max_left B D)) ((hv hp).trans (le_max_right B D))

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith (‖c‖ * B) (fun z => c • u z) s := by
  intro p hp
  calc
    ‖c • u p‖ = ‖c‖ * ‖u p‖ := norm_smul c (u p)
    _ ≤ ‖c‖ * B := mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg c)

theorem image_subset_closedBall_zero (hu : ParabolicBoundedWith B u s) :
    u '' s ⊆ Metric.closedBall (0 : E) B := by
  rintro y ⟨p, hp, rfl⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hu hp

theorem comp_of_range_bound {F : Type*} [NormedAddCommGroup F] {Bφ : ℝ}
    {φ : E → F} (hφ : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ) :
    ParabolicBoundedWith Bφ (fun z => φ (u z)) s := by
  intro p hp
  exact hφ (u p) ⟨p, hp, rfl⟩

theorem comp_of_closedBall_bound {F : Type*} [NormedAddCommGroup F] {Bφ : ℝ}
    {φ : E → F} (hu : ParabolicBoundedWith B u s)
    (hφ : ∀ y ∈ Metric.closedBall (0 : E) B, ‖φ y‖ ≤ Bφ) :
    ParabolicBoundedWith Bφ (fun z => φ (u z)) s :=
  comp_of_range_bound fun y hy => hφ y (hu.image_subset_closedBall_zero hy)

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

/-- Parabolic `C^{0,α}` control on an open set localizes, with the same constants, to one
uniform closed parabolic-ball radius around every point of a compact subset. -/
theorem exists_uniform_closedBall_of_isCompact_subset_open
    {K U : Set (ℝ × X)} (h : ParabolicC0AlphaWith B H α u U)
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ R > 0, ∀ x ∈ K, ParabolicC0AlphaWith B H α u (parabolicClosedBall x R) := by
  rcases parabolicClosedBall.exists_uniform_subset_open_of_isCompact hK hUopen hKU with
    ⟨R, hR, hRU⟩
  exact ⟨R, hR, fun x hx => h.mono_set (hRU x hx)⟩

/-- Parabolic `C^{0,α}` control on an open set localizes, with the same constants, to one
uniform closed product-parabolic-cylinder radius around every point of a compact subset. -/
theorem exists_uniform_closedCylinder_of_isCompact_subset_open
    {K U : Set (ℝ × X)} (h : ParabolicC0AlphaWith B H α u U)
    (hK : IsCompact K) (hUopen : IsOpen U) (hKU : K ⊆ U) :
    ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ∀ x ∈ K, ParabolicC0AlphaWith B H α u
        (parabolicClosedCylinder x timeRadius spaceRadius) := by
  rcases parabolicClosedCylinder.exists_uniform_subset_open_of_isCompact hK hUopen hKU with
    ⟨timeRadius, htimeRadius, spaceRadius, hspaceRadius, hRU⟩
  exact ⟨timeRadius, htimeRadius, spaceRadius, hspaceRadius,
    fun x hx => h.mono_set (hRU x hx)⟩

theorem mono_const (h : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hBB' : B₁ ≤ B₂) (hHH' : H₁ ≤ H₂) :
    ParabolicC0AlphaWith B₂ H₂ α u s :=
  ⟨h.bounded.mono_const hBB', h.holder.mono_const hHH'⟩

/-- Local-to-global parabolic `C^{0,α}` control from a parabolic ball cover.  The local bounded
constant controls the global bounded part, while the Holder constant globalizes through the
bounded local-to-global Holder estimate. -/
theorem of_parabolicBall_cover_closedBall {r : ℝ} {K N : Set (ℝ × X)}
    (hα : 0 < α) (hr : 0 < r)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y r)
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaWith B (max H (2 * B / r ^ α)) α u K := by
  have hbounded : ParabolicBoundedWith B u K := by
    intro p hp
    rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
    have hr_le_two : r ≤ 2 * r := by nlinarith [hr]
    have hpclosed : p ∈ parabolicClosedBall y (2 * r) :=
      (le_of_lt hpball).trans hr_le_two
    exact (hlocal y hyN).bounded hpclosed
  exact ⟨hbounded,
    ParabolicHolderWith.of_parabolicBall_cover_closedBall (C := H)
      hbounded hα hr hcover fun y hy => (hlocal y hy).holder⟩

/-- Compact local-to-global parabolic `C^{0,α}` control from uniform local closed-ball estimates. -/
theorem of_isCompact_of_uniform_local_closedBall {r : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (hr : 0 < r)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaWith B (max H (2 * B / r ^ α)) α u K := by
  rcases parabolicBall.exists_finite_cover_of_isCompact hK hr with
    ⟨N, hNK, _hNfinite, hcover⟩
  exact of_parabolicBall_cover_closedBall hα hr hcover
    (fun y hy => hlocal y (hNK hy))

theorem const (c : E) (hB : ‖c‖ ≤ B) (hH : 0 ≤ H) :
    ParabolicC0AlphaWith B H α (fun _ : ℝ × X => c) s :=
  ⟨ParabolicBoundedWith.const c hB, ParabolicHolderWith.const c hH⟩

theorem add (hu : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s) :
    ParabolicC0AlphaWith (B₁ + B₂) (H₁ + H₂) α (fun z => u z + v z) s :=
  ⟨hu.bounded.add hv.bounded, hu.holder.add hv.holder⟩

theorem sum {ι : Type*} (S : Finset ι) {B H : ι → ℝ} {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (u i) s) :
    ParabolicC0AlphaWith (∑ i ∈ S, B i) (∑ i ∈ S, H i) α
      (fun z => ∑ i ∈ S, u i z) s :=
  ⟨ParabolicBoundedWith.sum S (fun i hi => (h i hi).bounded),
    ParabolicHolderWith.sum S (fun i hi => (h i hi).holder)⟩

theorem neg (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith B H α (fun z => -u z) s :=
  ⟨hu.bounded.neg, hu.holder.neg⟩

theorem sub (hu : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s) :
    ParabolicC0AlphaWith (B₁ + B₂) (H₁ + H₂) α (fun z => u z - v z) s :=
  ⟨hu.bounded.sub hv.bounded, hu.holder.sub hv.holder⟩

theorem norm (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith B H α (fun z => ‖u z‖) s :=
  ⟨hu.bounded.norm, hu.holder.norm⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {B₃ H₃ : ℝ} {v : ℝ × X → F}
    (hu : ParabolicC0AlphaWith B H α u s)
    (hv : ParabolicC0AlphaWith B₃ H₃ α v s) :
    ParabolicC0AlphaWith (max B B₃) (max H H₃) α (fun z => (u z, v z)) s :=
  ⟨hu.bounded.prod hv.bounded, hu.holder.prod hv.holder⟩

theorem mul {A : Type*} [NormedRing A] {B₁ B₂ H₁ H₂ α : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicC0AlphaWith (B₁ * B₂) (B₁ * H₂ + B₂ * H₁) α
      (fun z => u z * v z) s := by
  constructor
  · intro p hp
    exact (norm_mul_le (u p) (v p)).trans
      (mul_le_mul (hu.bounded hp) (hv.bounded hp) (norm_nonneg _) hB₁)
  · intro p hp q hq
    let dα := (parabolicDistance p q) ^ α
    have hsplit :
        u p * v p - u q * v q = u p * (v p - v q) + (u p - u q) * v q := by
      noncomm_ring
    have hH₁d_nonneg : 0 ≤ H₁ * dα :=
      (norm_nonneg (u p - u q)).trans (hu.holder hp hq)
    calc
      ‖u p * v p - u q * v q‖
          = ‖u p * (v p - v q) + (u p - u q) * v q‖ := by rw [hsplit]
      _ ≤ ‖u p * (v p - v q)‖ + ‖(u p - u q) * v q‖ := norm_add_le _ _
      _ ≤ ‖u p‖ * ‖v p - v q‖ + ‖u p - u q‖ * ‖v q‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ B₁ * (H₂ * dα) + (H₁ * dα) * B₂ :=
        add_le_add
          (mul_le_mul (hu.bounded hp) (hv.holder hp hq) (norm_nonneg _) hB₁)
          (mul_le_mul (hu.holder hp hq) (hv.bounded hq) (norm_nonneg _) hH₁d_nonneg)
      _ = (B₁ * H₂ + B₂ * H₁) * dα := by ring

theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {B₁ B₂ H₁ H₂ α : ℝ} {a : ℝ × X → 𝕜} {u : ℝ × X → F} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaWith B₁ H₁ α a s)
    (hu : ParabolicC0AlphaWith B₂ H₂ α u s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicC0AlphaWith (B₁ * B₂) (B₁ * H₂ + B₂ * H₁) α
      (fun z => a z • u z) s := by
  constructor
  · intro p hp
    rw [norm_smul]
    exact mul_le_mul (ha.bounded hp) (hu.bounded hp) (norm_nonneg _) hB₁
  · intro p hp q hq
    let dα := (parabolicDistance p q) ^ α
    have hsplit :
        a p • u p - a q • u q = a p • (u p - u q) + (a p - a q) • u q := by
      calc
        a p • u p - a q • u q =
            (a p • u p - a p • u q) + (a p • u q - a q • u q) := by
          abel
        _ = a p • (u p - u q) + (a p - a q) • u q := by
          rw [smul_sub, sub_smul]
    have hH₁d_nonneg : 0 ≤ H₁ * dα :=
      (norm_nonneg (a p - a q)).trans (ha.holder hp hq)
    calc
      ‖a p • u p - a q • u q‖
          = ‖a p • (u p - u q) + (a p - a q) • u q‖ := by rw [hsplit]
      _ ≤ ‖a p • (u p - u q)‖ + ‖(a p - a q) • u q‖ := norm_add_le _ _
      _ = ‖a p‖ * ‖u p - u q‖ + ‖a p - a q‖ * ‖u q‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ B₁ * (H₂ * dα) + (H₁ * dα) * B₂ :=
        add_le_add
          (mul_le_mul (ha.bounded hp) (hu.holder hp hq) (norm_nonneg _) hB₁)
          (mul_le_mul (ha.holder hp hq) (hu.bounded hq) (norm_nonneg _) hH₁d_nonneg)
      _ = (B₁ * H₂ + B₂ * H₁) * dα := by ring

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith (‖c‖ * B) (‖c‖ * H) α (fun z => c • u z) s :=
  ⟨hu.bounded.smul c, hu.holder.smul c⟩

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F] {Bφ : ℝ} {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicC0AlphaWith B H α u s)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (u '' s)) :
    ParabolicC0AlphaWith Bφ ((K : ℝ) * H) α (fun z => φ (u z)) s :=
  ⟨ParabolicBoundedWith.comp_of_range_bound hφB, hu.holder.comp_lipschitzOnWith hφL⟩

theorem comp_lipschitzOnWith_of_closedBall {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaWith B H α u s)
    (hφB : ∀ y ∈ Metric.closedBall (0 : E) B, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (Metric.closedBall (0 : E) B)) :
    ParabolicC0AlphaWith Bφ ((K : ℝ) * H) α (fun z => φ (u z)) s :=
  hu.comp_lipschitzOnWith
    (fun y hy => hφB y (hu.bounded.image_subset_closedBall_zero hy))
    (hφL.mono hu.bounded.image_subset_closedBall_zero)

/-- The Holder component of positive-exponent parabolic `C^{0,α}` control gives continuity. -/
theorem continuousOn (h : ParabolicC0AlphaWith B H α u s) (hα : 0 < α) : ContinuousOn u s :=
  h.holder.continuousOn hα

/-- Positive-exponent parabolic `C^{0,α}` control gives uniform continuity. -/
theorem uniformContinuousOn (h : ParabolicC0AlphaWith B H α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.holder.uniformContinuousOn hα

theorem mono_exponent_of_parabolicDistance_le_one {β : ℝ}
    (h : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith B H β u s :=
  ⟨h.bounded, h.holder.mono_exponent_of_parabolicDistance_le_one hH hβ hβα hdiam⟩

theorem mono_exponent_of_subset_closedBall {β R : ℝ} {c : ℝ × X}
    (h : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith B H β u s :=
  ⟨h.bounded, h.holder.mono_exponent_of_subset_closedBall hH hβ hβα hs hR⟩

theorem mono_exponent_of_subset_closedCylinder {β timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith B H β u s :=
  ⟨h.bounded, h.holder.mono_exponent_of_subset_closedCylinder hH hβ hβα hs hdiam⟩

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

/-- Local-to-global parabolic `C^{0,α}` control from a finite parabolic ball cover, with local
constants chosen automatically and summed over the finite cover. -/
theorem of_finset_parabolicBall_cover_closedBall {r : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hα : 0 < α) (hr : 0 < r)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y r)
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaOn α u K := by
  classical
  let Bc : ℝ × X → ℝ :=
    fun y => if hy : y ∈ N then Classical.choose (hlocal y hy) else 0
  let Hc : ℝ × X → ℝ := fun y =>
    if hy : y ∈ N then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 0
  have hBnonneg : ∀ y ∈ N, 0 ≤ Bc y := by
    intro y hy
    dsimp [Bc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hHnonneg : ∀ y ∈ N, 0 ≤ Hc y := by
    intro y hy
    dsimp [Hc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hBH :
      ∀ y ∈ N, ParabolicC0AlphaWith (Bc y) (Hc y) α u
        (parabolicClosedBall y (2 * r)) := by
    intro y hy
    dsimp [Bc, Hc]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2
  let Bsum : ℝ := ∑ y ∈ N, Bc y
  let Hsum : ℝ := ∑ y ∈ N, Hc y
  have hBsum_nonneg : 0 ≤ Bsum := by
    dsimp [Bsum]
    exact Finset.sum_nonneg hBnonneg
  have hHsum_nonneg : 0 ≤ Hsum := by
    dsimp [Hsum]
    exact Finset.sum_nonneg hHnonneg
  have hB_le_sum : ∀ y ∈ N, Bc y ≤ Bsum := by
    intro y hy
    dsimp [Bsum]
    exact Finset.single_le_sum hBnonneg hy
  have hH_le_sum : ∀ y ∈ N, Hc y ≤ Hsum := by
    intro y hy
    dsimp [Hsum]
    exact Finset.single_le_sum hHnonneg hy
  have hlocal_sum :
      ∀ y ∈ N, ParabolicC0AlphaWith Bsum Hsum α u (parabolicClosedBall y (2 * r)) := by
    intro y hy
    exact (hBH y hy).mono_const (hB_le_sum y hy) (hH_le_sum y hy)
  refine ⟨Bsum, hBsum_nonneg, max Hsum (2 * Bsum / r ^ α),
    hHsum_nonneg.trans (le_max_left _ _), ?_⟩
  exact ParabolicC0AlphaWith.of_parabolicBall_cover_closedBall
    (B := Bsum) (H := Hsum) hα hr hcover hlocal_sum

/-- Local-to-global parabolic `C^{0,α}` control from a finite cover by variable-radius
parabolic balls.  The global sup constant is the sum of local sup constants, and the Holder
constant is supplied by the variable-radius Holder patching theorem. -/
theorem of_finset_parabolicBall_cover_closedBall_variable {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (R : ℝ × X → ℝ) (hα : 0 < α)
    (hRpos : ∀ y ∈ N, 0 < R y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y (R y))
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * R y))) :
    ParabolicC0AlphaOn α u K := by
  classical
  let Bc : ℝ × X → ℝ :=
    fun y => if hy : y ∈ N then Classical.choose (hlocal y hy) else 0
  have hBnonneg : ∀ y ∈ N, 0 ≤ Bc y := by
    intro y hy
    dsimp [Bc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hBlocal :
      ∀ y ∈ N, ParabolicBoundedWith (Bc y) u (parabolicClosedBall y (2 * R y)) := by
    intro y hy
    dsimp [Bc]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.1
  let Bsum : ℝ := ∑ y ∈ N, Bc y
  have hBsum_nonneg : 0 ≤ Bsum := by
    dsimp [Bsum]
    exact Finset.sum_nonneg hBnonneg
  have hB_le_sum : ∀ y ∈ N, Bc y ≤ Bsum := by
    intro y hy
    dsimp [Bsum]
    exact Finset.single_le_sum hBnonneg hy
  have hbounded : ParabolicBoundedWith Bsum u K := by
    intro p hp
    rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
    have hRy : 0 < R y := hRpos y hyN
    have hRy_le_two : R y ≤ 2 * R y := by linarith
    have hpclosed : p ∈ parabolicClosedBall y (2 * R y) :=
      (le_of_lt hpball).trans hRy_le_two
    exact (hBlocal y hyN hpclosed).trans (hB_le_sum y hyN)
  rcases ParabolicHolderOn.of_finset_parabolicBall_cover_closedBall_variable
      (B := Bsum) N R hbounded hα hRpos hcover
      (fun y hy => (hlocal y hy).holderOn) with
    ⟨H, hHnonneg, hH⟩
  exact ⟨Bsum, hBsum_nonneg, H, hHnonneg, hbounded, hH⟩

/-- Compact local-to-global parabolic `C^{0,α}` control from point-dependent doubled
closed-ball estimates, with all constants and cover radii chosen on a finite compact subcover. -/
theorem of_isCompact_of_local_closedBall_variable {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (R : ℝ × X → ℝ)
    (hRpos : ∀ y ∈ K, 0 < R y)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * R y))) :
    ParabolicC0AlphaOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicBall y (R y))
      (fun y hy => parabolicBall.mem_nhds (p := y) (R := R y) (hRpos y hy)) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicBall_cover_closedBall_variable N R hα
    (fun y hy => hRpos y (hNK y hy)) hcover
    (fun y hy => hlocal y (hNK y hy))

/-- Compact local-to-global parabolic `C^{0,α}` control from pointwise positive local radii,
with the radii, cover, and constants chosen automatically. -/
theorem of_isCompact_of_exists_local_closedBall {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ r > 0,
      ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaOn α u K := by
  classical
  let R : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  have hRpos : ∀ y ∈ K, 0 < R y := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hlocalR : ∀ y ∈ K, ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * R y)) := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  exact of_isCompact_of_local_closedBall_variable hK hα R hRpos hlocalR

/-- Compact local-to-global parabolic `C^{0,α}` control from local doubled closed-ball estimates,
with all constants chosen automatically from a finite compact subcover. -/
theorem of_isCompact_of_local_closedBall {r : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (hr : 0 < r)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaOn α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicBall y r)
      (fun y _hy => parabolicBall.mem_nhds (p := y) (R := r) hr) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicBall_cover_closedBall N hα hr hcover
    (fun y hy => hlocal y (hNK y hy))

theorem const (c : E) : ParabolicC0AlphaOn α (fun _ : ℝ × X => c) s :=
  ⟨‖c‖, norm_nonneg c, 0, le_rfl, ParabolicC0AlphaWith.const c le_rfl le_rfl⟩

theorem add (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => u z + v z) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ + B₂, add_nonneg hB₁ hB₂, H₁ + H₂, add_nonneg hH₁ hH₂, hBH₁.add hBH₂⟩

theorem sum {ι : Type*} (S : Finset ι) {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaOn α (u i) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i ∈ S, u i z) s := by
  classical
  let B : ι → ℝ := fun i => if hi : i ∈ S then Classical.choose (h i hi) else 0
  let H : ι → ℝ := fun i =>
    if hi : i ∈ S then Classical.choose (Classical.choose_spec (h i hi)).2 else 0
  have hBnonneg : ∀ i ∈ S, 0 ≤ B i := by
    intro i hi
    dsimp [B]
    rw [dif_pos hi]
    exact (Classical.choose_spec (h i hi)).1
  have hHnonneg : ∀ i ∈ S, 0 ≤ H i := by
    intro i hi
    dsimp [H]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (h i hi)).2).1
  have hBH :
      ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (u i) s := by
    intro i hi
    dsimp [B, H]
    rw [dif_pos hi, dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (h i hi)).2).2
  refine ⟨∑ i ∈ S, B i, Finset.sum_nonneg hBnonneg,
    ∑ i ∈ S, H i, Finset.sum_nonneg hHnonneg, ?_⟩
  exact ParabolicC0AlphaWith.sum S hBH

theorem neg (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => -u z) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH, hBH.neg⟩

theorem sub (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => u z - v z) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ + B₂, add_nonneg hB₁ hB₂, H₁ + H₂, add_nonneg hH₁ hH₂, hBH₁.sub hBH₂⟩

theorem norm (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => ‖u z‖) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH, hBH.norm⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {v : ℝ × X → F}
    (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => (u z, v z)) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨max B₁ B₂, hB₁.trans (le_max_left B₁ B₂), max H₁ H₂,
    hH₁.trans (le_max_left H₁ H₂),
    hBH₁.prod hBH₂⟩

theorem mul {A : Type*} [NormedRing A] {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => u z * v z) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ * B₂, mul_nonneg hB₁ hB₂,
    B₁ * H₂ + B₂ * H₁, add_nonneg (mul_nonneg hB₁ hH₂) (mul_nonneg hB₂ hH₁),
    hBH₁.mul hBH₂ hB₁⟩

theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {a : ℝ × X → 𝕜} {u : ℝ × X → F} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaOn α a s) (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => a z • u z) s := by
  rcases ha with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hu with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ * B₂, mul_nonneg hB₁ hB₂,
    B₁ * H₂ + B₂ * H₁, add_nonneg (mul_nonneg hB₁ hH₂) (mul_nonneg hB₂ hH₁),
    hBH₁.smul_fun hBH₂ hB₁⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => c • u z) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB,
    ‖c‖ * H, mul_nonneg (norm_nonneg c) hH, hBH.smul c⟩

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F] {Bφ : ℝ} {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicC0AlphaOn α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (u '' s)) :
    ParabolicC0AlphaOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨Bφ, hBφ, (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH,
    hBH.comp_lipschitzOnWith hφB hφL⟩

theorem comp_lipschitzOnWith_of_closedBall {F : Type*} [NormedAddCommGroup F]
    {B Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaOn α u s) (hBound : ParabolicBoundedWith B u s)
    (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ Metric.closedBall (0 : E) B, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (Metric.closedBall (0 : E) B)) :
    ParabolicC0AlphaOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨_B, _hB, H, hH, hBH⟩
  exact ⟨Bφ, hBφ, (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH,
    ⟨hBound.comp_of_closedBall_bound hφB,
      hBH.holder.comp_lipschitzOnWith (hφL.mono hBound.image_subset_closedBall_zero)⟩⟩

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

theorem mono_exponent_of_parabolicDistance_le_one {β : ℝ}
    (h : ParabolicC0AlphaOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn β u s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH,
    hBH.mono_exponent_of_parabolicDistance_le_one hH hβ hβα hdiam⟩

theorem mono_exponent_of_subset_closedBall {β R : ℝ} {c : ℝ × X}
    (h : ParabolicC0AlphaOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn β u s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH, hBH.mono_exponent_of_subset_closedBall hH hβ hβα hs hR⟩

theorem mono_exponent_of_subset_closedCylinder {β timeRadius spaceRadius : ℝ}
    {c : ℝ × X}
    (h : ParabolicC0AlphaOn α u s) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn β u s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH,
    hBH.mono_exponent_of_subset_closedCylinder hH hβ hβα hs hdiam⟩

end ParabolicC0AlphaOn

end AnalyticPDE
end RicciFlow

