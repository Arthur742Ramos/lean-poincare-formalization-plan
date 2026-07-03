module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Normed.Operator.NormedSpace
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

/-- A point in an open product parabolic cylinder lies in the doubled closed cylinder. -/
theorem mem_closedCylinder_two_of_mem
    (hq : q ∈ parabolicCylinder p timeRadius spaceRadius) :
    q ∈ parabolicClosedCylinder p (2 * timeRadius) (2 * spaceRadius) := by
  have htime_pos : 0 < timeRadius := lt_of_le_of_lt (abs_nonneg _) hq.1
  have hspace_pos : 0 < spaceRadius := lt_of_le_of_lt dist_nonneg hq.2
  exact ⟨(le_of_lt hq.1).trans (by linarith),
    (le_of_lt hq.2).trans (by linarith)⟩

/-- If `p` lies in a product parabolic cylinder and `q` is parabolically close to `p` at the
smaller of the time and spatial scales, then `q` lies in the doubled closed cylinder. -/
theorem mem_closedCylinder_two_of_mem_of_parabolicDistance_lt_min_sqrt
    {c p q : ℝ × X}
    (hp : p ∈ parabolicCylinder c timeRadius spaceRadius)
    (hpq : parabolicDistance p q < min (Real.sqrt timeRadius) spaceRadius) :
    q ∈ parabolicClosedCylinder c (2 * timeRadius) (2 * spaceRadius) := by
  have htime_pos : 0 < timeRadius := lt_of_le_of_lt (abs_nonneg _) hp.1
  have hpq_sqrt : Real.sqrt |p.1 - q.1| < Real.sqrt timeRadius :=
    lt_of_le_of_lt (parabolicDistance.sqrt_time_le p q)
      (lt_of_lt_of_le hpq (min_le_left _ _))
  have hpq_time : |p.1 - q.1| < timeRadius := by
    calc
      |p.1 - q.1| = (Real.sqrt |p.1 - q.1|) ^ 2 := by
        rw [Real.sq_sqrt (abs_nonneg _)]
      _ < (Real.sqrt timeRadius) ^ 2 :=
        (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hpq_sqrt
      _ = timeRadius := Real.sq_sqrt htime_pos.le
  have htime : |c.1 - q.1| < 2 * timeRadius := by
    calc
      |c.1 - q.1| = |(c.1 - p.1) + (p.1 - q.1)| := by ring_nf
      _ ≤ |c.1 - p.1| + |p.1 - q.1| := abs_add_le _ _
      _ < timeRadius + timeRadius := add_lt_add hp.1 hpq_time
      _ = 2 * timeRadius := by ring
  have hpq_space : dist p.2 q.2 < spaceRadius :=
    lt_of_le_of_lt (parabolicDistance.space_dist_le p q)
      (lt_of_lt_of_le hpq (min_le_right _ _))
  have hspace : dist c.2 q.2 < 2 * spaceRadius := by
    calc
      dist c.2 q.2 ≤ dist c.2 p.2 + dist p.2 q.2 := dist_triangle _ _ _
      _ < spaceRadius + spaceRadius := add_lt_add hp.2 hpq_space
      _ = 2 * spaceRadius := by ring
  exact ⟨le_of_lt htime, le_of_lt hspace⟩

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

/-- **Parabolic scaling identity.** Under the affine parabolic dilation of `ℝ × X` that
scales time by `r ^ 2` and space by `r`, the parabolic distance scales by exactly `|r|`.
Combined with `ParabolicC0AlphaWith.comp_parabolicDistanceLe` (with `L = |r|`), this is the
change of variables underlying the Schauder scaling argument. -/
theorem parabolicDistance_dilation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (r : ℝ) (p q : ℝ × X) :
    parabolicDistance (r ^ 2 * p.1, r • p.2) (r ^ 2 * q.1, r • q.2)
      = |r| * parabolicDistance p q := by
  have htime : Real.sqrt |r ^ 2 * p.1 - r ^ 2 * q.1| = |r| * Real.sqrt |p.1 - q.1| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r), Real.sqrt_mul (sq_nonneg r),
      Real.sqrt_sq_eq_abs]
  have hspace : dist (r • p.2) (r • q.2) = |r| * dist p.2 q.2 := by
    rw [dist_smul₀, Real.norm_eq_abs]
  show max (Real.sqrt |r ^ 2 * p.1 - r ^ 2 * q.1|) (dist (r • p.2) (r • q.2))
      = |r| * max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)
  rw [htime, hspace]
  exact (mul_max_of_nonneg _ _ (abs_nonneg r)).symm

/-- **Parabolic distance is translation invariant.** Adding a fixed time-space vector `c` to
both arguments leaves the parabolic distance unchanged.  Together with `parabolicDistance_dilation`
this gives the affine parabolic change of variables (rescaling about an arbitrary center) used in
the Schauder argument. -/
theorem parabolicDistance_add_left {X : Type*} [NormedAddCommGroup X] (c p q : ℝ × X) :
    parabolicDistance (c + p) (c + q) = parabolicDistance p q := by
  have htime : |(c + p).1 - (c + q).1| = |p.1 - q.1| := by
    simp [add_sub_add_left_eq_sub]
  have hspace : dist (c + p).2 (c + q).2 = dist p.2 q.2 := by
    simp [dist_add_left]
  show max (Real.sqrt |(c + p).1 - (c + q).1|) (dist (c + p).2 (c + q).2)
      = max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)
  rw [htime, hspace]

/-- The origin-centered parabolic dilation maps the closed parabolic ball of radius `ρ` into
the closed parabolic ball of radius `|r| * ρ`.  This discharges the `Set.MapsTo` hypothesis of
the Schauder scaling estimates for balls centered at the origin. -/
theorem parabolicClosedBall_zero_mapsTo_dilation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r ρ : ℝ} :
    Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2))
      (parabolicClosedBall (0 : ℝ × X) ρ) (parabolicClosedBall (0 : ℝ × X) (|r| * ρ)) := by
  intro q hq
  simp only [parabolicClosedBall, Set.mem_setOf_eq] at hq ⊢
  have hz : ((r ^ 2 * (0 : ℝ × X).1, r • (0 : ℝ × X).2) : ℝ × X) = (0 : ℝ × X) := by
    simp
  have hkey : parabolicDistance (0 : ℝ × X) (r ^ 2 * q.1, r • q.2)
      = |r| * parabolicDistance (0 : ℝ × X) q := by
    have h := parabolicDistance_dilation r (0 : ℝ × X) q
    rw [hz] at h
    exact h
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg r)

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

/-- The reciprocal map is Lipschitz on the set where the norm is bounded below by a
positive constant.  This scalar estimate is the local model behind reciprocal and inverse-metric
Lipschitz bounds in chart estimates. -/
theorem lipschitzOnWith_inv_of_norm_ge {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ}
    (hδpos : 0 < δ) :
    LipschitzOnWith
      ⟨δ⁻¹ * δ⁻¹, mul_nonneg (inv_nonneg.mpr hδpos.le) (inv_nonneg.mpr hδpos.le)⟩
      (fun a : 𝕜 => a⁻¹) {a : 𝕜 | δ ≤ ‖a‖} := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro a ha b hb
  have ha_pos : 0 < ‖a‖ := lt_of_lt_of_le hδpos ha
  have hb_pos : 0 < ‖b‖ := lt_of_lt_of_le hδpos hb
  have ha_ne : a ≠ 0 := norm_pos_iff.mp ha_pos
  have hb_ne : b ≠ 0 := norm_pos_iff.mp hb_pos
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have haina : ‖a⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ ha_pos hδpos).2 ha
  have hinvb : ‖b⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hb_pos hδpos).2 hb
  have hsplit : a⁻¹ - b⁻¹ = -(a⁻¹ * (a - b) * b⁻¹) := by
    field_simp [ha_ne, hb_ne]
    ring
  calc
    dist (a⁻¹) (b⁻¹) = ‖a⁻¹ - b⁻¹‖ := by rw [dist_eq_norm]
    _ = ‖-(a⁻¹ * (a - b) * b⁻¹)‖ := by rw [hsplit]
    _ = ‖a⁻¹ * (a - b) * b⁻¹‖ := norm_neg _
    _ ≤ ‖a⁻¹‖ * ‖a - b‖ * ‖b⁻¹‖ := by
      calc
        ‖a⁻¹ * (a - b) * b⁻¹‖ ≤ ‖a⁻¹ * (a - b)‖ * ‖b⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖a⁻¹‖ * ‖a - b‖) * ‖b⁻¹‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ δ⁻¹ * ‖a - b‖ * δ⁻¹ := by
      have hleft : ‖a⁻¹‖ * ‖a - b‖ ≤ δ⁻¹ * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right haina (norm_nonneg _)
      exact mul_le_mul hleft hinvb (norm_nonneg _)
        (mul_nonneg hinvδ_nonneg (norm_nonneg _))
    _ = (δ⁻¹ * δ⁻¹) * dist a b := by rw [dist_eq_norm]; ring

/-- A finite product is bounded by the product of factor bounds, with a unit-norm factor that keeps
the statement valid for normed rings whose unit is not normalized. -/
theorem norm_finset_prod_le_unit_mul_prod_max {ι A : Type*} [NormedCommRing A]
    (S : Finset ι) {C : ι → ℝ} {a : ι → A}
    (ha : ∀ i ∈ S, ‖a i‖ ≤ C i) :
    ‖∏ i ∈ S, a i‖ ≤ max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1 := by
  classical
  revert ha
  refine Finset.induction_on S ?base ?step
  · intro _ha
    simp
  · intro x S hx ih ha
    have hx_bound : ‖a x‖ ≤ max (C x) 1 :=
      (ha x (by simp [hx])).trans (le_max_left _ _)
    have htail :
        ‖∏ i ∈ S, a i‖ ≤ max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1 :=
      ih fun i hi => ha i (by simp [hi])
    have hx_bound_nonneg : 0 ≤ max (C x) 1 := zero_le_one.trans (le_max_right _ _)
    calc
      ‖∏ i ∈ insert x S, a i‖ = ‖a x * ∏ i ∈ S, a i‖ := by
        rw [Finset.prod_insert hx]
      _ ≤ ‖a x‖ * ‖∏ i ∈ S, a i‖ := norm_mul_le _ _
      _ ≤ max (C x) 1 * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1) :=
        mul_le_mul hx_bound htail (norm_nonneg _) hx_bound_nonneg
      _ = max ‖(1 : A)‖ 1 * ∏ i ∈ insert x S, max (C i) 1 := by
        rw [Finset.prod_insert hx]
        ring

/-- A finite product is Lipschitz, pointwise, on factorwise bounded sets.  The right-hand side is
deliberately coarse: a sum of factor differences times a product of closed sup bounds. -/
theorem norm_finset_prod_sub_prod_le_sum_norm_sub_mul_unit_prod_max {ι A : Type*}
    [NormedCommRing A] (S : Finset ι) {C : ι → ℝ} {a b : ι → A}
    (ha : ∀ i ∈ S, ‖a i‖ ≤ C i) (hb : ∀ i ∈ S, ‖b i‖ ≤ C i) :
    ‖(∏ i ∈ S, a i) - ∏ i ∈ S, b i‖ ≤
      (∑ i ∈ S, ‖a i - b i‖) * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1) := by
  classical
  revert ha hb
  refine Finset.induction_on S ?base ?step
  · intro _ha _hb
    simp
  · intro x S hx ih ha hb
    have htail :
        ‖(∏ i ∈ S, a i) - ∏ i ∈ S, b i‖ ≤
          (∑ i ∈ S, ‖a i - b i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1) :=
      ih (fun i hi => ha i (by simp [hi])) (fun i hi => hb i (by simp [hi]))
    have hx_bound : ‖a x‖ ≤ max (C x) 1 :=
      (ha x (by simp [hx])).trans (le_max_left _ _)
    have hbtail :
        ‖∏ i ∈ S, b i‖ ≤ max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1 :=
      norm_finset_prod_le_unit_mul_prod_max S (fun i hi => hb i (by simp [hi]))
    have hsplit :
        (∏ i ∈ insert x S, a i) - ∏ i ∈ insert x S, b i =
          a x * ((∏ i ∈ S, a i) - ∏ i ∈ S, b i) + (a x - b x) * ∏ i ∈ S, b i := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    have hunit_tail_nonneg : 0 ≤ max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1 :=
      mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (C i) 1))
    have hsum_tail_nonneg : 0 ≤ ∑ i ∈ S, ‖a i - b i‖ :=
      Finset.sum_nonneg fun i _hi => norm_nonneg _
    have hx_max_ge_one : 1 ≤ max (C x) 1 := le_max_right _ _
    have hdiffx_nonneg : 0 ≤ ‖a x - b x‖ := norm_nonneg _
    have hdiffx_term :
        ‖a x - b x‖ * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1) ≤
          max (C x) 1 *
            (‖a x - b x‖ * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) := by
      calc
        ‖a x - b x‖ * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)
            = 1 * (‖a x - b x‖ *
              (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) := by ring
        _ ≤ max (C x) 1 *
              (‖a x - b x‖ *
                (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) :=
          mul_le_mul_of_nonneg_right hx_max_ge_one
            (mul_nonneg hdiffx_nonneg hunit_tail_nonneg)
    calc
      ‖(∏ i ∈ insert x S, a i) - ∏ i ∈ insert x S, b i‖
          = ‖a x * ((∏ i ∈ S, a i) - ∏ i ∈ S, b i) +
              (a x - b x) * ∏ i ∈ S, b i‖ := by rw [hsplit]
      _ ≤ ‖a x * ((∏ i ∈ S, a i) - ∏ i ∈ S, b i)‖ +
            ‖(a x - b x) * ∏ i ∈ S, b i‖ := norm_add_le _ _
      _ ≤ ‖a x‖ * ‖(∏ i ∈ S, a i) - ∏ i ∈ S, b i‖ +
            ‖a x - b x‖ * ‖∏ i ∈ S, b i‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ max (C x) 1 *
              ((∑ i ∈ S, ‖a i - b i‖) *
                (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) +
            ‖a x - b x‖ * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1) :=
        add_le_add
          (mul_le_mul hx_bound htail (norm_nonneg _) (zero_le_one.trans (le_max_right _ _)))
          (mul_le_mul_of_nonneg_left hbtail (norm_nonneg _))
      _ ≤ max (C x) 1 *
              ((∑ i ∈ S, ‖a i - b i‖) *
                (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) +
            max (C x) 1 *
              (‖a x - b x‖ * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (C i) 1)) := by
        exact add_le_add_right hdiffx_term _
      _ = (∑ i ∈ insert x S, ‖a i - b i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i ∈ insert x S, max (C i) 1) := by
        rw [Finset.sum_insert hx, Finset.prod_insert hx]
        ring

/-- A two-factor product is pointwise Lipschitz on bounded left/right factors.  The asymmetric
form matches the standard split `a * b - c * d = a * (b - d) + (a - c) * d`. -/
theorem norm_mul_sub_mul_le {A : Type*} [NormedRing A] {B D : ℝ} {a b c d : A}
    (ha : ‖a‖ ≤ B) (hd : ‖d‖ ≤ D) :
    ‖a * b - c * d‖ ≤ B * ‖b - d‖ + D * ‖a - c‖ := by
  have hsplit : a * b - c * d = a * (b - d) + (a - c) * d := by
    noncomm_ring
  calc
    ‖a * b - c * d‖ = ‖a * (b - d) + (a - c) * d‖ := by
      rw [hsplit]
    _ ≤ ‖a * (b - d)‖ + ‖(a - c) * d‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖b - d‖ + ‖a - c‖ * ‖d‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ B * ‖b - d‖ + ‖a - c‖ * D := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    _ = B * ‖b - d‖ + D * ‖a - c‖ := by
      ring

/-- A finite sum of two-factor products is pointwise Lipschitz on bounded left/right factors. -/
theorem norm_finset_sum_mul_sub_sum_mul_le {ι A : Type*} [NormedRing A]
    (S : Finset ι) {B D : ι → ℝ} {a b c d : ι → A}
    (ha : ∀ i ∈ S, ‖a i‖ ≤ B i) (hd : ∀ i ∈ S, ‖d i‖ ≤ D i) :
    ‖(∑ i ∈ S, a i * b i) - ∑ i ∈ S, c i * d i‖ ≤
      ∑ i ∈ S, (B i * ‖b i - d i‖ + D i * ‖a i - c i‖) := by
  classical
  calc
    ‖(∑ i ∈ S, a i * b i) - ∑ i ∈ S, c i * d i‖ =
        ‖∑ i ∈ S, (a i * b i - c i * d i)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ S, ‖a i * b i - c i * d i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (B i * ‖b i - d i‖ + D i * ‖a i - c i‖) :=
      Finset.sum_le_sum fun i hi => norm_mul_sub_mul_le (ha i hi) (hd i hi)

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

theorem zsmul (n : ℤ) (hu : ParabolicHolderWith C α u s) :
    ParabolicHolderWith (‖n‖ * C) α (fun z => n • u z) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsub : n • u p - n • u q = n • (u p - u q) := by
    rw [zsmul_sub]
  calc
    ‖n • u p - n • u q‖ = ‖n • (u p - u q)‖ := by rw [hsub]
    _ ≤ ‖n‖ * ‖u p - u q‖ := norm_zsmul_le n (u p - u q)
    _ ≤ ‖n‖ * (C * dα) := mul_le_mul_of_nonneg_left (hu hp hq) (norm_nonneg n)
    _ = (‖n‖ * C) * dα := by ring

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

/-- Componentwise finite parabolic Holder estimates package as a Pi-valued Holder estimate with
summed constants. -/
theorem pi {ι : Type*} [Fintype ι] {C : ι → ℝ} {u : ℝ × X → ι → E}
    (hC : ∀ i, 0 ≤ C i)
    (h : ∀ i, ParabolicHolderWith (C i) α (fun z => u z i) s) :
    ParabolicHolderWith (∑ i, C i) α u s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hdα : 0 ≤ dα := Real.rpow_nonneg (parabolicDistance.nonneg p q) α
  have hCsum_nonneg : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _hi => hC i
  have hC_le_sum : ∀ i, C i ≤ ∑ j, C j := by
    intro i
    exact Finset.single_le_sum (fun j _hj => hC j) (Finset.mem_univ i)
  have htarget_nonneg : 0 ≤ (∑ i, C i) * dα := mul_nonneg hCsum_nonneg hdα
  exact (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => by
    have hcomp : ‖u p i - u q i‖ ≤ C i * dα := h i hp hq
    have hscale : C i * dα ≤ (∑ j, C j) * dα :=
      mul_le_mul_of_nonneg_right (hC_le_sum i) hdα
    simpa [Pi.sub_apply, dα] using hcomp.trans hscale

/-- A Pi-valued parabolic Holder estimate restricts to each component with the same constant. -/
theorem eval {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ParabolicHolderWith C α u s) (i : ι) :
    ParabolicHolderWith C α (fun z => u z i) s := by
  intro p hp q hq
  calc
    ‖u p i - u q i‖ = ‖(u p - u q) i‖ := by simp [Pi.sub_apply]
    _ ≤ ‖u p - u q‖ := norm_le_pi_norm (u p - u q) i
    _ ≤ C * (parabolicDistance p q) ^ α := h hp hq

/-- Products of normed-ring-valued functions preserve parabolic Holder control when the two
factors are separately bounded. -/
theorem mul {A : Type*} [NormedRing A] {B₁ B₂ H₁ H₂ α : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicHolderWith H₁ α u s)
    (hv : ParabolicHolderWith H₂ α v s)
    (hBu : ParabolicBoundedWith B₁ u s)
    (hBv : ParabolicBoundedWith B₂ v s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicHolderWith (B₁ * H₂ + B₂ * H₁) α (fun z => u z * v z) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsplit :
      u p * v p - u q * v q = u p * (v p - v q) + (u p - u q) * v q := by
    noncomm_ring
  have hH₁d_nonneg : 0 ≤ H₁ * dα :=
    (norm_nonneg (u p - u q)).trans (hu hp hq)
  calc
    ‖u p * v p - u q * v q‖ =
        ‖u p * (v p - v q) + (u p - u q) * v q‖ := by rw [hsplit]
    _ ≤ ‖u p * (v p - v q)‖ + ‖(u p - u q) * v q‖ := norm_add_le _ _
    _ ≤ ‖u p‖ * ‖v p - v q‖ + ‖u p - u q‖ * ‖v q‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ B₁ * (H₂ * dα) + (H₁ * dα) * B₂ :=
      add_le_add
        (mul_le_mul (hBu hp) (hv hp hq) (norm_nonneg _) hB₁)
        (mul_le_mul (hu hp hq) (hBv hq) (norm_nonneg _) hH₁d_nonneg)
    _ = (B₁ * H₂ + B₂ * H₁) * dα := by ring

/-- Product differences inherit parabolic Holder control from one left factor, one right factor,
and Holder controls of the two factor differences. -/
theorem mul_sub_mul {A : Type*} [NormedRing A]
    {Bu Hu Bv Hv Bdu Hdu Bdv Hdv α : ℝ}
    {u u' v v' : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicHolderWith Hu α u s)
    (hv' : ParabolicHolderWith Hv α v' s)
    (hdu : ParabolicHolderWith Hdu α (fun z => u z - u' z) s)
    (hdv : ParabolicHolderWith Hdv α (fun z => v z - v' z) s)
    (hBu : ParabolicBoundedWith Bu u s)
    (hBv' : ParabolicBoundedWith Bv v' s)
    (hBdu : ParabolicBoundedWith Bdu (fun z => u z - u' z) s)
    (hBdv : ParabolicBoundedWith Bdv (fun z => v z - v' z) s)
    (hBu_nonneg : 0 ≤ Bu) (hBdu_nonneg : 0 ≤ Bdu) :
    ParabolicHolderWith ((Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu)) α
      (fun z => u z * v z - u' z * v' z) s := by
  have hleft :
      ParabolicHolderWith (Bu * Hdv + Bdv * Hu) α
        (fun z => u z * (v z - v' z)) s :=
    hu.mul hdv hBu hBdv hBu_nonneg
  have hright :
      ParabolicHolderWith (Bdu * Hv + Bv * Hdu) α
        (fun z => (u z - u' z) * v' z) s :=
    hdu.mul hv' hBdu hBv' hBdu_nonneg
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  noncomm_ring

theorem inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ} {a : ℝ × X → 𝕜}
    (ha : ParabolicHolderWith C α a s) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicHolderWith (δ⁻¹ * C * δ⁻¹) α (fun z => (a z)⁻¹) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hp_norm_pos : 0 < ‖a p‖ := lt_of_lt_of_le hδpos (hδ hp)
  have hq_norm_pos : 0 < ‖a q‖ := lt_of_lt_of_le hδpos (hδ hq)
  have hp_ne : a p ≠ 0 := norm_pos_iff.mp hp_norm_pos
  have hq_ne : a q ≠ 0 := norm_pos_iff.mp hq_norm_pos
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hinvp : ‖(a p)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hp_norm_pos hδpos).2 (hδ hp)
  have hinvq : ‖(a q)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hq_norm_pos hδpos).2 (hδ hq)
  have hholder : ‖a p - a q‖ ≤ C * dα := ha hp hq
  have hCd_nonneg : 0 ≤ C * dα := (norm_nonneg (a p - a q)).trans hholder
  have hsplit :
      (a p)⁻¹ - (a q)⁻¹ = -((a p)⁻¹ * (a p - a q) * (a q)⁻¹) := by
    field_simp [hp_ne, hq_ne]
    ring
  calc
    ‖(a p)⁻¹ - (a q)⁻¹‖ =
        ‖-((a p)⁻¹ * (a p - a q) * (a q)⁻¹)‖ := by rw [hsplit]
    _ = ‖(a p)⁻¹ * (a p - a q) * (a q)⁻¹‖ := norm_neg _
    _ ≤ ‖(a p)⁻¹‖ * ‖a p - a q‖ * ‖(a q)⁻¹‖ := by
      calc
        ‖(a p)⁻¹ * (a p - a q) * (a q)⁻¹‖
            ≤ ‖(a p)⁻¹ * (a p - a q)‖ * ‖(a q)⁻¹‖ := norm_mul_le _ _
        _ ≤ (‖(a p)⁻¹‖ * ‖a p - a q‖) * ‖(a q)⁻¹‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ δ⁻¹ * (C * dα) * δ⁻¹ := by
      have hleft :
          ‖(a p)⁻¹‖ * ‖a p - a q‖ ≤ δ⁻¹ * (C * dα) :=
        mul_le_mul hinvp hholder (norm_nonneg _) hinvδ_nonneg
      exact mul_le_mul hleft hinvq (norm_nonneg _) (mul_nonneg hinvδ_nonneg hCd_nonneg)
    _ = (δ⁻¹ * C * δ⁻¹) * dα := by ring

/-- Reciprocal differences inherit parabolic Holder control from the difference of the inputs,
under a common pointwise lower bound. -/
theorem inv_sub_inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ}
    {a b : ℝ × X → 𝕜} {Ha Hb Bd Hd α : ℝ}
    (ha : ParabolicHolderWith Ha α a s)
    (hb : ParabolicHolderWith Hb α b s)
    (hdiff : ParabolicHolderWith Hd α (fun z => a z - b z) s)
    (hbdiff : ParabolicBoundedWith Bd (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖)
    (hBd : 0 ≤ Bd) :
    ParabolicHolderWith
      ((δ⁻¹ * Bd) * (δ⁻¹ * Hb * δ⁻¹) +
        δ⁻¹ * (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹))) α
      (fun z => (a z)⁻¹ - (b z)⁻¹) s := by
  have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hainv :
      ParabolicHolderWith (δ⁻¹ * Ha * δ⁻¹) α (fun z => (a z)⁻¹) s :=
    ha.inv hδpos hδa
  have hbinv :
      ParabolicHolderWith (δ⁻¹ * Hb * δ⁻¹) α (fun z => (b z)⁻¹) s :=
    hb.inv hδpos hδb
  have hainv_bounded :
      ParabolicBoundedWith δ⁻¹ (fun z => (a z)⁻¹) s := by
    intro p hp
    have hp_norm_pos : 0 < ‖a p‖ := lt_of_lt_of_le hδpos (hδa hp)
    rw [norm_inv]
    exact (inv_le_inv₀ hp_norm_pos hδpos).2 (hδa hp)
  have hbinv_bounded :
      ParabolicBoundedWith δ⁻¹ (fun z => (b z)⁻¹) s := by
    intro p hp
    have hp_norm_pos : 0 < ‖b p‖ := lt_of_lt_of_le hδpos (hδb hp)
    rw [norm_inv]
    exact (inv_le_inv₀ hp_norm_pos hδpos).2 (hδb hp)
  have hleft :
      ParabolicHolderWith (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹)) α
        (fun z => (a z)⁻¹ * (a z - b z)) s :=
    hainv.mul hdiff hainv_bounded hbdiff hδinv_nonneg
  have hleft_bounded :
      ParabolicBoundedWith (δ⁻¹ * Bd) (fun z => (a z)⁻¹ * (a z - b z)) s := by
    intro p hp
    exact (norm_mul_le ((a p)⁻¹) (a p - b p)).trans
      (mul_le_mul (hainv_bounded hp) (hbdiff hp) (norm_nonneg _) hδinv_nonneg)
  have hleftB_nonneg : 0 ≤ δ⁻¹ * Bd := mul_nonneg hδinv_nonneg hBd
  have hprod :
      ParabolicHolderWith
        ((δ⁻¹ * Bd) * (δ⁻¹ * Hb * δ⁻¹) +
          δ⁻¹ * (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹))) α
        (fun z => ((a z)⁻¹ * (a z - b z)) * (b z)⁻¹) s :=
    hleft.mul hbinv hleft_bounded hbinv_bounded hleftB_nonneg
  have hneg := hprod.neg
  have hpoint : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      (a z)⁻¹ - (b z)⁻¹ = -(((a z)⁻¹ * (a z - b z)) * (b z)⁻¹) := by
    intro z hz
    have ha_ne : a z ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδpos (hδa hz))
    have hb_ne : b z ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδpos (hδb hz))
    field_simp [ha_ne, hb_ne]
    ring
  intro p hp q hq
  change ‖((a p)⁻¹ - (b p)⁻¹) - ((a q)⁻¹ - (b q)⁻¹)‖ ≤
    ((δ⁻¹ * Bd) * (δ⁻¹ * Hb * δ⁻¹) +
      δ⁻¹ * (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹))) * parabolicDistance p q ^ α
  rw [hpoint hp, hpoint hq]
  simpa using hneg hp hq

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

/-- Variable scalar action preserves parabolic Holder control when the scalar and vector
fields are separately bounded. -/
theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {B₁ B₂ H₁ H₂ α : ℝ} {a : ℝ × X → 𝕜} {u : ℝ × X → F}
    {s : Set (ℝ × X)}
    (ha : ParabolicHolderWith H₁ α a s)
    (hu : ParabolicHolderWith H₂ α u s)
    (hBa : ParabolicBoundedWith B₁ a s)
    (hBu : ParabolicBoundedWith B₂ u s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicHolderWith (B₁ * H₂ + B₂ * H₁) α (fun z => a z • u z) s := by
  intro p hp q hq
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
    (norm_nonneg (a p - a q)).trans (ha hp hq)
  calc
    ‖a p • u p - a q • u q‖ =
        ‖a p • (u p - u q) + (a p - a q) • u q‖ := by rw [hsplit]
    _ ≤ ‖a p • (u p - u q)‖ + ‖(a p - a q) • u q‖ := norm_add_le _ _
    _ = ‖a p‖ * ‖u p - u q‖ + ‖a p - a q‖ * ‖u q‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ B₁ * (H₂ * dα) + (H₁ * dα) * B₂ :=
      add_le_add
        (mul_le_mul (hBa hp) (hu hp hq) (norm_nonneg _) hB₁)
        (mul_le_mul (ha hp hq) (hBu hq) (norm_nonneg _) hH₁d_nonneg)
    _ = (B₁ * H₂ + B₂ * H₁) * dα := by ring

/-- A continuous linear map preserves parabolic Holder control, with the operator norm multiplying
the Holder constant. -/
theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicHolderWith C α u s) :
    ParabolicHolderWith (‖L‖ * C) α (fun z => L (u z)) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  calc
    ‖L (u p) - L (u q)‖ = ‖L (u p - u q)‖ := by rw [← map_sub]
    _ ≤ ‖L‖ * ‖u p - u q‖ := ContinuousLinearMap.le_opNorm L (u p - u q)
    _ ≤ ‖L‖ * (C * dα) :=
      mul_le_mul_of_nonneg_left (hu hp hq) (norm_nonneg L)
    _ = (‖L‖ * C) * dα := by ring

/-- A curried continuous bilinear map preserves parabolic Holder control when the two
inputs are separately bounded.  This is the standalone Holder part of the product-rule
estimate used by parabolic `C^{0,α}` calculus. -/
theorem continuousLinearMap₂ {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {B Bv Hv : ℝ} {v : ℝ × X → F}
    (L : E →L[ℝ] F →L[ℝ] G)
    (hu : ParabolicHolderWith C α u s)
    (hv : ParabolicHolderWith Hv α v s)
    (hBu : ParabolicBoundedWith B u s)
    (hBv : ParabolicBoundedWith Bv v s)
    (hB : 0 ≤ B) :
    ParabolicHolderWith (‖L‖ * (B * Hv + Bv * C)) α
      (fun z => L (u z) (v z)) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsplit :
      L (u p) (v p) - L (u q) (v q) =
        L (u p) (v p - v q) + L (u p - u q) (v q) := by
    simp [map_sub]
  have hLup : ‖L (u p)‖ ≤ ‖L‖ * B :=
    (ContinuousLinearMap.le_opNorm L (u p)).trans
      (mul_le_mul_of_nonneg_left (hBu hp) (norm_nonneg L))
  have hLup_nonneg : 0 ≤ ‖L‖ * B := mul_nonneg (norm_nonneg L) hB
  have hCd_nonneg : 0 ≤ C * dα :=
    (norm_nonneg (u p - u q)).trans (hu hp hq)
  have hLdiff : ‖L (u p - u q)‖ ≤ ‖L‖ * (C * dα) :=
    (ContinuousLinearMap.le_opNorm L (u p - u q)).trans
      (mul_le_mul_of_nonneg_left (hu hp hq) (norm_nonneg L))
  have hLdiff_nonneg : 0 ≤ ‖L‖ * (C * dα) :=
    mul_nonneg (norm_nonneg L) hCd_nonneg
  calc
    ‖L (u p) (v p) - L (u q) (v q)‖
        = ‖L (u p) (v p - v q) + L (u p - u q) (v q)‖ := by rw [hsplit]
    _ ≤ ‖L (u p) (v p - v q)‖ + ‖L (u p - u q) (v q)‖ := norm_add_le _ _
    _ ≤ ‖L (u p)‖ * ‖v p - v q‖ + ‖L (u p - u q)‖ * ‖v q‖ :=
        add_le_add
          (ContinuousLinearMap.le_opNorm (L (u p)) (v p - v q))
          (ContinuousLinearMap.le_opNorm (L (u p - u q)) (v q))
    _ ≤ (‖L‖ * B) * (Hv * dα) + (‖L‖ * (C * dα)) * Bv :=
        add_le_add
          (mul_le_mul hLup (hv hp hq) (norm_nonneg _) hLup_nonneg)
          (mul_le_mul hLdiff (hBv hq) (norm_nonneg _) hLdiff_nonneg)
    _ = (‖L‖ * (B * Hv + Bv * C)) * dα := by ring

/-- Differences of curried continuous bilinear-map applications inherit parabolic Holder control
from one left input, one right input, and Holder controls of the two input differences. -/
theorem continuousLinearMap₂_sub {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {Bu Hu Bv Hv Bdu Hdu Bdv Hdv : ℝ}
    {u u' : ℝ × X → E} {v v' : ℝ × X → F}
    (hu : ParabolicHolderWith Hu α u s)
    (hv' : ParabolicHolderWith Hv α v' s)
    (hdu : ParabolicHolderWith Hdu α (fun z => u z - u' z) s)
    (hdv : ParabolicHolderWith Hdv α (fun z => v z - v' z) s)
    (hBu : ParabolicBoundedWith Bu u s)
    (hBv' : ParabolicBoundedWith Bv v' s)
    (hBdu : ParabolicBoundedWith Bdu (fun z => u z - u' z) s)
    (hBdv : ParabolicBoundedWith Bdv (fun z => v z - v' z) s)
    (hBu_nonneg : 0 ≤ Bu) (hBdu_nonneg : 0 ≤ Bdu) :
    ParabolicHolderWith
      (‖L‖ * (Bu * Hdv + Bdv * Hu) + ‖L‖ * (Bdu * Hv + Bv * Hdu)) α
      (fun z => L (u z) (v z) - L (u' z) (v' z)) s := by
  have hleft :
      ParabolicHolderWith (‖L‖ * (Bu * Hdv + Bdv * Hu)) α
        (fun z => L (u z) (v z - v' z)) s :=
    hu.continuousLinearMap₂ L hdv hBu hBdv hBu_nonneg
  have hright :
      ParabolicHolderWith (‖L‖ * (Bdu * Hv + Bv * Hdu)) α
        (fun z => L (u z - u' z) (v' z)) s :=
    hdu.continuousLinearMap₂ L hv' hBdu hBv' hBdu_nonneg
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  simp [map_sub]

/-- Applying an operator-valued function to a vector-valued function preserves parabolic Holder
control when the operator and vector fields are separately bounded. -/
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A : ℝ × X → E →L[ℝ] F} {v : ℝ × X → E}
    {BA HA Bv Hv : ℝ}
    (hA : ParabolicHolderWith HA α A s)
    (hv : ParabolicHolderWith Hv α v s)
    (hAb : ParabolicBoundedWith BA A s)
    (hvb : ParabolicBoundedWith Bv v s)
    (hBA : 0 ≤ BA) :
    ParabolicHolderWith (BA * Hv + Bv * HA) α (fun z => A z (v z)) s := by
  intro p hp q hq
  let dα := (parabolicDistance p q) ^ α
  have hsplit :
      A p (v p) - A q (v q) =
        A p (v p - v q) + (A p - A q) (v q) := by
    simp [map_sub]
  have hHAd_nonneg : 0 ≤ HA * dα :=
    (norm_nonneg (A p - A q)).trans (hA hp hq)
  calc
    ‖A p (v p) - A q (v q)‖ =
        ‖A p (v p - v q) + (A p - A q) (v q)‖ := by rw [hsplit]
    _ ≤ ‖A p (v p - v q)‖ + ‖(A p - A q) (v q)‖ := norm_add_le _ _
    _ ≤ ‖A p‖ * ‖v p - v q‖ + ‖A p - A q‖ * ‖v q‖ :=
        add_le_add
          (ContinuousLinearMap.le_opNorm (A p) (v p - v q))
          (ContinuousLinearMap.le_opNorm (A p - A q) (v q))
    _ ≤ BA * (Hv * dα) + (HA * dα) * Bv :=
        add_le_add
          (mul_le_mul (hAb hp) (hv hp hq) (norm_nonneg _) hBA)
          (mul_le_mul (hA hp hq) (hvb hq) (norm_nonneg _) hHAd_nonneg)
    _ = (BA * Hv + Bv * HA) * dα := by ring

/-- Differences of operator-valued applications inherit parabolic Holder control from one
operator input, one vector input, and Holder controls of the operator and vector differences. -/
theorem continuousLinearMap_apply_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A A' : ℝ × X → E →L[ℝ] F} {v v' : ℝ × X → E}
    {BA HA Bv Hv BAd HAd Bvd Hvd : ℝ}
    (hA : ParabolicHolderWith HA α A s)
    (hv' : ParabolicHolderWith Hv α v' s)
    (hAdiff : ParabolicHolderWith HAd α (fun z => A z - A' z) s)
    (hvdiff : ParabolicHolderWith Hvd α (fun z => v z - v' z) s)
    (hAb : ParabolicBoundedWith BA A s)
    (hvb' : ParabolicBoundedWith Bv v' s)
    (hAdb : ParabolicBoundedWith BAd (fun z => A z - A' z) s)
    (hvdb : ParabolicBoundedWith Bvd (fun z => v z - v' z) s)
    (hBA : 0 ≤ BA) (hBAd : 0 ≤ BAd) :
    ParabolicHolderWith ((BA * Hvd + Bvd * HA) + (BAd * Hv + Bv * HAd)) α
      (fun z => A z (v z) - A' z (v' z)) s := by
  have hleft :
      ParabolicHolderWith (BA * Hvd + Bvd * HA) α
        (fun z => A z (v z - v' z)) s :=
    hA.continuousLinearMap_apply hvdiff hAb hvdb hBA
  have hright :
      ParabolicHolderWith (BAd * Hv + Bv * HAd) α
        (fun z => (A z - A' z) (v' z)) s :=
    hAdiff.continuousLinearMap_apply hv' hAdb hvb' hBAd
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  simp [map_sub]

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

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicHolderWith C α u s) (hφ : LipschitzWith K φ) :
    ParabolicHolderWith ((K : ℝ) * C) α (fun z => φ (u z)) s :=
  hu.comp_lipschitzOnWith hφ.lipschitzOnWith

/-- A spatial Holder estimate on the spatial projection lifts to the same parabolic Holder
estimate for the time-independent time-space function. -/
theorem of_snd_holder (hC : 0 ≤ C) (hα : 0 ≤ α) {f : X → E}
    (hf : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄, y ∈ Prod.snd '' s →
      ‖f x - f y‖ ≤ C * (dist x y) ^ α) :
    ParabolicHolderWith C α (fun z : ℝ × X => f z.2) s := by
  intro p hp q hq
  have hpim : p.2 ∈ Prod.snd '' s := ⟨p, hp, rfl⟩
  have hqim : q.2 ∈ Prod.snd '' s := ⟨q, hq, rfl⟩
  have hpow :
      (dist p.2 q.2) ^ α ≤ (parabolicDistance p q) ^ α :=
    Real.rpow_le_rpow dist_nonneg (parabolicDistance.space_dist_le p q) hα
  exact (hf hpim hqim).trans (mul_le_mul_of_nonneg_left hpow hC)

/-- A spatial Lipschitz function, lifted as a time-independent time-space function, is
parabolic Lipschitz on the time-space set. -/
theorem of_snd_lipschitzOnWith {K : ℝ≥0} {f : X → E}
    (hf : LipschitzOnWith K f (Prod.snd '' s)) :
    ParabolicHolderWith (K : ℝ) 1 (fun z : ℝ × X => f z.2) s := by
  intro p hp q hq
  have hpim : p.2 ∈ Prod.snd '' s := ⟨p, hp, rfl⟩
  have hqim : q.2 ∈ Prod.snd '' s := ⟨q, hq, rfl⟩
  calc
    ‖f p.2 - f q.2‖ = dist (f p.2) (f q.2) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist p.2 q.2 := hf.dist_le_mul p.2 hpim q.2 hqim
    _ ≤ (K : ℝ) * parabolicDistance p q :=
        mul_le_mul_of_nonneg_left (parabolicDistance.space_dist_le p q) (NNReal.coe_nonneg K)
    _ = (K : ℝ) * (parabolicDistance p q) ^ (1 : ℝ) := by rw [Real.rpow_one]

/-- A time-only Holder estimate with exponent `α / 2` lifts to parabolic Holder control with
exponent `α`. -/
theorem of_fst_holder (hC : 0 ≤ C) (hα : 0 ≤ α) {f : ℝ → E}
    (hf : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄, τ ∈ Prod.fst '' s →
      ‖f t - f τ‖ ≤ C * |t - τ| ^ (α / 2)) :
    ParabolicHolderWith C α (fun z : ℝ × X => f z.1) s := by
  intro p hp q hq
  have hpim : p.1 ∈ Prod.fst '' s := ⟨p, hp, rfl⟩
  have hqim : q.1 ∈ Prod.fst '' s := ⟨q, hq, rfl⟩
  have hpow :
      |p.1 - q.1| ^ (α / 2) ≤ (parabolicDistance p q) ^ α := by
    have hsqrt :
        (Real.sqrt |p.1 - q.1|) ^ α ≤ (parabolicDistance p q) ^ α :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (parabolicDistance.sqrt_time_le p q) hα
    simpa [Real.rpow_div_two_eq_sqrt α (abs_nonneg (p.1 - q.1))] using hsqrt
  exact (hf hpim hqim).trans (mul_le_mul_of_nonneg_left hpow hC)

/-- A time-only Lipschitz function lifts to parabolic Holder control with exponent `2`. -/
theorem of_fst_lipschitzOnWith {K : ℝ≥0} {f : ℝ → E}
    (hf : LipschitzOnWith K f (Prod.fst '' s)) :
    ParabolicHolderWith (K : ℝ) 2 (fun z : ℝ × X => f z.1) s := by
  intro p hp q hq
  have hpim : p.1 ∈ Prod.fst '' s := ⟨p, hp, rfl⟩
  have hqim : q.1 ∈ Prod.fst '' s := ⟨q, hq, rfl⟩
  have htime :
      |p.1 - q.1| ≤ (parabolicDistance p q) ^ 2 :=
    parabolicDistance.time_abs_le_sq_of_le (parabolicDistance.nonneg p q) le_rfl
  calc
    ‖f p.1 - f q.1‖ = dist (f p.1) (f q.1) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist p.1 q.1 := hf.dist_le_mul p.1 hpim q.1 hqim
    _ = (K : ℝ) * |p.1 - q.1| := by rw [Real.dist_eq]
    _ ≤ (K : ℝ) * (parabolicDistance p q) ^ 2 :=
      mul_le_mul_of_nonneg_left htime (NNReal.coe_nonneg K)
    _ = (K : ℝ) * (parabolicDistance p q) ^ (2 : ℝ) := by rw [Real.rpow_two]

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

/-- Local-to-global parabolic Holder control from a product-parabolic-cylinder cover.  If `K` is
covered by product cylinders and each doubled closed cylinder carries the same local Holder
constant, then `u` has a global Holder constant on `K`. -/
theorem of_parabolicCylinder_cover_closedCylinder {B timeRadius spaceRadius : ℝ}
    {K N : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y timeRadius spaceRadius)
    (hlocal : ∀ y ∈ N, ParabolicHolderWith C α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicHolderWith
      (max C (2 * B / (min (Real.sqrt timeRadius) spaceRadius) ^ α)) α u K := by
  intro p hp q hq
  let r : ℝ := min (Real.sqrt timeRadius) spaceRadius
  let D : ℝ := max C (2 * B / r ^ α)
  change ‖u p - u q‖ ≤ D * (parabolicDistance p q) ^ α
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (Real.sqrt_pos_of_pos htime) hspace
  let d : ℝ := parabolicDistance p q
  change ‖u p - u q‖ ≤ D * d ^ α
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  by_cases hsmall : d < r
  · rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
    have hpclosed : p ∈ parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius) :=
      parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
    have hqclosed : q ∈ parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius) := by
      exact parabolicCylinder.mem_closedCylinder_two_of_mem_of_parabolicDistance_lt_min_sqrt
        hpcy (by simpa [d, r] using hsmall)
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

/-- Compact local-to-global parabolic Holder control from uniform local doubled closed-cylinder
estimates. -/
theorem of_isCompact_of_uniform_local_closedCylinder {B timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hK : IsCompact K) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hlocal : ∀ y ∈ K, ParabolicHolderWith C α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicHolderWith
      (max C (2 * B / (min (Real.sqrt timeRadius) spaceRadius) ^ α)) α u K := by
  rcases parabolicCylinder.exists_finite_cover_of_isCompact hK htime hspace with
    ⟨N, hNK, _hNfinite, hcover⟩
  exact of_parabolicCylinder_cover_closedCylinder hbounded hα htime hspace hcover
    (fun y hy => hlocal y (hNK hy))

/-- Local-to-global parabolic Holder control from a finite cover by variable-radius parabolic
balls, when every doubled closed ball carries the same local Holder constant.  The global constant
is the sum of the local constant and the far-pair boundedness constant over the selected cover. -/
theorem of_finset_parabolicBall_cover_closedBall_variable {B : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (R : ℝ × X → ℝ)
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (hRpos : ∀ y ∈ N, 0 < R y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y (R y))
    (hlocal : ∀ y ∈ N, ParabolicHolderWith C α u (parabolicClosedBall y (2 * R y))) :
    ParabolicHolderWith (∑ y ∈ N, max C (2 * B / (R y) ^ α)) α u K := by
  intro p hp q hq
  let d : ℝ := parabolicDistance p q
  let D : ℝ := ∑ y ∈ N, max C (2 * B / (R y) ^ α)
  change ‖u p - u q‖ ≤ D * d ^ α
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  have hBnonneg : 0 ≤ B := (norm_nonneg (u p)).trans (hbounded hp)
  have hterm_nonneg : ∀ y ∈ N, 0 ≤ max C (2 * B / (R y) ^ α) := by
    intro y hy
    have hRy : 0 < R y := hRpos y hy
    have hrpow_pos : 0 < (R y) ^ α := Real.rpow_pos_of_pos hRy α
    have hfar_nonneg : 0 ≤ 2 * B / (R y) ^ α :=
      div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
    exact hfar_nonneg.trans (le_max_right _ _)
  have hterm_le_D : ∀ y ∈ N, max C (2 * B / (R y) ^ α) ≤ D := by
    intro y hy
    dsimp [D]
    exact Finset.single_le_sum hterm_nonneg hy
  rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
  have hRy : 0 < R y := hRpos y hyN
  have htermD : max C (2 * B / (R y) ^ α) ≤ D := hterm_le_D y hyN
  have hRy_le_two : R y ≤ 2 * R y := by linarith
  have hpclosed : p ∈ parabolicClosedBall y (2 * R y) :=
    (le_of_lt hpball).trans hRy_le_two
  have hpoint : ‖u p - u q‖ ≤ max C (2 * B / (R y) ^ α) * d ^ α := by
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
      have hlocalpq : ‖u p - u q‖ ≤ C * d ^ α := by
        simpa [d] using hlocal y hyN hpclosed hqclosed
      exact hlocalpq.trans
        (mul_le_mul_of_nonneg_right (le_max_left C (2 * B / (R y) ^ α))
          (Real.rpow_nonneg hd0 α))
    · have hfar : R y ≤ d := le_of_not_gt hsmall
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
      have hfar_bound : 2 * B ≤ max C (2 * B / (R y) ^ α) * d ^ α := by
        calc
          2 * B = (2 * B / (R y) ^ α) * (R y) ^ α := by
            rw [div_mul_cancel₀ _ hrpow_pos.ne']
          _ ≤ (2 * B / (R y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_left hrpow_le_dpow hcoef_nonneg
          _ ≤ max C (2 * B / (R y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right C (2 * B / (R y) ^ α))
              (Real.rpow_nonneg hd0 α)
      exact hdiff.trans hfar_bound
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right htermD (Real.rpow_nonneg hd0 α))

/-- Local-to-global parabolic Holder control from a finite cover by variable-radius product
parabolic cylinders, when every doubled closed cylinder carries the same local Holder constant. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder_variable {B : ℝ}
    {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hlocal : ∀ y ∈ N, ParabolicHolderWith C α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ParabolicHolderWith
      (∑ y ∈ N, max C
        (2 * B / (min (Real.sqrt (timeRadius y)) (spaceRadius y)) ^ α)) α u K := by
  intro p hp q hq
  let d : ℝ := parabolicDistance p q
  let r : ℝ × X → ℝ := fun y => min (Real.sqrt (timeRadius y)) (spaceRadius y)
  let D : ℝ := ∑ y ∈ N, max C (2 * B / (r y) ^ α)
  change ‖u p - u q‖ ≤ D * d ^ α
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  have hBnonneg : 0 ≤ B := (norm_nonneg (u p)).trans (hbounded hp)
  have hrpos : ∀ y ∈ N, 0 < r y := by
    intro y hy
    dsimp [r]
    exact lt_min (Real.sqrt_pos_of_pos (htime_pos y hy)) (hspace_pos y hy)
  have hterm_nonneg : ∀ y ∈ N, 0 ≤ max C (2 * B / (r y) ^ α) := by
    intro y hy
    have hry : 0 < r y := hrpos y hy
    have hrpow_pos : 0 < (r y) ^ α := Real.rpow_pos_of_pos hry α
    have hfar_nonneg : 0 ≤ 2 * B / (r y) ^ α :=
      div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
    exact hfar_nonneg.trans (le_max_right _ _)
  have hterm_le_D : ∀ y ∈ N, max C (2 * B / (r y) ^ α) ≤ D := by
    intro y hy
    dsimp [D]
    exact Finset.single_le_sum hterm_nonneg hy
  rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
  rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
  have hry : 0 < r y := hrpos y hyN
  have htermD : max C (2 * B / (r y) ^ α) ≤ D := hterm_le_D y hyN
  have hpclosed :
      p ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) :=
    parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
  have hpoint : ‖u p - u q‖ ≤ max C (2 * B / (r y) ^ α) * d ^ α := by
    by_cases hsmall : d < r y
    · have hqclosed :
          q ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) := by
        exact parabolicCylinder.mem_closedCylinder_two_of_mem_of_parabolicDistance_lt_min_sqrt
          hpcy (by simpa [d, r] using hsmall)
      have hlocalpq : ‖u p - u q‖ ≤ C * d ^ α := by
        simpa [d] using hlocal y hyN hpclosed hqclosed
      exact hlocalpq.trans
        (mul_le_mul_of_nonneg_right (le_max_left C (2 * B / (r y) ^ α))
          (Real.rpow_nonneg hd0 α))
    · have hfar : r y ≤ d := le_of_not_gt hsmall
      have hrpow_pos : 0 < (r y) ^ α := Real.rpow_pos_of_pos hry α
      have hrpow_le_dpow : (r y) ^ α ≤ d ^ α :=
        Real.rpow_le_rpow hry.le hfar hα.le
      have hcoef_nonneg : 0 ≤ 2 * B / (r y) ^ α :=
        div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
      have hdiff : ‖u p - u q‖ ≤ 2 * B := by
        calc
          ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hbounded hp) (hbounded hq)
          _ = 2 * B := by ring
      have hfar_bound : 2 * B ≤ max C (2 * B / (r y) ^ α) * d ^ α := by
        calc
          2 * B = (2 * B / (r y) ^ α) * (r y) ^ α := by
            rw [div_mul_cancel₀ _ hrpow_pos.ne']
          _ ≤ (2 * B / (r y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_left hrpow_le_dpow hcoef_nonneg
          _ ≤ max C (2 * B / (r y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right C (2 * B / (r y) ^ α))
              (Real.rpow_nonneg hd0 α)
      exact hdiff.trans hfar_bound
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right htermD (Real.rpow_nonneg hd0 α))

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

/-- Pullback of a parabolic Hölder estimate along a map `φ : ℝ × Y → ℝ × X` that expands
parabolic distance by at most a factor `L`.  This is the abstract change-of-variables /
reparametrization lemma behind parabolic scaling (the Schauder dilation argument): if `u`
is `α`-Hölder with constant `C` on `s`, and `φ` maps `t` into `s` with
`parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q`, then `u ∘ φ` is `α`-Hölder
with constant `C * L ^ α` on `t`. -/
theorem comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicHolderWith (C * L ^ α) α (fun p => u (φ p)) t := by
  intro p hp q hq
  have hbase : ‖u (φ p) - u (φ q)‖ ≤ C * (parabolicDistance (φ p) (φ q)) ^ α :=
    hu (hmaps hp) (hmaps hq)
  have hmono : (parabolicDistance (φ p) (φ q)) ^ α ≤ (L * parabolicDistance p q) ^ α :=
    Real.rpow_le_rpow (parabolicDistance.nonneg _ _) (hφ hp hq) hα
  have hsplit : (L * parabolicDistance p q) ^ α = L ^ α * (parabolicDistance p q) ^ α :=
    Real.mul_rpow hL (parabolicDistance.nonneg _ _)
  calc
    ‖u (φ p) - u (φ q)‖ ≤ C * (parabolicDistance (φ p) (φ q)) ^ α := hbase
    _ ≤ C * (L * parabolicDistance p q) ^ α := mul_le_mul_of_nonneg_left hmono hC
    _ = C * (L ^ α * (parabolicDistance p q) ^ α) := by rw [hsplit]
    _ = (C * L ^ α) * (parabolicDistance p q) ^ α := by ring

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

theorem zsmul (n : ℤ) (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => n • u z) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨‖n‖ * C, mul_nonneg (norm_nonneg n) hC, hCu.zsmul n⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {v : ℝ × X → F}
    (hu : ParabolicHolderOn α u s) (hv : ParabolicHolderOn α v s) :
    ParabolicHolderOn α (fun z => (u z, v z)) s := by
  rcases hu with ⟨C, hC, hCu⟩
  rcases hv with ⟨D, hD, hDv⟩
  exact ⟨max C D, hC.trans (le_max_left C D), hCu.prod hDv⟩

/-- Componentwise finite parabolic Holder control packages as Pi-valued Holder control. -/
theorem pi {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ∀ i, ParabolicHolderOn α (fun z => u z i) s) :
    ParabolicHolderOn α u s := by
  classical
  let C : ι → ℝ := fun i => Classical.choose (h i)
  have hCnonneg : ∀ i, 0 ≤ C i := by
    intro i
    dsimp [C]
    exact (Classical.choose_spec (h i)).1
  have hholder : ∀ i, ParabolicHolderWith (C i) α (fun z => u z i) s := by
    intro i
    dsimp [C]
    exact (Classical.choose_spec (h i)).2
  exact ⟨∑ i, C i, Finset.sum_nonneg fun i _hi => hCnonneg i,
    ParabolicHolderWith.pi hCnonneg hholder⟩

/-- A Pi-valued parabolic Holder estimate restricts to each component. -/
theorem eval {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ParabolicHolderOn α u s) (i : ι) :
    ParabolicHolderOn α (fun z => u z i) s := by
  rcases h with ⟨C, hC, hCu⟩
  exact ⟨C, hC, hCu.eval i⟩

theorem inv {𝕜 : Type*} [NormedField 𝕜] {a : ℝ × X → 𝕜} {δ : ℝ}
    (ha : ParabolicHolderOn α a s) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicHolderOn α (fun z => (a z)⁻¹) s := by
  rcases ha with ⟨C, hC, hCa⟩
  refine ⟨δ⁻¹ * C * δ⁻¹, ?_, hCa.inv hδpos hδ⟩
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hδpos.le) hC) (inv_nonneg.mpr hδpos.le)

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

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicHolderOn α u s) (hφ : LipschitzWith K φ) :
    ParabolicHolderOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨(K : ℝ) * C, mul_nonneg (NNReal.coe_nonneg K) hC,
    hCu.comp_lipschitzWith hφ⟩

/-- A continuous linear map preserves existential parabolic Holder control. -/
theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicHolderOn α u s) :
    ParabolicHolderOn α (fun z => L (u z)) s := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨‖L‖ * C, mul_nonneg (norm_nonneg L) hC, hCu.continuousLinearMap L⟩

/-- A spatial Holder estimate on the spatial projection lifts to parabolic Holder control for
the time-independent time-space function. -/
theorem of_snd_holder {C : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α) {f : X → E}
    (hf : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄, y ∈ Prod.snd '' s →
      ‖f x - f y‖ ≤ C * (dist x y) ^ α) :
    ParabolicHolderOn α (fun z : ℝ × X => f z.2) s :=
  ⟨C, hC, ParabolicHolderWith.of_snd_holder hC hα hf⟩

/-- A spatial Lipschitz function, lifted as a time-independent time-space function, is
parabolic Holder with exponent `1`. -/
theorem of_snd_lipschitzOnWith {K : ℝ≥0} {f : X → E}
    (hf : LipschitzOnWith K f (Prod.snd '' s)) :
    ParabolicHolderOn 1 (fun z : ℝ × X => f z.2) s :=
  ⟨(K : ℝ), NNReal.coe_nonneg K, ParabolicHolderWith.of_snd_lipschitzOnWith hf⟩

/-- A time-only Holder estimate with exponent `α / 2` lifts to existential parabolic Holder
control with exponent `α`. -/
theorem of_fst_holder {C : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α) {f : ℝ → E}
    (hf : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄, τ ∈ Prod.fst '' s →
      ‖f t - f τ‖ ≤ C * |t - τ| ^ (α / 2)) :
    ParabolicHolderOn α (fun z : ℝ × X => f z.1) s :=
  ⟨C, hC, ParabolicHolderWith.of_fst_holder hC hα hf⟩

/-- A time-only Lipschitz function lifts to existential parabolic Holder control with exponent
`2`. -/
theorem of_fst_lipschitzOnWith {K : ℝ≥0} {f : ℝ → E}
    (hf : LipschitzOnWith K f (Prod.fst '' s)) :
    ParabolicHolderOn 2 (fun z : ℝ × X => f z.1) s :=
  ⟨(K : ℝ), NNReal.coe_nonneg K, ParabolicHolderWith.of_fst_lipschitzOnWith hf⟩

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

/-- Local-to-global parabolic Holder control from a finite product-parabolic-cylinder cover, with
local Holder constants chosen automatically and summed over the finite cover. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder {B timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hbounded : ParabolicBoundedWith B u K)
    (hα : 0 < α) (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y timeRadius spaceRadius)
    (hlocal : ∀ y ∈ N, ParabolicHolderOn α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
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
      ∀ y ∈ N, ParabolicHolderWith (Hc y) α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius)) := by
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
      ∀ y ∈ N, ParabolicHolderWith Hsum α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius)) := by
    intro y hy
    exact (hH y hy).mono_const (hH_le_sum y hy)
  refine ⟨max Hsum (2 * B / (min (Real.sqrt timeRadius) spaceRadius) ^ α),
    hHsum_nonneg.trans (le_max_left _ _), ?_⟩
  exact ParabolicHolderWith.of_parabolicCylinder_cover_closedCylinder
    (B := B) (C := Hsum) hbounded hα htime hspace hcover hlocal_sum

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

/-- Local-to-global parabolic Holder control from a finite cover by variable-radius product
parabolic cylinders.  The local Holder constants and the far-pair boundedness constants are summed
over the finite cover. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder_variable {B : ℝ}
    {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hlocal : ∀ y ∈ N, ParabolicHolderOn α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ParabolicHolderOn α u K := by
  classical
  let C : ℝ × X → ℝ := fun y =>
    if hy : y ∈ N then Classical.choose (hlocal y hy) else 0
  let r : ℝ × X → ℝ := fun y => min (Real.sqrt (timeRadius y)) (spaceRadius y)
  have hCnonneg : ∀ y ∈ N, 0 ≤ C y := by
    intro y hy
    dsimp [C]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hC :
      ∀ y ∈ N, ParabolicHolderWith (C y) α u
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy
    dsimp [C]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  let A : ℝ × X → ℝ := fun y =>
    if hy : y ∈ N then max (C y) (2 * B / (r y) ^ α) else 0
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
  rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
  have hry : 0 < r y := by
    dsimp [r]
    exact lt_min (Real.sqrt_pos_of_pos (htime_pos y hyN)) (hspace_pos y hyN)
  have hAyD : A y ≤ D := hA_le_D y hyN
  have hpclosed :
      p ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) :=
    parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
  have hpoint : ‖u p - u q‖ ≤ A y * d ^ α := by
    by_cases hsmall : d < r y
    · have hqclosed :
          q ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) := by
        exact parabolicCylinder.mem_closedCylinder_two_of_mem_of_parabolicDistance_lt_min_sqrt
          hpcy (by simpa [d, r] using hsmall)
      have hlocalpq : ‖u p - u q‖ ≤ C y * d ^ α := by
        simpa [d] using hC y hyN hpclosed hqclosed
      have hCA : C y ≤ A y := by
        dsimp [A]
        rw [if_pos hyN]
        exact le_max_left _ _
      exact hlocalpq.trans
        (mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hd0 α))
    · have hfar : r y ≤ d := le_of_not_gt hsmall
      have hBnonneg : 0 ≤ B := (norm_nonneg (u p)).trans (hbounded hp)
      have hrpow_pos : 0 < (r y) ^ α := Real.rpow_pos_of_pos hry α
      have hrpow_le_dpow : (r y) ^ α ≤ d ^ α :=
        Real.rpow_le_rpow hry.le hfar hα.le
      have hcoef_nonneg : 0 ≤ 2 * B / (r y) ^ α :=
        div_nonneg (mul_nonneg (by positivity) hBnonneg) hrpow_pos.le
      have hdiff : ‖u p - u q‖ ≤ 2 * B := by
        calc
          ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hbounded hp) (hbounded hq)
          _ = 2 * B := by ring
      have hfar_bound : 2 * B ≤ A y * d ^ α := by
        calc
          2 * B = (2 * B / (r y) ^ α) * (r y) ^ α := by
            rw [div_mul_cancel₀ _ hrpow_pos.ne']
          _ ≤ (2 * B / (r y) ^ α) * d ^ α :=
            mul_le_mul_of_nonneg_left hrpow_le_dpow hcoef_nonneg
          _ ≤ A y * d ^ α := by
            have hcoefA : 2 * B / (r y) ^ α ≤ A y := by
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

/-- Compact local-to-global parabolic Holder control from point-dependent doubled closed-cylinder
estimates, with Holder constants and cover radii chosen on a finite compact subcover. -/
theorem of_isCompact_of_local_closedCylinder_variable {B : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hlocal : ∀ y ∈ K, ParabolicHolderOn α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ParabolicHolderOn α u K := by
  rcases hK.elim_nhds_subcover
      (fun y => parabolicCylinder y (timeRadius y) (spaceRadius y))
      (fun y hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius y)
        (spaceRadius := spaceRadius y) (htime_pos y hy) (hspace_pos y hy)) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicCylinder_cover_closedCylinder_variable N timeRadius spaceRadius
    hbounded hα
    (fun y hy => htime_pos y (hNK y hy))
    (fun y hy => hspace_pos y (hNK y hy)) hcover
    (fun y hy => hlocal y (hNK y hy))

/-- Compact local-to-global parabolic Holder control from pointwise positive local product-cylinder
radii, with the radii, cover, and Holder constants chosen automatically. -/
theorem of_isCompact_of_exists_local_closedCylinder {B : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hbounded : ParabolicBoundedWith B u K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ParabolicHolderOn α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicHolderOn α u K := by
  classical
  let timeRadius : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  let spaceRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ K then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 1
  have htime_pos : ∀ y ∈ K, 0 < timeRadius y := by
    intro y hy
    dsimp [timeRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hspace_pos : ∀ y ∈ K, 0 < spaceRadius y := by
    intro y hy
    dsimp [spaceRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hlocalR :
      ∀ y ∈ K, ParabolicHolderOn α u
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2
  exact of_isCompact_of_local_closedCylinder_variable hK hbounded hα timeRadius spaceRadius
    htime_pos hspace_pos hlocalR

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

/-- Compact local-to-global parabolic Holder control from local doubled closed-cylinder estimates,
with Holder constants chosen automatically from a finite compact subcover. -/
theorem of_isCompact_of_local_closedCylinder {B timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (hbounded : ParabolicBoundedWith B u K) (hK : IsCompact K) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hlocal : ∀ y ∈ K, ParabolicHolderOn α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicHolderOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicCylinder y timeRadius spaceRadius)
      (fun y _hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius)
        (spaceRadius := spaceRadius) htime hspace) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicCylinder_cover_closedCylinder N hbounded hα htime hspace hcover
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

/-- Pullback of parabolic Hölder membership along a map `φ : ℝ × Y → ℝ × X` that expands
parabolic distance by at most a factor `L` and maps `t` into `s`.  Existential-constant form
of `ParabolicHolderWith.comp_parabolicDistanceLe`. -/
theorem comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicHolderOn α (fun p => u (φ p)) t := by
  rcases hu with ⟨C, hC, hCu⟩
  exact ⟨C * L ^ α, mul_nonneg hC (Real.rpow_nonneg hL α),
    hCu.comp_parabolicDistanceLe hC hα hL hmaps hφ⟩

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

/-- Spatial boundedness on the projection gives boundedness for the time-independent lift. -/
theorem of_snd {f : X → E}
    (hf : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B) :
    ParabolicBoundedWith B (fun z : ℝ × X => f z.2) s := by
  intro p hp
  exact hf ⟨p, hp, rfl⟩

/-- Time-only boundedness lifts to a parabolic time-space bound. -/
theorem of_fst {f : ℝ → E}
    (hf : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B) :
    ParabolicBoundedWith B (fun z : ℝ × X => f z.1) s := by
  intro p hp
  exact hf ⟨p, hp, rfl⟩

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

theorem zsmul (n : ℤ) (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith (‖n‖ * B) (fun z => n • u z) s := by
  intro p hp
  calc
    ‖n • u p‖ ≤ ‖n‖ * ‖u p‖ := norm_zsmul_le n (u p)
    _ ≤ ‖n‖ * B := mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg n)

theorem prod {F : Type*} [NormedAddCommGroup F] {D : ℝ} {v : ℝ × X → F}
    (hu : ParabolicBoundedWith B u s) (hv : ParabolicBoundedWith D v s) :
    ParabolicBoundedWith (max B D) (fun z => (u z, v z)) s := by
  intro p hp
  change ‖(u p, v p)‖ ≤ max B D
  rw [Prod.norm_mk]
  exact max_le ((hu hp).trans (le_max_left B D)) ((hv hp).trans (le_max_right B D))

/-- Componentwise finite sup-norm bounds package as a Pi-valued sup-norm bound with summed
constants. -/
theorem pi {ι : Type*} [Fintype ι] {B : ι → ℝ} {u : ℝ × X → ι → E}
    (hB : ∀ i, 0 ≤ B i)
    (h : ∀ i, ParabolicBoundedWith (B i) (fun z => u z i) s) :
    ParabolicBoundedWith (∑ i, B i) u s := by
  intro p hp
  have hBsum_nonneg : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _hi => hB i
  have hB_le_sum : ∀ i, B i ≤ ∑ j, B j := by
    intro i
    exact Finset.single_le_sum (fun j _hj => hB j) (Finset.mem_univ i)
  exact (pi_norm_le_iff_of_nonneg hBsum_nonneg).2 fun i =>
    (h i hp).trans (hB_le_sum i)

/-- A Pi-valued sup-norm bound restricts to each component with the same constant. -/
theorem eval {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ParabolicBoundedWith B u s) (i : ι) :
    ParabolicBoundedWith B (fun z => u z i) s := by
  intro p hp
  exact (norm_le_pi_norm (u p) i).trans (h hp)

/-- Products of normed-ring-valued functions preserve sup-norm control. -/
theorem mul {A : Type*} [NormedRing A] {B₁ B₂ : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicBoundedWith B₁ u s)
    (hv : ParabolicBoundedWith B₂ v s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicBoundedWith (B₁ * B₂) (fun z => u z * v z) s := by
  intro p hp
  exact (norm_mul_le (u p) (v p)).trans
    (mul_le_mul (hu hp) (hv hp) (norm_nonneg _) hB₁)

/-- Product differences inherit sup-norm control from one left factor, one right factor, and
bounded controls of the two factor differences. -/
theorem mul_sub_mul {A : Type*} [NormedRing A]
    {Bu Bv Bdu Bdv : ℝ}
    {u u' v v' : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicBoundedWith Bu u s)
    (hv' : ParabolicBoundedWith Bv v' s)
    (hdu : ParabolicBoundedWith Bdu (fun z => u z - u' z) s)
    (hdv : ParabolicBoundedWith Bdv (fun z => v z - v' z) s)
    (hBu : 0 ≤ Bu) (hBdu : 0 ≤ Bdu) :
    ParabolicBoundedWith (Bu * Bdv + Bdu * Bv)
      (fun z => u z * v z - u' z * v' z) s := by
  have hleft :
      ParabolicBoundedWith (Bu * Bdv) (fun z => u z * (v z - v' z)) s :=
    hu.mul hdv hBu
  have hright :
      ParabolicBoundedWith (Bdu * Bv) (fun z => (u z - u' z) * v' z) s :=
    hdu.mul hv' hBdu
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  noncomm_ring

theorem inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ} {a : ℝ × X → 𝕜}
    (hδpos : 0 < δ) (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicBoundedWith δ⁻¹ (fun z => (a z)⁻¹) s := by
  intro p hp
  have hp_norm_pos : 0 < ‖a p‖ := lt_of_lt_of_le hδpos (hδ hp)
  rw [norm_inv]
  exact (inv_le_inv₀ hp_norm_pos hδpos).2 (hδ hp)

/-- Reciprocal differences inherit sup-norm control from the difference of the inputs, under a
common pointwise lower bound. -/
theorem inv_sub_inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ}
    {a b : ℝ × X → 𝕜} {Bd : ℝ}
    (hdiff : ParabolicBoundedWith Bd (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖)
    (hBd : 0 ≤ Bd) :
    ParabolicBoundedWith ((δ⁻¹ * Bd) * δ⁻¹)
      (fun z => (a z)⁻¹ - (b z)⁻¹) s := by
  have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hainv :
      ParabolicBoundedWith δ⁻¹ (fun z => (a z)⁻¹) s :=
    ParabolicBoundedWith.inv hδpos hδa
  have hbinv :
      ParabolicBoundedWith δ⁻¹ (fun z => (b z)⁻¹) s :=
    ParabolicBoundedWith.inv hδpos hδb
  have hleft :
      ParabolicBoundedWith (δ⁻¹ * Bd) (fun z => (a z)⁻¹ * (a z - b z)) s :=
    hainv.mul hdiff hδinv_nonneg
  have hleftB_nonneg : 0 ≤ δ⁻¹ * Bd := mul_nonneg hδinv_nonneg hBd
  have hprod :
      ParabolicBoundedWith ((δ⁻¹ * Bd) * δ⁻¹)
        (fun z => ((a z)⁻¹ * (a z - b z)) * (b z)⁻¹) s :=
    hleft.mul hbinv hleftB_nonneg
  have hneg := hprod.neg
  have hpoint : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      (a z)⁻¹ - (b z)⁻¹ = -(((a z)⁻¹ * (a z - b z)) * (b z)⁻¹) := by
    intro z hz
    have ha_ne : a z ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδpos (hδa hz))
    have hb_ne : b z ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδpos (hδb hz))
    field_simp [ha_ne, hb_ne]
    ring
  intro p hp
  change ‖(a p)⁻¹ - (b p)⁻¹‖ ≤ (δ⁻¹ * Bd) * δ⁻¹
  rw [hpoint hp]
  simpa using hneg hp

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith (‖c‖ * B) (fun z => c • u z) s := by
  intro p hp
  calc
    ‖c • u p‖ = ‖c‖ * ‖u p‖ := norm_smul c (u p)
    _ ≤ ‖c‖ * B := mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg c)

/-- Variable scalar action preserves sup-norm control. -/
theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {B₁ B₂ : ℝ} {a : ℝ × X → 𝕜} {u : ℝ × X → F} {s : Set (ℝ × X)}
    (ha : ParabolicBoundedWith B₁ a s)
    (hu : ParabolicBoundedWith B₂ u s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicBoundedWith (B₁ * B₂) (fun z => a z • u z) s := by
  intro p hp
  rw [norm_smul]
  exact mul_le_mul (ha hp) (hu hp) (norm_nonneg _) hB₁

/-- A continuous linear map preserves sup-norm control, with the operator norm multiplying the
bound. -/
theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicBoundedWith B u s) :
    ParabolicBoundedWith (‖L‖ * B) (fun z => L (u z)) s := by
  intro p hp
  calc
    ‖L (u p)‖ ≤ ‖L‖ * ‖u p‖ := ContinuousLinearMap.le_opNorm L (u p)
    _ ≤ ‖L‖ * B := mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg L)

/-- A curried continuous bilinear map preserves sup-norm control, with the operator norm and
factor bounds multiplying. -/
theorem continuousLinearMap₂ {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {D : ℝ} {v : ℝ × X → F}
    (L : E →L[ℝ] F →L[ℝ] G)
    (hu : ParabolicBoundedWith B u s) (hv : ParabolicBoundedWith D v s)
    (hB : 0 ≤ B) :
    ParabolicBoundedWith (‖L‖ * B * D) (fun z => L (u z) (v z)) s := by
  intro p hp
  have hLup : ‖L (u p)‖ ≤ ‖L‖ * B :=
    (ContinuousLinearMap.le_opNorm L (u p)).trans
      (mul_le_mul_of_nonneg_left (hu hp) (norm_nonneg L))
  have hLup_nonneg : 0 ≤ ‖L‖ * B := mul_nonneg (norm_nonneg L) hB
  calc
    ‖L (u p) (v p)‖ ≤ ‖L (u p)‖ * ‖v p‖ :=
      ContinuousLinearMap.le_opNorm (L (u p)) (v p)
    _ ≤ (‖L‖ * B) * D :=
      mul_le_mul hLup (hv hp) (norm_nonneg _) hLup_nonneg
    _ = ‖L‖ * B * D := by ring

/-- Differences of curried continuous bilinear-map applications inherit sup-norm control from
one left input, one right input, and bounded controls of the two input differences. -/
theorem continuousLinearMap₂_sub {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {Bu Bv Bdu Bdv : ℝ}
    {u u' : ℝ × X → E} {v v' : ℝ × X → F}
    (hu : ParabolicBoundedWith Bu u s)
    (hv' : ParabolicBoundedWith Bv v' s)
    (hdu : ParabolicBoundedWith Bdu (fun z => u z - u' z) s)
    (hdv : ParabolicBoundedWith Bdv (fun z => v z - v' z) s)
    (hBu : 0 ≤ Bu) (hBdu : 0 ≤ Bdu) :
    ParabolicBoundedWith (‖L‖ * Bu * Bdv + ‖L‖ * Bdu * Bv)
      (fun z => L (u z) (v z) - L (u' z) (v' z)) s := by
  have hleft :
      ParabolicBoundedWith (‖L‖ * Bu * Bdv)
        (fun z => L (u z) (v z - v' z)) s := by
    simpa using hu.continuousLinearMap₂ L hdv hBu
  have hright :
      ParabolicBoundedWith (‖L‖ * Bdu * Bv)
        (fun z => L (u z - u' z) (v' z)) s := by
    simpa using hdu.continuousLinearMap₂ L hv' hBdu
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  simp [map_sub]

/-- Applying an operator-valued function to a vector-valued function preserves sup-norm control. -/
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A : ℝ × X → E →L[ℝ] F} {v : ℝ × X → E} {BA Bv : ℝ}
    (hA : ParabolicBoundedWith BA A s) (hv : ParabolicBoundedWith Bv v s)
    (hBA : 0 ≤ BA) :
    ParabolicBoundedWith (BA * Bv) (fun z => A z (v z)) s := by
  intro p hp
  calc
    ‖A p (v p)‖ ≤ ‖A p‖ * ‖v p‖ := ContinuousLinearMap.le_opNorm (A p) (v p)
    _ ≤ BA * Bv := mul_le_mul (hA hp) (hv hp) (norm_nonneg _) hBA

/-- Differences of operator-valued applications inherit sup-norm control from one operator
input, one vector input, and bounded controls of the operator and vector differences. -/
theorem continuousLinearMap_apply_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A A' : ℝ × X → E →L[ℝ] F} {v v' : ℝ × X → E}
    {BA Bv BAd Bvd : ℝ}
    (hA : ParabolicBoundedWith BA A s)
    (hv' : ParabolicBoundedWith Bv v' s)
    (hAdiff : ParabolicBoundedWith BAd (fun z => A z - A' z) s)
    (hvdiff : ParabolicBoundedWith Bvd (fun z => v z - v' z) s)
    (hBA : 0 ≤ BA) (hBAd : 0 ≤ BAd) :
    ParabolicBoundedWith (BA * Bvd + BAd * Bv)
      (fun z => A z (v z) - A' z (v' z)) s := by
  have hleft :
      ParabolicBoundedWith (BA * Bvd) (fun z => A z (v z - v' z)) s :=
    hA.continuousLinearMap_apply hvdiff hBA
  have hright :
      ParabolicBoundedWith (BAd * Bv) (fun z => (A z - A' z) (v' z)) s :=
    hAdiff.continuousLinearMap_apply hv' hBAd
  have hsum := hleft.add hright
  convert hsum using 1
  ext z
  simp [map_sub]

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

theorem comp_lipschitzOnWith_of_closedBall {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicBoundedWith B u s) (hB : 0 ≤ B)
    (hφ : LipschitzOnWith K φ (Metric.closedBall (0 : E) B)) :
    ParabolicBoundedWith (‖φ (0 : E)‖ + (K : ℝ) * B) (fun z => φ (u z)) s := by
  intro p hp
  have hpball : u p ∈ Metric.closedBall (0 : E) B := hu.image_subset_closedBall_zero ⟨p, hp, rfl⟩
  have hzeroball : (0 : E) ∈ Metric.closedBall (0 : E) B := by
    simpa [Metric.mem_closedBall, dist_self] using hB
  calc
    ‖φ (u p)‖ = ‖(φ (u p) - φ 0) + φ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖φ (u p) - φ 0‖ + ‖φ 0‖ := norm_add_le _ _
    _ = dist (φ (u p)) (φ 0) + ‖φ 0‖ := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (u p) 0 + ‖φ 0‖ := by
      exact add_le_add_left (hφ.dist_le_mul (u p) hpball 0 hzeroball) _
    _ = (K : ℝ) * ‖u p‖ + ‖φ 0‖ := by rw [dist_eq_norm, sub_zero]
    _ ≤ (K : ℝ) * B + ‖φ 0‖ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (hu hp) (NNReal.coe_nonneg K)) _
    _ = ‖φ (0 : E)‖ + (K : ℝ) * B := by ring

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicBoundedWith B u s) (hφ : LipschitzWith K φ) :
    ParabolicBoundedWith (‖φ (0 : E)‖ + (K : ℝ) * B) (fun z => φ (u z)) s := by
  intro p hp
  calc
    ‖φ (u p)‖ = ‖(φ (u p) - φ 0) + φ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖φ (u p) - φ 0‖ + ‖φ 0‖ := norm_add_le _ _
    _ = dist (φ (u p)) (φ 0) + ‖φ 0‖ := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (u p) 0 + ‖φ 0‖ := by
      exact add_le_add_left (hφ.dist_le_mul (u p) 0) _
    _ = (K : ℝ) * ‖u p‖ + ‖φ 0‖ := by rw [dist_eq_norm, sub_zero]
    _ ≤ (K : ℝ) * B + ‖φ 0‖ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (hu hp) (NNReal.coe_nonneg K)) _
    _ = ‖φ (0 : E)‖ + (K : ℝ) * B := by ring

/-- Pullback of a parabolic sup-norm bound along a map `φ : ℝ × Y → ℝ × X` that maps `t`
into `s`.  This is the boundedness half of the parabolic change-of-variables lemma; the
bound constant is unchanged. -/
theorem comp_mapsTo {Y : Type*} [PseudoMetricSpace Y]
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicBoundedWith B u s) (hmaps : Set.MapsTo φ t s) :
    ParabolicBoundedWith B (fun p => u (φ p)) t := by
  intro p hp
  exact hu (hmaps hp)

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

/-- Local-to-global parabolic `C^{0,α}` control from a product-parabolic-cylinder cover.  The
local bounded constant controls the global bounded part, while the Holder constant globalizes
through the bounded local-to-global cylinder estimate. -/
theorem of_parabolicCylinder_cover_closedCylinder {timeRadius spaceRadius : ℝ}
    {K N : Set (ℝ × X)}
    (hα : 0 < α) (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y timeRadius spaceRadius)
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaWith B H α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicC0AlphaWith B
      (max H (2 * B / (min (Real.sqrt timeRadius) spaceRadius) ^ α)) α u K := by
  have hbounded : ParabolicBoundedWith B u K := by
    intro p hp
    rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
    have hpclosed :
        p ∈ parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius) :=
      parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
    exact (hlocal y hyN).bounded hpclosed
  exact ⟨hbounded,
    ParabolicHolderWith.of_parabolicCylinder_cover_closedCylinder (C := H)
      hbounded hα htime hspace hcover fun y hy => (hlocal y hy).holder⟩

/-- Compact local-to-global parabolic `C^{0,α}` control from uniform local closed-ball estimates. -/
theorem of_isCompact_of_uniform_local_closedBall {r : ℝ} {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (hr : 0 < r)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * r))) :
    ParabolicC0AlphaWith B (max H (2 * B / r ^ α)) α u K := by
  rcases parabolicBall.exists_finite_cover_of_isCompact hK hr with
    ⟨N, hNK, _hNfinite, hcover⟩
  exact of_parabolicBall_cover_closedBall hα hr hcover
    (fun y hy => hlocal y (hNK hy))

/-- Compact local-to-global parabolic `C^{0,α}` control from uniform local doubled
closed-cylinder estimates. -/
theorem of_isCompact_of_uniform_local_closedCylinder {timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaWith B H α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicC0AlphaWith B
      (max H (2 * B / (min (Real.sqrt timeRadius) spaceRadius) ^ α)) α u K := by
  rcases parabolicCylinder.exists_finite_cover_of_isCompact hK htime hspace with
    ⟨N, hNK, _hNfinite, hcover⟩
  exact of_parabolicCylinder_cover_closedCylinder hα htime hspace hcover
    (fun y hy => hlocal y (hNK hy))

/-- Local-to-global parabolic `C^{0,α}` control from a finite cover by variable-radius
parabolic balls, preserving the local sup constant and summing the variable-radius Holder
constants. -/
theorem of_finset_parabolicBall_cover_closedBall_variable {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (R : ℝ × X → ℝ) (hα : 0 < α)
    (hRpos : ∀ y ∈ N, 0 < R y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y (R y))
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * R y))) :
    ParabolicC0AlphaWith B (∑ y ∈ N, max H (2 * B / (R y) ^ α)) α u K := by
  have hbounded : ParabolicBoundedWith B u K := by
    intro p hp
    rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpball⟩
    have hRy : 0 < R y := hRpos y hyN
    have hRy_le_two : R y ≤ 2 * R y := by linarith
    have hpclosed : p ∈ parabolicClosedBall y (2 * R y) :=
      (le_of_lt hpball).trans hRy_le_two
    exact (hlocal y hyN).bounded hpclosed
  exact ⟨hbounded,
    ParabolicHolderWith.of_finset_parabolicBall_cover_closedBall_variable
      (B := B) (C := H) N R hbounded hα hRpos hcover
      (fun y hy => (hlocal y hy).holder)⟩

/-- Local-to-global parabolic `C^{0,α}` control from a finite cover by variable-radius product
parabolic cylinders, preserving the local sup constant and summing the variable-radius Holder
constants. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder_variable {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaWith B H α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ParabolicC0AlphaWith B
      (∑ y ∈ N, max H
        (2 * B / (min (Real.sqrt (timeRadius y)) (spaceRadius y)) ^ α)) α u K := by
  have hbounded : ParabolicBoundedWith B u K := by
    intro p hp
    rcases mem_iUnion.1 (hcover hp) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
    have hpclosed :
        p ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) :=
      parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
    exact (hlocal y hyN).bounded hpclosed
  exact ⟨hbounded,
    ParabolicHolderWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      (B := B) (C := H) N timeRadius spaceRadius hbounded hα htime_pos hspace_pos hcover
      (fun y hy => (hlocal y hy).holder)⟩

/-- Compact variable-radius parabolic `C^{0,α}` patching from point-dependent doubled closed-ball
estimates.  The finite compact subcover is chosen internally while the global sup constant remains
the fixed local sup constant. -/
theorem exists_holderConst_of_isCompact_of_local_closedBall_variable {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (R : ℝ × X → ℝ)
    (hRpos : ∀ y ∈ K, 0 < R y)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * R y))) :
    ∃ Hglobal, ParabolicC0AlphaWith B Hglobal α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicBall y (R y))
      (fun y hy => parabolicBall.mem_nhds (p := y) (R := R y) (hRpos y hy)) with
    ⟨N, hNK, hcover⟩
  exact ⟨∑ y ∈ N, max H (2 * B / (R y) ^ α),
    of_finset_parabolicBall_cover_closedBall_variable N R hα
      (fun y hy => hRpos y (hNK y hy)) hcover
      (fun y hy => hlocal y (hNK y hy))⟩

/-- Compact parabolic `C^{0,α}` patching from pointwise positive local closed-ball radii. -/
theorem exists_holderConst_of_isCompact_of_exists_local_closedBall {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ r > 0,
      ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * r))) :
    ∃ Hglobal, ParabolicC0AlphaWith B Hglobal α u K := by
  classical
  let R : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  have hRpos : ∀ y ∈ K, 0 < R y := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hlocalR : ∀ y ∈ K, ParabolicC0AlphaWith B H α u (parabolicClosedBall y (2 * R y)) := by
    intro y hy
    dsimp [R]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).2
  exact exists_holderConst_of_isCompact_of_local_closedBall_variable hK hα R hRpos hlocalR

/-- Compact variable-radius parabolic `C^{0,α}` patching from point-dependent doubled
closed-cylinder estimates.  The finite compact subcover is chosen internally while the global sup
constant remains the fixed local sup constant. -/
theorem exists_holderConst_of_isCompact_of_local_closedCylinder_variable {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaWith B H α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ∃ Hglobal, ParabolicC0AlphaWith B Hglobal α u K := by
  rcases hK.elim_nhds_subcover
      (fun y => parabolicCylinder y (timeRadius y) (spaceRadius y))
      (fun y hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius y)
        (spaceRadius := spaceRadius y) (htime_pos y hy) (hspace_pos y hy)) with
    ⟨N, hNK, hcover⟩
  exact ⟨∑ y ∈ N, max H
      (2 * B / (min (Real.sqrt (timeRadius y)) (spaceRadius y)) ^ α),
    of_finset_parabolicCylinder_cover_closedCylinder_variable N timeRadius spaceRadius hα
      (fun y hy => htime_pos y (hNK y hy))
      (fun y hy => hspace_pos y (hNK y hy)) hcover
      (fun y hy => hlocal y (hNK y hy))⟩

/-- Compact parabolic `C^{0,α}` patching from pointwise positive local product-cylinder radii. -/
theorem exists_holderConst_of_isCompact_of_exists_local_closedCylinder {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ParabolicC0AlphaWith B H α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ∃ Hglobal, ParabolicC0AlphaWith B Hglobal α u K := by
  classical
  let timeRadius : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  let spaceRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ K then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 1
  have htime_pos : ∀ y ∈ K, 0 < timeRadius y := by
    intro y hy
    dsimp [timeRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hspace_pos : ∀ y ∈ K, 0 < spaceRadius y := by
    intro y hy
    dsimp [spaceRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hlocalR :
      ∀ y ∈ K, ParabolicC0AlphaWith B H α u
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2
  exact exists_holderConst_of_isCompact_of_local_closedCylinder_variable
    hK hα timeRadius spaceRadius htime_pos hspace_pos hlocalR

theorem const (c : E) (hB : ‖c‖ ≤ B) (hH : 0 ≤ H) :
    ParabolicC0AlphaWith B H α (fun _ : ℝ × X => c) s :=
  ⟨ParabolicBoundedWith.const c hB, ParabolicHolderWith.const c hH⟩

/-- Spatial boundedness and Lipschitz control on the projection give parabolic `C^{0,1}`
control for the time-independent lift. -/
theorem of_snd_lipschitzOnWith {K : ℝ≥0} {f : X → E}
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s)) :
    ParabolicC0AlphaWith B (K : ℝ) 1 (fun z : ℝ × X => f z.2) s :=
  ⟨ParabolicBoundedWith.of_snd hB, ParabolicHolderWith.of_snd_lipschitzOnWith hL⟩

/-- Spatial boundedness and Holder control on the projection give parabolic `C^{0,α}` control
for the time-independent lift. -/
theorem of_snd_holder {f : X → E}
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hf : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄, y ∈ Prod.snd '' s →
      ‖f x - f y‖ ≤ H * (dist x y) ^ α) :
    ParabolicC0AlphaWith B H α (fun z : ℝ × X => f z.2) s :=
  ⟨ParabolicBoundedWith.of_snd hB, ParabolicHolderWith.of_snd_holder hH hα hf⟩

/-- Time-only boundedness and Holder control with exponent `α / 2` give parabolic `C^{0,α}`
control for the time-only lift. -/
theorem of_fst_holder {f : ℝ → E}
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hf : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄, τ ∈ Prod.fst '' s →
      ‖f t - f τ‖ ≤ H * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaWith B H α (fun z : ℝ × X => f z.1) s :=
  ⟨ParabolicBoundedWith.of_fst hB, ParabolicHolderWith.of_fst_holder hH hα hf⟩

/-- Time-only boundedness and Lipschitz control give parabolic `C^{0,2}` control for the
time-only lift. -/
theorem of_fst_lipschitzOnWith {K : ℝ≥0} {f : ℝ → E}
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s)) :
    ParabolicC0AlphaWith B (K : ℝ) 2 (fun z : ℝ × X => f z.1) s :=
  ⟨ParabolicBoundedWith.of_fst hB, ParabolicHolderWith.of_fst_lipschitzOnWith hL⟩

/-- On a unit parabolic-diameter set, spatial boundedness and Lipschitz control on the projection
give fixed-constant parabolic `C^{0,α}` control for every `0 ≤ α ≤ 1`. -/
theorem of_snd_lipschitzOnWith_of_parabolicDistance_le_one {K : ℝ≥0} {f : X → E}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.2) s :=
  ⟨ParabolicBoundedWith.of_snd hB,
    (ParabolicHolderWith.of_snd_lipschitzOnWith hL).mono_exponent_of_parabolicDistance_le_one
      (NNReal.coe_nonneg K) hα_nonneg hα_le_one hdiam⟩

/-- On a unit parabolic-diameter set, time-only boundedness and Lipschitz control give
fixed-constant parabolic `C^{0,α}` control for every `0 ≤ α ≤ 2`. -/
theorem of_fst_lipschitzOnWith_of_parabolicDistance_le_one {K : ℝ≥0} {f : ℝ → E}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.1) s :=
  ⟨ParabolicBoundedWith.of_fst hB,
    (ParabolicHolderWith.of_fst_lipschitzOnWith hL).mono_exponent_of_parabolicDistance_le_one
      (NNReal.coe_nonneg K) hα_nonneg hα_le_two hdiam⟩

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

/-- Finite sums of termwise differences inherit parabolic `C^{0,α}` control from the termwise
difference controls. -/
theorem sum_sub_sum {ι : Type*} (S : Finset ι) {B H : ι → ℝ}
    {u v : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (fun z => u i z - v i z) s) :
    ParabolicC0AlphaWith (∑ i ∈ S, B i) (∑ i ∈ S, H i) α
      (fun z => (∑ i ∈ S, u i z) - ∑ i ∈ S, v i z) s := by
  classical
  have hsum := ParabolicC0AlphaWith.sum (s := s) (α := α) S h
  convert hsum using 1
  ext z
  rw [Finset.sum_sub_distrib]

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

theorem zsmul (n : ℤ) (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith (‖n‖ * B) (‖n‖ * H) α (fun z => n • u z) s :=
  ⟨hu.bounded.zsmul n, hu.holder.zsmul n⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {B₃ H₃ : ℝ} {v : ℝ × X → F}
    (hu : ParabolicC0AlphaWith B H α u s)
    (hv : ParabolicC0AlphaWith B₃ H₃ α v s) :
    ParabolicC0AlphaWith (max B B₃) (max H H₃) α (fun z => (u z, v z)) s :=
  ⟨hu.bounded.prod hv.bounded, hu.holder.prod hv.holder⟩

/-- Componentwise finite parabolic `C^{0,α}` estimates package as a Pi-valued estimate with
summed sup and Holder constants. -/
theorem pi {ι : Type*} [Fintype ι] {B H : ι → ℝ} {u : ℝ × X → ι → E}
    (hB : ∀ i, 0 ≤ B i) (hH : ∀ i, 0 ≤ H i)
    (h : ∀ i, ParabolicC0AlphaWith (B i) (H i) α (fun z => u z i) s) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, H i) α u s :=
  ⟨ParabolicBoundedWith.pi hB fun i => (h i).bounded,
    ParabolicHolderWith.pi hH fun i => (h i).holder⟩

/-- A Pi-valued parabolic `C^{0,α}` estimate restricts to each component with the same
constants. -/
theorem eval {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ParabolicC0AlphaWith B H α u s) (i : ι) :
    ParabolicC0AlphaWith B H α (fun z => u z i) s :=
  ⟨h.bounded.eval i, h.holder.eval i⟩

theorem inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ} {a : ℝ × X → 𝕜}
    (ha : ParabolicC0AlphaWith B H α a s) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicC0AlphaWith δ⁻¹ (δ⁻¹ * H * δ⁻¹) α (fun z => (a z)⁻¹) s :=
  ⟨ParabolicBoundedWith.inv hδpos hδ, ha.holder.inv hδpos hδ⟩

/-- Sup constant for the parabolic `C^{0,α}` difference of two reciprocal functions. -/
def invSubBoundConst (δ Bd : ℝ) : ℝ :=
  (δ⁻¹ * Bd) * δ⁻¹

/-- Holder constant for the parabolic `C^{0,α}` difference of two reciprocal functions.  The
terms are written in product-rule form: first multiply `a⁻¹` with `a - b`, then multiply by
`b⁻¹`. -/
def invSubHolderConst (δ Ha Hb Bd Hd : ℝ) : ℝ :=
  (δ⁻¹ * Bd) * (δ⁻¹ * Hb * δ⁻¹) +
    δ⁻¹ * (δ⁻¹ * Hd + Bd * (δ⁻¹ * Ha * δ⁻¹))

/-- Nonnegativity of the reciprocal-difference sup constant. -/
theorem invSubBoundConst_nonneg {δ Bd : ℝ} (hδpos : 0 < δ) (hBd : 0 ≤ Bd) :
    0 ≤ invSubBoundConst δ Bd := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hδpos.le) hBd)
    (inv_nonneg.mpr hδpos.le)

/-- Nonnegativity of the reciprocal-difference Holder constant. -/
theorem invSubHolderConst_nonneg {δ Ha Hb Bd Hd : ℝ} (hδpos : 0 < δ)
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) (hBd : 0 ≤ Bd) (hHd : 0 ≤ Hd) :
    0 ≤ invSubHolderConst δ Ha Hb Bd Hd := by
  have hδnn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  exact add_nonneg
    (mul_nonneg (mul_nonneg hδnn hBd) (mul_nonneg (mul_nonneg hδnn hHb) hδnn))
    (mul_nonneg hδnn
      (add_nonneg (mul_nonneg hδnn hHd)
        (mul_nonneg hBd (mul_nonneg (mul_nonneg hδnn hHa) hδnn))))

theorem mul {A : Type*} [NormedRing A] {B₁ B₂ H₁ H₂ α : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith B₁ H₁ α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicC0AlphaWith (B₁ * B₂) (B₁ * H₂ + B₂ * H₁) α
      (fun z => u z * v z) s := by
  constructor
  · exact hu.bounded.mul hv.bounded hB₁
  · exact hu.holder.mul hv.holder hu.bounded hv.bounded hB₁

/-- Finite sums of products inherit parabolic `C^{0,α}` control from factorwise controls. -/
theorem finset_sum_mul {ι A : Type*} [NormedRing A] (S : Finset ι)
    {Bu Hu Bv Hv : ι → ℝ} {α : ℝ} {u v : ι → ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ∀ i ∈ S, ParabolicC0AlphaWith (Bu i) (Hu i) α (u i) s)
    (hv : ∀ i ∈ S, ParabolicC0AlphaWith (Bv i) (Hv i) α (v i) s)
    (hBu : ∀ i ∈ S, 0 ≤ Bu i) :
    ParabolicC0AlphaWith
      (Finset.sum S fun i => Bu i * Bv i)
      (Finset.sum S fun i => Bu i * Hv i + Bv i * Hu i) α
      (fun z => Finset.sum S fun i => u i z * v i z) s :=
  ParabolicC0AlphaWith.sum (X := X) (E := A) (s := s) (α := α) S
    (fun i hi => (hu i hi).mul (hv i hi) (hBu i hi))

/-- Reciprocal differences inherit parabolic `C^{0,α}` control from the difference of the
inputs, under a common pointwise lower bound.  This is the scalar local-Lipschitz form behind
inverse-metric estimates: the Holder constant depends on the Holder size of `a - b`, not only on
the two standalone reciprocal Holder constants. -/
theorem inv_sub_inv {𝕜 : Type*} [NormedField 𝕜] {δ : ℝ}
    {a b : ℝ × X → 𝕜} {Ba Ha Bb Hb Bd Hd α : ℝ}
    (ha : ParabolicC0AlphaWith Ba Ha α a s)
    (hb : ParabolicC0AlphaWith Bb Hb α b s)
    (hdiff : ParabolicC0AlphaWith Bd Hd α (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖)
    (hBd : 0 ≤ Bd) :
    ParabolicC0AlphaWith
      (invSubBoundConst δ Bd)
      (invSubHolderConst δ Ha Hb Bd Hd) α
      (fun z => (a z)⁻¹ - (b z)⁻¹) s := by
  constructor
  · simpa [invSubBoundConst] using hdiff.bounded.inv_sub_inv hδpos hδa hδb hBd
  · simpa [invSubHolderConst] using
      ha.holder.inv_sub_inv hb.holder hdiff.holder hdiff.bounded hδpos hδa hδb hBd

/-- Product differences inherit parabolic `C^{0,α}` control from one left factor, one right
factor, and `C^{0,α}` controls of the two factor differences. -/
theorem mul_sub_mul {A : Type*} [NormedRing A]
    {Bu Hu Bv Hv Bdu Hdu Bdv Hdv α : ℝ}
    {u u' v v' : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith Bu Hu α u s)
    (hv' : ParabolicC0AlphaWith Bv Hv α v' s)
    (hdu : ParabolicC0AlphaWith Bdu Hdu α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaWith Bdv Hdv α (fun z => v z - v' z) s)
    (hBu : 0 ≤ Bu) (hBdu : 0 ≤ Bdu) :
    ParabolicC0AlphaWith (Bu * Bdv + Bdu * Bv)
      ((Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu)) α
      (fun z => u z * v z - u' z * v' z) s := by
  constructor
  · exact hu.bounded.mul_sub_mul hv'.bounded hdu.bounded hdv.bounded hBu hBdu
  · exact hu.holder.mul_sub_mul hv'.holder hdu.holder hdv.holder hu.bounded
      hv'.bounded hdu.bounded hdv.bounded hBu hBdu

/-- Finite sums of product differences inherit parabolic `C^{0,α}` control from factorwise
controls and factor-difference controls. -/
theorem finset_sum_mul_sub_sum_mul {ι A : Type*} [NormedRing A] (S : Finset ι)
    {Bu Hu Bv Hv Bdu Hdu Bdv Hdv : ι → ℝ} {α : ℝ}
    {u u' v v' : ι → ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ∀ i ∈ S, ParabolicC0AlphaWith (Bu i) (Hu i) α (u i) s)
    (hv' : ∀ i ∈ S, ParabolicC0AlphaWith (Bv i) (Hv i) α (v' i) s)
    (hdu : ∀ i ∈ S,
      ParabolicC0AlphaWith (Bdu i) (Hdu i) α (fun z => u i z - u' i z) s)
    (hdv : ∀ i ∈ S,
      ParabolicC0AlphaWith (Bdv i) (Hdv i) α (fun z => v i z - v' i z) s)
    (hBu : ∀ i ∈ S, 0 ≤ Bu i) (hBdu : ∀ i ∈ S, 0 ≤ Bdu i) :
    ParabolicC0AlphaWith
      (∑ i ∈ S, (Bu i * Bdv i + Bdu i * Bv i))
      (∑ i ∈ S, ((Bu i * Hdv i + Bdv i * Hu i) +
        (Bdu i * Hv i + Bv i * Hdu i))) α
      (fun z => (∑ i ∈ S, u i z * v i z) - ∑ i ∈ S, u' i z * v' i z) s := by
  classical
  have hsum := ParabolicC0AlphaWith.sum (s := s) (α := α) S
    (B := fun i => Bu i * Bdv i + Bdu i * Bv i)
    (H := fun i => (Bu i * Hdv i + Bdv i * Hu i) +
      (Bdu i * Hv i + Bv i * Hdu i))
    (u := fun i z => u i z * v i z - u' i z * v' i z)
    (fun i hi =>
      (hu i hi).mul_sub_mul (hv' i hi) (hdu i hi) (hdv i hi) (hBu i hi) (hBdu i hi))
  convert hsum using 1
  ext z
  rw [Finset.sum_sub_distrib]

theorem div {𝕜 : Type*} [NormedField 𝕜] {B₁ B₂ H₁ H₂ δ : ℝ}
    {a b : ℝ × X → 𝕜} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaWith B₁ H₁ α a s)
    (hb : ParabolicC0AlphaWith B₂ H₂ α b s)
    (hB₁ : 0 ≤ B₁) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖) :
    ParabolicC0AlphaWith (B₁ * δ⁻¹)
      (B₁ * (δ⁻¹ * H₂ * δ⁻¹) + δ⁻¹ * H₁) α (fun z => a z / b z) s := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    ha.mul (hb.inv hδpos hδ) hB₁

/-- A finite product of normed-commutative-ring-valued parabolic `C^{0,α}` functions has an
explicit bounded `C^{0,α}` estimate.  The estimate uses `max (B i) 1` as a uniform factor so the
induction has a monotone closed form, and includes the unit norm needed for the empty product. -/
theorem finset_prod {ι A : Type*} [NormedCommRing A] (S : Finset ι)
    {B H : ι → ℝ} {u : ι → ℝ × X → A}
    (hH : ∀ i ∈ S, 0 ≤ H i)
    (h : ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (u i) s) :
    ParabolicC0AlphaWith
      (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)
      ((∑ i ∈ S, H i) * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1))
      α (fun z => ∏ i ∈ S, u i z) s := by
  classical
  revert hH h
  refine Finset.induction_on S ?base ?step
  · intro _hH _h
    simpa using
      (ParabolicC0AlphaWith.const (s := s) (α := α) (B := max ‖(1 : A)‖ 1)
        (H := 0) (1 : A) (le_max_left _ _) le_rfl)
  · intro a S ha ih hH h
    have ha_ctrl : ParabolicC0AlphaWith (B a) (H a) α (u a) s :=
      h a (by simp [ha])
    have htail :
        ParabolicC0AlphaWith
          (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)
          ((∑ i ∈ S, H i) * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1))
          α (fun z => ∏ i ∈ S, u i z) s :=
      ih
        (fun i hi => hH i (by simp [hi]))
        (fun i hi => h i (by simp [hi]))
    have hBamax_nonneg : 0 ≤ max (B a) 1 := (zero_le_one.trans (le_max_right _ _))
    have ha_ctrl' : ParabolicC0AlphaWith (max (B a) 1) (H a) α (u a) s :=
      ha_ctrl.mono_const (le_max_left _ _) le_rfl
    have hprod := ha_ctrl'.mul htail hBamax_nonneg
    have hprod' :
        ParabolicC0AlphaWith
          (max (B a) 1 * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1))
          (max (B a) 1 *
              ((∑ i ∈ S, H i) * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) +
            (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a)
          α (fun z => ∏ i ∈ insert a S, u i z) s := by
      simpa [Finset.prod_insert ha] using hprod
    refine hprod'.mono_const ?_ ?_
    · rw [Finset.prod_insert ha]
      ring_nf
      exact le_refl (max (B a) 1 * max ‖(1 : A)‖ 1 * ∏ x ∈ S, max (B x) 1)
    · rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hHtail_nonneg : 0 ≤ ∑ i ∈ S, H i :=
        Finset.sum_nonneg fun i hi => hH i (by simp [hi])
      have hunit_nonneg : 0 ≤ max ‖(1 : A)‖ 1 :=
        zero_le_one.trans (le_max_right _ _)
      have hBtail_nonneg : 0 ≤ max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1 :=
        mul_nonneg hunit_nonneg
          (Finset.prod_nonneg fun i hi => (zero_le_one.trans (le_max_right (B i) 1)))
      have hHa_nonneg : 0 ≤ H a := hH a (by simp [ha])
      have hBamax_ge_one : 1 ≤ max (B a) 1 := le_max_right _ _
      have hHa_term :
          (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a ≤
            max (B a) 1 *
              ((max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a) := by
        calc
          (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a
              = 1 * ((max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a) := by ring
          _ ≤ max (B a) 1 *
                ((max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a) :=
            mul_le_mul_of_nonneg_right hBamax_ge_one
              (mul_nonneg hBtail_nonneg hHa_nonneg)
      calc
        max (B a) 1 *
              ((∑ i ∈ S, H i) *
                (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) +
            (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a
            ≤
              max (B a) 1 *
                  ((∑ i ∈ S, H i) *
                    (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) +
                max (B a) 1 *
                  ((max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1) * H a) := by
              exact add_le_add_right hHa_term _
        _ = (H a + ∑ x ∈ S, H x) *
              (max ‖(1 : A)‖ 1 * (max (B a) 1 * ∏ x ∈ S, max (B x) 1)) := by
              ring

/-- Finite products are locally Lipschitz in parabolic `C^{0,α}` form.  The Holder constant is
coarse but depends on the factor-difference controls, so it can feed contraction estimates. -/
theorem finset_prod_sub_prod {ι A : Type*} [NormedCommRing A] (S : Finset ι)
    {B H Bd Hd : ι → ℝ} {u v : ι → ℝ × X → A}
    (hH : ∀ i ∈ S, 0 ≤ H i)
    (hBd : ∀ i ∈ S, 0 ≤ Bd i)
    (hHd : ∀ i ∈ S, 0 ≤ Hd i)
    (hu : ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (u i) s)
    (hv : ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (v i) s)
    (hdiff : ∀ i ∈ S,
      ParabolicC0AlphaWith (Bd i) (Hd i) α (fun z => u i z - v i z) s) :
    ParabolicC0AlphaWith
      ((∑ i ∈ S, Bd i) *
        (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1))
      (((∑ i ∈ S, Hd i) + (∑ i ∈ S, H i) * (∑ i ∈ S, Bd i)) *
        (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1))
      α (fun z => (∏ i ∈ S, u i z) - ∏ i ∈ S, v i z) s := by
  classical
  revert hH hBd hHd hu hv hdiff
  refine Finset.induction_on S ?base ?step
  · intro _hH _hBd _hHd _hu _hv _hdiff
    simpa using
      (ParabolicC0AlphaWith.const (s := s) (α := α) (B := 0) (H := 0)
        (0 : A) (by simp) le_rfl)
  · intro a S ha ih hH hBd hHd hu hv hdiff
    let Utail : ℝ := max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1
    let Dtail : ℝ := ∑ i ∈ S, Bd i
    let Htail : ℝ := ∑ i ∈ S, H i
    let Hdtail : ℝ := ∑ i ∈ S, Hd i
    have hBamax_nonneg : 0 ≤ max (B a) 1 := zero_le_one.trans (le_max_right _ _)
    have hBamax_ge_one : 1 ≤ max (B a) 1 := le_max_right _ _
    have hUtail_nonneg : 0 ≤ Utail := by
      dsimp [Utail]
      exact mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (B i) 1))
    have hDtail_nonneg : 0 ≤ Dtail := by
      dsimp [Dtail]
      exact Finset.sum_nonneg fun i hi => hBd i (Finset.mem_insert_of_mem hi)
    have hHtail_nonneg : 0 ≤ Htail := by
      dsimp [Htail]
      exact Finset.sum_nonneg fun i hi => hH i (Finset.mem_insert_of_mem hi)
    have hHdtail_nonneg : 0 ≤ Hdtail := by
      dsimp [Hdtail]
      exact Finset.sum_nonneg fun i hi => hHd i (Finset.mem_insert_of_mem hi)
    have hBda_nonneg : 0 ≤ Bd a := hBd a (Finset.mem_insert_self a S)
    have hHa_nonneg : 0 ≤ H a := hH a (Finset.mem_insert_self a S)
    have hHda_nonneg : 0 ≤ Hd a := hHd a (Finset.mem_insert_self a S)
    have hau :
        ParabolicC0AlphaWith (max (B a) 1) (H a) α (u a) s :=
      (hu a (Finset.mem_insert_self a S)).mono_const (le_max_left _ _) le_rfl
    have htail_v :
        ParabolicC0AlphaWith
          Utail (Htail * Utail) α (fun z => ∏ i ∈ S, v i z) s := by
      dsimp [Utail, Htail]
      simpa using
        (ParabolicC0AlphaWith.finset_prod (X := X) (α := α) (s := s)
          (S := S) (B := B) (H := H) (u := v)
          (fun i hi => hH i (Finset.mem_insert_of_mem hi))
          (fun i hi => hv i (Finset.mem_insert_of_mem hi)))
    have htail_diff :
        ParabolicC0AlphaWith
          (Dtail * Utail)
          ((Hdtail + Htail * Dtail) * Utail)
          α (fun z => (∏ i ∈ S, u i z) - ∏ i ∈ S, v i z) s := by
      dsimp [Utail, Dtail, Htail, Hdtail]
      simpa using
        (ih
          (fun i hi => hH i (Finset.mem_insert_of_mem hi))
          (fun i hi => hBd i (Finset.mem_insert_of_mem hi))
          (fun i hi => hHd i (Finset.mem_insert_of_mem hi))
          (fun i hi => hu i (Finset.mem_insert_of_mem hi))
          (fun i hi => hv i (Finset.mem_insert_of_mem hi))
          (fun i hi => hdiff i (Finset.mem_insert_of_mem hi)))
    have hraw :
        ParabolicC0AlphaWith
          (max (B a) 1 * (Dtail * Utail) + Bd a * Utail)
          ((max (B a) 1 * ((Hdtail + Htail * Dtail) * Utail) +
              (Dtail * Utail) * H a) +
            (Bd a * (Htail * Utail) + Utail * Hd a))
          α
          (fun z => u a z * (∏ i ∈ S, u i z) -
            v a z * ∏ i ∈ S, v i z) s :=
      hau.mul_sub_mul htail_v (hdiff a (Finset.mem_insert_self a S)) htail_diff
        hBamax_nonneg hBda_nonneg
    have hB_le :
        max (B a) 1 * (Dtail * Utail) + Bd a * Utail ≤
          ((∑ i ∈ insert a S, Bd i) *
            (max ‖(1 : A)‖ 1 * ∏ i ∈ insert a S, max (B i) 1)) := by
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      dsimp [Dtail, Utail]
      calc
        max (B a) 1 * ((∑ i ∈ S, Bd i) *
              (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) +
            Bd a * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)
            ≤
          max (B a) 1 * ((∑ i ∈ S, Bd i) *
              (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) +
            max (B a) 1 *
              (Bd a * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) := by
            refine add_le_add (le_rfl) ?_
            calc
              Bd a * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)
                  = 1 * (Bd a *
                    (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)) := by ring
              _ ≤ max (B a) 1 *
                    (Bd a * (max ‖(1 : A)‖ 1 *
                      ∏ i ∈ S, max (B i) 1)) :=
                mul_le_mul_of_nonneg_right hBamax_ge_one
                  (mul_nonneg hBda_nonneg hUtail_nonneg)
        _ =
          (Bd a + ∑ i ∈ S, Bd i) *
            (max ‖(1 : A)‖ 1 * (max (B a) 1 *
              ∏ i ∈ S, max (B i) 1)) := by
            ring
    have hH_le :
        (max (B a) 1 * ((Hdtail + Htail * Dtail) * Utail) +
              (Dtail * Utail) * H a) +
            (Bd a * (Htail * Utail) + Utail * Hd a) ≤
          (((∑ i ∈ insert a S, Hd i) +
              (∑ i ∈ insert a S, H i) * (∑ i ∈ insert a S, Bd i)) *
            (max ‖(1 : A)‖ 1 * ∏ i ∈ insert a S, max (B i) 1)) := by
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.prod_insert ha]
      dsimp [Dtail, Htail, Hdtail, Utail]
      let m : ℝ := max (B a) 1
      let U : ℝ := max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1
      let D : ℝ := ∑ i ∈ S, Bd i
      let G : ℝ := ∑ i ∈ S, H i
      let E : ℝ := ∑ i ∈ S, Hd i
      have hm_nonneg : 0 ≤ m := by
        dsimp [m]
        exact hBamax_nonneg
      have hm_ge_one : 1 ≤ m := by
        dsimp [m]
        exact hBamax_ge_one
      have hU_nonneg : 0 ≤ U := by
        dsimp [U]
        exact hUtail_nonneg
      have hD_nonneg : 0 ≤ D := by
        dsimp [D]
        exact hDtail_nonneg
      have hG_nonneg : 0 ≤ G := by
        dsimp [G]
        exact hHtail_nonneg
      have hE_nonneg : 0 ≤ E := by
        dsimp [E]
        exact hHdtail_nonneg
      have hraw_le :
          (m * ((E + G * D) * U) + (D * U) * H a) +
              (Bd a * (G * U) + U * Hd a) ≤
            (m * ((E + G * D) * U) +
                m * ((D * U) * H a)) +
              (m * (Bd a * (G * U)) + m * (U * Hd a)) := by
        refine add_le_add ?_ ?_
        · refine add_le_add (le_rfl) ?_
          calc
            (D * U) * H a = 1 * ((D * U) * H a) := by ring
            _ ≤ m * ((D * U) * H a) :=
              mul_le_mul_of_nonneg_right hm_ge_one
                (mul_nonneg (mul_nonneg hD_nonneg hU_nonneg) hHa_nonneg)
        · exact add_le_add
            (by
              calc
                Bd a * (G * U) = 1 * (Bd a * (G * U)) := by ring
                _ ≤ m * (Bd a * (G * U)) :=
                  mul_le_mul_of_nonneg_right hm_ge_one
                    (mul_nonneg hBda_nonneg (mul_nonneg hG_nonneg hU_nonneg)))
            (by
              calc
                U * Hd a = 1 * (U * Hd a) := by ring
                _ ≤ m * (U * Hd a) :=
                  mul_le_mul_of_nonneg_right hm_ge_one
                    (mul_nonneg hU_nonneg hHda_nonneg))
      calc
        (m * ((E + G * D) * U) + (D * U) * H a) +
              (Bd a * (G * U) + U * Hd a)
            ≤
          (m * ((E + G * D) * U) + m * ((D * U) * H a)) +
              (m * (Bd a * (G * U)) + m * (U * Hd a)) := hraw_le
        _ ≤ ((Hd a + E) + (H a + G) * (Bd a + D)) * (m * U) := by
          have hextra_nonneg : 0 ≤ m * ((H a * Bd a) * U) :=
            mul_nonneg hm_nonneg (mul_nonneg (mul_nonneg hHa_nonneg hBda_nonneg) hU_nonneg)
          calc
            (m * ((E + G * D) * U) + m * ((D * U) * H a)) +
                (m * (Bd a * (G * U)) + m * (U * Hd a))
                ≤
              (m * ((E + G * D) * U) + m * ((D * U) * H a)) +
                  (m * (Bd a * (G * U)) + m * (U * Hd a)) +
                m * ((H a * Bd a) * U) := by linarith
            _ = ((Hd a + E) + (H a + G) * (Bd a + D)) * (m * U) := by
              ring
        _ =
          ((Hd a + ∑ x ∈ S, Hd x) +
              (H a + ∑ x ∈ S, H x) * (Bd a + ∑ x ∈ S, Bd x)) *
            (max ‖(1 : A)‖ 1 * (max (B a) 1 *
              ∏ x ∈ S, max (B x) 1)) := by
          dsimp [m, U, D, G, E]
          ring
    convert (hraw.mono_const hB_le hH_le) using 1
    ext z
    simp [Finset.prod_insert ha]

theorem smul_fun {𝕜 F : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {B₁ B₂ H₁ H₂ α : ℝ} {a : ℝ × X → 𝕜} {u : ℝ × X → F} {s : Set (ℝ × X)}
    (ha : ParabolicC0AlphaWith B₁ H₁ α a s)
    (hu : ParabolicC0AlphaWith B₂ H₂ α u s)
    (hB₁ : 0 ≤ B₁) :
    ParabolicC0AlphaWith (B₁ * B₂) (B₁ * H₂ + B₂ * H₁) α
      (fun z => a z • u z) s := by
  constructor
  · exact ha.bounded.smul_fun hu.bounded hB₁
  · exact ha.holder.smul_fun hu.holder ha.bounded hu.bounded hB₁

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith (‖c‖ * B) (‖c‖ * H) α (fun z => c • u z) s :=
  ⟨hu.bounded.smul c, hu.holder.smul c⟩

/-- A continuous linear map preserves parabolic `C^{0,α}` control, with the operator norm
multiplying both the sup and Holder constants. -/
theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaWith (‖L‖ * B) (‖L‖ * H) α (fun z => L (u z)) s :=
  ⟨hu.bounded.continuousLinearMap L, hu.holder.continuousLinearMap L⟩

/-- A curried continuous bilinear map preserves parabolic `C^{0,α}` control. -/
theorem continuousLinearMap₂ {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {B₂ H₂ : ℝ} {v : ℝ × X → F}
    (L : E →L[ℝ] F →L[ℝ] G)
    (hu : ParabolicC0AlphaWith B H α u s)
    (hv : ParabolicC0AlphaWith B₂ H₂ α v s)
    (hB : 0 ≤ B) :
    ParabolicC0AlphaWith (‖L‖ * B * B₂)
      (‖L‖ * (B * H₂ + B₂ * H)) α (fun z => L (u z) (v z)) s := by
  constructor
  · exact hu.bounded.continuousLinearMap₂ L hv.bounded hB
  · exact hu.holder.continuousLinearMap₂ L hv.holder hu.bounded hv.bounded hB

/-- Differences of curried continuous bilinear-map applications inherit parabolic `C^{0,α}`
control from one left input, one right input, and `C^{0,α}` controls of the two input
differences. -/
theorem continuousLinearMap₂_sub {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {Bu Hu Bv Hv Bdu Hdu Bdv Hdv α : ℝ}
    {u u' : ℝ × X → E} {v v' : ℝ × X → F} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith Bu Hu α u s)
    (hv' : ParabolicC0AlphaWith Bv Hv α v' s)
    (hdu : ParabolicC0AlphaWith Bdu Hdu α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaWith Bdv Hdv α (fun z => v z - v' z) s)
    (hBu : 0 ≤ Bu) (hBdu : 0 ≤ Bdu) :
    ParabolicC0AlphaWith (‖L‖ * Bu * Bdv + ‖L‖ * Bdu * Bv)
      (‖L‖ * (Bu * Hdv + Bdv * Hu) + ‖L‖ * (Bdu * Hv + Bv * Hdu)) α
      (fun z => L (u z) (v z) - L (u' z) (v' z)) s := by
  constructor
  · exact hu.bounded.continuousLinearMap₂_sub L hv'.bounded hdu.bounded hdv.bounded
      hBu hBdu
  · exact hu.holder.continuousLinearMap₂_sub L hv'.holder hdu.holder hdv.holder
      hu.bounded hv'.bounded hdu.bounded hdv.bounded hBu hBdu

/-- Applying an operator-valued function to a vector-valued function preserves parabolic
`C^{0,α}` control with the usual product-rule Holder constant. -/
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A : ℝ × X → E →L[ℝ] F} {v : ℝ × X → E}
    {BA HA Bv Hv : ℝ}
    (hA : ParabolicC0AlphaWith BA HA α A s)
    (hv : ParabolicC0AlphaWith Bv Hv α v s)
    (hBA : 0 ≤ BA) :
    ParabolicC0AlphaWith (BA * Bv) (BA * Hv + Bv * HA) α
      (fun z => A z (v z)) s := by
  constructor
  · exact hA.bounded.continuousLinearMap_apply hv.bounded hBA
  · exact hA.holder.continuousLinearMap_apply hv.holder hA.bounded hv.bounded hBA

/-- Differences of operator-valued applications inherit parabolic `C^{0,α}` control from one
operator input, one vector input, and `C^{0,α}` controls of the operator and vector differences. -/
theorem continuousLinearMap_apply_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A A' : ℝ × X → E →L[ℝ] F} {v v' : ℝ × X → E}
    {BA HA Bv Hv BAd HAd Bvd Hvd α : ℝ}
    (hA : ParabolicC0AlphaWith BA HA α A s)
    (hv' : ParabolicC0AlphaWith Bv Hv α v' s)
    (hAdiff : ParabolicC0AlphaWith BAd HAd α (fun z => A z - A' z) s)
    (hvdiff : ParabolicC0AlphaWith Bvd Hvd α (fun z => v z - v' z) s)
    (hBA : 0 ≤ BA) (hBAd : 0 ≤ BAd) :
    ParabolicC0AlphaWith (BA * Bvd + BAd * Bv)
      ((BA * Hvd + Bvd * HA) + (BAd * Hv + Bv * HAd)) α
      (fun z => A z (v z) - A' z (v' z)) s := by
  constructor
  · exact hA.bounded.continuousLinearMap_apply_sub hv'.bounded hAdiff.bounded
      hvdiff.bounded hBA hBAd
  · exact hA.holder.continuousLinearMap_apply_sub hv'.holder hAdiff.holder
      hvdiff.holder hA.bounded hv'.bounded hAdiff.bounded hvdiff.bounded hBA hBAd

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

theorem comp_lipschitzOnWith_of_closedBall_auto_bound {F : Type*} [NormedAddCommGroup F]
    {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaWith B H α u s) (hB : 0 ≤ B)
    (hφ : LipschitzOnWith K φ (Metric.closedBall (0 : E) B)) :
    ParabolicC0AlphaWith (‖φ (0 : E)‖ + (K : ℝ) * B) ((K : ℝ) * H) α
      (fun z => φ (u z)) s :=
  ⟨hu.bounded.comp_lipschitzOnWith_of_closedBall hB hφ,
    hu.holder.comp_lipschitzOnWith (hφ.mono hu.bounded.image_subset_closedBall_zero)⟩

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicC0AlphaWith B H α u s) (hφ : LipschitzWith K φ) :
    ParabolicC0AlphaWith (‖φ (0 : E)‖ + (K : ℝ) * B) ((K : ℝ) * H) α
      (fun z => φ (u z)) s :=
  ⟨hu.bounded.comp_lipschitzWith hφ, hu.holder.comp_lipschitzWith hφ⟩

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

/-- Spatial boundedness and Lipschitz control on the projection give fixed-constant parabolic
`C^{0,α}` control on subsets of a closed parabolic ball of diameter at most one. -/
theorem of_snd_lipschitzOnWith_of_subset_closedBall {K : ℝ≥0} {f : X → E}
    {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.2) s := by
  have hbase :=
    of_snd_lipschitzOnWith (s := s) (B := B) (K := K) (f := f) hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (NNReal.coe_nonneg K) hα_nonneg hα_le_one hs hR

/-- Time-only boundedness and Lipschitz control give fixed-constant parabolic `C^{0,α}` control
on subsets of a closed parabolic ball of diameter at most one. -/
theorem of_fst_lipschitzOnWith_of_subset_closedBall {K : ℝ≥0} {f : ℝ → E}
    {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.1) s := by
  have hbase :=
    of_fst_lipschitzOnWith (s := s) (B := B) (K := K) (f := f) hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (NNReal.coe_nonneg K) hα_nonneg hα_le_two hs hR

/-- Spatial boundedness and Lipschitz control on the projection give fixed-constant parabolic
`C^{0,α}` control on subsets of a closed parabolic cylinder of diameter at most one. -/
theorem of_snd_lipschitzOnWith_of_subset_closedCylinder {K : ℝ≥0} {f : X → E}
    {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.2) s := by
  have hbase :=
    of_snd_lipschitzOnWith (s := s) (B := B) (K := K) (f := f) hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (NNReal.coe_nonneg K) hα_nonneg hα_le_one hs hdiam

/-- Time-only boundedness and Lipschitz control give fixed-constant parabolic `C^{0,α}` control
on subsets of a closed parabolic cylinder of diameter at most one. -/
theorem of_fst_lipschitzOnWith_of_subset_closedCylinder {K : ℝ≥0} {f : ℝ → E}
    {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith B (K : ℝ) α (fun z : ℝ × X => f z.1) s := by
  have hbase :=
    of_fst_lipschitzOnWith (s := s) (B := B) (K := K) (f := f) hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (NNReal.coe_nonneg K) hα_nonneg hα_le_two hs hdiam

/-- Pullback of parabolic `C^{0,α}` control along a map `φ : ℝ × Y → ℝ × X` that maps `t`
into `s` and expands parabolic distance by at most a factor `L`.  The sup bound `B` is
preserved and the Hölder constant `H` scales by `L ^ α`.  This packages the abstract
change-of-variables lemma behind parabolic (Schauder) scaling. -/
theorem comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicC0AlphaWith B (H * L ^ α) α (fun p => u (φ p)) t :=
  ⟨hu.bounded.comp_mapsTo hmaps,
    hu.holder.comp_parabolicDistanceLe hH hα hL hmaps hφ⟩

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

/-- Local-to-global parabolic `C^{0,α}` control from a finite product-parabolic-cylinder cover,
with local constants chosen automatically and summed over the finite cover. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder {timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y timeRadius spaceRadius)
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaOn α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
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
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius)) := by
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
      ∀ y ∈ N, ParabolicC0AlphaWith Bsum Hsum α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius)) := by
    intro y hy
    exact (hBH y hy).mono_const (hB_le_sum y hy) (hH_le_sum y hy)
  refine ⟨Bsum, hBsum_nonneg,
    max Hsum (2 * Bsum / (min (Real.sqrt timeRadius) spaceRadius) ^ α),
    hHsum_nonneg.trans (le_max_left _ _), ?_⟩
  exact ParabolicC0AlphaWith.of_parabolicCylinder_cover_closedCylinder
    (B := Bsum) (H := Hsum) hα htime hspace hcover hlocal_sum

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

/-- Local-to-global parabolic `C^{0,α}` control from a finite cover by variable-radius product
parabolic cylinders.  The global sup constant is the sum of local sup constants, and the Holder
constant is supplied by the variable-radius cylinder Holder patching theorem. -/
theorem of_finset_parabolicCylinder_cover_closedCylinder_variable {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hlocal : ∀ y ∈ N, ParabolicC0AlphaOn α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
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
      ∀ y ∈ N, ParabolicBoundedWith (Bc y) u
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
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
    rcases mem_iUnion.1 hy with ⟨hyN, hpcy⟩
    have hpclosed :
        p ∈ parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y) :=
      parabolicCylinder.mem_closedCylinder_two_of_mem hpcy
    exact (hBlocal y hyN hpclosed).trans (hB_le_sum y hyN)
  rcases ParabolicHolderOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      (B := Bsum) N timeRadius spaceRadius hbounded hα htime_pos hspace_pos hcover
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

/-- Compact local-to-global parabolic `C^{0,α}` control from point-dependent doubled
closed-cylinder estimates, with all constants and cover radii chosen on a finite compact subcover. -/
theorem of_isCompact_of_local_closedCylinder_variable {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α) (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaOn α u
      (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y))) :
    ParabolicC0AlphaOn α u K := by
  rcases hK.elim_nhds_subcover
      (fun y => parabolicCylinder y (timeRadius y) (spaceRadius y))
      (fun y hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius y)
        (spaceRadius := spaceRadius y) (htime_pos y hy) (hspace_pos y hy)) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicCylinder_cover_closedCylinder_variable N timeRadius spaceRadius hα
    (fun y hy => htime_pos y (hNK y hy))
    (fun y hy => hspace_pos y (hNK y hy)) hcover
    (fun y hy => hlocal y (hNK y hy))

/-- Compact local-to-global parabolic `C^{0,α}` control from pointwise positive local
product-cylinder radii, with the radii, cover, and constants chosen automatically. -/
theorem of_isCompact_of_exists_local_closedCylinder {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      ParabolicC0AlphaOn α u
        (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicC0AlphaOn α u K := by
  classical
  let timeRadius : ℝ × X → ℝ :=
    fun y => if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  let spaceRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ K then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 1
  have htime_pos : ∀ y ∈ K, 0 < timeRadius y := by
    intro y hy
    dsimp [timeRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hspace_pos : ∀ y ∈ K, 0 < spaceRadius y := by
    intro y hy
    dsimp [spaceRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hlocalR :
      ∀ y ∈ K, ParabolicC0AlphaOn α u
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2
  exact of_isCompact_of_local_closedCylinder_variable hK hα timeRadius spaceRadius
    htime_pos hspace_pos hlocalR

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

/-- Compact local-to-global parabolic `C^{0,α}` control from local doubled closed-cylinder
estimates, with all constants chosen automatically from a finite compact subcover. -/
theorem of_isCompact_of_local_closedCylinder {timeRadius spaceRadius : ℝ}
    {K : Set (ℝ × X)}
    (hK : IsCompact K) (hα : 0 < α)
    (htime : 0 < timeRadius) (hspace : 0 < spaceRadius)
    (hlocal : ∀ y ∈ K, ParabolicC0AlphaOn α u
      (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) :
    ParabolicC0AlphaOn α u K := by
  rcases hK.elim_nhds_subcover (fun y => parabolicCylinder y timeRadius spaceRadius)
      (fun y _hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius)
        (spaceRadius := spaceRadius) htime hspace) with
    ⟨N, hNK, hcover⟩
  exact of_finset_parabolicCylinder_cover_closedCylinder N hα htime hspace hcover
    (fun y hy => hlocal y (hNK y hy))

theorem const (c : E) : ParabolicC0AlphaOn α (fun _ : ℝ × X => c) s :=
  ⟨‖c‖, norm_nonneg c, 0, le_rfl, ParabolicC0AlphaWith.const c le_rfl le_rfl⟩

/-- Spatial boundedness and Lipschitz control on the projection give parabolic `C^{0,1}`
control for the time-independent lift. -/
theorem of_snd_lipschitzOnWith {B : ℝ} {K : ℝ≥0} {f : X → E}
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s)) :
    ParabolicC0AlphaOn 1 (fun z : ℝ × X => f z.2) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_snd_lipschitzOnWith hB hL⟩

/-- Spatial boundedness and Holder control on the projection give parabolic `C^{0,α}` control
for the time-independent lift. -/
theorem of_snd_holder {B H : ℝ} {f : X → E}
    (hB_nonneg : 0 ≤ B) (hH_nonneg : 0 ≤ H) (hα : 0 ≤ α)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hf : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄, y ∈ Prod.snd '' s →
      ‖f x - f y‖ ≤ H * (dist x y) ^ α) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.2) s :=
  ⟨B, hB_nonneg, H, hH_nonneg, ParabolicC0AlphaWith.of_snd_holder hB hH_nonneg hα hf⟩

/-- Time-only boundedness and Holder control with exponent `α / 2` give existential parabolic
`C^{0,α}` control for the time-only lift. -/
theorem of_fst_holder {B H : ℝ} {f : ℝ → E}
    (hB_nonneg : 0 ≤ B) (hH_nonneg : 0 ≤ H) (hα : 0 ≤ α)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hf : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄, τ ∈ Prod.fst '' s →
      ‖f t - f τ‖ ≤ H * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.1) s :=
  ⟨B, hB_nonneg, H, hH_nonneg, ParabolicC0AlphaWith.of_fst_holder hB hH_nonneg hα hf⟩

/-- Time-only boundedness and Lipschitz control give existential parabolic `C^{0,2}` control for
the time-only lift. -/
theorem of_fst_lipschitzOnWith {B : ℝ} {K : ℝ≥0} {f : ℝ → E}
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s)) :
    ParabolicC0AlphaOn 2 (fun z : ℝ × X => f z.1) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_fst_lipschitzOnWith hB hL⟩

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

/-- Finite sums of termwise differences preserve existential parabolic `C^{0,α}` control from
the termwise difference controls. -/
theorem sum_sub_sum {ι : Type*} (S : Finset ι) {u v : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaOn α (fun z => u i z - v i z) s) :
    ParabolicC0AlphaOn α (fun z => (∑ i ∈ S, u i z) - ∑ i ∈ S, v i z) s := by
  classical
  have hsum := ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s) S h
  convert hsum using 1
  ext z
  rw [Finset.sum_sub_distrib]

/-- Componentwise parabolic `C^{0,α}` control packages a finite vector-valued function as
parabolic `C^{0,α}`. -/
theorem pi {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ∀ i, ParabolicC0AlphaOn α (fun z => u z i) s) :
    ParabolicC0AlphaOn α u s := by
  classical
  let B : ι → ℝ := fun i => Classical.choose (h i)
  let H : ι → ℝ := fun i => Classical.choose (Classical.choose_spec (h i)).2
  have hBnonneg : ∀ i, 0 ≤ B i := by
    intro i
    dsimp [B]
    exact (Classical.choose_spec (h i)).1
  have hHnonneg : ∀ i, 0 ≤ H i := by
    intro i
    dsimp [H]
    exact (Classical.choose_spec (Classical.choose_spec (h i)).2).1
  have hBH :
      ∀ i, ParabolicC0AlphaWith (B i) (H i) α (fun z => u z i) s := by
    intro i
    dsimp [B, H]
    exact (Classical.choose_spec (Classical.choose_spec (h i)).2).2
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hBnonneg i,
    ∑ i, H i, Finset.sum_nonneg fun i _hi => hHnonneg i, ?_⟩
  exact ParabolicC0AlphaWith.pi hBnonneg hHnonneg hBH

/-- A Pi-valued parabolic `C^{0,α}` estimate restricts to each component. -/
theorem eval {ι : Type*} [Fintype ι] {u : ℝ × X → ι → E}
    (h : ParabolicC0AlphaOn α u s) (i : ι) :
    ParabolicC0AlphaOn α (fun z => u z i) s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H, hH, hBH.eval i⟩

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

theorem zsmul (n : ℤ) (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => n • u z) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨‖n‖ * B, mul_nonneg (norm_nonneg n) hB,
    ‖n‖ * H, mul_nonneg (norm_nonneg n) hH, hBH.zsmul n⟩

theorem prod {F : Type*} [NormedAddCommGroup F] {v : ℝ × X → F}
    (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => (u z, v z)) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨max B₁ B₂, hB₁.trans (le_max_left B₁ B₂), max H₁ H₂,
    hH₁.trans (le_max_left H₁ H₂),
    hBH₁.prod hBH₂⟩

theorem inv {𝕜 : Type*} [NormedField 𝕜] {a : ℝ × X → 𝕜} {δ : ℝ}
    (ha : ParabolicC0AlphaOn α a s) (hδpos : 0 < δ)
    (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖) :
    ParabolicC0AlphaOn α (fun z => (a z)⁻¹) s := by
  rcases ha with ⟨B, hB, H, hH, hBH⟩
  refine ⟨δ⁻¹, inv_nonneg.mpr hδpos.le, δ⁻¹ * H * δ⁻¹, ?_, hBH.inv hδpos hδ⟩
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hδpos.le) hH) (inv_nonneg.mpr hδpos.le)

/-- Reciprocal differences preserve existential parabolic `C^{0,α}` control
from a difference control and a common pointwise lower bound. -/
theorem inv_sub_inv {𝕜 : Type*} [NormedField 𝕜] {a b : ℝ × X → 𝕜} {δ : ℝ}
    (ha : ParabolicC0AlphaOn α a s) (hb : ParabolicC0AlphaOn α b s)
    (hdiff : ParabolicC0AlphaOn α (fun z => a z - b z) s)
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖) :
    ParabolicC0AlphaOn α (fun z => (a z)⁻¹ - (b z)⁻¹) s := by
  rcases ha with ⟨_Ba, _hBa, Ha, hHa, hBHa⟩
  rcases hb with ⟨_Bb, _hBb, Hb, hHb, hBHb⟩
  rcases hdiff with ⟨Bd, hBd, Hd, hHd, hBHd⟩
  exact ⟨ParabolicC0AlphaWith.invSubBoundConst δ Bd,
    ParabolicC0AlphaWith.invSubBoundConst_nonneg hδpos hBd,
    ParabolicC0AlphaWith.invSubHolderConst δ Ha Hb Bd Hd,
    ParabolicC0AlphaWith.invSubHolderConst_nonneg hδpos hHa hHb hBd hHd,
    hBHa.inv_sub_inv hBHb hBHd hδpos hδa hδb hBd⟩

theorem mul {A : Type*} [NormedRing A] {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => u z * v z) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  exact ⟨B₁ * B₂, mul_nonneg hB₁ hB₂,
    B₁ * H₂ + B₂ * H₁, add_nonneg (mul_nonneg hB₁ hH₂) (mul_nonneg hB₂ hH₁),
    hBH₁.mul hBH₂ hB₁⟩

/-- Finite sums of products preserve existential parabolic `C^{0,α}` control from factorwise
controls. -/
theorem finset_sum_mul {ι A : Type*} [NormedRing A] (S : Finset ι)
    {u v : ι → ℝ × X → A}
    (hu : ∀ i ∈ S, ParabolicC0AlphaOn α (u i) s)
    (hv : ∀ i ∈ S, ParabolicC0AlphaOn α (v i) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i ∈ S, u i z * v i z) s :=
  ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s) S fun i hi =>
    (hu i hi).mul (hv i hi)

/-- Product differences preserve existential parabolic `C^{0,α}` control from one left factor,
one right factor, and controls of the two factor differences. -/
theorem mul_sub_mul {A : Type*} [NormedRing A] {u u' v v' : ℝ × X → A}
    (hu : ParabolicC0AlphaOn α u s) (hv' : ParabolicC0AlphaOn α v' s)
    (hdu : ParabolicC0AlphaOn α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaOn α (fun z => v z - v' z) s) :
    ParabolicC0AlphaOn α (fun z => u z * v z - u' z * v' z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hBHu⟩
  rcases hv' with ⟨Bv, hBv, Hv, hHv, hBHv⟩
  rcases hdu with ⟨Bdu, hBdu, Hdu, hHdu, hBHdu⟩
  rcases hdv with ⟨Bdv, hBdv, Hdv, hHdv, hBHdv⟩
  refine ⟨Bu * Bdv + Bdu * Bv, ?_,
    (Bu * Hdv + Bdv * Hu) + (Bdu * Hv + Bv * Hdu), ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hBu hBdv) (mul_nonneg hBdu hBv)
  · exact add_nonneg
      (add_nonneg (mul_nonneg hBu hHdv) (mul_nonneg hBdv hHu))
      (add_nonneg (mul_nonneg hBdu hHv) (mul_nonneg hBv hHdu))
  · exact hBHu.mul_sub_mul hBHv hBHdu hBHdv hBu hBdu

/-- Finite sums of product differences preserve existential parabolic `C^{0,α}` control from
factorwise controls and factor-difference controls. -/
theorem finset_sum_mul_sub_sum_mul {ι A : Type*} [NormedRing A] (S : Finset ι)
    {u u' v v' : ι → ℝ × X → A}
    (hu : ∀ i ∈ S, ParabolicC0AlphaOn α (u i) s)
    (hv' : ∀ i ∈ S, ParabolicC0AlphaOn α (v' i) s)
    (hdu : ∀ i ∈ S, ParabolicC0AlphaOn α (fun z => u i z - u' i z) s)
    (hdv : ∀ i ∈ S, ParabolicC0AlphaOn α (fun z => v i z - v' i z) s) :
    ParabolicC0AlphaOn α
      (fun z => (∑ i ∈ S, u i z * v i z) - ∑ i ∈ S, u' i z * v' i z) s := by
  classical
  have hterm : ∀ i ∈ S,
      ParabolicC0AlphaOn α (fun z => u i z * v i z - u' i z * v' i z) s := by
    intro i hi
    exact (hu i hi).mul_sub_mul (hv' i hi) (hdu i hi) (hdv i hi)
  have hsum := ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s) S hterm
  convert hsum using 1
  ext z
  rw [Finset.sum_sub_distrib]

theorem div {𝕜 : Type*} [NormedField 𝕜] {a b : ℝ × X → 𝕜} {δ : ℝ}
    (ha : ParabolicC0AlphaOn α a s) (hb : ParabolicC0AlphaOn α b s)
    (hδpos : 0 < δ) (hδ : ∀ ⦃p : ℝ × X⦄, p ∈ s → δ ≤ ‖b p‖) :
    ParabolicC0AlphaOn α (fun z => a z / b z) s := by
  rcases ha with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hb with ⟨B₂, _hB₂, H₂, hH₂, hBH₂⟩
  refine ⟨B₁ * δ⁻¹, mul_nonneg hB₁ (inv_nonneg.mpr hδpos.le),
    B₁ * (δ⁻¹ * H₂ * δ⁻¹) + δ⁻¹ * H₁, ?_,
    hBH₁.div hBH₂ hB₁ hδpos hδ⟩
  exact add_nonneg
    (mul_nonneg hB₁
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hδpos.le) hH₂)
        (inv_nonneg.mpr hδpos.le)))
    (mul_nonneg (inv_nonneg.mpr hδpos.le) hH₁)

theorem finset_prod {ι A : Type*} [NormedCommRing A] (S : Finset ι)
    {u : ι → ℝ × X → A}
    (h : ∀ i ∈ S, ParabolicC0AlphaOn α (u i) s) :
    ParabolicC0AlphaOn α (fun z => ∏ i ∈ S, u i z) s := by
  classical
  revert h
  refine Finset.induction_on S ?base ?step
  · intro _h
    simpa using (ParabolicC0AlphaOn.const (α := α) (s := s) (1 : A))
  · intro a S ha ih h
    have ha_c0α : ParabolicC0AlphaOn α (u a) s := h a (by simp [ha])
    have htail : ParabolicC0AlphaOn α (fun z => ∏ i ∈ S, u i z) s :=
      ih fun i hi => h i (by simp [hi])
    simpa [Finset.prod_insert ha] using ha_c0α.mul htail

/-- Finite product differences preserve existential parabolic `C^{0,α}` control.  The proof
selects common factor bounds for the two products before applying the fixed-constant estimate. -/
theorem finset_prod_sub_prod {ι A : Type*} [NormedCommRing A] (S : Finset ι)
    {u v : ι → ℝ × X → A}
    (hu : ∀ i ∈ S, ParabolicC0AlphaOn α (u i) s)
    (hv : ∀ i ∈ S, ParabolicC0AlphaOn α (v i) s)
    (hdiff : ∀ i ∈ S, ParabolicC0AlphaOn α (fun z => u i z - v i z) s) :
    ParabolicC0AlphaOn α (fun z => (∏ i ∈ S, u i z) - ∏ i ∈ S, v i z) s := by
  classical
  let Bu : ι → ℝ := fun i => if hi : i ∈ S then Classical.choose (hu i hi) else 0
  let Hu : ι → ℝ := fun i =>
    if hi : i ∈ S then Classical.choose (Classical.choose_spec (hu i hi)).2 else 0
  let Bv : ι → ℝ := fun i => if hi : i ∈ S then Classical.choose (hv i hi) else 0
  let Hv : ι → ℝ := fun i =>
    if hi : i ∈ S then Classical.choose (Classical.choose_spec (hv i hi)).2 else 0
  let Bd : ι → ℝ := fun i => if hi : i ∈ S then Classical.choose (hdiff i hi) else 0
  let Hd : ι → ℝ := fun i =>
    if hi : i ∈ S then Classical.choose (Classical.choose_spec (hdiff i hi)).2 else 0
  let B : ι → ℝ := fun i => max (Bu i) (Bv i)
  let H : ι → ℝ := fun i => max (Hu i) (Hv i)
  have hBu_nonneg : ∀ i ∈ S, 0 ≤ Bu i := by
    intro i hi
    dsimp [Bu]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hu i hi)).1
  have hHu_nonneg : ∀ i ∈ S, 0 ≤ Hu i := by
    intro i hi
    dsimp [Hu]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (hu i hi)).2).1
  have hBv_nonneg : ∀ i ∈ S, 0 ≤ Bv i := by
    intro i hi
    dsimp [Bv]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hv i hi)).1
  have hHv_nonneg : ∀ i ∈ S, 0 ≤ Hv i := by
    intro i hi
    dsimp [Hv]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (hv i hi)).2).1
  have hBd_nonneg : ∀ i ∈ S, 0 ≤ Bd i := by
    intro i hi
    dsimp [Bd]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hdiff i hi)).1
  have hHd_nonneg : ∀ i ∈ S, 0 ≤ Hd i := by
    intro i hi
    dsimp [Hd]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (hdiff i hi)).2).1
  have hH_nonneg : ∀ i ∈ S, 0 ≤ H i := by
    intro i hi
    exact (hHu_nonneg i hi).trans (le_max_left (Hu i) (Hv i))
  have hu_with :
      ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (u i) s := by
    intro i hi
    have hctrl : ParabolicC0AlphaWith (Bu i) (Hu i) α (u i) s := by
      dsimp [Bu, Hu]
      rw [dif_pos hi, dif_pos hi]
      exact (Classical.choose_spec (Classical.choose_spec (hu i hi)).2).2
    exact hctrl.mono_const (le_max_left (Bu i) (Bv i)) (le_max_left (Hu i) (Hv i))
  have hv_with :
      ∀ i ∈ S, ParabolicC0AlphaWith (B i) (H i) α (v i) s := by
    intro i hi
    have hctrl : ParabolicC0AlphaWith (Bv i) (Hv i) α (v i) s := by
      dsimp [Bv, Hv]
      rw [dif_pos hi, dif_pos hi]
      exact (Classical.choose_spec (Classical.choose_spec (hv i hi)).2).2
    exact hctrl.mono_const (le_max_right (Bu i) (Bv i)) (le_max_right (Hu i) (Hv i))
  have hdiff_with :
      ∀ i ∈ S, ParabolicC0AlphaWith (Bd i) (Hd i) α (fun z => u i z - v i z) s := by
    intro i hi
    dsimp [Bd, Hd]
    rw [dif_pos hi, dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec (hdiff i hi)).2).2
  refine ⟨
    ((∑ i ∈ S, Bd i) * (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)), ?_,
    (((∑ i ∈ S, Hd i) + (∑ i ∈ S, H i) * (∑ i ∈ S, Bd i)) *
      (max ‖(1 : A)‖ 1 * ∏ i ∈ S, max (B i) 1)), ?_, ?_⟩
  · exact mul_nonneg
      (Finset.sum_nonneg hBd_nonneg)
      (mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (B i) 1)))
  · exact mul_nonneg
      (add_nonneg (Finset.sum_nonneg hHd_nonneg)
        (mul_nonneg (Finset.sum_nonneg hH_nonneg) (Finset.sum_nonneg hBd_nonneg)))
      (mul_nonneg (zero_le_one.trans (le_max_right _ _))
        (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (B i) 1)))
  · exact ParabolicC0AlphaWith.finset_prod_sub_prod (X := X) (α := α) (s := s)
      (S := S) (B := B) (H := H) (Bd := Bd) (Hd := Hd) (u := u) (v := v)
      hH_nonneg hBd_nonneg hHd_nonneg hu_with hv_with hdiff_with

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

theorem comp_lipschitzOnWith_of_closedBall_auto_bound {F : Type*} [NormedAddCommGroup F]
    {B : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaOn α u s) (hBound : ParabolicBoundedWith B u s) (hB : 0 ≤ B)
    (hφ : LipschitzOnWith K φ (Metric.closedBall (0 : E) B)) :
    ParabolicC0AlphaOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨_B, _hB, H, hH, hBH⟩
  refine ⟨‖φ (0 : E)‖ + (K : ℝ) * B,
    add_nonneg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg K) hB),
    (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_⟩
  exact ⟨hBound.comp_lipschitzOnWith_of_closedBall hB hφ,
    hBH.holder.comp_lipschitzOnWith (hφ.mono hBound.image_subset_closedBall_zero)⟩

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F] {K : ℝ≥0}
    {φ : E → F} (hu : ParabolicC0AlphaOn α u s) (hφ : LipschitzWith K φ) :
    ParabolicC0AlphaOn α (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  refine ⟨‖φ (0 : E)‖ + (K : ℝ) * B,
    add_nonneg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg K) hB),
    (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_⟩
  exact hBH.comp_lipschitzWith hφ

/-- A continuous linear map preserves existential parabolic `C^{0,α}` control. -/
theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaOn α (fun z => L (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨‖L‖ * B, mul_nonneg (norm_nonneg L) hB,
    ‖L‖ * H, mul_nonneg (norm_nonneg L) hH, hBH.continuousLinearMap L⟩

/-- A curried continuous bilinear map preserves existential parabolic `C^{0,α}` control. -/
theorem continuousLinearMap₂ {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {v : ℝ × X → F} (L : E →L[ℝ] F →L[ℝ] G)
    (hu : ParabolicC0AlphaOn α u s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => L (u z) (v z)) s := by
  rcases hu with ⟨B₁, hB₁, H₁, hH₁, hBH₁⟩
  rcases hv with ⟨B₂, hB₂, H₂, hH₂, hBH₂⟩
  refine ⟨‖L‖ * B₁ * B₂, ?_, ‖L‖ * (B₁ * H₂ + B₂ * H₁), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (norm_nonneg L) hB₁) hB₂
  · exact mul_nonneg (norm_nonneg L)
      (add_nonneg (mul_nonneg hB₁ hH₂) (mul_nonneg hB₂ hH₁))
  · exact hBH₁.continuousLinearMap₂ L hBH₂ hB₁

/-- Differences of curried continuous bilinear-map applications preserve
existential parabolic `C^{0,α}` control. -/
theorem continuousLinearMap₂_sub {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {u u' : ℝ × X → E} {v v' : ℝ × X → F}
    (hu : ParabolicC0AlphaOn α u s) (hv' : ParabolicC0AlphaOn α v' s)
    (hdu : ParabolicC0AlphaOn α (fun z => u z - u' z) s)
    (hdv : ParabolicC0AlphaOn α (fun z => v z - v' z) s) :
    ParabolicC0AlphaOn α (fun z => L (u z) (v z) - L (u' z) (v' z)) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hBHu⟩
  rcases hv' with ⟨Bv, hBv, Hv, hHv, hBHv⟩
  rcases hdu with ⟨Bdu, hBdu, Hdu, hHdu, hBHdu⟩
  rcases hdv with ⟨Bdv, hBdv, Hdv, hHdv, hBHdv⟩
  refine ⟨‖L‖ * Bu * Bdv + ‖L‖ * Bdu * Bv, ?_,
    ‖L‖ * (Bu * Hdv + Bdv * Hu) + ‖L‖ * (Bdu * Hv + Bv * Hdu), ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg L) hBu) hBdv)
      (mul_nonneg (mul_nonneg (norm_nonneg L) hBdu) hBv)
  · exact add_nonneg
      (mul_nonneg (norm_nonneg L)
        (add_nonneg (mul_nonneg hBu hHdv) (mul_nonneg hBdv hHu)))
      (mul_nonneg (norm_nonneg L)
        (add_nonneg (mul_nonneg hBdu hHv) (mul_nonneg hBv hHdu)))
  · exact hBHu.continuousLinearMap₂_sub L hBHv hBHdu hBHdv hBu hBdu

/-- Applying an operator-valued function to a vector-valued function preserves existential
parabolic `C^{0,α}` control. -/
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A : ℝ × X → E →L[ℝ] F} {v : ℝ × X → E}
    (hA : ParabolicC0AlphaOn α A s) (hv : ParabolicC0AlphaOn α v s) :
    ParabolicC0AlphaOn α (fun z => A z (v z)) s := by
  rcases hA with ⟨BA, hBA, HA, hHA, hABH⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hvBH⟩
  refine ⟨BA * Bv, mul_nonneg hBA hBv, BA * Hv + Bv * HA,
    add_nonneg (mul_nonneg hBA hHv) (mul_nonneg hBv hHA), ?_⟩
  exact hABH.continuousLinearMap_apply hvBH hBA

/-- Differences of operator-valued applications preserve existential
parabolic `C^{0,α}` control. -/
theorem continuousLinearMap_apply_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {A A' : ℝ × X → E →L[ℝ] F} {w w' : ℝ × X → E}
    (hA : ParabolicC0AlphaOn α A s) (hw' : ParabolicC0AlphaOn α w' s)
    (hAdiff : ParabolicC0AlphaOn α (fun z => A z - A' z) s)
    (hwdiff : ParabolicC0AlphaOn α (fun z => w z - w' z) s) :
    ParabolicC0AlphaOn α (fun z => A z (w z) - A' z (w' z)) s := by
  rcases hA with ⟨BA, hBA, HA, hHA, hABH⟩
  rcases hw' with ⟨Bw, hBw, Hw, hHw, hwBH⟩
  rcases hAdiff with ⟨BAd, hBAd, HAd, hHAd, hAdiffBH⟩
  rcases hwdiff with ⟨Bwd, hBwd, Hwd, hHwd, hwdiffBH⟩
  refine ⟨BA * Bwd + BAd * Bw, ?_,
    (BA * Hwd + Bwd * HA) + (BAd * Hw + Bw * HAd), ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hBA hBwd) (mul_nonneg hBAd hBw)
  · exact add_nonneg
      (add_nonneg (mul_nonneg hBA hHwd) (mul_nonneg hBwd hHA))
      (add_nonneg (mul_nonneg hBAd hHw) (mul_nonneg hBw hHAd))
  · exact hABH.continuousLinearMap_apply_sub hwBH hAdiffBH hwdiffBH hBA hBAd

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

/-- On a unit parabolic-diameter domain, a spatial Lipschitz function lifted as a
time-independent function has parabolic `C^{0,α}` control for every `0 ≤ α ≤ 1`. -/
theorem of_snd_lipschitzOnWith_of_parabolicDistance_le_one {B α : ℝ} {K : ℝ≥0}
    {f : X → E} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.2) s :=
  (of_snd_lipschitzOnWith (s := s) hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    hα_nonneg hα_le_one hdiam

/-- On a unit parabolic-diameter domain, a time-only Lipschitz function has parabolic
`C^{0,α}` control for every `0 ≤ α ≤ 2`. -/
theorem of_fst_lipschitzOnWith_of_parabolicDistance_le_one {B α : ℝ} {K : ℝ≥0}
    {f : ℝ → E} (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.1) s :=
  (of_fst_lipschitzOnWith (s := s) hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    hα_nonneg hα_le_two hdiam

/-- On a subset of a closed parabolic ball of diameter at most one, a spatial Lipschitz function
lifted as a time-independent function has parabolic `C^{0,α}` control for every `0 ≤ α ≤ 1`. -/
theorem of_snd_lipschitzOnWith_of_subset_closedBall {B α R : ℝ} {K : ℝ≥0}
    {f : X → E} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.2) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_snd_lipschitzOnWith_of_subset_closedBall
      (s := s) (B := B) (K := K) (f := f)
      hα_nonneg hα_le_one hB hL hs hR⟩

/-- On a subset of a closed parabolic ball of diameter at most one, a time-only Lipschitz function
has parabolic `C^{0,α}` control for every `0 ≤ α ≤ 2`. -/
theorem of_fst_lipschitzOnWith_of_subset_closedBall {B α R : ℝ} {K : ℝ≥0}
    {f : ℝ → E} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.1) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_fst_lipschitzOnWith_of_subset_closedBall
      (s := s) (B := B) (K := K) (f := f)
      hα_nonneg hα_le_two hB hL hs hR⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, a spatial Lipschitz
function lifted as a time-independent function has parabolic `C^{0,α}` control for every
`0 ≤ α ≤ 1`. -/
theorem of_snd_lipschitzOnWith_of_subset_closedCylinder {B α : ℝ} {K : ℝ≥0}
    {f : X → E} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃x : X⦄, x ∈ Prod.snd '' s → ‖f x‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.2) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_snd_lipschitzOnWith_of_subset_closedCylinder
      (s := s) (B := B) (K := K) (f := f)
      hα_nonneg hα_le_one hB hL hs hdiam⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, a time-only Lipschitz
function has parabolic `C^{0,α}` control for every `0 ≤ α ≤ 2`. -/
theorem of_fst_lipschitzOnWith_of_subset_closedCylinder {B α : ℝ} {K : ℝ≥0}
    {f : ℝ → E} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : 0 ≤ B)
    (hB : ∀ ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖f t‖ ≤ B)
    (hL : LipschitzOnWith K f (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => f z.1) s :=
  ⟨B, hB_nonneg, (K : ℝ), NNReal.coe_nonneg K,
    ParabolicC0AlphaWith.of_fst_lipschitzOnWith_of_subset_closedCylinder
      (s := s) (B := B) (K := K) (f := f)
      hα_nonneg hα_le_two hB hL hs hdiam⟩

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

/-- Pullback of parabolic `C^{0,α}` membership along a map `φ : ℝ × Y → ℝ × X` that maps
`t` into `s` and expands parabolic distance by at most a factor `L`.  Existential-constant
form of `ParabolicC0AlphaWith.comp_parabolicDistanceLe`. -/
theorem comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicC0AlphaOn α (fun p => u (φ p)) t := by
  rcases hu with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B, hB, H * L ^ α, mul_nonneg hH (Real.rpow_nonneg hL α),
    hBH.comp_parabolicDistanceLe hH hα hL hmaps hφ⟩

end ParabolicC0AlphaOn

/-! ### Schauder scaling estimates

The parabolic dilation `p ↦ (r ^ 2 * p.1, r • p.2)` is the domain reparametrization used in the
Schauder scaling argument.  Composing the change-of-variables lemmas with the scaling identity
`parabolicDistance_dilation` gives ready-to-use estimates: precomposition with the dilation
preserves the parabolic Hölder / `C^{0,α}` classes, scaling the Hölder constant by `|r| ^ α`. -/

/-- Schauder scaling estimate for the parabolic Hölder seminorm. -/
theorem ParabolicHolderWith.comp_dilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {C α r : ℝ} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicHolderWith (C * |r| ^ α) α
      (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2)) t :=
  hu.comp_parabolicDistanceLe hC hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_dilation r p q).le)

/-- Schauder scaling estimate for parabolic Hölder membership. -/
theorem ParabolicHolderOn.comp_dilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicHolderOn α (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2)) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_dilation r p q).le)

/-- Schauder scaling estimate for parabolic `C^{0,α}` control: the sup bound `B` is preserved
and the Hölder constant scales by `|r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_dilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r : ℝ} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2)) t :=
  hu.comp_parabolicDistanceLe hH hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_dilation r p q).le)

/-- Schauder scaling estimate for parabolic `C^{0,α}` membership. -/
theorem ParabolicC0AlphaOn.comp_dilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2)) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_dilation r p q).le)

/-- **Schauder scaling on balls (`C^{0,α}` control).** If `u` is parabolic `C^{0,α}` with
constants `B, H` on the closed parabolic ball of radius `R` about the origin, and `|r| * ρ ≤ R`,
then `u` precomposed with the parabolic dilation is parabolic `C^{0,α}` on the closed ball of
radius `ρ`, with sup bound `B` and Hölder constant `H * |r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_dilation_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ R : ℝ} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedBall (0 : ℝ × X) R))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2)) (parabolicClosedBall (0 : ℝ × X) ρ) :=
  hu.comp_dilation hH hα
    (parabolicClosedBall_zero_mapsTo_dilation.mono_right (fun _q hq => le_trans hq hle))

/-- **Schauder scaling on balls (`C^{0,α}` membership).** Existential-constant form of
`ParabolicC0AlphaWith.comp_dilation_parabolicClosedBall`. -/
theorem ParabolicC0AlphaOn.comp_dilation_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ R : ℝ} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedBall (0 : ℝ × X) R))
    (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (r ^ 2 * p.1, r • p.2))
      (parabolicClosedBall (0 : ℝ × X) ρ) :=
  hu.comp_dilation hα
    (parabolicClosedBall_zero_mapsTo_dilation.mono_right (fun _q hq => le_trans hq hle))

/-! ### Affine (centered) Schauder change of variables

Composing the origin-centered parabolic dilation with a translation gives the affine parabolic
change of variables `p ↦ c + (r ^ 2 * p.1, r • p.2)`, which normalizes a parabolic ball about an
arbitrary center `c` to the origin.  By `parabolicDistance_add_left` the translation is an
isometry for the parabolic distance, so the centered dilation still expands parabolic distance by
exactly `|r|`; the Schauder scaling estimates therefore carry over verbatim, with the same
`|r| ^ α` Hölder-constant factor.  This is the change of variables underlying the interior
Schauder estimate, where the estimate on a ball about an interior point is reduced to the
origin-centered unit ball. -/

/-- **Affine parabolic scaling identity.** The centered parabolic dilation
`p ↦ c + (r ^ 2 * p.1, r • p.2)` scales parabolic distance by exactly `|r|`, for any center `c`.
This is `parabolicDistance_dilation` composed with the translation isometry
`parabolicDistance_add_left`. -/
theorem parabolicDistance_centeredDilation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c : ℝ × X) (r : ℝ) (p q : ℝ × X) :
    parabolicDistance (c + (r ^ 2 * p.1, r • p.2)) (c + (r ^ 2 * q.1, r • q.2))
      = |r| * parabolicDistance p q := by
  rw [parabolicDistance_add_left, parabolicDistance_dilation]

/-- The centered parabolic dilation `p ↦ c + (r ^ 2 * p.1, r • p.2)` maps the origin-centered
closed parabolic ball of radius `ρ` into the closed parabolic ball of radius `|r| * ρ` about `c`.
This discharges the `Set.MapsTo` hypothesis of the affine Schauder scaling estimates. -/
theorem parabolicClosedBall_mapsTo_centeredDilation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c : ℝ × X} {r ρ : ℝ} :
    Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * p.1, r • p.2))
      (parabolicClosedBall (0 : ℝ × X) ρ) (parabolicClosedBall c (|r| * ρ)) := by
  intro q hq
  simp only [parabolicClosedBall, Set.mem_setOf_eq] at hq ⊢
  have hz : ((r ^ 2 * (0 : ℝ × X).1, r • (0 : ℝ × X).2) : ℝ × X) = (0 : ℝ × X) := by simp
  have hkey : parabolicDistance c (c + (r ^ 2 * q.1, r • q.2))
      = |r| * parabolicDistance (0 : ℝ × X) q := by
    have h := parabolicDistance_centeredDilation c r (0 : ℝ × X) q
    rw [hz, add_zero] at h
    exact h
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg r)

/-- Affine Schauder scaling estimate for the parabolic Hölder seminorm. -/
theorem ParabolicHolderWith.comp_centeredDilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {C α r : ℝ} {c : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicHolderWith (C * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2))) t :=
  hu.comp_parabolicDistanceLe hC hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_centeredDilation c r p q).le)

/-- Affine Schauder scaling estimate for parabolic Hölder membership. -/
theorem ParabolicHolderOn.comp_centeredDilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {c : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicHolderOn α (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2))) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_centeredDilation c r p q).le)

/-- Affine Schauder scaling estimate for parabolic `C^{0,α}` control: the sup bound `B` is
preserved and the Hölder constant scales by `|r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_centeredDilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r : ℝ} {c : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2))) t :=
  hu.comp_parabolicDistanceLe hH hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_centeredDilation c r p q).le)

/-- Affine Schauder scaling estimate for parabolic `C^{0,α}` membership. -/
theorem ParabolicC0AlphaOn.comp_centeredDilation
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {c : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * p.1, r • p.2)) t s) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2))) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_centeredDilation c r p q).le)

/-- **Affine Schauder normalization (`C^{0,α}` control).** If `u` is parabolic `C^{0,α}` with
constants `B, H` on the closed parabolic ball of radius `R` about an arbitrary center `c`, and
`|r| * ρ ≤ R`, then `u` precomposed with the centered parabolic dilation
`p ↦ c + (r ^ 2 * p.1, r • p.2)` is parabolic `C^{0,α}` on the origin-centered closed ball of
radius `ρ`, with sup bound `B` and Hölder constant `H * |r| ^ α`.  This normalizes a parabolic
ball about any center to the origin. -/
theorem ParabolicC0AlphaWith.comp_centeredDilation_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ R : ℝ} {c : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedBall c R))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2))) (parabolicClosedBall (0 : ℝ × X) ρ) :=
  hu.comp_centeredDilation hH hα
    (parabolicClosedBall_mapsTo_centeredDilation.mono_right (fun _q hq => le_trans hq hle))

/-- **Affine Schauder normalization (`C^{0,α}` membership).** Existential-constant form of
`ParabolicC0AlphaWith.comp_centeredDilation_parabolicClosedBall`. -/
theorem ParabolicC0AlphaOn.comp_centeredDilation_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ R : ℝ} {c : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedBall c R))
    (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * p.1, r • p.2)))
      (parabolicClosedBall (0 : ℝ × X) ρ) :=
  hu.comp_centeredDilation hα
    (parabolicClosedBall_mapsTo_centeredDilation.mono_right (fun _q hq => le_trans hq hle))

/-! ### General affine parabolic change of variables

The centered dilation of the previous section fixes the origin as the source center.  Subtracting
a source center `a` first gives the fully general affine parabolic map
`p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))`, which carries the parabolic ball about `a` to the
parabolic ball about `c` and rescales by `|r|`.  This is the change of variables that relates two
arbitrary parabolic balls, used in the interior Schauder estimate to move between a ball about an
interior point and a normalized ball. -/

/-- **Parabolic distance is invariant under a fixed translation on the right.**  Subtracting a
fixed time-space vector `a` from both arguments leaves the parabolic distance unchanged; this is
the `sub` companion of `parabolicDistance_add_left`. -/
theorem parabolicDistance_sub_right {X : Type*} [NormedAddCommGroup X] (a p q : ℝ × X) :
    parabolicDistance (p - a) (q - a) = parabolicDistance p q := by
  have h := parabolicDistance_add_left (-a) p q
  simpa [sub_eq_neg_add] using h

/-- **General affine parabolic scaling identity.** The affine map
`p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` scales parabolic distance by exactly `|r|`, for
any source center `a` and target center `c`.  It is `parabolicDistance_centeredDilation` applied to
the translated points `p - a`, `q - a`, followed by `parabolicDistance_sub_right`. -/
theorem parabolicDistance_affineChart {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c a : ℝ × X) (r : ℝ) (p q : ℝ × X) :
    parabolicDistance (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
        (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2)))
      = |r| * parabolicDistance p q := by
  have h := parabolicDistance_centeredDilation c r (p - a) (q - a)
  rw [parabolicDistance_sub_right] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  exact h

/-- The general affine map `p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` maps the closed
parabolic ball of radius `ρ` about the source center `a` into the closed parabolic ball of radius
`|r| * ρ` about the target center `c`.  This discharges the `Set.MapsTo` hypothesis of the general
affine Schauder scaling estimates. -/
theorem parabolicClosedBall_mapsTo_affineChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r ρ : ℝ} :
    Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedBall a ρ) (parabolicClosedBall c (|r| * ρ)) := by
  intro q hq
  simp only [parabolicClosedBall, Set.mem_setOf_eq] at hq ⊢
  have hz : ((r ^ 2 * (a.1 - a.1), r • (a.2 - a.2)) : ℝ × X) = (0 : ℝ × X) := by simp
  have hkey : parabolicDistance c (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2)))
      = |r| * parabolicDistance a q := by
    have h := parabolicDistance_affineChart c a r a q
    rw [hz, add_zero] at h
    exact h
  rw [hkey]
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg r)

/-- General affine Schauder scaling estimate for the parabolic Hölder seminorm. -/
theorem ParabolicHolderWith.comp_affineChart
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {C α r : ℝ} {c a : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderWith C α u s) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) t s) :
    ParabolicHolderWith (C * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))) t :=
  hu.comp_parabolicDistanceLe hC hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_affineChart c a r p q).le)

/-- General affine Schauder scaling estimate for parabolic Hölder membership. -/
theorem ParabolicHolderOn.comp_affineChart
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {c a : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) t s) :
    ParabolicHolderOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_affineChart c a r p q).le)

/-- General affine Schauder scaling estimate for parabolic `C^{0,α}` control: the sup bound `B` is
preserved and the Hölder constant scales by `|r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_affineChart
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r : ℝ} {c a : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaWith B H α u s) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) t s) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))) t :=
  hu.comp_parabolicDistanceLe hH hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_affineChart c a r p q).le)

/-- General affine Schauder scaling estimate for parabolic `C^{0,α}` membership. -/
theorem ParabolicC0AlphaOn.comp_affineChart
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r : ℝ} {c a : ℝ × X} {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α)
    (hmaps : Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) t s) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))) t :=
  hu.comp_parabolicDistanceLe hα (abs_nonneg r) hmaps
    (fun p _ q _ => (parabolicDistance_affineChart c a r p q).le)

/-- **General affine Schauder normalization (`C^{0,α}` control).** If `u` is parabolic `C^{0,α}`
with constants `B, H` on the closed parabolic ball of radius `R` about a target center `c`, and
`|r| * ρ ≤ R`, then `u` precomposed with the general affine map
`p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` is parabolic `C^{0,α}` on the closed ball of radius
`ρ` about the source center `a`, with sup bound `B` and Hölder constant `H * |r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ R : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedBall c R))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicClosedBall a ρ) :=
  hu.comp_affineChart hH hα
    (parabolicClosedBall_mapsTo_affineChart.mono_right (fun _q hq => le_trans hq hle))

/-- **General affine Schauder normalization (`C^{0,α}` membership).** Existential-constant form of
`ParabolicC0AlphaWith.comp_affineChart_parabolicClosedBall`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ R : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedBall c R))
    (hα : 0 ≤ α) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicClosedBall a ρ) :=
  hu.comp_affineChart hα
    (parabolicClosedBall_mapsTo_affineChart.mono_right (fun _q hq => le_trans hq hle))

/-! ### Affine parabolic change of variables on cylinders

The general affine map also carries a closed parabolic cylinder about the source center `a` to a
closed parabolic cylinder about the target center `c`, scaling the time radius by `r ^ 2` and the
spatial radius by `|r|` (the anisotropic parabolic scaling).  This is the cylinder counterpart of
`parabolicClosedBall_mapsTo_affineChart`, giving the Schauder normalization on the product cylinder
shape used when the time and space radii are tracked independently. -/

/-- The general affine map `p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` maps the closed
parabolic cylinder of time radius `T` and space radius `S` about the source center `a` into the
closed parabolic cylinder of time radius `r ^ 2 * T` and space radius `|r| * S` about the target
center `c`. -/
theorem parabolicClosedCylinder_mapsTo_affineChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r T S : ℝ} :
    Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedCylinder a T S) (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) := by
  intro q hq
  simp only [parabolicClosedCylinder, Set.mem_setOf_eq] at hq ⊢
  obtain ⟨hqt, hqs⟩ := hq
  refine ⟨?_, ?_⟩
  · have htime : |c.1 - (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2))).1| = r ^ 2 * |a.1 - q.1| := by
      simp only [Prod.fst_add, sub_add_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg r),
        abs_sub_comm a.1 q.1]
    rw [htime]
    exact mul_le_mul_of_nonneg_left hqt (sq_nonneg r)
  · have hspace : dist c.2 (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2))).2 = |r| * dist a.2 q.2 := by
      simp only [Prod.snd_add, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs]
      rw [norm_sub_rev q.2 a.2]
    rw [hspace]
    exact mul_le_mul_of_nonneg_left hqs (abs_nonneg r)

/-- **Affine Schauder normalization on cylinders (`C^{0,α}` control).** If `u` is parabolic
`C^{0,α}` with constants `B, H` on the closed parabolic cylinder of time radius `T'` and space
radius `S'` about a target center `c`, and `r ^ 2 * T ≤ T'`, `|r| * S ≤ S'`, then `u` precomposed
with the general affine map is parabolic `C^{0,α}` on the closed cylinder of time radius `T` and
space radius `S` about the source center `a`, with sup bound `B` and Hölder constant
`H * |r| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_parabolicClosedCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r T S T' S' : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedCylinder c T' S'))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hT : r ^ 2 * T ≤ T') (hS : |r| * S ≤ S') :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicClosedCylinder a T S) :=
  hu.comp_affineChart hH hα
    (parabolicClosedCylinder_mapsTo_affineChart.mono_right
      (fun _x hx => ⟨le_trans hx.1 hT, le_trans hx.2 hS⟩))

/-- **Affine Schauder normalization on cylinders (`C^{0,α}` membership).** Existential-constant
form of `ParabolicC0AlphaWith.comp_affineChart_parabolicClosedCylinder`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_parabolicClosedCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r T S T' S' : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedCylinder c T' S'))
    (hα : 0 ≤ α) (hT : r ^ 2 * T ≤ T') (hS : |r| * S ≤ S') :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicClosedCylinder a T S) :=
  hu.comp_affineChart hα
    (parabolicClosedCylinder_mapsTo_affineChart.mono_right
      (fun _x hx => ⟨le_trans hx.1 hT, le_trans hx.2 hS⟩))

/-! ### Algebra of the affine parabolic charts

The affine parabolic maps compose to another affine parabolic map, with the dilation factors
multiplying and the intermediate center cancelling; the chart with unit factor and equal
source/target center is the identity.  These give the groupoid structure used to iterate the
Schauder scaling (for instance in a dyadic decomposition) and to invert the normalization. -/

/-- **Composition law for affine parabolic charts.**  Composing the affine map centered at `a`
into `c` with factor `r` after the affine map centered at `b` into `a` with factor `s` gives the
affine map centered at `b` into `c` with factor `r * s`: the intermediate center `a` cancels and
the dilation factors multiply. -/
theorem affineChart_comp_affineChart {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c a b : ℝ × X) (r s : ℝ) :
    (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) ∘
        (fun p : ℝ × X => a + (s ^ 2 * (p.1 - b.1), s • (p.2 - b.2)))
      = fun p : ℝ × X => c + ((r * s) ^ 2 * (p.1 - b.1), (r * s) • (p.2 - b.2)) := by
  funext p
  simp only [Function.comp_apply, Prod.fst_add, Prod.snd_add]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]; ring
  · simp only [Prod.snd_add]; module

/-- The affine parabolic chart with unit dilation factor and equal source and target center is the
identity map.  This is the unit of the affine-chart composition law. -/
theorem affineChart_one_self {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : ℝ × X) :
    (fun p : ℝ × X => c + ((1 : ℝ) ^ 2 * (p.1 - c.1), (1 : ℝ) • (p.2 - c.2))) = id := by
  funext p
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, one_pow, one_mul, id]; ring
  · simp only [Prod.snd_add, one_smul, id]; abel

/-- **The affine parabolic chart is invertible (left inverse).**  When `r ≠ 0`, the affine chart
`Φ_{a,c,r⁻¹} : p ↦ a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))` is a left inverse of the forward
chart `Φ_{c,a,r} : p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))`, by the composition law and
`inv_mul_cancel₀`.  This is the de-normalization map used to transport Schauder estimates back to
the original scale. -/
theorem affineChart_leftInverse {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0) :
    Function.LeftInverse (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) := by
  have h : (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))) ∘
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) = id := by
    rw [affineChart_comp_affineChart a c a r⁻¹ r, inv_mul_cancel₀ hr, affineChart_one_self]
  exact fun x => congrFun h x

/-- **The affine parabolic chart is invertible (right inverse).**  When `r ≠ 0`, the affine chart
`Φ_{a,c,r⁻¹}` is also a right inverse of the forward chart `Φ_{c,a,r}`, so the two charts are
mutually inverse bijections of `ℝ × X`. -/
theorem affineChart_rightInverse {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0) :
    Function.RightInverse (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) := by
  have h : (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) ∘
      (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))) = id := by
    rw [affineChart_comp_affineChart c a c r r⁻¹, mul_inv_cancel₀ hr, affineChart_one_self]
  exact fun x => congrFun h x

/-! ### The affine parabolic chart is a bijection of parabolic balls and cylinders

Combining the forward `Set.MapsTo` estimates with the two-sided inverse chart shows that, for
`r ≠ 0`, the affine parabolic chart is a `Set.BijOn` between a parabolic ball (or cylinder) about
the source center and the rescaled ball (cylinder) about the target center.  The inverse chart
`Φ_{a,c,r⁻¹}` supplies the de-normalization `Set.MapsTo` that carries the rescaled ball back to the
original ball.  These bijections are what legitimize transporting a Schauder `C^{0,α}` estimate in
*both* directions: normalize to a unit-scale ball, apply the estimate, and de-normalize back. -/

/-- **De-normalization map on balls.**  For `r ≠ 0`, the inverse affine chart
`Φ_{a,c,r⁻¹} : p ↦ a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))` maps the closed parabolic ball of
radius `|r| * ρ` about the target center `c` back into the closed parabolic ball of radius `ρ` about
the source center `a`, since `|r⁻¹| * (|r| * ρ) = ρ`.  This is the reverse `Set.MapsTo` companion of
`parabolicClosedBall_mapsTo_affineChart`. -/
theorem parabolicClosedBall_mapsTo_affineChart_inv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r ρ : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (parabolicClosedBall c (|r| * ρ)) (parabolicClosedBall a ρ) := by
  have h := parabolicClosedBall_mapsTo_affineChart (c := a) (a := c) (r := r⁻¹) (ρ := |r| * ρ)
  have hrad : |r⁻¹| * (|r| * ρ) = ρ := by
    rw [abs_inv, inv_mul_cancel_left₀ (abs_pos.mpr hr).ne']
  rwa [hrad] at h

/-- **The affine parabolic chart is a bijection of parabolic balls.**  For `r ≠ 0`, the forward
affine chart `Φ_{c,a,r} : p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` restricts to a `Set.BijOn`
from the closed parabolic ball of radius `ρ` about the source center `a` onto the closed parabolic
ball of radius `|r| * ρ` about the target center `c`.  The inverse chart `Φ_{a,c,r⁻¹}` is the
two-sided inverse, and both forward and reverse maps are `Set.MapsTo` on these balls. -/
theorem affineChart_bijOn_parabolicClosedBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (ρ : ℝ) :
    Set.BijOn (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedBall a ρ) (parabolicClosedBall c (|r| * ρ)) := by
  have hinv : Set.InvOn
      (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedBall a ρ) (parabolicClosedBall c (|r| * ρ)) :=
    ⟨(affineChart_leftInverse c a hr).leftInvOn (parabolicClosedBall a ρ),
      (affineChart_rightInverse c a hr).rightInvOn (parabolicClosedBall c (|r| * ρ))⟩
  exact hinv.bijOn parabolicClosedBall_mapsTo_affineChart
    (parabolicClosedBall_mapsTo_affineChart_inv hr)

/-- **De-normalization map on cylinders.**  For `r ≠ 0`, the inverse affine chart `Φ_{a,c,r⁻¹}` maps
the closed parabolic cylinder of time radius `r ^ 2 * T` and space radius `|r| * S` about the target
center `c` back into the closed parabolic cylinder of time radius `T` and space radius `S` about the
source center `a`, since `r⁻¹ ^ 2 * (r ^ 2 * T) = T` and `|r⁻¹| * (|r| * S) = S`.  This is the reverse
`Set.MapsTo` companion of `parabolicClosedCylinder_mapsTo_affineChart`. -/
theorem parabolicClosedCylinder_mapsTo_affineChart_inv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r T S : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) (parabolicClosedCylinder a T S) := by
  have h := parabolicClosedCylinder_mapsTo_affineChart
    (c := a) (a := c) (r := r⁻¹) (T := r ^ 2 * T) (S := |r| * S)
  have hT : r⁻¹ ^ 2 * (r ^ 2 * T) = T := by
    rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hr)]
  have hS : |r⁻¹| * (|r| * S) = S := by
    rw [abs_inv, inv_mul_cancel_left₀ (abs_pos.mpr hr).ne']
  rwa [hT, hS] at h

/-- **The affine parabolic chart is a bijection of parabolic cylinders.**  For `r ≠ 0`, the forward
affine chart `Φ_{c,a,r}` restricts to a `Set.BijOn` from the closed parabolic cylinder of time
radius `T` and space radius `S` about the source center `a` onto the closed parabolic cylinder of
time radius `r ^ 2 * T` and space radius `|r| * S` about the target center `c`, with the inverse
chart `Φ_{a,c,r⁻¹}` as two-sided inverse. -/
theorem affineChart_bijOn_parabolicClosedCylinder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (T S : ℝ) :
    Set.BijOn (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedCylinder a T S) (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) := by
  have hinv : Set.InvOn
      (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicClosedCylinder a T S) (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) :=
    ⟨(affineChart_leftInverse c a hr).leftInvOn (parabolicClosedCylinder a T S),
      (affineChart_rightInverse c a hr).rightInvOn
        (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S))⟩
  exact hinv.bijOn parabolicClosedCylinder_mapsTo_affineChart
    (parabolicClosedCylinder_mapsTo_affineChart_inv hr)

/-- **Exact image of a parabolic ball under the affine chart.**  For `r ≠ 0`, the forward affine
chart carries the closed parabolic ball of radius `ρ` about `a` *onto* (not merely into) the closed
parabolic ball of radius `|r| * ρ` about `c`.  This is the image-equality strengthening of
`parabolicClosedBall_mapsTo_affineChart`, obtained from the bijection. -/
theorem affineChart_image_parabolicClosedBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (ρ : ℝ) :
    (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) '' parabolicClosedBall a ρ
      = parabolicClosedBall c (|r| * ρ) :=
  (affineChart_bijOn_parabolicClosedBall c a hr ρ).image_eq

/-- **Exact image of a parabolic cylinder under the affine chart.**  For `r ≠ 0`, the forward affine
chart carries the closed parabolic cylinder of time radius `T` and space radius `S` about `a` onto
the closed parabolic cylinder of time radius `r ^ 2 * T` and space radius `|r| * S` about `c`. -/
theorem affineChart_image_parabolicClosedCylinder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (T S : ℝ) :
    (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) '' parabolicClosedCylinder a T S
      = parabolicClosedCylinder c (r ^ 2 * T) (|r| * S) :=
  (affineChart_bijOn_parabolicClosedCylinder c a hr T S).image_eq

/-! ### De-normalization Schauder estimates (inverse affine chart)

The forward `comp_affineChart_parabolicClosed{Ball,Cylinder}` estimates *normalize*: they transport
`C^{0,α}` / Hölder control from a target ball (cylinder) about `c` to the rescaled source ball
(cylinder) about `a`.  The following *de-normalization* estimates run in the reverse direction, using
the inverse chart `Φ_{a,c,r⁻¹}` and the reverse `Set.MapsTo` lemmas: control on the source ball
(cylinder) about `a` yields control of the reparametrized function on the rescaled ball (cylinder)
about `c`, with the Hölder constant scaled by `|r⁻¹| ^ α`.  These are exactly the estimates that
carry a unit-scale Schauder bound back to the original geometric scale. -/

/-- **De-normalization Hölder estimate on balls.**  For `r ≠ 0`, if `u` has parabolic Hölder
constant `C` on the closed parabolic ball of radius `ρ` about the source center `a`, then `u`
precomposed with the inverse affine chart `Φ_{a,c,r⁻¹}` has parabolic Hölder constant `C * |r⁻¹| ^ α`
on the closed parabolic ball of radius `|r| * ρ` about the target center `c`. -/
theorem ParabolicHolderWith.comp_affineChart_inv_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {C α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicHolderWith C α u (parabolicClosedBall a ρ)) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicHolderWith (C * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicClosedBall c (|r| * ρ)) :=
  hu.comp_affineChart hC hα (parabolicClosedBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` estimate on balls.**  For `r ≠ 0`, `C^{0,α}` control of `u` on the
closed parabolic ball of radius `ρ` about `a` gives `C^{0,α}` control of `u ∘ Φ_{a,c,r⁻¹}` on the
closed parabolic ball of radius `|r| * ρ` about `c`, with the sup bound preserved and the Hölder
constant scaled by `|r⁻¹| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_inv_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedBall a ρ)) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicC0AlphaWith B (H * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicClosedBall c (|r| * ρ)) :=
  hu.comp_affineChart hH hα (parabolicClosedBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` membership on balls.**  Existential-constant form of
`ParabolicC0AlphaWith.comp_affineChart_inv_parabolicClosedBall`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_inv_parabolicClosedBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedBall a ρ)) (hα : 0 ≤ α) (hr : r ≠ 0) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicClosedBall c (|r| * ρ)) :=
  hu.comp_affineChart hα (parabolicClosedBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` estimate on cylinders.**  For `r ≠ 0`, `C^{0,α}` control of `u` on
the closed parabolic cylinder of time radius `T` and space radius `S` about `a` gives `C^{0,α}`
control of `u ∘ Φ_{a,c,r⁻¹}` on the closed parabolic cylinder of time radius `r ^ 2 * T` and space
radius `|r| * S` about `c`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_inv_parabolicClosedCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r T S : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicClosedCylinder a T S)) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicC0AlphaWith B (H * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) :=
  hu.comp_affineChart hH hα (parabolicClosedCylinder_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` membership on cylinders.**  Existential-constant form of
`ParabolicC0AlphaWith.comp_affineChart_inv_parabolicClosedCylinder`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_inv_parabolicClosedCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r T S : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicClosedCylinder a T S)) (hα : 0 ≤ α) (hr : r ≠ 0) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicClosedCylinder c (r ^ 2 * T) (|r| * S)) :=
  hu.comp_affineChart hα (parabolicClosedCylinder_mapsTo_affineChart_inv hr)

/-- **The affine parabolic chart as a homeomorphism.**  For `r ≠ 0`, the forward affine parabolic
chart `Φ_{c,a,r} : p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` is a self-homeomorphism of the
time-space `ℝ × X`, with inverse the chart `Φ_{a,c,r⁻¹}`.  Being a homeomorphism, it transports open
sets, closed sets, closures, and interiors between the source and target scales — the topological
counterpart of the `Set.BijOn` statements above, used when a Schauder rescaling argument needs to
move open neighborhoods rather than just closed balls and cylinders. -/
def affineChartHomeomorph
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0) :
    Homeomorph (ℝ × X) (ℝ × X) where
  toFun := fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))
  invFun := fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))
  left_inv := affineChart_leftInverse c a hr
  right_inv := affineChart_rightInverse c a hr
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The forward direction of `affineChartHomeomorph` is the explicit affine parabolic chart. -/
@[simp] theorem affineChartHomeomorph_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (p : ℝ × X) :
    affineChartHomeomorph c a hr p = c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)) := rfl

/-- The inverse direction of `affineChartHomeomorph` is the explicit inverse affine parabolic
chart. -/
@[simp] theorem affineChartHomeomorph_symm_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (p : ℝ × X) :
    (affineChartHomeomorph c a hr).symm p = a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)) := rfl

/-! ### Open parabolic balls and cylinders under the affine chart

The `Set.MapsTo`/`Set.BijOn`/image lemmas above are stated for the *closed* parabolic ball and
cylinder shapes.  Parabolic PDE (Schauder) estimates, however, are naturally taken on the *open*
parabolic cylinder `Q = (t₀, t₁) × Ω` where the interior regularity lives, so the change of
variables must also be available for the open shapes.  Because the strict inequality
`parabolicDistance a q < ρ` is only preserved by the affine chart when the dilation factor is
*strictly* positive, the open-domain lemmas require `r ≠ 0` (the closed-domain ones held for all
`r`, since a nonnegative factor preserves `≤`).  With `r ≠ 0` the affine chart is a bijection of
open parabolic balls and cylinders, exactly as in the closed case, and transports open-domain
`C^{0,α}`/Hölder control in both directions. -/

/-- The general affine map `p ↦ c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))` maps the *open*
parabolic ball of radius `ρ` about the source center `a` into the *open* parabolic ball of radius
`|r| * ρ` about the target center `c`, provided `r ≠ 0` (so that the dilation factor `|r|` is
strictly positive and the strict inequality is preserved).  Open-domain companion of
`parabolicClosedBall_mapsTo_affineChart`. -/
theorem parabolicBall_mapsTo_affineChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r ρ : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicBall a ρ) (parabolicBall c (|r| * ρ)) := by
  intro q hq
  simp only [parabolicBall, Set.mem_setOf_eq] at hq ⊢
  have hz : ((r ^ 2 * (a.1 - a.1), r • (a.2 - a.2)) : ℝ × X) = (0 : ℝ × X) := by simp
  have hkey : parabolicDistance c (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2)))
      = |r| * parabolicDistance a q := by
    have h := parabolicDistance_affineChart c a r a q
    rw [hz, add_zero] at h
    exact h
  rw [hkey]
  exact mul_lt_mul_of_pos_left hq (abs_pos.mpr hr)

/-- The general affine map maps the *open* parabolic cylinder of time radius `T` and space radius
`S` about the source center `a` into the *open* parabolic cylinder of time radius `r ^ 2 * T` and
space radius `|r| * S` about the target center `c`, provided `r ≠ 0`.  Open-domain companion of
`parabolicClosedCylinder_mapsTo_affineChart`. -/
theorem parabolicCylinder_mapsTo_affineChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r T S : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicCylinder a T S) (parabolicCylinder c (r ^ 2 * T) (|r| * S)) := by
  intro q hq
  simp only [parabolicCylinder, Set.mem_setOf_eq] at hq ⊢
  obtain ⟨hqt, hqs⟩ := hq
  refine ⟨?_, ?_⟩
  · have htime : |c.1 - (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2))).1| = r ^ 2 * |a.1 - q.1| := by
      simp only [Prod.fst_add, sub_add_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg r),
        abs_sub_comm a.1 q.1]
    rw [htime]
    exact mul_lt_mul_of_pos_left hqt (by positivity)
  · have hspace : dist c.2 (c + (r ^ 2 * (q.1 - a.1), r • (q.2 - a.2))).2 = |r| * dist a.2 q.2 := by
      simp only [Prod.snd_add, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs]
      rw [norm_sub_rev q.2 a.2]
    rw [hspace]
    exact mul_lt_mul_of_pos_left hqs (abs_pos.mpr hr)

/-- **De-normalization map on open balls.**  For `r ≠ 0`, the inverse affine chart `Φ_{a,c,r⁻¹}`
maps the open parabolic ball of radius `|r| * ρ` about the target center `c` back into the open
parabolic ball of radius `ρ` about the source center `a`.  Open-domain companion of
`parabolicClosedBall_mapsTo_affineChart_inv`. -/
theorem parabolicBall_mapsTo_affineChart_inv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r ρ : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (parabolicBall c (|r| * ρ)) (parabolicBall a ρ) := by
  have h := parabolicBall_mapsTo_affineChart (c := a) (a := c) (r := r⁻¹) (ρ := |r| * ρ)
    (inv_ne_zero hr)
  have hrad : |r⁻¹| * (|r| * ρ) = ρ := by
    rw [abs_inv, inv_mul_cancel_left₀ (abs_pos.mpr hr).ne']
  rwa [hrad] at h

/-- **The affine parabolic chart is a bijection of open parabolic balls.**  For `r ≠ 0`, the forward
affine chart `Φ_{c,a,r}` restricts to a `Set.BijOn` from the open parabolic ball of radius `ρ` about
the source center `a` onto the open parabolic ball of radius `|r| * ρ` about the target center `c`,
with the inverse chart `Φ_{a,c,r⁻¹}` as two-sided inverse. -/
theorem affineChart_bijOn_parabolicBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (ρ : ℝ) :
    Set.BijOn (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicBall a ρ) (parabolicBall c (|r| * ρ)) := by
  have hinv : Set.InvOn
      (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicBall a ρ) (parabolicBall c (|r| * ρ)) :=
    ⟨(affineChart_leftInverse c a hr).leftInvOn (parabolicBall a ρ),
      (affineChart_rightInverse c a hr).rightInvOn (parabolicBall c (|r| * ρ))⟩
  exact hinv.bijOn (parabolicBall_mapsTo_affineChart hr)
    (parabolicBall_mapsTo_affineChart_inv hr)

/-- **Exact image of an open parabolic ball under the affine chart.**  For `r ≠ 0`, the forward
affine chart carries the open parabolic ball of radius `ρ` about `a` onto the open parabolic ball of
radius `|r| * ρ` about `c`. -/
theorem affineChart_image_parabolicBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (ρ : ℝ) :
    (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) '' parabolicBall a ρ
      = parabolicBall c (|r| * ρ) :=
  (affineChart_bijOn_parabolicBall c a hr ρ).image_eq

/-- **De-normalization map on open cylinders.**  For `r ≠ 0`, the inverse affine chart `Φ_{a,c,r⁻¹}`
maps the open parabolic cylinder of time radius `r ^ 2 * T` and space radius `|r| * S` about the
target center `c` back into the open parabolic cylinder of time radius `T` and space radius `S`
about the source center `a`.  Open-domain companion of
`parabolicClosedCylinder_mapsTo_affineChart_inv`. -/
theorem parabolicCylinder_mapsTo_affineChart_inv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {c a : ℝ × X} {r T S : ℝ} (hr : r ≠ 0) :
    Set.MapsTo (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (parabolicCylinder c (r ^ 2 * T) (|r| * S)) (parabolicCylinder a T S) := by
  have h := parabolicCylinder_mapsTo_affineChart
    (c := a) (a := c) (r := r⁻¹) (T := r ^ 2 * T) (S := |r| * S) (inv_ne_zero hr)
  have hT : r⁻¹ ^ 2 * (r ^ 2 * T) = T := by
    rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hr)]
  have hS : |r⁻¹| * (|r| * S) = S := by
    rw [abs_inv, inv_mul_cancel_left₀ (abs_pos.mpr hr).ne']
  rwa [hT, hS] at h

/-- **The affine parabolic chart is a bijection of open parabolic cylinders.**  For `r ≠ 0`, the
forward affine chart `Φ_{c,a,r}` restricts to a `Set.BijOn` from the open parabolic cylinder of time
radius `T` and space radius `S` about the source center `a` onto the open parabolic cylinder of time
radius `r ^ 2 * T` and space radius `|r| * S` about the target center `c`. -/
theorem affineChart_bijOn_parabolicCylinder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (T S : ℝ) :
    Set.BijOn (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicCylinder a T S) (parabolicCylinder c (r ^ 2 * T) (|r| * S)) := by
  have hinv : Set.InvOn
      (fun p : ℝ × X => a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2)))
      (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2)))
      (parabolicCylinder a T S) (parabolicCylinder c (r ^ 2 * T) (|r| * S)) :=
    ⟨(affineChart_leftInverse c a hr).leftInvOn (parabolicCylinder a T S),
      (affineChart_rightInverse c a hr).rightInvOn
        (parabolicCylinder c (r ^ 2 * T) (|r| * S))⟩
  exact hinv.bijOn (parabolicCylinder_mapsTo_affineChart hr)
    (parabolicCylinder_mapsTo_affineChart_inv hr)

/-- **Exact image of an open parabolic cylinder under the affine chart.**  For `r ≠ 0`, the forward
affine chart carries the open parabolic cylinder of time radius `T` and space radius `S` about `a`
onto the open parabolic cylinder of time radius `r ^ 2 * T` and space radius `|r| * S` about `c`. -/
theorem affineChart_image_parabolicCylinder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0)
    (T S : ℝ) :
    (fun p : ℝ × X => c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))) '' parabolicCylinder a T S
      = parabolicCylinder c (r ^ 2 * T) (|r| * S) :=
  (affineChart_bijOn_parabolicCylinder c a hr T S).image_eq

/-! ### Schauder estimates on open parabolic balls and cylinders

With the open-domain change of variables in place, the affine Schauder normalization and
de-normalization `C^{0,α}`/Hölder estimates are available on the open parabolic ball and cylinder
shapes, exactly paralleling the closed-domain estimates.  Normalization uses the forward chart to
transport `C^{0,α}` control on an open ball (cylinder) about the target center `c` to the rescaled
open ball (cylinder) about the source center `a`; de-normalization uses the inverse chart to run in
the reverse direction.  All the open-domain estimates require `r ≠ 0`, inherited from the
open-domain `Set.MapsTo` lemmas. -/

/-- **Affine Schauder normalization on open balls (`C^{0,α}` control).**  For `r ≠ 0`, if `u` is
parabolic `C^{0,α}` with constants `B, H` on the open parabolic ball of radius `R` about a target
center `c`, and `|r| * ρ ≤ R`, then `u` precomposed with the forward affine chart is parabolic
`C^{0,α}` on the open ball of radius `ρ` about the source center `a`, with sup bound `B` and Hölder
constant `H * |r| ^ α`.  Open-domain companion of
`ParabolicC0AlphaWith.comp_affineChart_parabolicClosedBall`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_parabolicBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ R : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicBall c R))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hr : r ≠ 0) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicBall a ρ) :=
  hu.comp_affineChart hH hα
    ((parabolicBall_mapsTo_affineChart hr).mono_right (parabolicBall.mono hle))

/-- **Affine Schauder normalization on open balls (`C^{0,α}` membership).**  Existential-constant
form of `ParabolicC0AlphaWith.comp_affineChart_parabolicBall`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_parabolicBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ R : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicBall c R))
    (hα : 0 ≤ α) (hr : r ≠ 0) (hle : |r| * ρ ≤ R) :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicBall a ρ) :=
  hu.comp_affineChart hα
    ((parabolicBall_mapsTo_affineChart hr).mono_right (parabolicBall.mono hle))

/-- **Affine Schauder normalization on open cylinders (`C^{0,α}` control).**  For `r ≠ 0`, if `u` is
parabolic `C^{0,α}` with constants `B, H` on the open parabolic cylinder of time radius `T'` and
space radius `S'` about a target center `c`, and `r ^ 2 * T ≤ T'`, `|r| * S ≤ S'`, then `u`
precomposed with the forward affine chart is parabolic `C^{0,α}` on the open cylinder of time radius
`T` and space radius `S` about the source center `a`, with sup bound `B` and Hölder constant
`H * |r| ^ α`.  Open-domain companion of
`ParabolicC0AlphaWith.comp_affineChart_parabolicClosedCylinder`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_parabolicCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r T S T' S' : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicCylinder c T' S'))
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hr : r ≠ 0) (hT : r ^ 2 * T ≤ T') (hS : |r| * S ≤ S') :
    ParabolicC0AlphaWith B (H * |r| ^ α) α
      (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicCylinder a T S) :=
  hu.comp_affineChart hH hα
    ((parabolicCylinder_mapsTo_affineChart hr).mono_right
      (fun _x hx => ⟨lt_of_lt_of_le hx.1 hT, lt_of_lt_of_le hx.2 hS⟩))

/-- **Affine Schauder normalization on open cylinders (`C^{0,α}` membership).**  Existential-constant
form of `ParabolicC0AlphaWith.comp_affineChart_parabolicCylinder`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_parabolicCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r T S T' S' : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicCylinder c T' S'))
    (hα : 0 ≤ α) (hr : r ≠ 0) (hT : r ^ 2 * T ≤ T') (hS : |r| * S ≤ S') :
    ParabolicC0AlphaOn α (fun p : ℝ × X => u (c + (r ^ 2 * (p.1 - a.1), r • (p.2 - a.2))))
      (parabolicCylinder a T S) :=
  hu.comp_affineChart hα
    ((parabolicCylinder_mapsTo_affineChart hr).mono_right
      (fun _x hx => ⟨lt_of_lt_of_le hx.1 hT, lt_of_lt_of_le hx.2 hS⟩))

/-- **De-normalization Hölder estimate on open balls.**  For `r ≠ 0`, parabolic Hölder control of
`u` with constant `C` on the open parabolic ball of radius `ρ` about the source center `a` gives
parabolic Hölder constant `C * |r⁻¹| ^ α` for `u ∘ Φ_{a,c,r⁻¹}` on the open parabolic ball of radius
`|r| * ρ` about the target center `c`.  Open-domain companion of
`ParabolicHolderWith.comp_affineChart_inv_parabolicClosedBall`. -/
theorem ParabolicHolderWith.comp_affineChart_inv_parabolicBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {C α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicHolderWith C α u (parabolicBall a ρ)) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicHolderWith (C * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicBall c (|r| * ρ)) :=
  hu.comp_affineChart hC hα (parabolicBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` estimate on open balls.**  For `r ≠ 0`, `C^{0,α}` control of `u` on
the open parabolic ball of radius `ρ` about `a` gives `C^{0,α}` control of `u ∘ Φ_{a,c,r⁻¹}` on the
open parabolic ball of radius `|r| * ρ` about `c`, with the sup bound preserved and the Hölder
constant scaled by `|r⁻¹| ^ α`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_inv_parabolicBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicBall a ρ)) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicC0AlphaWith B (H * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicBall c (|r| * ρ)) :=
  hu.comp_affineChart hH hα (parabolicBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` membership on open balls.**  Existential-constant form of
`ParabolicC0AlphaWith.comp_affineChart_inv_parabolicBall`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_inv_parabolicBall
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r ρ : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicBall a ρ)) (hα : 0 ≤ α) (hr : r ≠ 0) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicBall c (|r| * ρ)) :=
  hu.comp_affineChart hα (parabolicBall_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` estimate on open cylinders.**  For `r ≠ 0`, `C^{0,α}` control of
`u` on the open parabolic cylinder of time radius `T` and space radius `S` about `a` gives `C^{0,α}`
control of `u ∘ Φ_{a,c,r⁻¹}` on the open parabolic cylinder of time radius `r ^ 2 * T` and space
radius `|r| * S` about `c`. -/
theorem ParabolicC0AlphaWith.comp_affineChart_inv_parabolicCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {B H α r T S : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaWith B H α u (parabolicCylinder a T S)) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hr : r ≠ 0) :
    ParabolicC0AlphaWith B (H * |r⁻¹| ^ α) α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicCylinder c (r ^ 2 * T) (|r| * S)) :=
  hu.comp_affineChart hH hα (parabolicCylinder_mapsTo_affineChart_inv hr)

/-- **De-normalization `C^{0,α}` membership on open cylinders.**  Existential-constant form of
`ParabolicC0AlphaWith.comp_affineChart_inv_parabolicCylinder`. -/
theorem ParabolicC0AlphaOn.comp_affineChart_inv_parabolicCylinder
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
    {α r T S : ℝ} {c a : ℝ × X} {u : ℝ × X → E}
    (hu : ParabolicC0AlphaOn α u (parabolicCylinder a T S)) (hα : 0 ≤ α) (hr : r ≠ 0) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × X => u (a + (r⁻¹ ^ 2 * (p.1 - c.1), r⁻¹ • (p.2 - c.2))))
      (parabolicCylinder c (r ^ 2 * T) (|r| * S)) :=
  hu.comp_affineChart hα (parabolicCylinder_mapsTo_affineChart_inv hr)

end AnalyticPDE
end RicciFlow

