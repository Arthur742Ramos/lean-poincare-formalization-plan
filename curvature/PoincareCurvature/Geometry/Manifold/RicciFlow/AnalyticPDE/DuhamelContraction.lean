module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Duhamel contraction principle for mild solutions of semilinear evolution equations

## Mathematical context

For a semilinear evolution equation `u'(t) = A u(t) + N(u(t))` on a Banach space `X`,
where `A` generates a strongly continuous semigroup `S(t)` and `N : X → X` is Lipschitz,
a *mild solution* with initial data `u₀` satisfies the Duhamel (variation-of-constants)
formula:
  `u(t) = S(t) u₀ + ∫₀ᵗ S(t-s) N(u(s)) ds`.

After the substitution `s = t·r`, the Duhamel integral becomes an integral over the
*fixed* interval `[0,1]`:
  `∫₀ᵗ S(t-s) N(u(s)) ds = t • ∫₀¹ S(t(1-r)) N(u(t·r)) dr`.

This file proves the abstract (soft) fixed-point bridge for the mild-solution route:

1. **Well-definedness**: the Duhamel map
   `Φ(u)(t) = S(t)u₀ + t • ∫₀¹ S(t(1-r)) N(u(t·r)) dr`
   is a well-defined endomap of `C([0,T], X)`. Continuity of the Duhamel term follows
   from dominated convergence on the fixed interval `[0,1]` (`continuous_of_dominated_interval`).
2. **Duhamel estimate**: `Φ` is Lipschitz with constant `M·L·T`, where `M` bounds the
   semigroup and `L` is the Lipschitz constant of `N`.
3. **Contraction**: if `M·L·T < 1`, `Φ` is a contraction, hence has a unique fixed point
   by the Banach fixed-point theorem — the mild solution.

## Role in the Ricci–DeTurck program

This is the soft analytic bridge for the mild-solution route to Ricci–DeTurck existence,
parallel to `RicciDeTurckOperatorLipschitz.lean` (which handles the direct Picard route).
The hard PDE inputs isolated here are exactly:
- the semigroup bound `M` and joint continuity of the (frozen-coefficient) heat semigroup `S`,
  built toward by `EuclideanMild*` / `EuclideanDuhamel*` / `TensorHeatMildEuclidean`;
- the Lipschitz constant `L` of the DeTurck nonlinearity on the relevant Banach space.

No PDE estimates are assumed or proved here; this file is pure functional analysis.
-/

noncomputable section

open scoped Topology NNReal ENNReal Interval
open MeasureTheory Set Filter

namespace RicciFlow.AnalyticPDE

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Abstract Duhamel data for a semilinear evolution equation `u' = Au + N(u)` on a
Banach space `X`.

- `S : ℝ → X →L[ℝ] X` is the (frozen-coefficient) propagator, bounded by `M` on `[0,T]`
  and jointly continuous in `(t, x)` there (this holds for heat semigroups via their
  kernel representation).
- `N : X → X` is the nonlinearity, globally `L`-Lipschitz. (Local Lipschitz + cutoff
  is the standard reduction for the PDE application.)
- `u₀ : X` is the initial data. -/
public structure DuhamelData where
  T : ℝ
  hT : 0 < T
  S : ℝ → X →L[ℝ] X
  M : ℝ≥0
  hSbound : ∀ t ∈ Icc (0 : ℝ) T, ‖S t‖ ≤ M
  hSjoint : ContinuousOn (fun p : ℝ × X ↦ S p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  N : X → X
  L : ℝ≥0
  hN : LipschitzWith L N
  u₀ : X

namespace DuhamelData

variable (D : DuhamelData (X := X))

/-- Multiplication by `r ∈ [0,1]` preserves `[0,T]`. -/
theorem mul_mem_Icc {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) D.T) (hr : r ∈ Icc (0 : ℝ) 1) :
    t * r ∈ Icc (0 : ℝ) D.T := by
  constructor
  · exact mul_nonneg ht.1 hr.1
  · calc t * r ≤ D.T * 1 :=
          mul_le_mul ht.2 hr.2 hr.1 (by linarith [D.hT, ht.1])
      _ = D.T := mul_one _

/-- Multiplication by `(1-r)` for `r ∈ [0,1]` preserves `[0,T]`. -/
theorem mul_one_sub_mem_Icc {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) D.T)
    (hr : r ∈ Icc (0 : ℝ) 1) : t * (1 - r) ∈ Icc (0 : ℝ) D.T := by
  have h1r : (0 : ℝ) ≤ 1 - r := by linarith [hr.2]
  have h1r' : 1 - r ≤ 1 := by linarith [hr.1]
  constructor
  · exact mul_nonneg ht.1 h1r
  · calc t * (1 - r) ≤ D.T * 1 :=
          mul_le_mul ht.2 h1r' h1r (by linarith [D.hT, ht.1])
      _ = D.T := mul_one _

/-- The substituted Duhamel integrand on subtypes: for a curve `u`, time `t ∈ [0,T]`,
and quadrature parameter `r ∈ [0,1]`, this is `S(t(1-r))(N(u(t·r)))`. -/
public def duhamelIntegrandSub (u : C(Icc (0 : ℝ) D.T, X)) :
    Icc (0 : ℝ) D.T → Icc (0 : ℝ) 1 → X :=
  fun t r ↦ D.S (t.val * (1 - r.val))
    (D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩))

/-- The pair map `(t,r) ↦ (t(1-r), N(u(t·r)))` is continuous. -/
theorem continuous_duhamelPair (u : C(Icc (0 : ℝ) D.T, X)) :
    Continuous (fun p : Icc (0 : ℝ) D.T × Icc (0 : ℝ) 1 ↦
      (p.1.val * (1 - p.2.val),
        D.N (u ⟨p.1.val * p.2.val, D.mul_mem_Icc p.1.property p.2.property⟩))) := by
  apply Continuous.prodMk
  · exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
  · apply D.hN.continuous.comp
    apply u.continuous.comp
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The substituted integrand is continuous in `r` (for fixed `t`, `u`). -/
theorem continuous_duhamelIntegrandSub_r (u : C(Icc (0 : ℝ) D.T, X))
    (t : Icc (0 : ℝ) D.T) :
    Continuous (fun r : Icc (0 : ℝ) 1 ↦ D.duhamelIntegrandSub u t r) := by
  -- `(τ,y) ↦ S τ y` after `r ↦ (t(1-r), N(u⟨t*r, _⟩))`.
  have hpair : Continuous (fun r : Icc (0 : ℝ) 1 ↦
      (t.val * (1 - r.val),
        D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩))) := by
    apply Continuous.prodMk
    · exact continuous_const.mul
        (continuous_const.sub continuous_subtype_val)
    · apply D.hN.continuous.comp
      apply u.continuous.comp
      apply Continuous.subtype_mk
      exact continuous_const.mul continuous_subtype_val
  have hmem : Set.MapsTo
      (fun r : Icc (0 : ℝ) 1 ↦
        (t.val * (1 - r.val),
          D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩)))
      Set.univ (Icc (0 : ℝ) D.T ×ˢ (Set.univ : Set X)) := by
    intro r _
    exact ⟨D.mul_one_sub_mem_Icc t.property r.property, Set.mem_univ _⟩
  have hcomp : Continuous (fun r : Icc (0 : ℝ) 1 ↦
      D.duhamelIntegrandSub u t r) := by
    have h1 : Continuous
        ((fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun r : Icc (0 : ℝ) 1 ↦
          (t.val * (1 - r.val),
            D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩)))) :=
      (continuousOn_univ.mp (D.hSjoint.comp hpair.continuousOn hmem))
    have heq : (fun r : Icc (0 : ℝ) 1 ↦ D.duhamelIntegrandSub u t r) =
        (fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun r : Icc (0 : ℝ) 1 ↦
          (t.val * (1 - r.val),
            D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩))) := by
      rfl
    rwa [heq]
  exact hcomp

/-- The substituted integrand is continuous in `t` (for fixed `r`, `u`). -/
theorem continuous_duhamelIntegrandSub_t (u : C(Icc (0 : ℝ) D.T, X))
    (r : Icc (0 : ℝ) 1) :
    Continuous (fun t : Icc (0 : ℝ) D.T ↦ D.duhamelIntegrandSub u t r) := by
  -- `(τ,y) ↦ S τ y` after `t ↦ (t(1-r), N(u⟨t*r, _⟩))`.
  have hpair : Continuous (fun t : Icc (0 : ℝ) D.T ↦
      (t.val * (1 - r.val),
        D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩))) := by
    apply Continuous.prodMk
    · exact continuous_subtype_val.mul continuous_const
    · apply D.hN.continuous.comp
      apply u.continuous.comp
      apply Continuous.subtype_mk
      exact continuous_subtype_val.mul continuous_const
  have hmem : Set.MapsTo
      (fun t : Icc (0 : ℝ) D.T ↦
        (t.val * (1 - r.val),
          D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩)))
      Set.univ (Icc (0 : ℝ) D.T ×ˢ (Set.univ : Set X)) := by
    intro t _
    exact ⟨D.mul_one_sub_mem_Icc t.property r.property, Set.mem_univ _⟩
  have hcomp : Continuous (fun t : Icc (0 : ℝ) D.T ↦
      D.duhamelIntegrandSub u t r) := by
    have h1 : Continuous
        ((fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun t : Icc (0 : ℝ) D.T ↦
          (t.val * (1 - r.val),
            D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩)))) :=
      (continuousOn_univ.mp (D.hSjoint.comp hpair.continuousOn hmem))
    have heq : (fun t : Icc (0 : ℝ) D.T ↦ D.duhamelIntegrandSub u t r) =
        (fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun t : Icc (0 : ℝ) D.T ↦
          (t.val * (1 - r.val),
            D.N (u ⟨t.val * r.val, D.mul_mem_Icc t.property r.property⟩))) := by
      rfl
    rwa [heq]
  exact hcomp

/-- The integrand as `ℝ → X` (for the interval integral): agrees with the subtype
version on `[0,1]`, defined as `0` outside. -/
public def duhamelIntegrand (u : C(Icc (0 : ℝ) D.T, X)) (t : Icc (0 : ℝ) D.T) : ℝ → X :=
  fun r ↦ if hr : r ∈ Icc (0 : ℝ) 1 then D.duhamelIntegrandSub u t ⟨r, hr⟩ else 0

/-- On `[0,1]`, the `ℝ → X` integrand agrees with the subtype version. -/
theorem duhamelIntegrand_eq_on (u : C(Icc (0 : ℝ) D.T, X)) (t : Icc (0 : ℝ) D.T)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    D.duhamelIntegrand u t r = D.duhamelIntegrandSub u t ⟨r, hr⟩ := by
  unfold duhamelIntegrand
  rw [dif_pos hr]

/-- The integrand is continuous on `[0,1]` (for fixed `t`). -/
theorem continuousOn_duhamelIntegrand (u : C(Icc (0 : ℝ) D.T, X))
    (t : Icc (0 : ℝ) D.T) :
    ContinuousOn (D.duhamelIntegrand u t) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous (fun r : Icc (0 : ℝ) 1 ↦ D.duhamelIntegrandSub u t r) :=
    D.continuous_duhamelIntegrandSub_r u t
  have heq : (Icc (0 : ℝ) 1).domRestrict (D.duhamelIntegrand u t) =
      (fun r : Icc (0 : ℝ) 1 ↦ D.duhamelIntegrandSub u t r) := by
    funext r
    simp only [Set.domRestrict]
    rw [D.duhamelIntegrand_eq_on u t r.property]
  rw [heq]
  exact h

/-- Bound on the nonlinearity: `‖N y‖ ≤ ‖N 0‖ + L * ‖y‖`. -/
theorem norm_N_le (y : X) : ‖D.N y‖ ≤ ‖D.N 0‖ + D.L * ‖y‖ := by
  have h : edist (D.N y) (D.N 0) ≤ D.L * edist y 0 := D.hN y 0
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, sub_zero] at h
  have h' : ‖D.N y - D.N 0‖ ≤ (D.L : ℝ) * ‖y‖ := by
    have hL : (0 : ℝ) ≤ (D.L : ℝ) := D.L.coe_nonneg
    -- `↑D.L` as `ℝ≥0∞` equals `ENNReal.ofReal (D.L : ℝ)`
    have hcoe : ((D.L : ℝ≥0∞)) = ENNReal.ofReal (D.L : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
    rw [hcoe, ← ENNReal.ofReal_mul hL] at h
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  calc ‖D.N y‖ = ‖D.N 0 + (D.N y - D.N 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖D.N 0‖ + ‖D.N y - D.N 0‖ := norm_add_le _ _
    _ ≤ ‖D.N 0‖ + D.L * ‖y‖ := by gcongr

/-- Uniform bound on the integrand: `‖F t r‖ ≤ M * (‖N 0‖ + L * ‖u‖)`. -/
theorem norm_duhamelIntegrand_le (u : C(Icc (0 : ℝ) D.T, X)) (t : Icc (0 : ℝ) D.T)
    (r : ℝ) : ‖D.duhamelIntegrand u t r‖ ≤ D.M * (‖D.N 0‖ + D.L * ‖u‖) := by
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · -- On `[0,1]`: expand and estimate.
    rw [D.duhamelIntegrand_eq_on u t hr]
    unfold duhamelIntegrandSub
    have hS : ‖D.S (t.val * (1 - r))‖ ≤ (D.M : ℝ) :=
      D.hSbound _ (D.mul_one_sub_mem_Icc t.property hr)
    have hN : ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖ ≤
        ‖D.N 0‖ + D.L * ‖u‖ := by
      calc ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖
          ≤ ‖D.N 0‖ + D.L * ‖u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩‖ :=
            D.norm_N_le _
        _ ≤ ‖D.N 0‖ + D.L * ‖u‖ := by
            gcongr
            exact ContinuousMap.norm_coe_le_norm _ _
    calc ‖D.S (t.val * (1 - r)) (D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩))‖
        ≤ ‖D.S (t.val * (1 - r))‖ * ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ D.M * (‖D.N 0‖ + D.L * ‖u‖) :=
          mul_le_mul hS hN (by positivity) (by positivity)
  · -- Outside `[0,1]`: the integrand is defined as 0.
    unfold duhamelIntegrand
    rw [dif_neg hr]
    simp
    positivity

/-- The Duhamel integral over `[0,1]` for a curve `u` at time `t`. -/
public def duhamelIntegral (u : C(Icc (0 : ℝ) D.T, X)) (t : Icc (0 : ℝ) D.T) : X :=
  ∫ r in (0 : ℝ)..1, D.duhamelIntegrand u t r

/-- The Duhamel integral is continuous in `t`, by dominated convergence on `[0,1]`. -/
theorem continuous_duhamelIntegral (u : C(Icc (0 : ℝ) D.T, X)) :
    Continuous (fun t : Icc (0 : ℝ) D.T ↦ D.duhamelIntegral u t) := by
  -- Apply `continuous_of_dominated_interval` with `F t r = duhamelIntegrand u t r`.
  -- Note: `Ι 0 1 = Ioc 0 1 ⊆ Icc 0 1`.
  have hI : (Ι (0 : ℝ) 1) = Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hsub : (Ι (0 : ℝ) 1) ⊆ Icc (0 : ℝ) 1 := by
    rw [hI]
    exact Ioc_subset_Icc_self
  apply intervalIntegral.continuous_of_dominated_interval (a := (0 : ℝ)) (b := (1 : ℝ))
    (F := fun t r ↦ D.duhamelIntegrand u t r)
    (bound := fun _ ↦ (D.M * (‖D.N 0‖ + D.L * ‖u‖) : ℝ))
  · -- `hF_meas`: each `F t` is AEStronglyMeasurable on `Ι 0 1`.
    intro t
    have hcont := D.continuousOn_duhamelIntegrand u t
    exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc
  · -- `h_bound`: uniform bound.
    intro t
    apply Eventually.of_forall
    intro r hr
    exact D.norm_duhamelIntegrand_le u t r
  · -- `bound_integrable`: constant bound is integrable on `[0,1]`.
    apply intervalIntegrable_const
  · -- `h_cont`: for a.e. `r ∈ Ι 0 1`, `t ↦ F t r` is continuous.
    apply Eventually.of_forall
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := hsub hr
    -- `fun t ↦ duhamelIntegrand u t r = fun t ↦ duhamelIntegrandSub u t ⟨r, hr'⟩`
    have heq : (fun t : Icc (0 : ℝ) D.T ↦ D.duhamelIntegrand u t r) =
        (fun t : Icc (0 : ℝ) D.T ↦ D.duhamelIntegrandSub u t ⟨r, hr'⟩) := by
      funext t
      exact D.duhamelIntegrand_eq_on u t hr'
    rw [heq]
    exact D.continuous_duhamelIntegrandSub_t u ⟨r, hr'⟩

/-- The free evolution `t ↦ S(t) u₀`, as a continuous curve. -/
public def freeEvolution : C(Icc (0 : ℝ) D.T, X) where
  toFun := fun t ↦ D.S t.val D.u₀
  continuous_toFun := by
    -- `(τ,y) ↦ S τ y` after `t ↦ (t, u₀)`.
    have hpair : Continuous (fun t : Icc (0 : ℝ) D.T ↦ (t.val, D.u₀)) :=
      continuous_subtype_val.prodMk continuous_const
    have hmem : Set.MapsTo (fun t : Icc (0 : ℝ) D.T ↦ (t.val, D.u₀))
        Set.univ (Icc (0 : ℝ) D.T ×ˢ (Set.univ : Set X)) := by
      intro t _
      exact ⟨t.property, Set.mem_univ _⟩
    have h1 : Continuous
        ((fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun t : Icc (0 : ℝ) D.T ↦ (t.val, D.u₀))) :=
      continuousOn_univ.mp (D.hSjoint.comp hpair.continuousOn hmem)
    have heq : (fun t : Icc (0 : ℝ) D.T ↦ D.S t.val D.u₀) =
        (fun q : ℝ × X ↦ D.S q.1 q.2) ∘ (fun t : Icc (0 : ℝ) D.T ↦ (t.val, D.u₀)) := by
      rfl
    rwa [heq]

/-- The Duhamel term `t ↦ t • ∫₀¹ S(t(1-r)) N(u(t·r)) dr`, as a continuous curve. -/
public def duhamelTerm (u : C(Icc (0 : ℝ) D.T, X)) : C(Icc (0 : ℝ) D.T, X) where
  toFun := fun t ↦ (t.val : ℝ) • D.duhamelIntegral u t
  continuous_toFun := by
    apply Continuous.smul
    · exact continuous_subtype_val
    · exact D.continuous_duhamelIntegral u

/-- The Duhamel map `Φ(u) = freeEvolution + duhamelTerm(u)`. -/
public def duhamelMap (u : C(Icc (0 : ℝ) D.T, X)) : C(Icc (0 : ℝ) D.T, X) :=
  D.freeEvolution + D.duhamelTerm u

/-- Pointwise bound on the integrand difference:
`‖F_u(t,r) - F_v(t,r)‖ ≤ M * L * ‖u - v‖`. -/
theorem norm_duhamelIntegrand_sub_le (u v : C(Icc (0 : ℝ) D.T, X))
    (t : Icc (0 : ℝ) D.T) (r : ℝ) :
    ‖D.duhamelIntegrand u t r - D.duhamelIntegrand v t r‖ ≤
      D.M * (D.L * ‖u - v‖) := by
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · rw [D.duhamelIntegrand_eq_on u t hr, D.duhamelIntegrand_eq_on v t hr]
    unfold duhamelIntegrandSub
    -- `S(a)(N(u(b))) - S(a)(N(v(b))) = S(a)(N(u(b)) - N(v(b)))` by linearity
    have hlin : D.S (t.val * (1 - r)) (D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)) -
        D.S (t.val * (1 - r)) (D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)) =
        D.S (t.val * (1 - r))
          (D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
           D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)) := by
      rw [map_sub]
    rw [hlin]
    have hS : ‖D.S (t.val * (1 - r))‖ ≤ (D.M : ℝ) :=
      D.hSbound _ (D.mul_one_sub_mem_Icc t.property hr)
    have hN : ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
        D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖ ≤
        D.L * ‖u - v‖ := by
      have hN' : LipschitzWith D.L D.N := D.hN
      -- `‖N(a) - N(b)‖ ≤ L * ‖a - b‖` from LipschitzWith via edist
      have h : edist (D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩))
          (D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)) ≤
          D.L * edist (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)
            (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) :=
        D.hN _ _
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at h
      have hL : (0 : ℝ) ≤ (D.L : ℝ) := D.L.coe_nonneg
      have hcoe : ((D.L : ℝ≥0∞)) = ENNReal.ofReal (D.L : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
      rw [hcoe, ← ENNReal.ofReal_mul hL] at h
      have h2 : ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
          D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖ ≤
          (D.L : ℝ) * ‖u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩ -
            v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩‖ := by
        rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
      calc ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
            D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖
          ≤ (D.L : ℝ) * ‖u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩ -
              v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩‖ := h2
        _ ≤ (D.L : ℝ) * ‖u - v‖ := by
            gcongr
            -- `‖u y - v y‖ = ‖(u - v) y‖ ≤ ‖u - v‖`
            have heq : u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩ -
                v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩ =
                (u - v) ⟨t.val * r, D.mul_mem_Icc t.property hr⟩ := by
              rfl
            rw [heq]
            exact ContinuousMap.norm_coe_le_norm _ _
    calc ‖D.S (t.val * (1 - r))
            (D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
             D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩))‖
        ≤ ‖D.S (t.val * (1 - r))‖ *
            ‖D.N (u ⟨t.val * r, D.mul_mem_Icc t.property hr⟩) -
             D.N (v ⟨t.val * r, D.mul_mem_Icc t.property hr⟩)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ D.M * (D.L * ‖u - v‖) :=
          mul_le_mul hS hN (by positivity) (by positivity)
  · -- Outside `[0,1]`: both integrands are 0.
    unfold duhamelIntegrand
    rw [dif_neg hr, dif_neg hr, sub_zero]
    simp only [norm_zero]
    positivity

/-- The difference of Duhamel integrals is bounded:
`‖∫₀¹ F_u - ∫₀¹ F_v‖ ≤ M * (L * ‖u - v‖)`. -/
theorem norm_duhamelIntegral_sub_le (u v : C(Icc (0 : ℝ) D.T, X))
    (t : Icc (0 : ℝ) D.T) :
    ‖D.duhamelIntegral u t - D.duhamelIntegral v t‖ ≤ D.M * (D.L * ‖u - v‖) := by
  have h_int_u : IntervalIntegrable (fun r ↦ D.duhamelIntegrand u t r) volume 0 1 :=
    (D.continuousOn_duhamelIntegrand u t).intervalIntegrable_of_Icc (by norm_num)
  have h_int_v : IntervalIntegrable (fun r ↦ D.duhamelIntegrand v t r) volume 0 1 :=
    (D.continuousOn_duhamelIntegrand v t).intervalIntegrable_of_Icc (by norm_num)
  have h_diff : D.duhamelIntegral u t - D.duhamelIntegral v t =
      ∫ r in (0 : ℝ)..1, (D.duhamelIntegrand u t r - D.duhamelIntegrand v t r) := by
    unfold duhamelIntegral
    rw [← intervalIntegral.integral_sub h_int_u h_int_v]
  rw [h_diff]
  -- For `0 ≤ 1`, `∫ r in 0..1, g r = ∫ r in Ioc 0 1, g r ∂volume`.
  have h_eq : (∫ r in (0 : ℝ)..1,
      (D.duhamelIntegrand u t r - D.duhamelIntegrand v t r)) =
      ∫ r in Ioc (0 : ℝ) 1, (D.duhamelIntegrand u t r - D.duhamelIntegrand v t r) ∂volume := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [h_eq]
  -- Now `∫ r in Ioc 0 1, ...` is `∫ r, ... ∂(volume.restrict (Ioc 0 1))` by notation.
  -- Apply triangle inequality.
  have h_int_diff : Integrable
      (fun r ↦ D.duhamelIntegrand u t r - D.duhamelIntegrand v t r)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (h_int_u.sub h_int_v).1
  calc ‖∫ r in Ioc (0 : ℝ) 1, (D.duhamelIntegrand u t r - D.duhamelIntegrand v t r) ∂volume‖
      ≤ ∫ r in Ioc (0 : ℝ) 1, ‖D.duhamelIntegrand u t r - D.duhamelIntegrand v t r‖ ∂volume := by
        have h := norm_integral_le_integral_norm
          (fun r ↦ D.duhamelIntegrand u t r - D.duhamelIntegrand v t r)
          (μ := volume.restrict (Ioc (0 : ℝ) 1))
        simpa using h
    _ ≤ D.M * (D.L * ‖u - v‖) := by
        have h_bound : ∀ r ∈ Ioc (0 : ℝ) 1,
            ‖D.duhamelIntegrand u t r - D.duhamelIntegrand v t r‖ ≤
              D.M * (D.L * ‖u - v‖) := by
          intro r _
          exact D.norm_duhamelIntegrand_sub_le u v t r
        -- `∫ r in Ioc 0 1, ‖·‖ ≤ ∫ r in Ioc 0 1, C = C * volume(Ioc 0 1) = C`
        have h_mono : (∫ r in Ioc (0 : ℝ) 1,
            ‖D.duhamelIntegrand u t r - D.duhamelIntegrand v t r‖ ∂volume) ≤
            ∫ r in Ioc (0 : ℝ) 1, (D.M * (D.L * ‖u - v‖)) ∂volume := by
          have h1 : IntegrableOn
              (fun r ↦ ‖D.duhamelIntegrand u t r - D.duhamelIntegrand v t r‖)
              (Ioc (0 : ℝ) 1) volume := by
            -- `IntegrableOn` unfolds to `Integrable` on restrict
            show Integrable _ (volume.restrict (Ioc (0 : ℝ) 1))
            exact h_int_diff.norm
          have h2 : IntegrableOn (fun _ ↦ D.M * (D.L * ‖u - v‖))
              (Ioc (0 : ℝ) 1) volume :=
            integrableOn_const (by rw [Real.volume_Ioc]; simp)
          exact setIntegral_mono_on h1 h2 measurableSet_Ioc h_bound
        have h_const : (∫ r in Ioc (0 : ℝ) 1, (D.M * (D.L * ‖u - v‖)) ∂volume) =
            D.M * (D.L * ‖u - v‖) := by
          rw [setIntegral_const]
          simp [Measure.real, Real.volume_Ioc]
        rw [h_const] at h_mono
        exact h_mono

/-- The Lipschitz constant `M * L * T` as an `ℝ≥0`. -/
public def lipschitzConst : ℝ≥0 := ⟨D.M * D.L * D.T, by
  have h1 : (0:ℝ) ≤ (D.M * D.L : ℝ≥0) := (D.M * D.L).coe_nonneg
  have h2 : (0:ℝ) ≤ D.T := D.hT.le
  calc (0:ℝ) ≤ (D.M * D.L : ℝ) * D.T := mul_nonneg h1 h2
    _ = D.M * D.L * D.T := by simp [NNReal.coe_mul]⟩

/-- The Duhamel map is Lipschitz with constant `M * L * T`. -/
theorem lipschitzWith_duhamelMap :
    LipschitzWith D.lipschitzConst D.duhamelMap := by
  -- It suffices to bound the sup norm.
  rw [lipschitzWith_iff_norm_sub_le]
  intro u v
  -- `duhamelMap u - duhamelMap v = duhamelTerm u - duhamelTerm v`
  have h_eq : D.duhamelMap u - D.duhamelMap v =
      D.duhamelTerm u - D.duhamelTerm v := by
    unfold duhamelMap
    abel
  rw [h_eq]
  -- Bound the sup norm by the pointwise bound.
  have h_pointwise : ∀ t : Icc (0 : ℝ) D.T,
      ‖(D.duhamelTerm u - D.duhamelTerm v) t‖ ≤
        (D.M * D.L * D.T) * ‖u - v‖ := by
    intro t
    -- `(duhamelTerm u)(t) - (duhamelTerm v)(t) = t • (I_u - I_v)`
    have h_pt : (D.duhamelTerm u - D.duhamelTerm v) t =
        (t.val : ℝ) • (D.duhamelIntegral u t - D.duhamelIntegral v t) := by
      simp [duhamelTerm, ContinuousMap.sub_apply]
      rw [smul_sub]
    rw [h_pt, norm_smul]
    have h_t : ‖t.val‖ ≤ D.T := by
      have ht := t.property
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2
    calc ‖t.val‖ * ‖D.duhamelIntegral u t - D.duhamelIntegral v t‖
        ≤ D.T * (D.M * (D.L * ‖u - v‖)) := by
          apply mul_le_mul h_t (D.norm_duhamelIntegral_sub_le u v t)
            (by positivity) (D.hT.le)
      _ = (D.M * D.L * D.T) * ‖u - v‖ := by ring
  -- `‖f‖ ≤ C` from pointwise bound (domain is nonempty).
  have h_nonempty : Nonempty (Icc (0 : ℝ) D.T) :=
    ⟨⟨0, by simp [D.hT.le]⟩⟩
  have h_nonneg : (0:ℝ) ≤ D.M * D.L * D.T := by
    have h1 : (0:ℝ) ≤ (D.M * D.L : ℝ≥0) := (D.M * D.L).coe_nonneg
    have h2 : (0:ℝ) ≤ D.T := D.hT.le
    calc (0:ℝ) ≤ (D.M * D.L : ℝ) * D.T := mul_nonneg h1 h2
      _ = D.M * D.L * D.T := by simp [NNReal.coe_mul]
  have h_nonneg' : (0:ℝ) ≤ (D.M * D.L * D.T) * ‖u - v‖ :=
    mul_nonneg h_nonneg (norm_nonneg _)
  calc ‖D.duhamelTerm u - D.duhamelTerm v‖
      ≤ (D.M * D.L * D.T) * ‖u - v‖ :=
        (ContinuousMap.norm_le _ h_nonneg').mpr h_pointwise
    _ = (D.lipschitzConst : ℝ) * ‖u - v‖ := by
        rfl

/-- If `M * L * T < 1`, the Duhamel map is a contraction. -/
public theorem contractingWith_duhamelMap (h : (D.M * D.L * D.T : ℝ) < 1) :
    ContractingWith D.lipschitzConst D.duhamelMap := by
  constructor
  · -- `D.lipschitzConst < 1`
    simp only [lipschitzConst]
    exact h
  · exact D.lipschitzWith_duhamelMap

/-- Existence and uniqueness of the mild solution: the Duhamel map has a unique
fixed point when `M * L * T < 1`. -/
public theorem exists_unique_mild_solution (h : (D.M * D.L * D.T : ℝ) < 1) :
    ∃! u : C(Icc (0 : ℝ) D.T, X), D.duhamelMap u = u := by
  have hcon := D.contractingWith_duhamelMap h
  -- Banach fixed-point theorem
  exact ⟨hcon.fixedPoint D.duhamelMap,
    hcon.fixedPoint_isFixedPt,
    fun y hy ↦ hcon.fixedPoint_unique hy⟩

end DuhamelData

end RicciFlow.AnalyticPDE
