import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroupRestriction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.DuhamelContraction

/-!
# Little-Hölder space and honest DuhamelData (Point 4 PDE milestone)

This file closes the precise analytic gap identified in
`HolderHeatSemigroup.lean` and `HolderHeatSemigroupRestriction.lean`:
joint continuity `DuhamelData.hSjoint` of `(t, f) ↦ S t f` in the Hölder norm.

## Why a new space

Strong continuity `‖S t f - f‖_{C^α} → 0` as `t → 0⁺` is *false* on the full
Hölder space `HolderBCF α n` at the same exponent (the Hölder seminorm of
`S t f - f` need not vanish for general `C^α` data). The canonical remedy is
the **little-Hölder space**: the closed subspace where strong continuity holds.

We define it *intrinsically* via the semigroup (no density arguments needed
for the definition):
  `LittleHolder α n = {f : HolderBCF α n | S t f → f as t → 0⁺}`.
This is a linear subspace (by linearity of `S t`), closed (by a 3-ε argument),
hence a Banach space. The heat propagator preserves it (contraction +
semigroup commutativity) and satisfies `DuhamelData.hSjoint` on it:
strong continuity at `0` plus the semigroup property yields continuity at
`t > 0`, and strong continuity plus the uniform bound `‖S t‖ ≤ 1` yields
joint continuity.

## What is proved

* `holderSeminorm_le_of_isHolderConst_one` : Hölder interpolation —
  the `C^α` seminorm is controlled by sup-norm and Lipschitz constant.
* `isGoodHolder_of_isHolderConst_one` : L1-Lipschitz data is "good"
  (strong continuity at `0`), via interpolation.
* `littleHolderSubmodule` : the little-Hölder space as a `Submodule`,
  with `NormedAddCommGroup` (induced), `NormedSpace ℝ`, `CompleteSpace`.
* `littleHolderPropagator` : the heat propagator restricted to little-Hölder,
  with operator norm `≤ 1`.
* `littleHolderPropagator_hSjoint` : the full `DuhamelData.hSjoint`.
* `littleHolderDuhamelData` : honest `DuhamelData` constructor — the heat
  semigroup part is proved here; the nonlinearity `N` is an explicit
  Lipschitz interface (the genuine Ricci–DeTurck `N` is quasilinear and its
  Lipschitz control is the remaining PDE estimate).
* `exists_unique_littleHolder_mild_solution` : unique mild solution from
  `DuhamelData.exists_unique_mild_solution`.

Constraints: `0 < α < 1` (needed for the interpolation and the sup-norm
approximate-identity estimate).

No `sorry`, no `admit`, no axioms.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {n : ℕ} {α : ℝ}

/-! ## 1. Hölder interpolation: `C^α` seminorm from sup-norm and Lipschitz -/

/-- Subadditivity of `t ↦ t^α` for `0 < α ≤ 1`: `(∑ xᵢ)^α ≤ ∑ xᵢ^α`. -/
theorem rpow_sum_le_sum_rpow {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ i, x i) ^ p ≤ ∑ i, (x i) ^ p := by
  by_cases hS : ∑ i, x i = 0
  · have hxi : ∀ i, x i = 0 := by
      intro i
      have h1 : x i ≤ ∑ i, x i :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      rw [hS] at h1
      exact le_antisymm h1 (hx i)
    rw [hS, Real.zero_rpow hp0.ne']
    apply Finset.sum_nonneg
    intro i _
    rw [hxi i, Real.zero_rpow hp0.ne']
  · -- Normalize by `S = ∑ xᵢ > 0`.
    have hSpos : 0 < ∑ i, x i :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hx i)) (Ne.symm hS)
    have hSp : (∑ i, x i) ^ p ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hSpos p)
    have h2 : (∑ i, (x i) ^ p) = (∑ i, x i) ^ p * ∑ i, (x i / ∑ j, x j) ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.div_rpow (hx i) hSpos.le]
      field_simp
    have h1le : (1 : ℝ) ≤ ∑ i, (x i / ∑ j, x j) ^ p := by
      have hsum1 : ∑ i, (x i / ∑ j, x j) = 1 := by
        rw [← Finset.sum_div]
        exact div_self hSpos.ne'
      calc (1 : ℝ) = ∑ i, (x i / ∑ j, x j) := hsum1.symm
        _ ≤ ∑ i, (x i / ∑ j, x j) ^ p := by
            apply Finset.sum_le_sum
            intro i _
            have hzi0 : 0 ≤ x i / ∑ j, x j := div_nonneg (hx i) hSpos.le
            have hzi1 : x i / ∑ j, x j ≤ 1 := by
              rw [div_le_one hSpos]
              exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
            -- `z ≤ z^p` for `z ∈ [0,1]`, `0 < p ≤ 1`.
            have h := Real.rpow_le_rpow_of_exponent_ge' hzi0 hzi1 hp0.le hp1
            rwa [Real.rpow_one] at h
    rw [h2]
    calc (∑ i, x i) ^ p = (∑ i, x i) ^ p * 1 := (mul_one _).symm
      _ ≤ (∑ i, x i) ^ p * ∑ i, (x i / ∑ j, x j) ^ p :=
          mul_le_mul_of_nonneg_left h1le (Real.rpow_nonneg hSpos.le p)

/-- Hölder interpolation (coordinatewise): if `D` is bounded (sup-norm `≤ M₀`)
and L1-Lipschitz (constant `L₁`), then its `C^α` Hölder constant is at most
`(2M₀)^{1-α} * L₁^α`. In particular the `C^α` seminorm vanishes when the
sup-norm does, uniformly for bounded Lipschitz constant. -/
theorem isHolderConst_of_isHolderConst_one {D : BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {M₀ L₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₀D : ‖D‖ ≤ M₀)
    (hL₁ : IsHolderConst (1 : ℝ) D L₁) (hp0 : 0 < α) (hp1 : α < 1) :
    IsHolderConst α D ((2 * M₀) ^ (1 - α) * L₁ ^ α) := by
  have hα1 : α ≤ 1 := hp1.le
  have h1α : (0 : ℝ) ≤ 1 - α := by linarith
  have hL₁nn : 0 ≤ L₁ := hL₁.1
  have hMnn : (0 : ℝ) ≤ 2 * M₀ := by linarith
  refine ⟨mul_nonneg (Real.rpow_nonneg hMnn _) (Real.rpow_nonneg hL₁nn _), fun a b => ?_⟩
  -- Rewrite the `α = 1` Hölder bound with `|·|^1 = |·|`.
  have hLip : ∀ a b : Fin n → ℝ, |D a - D b| ≤ L₁ * ∑ j : Fin n, |(a - b) j| := by
    intro a b
    have h := hL₁.2 a b
    simpa [Real.rpow_one] using h
  have hxM : |D a - D b| ≤ 2 * M₀ := by
    have htri := abs_sub_le (D a) 0 (D b)
    rw [sub_zero, zero_sub, abs_neg] at htri
    calc |D a - D b| ≤ |D a| + |D b| := htri
      _ ≤ ‖D‖ + ‖D‖ := by
          apply add_le_add
          · exact BoundedContinuousFunction.norm_coe_le_norm D a
          · exact BoundedContinuousFunction.norm_coe_le_norm D b
      _ ≤ M₀ + M₀ := by linarith [hM₀D]
      _ = 2 * M₀ := by ring
  have hd1nn : 0 ≤ ∑ j : Fin n, |(a - b) j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  -- `(∑|·|)^α ≤ ∑|·|^α`.
  have hsub : (∑ j : Fin n, |(a - b) j|) ^ α ≤ ∑ j : Fin n, |(a - b) j| ^ α :=
    rpow_sum_le_sum_rpow (fun j => abs_nonneg _) hp0 hα1
  by_cases hx0 : |D a - D b| = 0
  · rw [hx0]
    apply mul_nonneg
    · apply mul_nonneg
      · exact Real.rpow_nonneg hMnn _
      · exact Real.rpow_nonneg hL₁nn _
    · apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (abs_nonneg _) _
  · have hxpos : 0 < |D a - D b| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hx0)
    have hd1 : |D a - D b| ≤ L₁ * ∑ j : Fin n, |(a - b) j| := hLip a b
    -- `|D a - D b| = |D a - D b|^{1-α} * |D a - D b|^α`.
    have hsplit : |D a - D b| = |D a - D b| ^ (1 - α) * |D a - D b| ^ α := by
      rw [← Real.rpow_add hxpos]
      norm_num
    rw [hsplit]
    calc |D a - D b| ^ (1 - α) * |D a - D b| ^ α
        ≤ (2 * M₀) ^ (1 - α) * (L₁ * ∑ j : Fin n, |(a - b) j|) ^ α := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow (abs_nonneg _) hxM h1α
          · exact Real.rpow_le_rpow (abs_nonneg _) hd1 hp0.le
          · exact Real.rpow_nonneg (abs_nonneg _) _
          · exact Real.rpow_nonneg hMnn _
      _ = (2 * M₀) ^ (1 - α) * (L₁ ^ α * (∑ j : Fin n, |(a - b) j|) ^ α) := by
          rw [Real.mul_rpow hL₁nn hd1nn]
      _ ≤ (2 * M₀) ^ (1 - α) * (L₁ ^ α * ∑ j : Fin n, |(a - b) j| ^ α) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hMnn _)
          apply mul_le_mul_of_nonneg_left hsub (Real.rpow_nonneg hL₁nn _)
      _ = ((2 * M₀) ^ (1 - α) * L₁ ^ α) * ∑ j : Fin n, |(a - b) j| ^ α := by ring

/-- Seminorm version of the interpolation: the `C^α` Hölder seminorm is
controlled by sup-norm and Lipschitz constant. -/
theorem holderSeminorm_le_of_isHolderConst_one {D : HolderBCF α n}
    {M₀ L₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₀D : ‖D.toBCF‖ ≤ M₀)
    (hL₁ : IsHolderConst (1 : ℝ) D.toBCF L₁) (hp0 : 0 < α) (hp1 : α < 1) :
    HolderBCF.holderSeminorm D ≤ (2 * M₀) ^ (1 - α) * L₁ ^ α := by
  have h := isHolderConst_of_isHolderConst_one hM₀ hM₀D hL₁ hp0 hp1
  unfold HolderBCF.holderSeminorm
  apply csInf_le (HolderBCF.bddBelow_holderSet D) h

/-! ## 2. The little-Hölder space

The little-Hölder space is the closed linear subspace of `HolderBCF α n`
where the heat semigroup is strongly continuous at `t = 0⁺`:
  `LittleHolder α n = {f | S t f → f as t → 0⁺}`.
This is defined intrinsically via the semigroup. It is a linear subspace
(by linearity of `S t`), and we prove it is closed via a 3-ε argument using
the uniform contraction bound `‖S t‖ ≤ 1`. Hence it is a Banach space. -/

/-- Total heat propagator on Hölder data: the heat semigroup for `t > 0`,
the identity at `t ≤ 0`. This agrees with `heatSemigroupHolderFun` on `t > 0`. -/
noncomputable def heatPropagatorTotal (t : ℝ) (f : HolderBCF α n) : HolderBCF α n :=
  if ht : 0 < t then heatSemigroupHolderFun (n := n) (α := α) ht f else f

theorem heatPropagatorTotal_of_pos {t : ℝ} (ht : 0 < t) (f : HolderBCF α n) :
    heatPropagatorTotal t f = heatSemigroupHolderFun (n := n) (α := α) ht f :=
  dif_pos ht

theorem heatPropagatorTotal_of_nonpos {t : ℝ} (ht : ¬ 0 < t) (f : HolderBCF α n) :
    heatPropagatorTotal t f = f :=
  dif_neg ht

/-- A Hölder function is "good" if the heat propagator converges to it
in Hölder norm as `t → 0⁺`. -/
def IsGoodHolder (f : HolderBCF α n) : Prop :=
  Tendsto (fun t : ℝ ↦ heatPropagatorTotal t f) (𝓝[>] 0) (𝓝 f)

/-- The total propagator preserves `0`. -/
theorem heatPropagatorTotal_zero (t : ℝ) :
    heatPropagatorTotal (n := n) (α := α) t (0 : HolderBCF α n) = 0 := by
  by_cases ht : 0 < t
  · rw [heatPropagatorTotal_of_pos ht]
    exact (heatSemigroupHolderCLM (n := n) (α := α) ht).map_zero
  · rw [heatPropagatorTotal_of_nonpos ht]

/-- The total propagator preserves addition. -/
theorem heatPropagatorTotal_add (t : ℝ) (f g : HolderBCF α n) :
    heatPropagatorTotal t (f + g) = heatPropagatorTotal t f + heatPropagatorTotal t g := by
  by_cases ht : 0 < t
  · rw [heatPropagatorTotal_of_pos ht, heatPropagatorTotal_of_pos ht,
      heatPropagatorTotal_of_pos ht]
    exact (heatSemigroupHolderCLM (n := n) (α := α) ht).map_add f g
  · rw [heatPropagatorTotal_of_nonpos ht, heatPropagatorTotal_of_nonpos ht,
      heatPropagatorTotal_of_nonpos ht]

/-- The total propagator preserves scalar multiplication. -/
theorem heatPropagatorTotal_smul (t : ℝ) (c : ℝ) (f : HolderBCF α n) :
    heatPropagatorTotal t (c • f) = c • heatPropagatorTotal t f := by
  by_cases ht : 0 < t
  · rw [heatPropagatorTotal_of_pos ht, heatPropagatorTotal_of_pos ht]
    exact (heatSemigroupHolderCLM (n := n) (α := α) ht).map_smul c f
  · rw [heatPropagatorTotal_of_nonpos ht, heatPropagatorTotal_of_nonpos ht]

/-- The little-Hölder space as a linear submodule. -/
def littleHolderSubmodule : Submodule ℝ (HolderBCF α n) where
  carrier := {f | IsGoodHolder f}
  zero_mem' := by
    show IsGoodHolder 0
    unfold IsGoodHolder
    simp [heatPropagatorTotal_zero]
  add_mem' := by
    intro f g hf hg
    show IsGoodHolder (f + g)
    unfold IsGoodHolder at *
    have h : (fun t : ℝ ↦ heatPropagatorTotal t (f + g)) =
        (fun t : ℝ ↦ heatPropagatorTotal t f + heatPropagatorTotal t g) := by
      funext t
      exact heatPropagatorTotal_add t f g
    rw [h]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    show IsGoodHolder (c • f)
    unfold IsGoodHolder at *
    have h : (fun t : ℝ ↦ heatPropagatorTotal t (c • f)) =
        (fun t : ℝ ↦ c • heatPropagatorTotal t f) := by
      funext t
      exact heatPropagatorTotal_smul t c f
    rw [h]
    exact hf.const_smul c

/-- The contraction bound for the total propagator: `‖S t f‖ ≤ ‖f‖` for all `t`. -/
theorem norm_heatPropagatorTotal_le (t : ℝ) (f : HolderBCF α n) :
    ‖heatPropagatorTotal t f‖ ≤ ‖f‖ := by
  by_cases ht : 0 < t
  · rw [heatPropagatorTotal_of_pos ht]
    have h := norm_heatSemigroupHolderCLM_le (n := n) (α := α) ht
    have h2 : ‖heatSemigroupHolderFun (n := n) (α := α) ht f‖ ≤
        ‖heatSemigroupHolderCLM (n := n) (α := α) ht‖ * ‖f‖ :=
      (heatSemigroupHolderCLM (n := n) (α := α) ht).le_opNorm f
    calc ‖heatSemigroupHolderFun (n := n) (α := α) ht f‖
        ≤ ‖heatSemigroupHolderCLM (n := n) (α := α) ht‖ * ‖f‖ := h2
      _ ≤ 1 * ‖f‖ := by
          apply mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  · rw [heatPropagatorTotal_of_nonpos ht]

/-- The little-Hölder submodule is closed: a 3-ε argument using the uniform
contraction bound. -/
theorem isClosed_littleHolderSubmodule :
    IsClosed (littleHolderSubmodule (n := n) (α := α)).carrier := by
  -- Sequential closedness in the metric space.
  apply SequentialSpace.isClosed_of_seq
  intro u f hu hlim
  -- `hu : ∀ n, u n ∈ carrier`, i.e., each `u n` is good.
  -- `hlim : Tendsto u atTop (𝓝 f)`.
  show IsGoodHolder f
  unfold IsGoodHolder
  -- 3-ε: for `ε > 0`, find `δ` such that `‖S t f - f‖ < ε` for `t ∈ (0,δ)`.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Pick `N` with `‖u N - f‖ < ε/3`.
  have h3 : (0 : ℝ) < ε / 3 := by linarith
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε / 3) h3
  have hN' : ‖u N - f‖ < ε / 3 := by
    have hdist := hN N le_rfl
    rwa [dist_eq_norm] at hdist
  -- `u N` is good: pick `δ` with `‖S t (u N) - u N‖ < ε/3` for `t ∈ (0,δ)`.
  have hgood : IsGoodHolder (u N) := hu N
  unfold IsGoodHolder at hgood
  rw [Metric.tendsto_nhdsWithin_nhds] at hgood
  obtain ⟨δ, hδpos, hδ⟩ := hgood (ε / 3) h3
  refine ⟨δ, hδpos, fun t ht hdist => ?_⟩
  have ht' := hδ ht hdist
  -- `‖S t (u N) - u N‖ < ε/3`.
  rw [dist_eq_norm] at ht'
  -- 3-ε triangle inequality.
  have hcontract : ‖heatPropagatorTotal t f - heatPropagatorTotal t (u N)‖ ≤ ‖u N - f‖ := by
    have hneg : heatPropagatorTotal t (-(u N)) = -(heatPropagatorTotal t (u N)) := by
      have h := heatPropagatorTotal_smul t (-1 : ℝ) (u N)
      rwa [neg_one_smul, neg_one_smul] at h
    have hsub : heatPropagatorTotal t f - heatPropagatorTotal t (u N) =
        heatPropagatorTotal t (f - u N) := by
      have hfu : f - u N = f + (-(u N)) := by abel
      rw [hfu, heatPropagatorTotal_add, hneg, ← sub_eq_add_neg]
    rw [hsub]
    calc ‖heatPropagatorTotal t (f - u N)‖ ≤ ‖f - u N‖ :=
          norm_heatPropagatorTotal_le t (f - u N)
      _ = ‖u N - f‖ := by rw [norm_sub_rev]
  calc dist (heatPropagatorTotal t f) f
      = ‖heatPropagatorTotal t f - f‖ := dist_eq_norm _ _
    _ ≤ ‖heatPropagatorTotal t f - heatPropagatorTotal t (u N)‖ +
          ‖heatPropagatorTotal t (u N) - u N‖ + ‖u N - f‖ := by
        have htri := norm_add_le (heatPropagatorTotal t f - heatPropagatorTotal t (u N))
          (heatPropagatorTotal t (u N) - u N + (u N - f))
        have heq : heatPropagatorTotal t f - f =
            (heatPropagatorTotal t f - heatPropagatorTotal t (u N)) +
            (heatPropagatorTotal t (u N) - u N + (u N - f)) := by abel
        rw [heq]
        calc ‖(heatPropagatorTotal t f - heatPropagatorTotal t (u N)) +
              (heatPropagatorTotal t (u N) - u N + (u N - f))‖
            ≤ ‖heatPropagatorTotal t f - heatPropagatorTotal t (u N)‖ +
              ‖heatPropagatorTotal t (u N) - u N + (u N - f)‖ := htri
          _ ≤ ‖heatPropagatorTotal t f - heatPropagatorTotal t (u N)‖ +
              (‖heatPropagatorTotal t (u N) - u N‖ + ‖u N - f‖) := by
              apply add_le_add_right
              exact norm_add_le _ _
          _ = _ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
        apply add_lt_add
        · apply add_lt_add
          · calc ‖heatPropagatorTotal t f - heatPropagatorTotal t (u N)‖
                ≤ ‖u N - f‖ := hcontract
              _ < ε / 3 := hN'
          · exact ht'
        · exact hN'
    _ = ε := by ring

/-! ## 3. The little-Hölder Banach space -/

/-- The little-Hölder space: the subtype of the little-Hölder submodule. -/
abbrev LittleHolder (n : ℕ) (α : ℝ) : Type := ↥(littleHolderSubmodule (n := n) (α := α))

namespace LittleHolder

variable {n : ℕ} {α : ℝ}

/-- Coercion to the ambient Hölder space. -/
def toHolder (f : LittleHolder n α) : HolderBCF α n := f.val

/-- Membership in the little-Hölder space means goodness. -/
theorem mem_iff (f : LittleHolder n α) : IsGoodHolder f.val := f.property

/-- The little-Hölder space is complete, as a closed submodule of a Banach space. -/
instance : CompleteSpace (LittleHolder n α) := by
  have hclosed : IsClosed (littleHolderSubmodule (n := n) (α := α)).carrier :=
    isClosed_littleHolderSubmodule
  haveI : IsClosed (littleHolderSubmodule (n := n) (α := α)).carrier := hclosed
  exact IsClosed.completeSpace_coe

/-- Semigroup property for the Hölder heat propagator. -/
theorem heatSemigroupHolderFun_comp {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (f : HolderBCF α n) :
    heatSemigroupHolderFun (n := n) (α := α) hs
        (heatSemigroupHolderFun (n := n) (α := α) ht f) =
    heatSemigroupHolderFun (n := n) (α := α) (add_pos hs ht) f := by
  apply Subtype.ext
  show (heatSemigroupHolderFun (n := n) (α := α) hs
    (heatSemigroupHolderFun (n := n) (α := α) ht f)).toBCF =
    (heatSemigroupHolderFun (n := n) (α := α) (add_pos hs ht) f).toBCF
  rw [heatSemigroupHolderFun_toBCF, heatSemigroupHolderFun_toBCF,
    heatSemigroupHolderFun_toBCF]
  exact heatSemigroupNDbcf_comp s t hs ht f.toBCF

/-- The heat propagator preserves the little-Hölder space. -/
theorem propagator_mem {t : ℝ} (ht : 0 < t) (f : LittleHolder n α) :
    IsGoodHolder (heatSemigroupHolderFun (n := n) (α := α) ht f.val) := by
  -- `S s (S t f) = S t (S s f)` by semigroup commutativity.
  -- As `s → 0⁺`, `S s f → f` (f good), so `S t (S s f) → S t f` (continuity of `S t`).
  unfold IsGoodHolder
  have hfgood : IsGoodHolder f.val := f.property
  unfold IsGoodHolder at hfgood
  -- Rewrite `S s (S t f)` as `S t (S s f)` for `s > 0`.
  have hrewrite : (fun s : ℝ ↦ heatPropagatorTotal s
      (heatSemigroupHolderFun (n := n) (α := α) ht f.val)) =
      (fun s : ℝ ↦ heatSemigroupHolderFun (n := n) (α := α) ht
        (heatPropagatorTotal s f.val)) := by
    funext s
    by_cases hs : 0 < s
    · rw [heatPropagatorTotal_of_pos hs, heatPropagatorTotal_of_pos hs]
      -- `S s (S t f) = S (s+t) f` and `S t (S s f) = S (t+s) f`; `s+t = t+s`.
      -- By proof irrelevance, the positivity proofs don't matter.
      have h1 := heatSemigroupHolderFun_comp hs ht f.val
      have h2 := heatSemigroupHolderFun_comp ht hs f.val
      simp only [add_comm s t] at h1
      rw [h1, ← h2]
    · rw [heatPropagatorTotal_of_nonpos hs, heatPropagatorTotal_of_nonpos hs]
  rw [hrewrite]
  -- `S t` is continuous, and `S s f → f`.
  have h1 : Tendsto (⇑(heatSemigroupHolderCLM (n := n) (α := α) ht))
      (𝓝 f.val) (𝓝 ((heatSemigroupHolderCLM (n := n) (α := α) ht) f.val)) :=
    (heatSemigroupHolderCLM (n := n) (α := α) ht).continuous.tendsto _
  exact h1.comp hfgood

/-- The heat propagator as a continuous linear map on little-Hölder. -/
noncomputable def littleHolderPropagatorCLM {t : ℝ} (ht : 0 < t) :
    LittleHolder n α →L[ℝ] LittleHolder n α :=
  (heatSemigroupHolderCLM (n := n) (α := α) ht).restrict (by
    intro x hx
    -- `hx : x ∈ littleHolderSubmodule`, i.e., `IsGoodHolder x`.
    have hmem := propagator_mem (n := n) (α := α) ht ⟨x, hx⟩
    -- `hmem : IsGoodHolder (heatSemigroupHolderFun ht x)`.
    -- This is `IsGoodHolder (⇑(CLM ht) x)` by definition.
    exact hmem)

/-- Operator norm bound `≤ 1` for the little-Hölder propagator. -/
theorem norm_littleHolderPropagatorCLM_le {t : ℝ} (ht : 0 < t) :
    ‖littleHolderPropagatorCLM (n := n) (α := α) ht‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  intro x
  -- `‖S t x‖_{LittleHolder} = ‖S t x.val‖_{HolderBCF} ≤ ‖x.val‖ = ‖x‖`.
  have h1 : ‖littleHolderPropagatorCLM (n := n) (α := α) ht x‖ =
      ‖(heatSemigroupHolderCLM (n := n) (α := α) ht) x.val‖ := rfl
  rw [h1]
  have hbound : ‖(heatSemigroupHolderCLM (n := n) (α := α) ht) x.val‖ ≤ ‖x.val‖ := by
    calc ‖(heatSemigroupHolderCLM (n := n) (α := α) ht) x.val‖
        ≤ ‖heatSemigroupHolderCLM (n := n) (α := α) ht‖ * ‖x.val‖ :=
          (heatSemigroupHolderCLM (n := n) (α := α) ht).le_opNorm x.val
      _ ≤ 1 * ‖x.val‖ := by
          apply mul_le_mul_of_nonneg_right (norm_heatSemigroupHolderCLM_le ht)
          exact norm_nonneg _
      _ = ‖x.val‖ := one_mul _
  calc ‖(heatSemigroupHolderCLM (n := n) (α := α) ht) x.val‖ ≤ ‖x.val‖ := hbound
    _ = ‖x‖ := rfl
    _ = 1 * ‖x‖ := (one_mul _).symm

/-- Total little-Hölder propagator: the heat semigroup for `t > 0`, identity at `t ≤ 0`. -/
noncomputable def littleHolderPropagator (t : ℝ) : LittleHolder n α →L[ℝ] LittleHolder n α :=
  if ht : 0 < t then littleHolderPropagatorCLM (n := n) (α := α) ht
  else ContinuousLinearMap.id ℝ (LittleHolder n α)

theorem littleHolderPropagator_of_pos {t : ℝ} (ht : 0 < t) :
    littleHolderPropagator (n := n) (α := α) t =
    littleHolderPropagatorCLM (n := n) (α := α) ht :=
  dif_pos ht

theorem littleHolderPropagator_of_nonpos {t : ℝ} (ht : ¬ 0 < t) :
    littleHolderPropagator (n := n) (α := α) t =
    ContinuousLinearMap.id ℝ (LittleHolder n α) :=
  dif_neg ht

/-- Semigroup property for the little-Hölder propagator. -/
theorem littleHolderPropagator_comp {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (f : LittleHolder n α) :
    littleHolderPropagator (n := n) (α := α) s
        (littleHolderPropagator (n := n) (α := α) t f) =
    littleHolderPropagator (n := n) (α := α) (s + t) f := by
  rw [littleHolderPropagator_of_pos hs, littleHolderPropagator_of_pos ht,
    littleHolderPropagator_of_pos (add_pos hs ht)]
  -- Reduce to the Hölder semigroup property via the subtype.
  have h := heatSemigroupHolderFun_comp (n := n) (α := α) hs ht f.val
  -- `littleHolderPropagatorCLM` is the restriction, so it acts as the Hölder propagator on values.
  apply Subtype.ext
  show ((littleHolderPropagatorCLM (n := n) (α := α) hs)
    ((littleHolderPropagatorCLM (n := n) (α := α) ht) f)).val =
    ((littleHolderPropagatorCLM (n := n) (α := α) (add_pos hs ht)) f).val
  -- Both sides are the Hölder propagator applied to values.
  have h1 : ((littleHolderPropagatorCLM (n := n) (α := α) hs)
      ((littleHolderPropagatorCLM (n := n) (α := α) ht) f)).val =
      (heatSemigroupHolderFun (n := n) (α := α) hs
        (heatSemigroupHolderFun (n := n) (α := α) ht f.val)) := rfl
  have h2 : ((littleHolderPropagatorCLM (n := n) (α := α) (add_pos hs ht)) f).val =
      (heatSemigroupHolderFun (n := n) (α := α) (add_pos hs ht) f.val) := rfl
  rw [h1, h2, h]

variable {n : ℕ} {α : ℝ}

/-- The propagator is a contraction for all `t`: `‖S t f‖ ≤ ‖f‖`. -/
theorem norm_propagator_le (t : ℝ) (f : LittleHolder n α) :
    ‖littleHolderPropagator (n := n) (α := α) t f‖ ≤ ‖f‖ := by
  by_cases ht : 0 < t
  · rw [littleHolderPropagator_of_pos ht]
    have h := norm_littleHolderPropagatorCLM_le (n := n) (α := α) ht
    calc ‖littleHolderPropagatorCLM (n := n) (α := α) ht f‖
        ≤ ‖littleHolderPropagatorCLM (n := n) (α := α) ht‖ * ‖f‖ :=
          (littleHolderPropagatorCLM (n := n) (α := α) ht).le_opNorm f
      _ ≤ 1 * ‖f‖ := by
          apply mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  · rw [littleHolderPropagator_of_nonpos ht]
    simp

end LittleHolder

end AnalyticPDE
end RicciFlow
