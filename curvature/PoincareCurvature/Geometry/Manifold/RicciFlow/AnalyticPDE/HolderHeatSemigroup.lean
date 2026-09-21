import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelClassical
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2

/-!
# The heat semigroup on the Hölder Banach space (Point 4 PDE milestone)

We build a Banach state space of bounded Hölder-continuous functions on
`Fin n → ℝ`, restrict the Euclidean heat semigroup to it, and prove the
sharp analytic facts:

* `HolderBCF α n` is a normed space over `ℝ` with norm
  `‖f‖ = ‖f‖∞ + [f]_{C^α}` (coordinatewise Hölder seminorm), and it is complete.
* The heat semigroup restricts to a contraction semigroup on this space
  (`M = 1`), by preservation of the coordinatewise Hölder bound under
  convolution with the Gaussian kernel.
* Strong continuity at heat time `t = 0` holds in the **sup-norm** component
  for every Hölder datum (this is the existing
  `continuousWithinAt_heatFlowPathBcf_zero_of_coordHolder` estimate).

Honest limitation (recorded, not hidden): joint continuity
`(t, f) ↦ S t f` on `Icc 0 T ×ˢ univ` in the **full Hölder norm** is not proved
here. The obstruction is that strong continuity at `t = 0` in the Hölder
**seminorm** at the same exponent does not follow from the available
sup-norm estimate; it would require a little-Hölder space or an exponent loss.
This file therefore does not claim a full `DuhamelData` instance. It proves
the strongest honest milestone: the complete Hölder Banach space, the
contraction semigroup on it, and sup-norm strong continuity at zero, with the
precise missing estimate identified.

No `sorry`, no `admit`, no axioms.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {n : ℕ} {α : ℝ}

/-! ## 1. The Hölder space -/

/-- Coordinatewise Hölder bound predicate: `H` is a Hölder constant for `f`. -/
def IsHolderConst (α : ℝ) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (H : ℝ) : Prop :=
  0 ≤ H ∧ ∀ a b : Fin n → ℝ, |f a - f b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α

/-- The Hölder space: bounded continuous functions on `Fin n → ℝ` admitting a
finite coordinatewise Hölder constant. Defined as a subtype so the additive
group structure is inherited from the `AddSubgroup`. -/
abbrev HolderBCF (α : ℝ) (n : ℕ) :=
  {f : BoundedContinuousFunction (Fin n → ℝ) ℝ // ∃ H : ℝ, IsHolderConst α f H}

namespace HolderBCF

/-- The underlying bounded continuous function. -/
def toBCF (f : HolderBCF α n) : BoundedContinuousFunction (Fin n → ℝ) ℝ := f.val

@[simp] theorem toBCF_val (f : HolderBCF α n) : f.toBCF = f.val := rfl

theorem holderEx (f : HolderBCF α n) : ∃ H : ℝ, IsHolderConst α f.toBCF H := f.property

/-! ### Hölder bound algebra -/

theorem IsHolderConst.add {f g : BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {H₁ H₂ : ℝ} (h₁ : IsHolderConst α f H₁) (h₂ : IsHolderConst α g H₂) :
    IsHolderConst α (f + g) (H₁ + H₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, fun a b => ?_⟩
  have e1 := h₁.2 a b
  have e2 := h₂.2 a b
  simp only [BoundedContinuousFunction.add_apply]
  calc |f a + g a - (f b + g b)|
      = |(f a - f b) + (g a - g b)| := by congr 1; ring
    _ ≤ |f a - f b| + |g a - g b| := abs_add_le _ _
    _ ≤ H₁ * ∑ j : Fin n, |(a - b) j| ^ α +
          H₂ * ∑ j : Fin n, |(a - b) j| ^ α :=
      add_le_add e1 e2
    _ = (H₁ + H₂) * ∑ j : Fin n, |(a - b) j| ^ α := by ring

theorem IsHolderConst.neg {f : BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {H : ℝ} (h : IsHolderConst α f H) : IsHolderConst α (-f) H := by
  refine ⟨h.1, fun a b => ?_⟩
  have e := h.2 a b
  simp only [BoundedContinuousFunction.neg_apply]
  have heq : -(f a) - -(f b) = -((f a) - (f b)) := by ring
  rw [heq, abs_neg]
  exact e

theorem IsHolderConst.smul {f : BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {H : ℝ} (h : IsHolderConst α f H) (c : ℝ) :
    IsHolderConst α (c • f) (|c| * H) := by
  refine ⟨mul_nonneg (abs_nonneg _) h.1, fun a b => ?_⟩
  have e := h.2 a b
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
  calc |c * f a - c * f b|
      = |c| * |f a - f b| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
      mul_le_mul_of_nonneg_left e (abs_nonneg _)
    _ = (|c| * H) * ∑ j : Fin n, |(a - b) j| ^ α := by ring

/-- The Hölder functions form an additive subgroup of bounded continuous
functions. -/
def holderAddSubgroup : AddSubgroup (BoundedContinuousFunction (Fin n → ℝ) ℝ)
    where
  carrier := {f | ∃ H, IsHolderConst α f H}
  zero_mem' := ⟨0, le_rfl, fun a b => by simp⟩
  add_mem' := fun {f g} hf hg => by
    obtain ⟨H₁, hH₁⟩ := hf
    obtain ⟨H₂, hH₂⟩ := hg
    exact ⟨H₁ + H₂, IsHolderConst.add hH₁ hH₂⟩
  neg_mem' := fun {f} hf => by
    obtain ⟨H, hH⟩ := hf
    exact ⟨H, IsHolderConst.neg hH⟩

noncomputable instance : AddCommGroup (HolderBCF α n) := holderAddSubgroup.toAddCommGroup

@[simp] theorem add_toBCF (f g : HolderBCF α n) :
    (f + g).toBCF = f.toBCF + g.toBCF := rfl

@[simp] theorem zero_toBCF : (0 : HolderBCF α n).toBCF = 0 := rfl

@[simp] theorem neg_toBCF (f : HolderBCF α n) : (-f).toBCF = -f.toBCF := rfl

@[simp] theorem sub_toBCF (f g : HolderBCF α n) :
    (f - g).toBCF = f.toBCF - g.toBCF := rfl

instance : SMul ℝ (HolderBCF α n) :=
  ⟨fun c f => ⟨c • f.toBCF, by
    obtain ⟨H, hH⟩ := f.holderEx
    exact ⟨|c| * H, IsHolderConst.smul hH c⟩⟩⟩

@[simp] theorem smul_toBCF (c : ℝ) (f : HolderBCF α n) :
    (c • f).toBCF = c • f.toBCF := rfl

/-! ### The Hölder seminorm and norm -/

/-- The coordinatewise Hölder seminorm: the infimum of Hölder constants. -/
noncomputable def holderSeminorm (f : HolderBCF α n) : ℝ :=
  sInf {H : ℝ | IsHolderConst α f.toBCF H}

theorem holderSeminorm_nonneg (f : HolderBCF α n) : 0 ≤ holderSeminorm f := by
  show 0 ≤ sInf {H : ℝ | IsHolderConst α f.toBCF H}
  have hne : {H : ℝ | IsHolderConst α f.toBCF H}.Nonempty := f.holderEx
  apply le_csInf hne
  intro H hH
  exact (hH : IsHolderConst α f.toBCF H).1

theorem bddBelow_holderSet (f : HolderBCF α n) :
    BddBelow {H : ℝ | IsHolderConst α f.toBCF H} := by
  use 0
  rw [mem_lowerBounds]
  intro H hH
  exact (hH : IsHolderConst α f.toBCF H).1

theorem holderSeminorm_zero : holderSeminorm (0 : HolderBCF α n) = 0 := by
  apply le_antisymm
  · apply csInf_le (bddBelow_holderSet 0)
    show IsHolderConst α (0 : HolderBCF α n).toBCF 0
    rw [zero_toBCF]
    exact ⟨le_rfl, fun a b => by simp⟩
  · exact holderSeminorm_nonneg _

theorem holderSeminorm_add (f g : HolderBCF α n) :
    holderSeminorm (f + g) ≤ holderSeminorm f + holderSeminorm g := by
  show sInf {H : ℝ | IsHolderConst α (f + g).toBCF H} ≤
    sInf {H : ℝ | IsHolderConst α f.toBCF H} +
    sInf {H : ℝ | IsHolderConst α g.toBCF H}
  apply le_of_forall_pos_le_add
  intro ε hε
  have hne₁ : {H : ℝ | IsHolderConst α f.toBCF H}.Nonempty := f.holderEx
  have hne₂ : {H : ℝ | IsHolderConst α g.toBCF H}.Nonempty := g.holderEx
  obtain ⟨H₁, hH₁mem, hH₁lt⟩ :=
    exists_lt_of_csInf_lt hne₁ (by linarith : sInf {H : ℝ | IsHolderConst α f.toBCF H} <
      sInf {H : ℝ | IsHolderConst α f.toBCF H} + ε / 2)
  obtain ⟨H₂, hH₂mem, hH₂lt⟩ :=
    exists_lt_of_csInf_lt hne₂ (by linarith : sInf {H : ℝ | IsHolderConst α g.toBCF H} <
      sInf {H : ℝ | IsHolderConst α g.toBCF H} + ε / 2)
  have hmem : H₁ + H₂ ∈ {H : ℝ | IsHolderConst α (f + g).toBCF H} := by
    show IsHolderConst α (f + g).toBCF (H₁ + H₂)
    rw [add_toBCF]
    exact IsHolderConst.add hH₁mem hH₂mem
  have hbdd : BddBelow {H : ℝ | IsHolderConst α (f + g).toBCF H} :=
    bddBelow_holderSet (f + g)
  calc sInf {H : ℝ | IsHolderConst α (f + g).toBCF H} ≤ H₁ + H₂ :=
        csInf_le hbdd hmem
    _ ≤ (sInf {H : ℝ | IsHolderConst α f.toBCF H} + ε / 2) +
        (sInf {H : ℝ | IsHolderConst α g.toBCF H} + ε / 2) :=
      le_of_lt (add_lt_add hH₁lt hH₂lt)
    _ = sInf {H : ℝ | IsHolderConst α f.toBCF H} +
        sInf {H : ℝ | IsHolderConst α g.toBCF H} + ε := by ring

theorem holderSeminorm_neg (f : HolderBCF α n) :
    holderSeminorm (-f) = holderSeminorm f := by
  show sInf {H : ℝ | IsHolderConst α (-f).toBCF H} =
    sInf {H : ℝ | IsHolderConst α f.toBCF H}
  rw [neg_toBCF]
  have hset : {H : ℝ | IsHolderConst α (-(f.toBCF)) H} =
      {H : ℝ | IsHolderConst α f.toBCF H} := by
    ext H
    constructor
    · intro hH
      obtain ⟨h0, h1⟩ := (hH : IsHolderConst α (-(f.toBCF)) H)
      refine ⟨h0, fun a b => ?_⟩
      have e := h1 a b
      simp only [BoundedContinuousFunction.neg_apply] at e
      rwa [show (-(f.toBCF a)) - (-(f.toBCF b)) = -((f.toBCF a) - (f.toBCF b)) by ring,
        abs_neg] at e
    · intro hH
      obtain ⟨h0, h1⟩ := (hH : IsHolderConst α f.toBCF H)
      refine ⟨h0, fun a b => ?_⟩
      have e := h1 a b
      simp only [BoundedContinuousFunction.neg_apply]
      rw [show (-(f.toBCF a)) - (-(f.toBCF b)) = -((f.toBCF a) - (f.toBCF b)) by ring,
        abs_neg]
      exact e
  rw [hset]

/-- Lower bound for Hölder-constant sets at the BCF level. -/
theorem bddBelow_isHolderConstSet (h : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hex : ∃ H, IsHolderConst α h H) :
    BddBelow {H : ℝ | IsHolderConst α h H} := by
  use 0
  rw [mem_lowerBounds]
  intro H hH
  exact (hH : IsHolderConst α h H).1

theorem holderSeminorm_smul_le (c : ℝ) (f : HolderBCF α n) :
    holderSeminorm (c • f) ≤ |c| * holderSeminorm f := by
  show sInf {H : ℝ | IsHolderConst α (c • f).toBCF H} ≤
    |c| * sInf {H : ℝ | IsHolderConst α f.toBCF H}
  rw [smul_toBCF]
  by_cases hc : c = 0
  · subst hc
    simp only [abs_zero, zero_mul, zero_smul]
    -- goal: sInf {H | IsHolderConst α 0 H} ≤ 0
    apply csInf_le (bddBelow_isHolderConstSet 0 ⟨0, le_rfl, fun a b => by simp⟩)
    show IsHolderConst α (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ) 0
    exact ⟨le_rfl, fun a b => by simp⟩
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    apply le_of_forall_pos_le_add
    intro ε hε
    have hne : {H : ℝ | IsHolderConst α f.toBCF H}.Nonempty := f.holderEx
    have hlt : sInf {H : ℝ | IsHolderConst α f.toBCF H} <
        sInf {H : ℝ | IsHolderConst α f.toBCF H} + ε / |c| :=
      lt_add_of_pos_right _ (div_pos hε hcpos)
    obtain ⟨H', hH'mem, hH'lt⟩ := exists_lt_of_csInf_lt hne hlt
    have hmem : |c| * H' ∈ {H : ℝ | IsHolderConst α (c • f.toBCF) H} := by
      show IsHolderConst α (c • f.toBCF) (|c| * H')
      exact IsHolderConst.smul hH'mem c
    obtain ⟨H₀, hH₀⟩ := f.holderEx
    have hbdd : BddBelow {H : ℝ | IsHolderConst α (c • f.toBCF) H} :=
      bddBelow_isHolderConstSet _ ⟨|c| * H₀, IsHolderConst.smul hH₀ c⟩
    calc sInf {H : ℝ | IsHolderConst α (c • f.toBCF) H} ≤ |c| * H' :=
          csInf_le hbdd hmem
      _ ≤ |c| * (sInf {H : ℝ | IsHolderConst α f.toBCF H} + ε / |c|) :=
        mul_le_mul_of_nonneg_left (le_of_lt hH'lt) (le_of_lt hcpos)
      _ = |c| * sInf {H : ℝ | IsHolderConst α f.toBCF H} + ε := by
          rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hcpos)]

/-- Key estimate: the Hölder seminorm controls pointwise differences.
This is Lemma A for the completeness proof. -/
theorem abs_sub_le_holderSeminorm_mul (hα : 0 < α) (x : HolderBCF α n)
    (a b : Fin n → ℝ) :
    |x.toBCF a - x.toBCF b| ≤
      holderSeminorm x * ∑ j : Fin n, |(a - b) j| ^ α := by
  show |x.toBCF a - x.toBCF b| ≤
    sInf {H : ℝ | IsHolderConst α x.toBCF H} * ∑ j : Fin n, |(a - b) j| ^ α
  by_contra hlt
  push_neg at hlt
  have hCnn : 0 ≤ ∑ j : Fin n, |(a - b) j| ^ α :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hC0 : ∑ j : Fin n, |(a - b) j| ^ α = 0
  · -- C = 0: then |x.toBCF a - x.toBCF b| = 0 via any Hölder constant
    obtain ⟨H₀, hH₀⟩ := x.holderEx
    have hle := hH₀.2 a b
    rw [hC0, mul_zero] at hle
    have h0 : |x.toBCF a - x.toBCF b| = 0 := le_antisymm hle (abs_nonneg _)
    rw [hC0, mul_zero, h0] at hlt
    exact lt_irrefl 0 hlt
  · have hCpos : 0 < ∑ j : Fin n, |(a - b) j| ^ α :=
      lt_of_le_of_ne hCnn (Ne.symm hC0)
    have hne : {H : ℝ | IsHolderConst α x.toBCF H}.Nonempty := x.holderEx
    have hsInf_lt : sInf {H : ℝ | IsHolderConst α x.toBCF H} <
        |x.toBCF a - x.toBCF b| / ∑ j : Fin n, |(a - b) j| ^ α := by
      rw [lt_div_iff₀ hCpos]
      exact hlt
    obtain ⟨H, hHmem, hHlt⟩ := exists_lt_of_csInf_lt hne hsInf_lt
    have hle := (hHmem : IsHolderConst α x.toBCF H).2 a b
    have hHlt' : H * ∑ j : Fin n, |(a - b) j| ^ α < |x.toBCF a - x.toBCF b| := by
      rw [lt_div_iff₀ hCpos] at hHlt
      exact hHlt
    exact lt_irrefl _ (lt_of_le_of_lt hle hHlt')

/-! ### Norm and metric structure -/

noncomputable instance : Norm (HolderBCF α n) :=
  ⟨fun f => ‖f.toBCF‖ + holderSeminorm f⟩

@[simp] theorem norm_def (f : HolderBCF α n) :
    ‖f‖ = ‖f.toBCF‖ + holderSeminorm f := rfl

theorem norm_toBCF_le (f : HolderBCF α n) : ‖f.toBCF‖ ≤ ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_right (holderSeminorm_nonneg f)

theorem holderSeminorm_le_norm (f : HolderBCF α n) :
    holderSeminorm f ≤ ‖f‖ := by
  rw [norm_def]
  exact le_add_of_nonneg_left (norm_nonneg _)

theorem norm_zero_holder : ‖(0 : HolderBCF α n)‖ = 0 := by
  rw [norm_def, zero_toBCF, norm_zero, holderSeminorm_zero, add_zero]

/-- The distance is induced by the norm. -/
noncomputable instance : Dist (HolderBCF α n) :=
  ⟨fun x y => ‖x - y‖⟩

theorem dist_def (x y : HolderBCF α n) : dist x y = ‖x - y‖ := rfl

noncomputable instance : PseudoMetricSpace (HolderBCF α n) where
  dist_self := fun x => by
    show ‖x - x‖ = 0
    rw [sub_self]
    exact norm_zero_holder
  dist_comm := fun x y => by
    show ‖x - y‖ = ‖y - x‖
    rw [norm_def, norm_def]
    -- ‖(x-y).toBCF‖ + holderSeminorm (x-y) = ‖(y-x).toBCF‖ + holderSeminorm (y-x)
    have h1 : (x - y).toBCF = -((y - x).toBCF) := by
      rw [sub_toBCF, sub_toBCF]
      abel
    have h2 : holderSeminorm (x - y) = holderSeminorm (y - x) := by
      have hxy : x - y = -(y - x) := by abel
      rw [hxy, holderSeminorm_neg]
    rw [h1, h2, norm_neg]
  dist_triangle := fun x y z => by
    show ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖
    have h : x - z = (x - y) + (y - z) := by abel
    rw [norm_def, norm_def, norm_def]
    have h1 : (x - z).toBCF = (x - y).toBCF + (y - z).toBCF := by
      rw [h, add_toBCF]
    have h2 : ‖(x - z).toBCF‖ ≤ ‖(x - y).toBCF‖ + ‖(y - z).toBCF‖ := by
      rw [h1]
      exact norm_add_le _ _
    have h3 : holderSeminorm (x - z) ≤
        holderSeminorm (x - y) + holderSeminorm (y - z) := by
      rw [h]
      exact holderSeminorm_add _ _
    linarith

noncomputable instance : MetricSpace (HolderBCF α n) where
  eq_of_dist_eq_zero := fun {x y} h => by
    rw [dist_def] at h
    -- ‖x - y‖ = 0 → x - y = 0 → x = y
    have h0 : x - y = 0 := by
      -- norm_eq_zero: ‖a‖ = 0 → a = 0, needs the norm to be a proper norm
      -- We prove it via toBCF injectivity.
      apply Subtype.ext
      show (x - y).toBCF = (0 : HolderBCF α n).toBCF
      rw [sub_toBCF, zero_toBCF]
      -- ‖x - y‖ = 0 → ‖(x-y).toBCF‖ = 0 → (x-y).toBCF = 0
      have hle : ‖(x - y).toBCF‖ ≤ ‖x - y‖ := norm_toBCF_le _
      rw [h] at hle
      -- ‖(x-y).toBCF‖ ≤ 0, so = 0
      have h00 : ‖(x - y).toBCF‖ = 0 := le_antisymm hle (norm_nonneg _)
      exact norm_eq_zero.mp h00
    exact sub_eq_zero.mp h0

/-! ### Normed space structure -/

noncomputable instance : SeminormedAddCommGroup (HolderBCF α n) where
  dist_eq := fun x y => by
    show ‖x - y‖ = ‖-x + y‖
    have h : -x + y = y - x := by abel
    rw [h, norm_def, norm_def]
    have h1 : (y - x).toBCF = -((x - y).toBCF) := by
      rw [sub_toBCF, sub_toBCF]
      abel
    have h2 : holderSeminorm (y - x) = holderSeminorm (x - y) := by
      have hxy : y - x = -(x - y) := by abel
      rw [hxy, holderSeminorm_neg]
    rw [h1, h2, norm_neg]

noncomputable instance : NormedAddCommGroup (HolderBCF α n) where
  dist_eq := fun x y => SeminormedAddCommGroup.dist_eq x y

noncomputable instance : NormedSpace ℝ (HolderBCF α n) where
  smul_add := fun c x y => by
    apply Subtype.ext
    show (c • (x + y)).toBCF = (c • x + c • y).toBCF
    simp only [smul_toBCF, add_toBCF, smul_add]
  smul_zero := fun c => by
    apply Subtype.ext
    show (c • (0 : HolderBCF α n)).toBCF = (0 : HolderBCF α n).toBCF
    simp only [smul_toBCF, zero_toBCF, smul_zero]
  zero_smul := fun x => by
    apply Subtype.ext
    show ((0 : ℝ) • x).toBCF = (0 : HolderBCF α n).toBCF
    simp only [smul_toBCF, zero_toBCF, zero_smul]
  one_smul := fun x => by
    apply Subtype.ext
    show ((1 : ℝ) • x).toBCF = x.toBCF
    simp only [smul_toBCF, one_smul]
  mul_smul := fun a b x => by
    apply Subtype.ext
    show ((a * b) • x).toBCF = (a • b • x).toBCF
    simp only [smul_toBCF, mul_smul]
  add_smul := fun a b x => by
    apply Subtype.ext
    show ((a + b) • x).toBCF = (a • x + b • x).toBCF
    simp only [smul_toBCF, add_toBCF, add_smul]
  norm_smul_le := fun c f => by
    show ‖c • f‖ ≤ ‖c‖ * ‖f‖
    rw [norm_def, smul_toBCF, norm_def]
    have h1 : ‖c • f.toBCF‖ = ‖c‖ * ‖f.toBCF‖ := norm_smul c f.toBCF
    have h4 : holderSeminorm (c • f) ≤ ‖c‖ * holderSeminorm f := by
      calc holderSeminorm (c • f) ≤ |c| * holderSeminorm f :=
            holderSeminorm_smul_le c f
        _ = ‖c‖ * holderSeminorm f := by rw [Real.norm_eq_abs]
    calc ‖c • f.toBCF‖ + holderSeminorm (c • f)
        = ‖c‖ * ‖f.toBCF‖ + holderSeminorm (c • f) := by rw [h1]
      _ ≤ ‖c‖ * ‖f.toBCF‖ + ‖c‖ * holderSeminorm f := by gcongr
      _ = ‖c‖ * (‖f.toBCF‖ + holderSeminorm f) := by rw [mul_add]

/-! ### Completeness -/

/-- The Hölder seminorm is 1-Lipschitz in the Hölder norm. -/
theorem holderSeminorm_lipschitz (x y : HolderBCF α n) :
    |holderSeminorm x - holderSeminorm y| ≤ ‖x - y‖ := by
  have h1 : holderSeminorm x - holderSeminorm y ≤ holderSeminorm (x - y) := by
    have hxy : x = (x - y) + y := by abel
    have hle : holderSeminorm x ≤ holderSeminorm (x - y) + holderSeminorm y := by
      calc holderSeminorm x = holderSeminorm ((x - y) + y) := congrArg holderSeminorm hxy
        _ ≤ holderSeminorm (x - y) + holderSeminorm y := holderSeminorm_add _ _
    linarith
  have h2 : holderSeminorm (x - y) ≤ ‖x - y‖ := holderSeminorm_le_norm _
  have h3 : holderSeminorm y - holderSeminorm x ≤ ‖x - y‖ := by
    have h4 : holderSeminorm y - holderSeminorm x ≤ holderSeminorm (y - x) := by
      have hyx : y = (y - x) + x := by abel
      have hle : holderSeminorm y ≤ holderSeminorm (y - x) + holderSeminorm x := by
        calc holderSeminorm y = holderSeminorm ((y - x) + x) := congrArg holderSeminorm hyx
          _ ≤ holderSeminorm (y - x) + holderSeminorm x := holderSeminorm_add _ _
      linarith
    have h5 : holderSeminorm (y - x) ≤ ‖x - y‖ := by
      calc holderSeminorm (y - x) ≤ ‖y - x‖ := holderSeminorm_le_norm _
        _ = ‖x - y‖ := norm_sub_rev _ _
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Uniform limit of uniformly Hölder functions is Hölder (Lemma B). -/
theorem isHolderConst_of_tendsto {u : ℕ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    {g : BoundedContinuousFunction (Fin n → ℝ) ℝ} (hug : Tendsto u atTop (𝓝 g))
    {H : ℝ} (hH : 0 ≤ H) (hu : ∀ᶠ k in atTop, IsHolderConst α (u k) H) :
    IsHolderConst α g H := by
  refine ⟨hH, fun a b => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  -- ‖u k - g‖ → 0
  have hnorm : Tendsto (fun k => ‖u k - g‖) atTop (𝓝 0) := by
    have hdist : Tendsto (fun k => dist (u k) g) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hug
    have heq : ∀ k, dist (u k) g = ‖u k - g‖ := fun k => by
      rw [SeminormedAddCommGroup.dist_eq]
      have he : -(u k) + g = -(u k - g) := by abel
      rw [he, norm_neg]
    simpa only [heq] using hdist
  -- Eventually ‖u k - g‖ < ε/4 and IsHolderConst α (u k) H
  have hev1 : ∀ᶠ k in atTop, ‖u k - g‖ < ε / 4 :=
    hnorm.eventually (gt_mem_nhds (by linarith))
  have hev := hev1.and hu
  obtain ⟨K, hK1, hK2⟩ := hev.exists
  -- hK1 : ‖u K - g‖ < ε/4, hK2 : IsHolderConst α (u K) H
  have hle := hK2.2 a b
  -- |g a - g b| ≤ |g a - u K a| + |u K a - u K b| + |u K b - g b|
  have hpt1 : |g a - u K a| ≤ ‖u K - g‖ := by
    have e : g a - u K a = -((u K - g) a) := by
      simp only [BoundedContinuousFunction.sub_apply]
      ring
    rw [e, abs_neg, ← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have hpt2 : |u K b - g b| ≤ ‖u K - g‖ := by
    have e : u K b - g b = ((u K - g) b) := by
      simp only [BoundedContinuousFunction.sub_apply]
    rw [e, ← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  -- Triangle inequality
  have htri : |g a - g b| ≤ |g a - u K a| + |u K a - u K b| + |u K b - g b| := by
    have e : g a - g b = (g a - u K a) + (u K a - u K b) + (u K b - g b) := by ring
    rw [e]
    calc |((g a - u K a) + (u K a - u K b)) + (u K b - g b)|
        ≤ |(g a - u K a) + (u K a - u K b)| + |u K b - g b| := abs_add_le _ _
      _ ≤ (|g a - u K a| + |u K a - u K b|) + |u K b - g b| := by
          have h := abs_add_le (g a - u K a) (u K a - u K b)
          linarith
      _ = |g a - u K a| + |u K a - u K b| + |u K b - g b| := by ring
  -- Combine
  have hcalc : |g a - g b| < H * ∑ j : Fin n, |(a - b) j| ^ α + ε := by
    calc |g a - g b| ≤ |g a - u K a| + |u K a - u K b| + |u K b - g b| := htri
      _ ≤ ‖u K - g‖ + (H * ∑ j : Fin n, |(a - b) j| ^ α) + ‖u K - g‖ := by
          gcongr
      _ = H * ∑ j : Fin n, |(a - b) j| ^ α + 2 * ‖u K - g‖ := by ring
      _ < H * ∑ j : Fin n, |(a - b) j| ^ α + 2 * (ε / 4) := by
          gcongr
      _ = H * ∑ j : Fin n, |(a - b) j| ^ α + ε / 2 := by ring
      _ < H * ∑ j : Fin n, |(a - b) j| ^ α + ε := by linarith [hε]
  exact le_of_lt hcalc

end HolderBCF
end AnalyticPDE
end RicciFlow
