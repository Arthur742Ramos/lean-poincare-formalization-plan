/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HrangeDischarge
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel

/-!
# Euclidean section in the little-Hölder C^{2,α} space (Point 4 PDE milestone)

Constructs the Euclidean section `c : Jet2Section d d α` (constant identity
metric, vanishing derivatives) from constant `LittleHolder` functions.

The key lemma is that constant functions are `IsGoodHolder`: the heat
semigroup fixes constants (`heatSemigroupND_const`), so
`S(t)(const c) = const c` for all `t > 0`, and the convergence
`S(t)f → f` is trivial.

This unlocks `hrange_of_mem_closedBall` from `HrangeDischarge.lean`,
which needs a section `c` with `∀ x, jet2OfSection c x = euclideanJet2`.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology Metric
open scoped NNReal ENNReal Interval

variable {d : ℕ} {α : ℝ}

/-! ## 1. Constant HolderBCF -/

/-- A constant function as a `BoundedContinuousFunction`. -/
noncomputable def constBCF (n : ℕ) (c : ℝ) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.const (Fin n → ℝ) c

/-- A constant function is Hölder with constant 0. -/
theorem isHolderConst_const (n : ℕ) (α : ℝ) (c : ℝ) :
    IsHolderConst α (constBCF n c) 0 := by
  refine ⟨le_rfl, fun a b => ?_⟩
  show |constBCF n c a - constBCF n c b| ≤ 0 * ∑ j : Fin n, |(a - b) j| ^ α
  have h1 : constBCF n c a = c := rfl
  have h2 : constBCF n c b = c := rfl
  rw [h1, h2, sub_self, abs_zero]
  exact mul_nonneg le_rfl (Finset.sum_nonneg fun j _ => by positivity)

/-- A constant function as `HolderBCF`. -/
noncomputable def constHolderBCF (n : ℕ) (α : ℝ) (c : ℝ) : HolderBCF α n :=
  ⟨constBCF n c, 0, isHolderConst_const n α c⟩

/-- The underlying BCF of a constant is the constant BCF. -/
theorem constHolderBCF_toBCF (n : ℕ) (α : ℝ) (c : ℝ) :
    (constHolderBCF n α c).toBCF = constBCF n c := rfl

/-- Evaluation of a constant `HolderBCF` returns the constant. -/
theorem constHolderBCF_eval (n : ℕ) (α : ℝ) (c : ℝ) (x : Fin n → ℝ) :
    (constHolderBCF n α c).toBCF x = c := rfl

/-! ## 2. Heat semigroup fixes constants -/

/-- The heat semigroup (on BCF) fixes constant functions.

This follows from `heatSemigroupND_const`: the n-dimensional heat
semigroup fixes constants pointwise. -/
theorem heatSemigroupNDbcf_const {n : ℕ} {t : ℝ} (ht : 0 < t) (c : ℝ) :
    heatSemigroupNDbcf (n := n) ht (constBCF n c) = constBCF n c := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [heatSemigroupNDbcf_apply]
  have h1 : ((constBCF n c : BoundedContinuousFunction (Fin n → ℝ) ℝ) : (Fin n → ℝ) → ℝ)
      = fun _ => c := rfl
  rw [h1]
  exact heatSemigroupND_const ht c x

/-- `heatSemigroupHolderFun` fixes constant `HolderBCF`. -/
theorem heatSemigroupHolderFun_constHolderBCF {n : ℕ} {α : ℝ} {t : ℝ} (ht : 0 < t)
    (c : ℝ) :
    heatSemigroupHolderFun (n := n) (α := α) ht (constHolderBCF n α c) =
      constHolderBCF n α c := by
  apply Subtype.ext
  show (heatSemigroupHolderFun (n := n) (α := α) ht (constHolderBCF n α c)).toBCF
      = (constHolderBCF n α c).toBCF
  rw [heatSemigroupHolderFun_toBCF]
  have h1 : ((constHolderBCF (n := n) (α := α) c).toBCF : BoundedContinuousFunction _ _)
      = constBCF n c := rfl
  rw [h1]
  exact heatSemigroupNDbcf_const ht c

/-- `heatPropagatorTotal` fixes constants for `t > 0`. -/
theorem heatPropagatorTotal_constHolderBCF {n : ℕ} {α : ℝ} {t : ℝ} (ht : 0 < t)
    (c : ℝ) :
    heatPropagatorTotal (n := n) (α := α) t (constHolderBCF n α c) =
      constHolderBCF n α c := by
  rw [heatPropagatorTotal_of_pos ht]
  exact heatSemigroupHolderFun_constHolderBCF ht c

/-- Constant functions are `IsGoodHolder`.

Since the heat propagator fixes constants for `t > 0` (and is the
identity for `t ≤ 0`), the function `t ↦ heatPropagatorTotal t const`
is constantly `const` in a neighborhood of `0` within `𝓝[>] 0`,
hence tends to `const`. -/
theorem isGoodHolder_constHolderBCF (n : ℕ) (α : ℝ) (c : ℝ) :
    IsGoodHolder (constHolderBCF (n := n) (α := α) c) := by
  unfold IsGoodHolder
  have heq : (fun t : ℝ ↦ heatPropagatorTotal (n := n) (α := α) t
      (constHolderBCF n α c)) = fun _ => constHolderBCF n α c := by
    funext t
    by_cases ht : 0 < t
    · exact heatPropagatorTotal_constHolderBCF ht c
    · rw [heatPropagatorTotal_of_nonpos ht]
  rw [heq]
  exact tendsto_const_nhds

/-- A constant function as `LittleHolder`. -/
noncomputable def constLittleHolder (n : ℕ) (α : ℝ) (c : ℝ) : LittleHolder n α :=
  ⟨constHolderBCF n α c, isGoodHolder_constHolderBCF n α c⟩

/-- Evaluation of a constant `LittleHolder` returns the constant. -/
theorem constLittleHolder_eval (n : ℕ) (α : ℝ) (c : ℝ) (x : Fin n → ℝ) :
    evalLH (constLittleHolder n α c) x = c := rfl

/-! ## 3. The Euclidean section -/

/-- The Euclidean section: constant identity metric, vanishing derivatives.

The 0-jet is the identity matrix (1 on diagonal, 0 elsewhere);
the 1-jet and 2-jet are zero. -/
noncomputable def euclideanSection (d : ℕ) (α : ℝ) : Jet2Section d d α :=
  (fun i j => constLittleHolder d α (if i = j then 1 else 0),
   fun _ _ _ => constLittleHolder d α 0,
   fun _ _ _ _ => constLittleHolder d α 0)

/-- The Euclidean section extracts to the Euclidean jet.

For each `x`, `jet2OfSection (euclideanSection d α) x` has:
- 0-jet: `fun i j => if i = j then 1 else 0` (identity matrix),
- 1-jet, 2-jet: zero.
This equals `euclideanJet2 = ⟨1, 0, 0⟩`. -/
theorem jet2OfSection_euclideanSection (d : ℕ) (α : ℝ) (x : Fin d → ℝ) :
    jet2OfSection (euclideanSection d α) x =
      GenuinePhiRD.euclideanJet2 (d := d) := by
  have h0 : ∀ i j : Fin d,
      evalLH ((euclideanSection d α).val i j) x = (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
    intro i j
    show evalLH (constLittleHolder d α (if i = j then 1 else 0)) x = _
    rw [constLittleHolder_eval]
    rfl
  have h1 : ∀ k : Fin d, ∀ i j : Fin d,
      evalLH (((euclideanSection d α).der1 k) i j) x = 0 := by
    intro k i j
    show evalLH (constLittleHolder d α (0 : ℝ)) x = _
    rw [constLittleHolder_eval]
  have h2 : ∀ k l : Fin d, ∀ i j : Fin d,
      evalLH ((((euclideanSection d α).der2 k) l) i j) x = 0 := by
    intro k l i j
    show evalLH (constLittleHolder d α (0 : ℝ)) x = _
    rw [constLittleHolder_eval]
  unfold jet2OfSection GenuinePhiRD.euclideanJet2
  ext i j
  · exact h0 i j
  · exact h1 _ _ _
  · exact h2 _ _ _ _

end AnalyticPDE
end RicciFlow
