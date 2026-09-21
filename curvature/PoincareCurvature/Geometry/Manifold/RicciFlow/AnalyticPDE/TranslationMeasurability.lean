import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Translation measurability for the heat semigroup (Point 4 PDE milestone)

This file provides the measurability technicality needed for heat semigroup
Hölder preservation on raw (non-BCF) functions.

## Mathematical content

The heat semigroup can be written as a convolution:
  `S(t)f(x) = ∫ f(x - z) G_t(z) dz`

To show `S(t)` preserves Hölder regularity for raw functions `f`, we need
`AEStronglyMeasurable (fun z => f (x - z))` from `AEStronglyMeasurable f`.
This follows because `z ↦ x - z` is measure-preserving for `volume` on
`Fin n → ℝ`:

1. **Negation** `z ↦ -z` is measure-preserving, via `IsNegInvariant volume`
   (from Haar measure regularity: `IsHaarMeasure.isNegInvariant_of_regular`).
2. **Left-addition** `w ↦ x + w` is measure-preserving, via
   `IsAddLeftInvariant volume` (`map_add_left_eq_self`).
3. **Composition**: `x - z = (x + ·) ∘ (-·)`, so `z ↦ x - z` is
   measure-preserving by `MeasurePreserving.comp`.
4. **Transfer**: `AEStronglyMeasurable.comp_measurePreserving` gives the result.

## Main result

- `aestronglyMeasurable_comp_sub_left`: If `f` is ae-strongly-measurable for
  `volume` on `Fin n → ℝ`, then so is `fun z => f (x - z)`.

No `sorry`, no `admit`, no axioms. No new theorem-level assumptions.
-/

namespace RicciFlow
namespace AnalyticPDE

open MeasureTheory Measure

variable {n : ℕ}

/-- Negation `z ↦ -z` is measure-preserving for `volume` on `Fin n → ℝ`.
Uses `IsNegInvariant` from Haar measure regularity. -/
theorem measurePreserving_neg_fin {n : ℕ} :
    MeasurePreserving (fun z : Fin n → ℝ => -z) volume volume :=
  measurePreserving_neg (volume : Measure (Fin n → ℝ))

/-- Left-addition `w ↦ x + w` is measure-preserving for `volume` on `Fin n → ℝ`.
Uses `IsAddLeftInvariant` (translation invariance of Lebesgue measure). -/
theorem measurePreserving_add_left_fin (x : Fin n → ℝ) :
    MeasurePreserving (fun w : Fin n → ℝ => x + w) volume volume := by
  refine ⟨measurable_const_add x, ?_⟩
  exact map_add_left_eq_self volume x

/-- The reflection-translation `z ↦ x - z` is measure-preserving for `volume`
on `Fin n → ℝ`, as the composite `(x + ·) ∘ (-·)`. -/
theorem measurePreserving_sub_left_fin (x : Fin n → ℝ) :
    MeasurePreserving (fun z : Fin n → ℝ => x - z) volume volume := by
  have hcomp := (measurePreserving_add_left_fin x).comp (measurePreserving_neg_fin (n := n))
  have heq : ((fun w : Fin n → ℝ => x + w) ∘ (fun z : Fin n → ℝ => -z))
      = (fun z : Fin n → ℝ => x - z) := by
    funext z
    simp [sub_eq_add_neg]
  rw [heq] at hcomp
  exact hcomp

/-- Ae-strong-measurability is preserved under precomposition with `z ↦ x - z`.
This is the key measurability lemma for heat semigroup Hölder preservation
on raw functions. -/
theorem aestronglyMeasurable_comp_sub_left {f : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z => f (x - z)) volume :=
  hf.comp_measurePreserving (measurePreserving_sub_left_fin x)

end AnalyticPDE
end RicciFlow
