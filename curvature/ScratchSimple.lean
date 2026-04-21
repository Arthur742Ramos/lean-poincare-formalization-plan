-- Minimal test for ext issue

import Mathlib.Tactic

variable {R : Type*} [Semiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

-- Test: ext with too many arguments
example (f g : M →L[R] N) : f = g := by
  ext x
  sorry

-- This should work
example (f g : M →L[R] N →L[R] ℝ) (h : ∀ x y, f x y = g x y) : f = g := by
  ext x y
  exact h x y

-- This might be the issue - using ext u w when the types don't support it
example (f g : M →L[R] N) (h : ∀ x y, f x = g x) : f = g := by
  ext x
  -- Now the goal should be f x = g x, not a function equality
  sorry
