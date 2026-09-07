module

public import Mathlib

public section

/-!
# The sharp almost-Schur reduction

This is the independent statement surface for the De Lellis--Topping
formalization.  The variables below are the scalar quantities produced by the
geometric proof: `A` is scalar-curvature variance, `B` is squared
trace-free-Ricci energy, `H` is trace-free-Hessian energy, `P` is the
contracted-Bianchi pairing, and `Ric` is the integrated Ricci-gradient term.

The two displayed identities are the exact analytic output of the geometric
integration and Bochner layers.  The Challenge deliberately contains no local
project imports; `Solution.lean` proves these reductions and also exports the
complete manifold-level inequality and equality characterization.
-/

namespace AlmostSchurEntry

/-- The sharp dimensional almost-Schur constant follows from the contracted
Bianchi pairing estimate and the integrated Bochner/trace identities. -/
theorem almostSchur_from_identities {d A B Hess Ric H P : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRic : 0 ≤ Ric)
    (hcontracted : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H)
    (hbochner : Hess + Ric = A)
    (htrace : d * H = d * Hess - A) :
    A ≤ (4 * d * (d - 1) / (d - 2) ^ 2) * B := by
  sorry

/-- Equality in the sharp reduction either has zero trace-free-Ricci energy,
or forces equality in every intermediate nonnegative estimate. -/
theorem almostSchur_equality_data {d A B Hess Ric H P : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRic : 0 ≤ Ric)
    (hcontracted : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H)
    (hbochner : Hess + Ric = A)
    (htrace : d * H = d * Hess - A)
    (heq : A = (4 * d * (d - 1) / (d - 2) ^ 2) * B) :
    B = 0 ∨
      (0 < A ∧ 0 < B ∧ d * H = (d - 1) * A ∧ Ric = 0 ∧
        P ^ 2 = B * H ∧ (d - 2) * P = 2 * (d - 1) * B) := by
  sorry

end AlmostSchurEntry

end
