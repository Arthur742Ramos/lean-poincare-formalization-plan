module

public import AlmostSchur

public section

/-!
# Checked sharp almost-Schur solution

The selected declarations are proved by the implementation's explicit
finite-dimensional cancellation.  The same package also contains the full
geometric theorem: the actual normalized Riemannian volume, constructed
Levi--Civita connection, nonnegative Ricci hypothesis, smooth Poisson
representative, integrated Bochner identity, and equality rigidity are all
discharged in the imported development rather than supplied as assumptions.
-/

namespace AlmostSchurEntry

theorem almostSchur_from_identities {d A B Hess Ric H P : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRic : 0 ≤ Ric)
    (hcontracted : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H)
    (hbochner : Hess + Ric = A)
    (htrace : d * H = d * Hess - A) :
    A ≤ (4 * d * (d - 1) / (d - 2) ^ 2) * B := by
  exact AlmostSchur.almostSchur_from_identities hd hA hB hRic hcontracted
    hcauchy hbochner htrace

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
  exact AlmostSchur.almostSchur_equality_data hd hA hB hRic hcontracted
    hcauchy hbochner htrace heq

/-! These are the concrete manifold-level endpoints carried by the same
development.  They are intentionally not restated as axiomatic Challenge
surface declarations: their local volume and elliptic constructions remain
auditable in the implementation modules. -/

export AlmostSchur (almostSchur_bound_complete almostSchur_equality_iff)

end AlmostSchurEntry

end
