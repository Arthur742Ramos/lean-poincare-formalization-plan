module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public noncomputable section

namespace HamiltonIveyChallenge

/-- Closed Mathlib-only statement of Hamilton--Ivey pinching preservation for
the three-dimensional curvature-reaction ODE. -/
def completeStatement : Prop :=
  let scalar := fun lambda mu nu : ℝ ↦ lambda + mu + nu
  let defect := fun K t lambda mu nu : ℝ ↦
    scalar lambda mu nu / (-nu) - Real.log (-nu) + 3 +
      Real.log (K / (1 + K * t))
  ∀ (K T : ℝ) (lambda mu nu : ℝ → ℝ),
    0 < K → 0 ≤ T →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t) →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t) →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t) →
    (∀ t ∈ Set.Icc 0 T, mu t ≤ lambda t) →
    (∀ t ∈ Set.Icc 0 T, nu t ≤ mu t) →
    (∀ t ∈ Set.Icc 0 T, nu t < 0) →
    -K ≤ nu 0 →
    ∀ t ∈ Set.Icc 0 T, 0 ≤ defect K t (lambda t) (mu t) (nu t)

theorem hamiltonIveyODEPinching : completeStatement := by
  sorry

end HamiltonIveyChallenge
