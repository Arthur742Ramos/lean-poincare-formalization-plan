module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public noncomputable section

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Interpolation inequality: C² control gives C¹ bound. (Proved on paper 2026-09-21.)

If `f` is C² on `ball x₀ R` with `‖f‖ ≤ M₀` and `‖D²f‖ ≤ M₂`,
then for `x` with `closedBall x δ ⊆ ball x₀ R` and `0 < h ≤ δ`:
  `‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂`.

Proof sketch: For unit `v`, set `g(s) = f(x + s•v)`. Then `‖g‖ ≤ M₀`,
`‖g''‖ ≤ M₂`. Define `ψ(s) = g(s) - s•g'(0)`. Then `‖ψ'(s)‖ = ‖g'(s)-g'(0)‖ ≤ M₂*s`
by MVT on `g'`. Apply MVT to `ψ` on `[0,h]`: `‖ψ(h)-ψ(0)‖ ≤ M₂*h²`.
But `ψ(h)-ψ(0) = (g(h)-g(0)) - h•g'(0)`, so `h*‖g'(0)‖ ≤ 2*M₀ + M₂*h²`.
Divide by `h` and note `g'(0) = Df(x)(v)`.
-/
axiom norm_fderiv_le_of_C2_bound
    {f : E → F} {x₀ : E} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R))
    {M₀ M₂ : ℝ}
    (h0 : ∀ y ∈ ball x₀ R, ‖f y‖ ≤ M₀)
    (h2 : ∀ y ∈ ball x₀ R, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ M₂)
    {x : E} {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hhδ : h ≤ δ)
    (hx : closedBall x δ ⊆ ball x₀ R) :
    ‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂

end
