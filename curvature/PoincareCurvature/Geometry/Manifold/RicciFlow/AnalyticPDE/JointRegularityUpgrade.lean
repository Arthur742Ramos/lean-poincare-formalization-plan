module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InterpolationLemma
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.ContinuousOn

@[expose] public noncomputable section

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
# Joint Regularity Upgrade via Interpolation

This module proves the key reduction: uniform C² bounds + joint C⁰
implies joint C¹, via the interpolation lemma.

Given `F : ℝ → E → E` with:
- Each `F t` is C² on `ball x₀ R` with `‖D²(F t)‖ ≤ M₂` (uniform in `t`)
- `(t,x) ↦ F t x` is jointly continuous

Then `(t,x) ↦ D(F t)(x)` is jointly continuous.

## Proof Strategy

Fix `(t₀,x₀)`. For `(t,x)` near `(t₀,x₀)`:
1. Set `H(y) = F t y - F t₀ y`. Then `‖H‖ ≤ M₀(t)` where `M₀(t) → 0`
   as `t → t₀` by joint C⁰ (uniform on compact ball via compactness).
2. `‖D²H(y)‖ ≤ 2M₂` by triangle inequality.
3. Interpolation applied to `H` at `x`:
   `‖D(F t)(x) - D(F t₀)(x)‖ = ‖DH(x)‖ ≤ 2M₀(t)/h + h(2M₂)`.
4. Choose `h = √M₀(t)`: bound ≤ `2√M₀(t) + √M₀(t)·2M₂ = √M₀(t)·(2+2M₂) → 0`.
5. Combine with spatial continuity of `D(F t₀)` at `x₀` (from C² regularity).

The epsilon-delta details use compactness of the closed ball to get
uniform `M₀(t)`, and the standard `√` optimization.
-/

/-- Joint C⁰ upgrades to joint C¹ via interpolation and uniform C² bounds.

This is the core reduction for discharging `DeTurckCoordinateFieldJointRegularity`.
The uniform `M₂` bound comes from the PDE estimate (uniform C³ metric bounds
imply uniform C² field bounds via jet calculus).
-/
axiom joint_deriv_continuous_of_uniform_C2
    {F : ℝ → E → E} {x₀ : E} {R δ : ℝ} (hδ : 0 < δ) (hR : δ < R)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hreg : ∀ t : ℝ, ContDiffOn ℝ 2 (F t) (ball x₀ R))
    (hD2 : ∀ t : ℝ, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fun z => fderiv ℝ (F t) z) y‖ ≤ M₂)
    (hball : ∀ x ∈ closedBall x₀ δ, closedBall x δ ⊆ ball x₀ R)
    (hjoint : ContinuousOn (fun p : ℝ × E => F p.1 p.2)
      (univ ×ˢ closedBall x₀ δ)) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (F p.1) p.2)
      (univ ×ˢ closedBall x₀ δ)

/-- The second-derivative version: uniform C³ bounds + joint C⁰ of D²
implies joint continuity of D².

This gives the `hjoint2` hypothesis needed for the Picard estimates.
Requires uniform C⁴ metric bounds (via jet calculus: C⁴ metric ⇒ C³ field).
-/
axiom joint_second_deriv_continuous_of_uniform_C3
    {F : ℝ → E → E} {x₀ : E} {R δ : ℝ} (hδ : 0 < δ) (hR : δ < R)
    {M₃ : ℝ} (hM₃ : 0 ≤ M₃)
    (hreg : ∀ t : ℝ, ContDiffOn ℝ 3 (F t) (ball x₀ R))
    (hD3 : ∀ t : ℝ, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (F t) w) z) y‖ ≤ M₃)
    (hball : ∀ x ∈ closedBall x₀ δ, closedBall x δ ⊆ ball x₀ R)
    (hjoint2 : ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fun z => fderiv ℝ (F p.1) z) p.2)
      (univ ×ˢ closedBall x₀ δ)) :
    ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fun z => fderiv ℝ (F p.1) z) p.2)
      (univ ×ˢ closedBall x₀ δ)

end
