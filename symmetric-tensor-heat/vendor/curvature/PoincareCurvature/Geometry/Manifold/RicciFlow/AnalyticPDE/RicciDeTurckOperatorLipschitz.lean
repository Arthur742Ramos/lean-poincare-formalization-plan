module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Lipschitz framework for the Ricci–DeTurck chart operator

This file isolates the precise Lipschitz estimate required for the
Picard–Lindelöf theorem applied to the Ricci–DeTurck flow in Banach charts.

## The problem

The chart operator `A : ℝ → CSS → CSS` (where `CSS` is the continuous section
space of symmetric 2-tensors) is defined pointwise by the intrinsic
Ricci–DeTurck right-hand side:
  `A t s x = intrinsicRicciDeTurckRHS g background t x`
where `g` is the metric family corresponding to the section `s`.

For `IsPicardLindelof` (via `isPicardLindelof_continuousSectionSpace_of_forall_coord`),
we need the coordinatewise Lipschitz estimate (`hlip`):
  `dist (A t s x) (A t s' x) ≤ K * dist s s'`

## The mathematical content

The Ricci–DeTurck operator is a second-order quasilinear operator:
  `A(g) = -2 Ric(g) + 𝓛_{W(g)} g`

where `W(g)` is the DeTurck vector field. The map `g ↦ Ric(g)` involves second
derivatives of `g`, so Lipschitz continuity on `C⁰` sections is false in
general. The estimate requires either:
- (a) a stronger Banach space norm (C² or Hölder C^{2,α}), or
- (b) a mild-solution formulation via the heat kernel (Duhamel principle).

This file proves the abstract reduction: **if** the operator is Fréchet
differentiable with bounded derivative on a convex set, **then** it is
Lipschitz there. This is the precise bridge from the (hard) PDE derivative
estimate to the (soft) Picard–Lindelöf hypothesis.

## What remains (analytic)

The hard input is the bound on the Fréchet derivative of the Ricci–DeTurck
operator. This requires:
1. The 2-jet smooth dependence: `g ↦ Ric(g)` is smooth as a map on 2-jets.
2. The DeTurck vector field `W(g)` is smooth in the 1-jet of `g`.
3. Composition estimates in the chosen Banach norm.

These are the quasilinear parabolic estimates referenced in
`TimeDependentGeometricRicciDeTurckBanachChart`.
-/

noncomputable section

open scoped Topology NNReal

namespace RicciFlow.AnalyticPDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Abstract Lipschitz via bounded derivative (Banach mean value inequality).**

If `f : E → F` is differentiable at each point of a convex set `s` and the Fréchet derivative
satisfies `‖fderiv ℝ f x‖₊ ≤ K` for all `x ∈ s`, then `f` is `K`-Lipschitz on `s`.

This is the soft analytic bridge: the Picard–Lindelöf Lipschitz hypothesis
reduces to a bound on the linearized operator. -/
theorem lipschitzOn_of_nnnorm_fderiv_le
    {f : E → F} {s : Set E} {K : ℝ≥0}
    (hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ s, ‖fderiv ℝ f x‖₊ ≤ K)
    (hconv : Convex ℝ s) :
    LipschitzOnWith K f s :=
  Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hbound hconv

/-- **Local Lipschitz from local derivative bound.**

If `f` is differentiable at each point of a ball and the derivative is bounded by `K` there,
then `f` is `K`-Lipschitz on that ball. This is the form needed for the
chart's local Picard theorem. -/
theorem lipschitzOn_ball_of_fderiv_bounded
    {f : E → F} {x₀ : E} {r : ℝ} {K : ℝ≥0}
    (hdiff : ∀ x ∈ Metric.ball x₀ r, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Metric.ball x₀ r, ‖fderiv ℝ f x‖₊ ≤ K) :
    LipschitzOnWith K f (Metric.ball x₀ r) :=
  Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hbound (convex_ball x₀ r)

/-- **The Lipschitz goal for the Ricci–DeTurck chart operator.**

For the Picard–Lindelöf theorem (`isPicardLindelof_continuousSectionSpace_of_forall_coord`),
the time-dependent chart operator `A : ℝ → CSS → CSS` must satisfy: for each time `t`,
the map `s ↦ A t s` is `K`-Lipschitz on the section space.

This is the precise analytic obligation. The `hlip` hypothesis of the section-space
Picard theorem is the coordinatewise form of this estimate.

Note: for the genuine second-order Ricci–DeTurck operator, this estimate is false
on `C⁰` sections (the output depends on second derivatives of the input). It becomes
true on a stronger Banach space (C² or Hölder) where the norm controls the 2-jet,
or for a mild-solution (Duhamel) reformulation. -/
def RicciDeTurckChartOperatorLipschitz
    {CSS : Type*} [PseudoMetricSpace CSS]
    (A : ℝ → CSS → CSS) (K : ℝ≥0) : Prop :=
  ∀ t : ℝ, LipschitzWith K (A t)

/-- **Reduction: bounded derivative implies the chart Lipschitz goal.**

If for each time `t`, the operator `s ↦ A t s` is differentiable on a convex set
of sections with Fréchet derivative bounded by `K`, then the chart Lipschitz goal
holds. This isolates the hard PDE estimate (the derivative bound) from the soft
Picard–Lindelöf machinery. -/
theorem ricciDeTurckChartOperatorLipschitz_of_fderiv_bounded
    {CSS : Type*} [NormedAddCommGroup CSS] [NormedSpace ℝ CSS] [CompleteSpace CSS]
    (A : ℝ → CSS → CSS) (K : ℝ≥0)
    (hdiff : ∀ t : ℝ, Differentiable ℝ (A t))
    (hbound : ∀ t : ℝ, ∀ s : CSS, ‖fderiv ℝ (A t) s‖₊ ≤ K) :
    RicciDeTurckChartOperatorLipschitz A K := by
  intro t
  exact lipschitzWith_of_nnnorm_fderiv_le (hdiff t) (hbound t)

end RicciFlow.AnalyticPDE
