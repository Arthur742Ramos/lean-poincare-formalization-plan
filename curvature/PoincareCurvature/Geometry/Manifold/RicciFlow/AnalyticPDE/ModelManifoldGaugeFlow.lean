import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.GaugeFlowAssembly
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceManifold
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.FieldJetContDiff

/-!
# Model-manifold raw `C³` gauge-flow existence from field-jet data (roadmap point 4, Item 2)

The compact-manifold gauge-flow constructor of Item 2 consumes its flow data through
`GaugeReduction/GaugeFlowAssembly.gaugeFlow_of_inverse_flow`, whose reduction target is a pair of
mutually inverse, spatially-`ContMDiff I I 3` time-slice maps `F`, `G : ℝ → M → M` together with the
anchoring `F t₀ = id` and the manifold ODE derivative equation
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun τ ↦ F τ x) s t ((1).smulRight (X t (F t x)))`.

The Banach → manifold smooth-dependence tower (`AnalyticPDE/SmoothDependenceCk`,
`AnalyticPDE/FlowDiffeomorphism`, `AnalyticPDE/SmoothDependenceManifold`) supplies **exactly** this
data for the **model manifold** `M = E` (`𝓘(ℝ, E)`), where a time-dependent vector field
`X : CovariantDerivative.TimeDependentVectorField 𝓘(ℝ, E) E` is definitionally an ordinary field
`ℝ → E → E` (`TangentSpace 𝓘(ℝ, E) x = E`).  This module closes the last mile of that connection:
from the `C^{3,1}` field jet of `v` alone (globally Lipschitz `v`, plus the Fréchet jet `Dv`, `D²v`,
`D³v` with the standard global Lipschitz/continuity/compatibility bounds), the raw `C³` DeTurck
gauge-flow structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` is **inhabited** for the model manifold
`E`, on an *arbitrary* time set `s`.

Because Item 2's general-manifold smooth-dependence theorem is proved chart-by-chart with each chart
*the model space `E`*, this model-manifold gauge-flow existence is the load-bearing chart-level core
of the general compact-manifold constructor: the remaining work upstream is the chart-patching that
lives in the heavy `GaugeReduction/ModelGaugeFlowODE.lean` / `Diffeomorph3FlowExistence.lean`, not the
per-chart flow existence, which is now available here.

No new PDE or analytic content: a pure assembly of the already-proved model-manifold gauge-data
bundle `exists_flow_contMDiff_three_gaugeData` into the consumer `gaugeFlow_of_inverse_flow`.  Nothing
here touches the heavy gauge files.

* `exists_diffeomorph3GaugeFlowOn_of_field_jet` — the model-manifold (`M = E`) instance of Item 2's
  raw `C³` gauge-flow existence target, from field-jet data alone.

Proved sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Model-manifold raw `C³` gauge-flow existence from field-jet data.**  For the model manifold
`M = E` (`𝓘(ℝ, E)`), a time-dependent vector field is definitionally an ordinary field
`v : ℝ → E → E`.  From its `C^{3,1}` jet — `v` globally `K`-Lipschitz and time-continuous, with the
everywhere Fréchet derivatives `Dv`, `D²v` (in both continuous-linear `D2vc` and multilinear `D2vm`
guises), `D³v` (`D3vm`/`D3v`), all globally Lipschitz / jointly continuous, and the standard
compatibility `D2vc = curry2 (D2vm)`, `D3vm = (D3v).curryLeft` — the raw `C³` DeTurck gauge-flow
structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` is inhabited on an arbitrary time set `s`.

The flow data is the model-manifold gauge-data bundle `exists_flow_contMDiff_three_gaugeData`: the
forward flow map `F t = (x ↦ Φ x t)` and its per-time smooth inverse `G t` supply the mutually
inverse `ContMDiff I I 3` time slices, `Φ · t₀ = id` the anchoring, and the manifold integral-curve
derivative the ODE equation (weakened to the within-set form via `HasMFDerivAt.hasMFDerivWithinAt`).
This is the model-manifold instance — hence the chart-level core — of Item 2's compact-manifold
gauge-flow existence target. -/
theorem exists_diffeomorph3GaugeFlowOn_of_field_jet
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ} (s : Set ℝ)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ N : ℝ≥0}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ)
    (hD2vcc : Continuous fun p : ℝ × E => D2vc p.1 p.2)
    (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD2vmlip : ∀ s, LipschitzWith N (D2vm s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ)
    (hD3vmc : Continuous fun p : ℝ × E => D3vm p.1 p.2)
    (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hD3vc : Continuous fun p : ℝ × E => D3v p.1 p.2)
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  obtain ⟨Φ, h0, hderiv, hdiff⟩ := exists_flow_contMDiff_three_gaugeData
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  choose G hL hR hcdF hcdψ using hdiff
  exact PoincareCurvature.GaugeFlowAssembly.gaugeFlow_of_inverse_flow
    (I := 𝓘(ℝ, E)) (M := E) (X := v) (s := s) (t₀ := t₀)
    (fun t x => Φ x t) G hL hR hcdF hcdψ h0
    (fun t _ x => (hderiv x t).hasMFDerivWithinAt)

/-- **Model-manifold `C³` flow: first-class `Diffeomorph` family together with the ODE equation.**
From the `C^{3,1}` field jet of `v` alone there is a *single* flow family `Φ` on the model manifold
`𝓘(ℝ, E)` that simultaneously

* anchors, `Φ z t₀ = z`;
* satisfies the manifold integral-curve ODE derivative equation at every time,
  `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ ↦ Φ z τ) t ((1).smulRight (v t (Φ z t)))`;
* is, for every `t`, the coercion of a genuine bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`.

This threads a single `Φ` through both `exists_flow_diffeomorph_three` (which exposes the `Diffeomorph`
family but discards the flow equation) and the gauge-data bundle (which exposes the ODE but only an
unbundled inverse), giving the exact per-chart export the general compact-manifold lift transports:
in each chart, a first-class `C³` self-diffeomorphism family that *is* the flow of the (chart-local)
field.  A pure assembly of `exists_flow_contMDiff_three_gaugeData`. -/
theorem exists_flow_diffeomorph_three_hasMFDerivAt [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ N : ℝ≥0}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ)
    (hD2vcc : Continuous fun p : ℝ × E => D2vc p.1 p.2)
    (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD2vmlip : ∀ s, LipschitzWith N (D2vm s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ)
    (hD3vmc : Continuous fun p : ℝ × E => D3vm p.1 p.2)
    (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hD3vc : Continuous fun p : ℝ × E => D3v p.1 p.2)
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧
      (∀ z t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => Φ z τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (Φ z t)))) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3, ∀ z, F z = Φ z t := by
  obtain ⟨Φ, h0, hderiv, hdiff⟩ := exists_flow_contMDiff_three_gaugeData
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  refine ⟨Φ, h0, hderiv, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ := hdiff t
  exact ⟨⟨⟨fun z => Φ z t, ψ, hL, hR⟩, hcdΦ, hcdψ⟩, fun z => rfl⟩

/-- **Model-manifold raw `C³` gauge-flow existence from a single joint-`ContDiff` field.**
Same conclusion as `exists_diffeomorph3GaugeFlowOn_of_field_jet` — the raw `C³` DeTurck gauge-flow
structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` on the model manifold `M = E` (`𝓘(ℝ, E)`) — but with
the entire `C^{3,1}` Fréchet jet (`Dv`, `D²v` in both `curry`/multilinear guises, `D³v`) and its
pointwise-`HasFDerivAt`/joint-continuity/compatibility obligations *discharged from a single
`ContDiff ℝ n (Function.uncurry v)` hypothesis* (`3 ≤ n`).  Only the honest top-order controls remain
as hypotheses: `v` globally `K`-Lipschitz and time-continuous, plus the four Lipschitz bounds on the
first/second/third spatial-derivative fields (`hDvlip`/`hD2vclip`/`hD2vmlip`/`hD3vmlip`/`hD3vlip`),
matching the tower's own `C³` interface (expressing the top-order bounds as fourth-derivative bounds
would need a further multilinear jet).

This is the `ContDiff`-packaged form of the model-manifold gauge-flow existence — the chart-level core
of Item 2 stated behind the single smoothness hypothesis the compact-manifold gauge-flow lift will
supply from a `ContDiff` DeTurck gauge vector field, mirroring the `_of_contDiff` field-jet extraction
API (`exists_flow_contMDiff_three_diffeomorph_of_contDiff`). A pure assembly: the jet extraction of
`FieldJetContDiff` fed into `exists_diffeomorph3GaugeFlowOn_of_field_jet`. -/
theorem exists_diffeomorph3GaugeFlowOn_of_contDiff
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {n : WithTop ℕ∞} (s : Set ℝ)
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact exists_diffeomorph3GaugeFlowOn_of_field_jet (t₀ := t₀) s
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    hDvlip
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn2 s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn2)
    hD2vclip
    hD2vmlip
    (fun s ξ => hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn)
    hD3vmlip
    (continuous_iteratedFDeriv_three_of_contDiff_uncurry h hn)
    hD3vlip
    (fun s ξ => fderiv_fderiv_eq_curry2_iteratedFDeriv_two (v s) ξ)
    (fun s ξ => fderiv_iteratedFDeriv_two_eq_curryLeft (v s) ξ)

/-- **Model-manifold `C³` flow family + ODE equation from a single joint-`ContDiff` field.**
The `ContDiff`-packaged form of `exists_flow_diffeomorph_three_hasMFDerivAt`: from a single
`ContDiff ℝ n (Function.uncurry v)` hypothesis (`3 ≤ n`) plus the honest top-order Lipschitz controls,
there is a *single* flow family `Φ` on the model manifold `𝓘(ℝ, E)` that simultaneously anchors
(`Φ z t₀ = z`), solves the manifold integral-curve ODE derivative equation at every time, and is —
for every `t` — the coercion of a genuine bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`.  The entire
`C^{3,1}` Fréchet jet and its `HasFDerivAt`/joint-continuity/compatibility obligations are discharged
from the one smoothness hypothesis.

This is the second documented per-chart export the general compact-manifold lift transports (a
first-class `C³` self-diffeomorphism family that *is* the flow of the chart-local field), now stated
behind the single `ContDiff` hypothesis, completing the `_of_contDiff` entry points to both
model-manifold gauge-flow exports.  A pure assembly of the `FieldJetContDiff` jet extraction fed into
`exists_flow_diffeomorph_three_hasMFDerivAt`. -/
theorem exists_flow_diffeomorph_three_hasMFDerivAt_of_contDiff
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {n : WithTop ℕ∞}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧
      (∀ z t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => Φ z τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (Φ z t)))) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3, ∀ z, F z = Φ z t := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact exists_flow_diffeomorph_three_hasMFDerivAt (t₀ := t₀)
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    hDvlip
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn2 s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn2)
    hD2vclip
    hD2vmlip
    (fun s ξ => hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn)
    hD3vmlip
    (continuous_iteratedFDeriv_three_of_contDiff_uncurry h hn)
    hD3vlip
    (fun s ξ => fderiv_fderiv_eq_curry2_iteratedFDeriv_two (v s) ξ)
    (fun s ξ => fderiv_iteratedFDeriv_two_eq_curryLeft (v s) ξ)

/-!
## Compact-support jet bounds for the bump-globalised gauge field (Item 2 GAP 1)

The compact-manifold lift feeds `exists_diffeomorph3GaugeFlowOn_of_contDiff` a field
`v : ℝ → E → E` obtained by bump-cutting the chart pushforward field to a globally-`C^{3,1}`,
compactly-supported representative.  Its hypotheses demand *uniform-in-time* Lipschitz bounds on the
spatial-derivative fields `Dⁱ (v s)`.  These reduce to the following two purely model-space facts
about a jointly-`ContDiff`, compactly-supported two-variable function `F = uncurry v`:

* the `n`-th iterated derivative of a time slice `y ↦ F (s, y)` is dominated in norm by the full
  `n`-th iterated derivative of `F` at `(s, y)` (`norm_iteratedFDeriv_prodMk_left_le`); and
* consequently the slice iterated derivatives are **uniformly bounded** in `(s, y)` whenever `F` has
  compact support (`exists_bound_iteratedFDeriv_prodMk_left`).

Both are the reusable analytic core supplying the uniform jet bounds of the globalised field; no
gauge-flow content.
-/

/-- **Norm slice bound for iterated derivatives of a two-variable function.**  The `n`-th iterated
Fréchet derivative of the `s`-slice `y ↦ F (s, y)` of `F : ℝ × E → G` is bounded in norm by the full
`n`-th iterated derivative of `F` at `(s, y)`.

The slice factors as `(fun p ↦ F (p + (s, 0))) ∘ inr` with `inr : E →L[ℝ] ℝ × E` the norm-`≤ 1`
inclusion `y ↦ (0, y)`; iterated differentiation of that composition
(`ContinuousLinearMap.iteratedFDeriv_comp_right`) precomposes the full iterated derivative with `inr`
in every slot, and the constant shift moves the base point from `inr x` to `(s, x)`
(`iteratedFDeriv_comp_add_right`).  Taking norms with `‖inr‖ ≤ 1` gives the bound. -/
theorem norm_iteratedFDeriv_prodMk_left_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F)
    {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) (s : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => F (s, y)) x‖ ≤ ‖iteratedFDeriv ℝ n F (s, x)‖ := by
  have hcomp : (fun y => F (s, y))
      = (fun p : ℝ × E => F (p + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ E : E → ℝ × E) := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      zero_add, add_zero]
  have hG : ContDiff ℝ N (fun p : ℝ × E => F (p + (s, 0))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ ℝ E) hG x hn]
  have hshift : iteratedFDeriv ℝ n (fun p : ℝ × E => F (p + (s, 0)))
        (ContinuousLinearMap.inr ℝ ℝ E x)
      = iteratedFDeriv ℝ n F ((s, x) : ℝ × E) := by
    rw [iteratedFDeriv_comp_add_right n (s, 0) (ContinuousLinearMap.inr ℝ ℝ E x)]
    congr 1
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
  rw [hshift]
  calc ‖(iteratedFDeriv ℝ n F ((s, x) : ℝ × E)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖
          * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_one (fun i _ => norm_nonneg _)
          (fun i _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)
    _ = ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖ := mul_one _

/-- **Uniform bound on the slice iterated derivatives of a compactly-supported field.**  If
`F : ℝ × E → G` is jointly `C^N` with compact support then, for each `n ≤ N`, the `n`-th iterated
derivative of every time slice `y ↦ F (s, y)` is uniformly bounded in `(s, y)`.  Combines the slice
bound `norm_iteratedFDeriv_prodMk_left_le` with the global bound on `iteratedFDeriv ℝ n F` obtained
from compact support (`HasCompactSupport.iteratedFDeriv` + `HasCompactSupport.exists_bound_of_continuous`).
This is the uniform-in-time control the globalised gauge field's jet Lipschitz bounds are built on. -/
theorem exists_bound_iteratedFDeriv_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) :
    ∃ C : ℝ, ∀ (s : ℝ) (x : E), ‖iteratedFDeriv ℝ n (fun y => F (s, y)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hcs.iteratedFDeriv (𝕜 := ℝ) n).exists_bound_of_continuous
    (hF.continuous_iteratedFDeriv hn)
  exact ⟨C, fun s x => (norm_iteratedFDeriv_prodMk_left_le hF hn s x).trans (hC (s, x))⟩

/-- **Uniform-in-time Lipschitz bound on the slice iterated derivatives of a compactly-supported
field.**  If `F : ℝ × E → G` is jointly `C^N` with compact support and `n + 1 ≤ N`, then there is a
single Lipschitz constant `C` such that the `n`-th iterated derivative of *every* time slice
`y ↦ F (s, y)` is `C`-Lipschitz.

This is the exact shape of the uniform derivative-field Lipschitz hypotheses
(`hD2vmlip`/`hD3vlip`) consumed by `exists_diffeomorph3GaugeFlowOn_of_contDiff`: the constant is
obtained from the uniform order-`(n+1)` bound `exists_bound_iteratedFDeriv_prodMk_left`, converted to
a Lipschitz estimate via `norm_fderiv_iteratedFDeriv` (`‖fderiv (Dⁿf)‖ = ‖Dⁿ⁺¹f‖`) and
`lipschitzWith_of_nnnorm_fderiv_le`. -/
theorem exists_lipschitzWith_iteratedFDeriv_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N) :
    ∃ C : ℝ≥0, ∀ s : ℝ, LipschitzWith C (iteratedFDeriv ℝ n (fun y => F (s, y))) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_iteratedFDeriv_prodMk_left (n := n + 1) hF hcs hn
  refine ⟨⟨max C₀ 0, le_max_right _ _⟩, fun s => ?_⟩
  have hslice : ContDiff ℝ N (fun y => F (s, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hle : (1 : WithTop ℕ∞) + (n : WithTop ℕ∞) ≤ N := by
    have h1 : (1 : WithTop ℕ∞) + (n : WithTop ℕ∞) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
      push_cast; exact add_comm _ _
    rw [h1]; exact hn
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((hslice.iteratedFDeriv_right (m := 1) hle).differentiable one_ne_zero) (fun x => ?_)
  have hb : ‖fderiv ℝ (iteratedFDeriv ℝ n (fun y => F (s, y))) x‖ ≤ max C₀ 0 := by
    rw [norm_fderiv_iteratedFDeriv]
    exact (hC₀ s x).trans (le_max_left _ _)
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
  exact hb

/-- **Uniform-in-time Lipschitz bound on the time slices themselves.**  If `F : ℝ × E → G` is jointly
`C^N` with compact support and `1 ≤ N`, there is a single Lipschitz constant `C` with every time slice
`y ↦ F (s, y)` being `C`-Lipschitz.  This is the `hv` datum of `exists_diffeomorph3GaugeFlowOn_of_contDiff`
(the field itself uniformly Lipschitz).  Proof: the uniform order-`1` slice bound
`exists_bound_iteratedFDeriv_prodMk_left` combined with `norm_iteratedFDeriv_one`
(`‖D¹f‖ = ‖fderiv f‖`) and `lipschitzWith_of_nnnorm_fderiv_le`. -/
theorem exists_lipschitzWith_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    (hN : 1 ≤ N) :
    ∃ C : ℝ≥0, ∀ s : ℝ, LipschitzWith C (fun y => F (s, y)) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_iteratedFDeriv_prodMk_left (n := 1) hF hcs (by exact_mod_cast hN)
  have hN0 : N ≠ 0 := by rintro rfl; exact absurd hN (by norm_num)
  refine ⟨⟨max C₀ 0, le_max_right _ _⟩, fun s => ?_⟩
  have hslice : ContDiff ℝ N (fun y => F (s, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  refine lipschitzWith_of_nnnorm_fderiv_le (hslice.differentiable hN0) (fun x => ?_)
  have hb : ‖fderiv ℝ (fun y => F (s, y)) x‖ ≤ max C₀ 0 := by
    rw [← norm_iteratedFDeriv_one]
    exact (hC₀ s x).trans (le_max_left _ _)
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
  exact hb

/-- **Lipschitz transport across the `fderiv`↔iterated-derivative currying isometry.**  Since
`fderiv ℝ (iteratedFDeriv ℝ n f) = e ∘ iteratedFDeriv ℝ (n+1) f` with `e` the currying
`LinearIsometryEquiv` (`fderiv_iteratedFDeriv`), a Lipschitz bound on the `(n+1)`-st iterated
derivative transports to the same bound on `fderiv` of the `n`-th iterated derivative.  This turns the
`iteratedFDeriv`-shaped bounds of `exists_lipschitzWith_iteratedFDeriv_prodMk_left` into the
`fderiv (iteratedFDeriv …)`-shaped hypothesis `hD3vmlip` of `exists_diffeomorph3GaugeFlowOn_of_contDiff`. -/
theorem lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {C : ℝ≥0} {n : ℕ}
    (h : LipschitzWith C (iteratedFDeriv ℝ (n + 1) f)) :
    LipschitzWith C (fderiv ℝ (iteratedFDeriv ℝ n f)) := by
  rw [fderiv_iteratedFDeriv]
  exact (Isometry.lipschitzWith_iff C
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).isometry).mpr h

/-- **Model-manifold raw `C³` gauge-flow existence from a compactly-supported `C^N` field (`N ≥ 4`).**
The bump-globalised gauge field is a jointly-`ContDiff`, compactly-supported `v : ℝ → E → E`; from that
data *alone* (no separately-supplied jet Lipschitz constants) the raw `C³` DeTurck gauge-flow structure
`Diffeomorph3GaugeFlowOn (X := v) s t₀` is inhabited on the model manifold `E`.

Every uniform-in-time jet Lipschitz hypothesis of `exists_diffeomorph3GaugeFlowOn_of_contDiff` is
discharged from compact support:
* `hv` from `exists_lipschitzWith_prodMk_left`;
* `hD2vmlip` / `hD3vlip` from `exists_lipschitzWith_iteratedFDeriv_prodMk_left` (orders `2`, `3`);
* `hD3vmlip` by transporting the order-`3` bound through the currying isometry
  (`lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ`) — with the *same*
  constant `M₃` as `hD3vlip`;
* the nested-`fderiv` bounds `hDvlip` / `hD2vclip` through the two-fold curry `curry2`, which is
  norm-nonexpansive (`norm_curry2_le`) and linear (`curry2_sub`), hence `1`-Lipschitz, combined with
  the uniform order-`2` slice bound.

This is the compact-support entry point the general compact-manifold gauge-flow lift consumes after
bump-cutting the chart pushforward field to a globally-`C^{3,1}` representative. -/
theorem exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {t₀ : ℝ} {N : WithTop ℕ∞} (s : Set ℝ)
    (hF : ContDiff ℝ N (Function.uncurry v))
    (hcs : HasCompactSupport (Function.uncurry v)) (hN : 4 ≤ N) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  have hsl : ∀ σ : ℝ, (fun y => Function.uncurry v (σ, y)) = v σ := fun _ => rfl
  have hslc : ∀ σ : ℝ, ContDiff ℝ N (fun y => Function.uncurry v (σ, y)) :=
    fun _ => hF.comp (contDiff_const.prodMk contDiff_id)
  have hN1 : (1 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  have hN2 : (2 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  have hN3 : (3 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  obtain ⟨K, hK⟩ := exists_lipschitzWith_prodMk_left hF hcs hN1
  obtain ⟨Nc, hNc⟩ :=
    exists_lipschitzWith_iteratedFDeriv_prodMk_left (n := 2) hF hcs (by exact_mod_cast hN3)
  obtain ⟨M₃, hM₃⟩ :=
    exists_lipschitzWith_iteratedFDeriv_prodMk_left (n := 3) hF hcs (by exact_mod_cast hN)
  obtain ⟨C₂, hC₂⟩ :=
    exists_bound_iteratedFDeriv_prodMk_left (n := 2) hF hcs (by exact_mod_cast hN2)
  have hcurry2 : LipschitzWith 1 (curry2 (E := E)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro X Y
    rw [dist_eq_norm, dist_eq_norm, ← curry2_sub]
    simpa using norm_curry2_le (X - Y)
  refine exists_diffeomorph3GaugeFlowOn_of_contDiff (K := K) (L := ⟨max C₂ 0, le_max_right _ _⟩)
    (M₂ := 1 * Nc) (N := Nc) (M₃ := M₃) s hF hN3
    ?hv ?hvc ?hDvlip ?hD2vclip ?hD2vmlip ?hD3vmlip ?hD3vlip
  case hv => intro σ; rw [← hsl σ]; exact hK σ
  case hvc =>
    intro x
    exact hF.continuous.comp (continuous_id.prodMk continuous_const)
  case hDvlip =>
    intro σ
    rw [← hsl σ]
    refine lipschitzWith_of_nnnorm_fderiv_le (C := ⟨max C₂ 0, le_max_right _ _⟩)
      (((hslc σ).fderiv_right (m := 1) hN2).differentiable one_ne_zero) (fun x => ?_)
    rw [fderiv_fderiv_eq_curry2_iteratedFDeriv_two, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
    calc ‖curry2 (iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) x)‖
        ≤ ‖iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) x‖ := norm_curry2_le _
      _ ≤ C₂ := hC₂ σ x
      _ ≤ max C₂ 0 := le_max_left _ _
  case hD2vclip =>
    intro σ
    rw [← hsl σ]
    have hmap : fderiv ℝ (fderiv ℝ (fun y => Function.uncurry v (σ, y)))
        = curry2 ∘ iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) := by
      funext x; exact fderiv_fderiv_eq_curry2_iteratedFDeriv_two _ x
    rw [hmap]
    exact hcurry2.comp (hNc σ)
  case hD2vmlip => intro σ; rw [← hsl σ]; exact hNc σ
  case hD3vmlip =>
    intro σ
    rw [← hsl σ]
    exact lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ (n := 2) (hM₃ σ)
  case hD3vlip => intro σ; rw [← hsl σ]; exact hM₃ σ

/-- **A cutoff multiple of a locally-`C^n` field is globally `C^n` with compact support.**  If `w` is
`C^n` on an open set `U`, and `χ` is a globally-`C^n`, compactly-supported cutoff with `tsupport χ ⊆ U`,
then `fun x ↦ χ x • w x` is globally `C^n` and compactly supported.  This is the extension-by-zero step
of the bump-globalisation: at a point of `tsupport χ ⊆ U` both factors are `C^n` (`ContDiffOn.contDiffAt`
on the open `U`); off `tsupport χ` the product vanishes on the neighbourhood `(tsupport χ)ᶜ`
(`image_eq_zero_of_notMem_tsupport`).  It globalises the chart-local pushforward field to a field defined
and regular on all of the model space with compact support, the exact input shape of
`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport`. -/
theorem contDiff_and_hasCompactSupport_cutoff_smul
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set H} {w : H → V} {χ : H → ℝ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ n w U)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    ContDiff ℝ n (fun x => χ x • w x) ∧ HasCompactSupport (fun x => χ x • w x) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x => ?_), ?_⟩
  · by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hw.contDiffAt (hU.mem_nhds (hsub hx)))
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · refine hχc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun hχx => hx (by rw [hχx, zero_smul])

/-- **Bump-globalised chart pushforward field: globally `C^N` with compact support.**  Combining the
joint-in-time field regularity `contDiffOn_prod_chartPushforwardField` with the extension-by-zero cutoff
product `contDiff_and_hasCompactSupport_cutoff_smul`: given joint `C^N` regularity of the time-dependent
tangent-bundle section `(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source`, and a globally-`C^N`,
compactly-supported cutoff `χ : ℝ × E → ℝ` with `tsupport χ ⊆ ℝ ×ˢ (extChartAt I p).target`, the cutoff
multiple `(τ, q) ↦ χ (τ, q) • chartPushforwardField I X p τ q` is globally `ContDiff ℝ N` on the model
product `ℝ × E` and has compact support.  The chart target is open
(`isOpen_extChartAt_target`, using `I.Boundaryless`), so the field is `C^N` on the open tube where the
cutoff lives.  This is GAP-1 step (iii): the compactly-supported `C^N` field
`v := Function.curry (χ • chartPushforwardField …)` whose `(ContDiff, HasCompactSupport)` pair is exactly
the input consumed by `exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` to produce the model
gauge flow `Ψ`. -/
theorem contDiff_hasCompactSupport_cutoff_chartPushforwardField
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {χ : ℝ × E → ℝ} (hχ : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target) :
    ContDiff ℝ N (fun r : ℝ × E => χ r •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p r.1 r.2) ∧
      HasCompactSupport (fun r : ℝ × E => χ r •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p r.1 r.2) :=
  contDiff_and_hasCompactSupport_cutoff_smul
    (isOpen_univ.prod (isOpen_extChartAt_target p))
    (PoincareCurvature.GaugeFlowAssembly.contDiffOn_prod_chartPushforwardField hX) hχ hχc hsub

/-- **Model gauge flow `Ψ` from a jointly-`C^N` section plus a chart-target cutoff (`N ≥ 4`).**  The
capstone of GAP-1 steps (i)–(iv): from joint `C^N` regularity of the time-dependent tangent-bundle
section `(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source` and a globally-`C^N`, compactly-supported
cutoff `χ` with `tsupport χ ⊆ ℝ ×ˢ (extChartAt I p).target`, the bump-globalised chart pushforward field
`v := fun τ q ↦ χ (τ, q) • chartPushforwardField I X p τ q` is a compactly-supported `C^N` field on the
model manifold `E`, and hence (`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport`) inhabits
the raw `C³` DeTurck gauge-flow structure `Diffeomorph3GaugeFlowOn (X := v) s t₀`.  This is the model
comparison flow `Ψ` used by `contMDiffOn_of_extChartAt_conjugation'` to transfer spatial `C³` regularity
to the compact manifold `M` (step (v), `hslicesC3`); only the construction of the cutoff `χ` around the
compact trajectory (step (ii)) remains between this and the compact-manifold gauge-flow lift. -/
theorem exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {χ : ℝ × E → ℝ} (hχ : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hN : 4 ≤ N) (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀) := by
  obtain ⟨hF, hcs⟩ :=
    contDiff_hasCompactSupport_cutoff_chartPushforwardField hX hχ hχc hsub
  exact exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport s hF hcs hN

/-- **Smooth cutoff equal to `1` near a compact set, supported in an open set (GAP-1 step (ii)).**
On a finite-dimensional real normed space `F`, for a compact set `K` inside an open set `U`, there is
a globally-`C^n` function `χ : F → ℝ` that
  * has compact support,
  * has `tsupport χ ⊆ U`,
  * is identically `1` on a neighbourhood of `K` (`∀ᶠ x in 𝓝ˢ K, χ x = 1`), and
  * takes values in `[0, 1]`.

This is the cutoff datum consumed by `exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`:
applied with `F := ℝ × E`, `U := Set.univ ×ˢ (extChartAt I p).target` (open) and `K` the compact
trajectory window, it supplies the `hχ`/`hχc`/`hsub` hypotheses of that capstone, while the extra
`χ ≡ 1` near `K` clause is what makes the bump-cut field agree with the un-cut chart pushforward field
on the orbit (the input to the step-(v) integral-curve comparison
`extChartAt_comp_eqOn_of_lipschitzOnWith`).

Construction: interpose (`exists_compact_between`, using local compactness) a compact `L` with
`K ⊆ interior L ⊆ L ⊆ U`; view `F` as the model manifold `𝓘(ℝ, F)` and apply the manifold cutoff
`exists_contMDiffMap_one_nhds_of_subset_interior` with `s := K`, `t := L` to get a smooth `f` equal to
`1` near `K` and vanishing off `L`; `support f ⊆ L` (compact) gives `HasCompactSupport` and
`tsupport f ⊆ L ⊆ U`; the `ContMDiff → ContDiff` transfer is `contMDiff_iff_contDiff`. -/
theorem exists_contDiff_cutoff_one_nhdsSet_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ∞} {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : F → ℝ, ContDiff ℝ n χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, h1, h0, hIcc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, F) hK.isClosed hKL (n := n)
  have hsupp : Function.support (f : F → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (h0 x hxL)
  have hcs : HasCompactSupport (f : F → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hLc hsupp
  refine ⟨(f : F → ℝ), contMDiff_iff_contDiff.mp f.contMDiff, hcs, ?_, h1, hIcc⟩
  calc tsupport (f : F → ℝ) = closure (Function.support (f : F → ℝ)) := rfl
    _ ⊆ closure L := closure_mono hsupp
    _ = L := hLc.isClosed.closure_eq
    _ ⊆ U := hLU

/-- **Model gauge flow `Ψ` from an internally-constructed chart-target cutoff around a compact orbit
window (`4 ≤ n`).**  Removes the "cutoff assumed" residual of
`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`: given only the joint `C^n` section
regularity `hX` and a *compact* trajectory window `K ⊆ ℝ ×ˢ (extChartAt I p).target`, this constructs
the cutoff `χ` itself (`exists_contDiff_cutoff_one_nhdsSet_of_isCompact` on the finite-dimensional
model `ℝ × E`, with `U := ℝ ×ˢ (extChartAt I p).target` open via `isOpen_extChartAt_target`) and hands
back both

  * the guarantee `∀ᶠ r in 𝓝ˢ K, χ r = 1` — so where `χ ≡ 1` the bump-cut field
    `(τ, q) ↦ χ (τ, q) • chartPushforwardField I X p τ q` agrees with the un-cut chart pushforward
    field, the hypothesis the step-(v) integral-curve comparison
    `extChartAt_comp_eqOn_of_lipschitzOnWith` consumes on the orbit; and
  * the model comparison flow `Ψ`, i.e. `Nonempty (Diffeomorph3GaugeFlowOn … s t₀)` for that cut field
    (`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`).

This is GAP-1 steps (ii)+(iv) packaged for the compact-manifold spatial-`C³` transfer (step (v),
`hslicesC3`); the remaining residual is supplying `hX` from the actual gauge field `X`. -/
theorem exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {n : ℕ∞} [IsManifold I n M]
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {K : Set (ℝ × E)} (hK : IsCompact K)
    (hKU : K ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hn : 4 ≤ n) (s : Set ℝ) (t₀ : ℝ) :
    ∃ χ : ℝ × E → ℝ, (∀ᶠ r in 𝓝ˢ K, χ r = 1) ∧
      Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
        (X := fun τ q => χ (τ, q) •
          PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀) := by
  obtain ⟨χ, hχC, hχcs, hχsub, hχ1, _hχIcc⟩ :=
    exists_contDiff_cutoff_one_nhdsSet_of_isCompact (n := n) hK
      (isOpen_univ.prod (isOpen_extChartAt_target p)) hKU
  exact ⟨χ, hχ1,
    exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField hX hχC hχcs hχsub
      (by simpa using WithTop.coe_le_coe.mpr hn) s t₀⟩

/-- **Model gauge-flow slices are `ContDiff ℝ 3` (the step-(v) `hΨ` datum).**  On the model manifold
`E`, every time slice `G.maps3 t : E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E` of a raw `C³` gauge-flow witness is a
bundled `C³` self-diffeomorphism, so its underlying map is `ContDiff ℝ 3` (`Diffeomorph.contMDiff`
followed by the model-space `contMDiff_iff_contDiff`).  This is exactly the `hΨ : ContDiff ℝ 3 Ψ`
hypothesis consumed by the chart-conjugation spatial-`C³` transfer
`GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` when the comparison flow `Ψ := G.maps3 t`
is the model gauge flow produced by `exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`
(GAP-1 step (v)). -/
theorem contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {Xc : CovariantDerivative.TimeDependentVectorField (I := 𝓘(ℝ, E)) (M := E)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) Xc s t₀) (t : ℝ) :
    ContDiff ℝ 3 (G.maps3 t : E → E) :=
  contMDiff_iff_contDiff.mp (G.maps3 t).contMDiff

/-- **Model gauge-flow curves are integral curves of the field (ordinary within-set derivative).**  On
the model manifold `E`, the manifold ODE readout `Diffeomorph3GaugeFlowOn.hasMFDerivWithinAt` becomes a
genuine `HasDerivWithinAt`: for a fixed base point `q`, the flow curve `τ ↦ G.maps3 τ q` has, at every
time `t ∈ s`, derivative `Xc t (G.maps3 t q)` (the field value at the current position).  The manifold
Fréchet derivative `(1).smulRight (Xc t (G.maps3 t q))` transfers to the ordinary derivative via the
model-space `HasMFDerivWithinAt.hasFDerivWithinAt` and `smulRight_one_eq_toSpanSingleton`.

This is the `hg'` datum consumed by `GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith`: with
`g := τ ↦ G.maps3 τ q` the model comparison curve, on the region where the cutoff `χ ≡ 1` the field
`Xc = χ • chartPushforwardField` reduces to `chartPushforwardField`, so this readout supplies the
integral-curve hypothesis of the step-(v) temporal uniqueness comparison. -/
theorem hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {Xc : CovariantDerivative.TimeDependentVectorField (I := 𝓘(ℝ, E)) (M := E)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) Xc s t₀)
    {t : ℝ} (ht : t ∈ s) (q : E) :
    HasDerivWithinAt (fun τ : ℝ => (G.maps3 τ) q) (Xc t ((G.maps3 t) q)) s t := by
  have hfd := (G.hasMFDerivWithinAt ht q).hasFDerivWithinAt
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] at hfd
  exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr hfd

/-- **The `hg'` datum of the step-(v) glue: the model comparison curve is a full `HasDerivAt` integral
curve of the *uncut* `chartPushforwardField` wherever the cutoff `χ ≡ 1`.**  For the model gauge flow
`G` of the cut field `fun τ q ↦ χ (τ, q) • chartPushforwardField I X p τ q` produced by
`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField` /
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`, on an open time window
(`hs : s ∈ 𝓝 t`) and at a base point `q` whose current position `(G.maps3 t) q` lies in the region where
the cutoff equals one (`hχ`), the within-set flow-ODE readout
`hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn` — which carries the *cut* field value
`χ (t, (G.maps3 t) q) • chartPushforwardField …` — collapses to the un-cut field
(`1 • chartPushforwardField = chartPushforwardField`, `one_smul`) and upgrades from `HasDerivWithinAt` to
`HasDerivAt` via the window neighbourhood (`HasDerivWithinAt.hasDerivAt`).

This is exactly the shape of the
`hg' : ∀ t ∈ Set.Ioo a b, HasDerivAt g (chartPushforwardField I X p t (g t)) t` hypothesis consumed by
`GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith`, with the model comparison curve
`g := fun τ ↦ (G.maps3 τ) q`.  The `χ ≡ 1` fact `hχ` is the pointwise face of the orbit-containment
control (supplied separately), keeping this readout free of that delicate step. -/
theorem hasDerivAt_maps3_eval_of_cutoff_eqOne
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀)
    {t : ℝ} (hs : s ∈ 𝓝 t) (ht : t ∈ s) (q : E)
    (hχ : χ (t, (G.maps3 t) q) = 1) :
    HasDerivAt (fun τ : ℝ => (G.maps3 τ) q)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)) t := by
  have h := hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn G ht q
  have key : (fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) t ((G.maps3 t) q)
      = PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q) := by
    show χ (t, (G.maps3 t) q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)
        = PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)
    rw [hχ, one_smul]
  rw [← key]
  exact h.hasDerivAt hs

/-- **Step-(v) uniqueness packaging: the manifold-flow chart representation equals the model
`G.maps3`-curve on the window, modulo orbit-containment hypotheses.**  Instantiates the temporal
integral-curve uniqueness comparison
`GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith` with the model gauge flow `G` (of the cut
field `χ • chartPushforwardField`) as the comparison curve `g := fun τ ↦ (G.maps3 τ) (extChartAt I p x)`,
supplying the `hg'` integral-curve hypothesis via `hasDerivAt_maps3_eval_of_cutoff_eqOne` on the region
where `χ ≡ 1`.  Given the raw manifold flow's ODE (`hγ`) and chart-source containment (`hγ_src`), the
time-uniform field Lipschitz bound (`hlip`, e.g. from
`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField`), the orbit-containment facts
(`hχ` — the cutoff equals one along the model curve; `hγ_mem`/`hg_mem` — both curves stay in the state
tube), and agreement at `t₀` (`heq`), the two curves coincide on the whole open window `Set.Ioo a b`.

Evaluated at any interior time `t`, this yields the *spatial conjugation identity*
`extChartAt I p (γ t) = (G.maps3 t) (extChartAt I p x)` — the `hconj` datum fed (together with the model
slice `C³` bound `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn`) to
`GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` to establish the spatial-`C³` regularity
`hslicesC3` of the compact-manifold gauge flow (GAP-1 step (v)).  Only the orbit-containment facts remain
to be discharged; the uniqueness/derivative machinery is now fully assembled. -/
theorem extChartAt_comp_eqOn_maps3_of_cutoff_eqOne
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {sTime : Set ℝ} {t₀' : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
    {γ : ℝ → M} {a b t₀ : ℝ} {K : NNReal} {state : ℝ → Set E} {x : M}
    (hnhds : ∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ)
    (hγ : ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (γ τ))))
    (hγ_src : ∀ τ ∈ Set.Ioo a b, γ τ ∈ (extChartAt I p).source)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hlip : ∀ τ ∈ Set.Ioo a b,
      LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hχ : ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p x)) = 1)
    (hγ_mem : ∀ τ ∈ Set.Ioo a b, extChartAt I p (γ τ) ∈ state τ)
    (hg_mem : ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p x) ∈ state τ)
    (heq : extChartAt I p (γ t₀) = (G.maps3 t₀) (extChartAt I p x)) :
    Set.EqOn (fun τ : ℝ => extChartAt I p (γ τ))
      (fun τ : ℝ => (G.maps3 τ) (extChartAt I p x)) (Set.Ioo a b) := by
  refine PoincareCurvature.GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith
    hγ hγ_src ht₀ hlip ?_ hγ_mem hg_mem heq
  intro τ hτ
  exact hasDerivAt_maps3_eval_of_cutoff_eqOne G (hnhds τ hτ)
    (mem_of_mem_nhds (hnhds τ hτ)) (extChartAt I p x) (hχ τ hτ)

/-- **Step-(v) capstone: the compact-manifold gauge-flow slice is `ContMDiffOn I I 3` on a chart patch,
modulo orbit-containment hypotheses.**  Assembles the full spatial-`C³` transfer of GAP-1 step (v) for a
single time slice `Φ t` on a patch `U ⊆ (chartAt H p).source`.  For each `x ∈ U`, the uniqueness
packaging `extChartAt_comp_eqOn_maps3_of_cutoff_eqOne` identifies the manifold-flow chart representation
`τ ↦ extChartAt I p (Φ τ x)` with the model `G.maps3`-curve `τ ↦ (G.maps3 τ) (extChartAt I p x)` on the
window; evaluated at the interior time `t` this is the spatial conjugation identity
`extChartAt I p (Φ t x) = (G.maps3 t) (extChartAt I p x)`.  Feeding that (as `hconj`) together with the
model slice-`C³` bound `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn G t` (as `hΨ`) into the
chart-conjugation transfer `GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` (single chart `p`
for source and target) yields `ContMDiffOn I I 3 (fun x ↦ Φ t x) U`.

This is exactly the per-patch content of the `hslicesC3` obligation
(`∀ t ∈ Set.Ioo a b, ContMDiff I I 3 (Φ t)`) consumed by
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`: with the compact
manifold covered by finitely many such chart patches and the orbit-containment facts discharged, the
per-patch `ContMDiffOn` glue to global `ContMDiff` closes GAP 1.  The remaining input is purely the
orbit-containment control (the raw flow's chart-source stay `hγ_src`, the cutoff `hχ`, the tube
memberships `hγ_mem`/`hg_mem`); all derivative/uniqueness/`C³`-transfer machinery is assembled here. -/
theorem contMDiffOn_flowSlice_of_cutoff_orbit_control
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {sTime : Set ℝ} {t₀' : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
    (Φ : ℝ → M → M) {U : Set M} {a b t₀ t : ℝ} {K : NNReal} {state : ℝ → Set E}
    (hU : U ⊆ (chartAt H p).source)
    (ht : t ∈ Set.Ioo a b)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hnhds : ∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ)
    (hlip : ∀ τ ∈ Set.Ioo a b,
      LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hγ : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hγ_src : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hχ : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p x)) = 1)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p x) ∈ state τ)
    (heq : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = (G.maps3 t₀) (extChartAt I p x)) :
    ContMDiffOn I I 3 (fun x : M => Φ t x) U := by
  have hFU : Set.MapsTo (fun x : M => Φ t x) U (chartAt H p).source := by
    intro x hx
    have hsrc := hγ_src x hx t ht
    rwa [extChartAt_source] at hsrc
  refine PoincareCurvature.GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'
    (x₀ := p) (y₀ := p) hU
    (contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn G t) hFU ?_
  intro x hx
  have hEqOn := extChartAt_comp_eqOn_maps3_of_cutoff_eqOne (γ := fun σ : ℝ => Φ σ x) G hnhds
    (hγ x hx) (hγ_src x hx) ht₀ hlip (hχ x hx) (hγ_mem x hx) (hg_mem x hx) (heq x hx)
  exact hEqOn ht

/-- **Reducing the `hχ` orbit-containment face of the step-(v) capstone to graph-containment in the
compact cutoff window.**  The cutoff `χ` produced by
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window` satisfies `∀ᶠ r in 𝓝ˢ K, χ r = 1` for
the chosen compact window `K`.  Hence whenever the graph `τ ↦ (τ, g τ)` of the model comparison curve
over the time set lies inside `K`, the cutoff equals one along it — `Filter.Eventually.self_of_nhdsSet`
turns `χ ≡ 1` on a neighbourhood of `K` into `χ ≡ 1` on `K` itself.  This packages the `hχ` hypothesis of
`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne` / `contMDiffOn_flowSlice_of_cutoff_orbit_control` into the
single geometric orbit-containment fact "the model curve's graph stays in the cutoff window", isolating
the remaining delicate GAP-1 step (v) content to that flow-trajectory-confinement estimate. -/
theorem cutoff_eqOne_along_curve_of_graph_subset
    {χ : ℝ × E → ℝ} {g : ℝ → E} {s : Set ℝ} {K : Set (ℝ × E)}
    (hχ : ∀ᶠ r in 𝓝ˢ K, χ r = 1)
    (hgraph : ∀ τ ∈ s, ((τ, g τ) : ℝ × E) ∈ K) :
    ∀ τ ∈ s, χ (τ, g τ) = 1 :=
  fun τ hτ => hχ.self_of_nhdsSet (τ, g τ) (hgraph τ hτ)

/-- **Uniform short-time orbit-graph confinement — the *producing* companion of
`cutoff_eqOne_along_curve_of_graph_subset`.**  For a time-dependent flow map `Ψ : ℝ → E → E` whose
space-time graph map `z ↦ (z.1, Ψ z.1 z.2)` is (jointly) continuous at every *anchored* point `(t₀, q)`
with `q` ranging over a compact initial set `Q`, and an open space-time target `W` containing the whole
anchored graph `{(t₀, Ψ t₀ q) | q ∈ Q}`, there is an open time window `Set.Ioo a b ∋ t₀` on which **every**
orbit graph stays in `W`:
`∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, (τ, Ψ τ q) ∈ W`.

This is precisely the flow-trajectory-confinement mechanism the GAP-1 step-(v) orbit control needs:
applied with `W` the interior of the compact cutoff window `K` (so `W ⊆ K`), it produces the
`graph ⊆ K` hypothesis of `cutoff_eqOne_along_curve_of_graph_subset` *uniformly over a chart patch*,
once the joint continuity of the model gauge flow `(τ, q) ↦ (G.maps3 τ) q` is supplied.  The proof is
the tube-lemma confinement: `IsCompact.eventually_forall_of_forall_eventually` turns the pointwise
"the anchored orbit starts in the open target" facts (each an open-preimage neighbourhood via
`ContinuousAt.preimage_mem_nhds`) into a single *time* neighbourhood of `t₀` valid for all `q ∈ Q`,
whence an honest `Set.Ioo` window through `mem_nhds_iff_exists_Ioo_subset`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt
    {Ψ : ℝ → E → E} {Q : Set E} {W : Set (ℝ × E)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × E) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × E => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × E) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × E) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × E => ((z.1, Ψ z.1 z.2) : ℝ × E)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Joint continuity of the model gauge flow `(τ, q) ↦ (G.maps3 τ) q`.**  On the model manifold `E`,
a raw `C³` gauge-flow witness `G : Diffeomorph3GaugeFlowOn (X := X) Set.univ t₀` of a *uniformly-in-time
globally `K`-Lipschitz* field `X : ℝ → E → E` has jointly continuous total flow map.  Each base curve
`τ ↦ (G.maps3 τ) q` is a genuine global `IsIntegralCurve` of `X` (the within-`Set.univ` manifold ODE
readout `hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn` upgraded via `hasDerivWithinAt_univ`),
and the flow is anchored at `t₀` (`SmoothSelfDiffeomorph3Family.AnchoredAt.apply`), so the abstract
Grönwall joint-continuity theorem `continuous_flow` (uniform-exponential Lipschitz-in-initial-value ×
integral-curve continuity-in-time) applies verbatim.

This supplies the joint-continuity input that the tube-lemma confinement
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` consumes: it is the concrete
`(τ, q) ↦ (G.maps3 τ) q` continuity the GAP-1 step-(v) orbit control needs for the model comparison
flow.  Crucially the joint continuity is *not* a missing Banach→manifold-ODE-regularity primitive here —
it is already available for globally-Lipschitz fields through `continuous_flow`, which the compactly
supported cut field `χ • chartPushforwardField` satisfies. -/
theorem continuous_maps3_of_lipschitzWith
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {X : ℝ → E → E} {t₀ : ℝ} {K : ℝ≥0}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X) Set.univ t₀)
    (hX : ∀ t, LipschitzWith K (X t)) :
    Continuous (fun p : ℝ × E => (G.maps3 p.1) p.2) := by
  have hΦ : ∀ q : E, IsIntegralCurve (fun τ : ℝ => (G.maps3 τ) q) X := by
    intro q t
    have h := hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn G (Set.mem_univ t) q
    rwa [hasDerivWithinAt_univ] at h
  have h0 : ∀ q : E, (fun τ : ℝ => (G.maps3 τ) q) t₀ = q :=
    fun q => SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := G.maps3) G.anchored q
  exact continuous_flow (Φ := fun q τ => (G.maps3 τ) q) hX hΦ h0

/-- **Joint continuity of the model gauge flow from the cut field's `ContDiff`/compact-support data.**
The natural interface form of `continuous_maps3_of_lipschitzWith`: for a model gauge flow `G` of a field
`v : ℝ → E → E` whose uncurried form is `ContDiff ℝ N` (`1 ≤ N`) with compact support — exactly the shape
`contDiff_hasCompactSupport_cutoff_chartPushforwardField` produces for the bump-globalised cut field
`χ • chartPushforwardField` — the total flow map `(τ, q) ↦ (G.maps3 τ) q` is jointly continuous.  The
required uniform-in-time Lipschitz constant of the field is *derived* (not assumed) from the compact
support via `exists_lipschitzWith_prodMk_left`, so no free-floating Lipschitz hypothesis is needed. -/
theorem continuous_maps3_of_contDiff_hasCompactSupport
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {t₀ : ℝ} {N : WithTop ℕ∞}
    (hF : ContDiff ℝ N (Function.uncurry v))
    (hcs : HasCompactSupport (Function.uncurry v)) (hN : 1 ≤ N)
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) Set.univ t₀) :
    Continuous (fun p : ℝ × E => (G.maps3 p.1) p.2) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_prodMk_left hF hcs hN
  exact continuous_maps3_of_lipschitzWith G (fun t => hC t)

/-- **Uniform short-time orbit-graph confinement for the model gauge flow.**  The direct composition of
`continuous_maps3_of_lipschitzWith` (joint continuity of `(τ, q) ↦ (G.maps3 τ) q`) with the tube-lemma
confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt`: for a model gauge flow `G`
of a uniformly `K`-Lipschitz field on `E`, a compact initial set `Q`, and an open space-time target `W`
containing the anchored graph `{(t₀, (G.maps3 t₀) q) | q ∈ Q}`, there is an honest open time window
`Set.Ioo a b ∋ t₀` on which **every** orbit graph `τ ↦ (τ, (G.maps3 τ) q)` (for `q ∈ Q`) stays in `W`.

Applied with `W` the interior of the compact cutoff window `K₀` (so `W ⊆ K₀`), this yields the
`graph ⊆ K₀` hypothesis consumed by `cutoff_eqOne_along_curve_of_graph_subset` **uniformly over a chart
patch** — closing the flow-trajectory-confinement obligation for the model comparison curve of GAP-1
step (v). -/
theorem exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {X : ℝ → E → E} {t₀ : ℝ} {K : ℝ≥0} {Q : Set E} {W : Set (ℝ × E)}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X) Set.univ t₀)
    (hX : ∀ t, LipschitzWith K (X t))
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, (G.maps3 t₀) q) : ℝ × E) ∈ W) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, (G.maps3 τ) q) : ℝ × E) ∈ W := by
  have hcont := continuous_maps3_of_lipschitzWith G hX
  exact exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt
    (Ψ := fun τ q => (G.maps3 τ) q) hQ hW hgraph0
    (fun q _ => hcont.continuousAt)

/-- **Manifold-target generalisation of the uniform short-time orbit-graph confinement.**  The
tube-lemma confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` holds with the
model normed space `E` replaced by an *arbitrary topological space* `Y`: its proof only ever uses `E`
through its topology (never the linear structure — the elaborator even flags `[NormedSpace ℝ E]` as
unused there).  This is exactly the form the GAP-1 step-(v) **raw-manifold** orbit control needs, where
the flow `Φ : ℝ → M → M` maps the general compact manifold `M` to itself and `M` carries no normed-space
structure, so the model `E`-target confinement cannot be applied directly.  For a time-dependent flow
`Ψ : ℝ → Y → Y` whose space-time graph map `z ↦ (z.1, Ψ z.1 z.2)` is jointly continuous at each
*anchored* point `(t₀, q)` (with `q` ranging over a compact initial set `Q`) and an open space-time
target `W` containing the whole anchored graph `{(t₀, Ψ t₀ q) | q ∈ Q}`, there is an open time window
`Set.Ioo a b ∋ t₀` on which **every** orbit graph stays in `W`.  Proof: identical to the `E`-version —
`IsCompact.eventually_forall_of_forall_eventually` turns the pointwise open-preimage neighbourhoods
(`ContinuousAt.preimage_mem_nhds`) into a single *time* neighbourhood of `t₀` valid for all `q ∈ Q`,
whence an honest `Set.Ioo` window through `mem_nhds_iff_exists_Ioo_subset`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q : Set Y} {W : Set (ℝ × Y)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Y) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × Y => ((z.1, Ψ z.1 z.2) : ℝ × Y)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Single-orbit short-time source confinement (manifold-target).**  The `Q = {x}` case of
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`, packaged directly for
the `hγ_src` obligation of GAP-1 step (v): if the space-time flow `Ψ : ℝ → Y → Y` (`Y` an arbitrary
topological space) is jointly continuous at `(t₀, x)` and `U` is an open set containing the anchor value
`Ψ t₀ x`, there is an open time window `Set.Ioo a b ∋ t₀` on which the single orbit `τ ↦ Ψ τ x` stays
inside `U`.  Applied with `Ψ = Φ` the raw manifold gauge flow, `x` a chart-patch point and
`U = (extChartAt I p).source`, this is exactly the "the orbit stays in the chart source" window the
step-(v) chart-conjugation transfer (`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne`) requires. -/
theorem exists_Ioo_forall_mem_of_continuousAt_source
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {U : Set Y} {t₀ : ℝ} {x : Y}
    (hU : IsOpen U) (hx : Ψ t₀ x ∈ U)
    (hcont : ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, x)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, Ψ τ x ∈ U := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      (Ψ := Ψ) (Q := ({x} : Set Y)) (W := Set.univ ×ˢ U) (t₀ := t₀)
      isCompact_singleton (isOpen_univ.prod hU)
      (fun q hq => by
        rw [Set.mem_singleton_iff] at hq; subst hq
        exact ⟨Set.mem_univ _, hx⟩)
      (fun q hq => by
        rw [Set.mem_singleton_iff] at hq; subst hq
        exact hcont)
  exact ⟨a, b, hmem, fun τ hτ => (hgraph τ hτ x rfl).2⟩

/-- **Compact-window orbit-graph containment (manifold-target) — the bridge to
`cutoff_eqOne_along_curve_of_graph_subset`.**  Where
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget` confines the orbit
graphs into an *open* space-time target, this variant delivers containment in a *compact window* `K`
whose **interior** contains the anchored graph — the exact `∀ τ ∈ s, (τ, g τ) ∈ K` datum that
`cutoff_eqOne_along_curve_of_graph_subset` consumes (a cutoff `χ` with `∀ᶠ r in 𝓝ˢ K, χ r = 1` is then
`≡ 1` along every confined orbit).  Proof: apply the open-target confinement to `interior K`
(`isOpen_interior`), then `interior_subset`.  This closes the "open target ⟹ compact-window graph
containment" glue for the raw-manifold side of GAP-1 step (v), uniformly over a compact chart patch. -/
theorem exists_Ioo_forall_forall_graph_mem_compact_of_isCompact_of_continuousAt_manifoldTarget
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q : Set Y} {K : Set (ℝ × Y)} {t₀ : ℝ}
    (hQ : IsCompact Q)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Y) ∈ interior K)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ K := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      hQ isOpen_interior hgraph0 hcont
  exact ⟨a, b, hmem, fun τ hτ q hq => interior_subset (hgraph τ hτ q hq)⟩

/-- **Uniform short-time source confinement over a compact set (manifold-target).**  The compact-`Q`
generalisation of `exists_Ioo_forall_mem_of_continuousAt_source`: where that lemma confines a *single*
orbit `τ ↦ Ψ τ x` into an open set `U`, this one confines *every* orbit `τ ↦ Ψ τ q` (for `q` in a
compact set `Q`) into `U` on a **single** time window.  For a time-dependent flow `Ψ : ℝ → Y → Y` (`Y`
an arbitrary topological space) jointly continuous at each anchored point `(t₀, q)` (`q ∈ Q`), with the
anchor values `Ψ t₀ q ∈ U` for all `q ∈ Q` and `U` open, there is an open time window `Set.Ioo a b ∋ t₀`
on which `Ψ τ q ∈ U` for every `τ` in the window and every `q ∈ Q`.  Proof: apply the manifold-target
tube-lemma confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`
to the open space-time target `W = univ ×ˢ U`, then read off the second component.  This is the
`hγ_src`-producing datum of GAP-1 step (v) **uniformly over a compact chart patch** (take
`U = (extChartAt I p).source` and `Q` a compact neighbourhood of the patch). -/
theorem exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q U : Set Y} {t₀ : ℝ}
    (hQ : IsCompact Q) (hU : IsOpen U)
    (hanchor : ∀ q ∈ Q, Ψ t₀ q ∈ U)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, Ψ τ q ∈ U := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      (Ψ := Ψ) (Q := Q) (W := Set.univ ×ˢ U) (t₀ := t₀)
      hQ (isOpen_univ.prod hU)
      (fun q hq => ⟨Set.mem_univ _, hanchor q hq⟩) hcont
  exact ⟨a, b, hmem, fun τ hτ q hq => (hgraph τ hτ q hq).2⟩

/-- **The `hγ_src` datum of GAP-1 step (v), produced from the raw manifold flow's joint continuity.**
Specialises `exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source` to the open target
`U = (extChartAt I p).source` and an **anchored** flow `Φ` (`Φ 0 = id` on `Q`): the anchor condition
`Φ 0 x ∈ (extChartAt I p).source` then reduces to `Q ⊆ (extChartAt I p).source`.  For a jointly-continuous
(at each `(0, x)`, `x ∈ Q`) anchored flow `Φ` on a compact patch `Q` contained in a chart source, there
is an open window `Set.Ioo a b ∋ 0` on which every orbit stays in the chart source:
`∀ τ ∈ Ioo a b, ∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source`.  Since `U ⊆ Q` for the open chart patch `U`
of the step-(v) capstone, this delivers exactly the `hγ_src` hypothesis of
`contMDiffOn_flowSlice_of_cutoff_orbit_control`, derived from the raw manifold gauge flow's joint
continuity (`exists_timeDependent_flow_compact_continuousAt`) rather than assumed. -/
theorem exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source := by
  have hUopen : IsOpen (extChartAt I p).source := by
    rw [extChartAt_source]; exact (chartAt H p).open_source
  exact exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source
    hQ hUopen (fun x hx => by rw [hanchor x hx]; exact hQsub hx) hcont

/-- **General tube-lemma confinement with distinct source/target types.**  Identical to
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`, but allowing the
compact initial set `Q ⊆ Y` and the space-time target `W ⊆ ℝ × Z` to live over *different* topological
spaces `Y` (domain) and `Z` (codomain) — the proof never uses `Y = Z`.  This is what the raw-manifold
`hγ_mem` control needs, where the confined quantity is the **chart image** `extChartAt I p (Φ τ x) : E`
of the orbit `Φ τ x : M`, so the domain `M` and codomain `E` genuinely differ.  For a map `Ψ : ℝ → Y → Z`
jointly continuous at each anchored point `(t₀, q)` (`q ∈ Q` compact) into an open space-time target `W`
containing the anchored graph, there is an open time window `Set.Ioo a b ∋ t₀` on which every orbit
graph `τ ↦ (τ, Ψ τ q)` stays in `W`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {Ψ : ℝ → Y → Z} {Q : Set Y} {W : Set (ℝ × Z)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Z) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Z) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Z) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × Y => ((z.1, Ψ z.1 z.2) : ℝ × Z)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Joint continuity of the chart-composed manifold flow at the anchor.**  For an anchored flow
`Φ` (`Φ 0 x = x`) jointly continuous at `(0, x)` with `x` in the chart source, the chart-composed map
`z ↦ extChartAt I p (Φ z.1 z.2)` is `ContinuousAt (0, x)`: post-compose `Φ`'s joint continuity with the
continuity of `extChartAt I p` at `Φ 0 x = x ∈ (extChartAt I p).source` (`continuousAt_extChartAt'`).
This is the joint-continuity input the `hγ_mem` confinement of GAP-1 step (v) consumes (the confined
quantity being the chart image of the orbit). -/
theorem continuousAt_zero_prod_extChartAt_flow
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {p x : M}
    (hxsrc : x ∈ (extChartAt I p).source)
    (hanchor : Φ 0 x = x)
    (hcont : ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ContinuousAt (fun z : ℝ × M => extChartAt I p (Φ z.1 z.2)) (0, x) := by
  have hchart : ContinuousAt (extChartAt I p) x := continuousAt_extChartAt' hxsrc
  exact hchart.comp_of_eq hcont (by exact hanchor)

/-- **The `hγ_mem` datum of GAP-1 step (v), produced from the raw manifold flow's joint continuity.**
Applies the distinct-type tube-lemma confinement
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod` to the chart-composed flow
`Ψ τ x = extChartAt I p (Φ τ x)` (jointly continuous by `continuousAt_zero_prod_extChartAt_flow`), over a
compact patch `Q ⊆ (extChartAt I p).source` and an open space-time target `W ⊆ ℝ × E` containing the
anchored chart-image graph.  Yields an open window `Set.Ioo a b ∋ 0` on which the chart image of every
orbit stays in `W`: `∀ τ ∈ Ioo a b, ∀ x ∈ Q, (τ, extChartAt I p (Φ τ x)) ∈ W`.  With `W` the state graph
`{z | z.2 ∈ state z.1}` (open) this is exactly the `hγ_mem` hypothesis of
`contMDiffOn_flowSlice_of_cutoff_orbit_control`. -/
theorem exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W := by
  refine exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod
    (Ψ := fun τ x => extChartAt I p (Φ τ x)) (Q := Q) (W := W) hQ hW ?_ ?_
  · intro x hx
    simpa only [hanchor x hx] using hgraph0 x hx
  · intro x hx
    exact continuousAt_zero_prod_extChartAt_flow (hQsub hx) (hanchor x hx) (hcont x hx)

/-- **Intersecting two open-window confinements at a common anchor.**  Given two short-time confinements
`∃ a b, t₀ ∈ Ioo a b ∧ ∀ τ ∈ Ioo a b, P τ` and the same for `R`, their windows intersect to a single
open window `Ioo (max a₁ a₂) (min b₁ b₂) ∋ t₀` on which **both** `P τ` and `R τ` hold.  The generic glue
for assembling the several separate short-time orbit-confinement windows of GAP-1 step (v)
(`hγ_src`, `hγ_mem`, the model-curve `hg_mem`, the cutoff window) into the *single* window
`contMDiffOn_flowSlice_of_cutoff_orbit_control` consumes. -/
theorem exists_Ioo_forall_and {t₀ : ℝ} {P R : ℝ → Prop}
    (h₁ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, P τ)
    (h₂ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, R τ) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, P τ ∧ R τ := by
  obtain ⟨a₁, b₁, ⟨ha₁, hb₁⟩, hP⟩ := h₁
  obtain ⟨a₂, b₂, ⟨ha₂, hb₂⟩, hR⟩ := h₂
  refine ⟨max a₁ a₂, min b₁ b₂, ⟨max_lt ha₁ ha₂, lt_min hb₁ hb₂⟩, fun τ hτ => ?_⟩
  exact ⟨hP τ (Set.Ioo_subset_Ioo (le_max_left a₁ a₂) (min_le_left b₁ b₂) hτ),
         hR τ (Set.Ioo_subset_Ioo (le_max_right a₁ a₂) (min_le_right b₁ b₂) hτ)⟩

/-- **The `hγ_src` *and* `hγ_mem` data of GAP-1 step (v) on a single common window.**  Bundles
`exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt` (orbit stays in the chart source) and
`exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt` (chart image of orbit stays in the open
space-time target `W`) into one open window `Set.Ioo a b ∋ 0` via `exists_Ioo_forall_and`.  For a
jointly-continuous anchored raw manifold flow `Φ` over a compact patch `Q ⊆ (extChartAt I p).source`,
delivers both raw-manifold orbit-confinement faces of the step-(v) capstone simultaneously — the exact
common time window `contMDiffOn_flowSlice_of_cutoff_orbit_control` needs. -/
theorem exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b,
        (∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source) ∧
        (∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W) :=
  exists_Ioo_forall_and
    (exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt hQ hQsub hanchor hcont)
    (exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt hQ hQsub hW hanchor hgraph0 hcont)

/-- **The compact-manifold time-dependent flow together with its raw-manifold orbit confinement, on one
window.**  End-to-end assembly: from a jointly-`C¹` time-dependent field `X` on a compact boundaryless
`T2` manifold, `exists_timeDependent_flow_compact_continuousAt` produces the anchored flow `Φ`
(`Φ 0 = id`), its orbit ODE on `Ioo (-ε) ε`, and its joint continuity at every anchor `(0, x)`.  Feeding
the joint continuity into `exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt` and
intersecting the resulting confinement window with the ODE window `Ioo (-ε) ε` (via
`exists_Ioo_forall_and` against the identity confinement of `Ioo (-ε) ε`) yields a **single** open window
`Set.Ioo a b ∋ 0` on which, over a compact chart patch `Q ⊆ (extChartAt I p).source`:
the orbit ODE holds (`hγ`, `mono`-restricted from `Ioo (-ε) ε`), every orbit stays in the chart source
(`hγ_src`), and the chart image of every orbit stays in the open space-time target `W` (`hγ_mem`).  This
is the raw-manifold-side input package of `contMDiffOn_flowSlice_of_cutoff_orbit_control`, produced
unconditionally from the field's jet — no assumed flow or confinement. -/
theorem exists_timeDependent_flow_compact_extChartAt_source_and_mem
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E]
    [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W) :
    ∃ (Φ : ℝ → M → M) (a b : ℝ), (0 : ℝ) ∈ Set.Ioo a b ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x ∈ Q, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x)))) ∧
      (∀ τ ∈ Set.Ioo a b,
        (∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source) ∧
        (∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W)) := by
  obtain ⟨ε, hε, Φ, hanchor, horbit, hcontA⟩ :=
    PoincareCurvature.ManifoldFlow.exists_timeDependent_flow_compact_continuousAt hX
  have hconf := exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt
    (Φ := Φ) hQ hQsub hW (fun x _ => hanchor x) hgraph0 (fun x _ => hcontA x)
  obtain ⟨a, b, hmem0, hboth⟩ := exists_Ioo_forall_and hconf
    ⟨-ε, ε, ⟨neg_lt_zero.mpr hε, hε⟩, fun τ hτ => hτ⟩
  have hsub : Set.Ioo a b ⊆ Set.Ioo (-ε) ε := fun τ hτ => (hboth τ hτ).2
  refine ⟨Φ, a, b, hmem0, hanchor, ?_, fun τ hτ => (hboth τ hτ).1⟩
  intro x _ τ hτ
  exact (horbit x τ (hsub hτ)).mono hsub

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
