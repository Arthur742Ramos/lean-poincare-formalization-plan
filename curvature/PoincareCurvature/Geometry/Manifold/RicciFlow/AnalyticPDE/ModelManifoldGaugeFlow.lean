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

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
