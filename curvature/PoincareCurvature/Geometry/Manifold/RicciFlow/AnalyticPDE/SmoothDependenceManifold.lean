module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.FlowDiffeomorphism
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.Diffeomorph

set_option linter.unusedSectionVars false

/-!
# Manifold-level (`ContMDiff` / `HasMFDerivAt`) smooth dependence of the ODE flow on initial data

The Banach smooth-dependence towers `SmoothDependenceCk` and `FlowDiffeomorphism` establish, for a
flow family `Φ : E → ℝ → E` of a `C^{3,1}` time-dependent vector field `v` on a real Banach space
`E`, that the time-`t` flow map `x ↦ Φ x t` is a **`C³` diffeomorphism** of the state space (bijective,
two-sided-regular, both directions `ContDiff ℝ 3`).  Those results are stated entirely in the
*Fréchet* (`ContDiff` / `HasFDerivAt` / `IsIntegralCurve`) vocabulary of `Mathlib.Analysis`.

Item 2's compact-manifold gauge-flow constructor, however, consumes this data in the *manifold*
(`ContMDiff` / `HasMFDerivAt`) vocabulary of `Mathlib.Geometry.Manifold` — cf.
`GaugeReduction/GaugeFlowAssembly.lean`, whose reduction target `gaugeFlow_of_inverse_flow` needs
mutually inverse `ContMDiff I I 3` time-slice maps together with the manifold ODE derivative equation
`HasMFDerivAt (fun τ ↦ F τ x) t ((1).smulRight (X t (F t x)))`.

This module supplies the missing **Fréchet → manifold bridge** for the model manifold `𝓘(ℝ, E)`
(the state space `E` equipped with its canonical trivial model-with-corners).  Everything is a
transport of the already-proved Banach tower through the standard Mathlib identifications
`contMDiff_iff_contDiff`, `hasMFDerivAt_iff_hasFDerivAt`, `hasDerivAt_iff_hasFDerivAt`; no new PDE or
analytic content is introduced, and nothing here touches the heavy gauge files.  Because the
general-manifold smooth-dependence theorem is proved chart-by-chart and each chart *is* the model
space `E`, this model-manifold layer is the load-bearing chart-level core.

* `hasMFDerivAt_of_isIntegralCurve` — the manifold ODE derivative form of an integral curve:
  from `IsIntegralCurve γ v`, for every `t`,
  `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (γ t)))`
  (exactly the `hderiv` shape the gauge-flow assembly consumes).
* `contMDiff_three_flow_apply_of_lipschitz_thirdDeriv` — the manifold form of the spatial `C³`
  regularity of the flow map: `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z ↦ Φ z t)`, for every `t`.
* `exists_flow_contMDiff_three` — field-data-only manifold smooth-dependence existence: a flow family
  `Φ` (anchored at `t₀`, integral curve of `v`) whose time-`t` map is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`.
* `exists_flow_contMDiff_three_diffeomorph` — the manifold `C³` **self-diffeomorphism family**: for
  every `t` the time-`t` map has a two-sided inverse `ψ`, and both `x ↦ Φ x t` and `ψ` are
  `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`.  This is the model-manifold instance of the diffeomorphism data the
  compact-manifold gauge flow of Item 2 consumes.
* `exists_flow_contMDiff_three_gaugeData` — the full bundle: anchoring, the manifold ODE derivative
  equation, and the per-time `C³` self-diffeomorphism data, packaged in the exact shapes
  `gaugeFlow_of_inverse_flow` needs (for the model manifold `𝓘(ℝ, E)`).

Everything is proved sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
variable {Φ : E → ℝ → E}

/-- **Manifold ODE derivative form of an integral curve.**  If `γ : ℝ → E` is an integral curve of
the field `v` (`IsIntegralCurve γ v`, i.e. `HasDerivAt γ (v t (γ t)) t` for all `t`), then in the
`𝓘(ℝ, E)` model-manifold vocabulary it satisfies the gauge-flow ODE derivative equation

`HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (γ t)))`

for every `t`.  This is exactly the `hderiv` shape the compact-manifold gauge-flow assembly
(`GaugeReduction/GaugeFlowAssembly.lean`) consumes.  A pure transport through
`hasDerivAt_iff_hasFDerivAt` (`toSpanSingleton = (1).smulRight`) and `hasMFDerivAt_iff_hasFDerivAt`. -/
theorem hasMFDerivAt_of_isIntegralCurve {γ : ℝ → E} (h : IsIntegralCurve γ v) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (γ t))) := by
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  exact ((h t).hasFDerivAt).hasMFDerivAt

/-- **Within-set manifold ODE derivative form of an integral curve.**  The `HasMFDerivWithinAt`
(`HasMFDerivAt[s]`) refinement of `hasMFDerivAt_of_isIntegralCurve`, holding for every time set `s`
and every time `t` — this is the exact `hderiv` shape (`HasMFDerivAt[s] (fun τ ↦ F τ x) t …`) that
the compact-manifold gauge-flow reduction `GaugeReduction/GaugeFlowAssembly.gaugeFlow_of_inverse_flow`
consumes. -/
theorem hasMFDerivWithinAt_of_isIntegralCurve {γ : ℝ → E} (h : IsIntegralCurve γ v)
    (s : Set ℝ) (t : ℝ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (γ t))) :=
  (hasMFDerivAt_of_isIntegralCurve h t).hasMFDerivWithinAt

/-- **Manifold spatial `C³` regularity of the flow map.**  Under the `C^{3,1}` jet hypotheses on the
field `v`, together with a flow family `Φ` anchored at `t₀` and integrating `v`, the time-`t` flow map
`x ↦ Φ x t` is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3` for every `t`.  The manifold form of
`contDiff_three_flow_apply_of_lipschitz_thirdDeriv`, obtained through `contMDiff_iff_contDiff`. -/
theorem contMDiff_three_flow_apply_of_lipschitz_thirdDeriv [CompleteSpace E]
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
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) :=
  contMDiff_iff_contDiff.mpr <|
    contDiff_three_flow_apply_of_lipschitz_thirdDeriv
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry hΦ h0 t

/-- **Field-data-only manifold smooth-dependence existence.**  From the `C^{3,1}` jet of the field
`v` alone there is a flow family `Φ`, anchored at `t₀` and integrating `v`, whose time-`t` flow map is
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3` for every `t`.  The manifold form of
`SmoothDependenceCk.exists_flow_family` plus `C³` spatial regularity. -/
theorem exists_flow_contMDiff_three [CompleteSpace E]
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
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  exact contMDiff_three_flow_apply_of_lipschitz_thirdDeriv
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry hΦ h0 t

/-- **Manifold `C³` self-diffeomorphism family.**  From the `C^{3,1}` jet of the field `v` alone
there is a flow family `Φ`, anchored at `t₀` and integrating `v`, whose time-`t` map is a `C³`
diffeomorphism of the state space *for every* `t`: it has a two-sided inverse `ψ`, and both
`x ↦ Φ x t` and `ψ` are `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`.  The manifold form of
`exists_flow_contDiff_three_diffeomorph` — the model-manifold instance of the diffeomorphism data the
compact-manifold gauge flow of Item 2 consumes. -/
theorem exists_flow_contMDiff_three_diffeomorph [CompleteSpace E]
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
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
        Function.RightInverse ψ (fun z => Φ z t) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 ψ := by
  obtain ⟨Φ, h0, hΦ, hdiff⟩ := exists_flow_contDiff_three_diffeomorph
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ := hdiff t
  exact ⟨ψ, hL, hR, contMDiff_iff_contDiff.mpr hcdΦ, contMDiff_iff_contDiff.mpr hcdψ⟩

/-- **Full model-manifold gauge-flow data bundle.**  From the `C^{3,1}` jet of the field `v` alone
there is a flow family `Φ` providing, for the model manifold `𝓘(ℝ, E)`, all the data the
compact-manifold gauge-flow constructor `GaugeFlowAssembly.gaugeFlow_of_inverse_flow` consumes:

* anchoring `Φ z t₀ = z`;
* the manifold gauge-flow ODE derivative equation
  `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ ↦ Φ z τ) t ((1).smulRight (v t (Φ z t)))` at every time;
* for every `t`, mutually inverse `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3` time-slice maps `x ↦ Φ x t` and `ψ`.

This is the model-manifold instance (state space `E`) of Item 2's raw `C³` gauge-flow existence data,
assembled entirely from the Banach smooth-dependence tower. -/
theorem exists_flow_contMDiff_three_gaugeData [CompleteSpace E]
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
      ∀ t, ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
        Function.RightInverse ψ (fun z => Φ z t) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 ψ := by
  obtain ⟨Φ, h0, hΦ, hdiff⟩ := exists_flow_contMDiff_three_diffeomorph
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  exact ⟨Φ, h0, fun z t => hasMFDerivAt_of_isIntegralCurve (hΦ z) t, hdiff⟩

/-- **The time-`t` flow map bundled as a first-class Mathlib `C³` `Diffeomorph`.**  From the `C^{3,1}`
jet of the field `v` alone there is a flow family `Φ`, anchored at `t₀` and integrating `v`, such that
for *every* `t` the time-`t` map `x ↦ Φ x t` is (the coercion of) a genuine
`Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3` — a `C³` diffeomorphism of the model manifold `E` in Mathlib's
own bundled sense.  The reverse-time inverse flow supplies the smooth inverse. -/
theorem exists_flow_diffeomorph_three [CompleteSpace E]
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
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3, ∀ z, F z = Φ z t := by
  obtain ⟨Φ, h0, hΦ, hdiff⟩ := exists_flow_contMDiff_three_diffeomorph
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ := hdiff t
  exact ⟨⟨⟨fun z => Φ z t, ψ, hL, hR⟩, hcdΦ, hcdψ⟩, fun z => rfl⟩

/-!
## `C¹` and `C²` manifold layers

The same Fréchet → manifold transport applies verbatim to the `C¹` (`C^{1,1}` field) and `C²`
(`C^{2,1}` field) Banach diffeomorphism capstones, giving the lower-order manifold spatial regularity
and the `C¹`/`C²` `Diffeomorph` bundles.  This rounds the module out into a full `C¹`/`C²`/`C³`
manifold smooth-dependence tower.
-/

/-- **Manifold spatial `C¹` regularity of the flow map** (`C^{1,1}` field): the manifold form of
`contDiff_one_flow_apply_of_lipschitz_deriv`, via `contMDiff_iff_contDiff`. -/
theorem contMDiff_one_flow_apply_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) :=
  contMDiff_iff_contDiff.mpr <|
    contDiff_one_flow_apply_of_lipschitz_deriv hv hvc hderiv hDvc hDvlip hΦ h0 t

/-- **Manifold spatial `C²` regularity of the flow map** (`C^{2,1}` field): the manifold form of
`contDiff_two_flow_apply_of_lipschitz_secondDeriv`, via `contMDiff_iff_contDiff`. -/
theorem contMDiff_two_flow_apply_of_lipschitz_secondDeriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun z => Φ z t) :=
  contMDiff_iff_contDiff.mpr <|
    contDiff_two_flow_apply_of_lipschitz_secondDeriv
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip hΦ h0 t

/-- **The time-`t` flow map bundled as a Mathlib `C¹` `Diffeomorph`** of the model manifold `E`, from
the `C^{1,1}` field jet alone. -/
theorem exists_flow_diffeomorph_one [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s)) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 1, ∀ z, F z = Φ z t := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ :=
    exists_contDiff_one_diffeomorph_flow_apply hv hvc hderiv hDvc hDvlip hΦ h0 t
  exact ⟨⟨⟨fun z => Φ z t, ψ, hL, hR⟩,
    contMDiff_iff_contDiff.mpr hcdΦ, contMDiff_iff_contDiff.mpr hcdψ⟩, fun z => rfl⟩

/-- **The time-`t` flow map bundled as a Mathlib `C²` `Diffeomorph`** of the model manifold `E`, from
the `C^{2,1}` field jet alone. -/
theorem exists_flow_diffeomorph_two [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s)) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 2, ∀ z, F z = Φ z t := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ :=
    exists_contDiff_two_diffeomorph_flow_apply hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip hΦ h0 t
  exact ⟨⟨⟨fun z => Φ z t, ψ, hL, hR⟩,
    contMDiff_iff_contDiff.mpr hcdΦ, contMDiff_iff_contDiff.mpr hcdψ⟩, fun z => rfl⟩

/-!
## The spatial pushforward (differential) of the flow map, and the resolvent action

The layers above supply the *spatial* smoothness (`ContMDiff`) of the flow map `x ↦ Φ x t` and the
*time* derivative of a single trajectory (`hasMFDerivAt_of_isIntegralCurve`).  The remaining
manifold-vocabulary datum the gauge-flow consumers of Items 1 & 2 need is the **pushforward** — the
differential (`mfderiv`) of the flow map `x ↦ Φ x t` itself — together with its identification with
the resolvent / fundamental solution `D_x Φ_t`, and the manifold form of the vector variational ODE
obeyed by a pushed-forward direction `τ ↦ D_x Φ_τ · u₀`.

All three are transports of the already-proved Banach `SmoothDependenceCk` tower through the standard
Mathlib identifications `HasFDerivAt.hasMFDerivAt` / `HasMFDerivAt.mfderiv` (for the model manifold
`𝓘(ℝ, E)`, whose `mfderiv` *is* the Fréchet `fderiv`) and the module's own
`hasMFDerivAt_of_isIntegralCurve`; no new PDE or analytic content is introduced, and nothing here
touches the heavy gauge files.  Everything is sorry-free (axioms
`propext`/`Classical.choice`/`Quot.sound` only).
-/

/-- **Manifold pushforward of the flow map from its Fréchet derivative.**  If the time-`t` flow map
`x ↦ Φ x t` has Fréchet derivative `D` at `x₀`, then in the `𝓘(ℝ, E)` model-manifold vocabulary it
has manifold differential `D`:
`HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ Φ z t) x₀ D`.  The spatial companion of the trajectory
time-derivative `hasMFDerivAt_of_isIntegralCurve` — the manifold form of the flow's *pushforward*
(`Φ_t ·`) the tensor time-derivative chain rule (Item 1) and the compact-manifold gauge-flow
constructor (Item 2) consume.  A pure transport through `HasFDerivAt.hasMFDerivAt`. -/
theorem hasMFDerivAt_flow_apply_of_hasFDerivAt {t : ℝ} {x₀ : E} {D : E →L[ℝ] E}
    (h : HasFDerivAt (fun z => Φ z t) D x₀) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) x₀ D :=
  h.hasMFDerivAt

/-- **Within-set manifold pushforward of the flow map** from its Fréchet derivative:
`HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ Φ z t) s x₀ D` for every set `s`.  The `HasMFDerivAt[s]`
refinement of `hasMFDerivAt_flow_apply_of_hasFDerivAt`. -/
theorem hasMFDerivWithinAt_flow_apply_of_hasFDerivAt {t : ℝ} {x₀ : E} {D : E →L[ℝ] E} {s : Set E}
    (h : HasFDerivAt (fun z => Φ z t) D x₀) :
    HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) s x₀ D :=
  h.hasMFDerivAt.hasMFDerivWithinAt

/-- **The manifold differential (`mfderiv`) of the flow map equals its Fréchet derivative.**
`mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ Φ z t) x₀ = D` whenever `HasFDerivAt (fun z ↦ Φ z t) D x₀`. -/
theorem mfderiv_flow_apply_of_hasFDerivAt {t : ℝ} {x₀ : E} {D : E →L[ℝ] E}
    (h : HasFDerivAt (fun z => Φ z t) D x₀) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) x₀ = D :=
  h.hasMFDerivAt.mfderiv

/-- **The manifold pushforward of the flow map is the resolvent** (`C^{1,1}` field, self-contained).
For a `K`-Lipschitz field `v` with a spatial derivative `Dv` whose deviation from the reference
coefficient `A` along the trajectory chords is `L`-linear, the time-`t` flow map `x ↦ Φ x t` has
manifold differential the fundamental solution (resolvent) `D_x Φ_t`:
`HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ Φ z t) x₀ (fundamentalSolution hA hΦ' h0' t)`.  The manifold
form of `hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt` (the `E →L[ℝ] E` type ascription forces
the resolvent to elaborate at its Fréchet type before the tangent-space identification). -/
theorem hasMFDerivAt_flow_apply_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) x₀
      (fundamentalSolution hA hΦ' h0' t : E →L[ℝ] E) :=
  (hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL
    hlip).hasMFDerivAt

/-- **The manifold differential of the flow map is the resolvent** (`C^{1,1}` field, `mfderiv`
readout): `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t = D_x Φ_t`.
-/
theorem mfderiv_flow_apply_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) x₀
      = (fundamentalSolution hA hΦ' h0' t : E →L[ℝ] E) :=
  (hasMFDerivAt_flow_apply_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).mfderiv

/-- **Manifold vector variational ODE of a pushed-forward direction (resolvent column).**  For each
direction `u₀`, the path `τ ↦ D_x Φ_τ · u₀` (the resolvent applied to `u₀`, i.e. the pushforward of
the fixed tangent vector `u₀`) obeys, in the `𝓘(ℝ, E)` model-manifold vocabulary, the vector
variational ODE derivative equation
`HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ ↦ D_x Φ_τ · u₀) t ((1).smulRight (A t (D_x Φ_t · u₀)))` for every
`t`.  The manifold form of `isIntegralCurve_fundamentalSolution_apply` via
`hasMFDerivAt_of_isIntegralCurve` — exactly the "time-derivative of the pushforward `Φ_t · u`" datum
the tensor time-derivative chain rule (Item 1) consumes. -/
theorem hasMFDerivAt_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => fundamentalSolution hA hΦ h0 τ u₀) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (variationalFieldVec A t (fundamentalSolution hA hΦ h0 t u₀) : E)) :=
  hasMFDerivAt_of_isIntegralCurve (isIntegralCurve_fundamentalSolution_apply hA hΦ h0 u₀) t

/-- **Within-set manifold vector variational ODE of a pushed-forward direction.**  The
`HasMFDerivWithinAt` (`HasMFDerivAt[s]`) refinement of `hasMFDerivAt_fundamentalSolution_apply`,
holding for every time set `s` — the within-set derivative shape the gauge-flow assembly consumes for
the pushed-forward frame `τ ↦ D_x Φ_τ · u₀`. -/
theorem hasMFDerivWithinAt_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) (s : Set ℝ) (t : ℝ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => fundamentalSolution hA hΦ h0 τ u₀) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (variationalFieldVec A t (fundamentalSolution hA hΦ h0 t u₀) : E)) :=
  (hasMFDerivAt_fundamentalSolution_apply hA hΦ h0 u₀ t).hasMFDerivWithinAt

/-- **Manifold `C^{n+1}` time-regularity of a pushed-forward direction.**  For a `C^n`-in-time
coefficient `A`, the resolvent action `τ ↦ D_x Φ_τ · u₀` (the pushforward of the fixed tangent vector
`u₀` along the flow) is `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (n + 1)` in time.  The manifold form of
`contDiff_fundamentalSolution_apply_time`, via `contMDiff_iff_contDiff` — the pushforward-leg
time-regularity Item 1's tensor time-derivative chain rule consumes. -/
theorem contMDiff_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) (u₀ : E) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((n : WithTop ℕ∞) + 1)
      (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  contMDiff_iff_contDiff.mpr (contDiff_fundamentalSolution_apply_time hA hΦ h0 n hAdiff u₀)

/-- **Manifold `C^∞` time-regularity of a pushed-forward direction.**  For a `C^∞`-in-time
coefficient `A`, the resolvent action `τ ↦ D_x Φ_τ · u₀` is `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞` in time.
The `C^∞` companion of `contMDiff_fundamentalSolution_apply_time`. -/
theorem contMDiff_infty_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  contMDiff_iff_contDiff.mpr
    (contDiff_infty_fundamentalSolution_apply_time hA hAsmooth hΦ h0 u₀)

/-- **Manifold operator variational ODE of the resolvent path.**  For a norm-continuous coefficient
`A`, the *operator-valued* resolvent curve `τ ↦ D_x Φ_τ ∈ E →L[ℝ] E` (the fundamental solution as a
whole operator, not merely its action on one direction) obeys, in the model-manifold vocabulary of
`𝓘(ℝ, E →L[ℝ] E)`, the operator variational ODE derivative equation
`HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) (fun τ ↦ D_x Φ_τ) t ((1).smulRight (A t ∘ D_x Φ_t))` for every
`t`.  The operator-valued companion of `hasMFDerivAt_fundamentalSolution_apply`: it is the manifold
form of `isIntegralCurve_fundamentalSolution` (the resolvent is the integral curve of the operator
variational field `variationalField A : W ↦ A t ∘ W`), obtained through the module's own
`hasMFDerivAt_of_isIntegralCurve` instantiated at the *operator* model space `E →L[ℝ] E`.  This is the
time-regularity datum a consumer pushing forward a whole frame — rather than a single tangent
direction — along the flow consumes. -/
theorem hasMFDerivAt_fundamentalSolution {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) (fun τ => fundamentalSolution hA hΦ h0 τ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (variationalField A t (fundamentalSolution hA hΦ h0 t) : E →L[ℝ] E)) :=
  hasMFDerivAt_of_isIntegralCurve (isIntegralCurve_fundamentalSolution hA hAcont hΦ h0) t

/-- **Within-set manifold operator variational ODE of the resolvent path.**  The
`HasMFDerivWithinAt` (`HasMFDerivAt[s]`) refinement of `hasMFDerivAt_fundamentalSolution`, holding for
every time set `s` — the within-set derivative shape the gauge-flow assembly consumes for the
operator-valued resolvent frame `τ ↦ D_x Φ_τ`. -/
theorem hasMFDerivWithinAt_fundamentalSolution {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (s : Set ℝ) (t : ℝ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) (fun τ => fundamentalSolution hA hΦ h0 τ) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (variationalField A t (fundamentalSolution hA hΦ h0 t) : E →L[ℝ] E)) :=
  (hasMFDerivAt_fundamentalSolution hA hAcont hΦ h0 t).hasMFDerivWithinAt

/-- **Manifold `C^{n+1}` time-regularity of the operator-valued resolvent path.**  For a `C^n`-in-time
coefficient `A`, the resolvent curve `τ ↦ D_x Φ_τ ∈ E →L[ℝ] E` (the whole fundamental-solution
operator) is `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) (n + 1)` in time.  The operator-valued companion of
`contMDiff_fundamentalSolution_apply_time` — the manifold form of `contDiff_fundamentalSolution_time`,
via `contMDiff_iff_contDiff` for the operator model space `E →L[ℝ] E`. -/
theorem contMDiff_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) ((n : WithTop ℕ∞) + 1)
      (fun s => fundamentalSolution hA hΦ h0 s) :=
  contMDiff_iff_contDiff.mpr (contDiff_fundamentalSolution_time hA hΦ h0 n hAdiff)

/-- **Manifold `C^∞` time-regularity of the operator-valued resolvent path.**  For a `C^∞`-in-time
coefficient `A`, the resolvent curve `τ ↦ D_x Φ_τ ∈ E →L[ℝ] E` is `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) ∞`
in time.  The `C^∞` companion of `contMDiff_fundamentalSolution_time`. -/
theorem contMDiff_infty_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E →L[ℝ] E) ∞ (fun s => fundamentalSolution hA hΦ h0 s) :=
  contMDiff_iff_contDiff.mpr
    (contDiff_infty_fundamentalSolution_time hA hAsmooth hΦ h0)

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
