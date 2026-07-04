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

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
