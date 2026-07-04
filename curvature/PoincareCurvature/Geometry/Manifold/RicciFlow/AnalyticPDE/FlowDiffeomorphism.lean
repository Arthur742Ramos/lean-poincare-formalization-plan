module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk

set_option linter.unusedSectionVars false

/-!
# The time-`t` flow map is a homeomorphism (bijectivity / inverse-flow half of the diffeomorphism)

The smooth-dependence tower (`SmoothDependenceCk`) already establishes that for a flow family
`Φ : E → ℝ → E` of a uniformly `K`-Lipschitz, time-continuous vector field `v` anchored at
`Φ x t₀ = x`, the time-`t` flow map `x ↦ Φ x t` is **injective** (`injective_flow_apply`) and
**Lipschitz/continuous** in the initial value (`lipschitzWith_flow_apply`, `continuous_flow_apply`).
Injectivity is exactly the "diffeomorphism onto its image" half that Item 2's compact-manifold
gauge-flow constructor needs; the *other* half — that the flow map is a **bijection with a
continuous inverse** (so the flow at each time is an ambient self-homeomorphism, the topological
skeleton of the self-diffeomorphism family `SmoothSelfDiffeomorph3Family`) — was still missing.

This module closes that gap, entirely from the existence and uniqueness theory already in
`SmoothDependenceCk`:

* `surjective_flow_apply` — the flow map is **surjective**: every `w` is `Φ z t` for the initial
  value `z = γ t₀`, where `γ` is the integral curve through `w` at time `t`
  (`exists_isIntegralCurve_of_lipschitzWith`), identified with `Φ (γ t₀)` by uniqueness
  (`eq_of_isIntegralCurve_of_eq_at`).
* `bijective_flow_apply` — combining with `injective_flow_apply`.
* `exists_inverse_flow_apply` — the **explicit inverse flow map**: taking a companion flow family
  `Ψ` anchored at time `t` (from `exists_flow_family`), the map `ψ = fun w ↦ Ψ w t₀` is a two-sided
  inverse of `x ↦ Φ x t`, and being itself the time-`t₀` map of a flow family it is Lipschitz (with
  the exponential constant) and hence continuous.  This is the reverse-time flow.
* `exists_homeomorph_flow_apply` — the packaged statement that the time-`t` flow map underlies a
  `Homeomorph E E`.

Everything is proved sorry-free from Mathlib and the `SmoothDependenceCk` tower; no PDE or manifold
content is used.  The state space needs only `[CompleteSpace E]` (for the companion existence).
-/

open Set Filter Topology
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
variable {Φ : E → ℝ → E}

/-- **Surjectivity of the time-`t` flow map.**  For a flow family `Φ` of the uniformly
`K`-Lipschitz, time-continuous field `v` anchored at `Φ x t₀ = x`, every point `w` lies in the
image of `x ↦ Φ x t`.  Indeed the integral curve `γ` through `w` at time `t` (from
`exists_isIntegralCurve_of_lipschitzWith`) agrees at `t₀` with the anchored curve `Φ (γ t₀)`, so by
uniqueness (`eq_of_isIntegralCurve_of_eq_at`) they coincide, whence `Φ (γ t₀) t = γ t = w`. -/
theorem surjective_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Surjective (fun z => Φ z t) := by
  intro w
  obtain ⟨γ, hγt, hγcurve⟩ := exists_isIntegralCurve_of_lipschitzWith hv hvc t w
  refine ⟨γ t₀, ?_⟩
  have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (γ t₀)) hγcurve (h0 (γ t₀)) t
  show Φ (γ t₀) t = w
  rw [heq]; exact hγt

/-- **Bijectivity of the time-`t` flow map**, combining injectivity (`injective_flow_apply`) and
surjectivity (`surjective_flow_apply`). -/
theorem bijective_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Bijective (fun z => Φ z t) :=
  ⟨injective_flow_apply hv hΦ h0 t, surjective_flow_apply hv hvc hΦ h0 t⟩

/-- **Explicit two-sided inverse (reverse-time flow) of the time-`t` flow map.**  From a companion
flow family `Ψ` anchored at time `t` (produced by `exists_flow_family`), the reverse map
`ψ = fun w ↦ Ψ w t₀` is a two-sided inverse of `x ↦ Φ x t` and, being itself the time-`t₀` map of a
flow family, is Lipschitz with constant `exp (K · |t₀ - t|)` (hence continuous).

The inverse identities are pure uniqueness of integral curves: `Ψ (Φ z t)` agrees with `Φ z` at
time `t`, so at `t₀` we get `ψ (Φ z t) = Φ z t₀ = z`; symmetrically `Φ (Ψ w t₀)` agrees with `Ψ w` at
`t₀`, so at `t` we get `Φ (ψ w) t = Ψ w t = w`. -/
theorem exists_inverse_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
      Function.RightInverse ψ (fun z => Φ z t) ∧
      LipschitzWith (Real.exp ((K : ℝ) * |t₀ - t|)).toNNReal ψ := by
  obtain ⟨Ψ, hΨ0, hΨcurve⟩ := exists_flow_family (t₀ := t) hv hvc
  refine ⟨fun w => Ψ w t₀, ?_, ?_, ?_⟩
  · -- LeftInverse: ψ (Φ z t) = z
    intro z
    have hagree : Ψ (Φ z t) t = Φ z t := hΨ0 (Φ z t)
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΨcurve (Φ z t)) (hΦ z) hagree t₀
    show Ψ (Φ z t) t₀ = z
    rw [heq]; exact h0 z
  · -- RightInverse: Φ (ψ w) t = w
    intro w
    have hagree : Φ (Ψ w t₀) t₀ = Ψ w t₀ := h0 (Ψ w t₀)
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (Ψ w t₀)) (hΨcurve w) hagree t
    show Φ (Ψ w t₀) t = w
    rw [heq]; exact hΨ0 w
  · -- ψ is the time-`t₀` map of the family `Ψ` anchored at `t`, hence Lipschitz
    exact lipschitzWith_flow_apply (Φ := Ψ) (t₀ := t) hv hΨcurve hΨ0 t₀

/-- **The time-`t` flow map underlies a self-homeomorphism** of the state space.  Bundles the
bijectivity (`bijective_flow_apply`), the continuity of the flow map (`continuous_flow_apply`), and
the continuity of the reverse-time flow (`exists_inverse_flow_apply`) into a `Homeomorph E E` whose
coercion is `x ↦ Φ x t`.  This is the ambient-topological skeleton of the self-diffeomorphism family
consumed by the compact-manifold gauge flow of Item 2. -/
theorem exists_homeomorph_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    ∃ e : Homeomorph E E, ⇑e = fun z => Φ z t := by
  obtain ⟨ψ, hleft, hright, hψlip⟩ := exists_inverse_flow_apply hv hvc hΦ h0 t
  refine ⟨{ toFun := fun z => Φ z t
            invFun := ψ
            left_inv := hleft
            right_inv := hright
            continuous_toFun := continuous_flow_apply hv hΦ h0 t
            continuous_invFun := hψlip.continuous }, rfl⟩

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
