module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceManifold

/-!
# Field-jet extraction from a jointly-`ContDiff` time-dependent field (roadmap point 4, Item 2)

The Banach → manifold smooth-dependence tower (`AnalyticPDE/SmoothDependenceCk`,
`AnalyticPDE/FlowDiffeomorphism`, `AnalyticPDE/SmoothDependenceManifold`,
`AnalyticPDE/ModelManifoldGaugeFlow`) drives the `C³` gauge flow of Item 2 from a **field jet**:
the spatial Fréchet derivatives `Dv`, `D²v`, `D³v` of the time-dependent field `v : ℝ → E → E`,
supplied as separate objects with pointwise `HasFDerivAt`, joint `(t, x)`-continuity, and global
Lipschitz bounds.

Those jet hypotheses are stated abstractly so the tower is agnostic to how the derivatives arise.
This module supplies the honest bridge from a *single* clean smoothness hypothesis — `v` jointly
`ContDiff` in `(time, space)` (`ContDiff ℝ n (Function.uncurry v)`) — to the **first jet layer**:

* `contDiff_apply_of_contDiff_uncurry` — each time slice `v s` is spatially `ContDiff ℝ n`;
* `hasFDerivAt_fderiv_of_contDiff_uncurry` — the spatial derivative object `fderiv ℝ (v s)` is a
  genuine Fréchet derivative of `v s` at every point (`1 ≤ n`);
* `continuous_fderiv_of_contDiff_uncurry` — the spatial derivative is jointly continuous in `(t, x)`,
  via the partial-derivative identity `fderiv ℝ (v t) x = fderiv ℝ (uncurry v) (t, x) ∘L inr`.

Together these produce exactly the `hDv`/`hDvc` inputs of the tower's flow theorems (`Dv := fun s ↦
fderiv ℝ (v s)`).  No new analytic content: a transport of Mathlib's `ContDiff` calculus into the
jet shape the smooth-dependence tower consumes.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

@[expose] public section

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {n : WithTop ℕ∞}

/-- Each time slice `v s` of a jointly-`ContDiff` field is spatially `ContDiff ℝ n`, obtained by
precomposing `Function.uncurry v` with the affine inclusion `x ↦ (s, x)`. -/
theorem contDiff_apply_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (s : ℝ) :
    ContDiff ℝ n (v s) := by
  have hcomp : ContDiff ℝ n (Function.uncurry v ∘ fun x : E => (s, x)) :=
    h.comp (contDiff_prodMk_right s)
  have heq : (Function.uncurry v ∘ fun x : E => (s, x)) = v s := by funext x; rfl
  rwa [heq] at hcomp

/-- The spatial derivative object `fderiv ℝ (v s)` is a genuine Fréchet derivative of the time slice
`v s` at every point, for a jointly-`ContDiff` field with `1 ≤ n`.  This is the `hDv` input of the
smooth-dependence tower with `Dv := fun s ↦ fderiv ℝ (v s)`. -/
theorem hasFDerivAt_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (v s) (fderiv ℝ (v s) ξ) ξ :=
  (((contDiff_apply_of_contDiff_uncurry h s).differentiable
    ((lt_of_lt_of_le zero_lt_one hn).ne')).differentiableAt).hasFDerivAt

/-- **Joint `(t, x)`-continuity of the spatial derivative** of a jointly-`ContDiff` field
(`1 ≤ n`).  The partial spatial derivative equals the full joint derivative postcomposed with the
inclusion `inr : E →L[ℝ] ℝ × E`, `fderiv ℝ (v t) x = fderiv ℝ (Function.uncurry v) (t, x) ∘L inr`,
and both `p ↦ fderiv ℝ (uncurry v) p` and right-composition with the fixed `inr` are continuous.
This is the `hDvc` input of the smooth-dependence tower. -/
theorem continuous_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (v p.1) p.2) := by
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have key : (fun p : ℝ × E => fderiv ℝ (v p.1) p.2)
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (v p.1)
        ((fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry v ∘ fun x : E => (p.1, x)) = v p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact (h.continuous_fderiv hne).clm_comp continuous_const

/-- **Global Lipschitz bound on the spatial derivative from a second-derivative bound.**  If `v` is
jointly `ContDiff ℝ n` with `2 ≤ n` and the second spatial derivative `fderiv ℝ (fderiv ℝ (v s))` is
globally bounded in operator norm by `L`, then the spatial derivative object `fderiv ℝ (v s)` is
`L`-Lipschitz.  This is the `hDvlip` input of the smooth-dependence tower, obtained from the
mean-value bound `lipschitzWith_of_nnnorm_fderiv_le` together with differentiability of the derivative
(`ContDiff.fderiv_right`). -/
theorem lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    {L : ℝ≥0} (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L) (s : ℝ) :
    LipschitzWith L (fderiv ℝ (v s)) := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_num) hn
  have hdiff : Differentiable ℝ (fderiv ℝ (v s)) :=
    (hvs.fderiv_right (m := 1) hmn).differentiable one_ne_zero
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff (hL s)

/-- **Manifold spatial `C¹` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
field-jet extraction with the tower's `C^{1,1}` manifold regularity theorem
`contMDiff_one_flow_apply_of_lipschitz_deriv`: for a jointly-`ContDiff ℝ n` field `v` (`2 ≤ n`) that
is spatially `K`-Lipschitz and time-continuous, with a globally bounded second spatial derivative, any
integral-curve flow family `Φ` of `v` anchored at `t₀` has each time-`t` map `z ↦ Φ z t` in
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1`.  The field-jet hypotheses `hDv`/`hDvc`/`hDvlip` are supplied here from
the single `ContDiff` hypothesis via `hasFDerivAt_fderiv_of_contDiff_uncurry`,
`continuous_fderiv_of_contDiff_uncurry`, and
`lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le`; this is the first flow-regularity
statement in the tower stated purely in terms of joint `ContDiff` of the field. -/
theorem contMDiff_one_flow_apply_of_contDiff [CompleteSpace E]
    {K L : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_one_flow_apply_of_lipschitz_deriv (Dv := fun s => fderiv ℝ (v s))
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    (fun s => lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le h hn hL s)
    hΦ h0 t

/-- **Spatial Lipschitz bound of the field from a first-derivative bound.**  If `v` is jointly
`ContDiff ℝ n` with `1 ≤ n` and the spatial derivative `fderiv ℝ (v s)` is globally bounded in
operator norm by `K`, then each time slice `v s` is `K`-Lipschitz.  Supplies the `hv` input from a
derivative bound (via `lipschitzWith_of_nnnorm_fderiv_le`). -/
theorem lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n)
    {K : ℝ≥0} (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K) (s : ℝ) :
    LipschitzWith K (v s) := by
  have hdiff : Differentiable ℝ (v s) :=
    (contDiff_apply_of_contDiff_uncurry h s).differentiable ((lt_of_lt_of_le zero_lt_one hn).ne')
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff (hK s)

/-- **Time-continuity of the field slice** from joint `ContDiff`: for each `x`, `s ↦ v s x` is
continuous, since it is `Function.uncurry v` (continuous) precomposed with `s ↦ (s, x)`.  Supplies the
`hvc` input. -/
theorem continuous_apply_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (x : E) :
    Continuous (fun s : ℝ => v s x) := by
  have heq : (fun s : ℝ => v s x) = Function.uncurry v ∘ fun s : ℝ => (s, x) := by
    funext s; rfl
  rw [heq]
  exact h.continuous.comp (continuous_id.prodMk continuous_const)

/-- **Manifold spatial `C¹` regularity of the flow from joint `ContDiff` and derivative bounds
alone.**  The fully self-contained form of `contMDiff_one_flow_apply_of_contDiff`: from `v` jointly
`ContDiff ℝ n` (`2 ≤ n`) with globally bounded first and second spatial derivatives (bounds `K`, `L`),
plus an integral-curve flow family `Φ` anchored at `t₀`, each time-`t` map `z ↦ Φ z t` is
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1`.  The spatial Lipschitz and time-continuity inputs are here also
discharged from the `ContDiff` hypothesis (`lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le`,
`continuous_apply_of_contDiff_uncurry`), so the field is described by a single smoothness hypothesis
and two derivative bounds. -/
theorem contMDiff_one_flow_apply_of_contDiff_of_bddDerivs [CompleteSpace E]
    {K L : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_one_flow_apply_of_contDiff h hn
    (fun τ => lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le h hn1 hK τ)
    (fun x => continuous_apply_of_contDiff_uncurry h x)
    hL hΦ h0 t

/-! ## Layer-2 field-jet extraction (`C²` flow regularity from a single `ContDiff` hypothesis)

The layer-1 lemmas above fix the field codomain as `E`.  To iterate the jet extraction one derivative
order higher we re-apply them to the derivative field `fun s ↦ fderiv ℝ (v s) : ℝ → E → (E →L[ℝ] E)`,
whose codomain is `E →L[ℝ] E`, not `E`.  So we first record codomain-general (`'`) forms of the two
layer-1 building blocks, then assemble the second-jet inputs `hD2v`/`hD2vc`/`hD2vlip` of the tower's
`C²` flow theorem `contMDiff_two_flow_apply_of_lipschitz_secondDeriv` from a single joint-`ContDiff`
hypothesis plus global spatial second/third-derivative bounds. -/

/-- **Codomain-general joint `(t, x)`-continuity of the spatial derivative.**  The codomain-general
form of `continuous_fderiv_of_contDiff_uncurry`: for a jointly-`ContDiff ℝ n` field `w : ℝ → E → F`
(`1 ≤ n`) the spatial derivative `fderiv ℝ (w t) x` is jointly continuous, via the partial-derivative
identity `fderiv ℝ (w t) x = fderiv ℝ (uncurry w) (t, x) ∘L inr`.  This enables iterating the field-jet
extraction to the next derivative order (the derivative field takes values in `E →L[ℝ] E`, not `E`). -/
theorem continuous_fderiv_of_contDiff_uncurry' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ → E → F} (h : ContDiff ℝ n (Function.uncurry w)) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (w p.1) p.2) := by
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have key : (fun p : ℝ × E => fderiv ℝ (w p.1) p.2)
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (w p.1)
        ((fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry w ∘ fun x : E => (p.1, x)) = w p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact (h.continuous_fderiv hne).clm_comp continuous_const

/-- **The layer-1 spatial-derivative field of a jointly-`ContDiff` field is itself jointly `ContDiff`
one order lower.**  If `w : ℝ → E → F` has `ContDiff ℝ n (uncurry w)` and `m + 1 ≤ n`, then
`uncurry (fun s ↦ fderiv ℝ (w s))` is `ContDiff ℝ m`, because it equals `fderiv ℝ (uncurry w)`
post-composed with the fixed inclusion `inr` (a bounded linear, hence `ContDiff`, map).  This is the
inductive step that lets the field-jet extraction recurse: apply the layer-1 lemmas to the derivative
field `fderiv ℝ (w ·)` to obtain the layer-2 jet. -/
theorem contDiff_uncurry_fderiv_of_contDiff_uncurry' {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w : ℝ → E → F} {m : WithTop ℕ∞}
    (h : ContDiff ℝ n (Function.uncurry w)) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun s => fderiv ℝ (w s))) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (self_le_add_left 1 m) hmn
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn1).ne'
  have key : Function.uncurry (fun s => fderiv ℝ (w s))
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (w p.1)
        ((fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry w ∘ fun x : E => (p.1, x)) = w p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact ContDiff.clm_comp (h.fderiv_right hmn) contDiff_const

/-- **Second spatial derivative exists as a genuine Fréchet derivative** (`2 ≤ n`).  The first spatial
derivative `fderiv ℝ (v s)` is itself `ContDiff ℝ 1`, hence differentiable, so `fderiv ℝ (fderiv ℝ
(v s)) ξ` is a genuine Fréchet derivative of `fderiv ℝ (v s)` at every point.  This is the `hD2v` input
of the tower's `C²` flow theorem `contMDiff_two_flow_apply_of_lipschitz_secondDeriv`. -/
theorem hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (fderiv ℝ (v s)) (fderiv ℝ (fderiv ℝ (v s)) ξ) ξ := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_num) hn
  have hdiff : Differentiable ℝ (fderiv ℝ (v s)) :=
    (hvs.fderiv_right (m := 1) hmn).differentiable one_ne_zero
  exact (hdiff ξ).hasFDerivAt

/-- **Joint `(t, x)`-continuity of the second spatial derivative** (`2 ≤ n`), obtained by applying the
codomain-general layer-1 continuity lemma `continuous_fderiv_of_contDiff_uncurry'` to the layer-1
derivative field `fderiv ℝ (v ·)`, which is itself jointly `ContDiff ℝ 1` by
`contDiff_uncurry_fderiv_of_contDiff_uncurry'`.  This is the `hD2vc` input of the tower's `C²` flow
theorem. -/
theorem continuous_fderiv_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (v p.1)) p.2) := by
  have hV : ContDiff ℝ (1 : WithTop ℕ∞) (Function.uncurry (fun s => fderiv ℝ (v s))) :=
    contDiff_uncurry_fderiv_of_contDiff_uncurry' h (le_trans (by norm_num) hn)
  exact continuous_fderiv_of_contDiff_uncurry' hV le_rfl

/-- **Manifold spatial `C²` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
layer-1 + layer-2 field-jet extraction with the tower's `C^{2,1}` manifold regularity theorem
`contMDiff_two_flow_apply_of_lipschitz_secondDeriv`: for a jointly-`ContDiff ℝ n` field `v` (`2 ≤ n`)
that is spatially `K`-Lipschitz and time-continuous, with a globally bounded second spatial derivative
(bound `L`) and an `M`-Lipschitz second spatial-derivative field, any integral-curve flow family `Φ`
anchored at `t₀` has each time-`t` map `z ↦ Φ z t` in `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2`.  The layer-1 jet
inputs `hDv`/`hDvc`/`hDvlip` and the second-jet inputs `hD2v`/`hD2vc` are supplied here from the single
`ContDiff` hypothesis; the top-order Lipschitz control `hD2vlip` is supplied directly (matching the
tower's own `C²` theorem), so no third-order derivative object is required.  This is the second
flow-regularity statement in the tower stated in terms of joint `ContDiff` of the field. -/
theorem contMDiff_two_flow_apply_of_contDiff [CompleteSpace E]
    {K L M : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hD2vlip : ∀ s, LipschitzWith M (fderiv ℝ (fderiv ℝ (v s))))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_two_flow_apply_of_lipschitz_secondDeriv
    (Dv := fun s => fderiv ℝ (v s)) (D2v := fun s => fderiv ℝ (fderiv ℝ (v s)))
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    (fun s => lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le h hn hL s)
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn)
    hD2vlip
    hΦ h0 t

/-- **Manifold spatial `C²` regularity of the flow from joint `ContDiff` and a first-derivative bound.**
The convenience form of `contMDiff_two_flow_apply_of_contDiff` that discharges the spatial Lipschitz
(`hv`) and time-continuity (`hvc`) inputs from the `ContDiff` hypothesis together with a global
first-derivative bound (`hK`), matching the layer-1 `contMDiff_one_flow_apply_of_contDiff_of_bddDerivs`
API: from `v` jointly `ContDiff ℝ n` (`2 ≤ n`) with a globally bounded first and second spatial
derivative (bounds `K`, `L`) and an `M`-Lipschitz second spatial-derivative field, each time-`t` flow
map `z ↦ Φ z t` is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2`.  The top-order Lipschitz control `hD2vlip` is
supplied directly, since expressing it as a third-derivative bound would require the multilinear
(rather than iterated-`fderiv`) representation of the third jet. -/
theorem contMDiff_two_flow_apply_of_contDiff_of_bddDerivs [CompleteSpace E]
    {K L M : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hD2vlip : ∀ s, LipschitzWith M (fderiv ℝ (fderiv ℝ (v s))))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_two_flow_apply_of_contDiff h hn
    (fun τ => lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le h hn1 hK τ)
    (fun x => continuous_apply_of_contDiff_uncurry h x)
    hL hD2vlip hΦ h0 t

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
