/-
Gauge-flow assembly toward the compact-manifold C³ gauge-flow existence
(roadmap point 4, Item 2).

This module re-exposes the project's raw `C³` gauge-flow adapter
`Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt` in a clean form,
isolating the exact data needed to inhabit `Diffeomorph3GaugeFlowOn`:

* mutually inverse, spatially-`C³` time-slice maps `F`, `G : ℝ → M → M`
  (`G t` is the spatial inverse of the diffeomorphism `F t`, NOT a backward
  time-flow — confirmed by the adapter's per-slice `LeftInverse`/`RightInverse`
  hypotheses);
* anchoring `F t₀ = id`;
* the forward family `τ ↦ F τ x` solving the gauge ODE
  (`HasMFDerivWithinAt … ((1).smulRight (X t (F t x)))`).

The `hderiv` field is exactly the manifold time-derivative that the autonomization
bridge in `ManifoldFlowExistence.lean`
(`isTimeDependentIntegralCurve_of_autonomous`) produces from an integral curve of
`(1, X)` on `ℝ × M`. The mutual-inverse data follows from the flow group law
(`flow_inverse_package`). The single genuinely-remaining analytic obligation is the
**spatial `C³` regularity of the flow map** `x ↦ F t x` (smooth dependence of the
ODE flow on the initial condition, `hF`/`hG`) — the project's `ModelGaugeFlowODE.lean`
already proves spatial `C¹` (Fréchet) differentiability, so this is a `C¹ → C³`
bootstrap, not a from-scratch development.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ManifoldFlowExistence

open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- **Gauge-flow from flow data.** Given mutually inverse spatially-`C³` time-slice
maps `F`, `G`, anchoring at `t₀`, and the pointwise within-time-set manifold ODE
derivative equation for the forward family, the raw `C³` DeTurck gauge-flow
`Diffeomorph3GaugeFlowOn` is inhabited.

This is the reduction target for Item 2: with the autonomization bridge supplying
`hderiv` and the flow group law supplying the mutual inverses, the only remaining
input is the spatial-`C³` regularity `hF`/`hG` of the flow map. -/
theorem gaugeFlow_of_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hderiv

/-- **Global-`ℝ` extension of a windowed inverse flow to the `C³` gauge-flow datum.**

The compact-manifold time-dependent flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`) produces mutually inverse, anchored
slice maps `Φ`, `G` solving the gauge ODE only on a *window* `Ioo (-ε) ε`, whereas the adapter
`gaugeFlow_of_inverse_flow` wants the mutual-inverse / spatial-`C³` data for *every* `t : ℝ`.
Extending both families by the identity outside the window closes that `∀ t`-gap: the extended
slices stay mutually inverse (`id` is its own inverse), spatially `C³` (`id` is smooth), anchored,
and — since the extension agrees with `Φ` on the window — solve the *same* gauge ODE on
`Ioo (-ε) ε` (`HasMFDerivWithinAt.congr_mono`).  This is the pure windowed → global assembly step
in the compact-manifold gauge-flow lift; the only remaining Item-2 analytic input is the
spatial-`C³` regularity `hΦC3`/`hGC3` of the *windowed* slices (the `C¹ → C³` bootstrap). -/
theorem exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {ε : ℝ} (hε : 0 < ε)
    (Φ G : ℝ → M → M)
    (hanchor : ∀ x : M, Φ 0 x = x)
    (hΦC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (Φ t))
    (hGC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (G t))
    (hleft : ∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t))
    (hright : ∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t))
    (hderiv : ∀ x : M, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  classical
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  refine gaugeFlow_of_inverse_flow (X := X) (s := Set.Ioo (-ε) ε) (t₀ := 0)
    (fun t => if t ∈ Set.Ioo (-ε) ε then Φ t else id)
    (fun t => if t ∈ Set.Ioo (-ε) ε then G t else id)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hleft t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hright t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hΦC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hGC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro x
    simp only [if_pos h0mem]; exact hanchor x
  · intro t ht x
    simp only []
    rw [if_pos ht]
    refine (hderiv x t ht).congr_mono ?_ ?_ (subset_refl _)
    · intro τ hτ; simp only [if_pos hτ]
    · simp only [if_pos ht]

/-- **Compact-manifold gauge-flow existence, reduced to spatial-`C³` regularity of the flow slices.**

Wires the compact-manifold time-dependent flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`, which only needs the `C¹` field datum
`hX`) into the raw `C³` gauge-flow adapter through the identity-extension assembly
`exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow`.  The flow supplies, on some window
`Ioo (-ε) ε`, the anchored mutually-inverse slice maps `Φ`, `G` solving the gauge ODE; the *only*
remaining analytic input is their spatial-`C³` regularity, isolated here as the hypothesis
`hslicesC3` (the `C¹ → C³` bootstrap, characterising the — necessarily unique — compact flow of `X`).
Given that, the raw `C³` DeTurck gauge-flow `Diffeomorph3GaugeFlowOn X (Ioo (-ε) ε) 0` is inhabited
for some `ε > 0`.  This is the first wiring of the compact-flow existence machinery into the
gauge-flow adapter — the honest current state of Item 2: *unconditional up to the flow-slice `C³`
regularity*. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hslicesC3 : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (Φ t)) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (G t))) :
    ∃ ε > 0, Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  obtain ⟨ε, hε, Φ, G, hΦ0, _hG0, hderiv, hleft, hright⟩ :=
    ManifoldFlow.exists_timeDependent_flow_compact_inverse (I := I) (M := M) (X := X) hX
  obtain ⟨hΦC3, hGC3⟩ := hslicesC3 ε hε Φ G hΦ0 hderiv hleft hright
  exact ⟨ε, hε, exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    hε Φ G hΦ0 hΦC3 hGC3 hleft hright hderiv⟩

/-- **Chart-conjugation `C³` transfer for a flow slice.**  If, on an open set `U` contained in the
source chart at `x₀`, the map `F` is represented in the extended charts at `x₀` (source) and `F x₀`
(target) by a globally `C³` model map `Ψ : E → E` — i.e.
`extChartAt I (F x₀) (F x) = Ψ (extChartAt I x₀ x)` for every `x ∈ U` — and `F` maps `U` into the
source chart at `F x₀`, then `F` is `ContMDiffOn I I 3` on `U`.

This is the manifold-level `C³` regularity transfer for a flow slice: the model-manifold
smooth-dependence tower (`SmoothDependenceManifold.exists_flow_diffeomorph_three` etc.) produces a
globally `C³` chart-local flow `Ψ`, and this lemma lifts that `C³` regularity to `ContMDiffOn I I 3`
of the genuine manifold flow slice on a chart-confined patch — exactly the
`forward_contMDiffOn`/`backward_contMDiffOn` field of `LocalGluingData 3` the compact gauge-flow
gluing route (`Diffeomorph3FlowExistence.exists_Ioo_gaugeFlow_…_localGluingData_…`) consumes.  The
proof factors `F` as `(extChartAt I (F x₀)).symm ∘ Ψ ∘ (extChartAt I x₀)` on `U` (using the chart
left-inverse identity) and composes the two `ContMDiffOn` chart maps with the globally-`C³` `Ψ`. -/
theorem contMDiffOn_of_extChartAt_conjugation
    {x₀ : M} {F : M → M} {U : Set M} {Ψ : E → E}
    (hU : U ⊆ (chartAt H x₀).source)
    (hΨ : ContDiff ℝ 3 Ψ)
    (hFU : Set.MapsTo F U (chartAt H (F x₀)).source)
    (hconj : ∀ x ∈ U, extChartAt I (F x₀) (F x) = Ψ (extChartAt I x₀ x)) :
    ContMDiffOn I I 3 F U := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) 3 (extChartAt I x₀) U :=
    (contMDiffOn_extChartAt (I := I) (n := 3) (x := x₀)).mono hU
  have hΨm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 Ψ := contMDiff_iff_contDiff.mpr hΨ
  have hmid : ContMDiffOn I 𝓘(ℝ, E) 3 (fun x => Ψ (extChartAt I x₀ x)) U :=
    hΨm.comp_contMDiffOn hchart
  have hmaps : Set.MapsTo (fun x => Ψ (extChartAt I x₀ x)) U (extChartAt I (F x₀)).target := by
    intro x hx
    show Ψ (extChartAt I x₀ x) ∈ (extChartAt I (F x₀)).target
    rw [← hconj x hx]
    exact PartialEquiv.map_source (extChartAt I (F x₀))
      (by rw [extChartAt_source]; exact hFU hx)
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I 3 (extChartAt I (F x₀)).symm
      (extChartAt I (F x₀)).target := contMDiffOn_extChartAt_symm (F x₀)
  have hcomp : ContMDiffOn I I 3
      (fun x => (extChartAt I (F x₀)).symm (Ψ (extChartAt I x₀ x))) U :=
    hsymm.comp hmid hmaps
  refine hcomp.congr (fun x hx => ?_)
  show F x = (extChartAt I (F x₀)).symm (Ψ (extChartAt I x₀ x))
  rw [← hconj x hx]
  exact (PartialEquiv.left_inv (extChartAt I (F x₀))
    (by rw [extChartAt_source]; exact hFU hx)).symm

/-- **`LocalGluingData 3` from chart-conjugation data.**  Packages the two chart-conjugation `C³`
transfers (`contMDiffOn_of_extChartAt_conjugation`, applied to the forward slice `F` and its local
inverse `G`) together with the mutual-inverse / mapping data into the exact
`RicciFlow.LocalGluingData 3 F G U V` structure the compact gauge-flow gluing theorems
(`Diffeomorph3FlowExistence.exists_…_gaugeFlow_…_localGluingData_…`) consume as their per-chart
`hlocal` hypothesis.

The two genuinely-analytic fields (`forward_contMDiffOn`/`backward_contMDiffOn`) are discharged by the
chart-conjugation transfer from globally-`C³` model representatives `ΨF`, `ΨG` (supplied by the
model-manifold smooth-dependence tower in each chart); the remaining fields are the topological
open-ness, the mapping, and the local mutual-inverse identities, which the flow group law provides. -/
theorem localGluingData_ofChartConjugation
    {F G : M → M} {U V : Set M} {xF xG : M} {ΨF ΨG : E → E}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hFmaps : Set.MapsTo F U V) (hGmaps : Set.MapsTo G V U)
    (hleft : Set.LeftInvOn G F U) (hright : Set.RightInvOn G F V)
    (hUF : U ⊆ (chartAt H xF).source) (hΨF : ContDiff ℝ 3 ΨF)
    (hFchart : Set.MapsTo F U (chartAt H (F xF)).source)
    (hconjF : ∀ x ∈ U, extChartAt I (F xF) (F x) = ΨF (extChartAt I xF x))
    (hVG : V ⊆ (chartAt H xG).source) (hΨG : ContDiff ℝ 3 ΨG)
    (hGchart : Set.MapsTo G V (chartAt H (G xG)).source)
    (hconjG : ∀ x ∈ V, extChartAt I (G xG) (G x) = ΨG (extChartAt I xG x)) :
    LocalGluingData (I := I) (M := M) 3 F G U V where
  source_open := hUopen
  target_open := hVopen
  forward_mapsTo := by simpa only [Set.univ_inter] using hFmaps
  backward_mapsTo := by simpa only [Set.univ_inter] using hGmaps
  forward_contMDiffOn := contMDiffOn_of_extChartAt_conjugation hUF hΨF hFchart hconjF
  backward_contMDiffOn := contMDiffOn_of_extChartAt_conjugation hVG hΨG hGchart hconjG
  left_invOn := by simpa only [Set.univ_inter] using hleft
  right_invOn := by simpa only [Set.univ_inter] using hright

/-- **Global slice `C³` regularity from per-point chart-conjugation.**  If every point `x : M` has a
neighbourhood `U` on which the map `F` is represented, in the extended charts at some centre `x₀`
(source) and `F x₀` (target), by a globally-`C³` model map `Ψ : E → E`, then `F` is globally
`ContMDiff I I 3`.

This is the `ContMDiff I I 3 (Φ t)` content of the compact gauge-flow reduction's `hslicesC3`
hypothesis (`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`): each
flow slice `Φ t : M → M` is, near every point, the chart-representation of a model `C³` flow supplied
by the smooth-dependence tower, and this lemma glues those local chart-conjugation witnesses into
global spatial `C³` regularity of the slice.  `ContMDiff` unfolds to `∀ x, ContMDiffAt`, each of which
is `contMDiffOn_of_extChartAt_conjugation` restricted to the neighbourhood via
`ContMDiffOn.contMDiffAt`. -/
theorem contMDiff_of_forall_extChartAt_conjugation
    {F : M → M}
    (h : ∀ x : M, ∃ (x₀ : M) (U : Set M) (Ψ : E → E),
      U ∈ 𝓝 x ∧ U ⊆ (chartAt H x₀).source ∧ ContDiff ℝ 3 Ψ ∧
      Set.MapsTo F U (chartAt H (F x₀)).source ∧
      (∀ y ∈ U, extChartAt I (F x₀) (F y) = Ψ (extChartAt I x₀ y))) :
    ContMDiff I I 3 F := by
  intro x
  obtain ⟨x₀, U, Ψ, hUmem, hU, hΨ, hFU, hconj⟩ := h x
  exact (contMDiffOn_of_extChartAt_conjugation hU hΨ hFU hconj).contMDiffAt hUmem

end PoincareCurvature.GaugeFlowAssembly
