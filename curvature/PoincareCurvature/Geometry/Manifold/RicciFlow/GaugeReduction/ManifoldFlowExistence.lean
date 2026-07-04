/-
Manifold integral-curve existence scaffolding toward the compact-manifold
gauge-flow construction (roadmap point 4, Item 2).

This module assembles the mathlib integral-curve API into the exact shapes the
gauge-flow construction consumes:

* `exists_local_integralCurve_Ioo` — per-point local existence of an integral
  curve on an open interval `Ioo (-ε) ε`, in the precise shape the globalization
  lemma wants;
* `exists_perpoint_integralCurve_time` — the per-point existence time on a
  compact boundaryless manifold (each point gets its own `εₓ`);
* `exists_global_integralCurve_of_uniform` — globalization: a *uniform* existence
  time immediately yields a global integral curve through every point.

The remaining gap to a *uniform* existence time (a single `ε` for all start
points) is the manifold "flow box" — continuous dependence of integral curves on
the initial point. Mathlib v4.29.1 provides this only at the Banach-space level
(`PicardLindelof`), not lifted to the manifold `IsMIntegralCurveOn` API; supplying
that neighborhood-uniform local existence lemma is the precise next increment.
-/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open scoped Manifold Topology
open Set Filter

namespace PoincareCurvature.ManifoldFlow

/-- **Per-point local integral curve in `Ioo` shape.** For a `C¹` vector field `v`
on a boundaryless complete manifold, every point `x₀` admits some `ε > 0` and an
integral curve through `x₀` (at time `0`) on `Ioo (-ε) ε`. This is the exact shape
the globalization lemma `exists_isMIntegralCurve_of_isMIntegralCurveOn` consumes. -/
theorem exists_local_integralCurve_Ioo {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  obtain ⟨γ, hγ0, hγat⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) (x₀ := x₀) hv.contMDiffAt
  obtain ⟨ε, hε, hon⟩ := (isMIntegralCurveAt_iff').mp hγat
  refine ⟨ε, hε, γ, hγ0, ?_⟩
  rw [show Set.Ioo (-ε) ε = Metric.ball (0 : ℝ) ε by rw [Real.ball_eq_Ioo]; simp]
  exact hon

/-- **Per-point existence time on a compact boundaryless manifold.** Each point of
a compact boundaryless manifold admits an integral curve through it on its *own*
interval `Ioo (-εₓ) εₓ`. This is the strongest statement mathlib's local-existence
API supports directly; promoting it to a *uniform* `ε` requires the manifold flow
box (see the module docstring). -/
theorem exists_perpoint_integralCurve_time {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∀ x : M, ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) :=
  fun x => exists_local_integralCurve_Ioo hv x

/-- **Globalization.** A *uniform* existence time (a single `ε > 0` working for
every start point) immediately yields a global integral curve through every point,
by mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`. This isolates the
remaining obligation: prove the uniform-time hypothesis. -/
theorem exists_global_integralCurve_of_uniform {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (ε : ℝ) (hε : 0 < ε)
    (huniform : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
  exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε huniform x

/-- **Manifold flow box: neighborhood-uniform local existence.** For a `C¹` vector
field `v` on a boundaryless complete manifold, around every point `x₀` there is a
neighborhood `U` and a single `ε > 0` such that *every* start point `y ∈ U` admits
an integral curve through `y` on the common interval `Ioo (-ε) ε`.

This generalizes mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt` (a single
curve at one point) to all nearby start points sharing one time interval, by
lifting the continuous-flow Picard–Lindelöf theorem through a chart and using a
tube-lemma argument to keep the nearby curves inside the chart target. It is the
piece mathlib lacks (continuous dependence of integral curves on the initial point,
lifted to the manifold `IsMIntegralCurveOn` API). -/
theorem exists_nhds_uniform_integralCurve {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x₀ : M) :
    ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  have hc : extChartAt I x₀ x₀ ∈ interior (extChartAt I x₀).target := (I.isInteriorPoint_iff).mp hx
  have hvx := (hv x₀)
  rw [contMDiffAt_iff] at hvx
  obtain ⟨_, hvx⟩ := hvx
  have hF := hvx.contDiffAt (range_mem_nhds_isInteriorPoint hx) |>.snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hflow, hcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hgc : ContinuousOn (fun t => α (extChartAt I x₀ x₀, t)) (Icc (0 - ε) (0 + ε)) :=
    hcont.comp (by fun_prop) (fun t ht => ⟨Metric.mem_closedBall_self hr.le, ht⟩)
  have hg0 : ContinuousAt (fun t => α (extChartAt I x₀ x₀, t)) 0 :=
    hgc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hαc0 : α (extChartAt I x₀ x₀, (0 : ℝ)) ∈ interior (extChartAt I x₀).target := by
    have h0 := (hflow (extChartAt I x₀ x₀) (Metric.mem_closedBall_self hr.le)).1
    simp only at h0
    rw [show α (extChartAt I x₀ x₀, (0 : ℝ)) = extChartAt I x₀ x₀ from h0]
    exact hc
  have g0W : (fun t => α (extChartAt I x₀ x₀, t)) ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 (0 : ℝ) :=
    hg0.preimage_mem_nhds (isOpen_interior.mem_nhds hαc0)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp g0W
  set ε₁ := min δ ε / 2 with hε₁def
  have hminpos : 0 < min δ ε := lt_min hδ hε
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  have hε₁ltδ : ε₁ < δ := by
    rw [hε₁def]; have := min_le_left δ ε; linarith
  have hε₁ltε : ε₁ < ε := by
    rw [hε₁def]; have := min_le_right δ ε; linarith
  have htube : ∀ᶠ x in 𝓝 (extChartAt I x₀ x₀),
      ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := by
    apply IsCompact.eventually_forall_of_forall_eventually isCompact_Icc
    intro t htK
    have htIoo : t ∈ Ioo (0 - ε) (0 + ε) :=
      ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    have hSnhds : (Metric.ball (extChartAt I x₀ x₀) (↑r) ×ˢ Ioo (0 - ε) (0 + ε))
        ∈ 𝓝 (extChartAt I x₀ x₀, t) :=
      (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨Metric.mem_ball_self hr, htIoo⟩
    have hcontAt : ContinuousAt α (extChartAt I x₀ x₀, t) :=
      hcont.continuousAt (mem_of_superset hSnhds
        (Set.prod_mono Metric.ball_subset_closedBall Ioo_subset_Icc_self))
    have hαW : α (extChartAt I x₀ x₀, t) ∈ interior (extChartAt I x₀).target := by
      apply hsub
      rw [Real.ball_eq_Ioo]
      exact ⟨by have := htK.1; linarith, by have := htK.2; linarith⟩
    exact hcontAt.preimage_mem_nhds (isOpen_interior.mem_nhds hαW)
  have hUmem : (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)} ∈ 𝓝 x₀ :=
    (continuousAt_extChartAt x₀).preimage_mem_nhds
      (htube.and (Metric.ball_mem_nhds _ hr))
  refine ⟨(extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹'
      {x | (∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target) ∧
        x ∈ Metric.ball (extChartAt I x₀ x₀) (↑r)},
    Filter.inter_mem (extChartAt_source_mem_nhds x₀) hUmem, ε₁, hε₁pos, ?_⟩
  intro y hy
  set x := extChartAt I x₀ y with hxdef
  have hxball : x ∈ Metric.closedBall (extChartAt I x₀ x₀) (↑r) :=
    Metric.ball_subset_closedBall hy.2.2
  have hball2 : ∀ t ∈ Icc (-ε₁) ε₁, α (x, t) ∈ interior (extChartAt I x₀).target := hy.2.1
  set g : ℝ → E := fun s => α (x, s) with hgdef
  refine ⟨(extChartAt I x₀).symm ∘ g, ?_, ?_⟩
  · have h0 := (hflow x hxball).1
    simp only at h0
    show (extChartAt I x₀).symm (g 0) = y
    rw [hgdef]
    beta_reduce
    rw [show α (x, (0 : ℝ)) = x from h0, hxdef,
      PartialEquiv.left_inv _ hy.1]
  · intro t ht
    let xₜ : M := (extChartAt I x₀).symm (g t)
    have htIcc : t ∈ Icc (0 - ε) (0 + ε) :=
      ⟨by have := ht.1; linarith, by have := ht.2; linarith⟩
    have h : HasDerivAt g (x := t) <|
        fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
          (range I) (extChartAt I xₜ xₜ) (v xₜ) :=
      ((hflow x hxball).2 t htIcc).hasDerivAt (Icc_mem_nhds (by have := ht.1; linarith)
        (by have := ht.2; linarith))
    rw [← tangentCoordChange_def] at h
    have hf3 : g t ∈ interior (extChartAt I x₀).target :=
      hball2 t (Ioo_subset_Icc_self ht)
    have hf3' := mem_of_mem_of_subset hf3 interior_subset
    have hft1 := mem_preimage.mp <|
      mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
    have hft2 := mem_extChartAt_source (I := I) xₜ
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) (v xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
      ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
      mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hf3⟩
    rw [← (extChartAt I x₀).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- **Uniform existence time from the flow box and compactness.** On a compact
manifold, the neighborhood-uniform flow box yields a single `ε > 0` working for
*every* start point, by extracting a finite subcover and taking the minimum
lifespan. -/
theorem exists_uniform_time_of_nhds_uniform {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [CompactSpace M]
    {v : (x : M) → TangentSpace I x}
    (hbox : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧
      IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  choose U hUmem ε hεpos hprop using hbox
  have hopen : ∀ x : M, ∃ t, t ⊆ U x ∧ IsOpen t ∧ x ∈ t := fun x => mem_nhds_iff.mp (hUmem x)
  choose V hVsub hVopen hVmem using hopen
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen
    (fun x _ => mem_iUnion.mpr ⟨x, hVmem x⟩)
  rcases t.eq_empty_or_nonempty with hte | htne
  · subst hte
    refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x ∈ (∅ : Set M) := by
      have h := ht (mem_univ x); simp at h
    exact absurd hx (notMem_empty x)
  · refine ⟨t.inf' htne ε, ?_, fun x => ?_⟩
    · exact (Finset.lt_inf'_iff htne).mpr (fun i _ => hεpos i)
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
      obtain ⟨γ, hγ0, hγon⟩ := hprop i x (hVsub i hxi)
      refine ⟨γ, hγ0, hγon.mono ?_⟩
      have hle : t.inf' htne ε ≤ ε i := Finset.inf'_le ε hi
      exact Ioo_subset_Ioo (by linarith) hle

/-- **Uniform existence time on a compact boundaryless manifold.** For a `C¹` vector
field `v` on a compact boundaryless complete manifold, there is a single `ε > 0`
such that every point admits an integral curve through it on `Ioo (-ε) ε`. Combines
the flow box with the compactness reduction. -/
theorem exists_uniform_integralCurve_time {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) :=
  exists_uniform_time_of_nhds_uniform (fun x₀ => exists_nhds_uniform_integralCurve hv x₀)

/-- **Global integral curves on a compact boundaryless manifold.** For a `C¹` vector
field on a compact boundaryless complete manifold, every point lies on a *global*
integral curve. This is the assembled flow-existence result the gauge-flow
construction needs: flow box ⇒ uniform time ⇒ globalization. -/
theorem exists_global_integralCurve_compact {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_integralCurve_time hv
  exact exists_global_integralCurve_of_uniform hv ε hε huniform x

/-! ### Time-dependent integral curves via autonomization

A *time-dependent* field `X : ℝ → (x : M) → TangentSpace I x` is integrated by
autonomizing: on the product manifold `ℝ × M`, the *autonomous* field
`(s, x) ↦ (1, X s x)` has integral curves whose first coordinate tracks the time
parameter, so projecting to `M` yields a time-dependent integral curve. The product
tangent space splits definitionally,
`TangentSpace (𝓘(ℝ,ℝ).prod I) (s, x) = ℝ × TangentSpace I x`, so the two fiber
components are handled independently. -/

/-- **Autonomization projection.** An integral curve `Γ` of the autonomous field
`(1, X · ·)` on `ℝ × M` whose first coordinate is the identity (`(Γ t).1 = t`)
projects, via the second coordinate, to a *time-dependent* integral curve of `X` on
`M`: `∂ₜ (Γ ·).2 = X t (Γ t).2`. -/
theorem isTimeDependentIntegralCurve_of_autonomous {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hfst : ∀ t ∈ s, (Γ t).1 = t)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => (Γ τ).2) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2))) := by
  intro t ht
  have hsnd : HasMFDerivAt ((𝓘(ℝ, ℝ)).prod I) I Prod.snd (Γ t)
      (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ t).1) (TangentSpace I (Γ t).2)) :=
    hasMFDerivAt_snd (Γ t)
  have hcomp := hsnd.comp_hasMFDerivWithinAt t (hΓ t ht)
  have hfun : (Prod.snd ∘ Γ) = (fun τ => (Γ τ).2) := rfl
  rw [hfun] at hcomp
  have hclm : (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ t).1)
        (TangentSpace I (Γ t).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))
      = (1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2)) := by
    ext
    simp [hfst t ht]
  exact hclm ▸ hcomp

/-- **The time component tracks the parameter.** An integral curve `Γ` of the
autonomous field `(1, X · ·)` on `ℝ × M` over a preconnected open set `s ∋ 0`, with
`(Γ 0).1 = 0`, has `(Γ t).1 = t` throughout `s` — because its first coordinate has
constant derivative `1`. -/
theorem autonomous_fst_eq_id {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = 0)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, (Γ t).1 = t := by
  set φ : ℝ → ℝ := fun τ => (Γ τ).1 with hφ
  have hd : ∀ τ ∈ s, HasDerivWithinAt φ 1 s τ := by
    intro τ hτ
    have hcomp :=
      ((hasMFDerivAt_fst (Γ τ)).hasMFDerivWithinAt (s := univ)).comp τ (hΓ τ hτ)
        (by rw [preimage_univ]; exact subset_univ s)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hcomp
    have hdw := hcomp.hasDerivWithinAt
    have hfun : (Prod.fst ∘ Γ) = φ := rfl
    rw [hfun] at hdw
    refine hdw.congr_deriv ?_
    show ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1) (TangentSpace I (Γ τ).2)).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ))))
        (1 : ℝ) = (1 : ℝ)
    simp
  have hderiv : ∀ τ ∈ s, deriv φ τ = 1 := fun τ hτ =>
    ((hd τ hτ).hasDerivAt (hs.mem_nhds hτ)).deriv
  have hdiff : DifferentiableOn ℝ φ s := fun τ hτ => (hd τ hτ).differentiableWithinAt
  have hg : ∀ τ ∈ s, deriv (fun y : ℝ => y) τ = 1 := fun τ _ => by simp
  have heq : EqOn φ (fun y : ℝ => y) s := by
    refine hs.eqOn_of_deriv_eq hconn hdiff differentiable_id.differentiableOn ?_ h0 ?_
    · intro τ hτ
      rw [hderiv τ hτ, hg τ hτ]
    · exact hΓ0
  intro t ht
  simpa [hφ] using heq ht

/-- **The time component tracks the parameter, anchored at an arbitrary start time.**
Generalises `autonomous_fst_eq_id` (anchor `t₀ = 0`): an integral curve `Γ` of the
autonomous field `(1, X · ·)` on a preconnected open set `s ∋ 0`, with
`(Γ 0).1 = t₀`, has `(Γ t).1 = t₀ + t` throughout `s` — the first coordinate has
constant derivative `1`, so it is the affine map `t ↦ t₀ + t`. This lets an
autonomous curve *anchored at time `t₀`* (not `0`) be recognised, after the time
shift `σ ↦ σ - t₀`, as a genuine time-dependent integral curve. -/
theorem autonomous_fst_eq_add {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ} {t₀ : ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = t₀)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, (Γ t).1 = t₀ + t := by
  set φ : ℝ → ℝ := fun τ => (Γ τ).1 with hφ
  have hd : ∀ τ ∈ s, HasDerivWithinAt φ 1 s τ := by
    intro τ hτ
    have hcomp :=
      ((hasMFDerivAt_fst (Γ τ)).hasMFDerivWithinAt (s := univ)).comp τ (hΓ τ hτ)
        (by rw [preimage_univ]; exact subset_univ s)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hcomp
    have hdw := hcomp.hasDerivWithinAt
    have hfun : (Prod.fst ∘ Γ) = φ := rfl
    rw [hfun] at hdw
    refine hdw.congr_deriv ?_
    show ((ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ℝ) (Γ τ).1) (TangentSpace I (Γ τ).2)).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (((1 : ℝ), X (Γ τ).1 (Γ τ).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ τ))))
        (1 : ℝ) = (1 : ℝ)
    simp
  have hderiv : ∀ τ ∈ s, deriv φ τ = 1 := fun τ hτ =>
    ((hd τ hτ).hasDerivAt (hs.mem_nhds hτ)).deriv
  have hdiff : DifferentiableOn ℝ φ s := fun τ hτ => (hd τ hτ).differentiableWithinAt
  have hg : ∀ τ ∈ s, deriv (fun y : ℝ => t₀ + y) τ = 1 := fun τ _ =>
    ((hasDerivAt_id τ).const_add t₀).deriv
  have heq : EqOn φ (fun y : ℝ => t₀ + y) s := by
    refine hs.eqOn_of_deriv_eq hconn hdiff (by fun_prop) ?_ h0 ?_
    · intro τ hτ
      rw [hderiv τ hτ, hg τ hτ]
    · show φ 0 = t₀ + 0
      rw [add_zero]; exact hΓ0
  intro t ht
  simpa [hφ] using heq ht

/-- **Time-dependent integral curve from an autonomous one** (combined form): if
`Γ` is an autonomous integral curve of `(1, X)` on a preconnected open `s ∋ 0` with
`(Γ 0).1 = 0`, then `(Γ ·).2` is a time-dependent integral curve of `X` on `s`. -/
theorem isTimeDependentIntegralCurve_of_autonomous_of_fst {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {Γ : ℝ → ℝ × M} {s : Set ℝ}
    (hs : IsOpen s) (h0 : (0 : ℝ) ∈ s) (hconn : IsPreconnected s)
    (hΓ0 : (Γ 0).1 = 0)
    (hΓ : ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) Γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (((1 : ℝ), X (Γ t).1 (Γ t).2) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ t)))) :
    ∀ t ∈ s, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => (Γ τ).2) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t ((Γ t).2))) :=
  isTimeDependentIntegralCurve_of_autonomous (autonomous_fst_eq_id hs h0 hconn hΓ0 hΓ) hΓ

/-! ### Time-dependent integral-curve existence and uniqueness

Assembling the flow box on `ℝ × M` with the autonomization bridge gives existence
and uniqueness of time-dependent integral curves on a (boundaryless, T2) manifold.
Existence uses the *non-compact* flow box per start point (since `ℝ × M` is never
compact); uniqueness uses mathlib's autonomous uniqueness on the product. -/

/-- **Per-point time-dependent local existence.** For a jointly-`C¹` time-dependent
field `X` on a boundaryless complete manifold, every start point `x` (at time `0`)
admits a time-dependent integral curve of `X` on some `Ioo (-ε) ε`. -/
theorem exists_timeDependent_integralCurve {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (x : M) :
    ∃ ε > 0, ∃ γ : ℝ → M, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  obtain ⟨U, hU, ε, hε, hcurve⟩ := exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX (0, x)
  have hmem : ((0 : ℝ), x) ∈ U := mem_of_mem_nhds hU
  obtain ⟨Γ, hΓ0, hΓint⟩ := hcurve ((0 : ℝ), x) hmem
  refine ⟨ε, hε, fun τ => (Γ τ).2, ?_, ?_⟩
  · show (Γ 0).2 = x
    rw [hΓ0]
  · have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
    have hΓ0fst : (Γ 0).1 = 0 := by rw [hΓ0]
    refine isTimeDependentIntegralCurve_of_autonomous_of_fst
      isOpen_Ioo h0 isPreconnected_Ioo hΓ0fst ?_
    intro t ht
    exact hΓint t ht

/-- The continuous-linear-map identity underlying the lift of an `M`-curve to the
product manifold: `(id, (1).smulRight v) = (1).smulRight (1, v)`. -/
private theorem timeDependent_lift_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (v : E') :
    (ContinuousLinearMap.id ℝ ℝ).prod ((1 : ℝ →L[ℝ] ℝ).smulRight v)
      = (1 : ℝ →L[ℝ] ℝ).smulRight ((1, v) : ℝ × E') := by
  apply ContinuousLinearMap.ext
  intro r
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply]

/-- **Reverse autonomization lift.** A time-dependent integral curve `γ` of `X` on
`M` lifts to an autonomous integral curve `τ ↦ (τ, γ τ)` of `(1, X)` on `ℝ × M`. -/
theorem autonomousLift_hasMFDerivWithinAt {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) (fun τ => (τ, γ τ)) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((1 : ℝ), X t (γ t)) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) (t, γ t))) := by
  have hid : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (id : ℝ → ℝ) s t
      (ContinuousLinearMap.id ℝ ℝ) := hasMFDerivWithinAt_id s t
  have h := hid.prodMk hγ
  refine h.congr_mfderiv ?_
  refine ContinuousLinearMap.ext fun r => ?_
  refine Prod.ext ?_ rfl
  rw [ContinuousLinearMap.prod_apply]
  show (ContinuousLinearMap.id ℝ ℝ) r
      = ((1 : ℝ →L[ℝ] ℝ) r • ((1 : ℝ), X t (γ t)) : ℝ × TangentSpace I (γ t)).1
  rw [ContinuousLinearMap.id_apply, Prod.smul_fst, ContinuousLinearMap.one_apply,
    smul_eq_mul, mul_one]

/-- **Uniqueness of time-dependent integral curves.** Two time-dependent integral
curves of a jointly-`C¹` field `X` on a boundaryless T2 manifold that agree at
`t = 0` agree throughout `Ioo a b` (with `0 ∈ Ioo a b`). Proved by lifting to
autonomous curves on `ℝ × M` and applying mathlib's autonomous uniqueness. -/
theorem timeDependent_integralCurve_unique {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {γ γ' : ℝ → M} {a b : ℝ} (hab : (0 : ℝ) ∈ Set.Ioo a b)
    (hγ : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hγ' : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ' (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t))))
    (h0 : γ 0 = γ' 0) :
    Set.EqOn γ γ' (Set.Ioo a b) := by
  set w : (x : ℝ × M) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) x :=
    fun p => ((1 : ℝ), X p.1 p.2) with hw
  set Γ : ℝ → ℝ × M := fun t => (t, γ t) with hΓdef
  set Γ' : ℝ → ℝ × M := fun t => (t, γ' t) with hΓ'def
  have hΓint : IsMIntegralCurveOn Γ w (Set.Ioo a b) := by
    intro t ht
    exact autonomousLift_hasMFDerivWithinAt ht (hγ t ht)
  have hΓ'int : IsMIntegralCurveOn Γ' w (Set.Ioo a b) := by
    intro t ht
    exact autonomousLift_hasMFDerivWithinAt ht (hγ' t ht)
  have hv : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun x => (⟨x, w x⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) := hX
  have hstart : Γ 0 = Γ' 0 := by simp [hΓdef, hΓ'def, h0]
  have heq : Set.EqOn Γ Γ' (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hab hv hΓint hΓ'int hstart
  intro t ht
  have h2 : (Γ t).2 = (Γ' t).2 := by rw [heq ht]
  simpa [hΓdef, hΓ'def] using h2

/-! ### Flow group law and mutual inverse

For an *autonomous* `C¹` field on a boundaryless T2 manifold, the flow `Φ` (with
`Φ 0 x = x` and each `τ ↦ Φ τ x` an integral curve) satisfies the group law
`Φ (s+t) = Φ s ∘ Φ t`, hence `Φ t` and `Φ (-t)` are mutual inverses. These follow
from integral-curve *uniqueness* alone — no smooth dependence on the initial
condition is needed — and supply the mutual-inverse data that
`SmoothSelfDiffeomorph3Family.ofInverse` consumes. -/

/-- **Flow group law.** For an autonomous `C¹` field, the flow satisfies
`Φ (s + t) x = Φ s (Φ t x)`, by uniqueness of the integral curve through `Φ t x`. -/
theorem flow_group_law {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Φ t x) v)
    (s t : ℝ) (x : M) :
    Φ (s + t) x = Φ s (Φ t x) := by
  have hγ1 : IsMIntegralCurve (fun τ => Φ (τ + t) x) v := by
    have h := (hcurve x).comp_add t
    convert h using 1
  have hγ2 : IsMIntegralCurve (fun τ => Φ τ (Φ t x)) v := hcurve (Φ t x)
  have heq : (fun τ => Φ (τ + t) x) = (fun τ => Φ τ (Φ t x)) :=
    isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
      (fun τ => BoundarylessManifold.isInteriorPoint) hv hγ1 hγ2
      (by simp [hanchor])
  exact congrFun heq s

/-- The flow's left/right inverses from the group law (pure algebra). -/
theorem flow_leftInverse {M : Type*} {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x)) (t : ℝ) :
    Function.LeftInverse (Φ (-t)) (Φ t) :=
  fun x => by rw [← hgroup (-t) t x, neg_add_cancel, hanchor]

theorem flow_rightInverse {M : Type*} {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x)) (t : ℝ) :
    Function.RightInverse (Φ (-t)) (Φ t) :=
  fun x => by rw [← hgroup t (-t) x, add_neg_cancel, hanchor]

/-- **The complete mutual-inverse package** for `SmoothSelfDiffeomorph3Family.ofInverse`:
from the flow's defining properties, both `Φ t` and `Φ (-t)` are mutual inverses for
every `t`. Derived from integral-curve uniqueness; no smooth dependence needed. -/
theorem flow_inverse_package {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Φ t x) v) :
    (∀ t, Function.LeftInverse (Φ (-t)) (Φ t)) ∧ (∀ t, Function.RightInverse (Φ (-t)) (Φ t)) := by
  have hgroup : ∀ (s t : ℝ) (x : M), Φ (s + t) x = Φ s (Φ t x) :=
    fun s t x => flow_group_law hv hanchor hcurve s t x
  exact ⟨fun t => flow_leftInverse hanchor hgroup t,
         fun t => flow_rightInverse hanchor hgroup t⟩

/-! ### Uniform time-dependent local flow on a compact manifold

The DeTurck gauge field is *time-dependent*. Integrating it uniformly over all
start points requires autonomizing to the product `ℝ × M`, which is *never*
compact, so `exists_uniform_integralCurve_time` (whole space compact) does not
apply. What *is* compact is the **initial-time slice** `{0} × M`; a uniform lifespan
over that slice suffices, because every start point `x` enters the autonomization
as `(0, x)`. This subsection supplies the compact-*slice* uniform-time reduction and
assembles the compact-manifold time-dependent local flow existence the gauge-flow
construction consumes. -/

/-- **Uniform existence time over a compact subset from the flow box.** The
neighborhood-uniform flow box yields, over any *compact subset* `S` of a (possibly
noncompact) manifold, a single `ε > 0` working for every start point in `S`, by
extracting a finite subcover of `S` and taking the minimum lifespan. This is the
compact-*slice* refinement of `exists_uniform_time_of_nhds_uniform` (which needs the
whole space compact); applied to the compact initial-time slice `{0} × M` of the
noncompact autonomization space `ℝ × M`, it integrates a *time-dependent* field with
a single uniform lifespan. -/
theorem exists_uniform_time_of_nhds_uniform_on_compact {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {v : (x : M) → TangentSpace I x}
    (hbox : ∀ x₀ : M, ∃ U ∈ nhds x₀, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M, γ 0 = y ∧
      IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε))
    {S : Set M} (hS : IsCompact S) :
    ∃ ε > 0, ∀ x ∈ S, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε) := by
  choose U hUmem ε hεpos hprop using hbox
  have hopen : ∀ x : M, ∃ t, t ⊆ U x ∧ IsOpen t ∧ x ∈ t := fun x => mem_nhds_iff.mp (hUmem x)
  choose V hVsub hVopen hVmem using hopen
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover V hVopen
    (fun x _ => mem_iUnion.mpr ⟨x, hVmem x⟩)
  rcases t.eq_empty_or_nonempty with hte | htne
  · subst hte
    refine ⟨1, one_pos, fun x hx => ?_⟩
    have h := ht hx; simp at h
  · refine ⟨t.inf' htne ε, (Finset.lt_inf'_iff htne).mpr (fun i _ => hεpos i), fun x hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    obtain ⟨γ, hγ0, hγon⟩ := hprop i x (hVsub i hxi)
    refine ⟨γ, hγ0, hγon.mono ?_⟩
    have hle : t.inf' htne ε ≤ ε i := Finset.inf'_le ε hi
    exact Ioo_subset_Ioo (by linarith) hle

/-- **Uniform time-dependent local flow existence on a compact manifold.** For a
jointly-`C¹` time-dependent field `X` on a compact boundaryless complete manifold,
there is a *single* `ε > 0` such that every start point `x` (at time `0`) admits a
time-dependent integral curve of `X` on the common interval `Ioo (-ε) ε`. Because the
DeTurck gauge field is time-dependent, this — not the autonomous
`exists_uniform_integralCurve_time` — is the existence core the gauge flow consumes.
Proved by autonomizing to the noncompact `ℝ × M` and taking the uniform lifespan over
the *compact initial-time slice* `{0} × M` via
`exists_uniform_time_of_nhds_uniform_on_compact`, then projecting through
`isTimeDependentIntegralCurve_of_autonomous_of_fst`. -/
theorem exists_uniform_timeDependent_integralCurve_time {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  have hScompact : IsCompact (({(0 : ℝ)} ×ˢ (Set.univ : Set M)) : Set (ℝ × M)) :=
    isCompact_singleton.prod isCompact_univ
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_time_of_nhds_uniform_on_compact
    (fun p => exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX p) hScompact
  refine ⟨ε, hε, fun x => ?_⟩
  obtain ⟨Γ, hΓ0, hΓon⟩ := huniform (0, x) (by simp)
  refine ⟨fun τ => (Γ τ).2, by simp [hΓ0], ?_⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hΓ0fst : (Γ 0).1 = 0 := by rw [hΓ0]
  exact isTimeDependentIntegralCurve_of_autonomous_of_fst
    isOpen_Ioo h0 isPreconnected_Ioo hΓ0fst (fun t ht => hΓon t ht)

/-- **Bundled uniform time-dependent flow on a compact manifold.** Packages
`exists_uniform_timeDependent_integralCurve_time` into a flow map `Φ : ℝ → M → M`
with `Φ 0 = id` such that, for every `x`, the orbit `τ ↦ Φ τ x` is a time-dependent
integral curve of `X` on the common interval `Ioo (-ε) ε`. This is the anchored
integral-curve family the compact-manifold gauge-flow construction is built on. -/
theorem exists_timeDependent_flow_compact {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) := by
  obtain ⟨ε, hε, huniform⟩ := exists_uniform_timeDependent_integralCurve_time hX
  choose γ hγ0 hγon using huniform
  exact ⟨ε, hε, fun t x => γ x t, hγ0, fun x t ht => hγon x t ht⟩

/-- **Uniqueness of time-dependent integral curves anchored at any interior time.**
For a jointly-`C¹` time-dependent field `X` on a boundaryless T2 manifold, two
time-dependent integral curves on `Ioo a b` that agree at a *single interior time*
`t₀ ∈ Ioo a b` agree on all of `Ioo a b`. Generalises
`timeDependent_integralCurve_unique` (anchor `t₀ = 0`) by anchoring at an arbitrary
interior time; proved by lifting to autonomous curves on `ℝ × M` and applying
mathlib's autonomous uniqueness at `t₀`. Anchoring at an arbitrary time is what
yields injectivity of each time-`t` flow map. -/
theorem timeDependent_integralCurve_eqOn_of_eq {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {γ γ' : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hγ' : ∀ t ∈ Set.Ioo a b, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ' (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t))))
    (h0 : γ t₀ = γ' t₀) :
    Set.EqOn γ γ' (Set.Ioo a b) := by
  set w : (x : ℝ × M) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) x :=
    fun p => ((1 : ℝ), X p.1 p.2) with hw
  set Γ : ℝ → ℝ × M := fun t => (t, γ t) with hΓdef
  set Γ' : ℝ → ℝ × M := fun t => (t, γ' t) with hΓ'def
  have hΓint : IsMIntegralCurveOn Γ w (Set.Ioo a b) := fun t ht =>
    autonomousLift_hasMFDerivWithinAt ht (hγ t ht)
  have hΓ'int : IsMIntegralCurveOn Γ' w (Set.Ioo a b) := fun t ht =>
    autonomousLift_hasMFDerivWithinAt ht (hγ' t ht)
  have hstart : Γ t₀ = Γ' t₀ := by simp [hΓdef, hΓ'def, h0]
  have heq : Set.EqOn Γ Γ' (Set.Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hX hΓint hΓ'int hstart
  intro t ht
  have h2 : (Γ t).2 = (Γ' t).2 := by rw [heq ht]
  simpa [hΓdef, hΓ'def] using h2

/-- **Injectivity of each time-`t` flow map.** For a jointly-`C¹` time-dependent
field `X` on a compact boundaryless T2 manifold, if a flow `Φ` is anchored
(`Φ 0 = id`) with every orbit `τ ↦ Φ τ x` a time-dependent integral curve of `X` on
`Ioo (-ε) ε`, then for each `t ∈ Ioo (-ε) ε` the time-`t` map `x ↦ Φ t x` is
injective: two orbits agreeing at time `t` agree everywhere on `Ioo (-ε) ε`, in
particular at time `0`, where the anchor reads off the two start points. This is the
diffeomorphism-onto-image (injectivity) half the compact-manifold gauge flow of
Item 2 consumes. -/
theorem timeDependent_flow_injective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ → M → M} (hanchor : ∀ x, Φ 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    Function.Injective (Φ t) := by
  intro x y hxy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have heq : Set.EqOn (fun τ => Φ τ x) (fun τ => Φ τ y) (Set.Ioo (-ε) ε) :=
    timeDependent_integralCurve_eqOn_of_eq hX ht (hflow x) (hflow y) hxy
  have h0 := heq h0mem
  simpa [hanchor] using h0

/-- **Bundled injective time-dependent flow on a compact manifold.** Combines
`exists_timeDependent_flow_compact` with `timeDependent_flow_injective`: for a
jointly-`C¹` time-dependent field `X` on a compact boundaryless T2 manifold there is a
uniform `ε > 0` and an anchored flow `Φ` (`Φ 0 = id`) whose orbits `τ ↦ Φ τ x` solve
the field's ODE on `Ioo (-ε) ε` and whose every time-`t` slice `x ↦ Φ t x` is
injective. This is the compact-manifold time-dependent local flow with injective
time-slices — the existence-plus-injectivity (diffeomorphism-onto-image) datum the
compact-manifold gauge flow of Item 2 consumes for its forward family `F`. -/
theorem exists_timeDependent_flow_compact_injective {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M)))) :
    ∃ ε > 0, ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
        (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Function.Injective (Φ t)) := by
  obtain ⟨ε, hε, Φ, hanchor, hflow⟩ := exists_timeDependent_flow_compact hX
  exact ⟨ε, hε, Φ, hanchor, hflow,
    fun t ht => timeDependent_flow_injective hX hε hanchor hflow ht⟩

/-- **Uniqueness (canonicity) of the anchored time-dependent flow.** For a jointly-`C¹`
time-dependent field `X` on a boundaryless T2 manifold, any two flows `Φ`, `Φ'` that are
anchored (`Φ 0 = Φ' 0 = id`) with orbits solving the field's ODE on `Ioo (-ε) ε` agree
on `Ioo (-ε) ε`: for every `x` the two orbits agree at `0`, hence everywhere by
`timeDependent_integralCurve_eqOn_of_eq`. Together with existence and injectivity this
makes the compact-manifold local flow a *canonically determined* family of injections. -/
theorem timeDependent_flow_unique {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ Φ' : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x) (hanchor' : ∀ x, Φ' 0 x = x)
    (hflow : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε, HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ => Φ' τ x)
      (Set.Ioo (-ε) ε) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x))))
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) (x : M) :
    Φ t x = Φ' t x := by
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have h0 : (fun τ => Φ τ x) 0 = (fun τ => Φ' τ x) 0 := by simp [hanchor, hanchor']
  have heq : Set.EqOn (fun τ => Φ τ x) (fun τ => Φ' τ x) (Set.Ioo (-ε) ε) :=
    timeDependent_integralCurve_eqOn_of_eq hX h0mem (hflow x) (hflow' x) h0
  exact heq ht

/-! ### Backward reachability and bijectivity of the compact-manifold flow

The forward flow `Φ` has injective time-slices (`timeDependent_flow_injective`), but
surjectivity of `x ↦ Φ t x` on a compact manifold is *not* automatic from injectivity
and continuity (invariance of domain would be needed); it requires a genuine backward
flow — an integral curve of `X` run from time `t` *back* to time `0`. Such curves need
the time-dependent existence *anchored at an arbitrary time* `t₀`, which the uniform
lifespan over the compact **time-slab** `Icc (-r) r ×ˢ univ` supplies (a single `δ`
covering every start time in `[-r, r]`). Reconciling that slab lifespan with the forward
lifespan closes surjectivity, hence bijectivity, of every time-slice — the
diffeomorphism-onto-image datum (its `G t` inverse half) Item 2's gauge flow consumes. -/

/-- **Uniform time-dependent integral-curve existence anchored at any time in a slab.**
For a jointly-`C¹` time-dependent field `X` on a compact boundaryless complete manifold
and any `r > 0`, there is a single `δ > 0` such that *every* start time `t₀ ∈ [-r, r]`
and *every* point `y` admit a time-dependent integral curve `γ` of `X` on the common
window `Ioo (t₀ - δ) (t₀ + δ)` with `γ t₀ = y`. Proved by taking the uniform lifespan of
the autonomization `(1, X)` over the compact time-slab `Icc (-r) r ×ˢ univ ⊆ ℝ × M`
(via `exists_uniform_time_of_nhds_uniform_on_compact`) and time-shifting the autonomous
curve anchored at `(t₀, y)` by `σ ↦ σ - t₀` (its first coordinate then tracks the
parameter by `autonomous_fst_eq_add`, so it descends to a time-dependent curve). This is
the anchored-anywhere existence the backward flow — and hence surjectivity — consumes. -/
theorem exists_uniform_timeDependent_integralCurve_anchored {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]
    [CompactSpace M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ t₀ ∈ Set.Icc (-r) r, ∀ y : M, ∃ γ : ℝ → M, γ t₀ = y ∧
      ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ
        (Set.Ioo (t₀ - δ) (t₀ + δ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  have hScompact : IsCompact ((Set.Icc (-r) r ×ˢ (Set.univ : Set M)) : Set (ℝ × M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨δ, hδ, huniform⟩ := exists_uniform_time_of_nhds_uniform_on_compact
    (fun p => exists_nhds_uniform_integralCurve (I := (𝓘(ℝ, ℝ)).prod I) hX p) hScompact
  refine ⟨δ, hδ, fun t₀ ht₀ y => ?_⟩
  obtain ⟨Γ, hΓ0, hΓon⟩ := huniform (t₀, y) ⟨ht₀, Set.mem_univ _⟩
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hΓ0fst : (Γ 0).1 = t₀ := by rw [hΓ0]
  -- the first coordinate of Γ is the affine map `ρ ↦ t₀ + ρ`
  have hfst_orig : ∀ ρ ∈ Set.Ioo (-δ) δ, (Γ ρ).1 = t₀ + ρ :=
    autonomous_fst_eq_add isOpen_Ioo h0mem isPreconnected_Ioo hΓ0fst (fun ρ hρ => hΓon ρ hρ)
  -- the shifted curve is an autonomous integral curve on `Ioo (t₀-δ) (t₀+δ)`
  have hΓs_curve : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod I) (fun σ => Γ (σ - t₀))
        (Set.Ioo (t₀ - δ) (t₀ + δ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (((1 : ℝ), X (Γ (t - t₀)).1 (Γ (t - t₀)).2) :
            TangentSpace ((𝓘(ℝ, ℝ)).prod I) (Γ (t - t₀)))) := by
    have h := hΓon.comp_add (-t₀)
    have he1 : (Γ ∘ (· + (-t₀))) = (fun σ => Γ (σ - t₀)) := by
      funext σ; simp only [Function.comp_apply, sub_eq_add_neg]
    have he2 : {σ : ℝ | σ + (-t₀) ∈ Set.Ioo (-δ) δ} = Set.Ioo (t₀ - δ) (t₀ + δ) := by
      ext σ; simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [he1, he2] at h
    exact fun t ht => h t ht
  -- the shifted first coordinate tracks the parameter
  have hfst : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), (Γ (t - t₀)).1 = t := by
    intro t ht
    rcases ht with ⟨h1, h2⟩
    have hρ : t - t₀ ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    rw [hfst_orig (t - t₀) hρ]; ring
  refine ⟨fun σ => (Γ (σ - t₀)).2, ?_, ?_⟩
  · show (Γ (t₀ - t₀)).2 = y
    rw [sub_self, hΓ0]
  · exact isTimeDependentIntegralCurve_of_autonomous (Γ := fun σ => Γ (σ - t₀)) hfst hΓs_curve

end PoincareCurvature.ManifoldFlow
