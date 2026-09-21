module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCoordinatePicardEstimates

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Phase-1 jet reduction for DeTurck Picard estimates

This module proves the pure differential-calculus reduction underlying Phase 1
of the Point-4 variational witness: **joint continuity of the metric jet**
implies the regularity package (`hreg`, `hjoint`, `hjoint2`) required by
`deTurckGaugeCoordinatePicardEstimates`.

## The analytic input: `SmoothDeTurckJetMap`

The (negated) DeTurck vector field is a smooth function of the metric's 1-jet:
in coordinates, `F(t, y) = Ψ(G(t,y), D_y G(t,y))` where `G` is the metric's
coordinate representative and `Ψ` is smooth (it is built from the matrix
inverse and the Christoffel symbols, which are rational in the 1-jet).
Consequently the first and second spatial derivatives of `F` are also smooth
functions of the jet, via the chain rule.

This analytic fact is packaged as `SmoothDeTurckJetMap`: a jet type `J`
(with its normed-space instances), a jet map `S`, and smooth coefficient maps
`Ψ₀, Ψ₁, Ψ₂` such that `F = Ψ₀ ∘ S` and the first/second spatial derivatives
are `Ψ₁ ∘ S`, `Ψ₂ ∘ S` (with the correct `HasFDerivAt` identities).

**Status of the geometric construction (Phase-1b).**  The `SmoothDeTurckJetMap`
structure is the precise interface for the geometric input.  Constructing it
for the genuine DeTurck field requires unfolding `deTurckGaugeCoordinateField`
through `extChartAt`, `mfderiv`, `intrinsicDeTurckGaugeField` (the NEGATED
DeTurck vector field), and the Christoffel-symbol calculus, then verifying
smoothness of the resulting jet expression.  This construction is NOT carried
out here; it is the Phase-1b work item.

What IS proved here, with no `sorry`, is the pure-calculus implication:

> `SmoothDeTurckJetMap` + joint continuity of `S` on the compact cylinder
> ⟹ `hreg` ∧ `hjoint` ∧ `hjoint2`

exactly as required by `deTurckGaugeCoordinatePicardEstimates`, so that once
Phase-1b constructs the jet map (e.g. from parabolic Schauder theory), the
Picard estimates follow by direct application.

**Background regularity.**  The DeTurck field depends on both the metric `g`
and the background connection `background`.  For the `SmoothDeTurckJetMap` to
exist with `C²` field regularity, the background must be `C²` (so the
connection difference is `C²`).  The background hypothesis is NOT assumed
here; it must be discharged when Phase-1b is carried out for the specific
background used in the Point-4 application.  The theorems below take the
`SmoothDeTurckJetMap` (which encapsulates both the metric and background
dependence) as an explicit hypothesis.

CONVENTION: `intrinsicDeTurckGaugeField` is the *negated* DeTurck vector field;
`deTurckGaugeCoordinateField` preserves this negation, and the jet-map package
is stated for the negated field as defined.
-/

@[expose] public noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- **Analytic input package (Phase-1b target).**  The DeTurck gauge coordinate
field `F` factors through a metric jet map `S : ℝ × E → J` via smooth
coefficient maps, with correct first and second spatial derivatives.

Mathematically: `F(t,y) = Ψ₀(S(t,y))` where `Ψ₀` is smooth in the jet, and the
chain rule gives `D_y F(t,y) = Ψ₁(S(t,y))`, `D²_y F(t,y) = Ψ₂(S(t,y))` for
smooth `Ψ₁, Ψ₂`.  The `HasFDerivAt` fields encode precisely these chain-rule
identities on the coordinate ball of radius `R`.

This is the single analytic input to the Phase-1 reduction.  It is a genuine
geometric fact about the DeTurck field (smooth dependence on the metric jet),
not a restatement of the conclusion: it says *how* `F` is built, while `hreg`,
`hjoint`, `hjoint2` are *regularity consequences* proved below from this
structure plus joint continuity of `S`. -/
structure SmoothDeTurckJetMap (F : ℝ → E → E) (y₀ : E) (R : ℝ)
    (J : Type*) [NormedAddCommGroup J] [NormedSpace ℝ J] where
  /-- The metric jet map `(t, y) ↦` 3-jet of the metric at `(t, y)`. -/
  S : ℝ × E → J
  /-- Smooth coefficient maps: field value, first and second derivatives. -/
  Ψ₀ : J → E
  Ψ₁ : J → (E →L[ℝ] E)
  Ψ₂ : J → (E →L[ℝ] E →L[ℝ] E)
  hΨ₀ : ContDiff ℝ ∞ Ψ₀
  hΨ₁ : ContDiff ℝ ∞ Ψ₁
  hΨ₂ : ContDiff ℝ ∞ Ψ₂
  /-- The field factors through the jet. -/
  hfactor₀ : ∀ (t : ℝ) (y : E), F t y = Ψ₀ (S (t, y))
  /-- First spatial derivative is the jet-smooth `Ψ₁` (chain rule). -/
  hfactor₁ : ∀ (t : ℝ) (y : E), y ∈ ball y₀ R →
    HasFDerivAt (F t) (Ψ₁ (S (t, y))) y
  /-- Second spatial derivative is the jet-smooth `Ψ₂` (chain rule twice). -/
  hfactor₂ : ∀ (t : ℝ) (y : E), y ∈ ball y₀ R →
    HasFDerivAt (fun z => Ψ₁ (S (t, z))) (Ψ₂ (S (t, y))) y

/-- A map is `C²` on an open set if it admits a first derivative `D₁`, and `D₁`
in turn admits a continuous second derivative `D₂`.  This is the workhorse
that turns the jet-map derivative identities into `hreg`. -/
theorem contDiffOn_two_of_hasFDerivAt
    {F : E → E} {s : Set E} (hs : IsOpen s)
    {D₁ : E → (E →L[ℝ] E)} {D₂ : E → (E →L[ℝ] E →L[ℝ] E)}
    (h₁ : ∀ y ∈ s, HasFDerivAt F (D₁ y) y)
    (h₂ : ∀ y ∈ s, HasFDerivAt D₁ (D₂ y) y)
    (hcont : ContinuousOn D₂ s) :
    ContDiffOn ℝ 2 F s := by
  have hfderiv : ∀ y ∈ s, fderiv ℝ F y = D₁ y :=
    fun y hy => (h₁ y hy).fderiv
  have hdiff : DifferentiableOn ℝ F s :=
    fun y hy => (h₁ y hy).differentiableAt.differentiableWithinAt
  -- `fderiv F` agrees with `D₁` near each point, hence is differentiable.
  have hdiff1 : DifferentiableOn ℝ (fderiv ℝ F) s := by
    intro y hy
    have heq : fderiv ℝ F =ᶠ[𝓝 y] D₁ := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hfderiv z hz
    exact ((h₂ y hy).differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt
  -- `fderiv (fderiv F)` agrees with the continuous `D₂`, hence is continuous.
  have hfderiv2 : ∀ y ∈ s, fderiv ℝ (fderiv ℝ F) y = D₂ y := by
    intro y hy
    have heq : fderiv ℝ F =ᶠ[𝓝 y] D₁ := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hfderiv z hz
    rw [heq.fderiv_eq]
    exact (h₂ y hy).fderiv
  have hcont2 : ContinuousOn (fderiv ℝ (fderiv ℝ F)) s :=
    hcont.congr fun y hy => hfderiv2 y hy
  -- Assemble: `C¹` of the derivative (n = 0; the analytic side-condition is vacuous).
  have hCD1 : ContDiffOn ℝ 1 (fderiv ℝ F) s := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (0 : ℕ)) hs).mpr
      ⟨hdiff1, fun hh => absurd hh (by decide), contDiffOn_zero.mpr hcont2⟩
    simpa using h
  -- Assemble: `C²` of `F` (n = 1; the analytic side-condition is vacuous).
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (1 : ℕ)) hs).mpr
    ⟨hdiff, fun hh => absurd hh (by decide), hCD1⟩
  exact_mod_cast h

/-- **Phase-1 reduction (general form).**  A smooth jet map for a general field
`F : ℝ → E → E`, plus joint continuity of the jet on the compact cylinder,
implies `C²`-in-space regularity and joint continuity of the field and its
first two spatial derivatives.

The proof is pure differential calculus: smooth maps preserve continuity
under composition, so `F = Ψ₀ ∘ S`, `DF = Ψ₁ ∘ S`, `D²F = Ψ₂ ∘ S` are jointly
continuous; and `F t` is `C²` by `contDiffOn_two_of_hasFDerivAt` applied to
the jet-map derivative identities. -/
theorem smoothJetMap_implies_regularity_aux
    (F : ℝ → E → E) (y₀ : E) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (J : Type*) [NormedAddCommGroup J] [NormedSpace ℝ J]
    (JM : SmoothDeTurckJetMap F y₀ ((a : ℝ) + 1) J)
    (H : ContinuousOn JM.S
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ((a : ℝ) + 1))) :
    (∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ 2 (F t) (ball y₀ ((a : ℝ) + 1)))
    ∧ ContinuousOn
      (fun p : ℝ × E => (F p.1 p.2, fderiv ℝ (F p.1) p.2))
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ))
    ∧ ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := by
  -- The small closed ball sits inside the large open ball.
  have hball_sub : closedBall y₀ (a : ℝ) ⊆ ball y₀ ((a : ℝ) + 1) := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball]
    calc dist y y₀ ≤ (a : ℝ) := hy
      _ < (a : ℝ) + 1 := by linarith
  -- The small cylinder sits inside the large cylinder.
  have hcyl_sub : Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)
      ⊆ Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ((a : ℝ) + 1) := by
    intro p hp
    obtain ⟨ht, hy⟩ := Set.mem_prod.mp hp
    exact Set.mk_mem_prod ht (closedBall_subset_closedBall (by linarith) hy)
  have HS_small : ContinuousOn JM.S
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) :=
    H.mono hcyl_sub
  -- The smooth coefficient maps are continuous.
  have hΨ₀c : Continuous JM.Ψ₀ := JM.hΨ₀.continuous
  have hΨ₁c : Continuous JM.Ψ₁ := JM.hΨ₁.continuous
  have hΨ₂c : Continuous JM.Ψ₂ := JM.hΨ₂.continuous
  -- First derivative identity on the small cylinder.
  have hDF_eq : ∀ p ∈ Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ),
      fderiv ℝ (F p.1) p.2 = JM.Ψ₁ (JM.S p) := by
    intro p hp
    have hy : p.2 ∈ ball y₀ ((a : ℝ) + 1) := hball_sub (Set.mem_prod.mp hp).2
    calc fderiv ℝ (F p.1) p.2 = JM.Ψ₁ (JM.S (p.1, p.2)) :=
          (JM.hfactor₁ p.1 p.2 hy).fderiv
      _ = JM.Ψ₁ (JM.S p) := by rw [Prod.mk.eta]
  -- Second derivative identity on the small cylinder.
  have hD2F_eq : ∀ p ∈ Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ),
      fderiv ℝ (fderiv ℝ (F p.1)) p.2 = JM.Ψ₂ (JM.S p) := by
    intro p hp
    have hyball : p.2 ∈ ball y₀ ((a : ℝ) + 1) := hball_sub (Set.mem_prod.mp hp).2
    have heq : fderiv ℝ (F p.1) =ᶠ[𝓝 p.2] (fun y => JM.Ψ₁ (JM.S (p.1, y))) := by
      filter_upwards [isOpen_ball.mem_nhds hyball] with y hy
      exact (JM.hfactor₁ p.1 y hy).fderiv
    calc fderiv ℝ (fderiv ℝ (F p.1)) p.2
        = fderiv ℝ (fun y => JM.Ψ₁ (JM.S (p.1, y))) p.2 := heq.fderiv_eq
      _ = JM.Ψ₂ (JM.S (p.1, p.2)) := (JM.hfactor₂ p.1 p.2 hyball).fderiv
      _ = JM.Ψ₂ (JM.S p) := by rw [Prod.mk.eta]
  -- Joint continuity of the field: `F = Ψ₀ ∘ S`.
  have hF_cont : ContinuousOn (fun p : ℝ × E => F p.1 p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := by
    have hcomp : ContinuousOn (JM.Ψ₀ ∘ JM.S)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) :=
      hΨ₀c.comp_continuousOn HS_small
    refine hcomp.congr (fun p hp => ?_)
    exact JM.hfactor₀ p.1 p.2
  -- Joint continuity of the derivative: `DF = Ψ₁ ∘ S`.
  have hDF_cont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (F p.1) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := by
    have hcomp : ContinuousOn (JM.Ψ₁ ∘ JM.S)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) :=
      hΨ₁c.comp_continuousOn HS_small
    refine hcomp.congr (fun p hp => ?_)
    exact hDF_eq p hp
  -- Joint continuity of the second derivative: `D²F = Ψ₂ ∘ S`.
  have hD2F_cont : ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (F p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := by
    have hcomp : ContinuousOn (JM.Ψ₂ ∘ JM.S)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) :=
      hΨ₂c.comp_continuousOn HS_small
    refine hcomp.congr (fun p hp => ?_)
    exact hD2F_eq p hp
  refine ⟨?_, hF_cont.prodMk hDF_cont, hD2F_cont⟩
  -- `C²` on the large ball, via the jet derivative identities.
  intro t ht
  apply contDiffOn_two_of_hasFDerivAt isOpen_ball
    (D₁ := fun y => JM.Ψ₁ (JM.S (t, y))) (D₂ := fun y => JM.Ψ₂ (JM.S (t, y)))
  · intro y hy
    exact JM.hfactor₁ t y hy
  · intro y hy
    exact JM.hfactor₂ t y hy
  · -- `D₂` is continuous: `Ψ₂` smooth composed with the fixed-time jet map.
    have hcomp : ContinuousOn (JM.Ψ₂ ∘ JM.S)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ((a : ℝ) + 1)) :=
      hΨ₂c.comp_continuousOn H
    have hmaps : MapsTo (fun y => (t, y)) (ball y₀ ((a : ℝ) + 1))
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ((a : ℝ) + 1)) := by
      intro y hy
      exact Set.mk_mem_prod ht (ball_subset_closedBall hy)
    have h1 : ContinuousOn (fun y => (t, y)) (ball y₀ ((a : ℝ) + 1)) :=
      continuousOn_const.prodMk continuousOn_id
    have h2 := hcomp.comp h1 hmaps
    refine h2.congr (fun y hy => ?_)
    rfl

/-- **Phase-1 reduction for the DeTurck field.**  A smooth DeTurck jet map plus
joint continuity of the jet on the compact cylinder implies the full
regularity package (`hreg`, `hjoint`, `hjoint2`) required by
`deTurckGaugeCoordinatePicardEstimates`, stated here for the genuine
coordinate field `deTurckGaugeCoordinateField` so it plugs in directly. -/
theorem smoothJetMap_implies_picardRegularity
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (J : Type*) [NormedAddCommGroup J] [NormedSpace ℝ J]
    (JM : SmoothDeTurckJetMap
      (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀)
      (extChartAt I p₀ p₀) ((a : ℝ) + 1) J)
    (H : ContinuousOn JM.S
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) ((a : ℝ) + 1))) :
    (∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ 2
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
        (ball (extChartAt I p₀ p₀) ((a : ℝ) + 1)))
    ∧ ContinuousOn
      (fun p : ℝ × E =>
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1 p.2,
          fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1) p.2))
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ))
    ∧ ContinuousOn
      (fun p : ℝ × E =>
        fderiv ℝ
          (fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ)) :=
  smoothJetMap_implies_regularity_aux _ _ _ _ ha _ JM H

/-! ## Universal DeTurck jet calculus (Phase-1b)

The following constructs the smooth coefficient maps `Ψ₀, Ψ₁, Ψ₂` for the
genuine DeTurck field.  The 0-jet consists of the chart differential, the
metric sharp map, and the DeTurck one-form; the field is the negated
composition.  The sign is preserved throughout.
-/

set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000

/-- Type alias for the sharp map, with instances. -/
abbrev SharpMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := (E →L[ℝ] ℝ) →L[ℝ] E

noncomputable instance : NormedAddCommGroup (SharpMap E) := inferInstance
noncomputable instance : NormedSpace ℝ (SharpMap E) := inferInstance

/-- 0-jet: chart differential, sharp map, one-form. -/
abbrev Jet0 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] E) × (SharpMap E) × (E →L[ℝ] ℝ)

noncomputable instance : NormedAddCommGroup (Jet0 E) := inferInstance
noncomputable instance : NormedSpace ℝ (Jet0 E) := inferInstance

/-- 1-jet: 0-jet plus derivative. -/
abbrev Jet1 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Jet0 E) × (E →L[ℝ] (Jet0 E))

noncomputable instance : NormedAddCommGroup (Jet1 E) := inferInstance
noncomputable instance : NormedSpace ℝ (Jet1 E) := inferInstance

/-- 2-jet: 0-jet plus first and second derivatives. -/
abbrev Jet2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Jet0 E) × (E →L[ℝ] (Jet0 E)) × (E →L[ℝ] E →L[ℝ] (Jet0 E))

noncomputable instance : NormedAddCommGroup (Jet2 E) := inferInstance
noncomputable instance : NormedSpace ℝ (Jet2 E) := inferInstance

/-- Explicit instances for nested CLM types to avoid synthesis timeouts. -/
noncomputable instance : NormedAddCommGroup (E →L[ℝ] Jet0 E) := inferInstance
noncomputable instance : NormedSpace ℝ (E →L[ℝ] Jet0 E) := inferInstance
noncomputable instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] Jet0 E) := inferInstance
noncomputable instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] Jet0 E) := inferInstance

/-- The universal 0-jet map: negated composition. Preserves the DeTurck sign. -/
noncomputable def deturckPsi0 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    : Jet0 E → E :=
  fun j => -(j.1 (j.2.1 (j.2.2)))

theorem deturckPsi0_contDiff : ContDiff ℝ ∞ (deturckPsi0 E) := by
  unfold deturckPsi0
  have h2 : ContDiff ℝ ∞ (fun j : Jet0 E => j.2.1) :=
    contDiff_fst.comp contDiff_snd
  have h3 : ContDiff ℝ ∞ (fun j : Jet0 E => j.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hinner : ContDiff ℝ ∞ (fun j : Jet0 E => (j.2.1 : SharpMap E) ((j.2.2 : E →L[ℝ] ℝ))) :=
    h2.clm_apply h3
  have h1 : ContDiff ℝ ∞ (fun j : Jet0 E => j.1) :=
    contDiff_fst
  have houter : ContDiff ℝ ∞ (fun j : Jet0 E => (j.1 : E →L[ℝ] E) ((j.2.1 : SharpMap E) ((j.2.2 : E →L[ℝ] ℝ)))) :=
    h1.clm_apply hinner
  simpa using houter.neg

theorem deturckPsi0_fderiv_contDiff :
    ContDiff ℝ ∞ (fderiv ℝ (deturckPsi0 E)) := by
  apply deturckPsi0_contDiff.fderiv_right
  show ((∞ : ℕ∞ω) + 1 ≤ ∞)
  simp

/-- The universal 1-jet map on the 1-jet: chain rule. -/
noncomputable def deturckPsi1' (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    : Jet1 E → (E →L[ℝ] E) :=
  fun j1 => (fderiv ℝ (deturckPsi0 E) j1.1).comp j1.2

theorem deturckPsi1'_contDiff : ContDiff ℝ ∞ (deturckPsi1' E) := by
  unfold deturckPsi1'
  have hF : ContDiff ℝ ∞ (fun j1 : Jet1 E => fderiv ℝ (deturckPsi0 E) j1.1) :=
    deturckPsi0_fderiv_contDiff.comp contDiff_fst
  have hG : ContDiff ℝ ∞ (fun j1 : Jet1 E => j1.2) :=
    contDiff_snd
  have hpair := hF.prodMk hG
  have hcomp : ContDiff ℝ ∞
      (fun p : ((Jet0 E) →L[ℝ] E) × (E →L[ℝ] (Jet0 E)) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp.contDiff
  have h := hcomp.comp hpair
  simpa [Function.comp_def] using h

set_option synthInstance.maxHeartbeats 50000 in
theorem deturckPsi1'_fderiv_contDiff :
    ContDiff ℝ ∞ (fderiv ℝ (deturckPsi1' E)) := by
  apply deturckPsi1'_contDiff.fderiv_right
  show ((∞ : ℕ∞ω) + 1 ≤ ∞)
  simp

/-- The universal 1-jet map on the 2-jet (via projection). -/
noncomputable def deturckPsi1 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    : Jet2 E → (E →L[ℝ] E) :=
  fun j => deturckPsi1' E (j.1, j.2.1)

theorem deturckPsi1_contDiff : ContDiff ℝ ∞ (deturckPsi1 E) := by
  unfold deturckPsi1
  apply deturckPsi1'_contDiff.comp
  have h1 : ContDiff ℝ ∞ (fun j : Jet2 E => j.1) := contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun j : Jet2 E => j.2.1) :=
    contDiff_fst.comp contDiff_snd
  exact h1.prodMk h2

/-- The pairing map as a continuous linear map (isometry by `opNorm_prod`).
Used to bundle the 1-jet derivative from the 2-jet. -/
noncomputable def prodPairCLM {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ((E →L[ℝ] F) × (E →L[ℝ] G)) →L[ℝ] (E →L[ℝ] (F × G)) where
  toFun p := p.1.prod p.2
  map_add' p q := by
    have h1 : (p + q).1 = p.1 + q.1 := rfl
    have h2 : (p + q).2 = p.2 + q.2 := rfl
    rw [h1, h2]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.prod_apply, add_apply, Prod.mk_add_mk]
  map_smul' c p := by
    have h1 : (c • p).1 = c • p.1 := rfl
    have h2 : (c • p).2 = c • p.2 := rfl
    rw [h1, h2]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.prod_apply, smul_apply, Prod.smul_mk, RingHom.id_apply]
  cont := by
    have h : LipschitzWith 1 (fun p : (E →L[ℝ] F) × (E →L[ℝ] G) => p.1.prod p.2) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro p q
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : p.1.prod p.2 - q.1.prod q.2 = (p.1 - q.1).prod (p.2 - q.2) := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.prod_apply, sub_apply, Prod.mk_sub_mk]
      rw [hsub, ContinuousLinearMap.opNorm_prod, ← Prod.mk_sub_mk]
      simp
    exact h.continuous

theorem prodPairCLM_contDiff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ContDiff ℝ (∞ : ℕ∞ω) (prodPairCLM (E := E) (F := F) (G := G)) :=
  ContinuousLinearMap.contDiff _

/-- The universal 2-jet map: second chain rule via the paired derivative. -/
noncomputable def deturckPsi2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    : Jet2 E → (E →L[ℝ] E →L[ℝ] E) :=
  fun j =>
    (fderiv ℝ (deturckPsi1' E) (j.1, j.2.1)).comp
      (ContinuousLinearMap.prod j.2.1 j.2.2)

theorem deturckPsi2_contDiff : ContDiff ℝ ∞ (deturckPsi2 E) := by
  unfold deturckPsi2
  have hF : ContDiff ℝ ∞ (fun j : Jet2 E => fderiv ℝ (deturckPsi1' E) (j.1, j.2.1)) := by
    apply deturckPsi1'_fderiv_contDiff.comp
    have h1 : ContDiff ℝ ∞ (fun j : Jet2 E => j.1) := contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun j : Jet2 E => j.2.1) :=
      contDiff_fst.comp contDiff_snd
    exact h1.prodMk h2
  have hG : ContDiff ℝ ∞ (fun j : Jet2 E => ContinuousLinearMap.prod j.2.1 j.2.2) := by
    have h : (fun j : Jet2 E => ContinuousLinearMap.prod j.2.1 j.2.2)
        = (fun j : Jet2 E => prodPairCLM (E := E) (F := Jet0 E) (G := E →L[ℝ] Jet0 E) (j.2.1, j.2.2)) := by
      rfl
    rw [h]
    apply prodPairCLM_contDiff.comp
    have h1 : ContDiff ℝ ∞ (fun j : Jet2 E => j.2.1) :=
      contDiff_fst.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ (fun j : Jet2 E => j.2.2) :=
      contDiff_snd.comp contDiff_snd
    exact h1.prodMk h2
  have hpair := hF.prodMk hG
  have hcomp : ContDiff ℝ ∞
      (fun p : ((Jet1 E) →L[ℝ] (E →L[ℝ] E)) × (E →L[ℝ] (Jet1 E)) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp.contDiff
  have h := hcomp.comp hpair
  simpa [Function.comp_def] using h

/-- The 0-jet map on the full 2-jet (via 0-jet projection). -/
noncomputable def deturckPsi0_jet2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    : Jet2 E → E :=
  fun j => deturckPsi0 E j.1

theorem deturckPsi0_jet2_contDiff : ContDiff ℝ ∞ (deturckPsi0_jet2 E) :=
  deturckPsi0_contDiff.comp contDiff_fst

end RicciFlow
