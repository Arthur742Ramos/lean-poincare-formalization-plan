module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Existence interfaces for `C^3` DeTurck gauge flows

This module isolates the remaining raw gauge-flow existence obligation from the
Ricci-flow theorem packages.  A future manifold ODE-flow construction should
produce `Diffeomorph3GaugeFlowOn` witnesses; this file turns those witnesses into
the fixed-IVP and theorem-family geometric gauge-flow bundles consumed by the
endpoint Ricci-flow APIs.
-/

@[expose] public noncomputable section

open Bundle
open Set
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- A concrete `C^3` diffeomorphism flow for a time-dependent vector field on a
time set, anchored at a base time.  This is the raw object expected from the
future manifold ODE-flow existence theorem. -/
structure Diffeomorph3GaugeFlowOn
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps3 t₀
  satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
    maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s

namespace Diffeomorph3GaugeFlowOn

/-- Extract the pointwise manifold derivative statement from a raw `C^3`
gauge-flow witness on its time set. -/
theorem hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  G.satisfies.hasMFDerivWithinAt ht x

/-- Raw gauge-flow curves have the expected within-time-set derivative in the
preferred chart centered at their time-`t` value. -/
theorem hasDerivWithinAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) s t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivWithinAt ht x) (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- A raw gauge-flow witness is continuous within its time set along every base
point. -/
theorem continuousWithinAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ (G.maps3 τ) x) s t :=
  (G.hasMFDerivWithinAt ht x).continuousWithinAt

/-- A raw gauge-flow witness is continuous on its time set along every base
point. -/
theorem continuousOn_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ (G.maps3 τ) x) s :=
  fun _t ht ↦ G.continuousWithinAt_eval ht x

/-- Raw gauge-flow curves are continuous within the time set in the preferred
chart centered at the base time value. -/
theorem continuousWithinAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) s t :=
  (G.hasDerivWithinAt_extChartAt_eval ht x).continuousWithinAt

/-- Within the raw gauge-flow time set, the image of a fixed base point
eventually remains in the preferred tangent-bundle trivialization centered at
its time-`t` image. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝[s] t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousWithinAt_eval ht x).preimage_mem_nhdsWithin
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- A raw gauge-flow witness on a closed Picard interval supplies an ordinary
manifold derivative at interior times. -/
theorem hasMFDerivAt_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  (G.satisfies.satisfiesAt (Icc_mem_nhds ht.1 ht.2)).hasMFDerivAt x

/-- Interior raw gauge-flow curves have the expected derivative in the preferred
chart centered at their time-`t` value. -/
theorem hasDerivAt_extChartAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt_of_mem_Ioo ht x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- A raw gauge-flow witness on a closed Picard interval is continuous at
interior times along every base point. -/
theorem continuousAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (G.maps3 τ) x) t :=
  (G.hasMFDerivAt_of_mem_Ioo ht x).continuousAt

/-- A closed-interval raw gauge-flow witness is continuous on the open Picard
interior along every base point. -/
theorem continuousOn_eval_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (x : M) :
    ContinuousOn (fun τ : ℝ ↦ (G.maps3 τ) x) (Ioo tmin tmax) :=
  fun _t ht ↦ (G.continuousAt_eval_of_mem_Ioo ht x).continuousWithinAt

/-- Interior raw gauge-flow curves are continuous in the preferred chart centered
at the time-`t` value. -/
theorem continuousAt_extChartAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) t :=
  (G.hasDerivAt_extChartAt_eval_of_mem_Ioo ht x).continuousAt

/-- Interior times of a closed-interval raw gauge flow have the tangent-chart
membership needed for coordinate pullback formulas. -/
theorem eventually_mem_trivializationAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousAt_eval_of_mem_Ioo ht x).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- A raw gauge-flow witness on a time set gives a local-at-time gauge-flow
statement whenever the time set is a neighborhood of that time. -/
theorem satisfiesAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) :
    SatisfiesGaugeFlowAt (I := I) (M := M)
      G.maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X t :=
  G.satisfies.satisfiesAt hs

/-- Extract the unrestricted manifold derivative statement from a raw gauge-flow
witness on a neighborhood of the time. -/
theorem hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  (G.satisfiesAt hs).hasMFDerivAt x

/-- At any time where the raw time set is a neighborhood, a raw gauge-flow curve
has the expected derivative in the preferred chart centered at its time-`t`
value. -/
theorem hasDerivAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt hs x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- A raw gauge-flow witness is continuous in time along every base point at
times where its time set is a neighborhood. -/
theorem continuousAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (G.maps3 τ) x) t :=
  (G.hasMFDerivAt hs x).continuousAt

/-- Near any time where the raw gauge-flow equation holds on a neighborhood,
the image of a fixed base point remains in the preferred tangent-bundle
trivialization centered at its time-`t` image. -/
theorem eventually_mem_trivializationAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousAt_eval hs x).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- Package a geometric `SatisfiesGaugeFlowOn` statement as a raw `C^3`
diffeomorphism gauge-flow witness. -/
def of_satisfiesGaugeFlowOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
      maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := maps3
  anchored := anchored
  satisfies := satisfies

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from the pointwise
manifold derivative form produced by ODE/integral-curve theorems. -/
noncomputable def of_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := maps3
  anchored := anchored
  satisfies := SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (Φ := maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
    (X := X) (s := s) hderiv

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from
unrestricted pointwise manifold derivatives. -/
noncomputable def of_hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t _ht x ↦ (hderiv t x).hasMFDerivWithinAt)

/-- Restrict a raw `C^3` gauge flow to a smaller time set. -/
def mono
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := G.satisfies.mono hst

/-- If the time-dependent vector field vanishes on the time set, the identity `C³`
diffeomorphism family is a raw gauge flow. -/
noncomputable def identity_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)
  anchored := SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t₀
  satisfies := SmoothSelfDiffeomorph3Family.id_satisfiesGaugeFlowOn_of_eq_zero
    (I := I) (M := M) (X := X) (s := s) hX

/-- If every tangent fiber is a subsingleton, the identity `C³` diffeomorphism
family is a raw gauge flow for any time-dependent vector field. -/
noncomputable def identity_of_subsingleton_tangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun t _ht x ↦ Subsingleton.elim (X t x) 0)

/-- Model-space version of `identity_of_subsingleton_tangent`. -/
noncomputable def identity_of_subsingleton_model
    [Subsingleton E]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_subsingleton_tangent (I := I) (M := M) X s t₀

/-- On an empty manifold, the identity `C³` diffeomorphism family is a raw gauge
flow for any time-dependent vector field. -/
noncomputable def identity_of_isEmpty
    [IsEmpty M]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun _t _ht x ↦ isEmptyElim x)

/-- Specialize a raw flow for the intrinsic DeTurck vector field to the anchored
gauge object used by gauge reduction. -/
def toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M) (g := g) (background := background)
    (s := s) (t₀ := t₀) G.maps3 G.anchored G.satisfies

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).maps = G.maps3 := rfl

end Diffeomorph3GaugeFlowOn

/-- Raw intrinsic DeTurck `C^3` gauge-flow existence data for every chosen
DeTurck local solution of a fixed initial-value problem. -/
structure IntrinsicDeTurckGaugeFlowExistence
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  flow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistence

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from pointwise
manifold derivative data.  This is the adapter expected when an ODE theorem
directly returns `HasMFDerivAt[s]` integral-curve witnesses. -/
noncomputable def of_hasMFDerivWithinAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data. -/
noncomputable def of_hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivWithinAt (I := I) (M := M) (ivp := ivp)
    maps3 anchored (fun sol t _ht x ↦ (hderiv sol t x).hasMFDerivWithinAt)

/-- If the intrinsic DeTurck gauge field vanishes on every local solution's time
set, the identity diffeomorphism family supplies the raw `C³` gauge-flow
existence data for a fixed IVP. -/
noncomputable def identityOfGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (hzero sol)

/-- Chosen-background intrinsic DeTurck solutions have zero intrinsic DeTurck gauge field, so the
identity diffeomorphism family supplies the raw `C³` gauge-flow existence data for a fixed IVP. -/
noncomputable def identityOfChosenBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (fun t _ht x ↦ by
        have hLC :
            CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
              (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background :=
          usesChosenBackground_isLeviCivita
            (I := I) (M := M) sol.1 sol.2
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background hLC
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- When every tangent fiber is a subsingleton, the intrinsic DeTurck vector field vanishes
identically, so the identity `C³` diffeomorphism family supplies the raw gauge-flow existence
data for any chosen DeTurck local solution of a fixed initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_subsingleton_tangent
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, every tangent fiber is automatically subsingleton, so the identity `C³` family
supplies raw gauge-flow existence data. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  identityOfSubsingletonTangent (I := I) (M := M) ivp

/-- On an empty manifold, the gauge-flow obligation is vacuous, so the identity `C³` diffeomorphism
family supplies the raw gauge-flow existence data for any chosen DeTurck local solution of a fixed
initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_isEmpty
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
def toDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := fun sol ↦ (G.flow sol).maps3
  anchored := fun sol ↦ (G.flow sol).anchored
  satisfies := fun sol ↦ (G.flow sol).satisfies

/-- For a fixed-IVP package whose intrinsic DeTurck gauge field vanishes on each
solution's time set, the identity raw gauge flow supplies the required pullback
metric time derivative. -/
theorem identityOfGaugeFieldEqZero_hpullDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0)
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
          hzero).toDiffeomorph3GaugeFlow).maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
          hzero).toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (hzero sol)
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  intro t ht x u v
  have hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t
  have hu : (gauge3.maps t).pushforwardTangent x u = u := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x u = u
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
  have hv : (gauge3.maps t).pushforwardTangent x v = v := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x v = v
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
  have hvec :
      sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t = 0 := by
    rw [sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField]
    have hsource :
        intrinsicDeTurckVectorField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t = 0 := by
      funext y
      simpa [intrinsicDeTurckGaugeField] using hzero sol t ht y
    rw [hsource]
    funext y
    rw [SmoothSelfDiffeomorph2.pullbackVectorField_apply]
    exact ContinuousLinearMap.map_zero ((gauge3.maps t).pullbackTangent y)
  let pulledConnection :=
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t
  have hcov :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) = 0 := by
    rw [hvec]
    exact CovariantDerivative.zero (cov := pulledConnection)
  have hcovu :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u = 0 := by
    exact congrArg (fun A => A u) (congrFun hcov x)
  have hcovv :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v = 0 := by
    exact congrArg (fun A => A v) (congrFun hcov x)
  have hleft :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    rw [hcovu]
    exact congrArg (fun L : (TangentSpace I : M → Type _) x →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.map_zero
        (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x))
  have hright :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    rw [hcovv]
    exact ContinuousLinearMap.map_zero
      (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u)
  have hleftExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    simpa [pulledConnection] using hleft
  have hrightExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    simpa [pulledConnection] using hright
  have hpoint :
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    change sol.1.toIntrinsicDeTurckSolution.metricVelocity t
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x) u v =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v
    rw [SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x]
  have hvelocity :
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
    rw [hu, hv, hleftExact, hrightExact, zero_add, sub_zero]
    exact hpoint
  rw [hvelocity]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution ht x u v

/-- Package a fixed-IVP geometric intrinsic DeTurck gauge-flow bundle as raw
gauge-flow existence data. -/
def ofDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_satisfiesGaugeFlowOn
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (G.maps3 sol) (G.anchored sol) (G.satisfies sol)

/-- Package fixed-IVP named derivative data as raw gauge-flow existence data. -/
noncomputable def ofDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivWithinAt (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Derivative-family data extracted directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem derivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
      (G.flow sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht x
  exact (G.flow sol).hasMFDerivWithinAt ht x

@[simp] theorem toDiffeomorph3GaugeFlow_maps3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.maps3 sol) = (G.flow sol).maps3 := rfl

end IntrinsicDeTurckGaugeFlowExistence

/-- The theorem-family version of raw intrinsic DeTurck `C^3` gauge-flow
existence data. -/
structure IntrinsicDeTurckGaugeFlowExistenceFamily where
  flow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistenceFamily

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from pointwise
manifold derivative data.  This is the family-level adapter expected from a
future compact-manifold ODE-flow construction. -/
noncomputable def of_hasMFDerivWithinAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasMFDerivWithinAt
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data. -/
noncomputable def of_hasMFDerivAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivWithinAt (I := I) (M := M)
    maps3 anchored (fun ivp sol t _ht x ↦ (hderiv ivp sol t x).hasMFDerivWithinAt)

/-- If the intrinsic DeTurck gauge field vanishes on every theorem-family local
solution time set, the identity diffeomorphism family supplies raw `C³`
gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfGaugeFieldEqZero
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (hzero ivp)).flow sol

/-- Chosen-background intrinsic DeTurck solutions admit the identity raw `C³` gauge flow for every
initial-value problem. -/
noncomputable def identityOfChosenBackground :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- When every tangent fiber is a subsingleton, the identity `C³` diffeomorphism family supplies
the raw gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, the identity `C³` diffeomorphism family supplies raw gauge-flow existence data for
every initial-value problem. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  identityOfSubsingletonTangent (I := I) (M := M)

/-- On an empty manifold, the identity `C³` diffeomorphism family supplies the raw gauge-flow
existence data vacuously for every initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Restrict theorem-family raw gauge-flow existence data to one initial-value
problem. -/
def forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := G.flow ivp

/-- Turn theorem-family raw intrinsic gauge-flow existence data into the
geometric gauge-flow family consumed by endpoint routes. -/
def toDiffeomorph3GaugeFlowFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M) where
  maps3 := fun ivp sol ↦ (G.flow ivp sol).maps3
  anchored := fun ivp sol ↦ (G.flow ivp sol).anchored
  satisfies := fun ivp sol ↦ (G.flow ivp sol).satisfies

/-- Package a theorem-family geometric intrinsic DeTurck gauge-flow bundle as raw
gauge-flow existence data. -/
def ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M)
      (G.forInitialValueProblem ivp)).flow sol

/-- Package theorem-family named derivative data as raw gauge-flow existence
data. -/
noncomputable def ofDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivWithinAt (I := I) (M := M)
    maps3 anchored hflowDeriv

/-- Derivative-family data extracted directly from theorem-family raw intrinsic
DeTurck gauge-flow existence. -/
theorem derivativeFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M)
      (fun ivp sol ↦ (G.flow ivp sol).maps3) := by
  intro ivp sol
  exact (G.forInitialValueProblem ivp).derivativeData sol

/-- The family-level chosen-background raw flow induces the same anchored gauge as the existing
identity `C³` gauge attached to a chosen-background solution. -/
theorem identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((identityOfChosenBackground
        (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol =
      sol.1.identityDiffeomorph3GaugeOn
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2) := by
  unfold ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.gauge
  unfold toDiffeomorph3GaugeFlowFamily identityOfChosenBackground
  unfold IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
  unfold IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn
  unfold identityDiffeomorph3GaugeOn_of_isLeviCivita
  unfold AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
  congr

/-- For the chosen-background identity raw gauge-flow family, the gauge-corrected pullback metric
has the original intrinsic DeTurck metric velocity. -/
theorem identityOfChosenBackground_hpullDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let hbackground :=
    usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
  rw [identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (E := E) (H := H) (I := I) (M := M) ivp sol,
    sol.1.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity hbackground]
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    sol.1.toIntrinsicDeTurckSolution.metricVelocity
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution

/-- For any theorem-family whose intrinsic DeTurck gauge field vanishes on each
solution's time set, the identity raw gauge-flow family supplies the required
pullback metric time derivative. -/
theorem identityOfGaugeFieldEqZero_hpullDerivative
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) hzero).toDiffeomorph3GaugeFlowFamily).maps3
            ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) hzero).toDiffeomorph3GaugeFlowFamily).gauge
            ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (hzero ivp sol)
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  intro t ht x u v
  have hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t
  have hx : (gauge3.maps t) x = x := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x = x
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x
  have hu : (gauge3.maps t).pushforwardTangent x u = u := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x u = u
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
  have hv : (gauge3.maps t).pushforwardTangent x v = v := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x v = v
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
  have hvec :
      sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t = 0 := by
    rw [sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField]
    have hsource :
        intrinsicDeTurckVectorField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t = 0 := by
      funext y
      simpa [intrinsicDeTurckGaugeField] using hzero ivp sol t ht y
    rw [hsource]
    funext y
    rw [SmoothSelfDiffeomorph2.pullbackVectorField_apply]
    exact ContinuousLinearMap.map_zero ((gauge3.maps t).pullbackTangent y)
  let pulledConnection :=
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t
  have hcov :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) = 0 := by
    rw [hvec]
    exact CovariantDerivative.zero (cov := pulledConnection)
  have hcovu :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u = 0 := by
    exact congrArg (fun A => A u) (congrFun hcov x)
  have hcovv :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v = 0 := by
    exact congrArg (fun A => A v) (congrFun hcov x)
  have hleft :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    rw [hcovu]
    exact congrArg (fun L : (TangentSpace I : M → Type _) x →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.map_zero
        (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x))
  have hright :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    rw [hcovv]
    exact ContinuousLinearMap.map_zero
      (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u)
  have hleftExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    simpa [pulledConnection] using hleft
  have hrightExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    simpa [pulledConnection] using hright
  have hpoint :
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    change sol.1.toIntrinsicDeTurckSolution.metricVelocity t
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x) u v =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v
    rw [SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x]
  have hvelocity :
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
    rw [hu, hv, hleftExact, hrightExact, zero_add, sub_zero]
    exact hpoint
  rw [hvelocity]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution ht x u v

@[simp] theorem toDiffeomorph3GaugeFlowFamily_forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (G.toDiffeomorph3GaugeFlowFamily.forInitialValueProblem ivp) =
      (G.forInitialValueProblem ivp).toDiffeomorph3GaugeFlow := rfl

/-- For the subsingleton-tangent identity raw gauge-flow family, the gauge-corrected pullback
metric has the original intrinsic DeTurck metric velocity. The proof routes through the
chosen-background `_hpullDerivative` because both constructors produce the same identity flow. -/
theorem identityOfSubsingletonTangent_hpullDerivative
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfSubsingletonTangent
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfSubsingletonTangent
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  identityOfChosenBackground_hpullDerivative
    (E := E) (H := H) (I := I) (M := M) ivp sol

/-- Model-space variant of `identityOfSubsingletonTangent_hpullDerivative`. -/
theorem identityOfSubsingletonModel_hpullDerivative
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfSubsingletonModel
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfSubsingletonModel
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  identityOfChosenBackground_hpullDerivative
    (E := E) (H := H) (I := I) (M := M) ivp sol

/-- For the empty-manifold identity raw gauge-flow family, the gauge-corrected pullback metric
has the original intrinsic DeTurck metric velocity vacuously. -/
theorem identityOfIsEmpty_hpullDerivative
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfIsEmpty
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfIsEmpty
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro t _ht x
  exact isEmptyElim x

end IntrinsicDeTurckGaugeFlowExistenceFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible directly from raw
intrinsic `C^3` gauge-flow existence data and a pulled-back metric time-derivative proof. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G.toDiffeomorph3GaugeFlowFamily hpullDerivative

/-- Intrinsic Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toOrdinary

/-- Gauge-reducible theorem-family projection when the intrinsic DeTurck gauge
field vanishes on each solution's time set.

This uses the identity raw `C³` gauge-flow family and the bundled zero-field
pullback time-derivative theorem, so callers only provide the pointwise gauge
field vanishing hypothesis. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) hzero)
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfGaugeFieldEqZero_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) hzero)

/-- Intrinsic Ricci-flow theorem-family projection from a chosen DeTurck package
whose intrinsic DeTurck gauge field vanishes on each solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFieldEqZero hzero).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a chosen DeTurck package
whose intrinsic DeTurck gauge field vanishes on each solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFieldEqZero hzero).toOrdinary

/-- A chosen-background DeTurck theorem family becomes gauge-reducible directly from raw
intrinsic `C^3` gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G.toDiffeomorph3GaugeFlowFamily hderiv

/-- Intrinsic Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toOrdinary

/-- A fixed-IVP chosen-background DeTurck theorem package becomes gauge-reducible directly from
raw intrinsic `C^3` gauge-flow existence data and a pulled-back metric time-derivative proof. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G.toDiffeomorph3GaugeFlow hpullDerivative

/-- Fixed-IVP intrinsic Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toOrdinary

/-- Fixed-IVP gauge-reducible projection when the intrinsic DeTurck gauge field
vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp) hzero)
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp) hzero)

/-- Fixed-IVP intrinsic Ricci-flow projection when the intrinsic DeTurck gauge
field vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFieldEqZero hzero).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow projection when the intrinsic DeTurck gauge
field vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFieldEqZero hzero).toOrdinary

/-- A fixed-IVP chosen-background DeTurck theorem package becomes gauge-reducible directly from
raw intrinsic `C^3` gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G.toDiffeomorph3GaugeFlow hderiv

/-- Fixed-IVP intrinsic Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toOrdinary

end RicciFlow
