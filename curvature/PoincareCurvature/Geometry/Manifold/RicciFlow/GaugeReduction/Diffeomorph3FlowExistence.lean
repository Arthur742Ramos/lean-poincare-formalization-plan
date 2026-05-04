module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Separation.Hausdorff
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

/-- Within the raw time set, the pointwise derivative readout can be rewritten
to any vector field that agrees with the original one along the flow in the
relative filter at the time. -/
theorem hasMFDerivWithinAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) := by
  have hXYt_all : ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x) :=
    show t ∈ {τ : ℝ | ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)} from
      mem_of_mem_nhdsWithin ht hXY
  have hXYt : X t (G.maps3 t x) = Y t (G.maps3 t x) :=
    hXYt_all x
  simpa [hXYt] using G.hasMFDerivWithinAt ht x

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

/-- Raw gauge-flow curves have the expected within-time-set derivative in the
preferred chart, with the velocity rewritten by relative-filter agreement of
vector fields along the flow. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) s t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivWithinAt_congr_vectorField ht hXY x)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- A raw gauge-flow curve has the expected within-time-set derivative in the preferred chart
centered at its time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) s t := by
  have h := G.hasDerivWithinAt_extChartAt_eval ht x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- A raw gauge-flow curve has the centered within-time-set preferred-chart
derivative, with the velocity rewritten by relative-filter agreement of vector
fields along the flow. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) s t := by
  have h := G.hasDerivWithinAt_extChartAt_eval_congr_vectorField ht hXY x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := Y t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

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

/-- Within the raw gauge-flow time set, the image of a fixed base point
eventually remains in the preferred chart source centered at its time-`t` image. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝[s] t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousWithinAt_eval ht x).preimage_mem_nhdsWithin
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

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

/-- Interior raw gauge-flow curves have the expected derivative in the preferred chart centered at
the time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval_of_mem_Ioo ht x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

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

/-- Interior times of a closed-interval raw gauge flow have the preferred-chart
source membership needed for centered chart ODE formulas. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousAt_eval_of_mem_Ioo ht x).preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

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

/-- At a neighborhood time, a raw gauge-flow witness also satisfies any vector field that agrees
with the original one along the flow in a neighborhood of that time. -/
theorem satisfiesAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    SatisfiesGaugeFlowAt (I := I) (M := M)
      G.maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily Y t :=
  (G.satisfiesAt hs).congr_vectorField hXY

/-- At a neighborhood time, the pointwise derivative readout can be rewritten to any vector field
that agrees with the original one along the flow near that time. -/
theorem hasMFDerivAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) :=
  (G.satisfiesAt_congr_vectorField hs hXY).hasMFDerivAt x

/-- At a neighborhood time, the preferred-chart derivative readout can be
rewritten to any vector field that agrees with the original one along the flow
near that time. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt_congr_vectorField hs hXY x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- At a neighborhood time, the centered preferred-chart derivative readout can
be rewritten to any vector field that agrees with the original one along the
flow near that time. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval_congr_vectorField hs hXY x
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := Y t ((G.maps3 t) x)) hsrc_ext] at h
  exact h

/-- A closed-interval raw gauge-flow witness gives an ordinary interior derivative for any vector
field that agrees with the original one along the flow near the interior time. -/
theorem hasMFDerivAt_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) :=
  G.hasMFDerivAt_congr_vectorField (Icc_mem_nhds ht.1 ht.2) hXY x

/-- A closed-interval raw gauge-flow witness gives the ordinary interior
preferred-chart derivative for any vector field that agrees with the original
one along the flow near the interior time. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField
    (Icc_mem_nhds ht.1 ht.2) hXY x

/-- A closed-interval raw gauge-flow witness gives the ordinary interior
centered preferred-chart derivative for any vector field that agrees with the
original one along the flow near the interior time. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self_congr_vectorField
    (Icc_mem_nhds ht.1 ht.2) hXY x

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

/-- At neighborhood-times, raw gauge-flow curves have the expected derivative in the preferred chart
centered at the time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval hs x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- At neighborhood-times, raw gauge-flow curves are continuous in the preferred
chart centered at the time-`t` value. -/
theorem continuousAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) t :=
  (G.hasDerivAt_extChartAt_eval hs x).continuousAt

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

/-- Near any time where the raw gauge-flow equation holds on a neighborhood, the
image of a fixed base point remains in the preferred chart source centered at
its time-`t` image. -/
theorem eventually_mem_extChartAt_source_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousAt_eval hs x).preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

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

/-- Package a geometric gauge-flow statement as proof-level raw `C^3`
diffeomorphism gauge-flow existence. -/
theorem nonempty_of_satisfiesGaugeFlowOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
      maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_satisfiesGaugeFlowOn maps3 anchored satisfies⟩

/-- Package autonomous Mathlib integral-curve data for a `C³` diffeomorphism
family as a raw gauge-flow witness for the constant-in-time vector field. -/
def of_autonomousIntegralCurves
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ x : M,
      IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (maps3 t) x) X s) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀ :=
  of_satisfiesGaugeFlowOn maps3 anchored (by
    intro x t ht
    simpa using hcurves x t ht)

/-- Proof-level raw `C³` gauge-flow existence from autonomous Mathlib
integral-curve data for a `C³` diffeomorphism family. -/
theorem nonempty_of_autonomousIntegralCurves
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ x : M,
      IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (maps3 t) x) X s) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀) :=
  ⟨of_autonomousIntegralCurves maps3 anchored hcurves⟩

/-- Package autonomous Mathlib local integral-curve data at every time in `s`
for a `C³` diffeomorphism family as a raw gauge-flow witness for the
constant-in-time vector field. -/
def of_autonomousIntegralCurveAt
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ t ∈ s, ∀ x : M,
      IsMIntegralCurveAt (I := I) (fun τ : ℝ ↦ (maps3 τ) x) X t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀ :=
  of_satisfiesGaugeFlowOn maps3 anchored (by
    intro x t ht
    exact (hcurves t ht x).hasMFDerivAt.hasMFDerivWithinAt)

/-- Proof-level raw `C³` gauge-flow existence from autonomous Mathlib local
integral-curve data at every time in `s`. -/
theorem nonempty_of_autonomousIntegralCurveAt
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ t ∈ s, ∀ x : M,
      IsMIntegralCurveAt (I := I) (fun τ : ℝ ↦ (maps3 τ) x) X t) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀) :=
  ⟨of_autonomousIntegralCurveAt maps3 anchored hcurves⟩

/-- Extract Mathlib autonomous integral-curve data from a raw gauge-flow
witness for a constant-in-time vector field. -/
theorem autonomousIntegralCurveOn
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀)
    (x : M) :
    IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (G.maps3 t) x) X s := by
  intro t ht
  simpa using G.satisfies x t ht

/-- Two anchored raw `C³` autonomous gauge flows for the same `C¹` vector field
agree on the open interval where both solve the ODE. -/
theorem eqOn_eval_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Ioo tmin tmax) := by
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) (t₀ := t₀) ht₀ hX
    (G₁.autonomousIntegralCurveOn x)
    (G₂.autonomousIntegralCurveOn x) ?_
  have h₁ :
      (G₁.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
  have h₂ :
      (G₂.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
  rw [h₁, h₂]

/-- Pointwise form of autonomous raw gauge-flow uniqueness on an open interval. -/
theorem eval_eq_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Ioo_boundaryless G₂ ht₀ hX x ht

/-- Time-slice diffeomorphism form of autonomous raw gauge-flow uniqueness on
an open interval. -/
theorem eqOn_maps3_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Ioo tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eval_eq_of_autonomous_Ioo_boundaryless G₂ ht₀ hX ht x

/-- Pointwise time-slice diffeomorphism form of autonomous raw gauge-flow
uniqueness on an open interval. -/
theorem maps3_eq_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless G₂ ht₀ hX ht

/-- Two anchored raw `C³` autonomous gauge flows for the same `C¹` vector field
agree on a closed interval once the anchor lies in its interior.  The endpoint
identification is the continuous extension of Mathlib's boundaryless
autonomous uniqueness theorem on the open interval. -/
theorem eqOn_eval_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Icc tmin tmax) := by
  have hIoo :
      EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
        (Ioo tmin tmax) := by
    refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (I := I) (t₀ := t₀) ht₀ hX
      ((G₁.autonomousIntegralCurveOn x).mono (fun _t ht ↦ Ioo_subset_Icc_self ht))
      ((G₂.autonomousIntegralCurveOn x).mono (fun _t ht ↦ Ioo_subset_Icc_self ht)) ?_
    have h₁ :
        (G₁.maps3 t₀) x = x :=
      SmoothSelfDiffeomorph3Family.AnchoredAt.apply
        (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
    have h₂ :
        (G₂.maps3 t₀) x = x :=
      SmoothSelfDiffeomorph3Family.AnchoredAt.apply
        (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
    rw [h₁, h₂]
  have hne : tmin ≠ tmax := ne_of_lt (lt_trans ht₀.1 ht₀.2)
  refine Set.EqOn.of_subset_closure hIoo
    (G₁.continuousOn_eval x) (G₂.continuousOn_eval x)
    (fun _t ht ↦ Ioo_subset_Icc_self ht) ?_
  intro t ht
  rw [closure_Ioo hne]
  exact ht

/-- Pointwise form of autonomous raw gauge-flow uniqueness on a closed interval
with the anchor in the interior. -/
theorem eval_eq_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Icc_boundaryless G₂ ht₀ hX x ht

/-- Time-slice diffeomorphism form of autonomous raw gauge-flow uniqueness on a
closed interval with the anchor in the interior. -/
theorem eqOn_maps3_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Icc tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eval_eq_of_autonomous_Icc_boundaryless G₂ ht₀ hX ht x

/-- Pointwise time-slice diffeomorphism form of autonomous raw gauge-flow
uniqueness on a closed interval with the anchor in the interior. -/
theorem maps3_eq_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Icc_boundaryless G₂ ht₀ hX ht

/-- Common-open-subinterval form of autonomous raw gauge-flow uniqueness.  The
two raw flows may live on different ambient time sets, as long as both contain
the visible open Picard interval. -/
theorem eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Ioo tmin tmax) := by
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) (t₀ := t₀) ht₀ hX
    ((G₁.autonomousIntegralCurveOn x).mono h₁)
    ((G₂.autonomousIntegralCurveOn x).mono h₂) ?_
  have hG₁ :
      (G₁.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
  have hG₂ :
      (G₂.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
  rw [hG₁, hG₂]

/-- Common-open-subinterval time-slice diffeomorphism form of autonomous raw
gauge-flow uniqueness. -/
theorem eqOn_maps3_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Ioo tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-open-subinterval form of autonomous raw gauge-flow
uniqueness. -/
theorem eval_eq_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-open-subinterval time-slice diffeomorphism form of
autonomous raw gauge-flow uniqueness. -/
theorem maps3_eq_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX ht

/-- Common-closed-subinterval form of autonomous raw gauge-flow uniqueness.  The
endpoint equality is obtained by extending the common open-subinterval equality
using the continuity of both ambient raw flows on the shared closed interval. -/
theorem eqOn_eval_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Icc tmin tmax) := by
  have hIoo :
      EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
        (Ioo tmin tmax) :=
    G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
      (fun _t ht ↦ h₁ (Ioo_subset_Icc_self ht))
      (fun _t ht ↦ h₂ (Ioo_subset_Icc_self ht))
      ht₀ hX x
  have hne : tmin ≠ tmax := ne_of_lt (lt_trans ht₀.1 ht₀.2)
  refine Set.EqOn.of_subset_closure hIoo
    ((G₁.continuousOn_eval x).mono h₁)
    ((G₂.continuousOn_eval x).mono h₂)
    (fun _t ht ↦ Ioo_subset_Icc_self ht) ?_
  intro t ht
  rw [closure_Ioo hne]
  exact ht

/-- Common-closed-subinterval time-slice diffeomorphism form of autonomous raw
gauge-flow uniqueness. -/
theorem eqOn_maps3_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Icc tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eqOn_eval_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-closed-subinterval form of autonomous raw gauge-flow
uniqueness. -/
theorem eval_eq_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-closed-subinterval time-slice diffeomorphism form of
autonomous raw gauge-flow uniqueness. -/
theorem maps3_eq_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX ht

/-- Reinterpret a raw `C³` gauge-flow witness for an equal vector field along the flow image. -/
def congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := G.satisfies.congr_vectorField hXY

/-- Reinterpret a raw `C³` gauge-flow witness when two vector fields agree
along the flow image in the relative time-set filter at each time. -/
def congr_vectorField_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := SatisfiesGaugeFlowOn.congr_vectorField_nhdsWithin
    (I := I) (M := M) G.satisfies hXY

/-- Reinterpret a raw `C³` gauge-flow witness when two vector fields agree on the time set. -/
def congr_vectorField_of_eqOn
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t x = Y t x) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ :=
  G.congr_vectorField (fun t ht x ↦ hXY t ht (G.maps3 t x))

@[simp] theorem congr_vectorField_maps3
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).maps3 = G.maps3 := rfl

@[simp] theorem congr_vectorField_nhdsWithin_maps3
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).maps3 = G.maps3 := rfl

@[simp] theorem congr_vectorField_anchored
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).anchored = G.anchored := rfl

@[simp] theorem congr_vectorField_nhdsWithin_anchored
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).anchored = G.anchored := rfl

@[simp] theorem congr_vectorField_satisfies
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).satisfies = G.satisfies.congr_vectorField hXY := rfl

@[simp] theorem congr_vectorField_nhdsWithin_satisfies
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).satisfies =
      SatisfiesGaugeFlowOn.congr_vectorField_nhdsWithin
        (I := I) (M := M) G.satisfies hXY := rfl

/-- Transport proof-level raw `C³` gauge-flow existence across vector fields that agree on the
time set. -/
theorem nonempty_congr_vectorField_of_eqOn
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀))
    (hXY : ∀ t ∈ s, ∀ x : M, X t x = Y t x) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.congr_vectorField_of_eqOn hXY⟩

/-- Transport proof-level raw `C³` gauge-flow existence across vector fields
that agree in the relative time-set filter at each time. -/
theorem nonempty_congr_vectorField_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀))
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ x = Y τ x) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.congr_vectorField_nhdsWithin
    (fun t ht ↦ (hXY t ht).mono fun τ hτ x ↦ hτ (G.maps3 τ x))⟩

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

/-- Build proof-level raw `C^3` gauge-flow existence from the pointwise
within-time-set manifold derivative form produced by ODE/integral-curve
theorems. -/
theorem nonempty_of_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from the preferred-chart
ODE form of the derivative on the time set.

This is the chart-local adapter expected from Banach/Picard constructions:
instead of asking for a manifold derivative directly, it accepts continuity of
the raw curves and the derivative of the coordinate curve in the chart centered
at the endpoint. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored
    (fun t ht x ↦ by
      rw [HasMFDerivWithinAt]
      refine ⟨hcont t ht x, ?_⟩
      have h := hderiv t ht x
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at h
      simpa [writtenInExtChartAt] using h)

/-- Proof-level raw `C^3` gauge-flow existence from preferred-chart ODE
derivatives on the time set. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- A centered preferred-chart derivative gives continuity of the manifold
curve, provided the curve is eventually in the source of the centered chart. -/
theorem continuousWithinAt_eval_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {s : Set ℝ} {t : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)) (x : M)
    (hsource :
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    {v : TangentSpace I ((maps3 t) x)}
    (hderiv : HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x)) v s t) :
    ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t := by
  let e := extChartAt I ((maps3 t) x)
  have hx : (maps3 t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((maps3 t) x)
  have hsymm : ContinuousAt e.symm (e ((maps3 t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((maps3 t) x)
  have hchart : ContinuousWithinAt (fun τ : ℝ ↦ e ((maps3 τ) x)) s t := by
    simpa [e] using hderiv.continuousWithinAt
  have hcomp' : ContinuousWithinAt
      (e.symm ∘ fun τ : ℝ ↦ e ((maps3 τ) x)) s t :=
    ContinuousAt.comp_continuousWithinAt
      (g := e.symm) (f := fun τ : ℝ ↦ e ((maps3 τ) x))
      (s := s) (x := t) hsymm hchart
  have hcomp : ContinuousWithinAt
      (fun τ : ℝ ↦ e.symm (e ((maps3 τ) x))) s t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝[s] t, (maps3 τ) x ∈ e.source := by
    simpa [e] using hsource
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)
    (by simpa [e] using (e.left_inv hx).symm)

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from centered
preferred-chart ODE data, deriving manifold-curve continuity from eventual
membership in the centered chart source. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      continuousWithinAt_eval_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
        (I := I) (M := M) maps3 x (hsource t ht x) (hderiv t ht x))
    hderiv

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart
ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from centered preferred-chart ODE
data for a model vector field, after identifying that model field with the
target field along the candidate flow. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart ODE
data for a model vector field identified with the target field along the
candidate flow. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness from centered preferred-chart ODE
data for a model vector field, after identifying that model field with the
target field along the candidate flow in the relative time-set filter. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  (of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (s := s) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart
ODE data for a model vector field identified with the target field along the
candidate flow in the relative time-set filter. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from
ordinary pointwise manifold derivatives available at each time of `s`.  This
matches local ODE constructions that first promote a closed-interval derivative
to an ordinary derivative on the open time set, without requiring data outside
that time set. -/
noncomputable def of_hasMFDerivAtOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t ht x ↦ (hderiv t ht x).hasMFDerivWithinAt)

/-- Build proof-level raw `C^3` gauge-flow existence on `s` from ordinary
pointwise manifold derivatives available at each time of `s`. -/
theorem nonempty_of_hasMFDerivAtOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on the open Picard
interior from pointwise manifold derivative data proved within the closed
Picard interval. -/
noncomputable def of_hasMFDerivWithinAt_Icc
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasMFDerivAt[Icc tmin tmax] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasMFDerivAtOn (I := I) (M := M) (X := X)
    (s := Ioo tmin tmax) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      (hderiv t (Ioo_subset_Icc_self ht) x).hasMFDerivAt
        (Icc_mem_nhds ht.1 ht.2))

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
pointwise manifold derivative data proved within the closed Picard interval. -/
theorem nonempty_of_hasMFDerivWithinAt_Icc
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasMFDerivAt[Icc tmin tmax] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasMFDerivWithinAt_Icc maps3 anchored hderiv⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from named primitive derivative data proved within the closed Picard
interval. -/
noncomputable def of_intrinsicDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_hasMFDerivWithinAt_Icc (I := I) (M := M)
    (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀) maps3 anchored hderiv

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from named primitive derivative data proved within the closed Picard
interval. -/
theorem nonempty_of_intrinsicDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicDerivativeOn_Ioo maps3 anchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from ordinary
preferred-chart ODE derivatives available at each time of `s`. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦ (hcont t ht x).continuousWithinAt)
    (fun t ht x ↦ (hderiv t ht x).hasDerivWithinAt)

/-- Proof-level raw `C^3` gauge-flow existence on `s` from ordinary
preferred-chart ODE derivatives available at each time of `s`. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- An ordinary centered preferred-chart derivative gives ordinary continuity
of the manifold curve, provided the curve is eventually in the source of the
centered chart. -/
theorem continuousAt_eval_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {t : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)) (x : M)
    (hsource :
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    {v : TangentSpace I ((maps3 t) x)}
    (hderiv : HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x)) v t) :
    ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t := by
  let e := extChartAt I ((maps3 t) x)
  have hx : (maps3 t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((maps3 t) x)
  have hsymm : ContinuousAt e.symm (e ((maps3 t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((maps3 t) x)
  have hchart : ContinuousAt (fun τ : ℝ ↦ e ((maps3 τ) x)) t := by
    simpa [e] using hderiv.continuousAt
  have hcomp' : ContinuousAt
      (e.symm ∘ fun τ : ℝ ↦ e ((maps3 τ) x)) t :=
    ContinuousAt.comp
      (g := e.symm) (f := fun τ : ℝ ↦ e ((maps3 τ) x))
      (x := t) hsymm hchart
  have hcomp : ContinuousAt (fun τ : ℝ ↦ e.symm (e ((maps3 τ) x))) t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝 t, (maps3 τ) x ∈ e.source := by
    simpa [e] using hsource
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from ordinary centered
preferred-chart ODE data, deriving ordinary manifold-curve continuity from
eventual membership in the centered chart source. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      continuousAt_eval_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
        (I := I) (M := M) maps3 x (hsource t ht x) (hderiv t ht x))
    hderiv

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from ordinary centered preferred-chart
ODE data for a model vector field, after identifying that model field with the
target field along the candidate flow. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data for a model vector field identified with the target
field along the candidate flow. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness from ordinary centered
preferred-chart ODE data for a model vector field, after identifying that model
field with the target field along the candidate flow in the relative time-set
filter. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  (of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (s := s) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data for a model vector field identified with the target
field along the candidate flow in the relative time-set filter. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on the open Picard
interior from centered preferred-chart ODE data proved within the closed Picard
interval. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) (Icc tmin tmax) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := Ioo tmin tmax) (t₀ := t₀)
    maps3 anchored
    (fun t ht x ↦ by
      have htime : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      simpa [nhdsWithin_eq_nhds.2 htime] using
        hsource t (Ioo_subset_Icc_self ht) x)
    (fun t ht x ↦
      (hderiv t (Ioo_subset_Icc_self ht) x).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
centered preferred-chart ODE data proved within the closed Picard interval. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) (Icc tmin tmax) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field,
after identifying that model field with the target field along the candidate
flow on the closed interval. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field
identified with the target field along the candidate flow. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field,
after identifying that model field with the target field along the candidate
flow in the relative open-interval filter. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  (of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior
from closed-interval centered preferred-chart ODE data for a model vector field
identified with the target field along the candidate flow in the relative
open-interval filter. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from named preferred-chart ODE data proved within the closed Picard
interval, by first converting the chart ODE into primitive manifold derivative
data. -/
noncomputable def of_intrinsicChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_intrinsicDerivativeOn_Ioo (I := I) (M := M)
    (g := g) (background := background) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored
    (Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
      (I := I) (M := M) hchart)

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from named preferred-chart ODE data proved within the closed Picard
interval. -/
theorem nonempty_of_intrinsicChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicChartDerivativeOn_Ioo maps3 anchored hchart⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from unrestricted
ordinary centered preferred-chart ODE data plus eventual membership in the
centered chart source. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t : ℝ, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t _ht x ↦ hsource t x) (fun t _ht x ↦ hderiv t x)

/-- Proof-level raw `C^3` gauge-flow existence from unrestricted ordinary
centered preferred-chart ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t : ℝ, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

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
  of_hasMFDerivAtOn (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t _ht x ↦ hderiv t x)

/-- Build proof-level raw `C^3` gauge-flow existence on `s` from unrestricted
pointwise manifold derivatives. -/
theorem nonempty_of_hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

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

/-- Restrict proof-level raw `C^3` gauge-flow existence to a smaller time set. -/
theorem nonempty_mono
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀))
    (hst : s ⊆ t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.mono hst⟩

@[simp] theorem mono_maps3
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).maps3 = G.maps3 := rfl

@[simp] theorem mono_anchored
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).anchored = G.anchored := rfl

@[simp] theorem mono_satisfies
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).satisfies = G.satisfies.mono hst := rfl

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

/-- If the time-dependent vector field vanishes on the time set, the identity
`C³` diffeomorphism family gives proof-level raw gauge-flow existence. -/
theorem nonempty_identity_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_eq_zero X s t₀ hX⟩

/-- If every tangent fiber is a subsingleton, the identity `C³` diffeomorphism
family is a raw gauge flow for any time-dependent vector field. -/
noncomputable def identity_of_subsingleton_tangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun t _ht x ↦ Subsingleton.elim (X t x) 0)

/-- If every tangent fiber is a subsingleton, the identity `C³` diffeomorphism
family gives proof-level raw gauge-flow existence for any vector field. -/
theorem nonempty_identity_of_subsingleton_tangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_subsingleton_tangent X s t₀⟩

/-- Model-space version of `identity_of_subsingleton_tangent`. -/
noncomputable def identity_of_subsingleton_model
    [Subsingleton E]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_subsingleton_tangent (I := I) (M := M) X s t₀

/-- Model-space version of
`nonempty_identity_of_subsingleton_tangent`. -/
theorem nonempty_identity_of_subsingleton_model
    [Subsingleton E]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_subsingleton_model X s t₀⟩

/-- On an empty manifold, the identity `C³` diffeomorphism family is a raw gauge
flow for any time-dependent vector field. -/
noncomputable def identity_of_isEmpty
    [IsEmpty M]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun _t _ht x ↦ isEmptyElim x)

/-- On an empty manifold, the identity `C³` diffeomorphism family gives
proof-level raw gauge-flow existence for any vector field. -/
theorem nonempty_identity_of_isEmpty
    [IsEmpty M]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_isEmpty X s t₀⟩

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

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_anchored
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).anchored = G.anchored := rfl

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_follows
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).follows = G.satisfies := rfl

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

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from pointwise
within-time-set manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivWithinAt
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
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary pointwise manifold derivative data on each local solution's time set.
This is the adapter expected when the manifold ODE construction has already
converted within-interval equations to ordinary derivatives on the open
solution interval. -/
noncomputable def of_hasMFDerivAtOn
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
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasMFDerivAtOn
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary
pointwise manifold derivative data on each local solution's time set, kept as
proof-level evidence. -/
theorem nonempty_of_hasMFDerivAtOn
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
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from primitive derivative data proved on closed Picard intervals. -/
noncomputable def ofPicardIccDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G := Diffeomorph3GaugeFlowOn.of_intrinsicDerivativeOn_Ioo
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from primitive closed-Picard derivative data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccDerivative maps3 anchored tmin tmax htimeSet hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from preferred-chart ODE data proved on closed Picard intervals, routed
through the primitive derivative handoff. -/
noncomputable def ofPicardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccDerivative (I := I) (M := M) (ivp := ivp)
    maps3 anchored tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
        (I := I) (M := M) (hchart sol))

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from preferred-chart closed-Picard data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative maps3 anchored tmin tmax htimeSet hchart⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard preferred-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G :=
      Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard model-vector-field chart ODE data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard preferred-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G :=
      Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard model-vector-field chart ODE data and relative-filter
field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ (maps3 sol τ) x)
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hcont sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ (maps3 sol τ) x)
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousAt (fun τ : ℝ ↦ (maps3 sol τ) x) t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hcont sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousAt (fun τ : ℝ ↦ (maps3 sol τ) x) t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (Y := Y sol)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from same-time-set
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (Y := Y sol)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored (fun sol t _ht x ↦ hsource sol t x) (fun sol t _ht x ↦ hderiv sol t x)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership,
kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

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
  of_hasMFDerivAtOn (I := I) (M := M) (ivp := ivp)
    maps3 anchored (fun sol t _ht x ↦ hderiv sol t x)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivAt
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
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

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

/-- Fixed-IVP zero-gauge-field identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfGaugeFieldEqZero hzero⟩

/-- Package fixed-IVP named derivative data as raw gauge-flow existence data. -/
noncomputable def ofDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivWithinAt (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Package fixed-IVP named derivative data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofDerivative maps3 anchored hflowDeriv⟩

/-- Package fixed-IVP within-time-set preferred-chart ODE data as raw gauge-flow
existence data. This is the named chart-data analogue of
`of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored
    (fun sol t ht x ↦ (hchart sol t ht x).1)
    (fun sol t ht x ↦ (hchart sol t ht x).2)

/-- Package fixed-IVP within-time-set preferred-chart ODE data as proof-level raw
gauge-flow existence data. -/
theorem nonempty_ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofChartDerivative maps3 anchored hchart⟩

/-- Fixed-IVP within-time-set preferred-chart ODE data also supplies the existing
within-time-set derivative view directly. -/
theorem derivativeData_ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivative_of_chartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3) hchart

/-- Package fixed-IVP ordinary-at-time named derivative data as raw gauge-flow
existence data. -/
noncomputable def ofDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivAtOn (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Package fixed-IVP ordinary-at-time named derivative data as proof-level raw
gauge-flow existence data. -/
theorem nonempty_ofDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofDerivativeAt maps3 anchored hflowDeriv⟩

/-- Package fixed-IVP preferred-chart ODE data as raw gauge-flow existence data.
This is the named chart-data analogue of
`of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored
    (fun sol t ht x ↦ (hchart sol t ht x).1)
    (fun sol t ht x ↦ (hchart sol t ht x).2)

/-- Package fixed-IVP preferred-chart ODE data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofChartDerivativeAt maps3 anchored hchart⟩

/-- Fixed-IVP ordinary preferred-chart ODE data also supplies the existing
within-time-set derivative view directly. -/
theorem derivativeData_ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivative_of_derivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3) hchart)

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

/-- Chosen-background fixed-IVP identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfChosenBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfChosenBackground ivp⟩

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

/-- Fixed-IVP subsingleton-tangent identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfSubsingletonTangent ivp⟩

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, every tangent fiber is automatically subsingleton, so the identity `C³` family
supplies raw gauge-flow existence data. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  identityOfSubsingletonTangent (I := I) (M := M) ivp

/-- Fixed-IVP subsingleton-model identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfSubsingletonModel ivp⟩

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

/-- Fixed-IVP empty-manifold identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfIsEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfIsEmpty ivp⟩

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

/-- Pointwise manifold derivative read out directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem hasMFDerivWithinAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivWithinAt ht x

/-- Preferred-chart derivative read out directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem hasDerivWithinAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval ht x

/-- Preferred-chart derivative read out directly from fixed-IVP raw intrinsic DeTurck gauge-flow
existence, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_self ht x

/-- Fixed-IVP raw intrinsic gauge-flow derivatives can be rewritten to a
relative-neighborhood-equal vector field. -/
theorem hasMFDerivWithinAt_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivWithinAt_congr_vectorField ht hXY x

/-- Fixed-IVP raw intrinsic gauge-flow preferred-chart derivatives can be
rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_congr_vectorField ht hXY x

/-- Fixed-IVP raw intrinsic gauge-flow centered preferred-chart derivatives can
be rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_self_congr_vectorField ht hXY x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous within the solution
time set in preferred chart coordinates. -/
theorem continuousWithinAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).continuousWithinAt_extChartAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous within the solution
time set. -/
theorem continuousWithinAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).continuousWithinAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous on the solution time
set. -/
theorem continuousOn_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.flow sol).continuousOn_eval x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
tangent-bundle trivialization within the solution time set. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  (G.flow sol).eventuallyWithin_mem_trivializationAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the
preferred chart source within the solution time set. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  (G.flow sol).eventuallyWithin_mem_extChartAt_source_eval ht x

/-- Fixed-IVP open-Picard solution time sets are neighborhoods of each of their
times when the chosen solution time set has been identified with `Ioo tmin tmax`. -/
theorem timeSet_mem_nhds_of_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol)) :
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t := by
  intro sol t ht
  have ht' : t ∈ Ioo (tmin sol) (tmax sol) := by
    simpa [htimeSet sol] using ht
  simpa [htimeSet sol] using (isOpen_Ioo.mem_nhds ht')

/-- Ordinary pointwise manifold derivative read out directly from fixed-IVP raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivAt hs x

/-- Ordinary preferred-chart derivative read out directly from fixed-IVP raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasDerivAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval hs x

/-- Ordinary preferred-chart derivative read out directly from fixed-IVP raw intrinsic DeTurck
gauge-flow existence at neighborhood-times, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x)) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_self hs x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow derivatives can be rewritten to
a neighborhood-equal vector field. -/
theorem hasMFDerivAt_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivAt_congr_vectorField hs hXY x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow preferred-chart derivatives can
be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_congr_vectorField hs hXY x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x)) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_self_congr_vectorField hs hXY x

/-- Fixed-IVP raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times in preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x)) t :=
  (G.flow sol).continuousAt_extChartAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times. -/
theorem continuousAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t :=
  (G.flow sol).continuousAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
tangent-bundle trivialization at neighborhood-times. -/
theorem eventually_mem_trivializationAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  (G.flow sol).eventually_mem_trivializationAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
chart source at neighborhood-times. -/
theorem eventually_mem_extChartAt_source_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  (G.flow sol).eventually_mem_extChartAt_source_eval hs x

/-- Fixed-IVP open-Picard pointwise manifold derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasMFDerivAt_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  G.hasMFDerivAt sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard preferred-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard pointwise manifold derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  G.hasMFDerivAt_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard preferred-chart derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard preferred-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard centered preferred-chart derivative readout rewritten
to a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard continuity of raw intrinsic gauge-flow curves in
preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x)) t :=
  G.continuousAt_extChartAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard continuity of raw intrinsic gauge-flow curves. -/
theorem continuousAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t :=
  G.continuousAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard tangent-trivialization control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  G.eventually_mem_trivializationAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard chart-source control of raw intrinsic gauge-flow
curves. -/
theorem eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  G.eventually_mem_extChartAt_source_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

@[simp] theorem toDiffeomorph3GaugeFlow_maps3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.maps3 sol) = (G.flow sol).maps3 := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.anchored sol) = (G.flow sol).anchored := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_satisfies
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.satisfies sol) = (G.flow sol).satisfies := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.gauge sol) =
      (G.flow sol).toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn := rfl

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

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from pointwise
within-time-set manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivWithinAt
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
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary pointwise manifold derivative data on each local solution's time set. -/
noncomputable def of_hasMFDerivAtOn
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
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasMFDerivAtOn
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
pointwise manifold derivative data on each local solution's time set, kept as
proof-level evidence. -/
theorem nonempty_of_hasMFDerivAtOn
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
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from primitive derivative data proved on closed Picard intervals. -/
noncomputable def ofPicardIccDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from primitive closed-Picard derivative data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccDerivative maps3 anchored tmin tmax htimeSet hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from preferred-chart ODE data proved on closed Picard intervals. -/
noncomputable def ofPicardIccChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hchart ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from preferred-chart closed-Picard data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative maps3 anchored tmin tmax htimeSet hchart⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard preferred-chart ODE data for model vector fields,
after identifying those model fields with the intrinsic DeTurck gauge fields
along the candidate flows. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_vectorField_eq
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (Y ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard model-vector-field chart ODE data, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard preferred-chart ODE data for model vector fields,
after identifying those model fields with the intrinsic DeTurck gauge fields
along the candidate flows in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (Y ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard model-vector-field chart ODE data and
relative-filter field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x)
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hcont ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x)
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hcont ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (hsource ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from same-time-set
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data plus eventual chart-source membership on each
local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (hsource ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data for model vector fields, after identifying
those model fields with the intrinsic DeTurck gauge fields along the candidate
flows in the relative solution-time filters. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t _ht x ↦ hsource ivp sol t x)
    (fun ivp sol t _ht x ↦ hderiv ivp sol t x)

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership,
kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

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
  of_hasMFDerivAtOn (I := I) (M := M)
    maps3 anchored (fun ivp sol t _ht x ↦ hderiv ivp sol t x)

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivAt
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
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

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

/-- Theorem-family zero-gauge-field identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfGaugeFieldEqZero
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfGaugeFieldEqZero hzero⟩

/-- Chosen-background intrinsic DeTurck solutions have the identity raw `C³` gauge flow for every
initial-value problem. -/
noncomputable def identityOfChosenBackground :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Chosen-background theorem-family identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfChosenBackground :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfChosenBackground⟩

/-- When every tangent fiber is a subsingleton, the identity `C³` diffeomorphism family supplies
the raw gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Theorem-family subsingleton-tangent identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfSubsingletonTangent⟩

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, the identity `C³` diffeomorphism family supplies raw gauge-flow existence data for
every initial-value problem. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  identityOfSubsingletonTangent (I := I) (M := M)

/-- Theorem-family subsingleton-model identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonModel
    [Subsingleton E] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfSubsingletonModel⟩

/-- On an empty manifold, the identity `C³` diffeomorphism family supplies the raw gauge-flow
existence data vacuously for every initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Theorem-family empty-manifold identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfIsEmpty
    [IsEmpty M] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfIsEmpty⟩

/-- Restrict theorem-family raw gauge-flow existence data to one initial-value
problem. -/
def forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := G.flow ivp

@[simp] theorem forInitialValueProblem_flow
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).flow sol) = G.flow ivp sol := rfl

/-- Restrict proof-level theorem-family raw gauge-flow existence to one
initial-value problem. -/
theorem nonempty_forInitialValueProblem
    (hG : Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases hG with ⟨G⟩
  exact ⟨G.forInitialValueProblem ivp⟩

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

@[simp] theorem toDiffeomorph3GaugeFlowFamily_maps3
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.maps3 ivp sol) = (G.flow ivp sol).maps3 := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_anchored
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.anchored ivp sol) =
      (G.flow ivp sol).anchored := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_satisfies
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.satisfies ivp sol) =
      (G.flow ivp sol).satisfies := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_gauge
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.gauge ivp sol) =
      (G.flow ivp sol).toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn := rfl

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

/-- Package a theorem-family geometric intrinsic DeTurck gauge-flow bundle as
proof-level raw gauge-flow existence data. -/
theorem nonempty_ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDiffeomorph3GaugeFlowFamily G⟩

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

/-- Package theorem-family named derivative data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofDerivativeFamily
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
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDerivativeFamily maps3 anchored hflowDeriv⟩

/-- Package theorem-family within-time-set preferred-chart ODE data as raw
gauge-flow existence data. This is the named chart-data analogue of
theorem-family `of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).1)
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).2)

/-- Package theorem-family within-time-set preferred-chart ODE data as
proof-level raw gauge-flow existence data. -/
theorem nonempty_ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofChartDerivativeFamily maps3 anchored hchart⟩

/-- Theorem-family within-time-set preferred-chart ODE data also supplies the
existing within-time-set derivative-family view directly. -/
theorem derivativeFamily_ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_chartDerivativeFamily
    (I := I) (M := M) (maps3 := maps3) hchart

/-- Package theorem-family ordinary-at-time named derivative data as raw
gauge-flow existence data.  This is the named derivative-family analogue of
`of_hasMFDerivAtOn`. -/
noncomputable def ofDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivAtOn (I := I) (M := M)
    maps3 anchored hflowDeriv

/-- Package theorem-family ordinary-at-time named derivative data as proof-level
raw gauge-flow existence data. -/
theorem nonempty_ofDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDerivativeAtFamily maps3 anchored hflowDeriv⟩

/-- Package theorem-family preferred-chart ODE data as raw gauge-flow existence
data.  This is the named chart-data analogue of theorem-family
`of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).1)
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).2)

/-- Package theorem-family preferred-chart ODE data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofChartDerivativeAtFamily maps3 anchored hchart⟩

/-- Theorem-family ordinary preferred-chart ODE data also supplies the existing
within-time-set derivative-family view directly. -/
theorem derivativeFamily_ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_derivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
      (I := I) (M := M) (maps3 := maps3) hchart)

/-- Derivative-family data extracted directly from theorem-family raw intrinsic
DeTurck gauge-flow existence. -/
theorem derivativeFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M)
      (fun ivp sol ↦ (G.flow ivp sol).maps3) := by
  intro ivp sol
  exact (G.forInitialValueProblem ivp).derivativeData sol

/-- Pointwise manifold derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence. -/
theorem hasMFDerivWithinAt
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivWithinAt sol ht x

/-- Preferred-chart derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence. -/
theorem hasDerivWithinAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval sol ht x

/-- Preferred-chart derivative read out directly from theorem-family raw intrinsic DeTurck
gauge-flow existence, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_self sol ht x

/-- Theorem-family raw intrinsic gauge-flow derivatives can be rewritten to a
relative-neighborhood-equal vector field. -/
theorem hasMFDerivWithinAt_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivWithinAt_congr_vectorField sol ht hXY x

/-- Theorem-family raw intrinsic gauge-flow preferred-chart derivatives can be
rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_congr_vectorField
    sol ht hXY x

/-- Theorem-family raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    sol ht hXY x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous within the
solution time set in preferred chart coordinates. -/
theorem continuousWithinAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).continuousWithinAt_extChartAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous within the
solution time set. -/
theorem continuousWithinAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).continuousWithinAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous on the solution
time set. -/
theorem continuousOn_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).continuousOn_eval sol x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred tangent-bundle trivialization within the solution time set. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventuallyWithin_mem_trivializationAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred chart source within the solution time set. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventuallyWithin_mem_extChartAt_source_eval sol ht x

/-- Theorem-family open-Picard solution time sets are neighborhoods of each of
their times when each solution time set has been identified with `Ioo tmin tmax`. -/
theorem timeSet_mem_nhds_of_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t := by
  intro ivp sol t ht
  exact (G.forInitialValueProblem ivp).timeSet_mem_nhds_of_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht

/-- Ordinary pointwise manifold derivative read out directly from theorem-family
raw intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasMFDerivAt
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt sol hs x

/-- Ordinary preferred-chart derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasDerivAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval sol hs x

/-- Ordinary preferred-chart derivative read out directly from theorem-family raw intrinsic DeTurck
gauge-flow existence at neighborhood-times, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self sol hs x

/-- Ordinary theorem-family raw intrinsic gauge-flow derivatives can be
rewritten to a neighborhood-equal vector field. -/
theorem hasMFDerivAt_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_congr_vectorField sol hs hXY x

/-- Ordinary theorem-family raw intrinsic gauge-flow preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_congr_vectorField
    sol hs hXY x

/-- Ordinary theorem-family raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_congr_vectorField
    sol hs hXY x

/-- Theorem-family raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times in preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x)) t :=
  (G.forInitialValueProblem ivp).continuousAt_extChartAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times. -/
theorem continuousAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t :=
  (G.forInitialValueProblem ivp).continuousAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred tangent-bundle trivialization at neighborhood-times. -/
theorem eventually_mem_trivializationAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventually_mem_trivializationAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred chart source at neighborhood-times. -/
theorem eventually_mem_extChartAt_source_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventually_mem_extChartAt_source_eval sol hs x

/-- Theorem-family open-Picard pointwise manifold derivative readout without
an extra neighborhood-of-time hypothesis. -/
theorem hasMFDerivAt_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard preferred-chart derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard pointwise manifold derivative readout rewritten
to a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard preferred-chart derivative readout rewritten to
a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard preferred-chart derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard centered preferred-chart derivative readout
rewritten to a neighborhood-equal vector field, without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard continuity of raw intrinsic gauge-flow curves in
preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x)) t :=
  (G.forInitialValueProblem ivp).continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard continuity of raw intrinsic gauge-flow curves. -/
theorem continuousAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t :=
  (G.forInitialValueProblem ivp).continuousAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard tangent-trivialization control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard chart-source control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

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
