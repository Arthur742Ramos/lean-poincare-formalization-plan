module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Derivative views of `C^3` DeTurck gauge flows

This small extension module keeps derivative-level gauge-flow adapters out of the
large gauge-reduction file.  It exposes the exact pointwise derivative hypothesis
used by derivative-level non-identity gauge routes from the more geometric
`SatisfiesGaugeFlowOn` statement.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology
open Set

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- The primitive pointwise derivative form of the intrinsic DeTurck gauge-flow equation
for a `C^3` diffeomorphism family. -/
def Diffeomorph3IntrinsicGaugeFlowDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))

/-- Within-time-set preferred-chart ODE data for the intrinsic DeTurck
gauge-flow equation.

This is the chart-local endpoint shape produced by closed-interval Picard
arguments: the curve is known to remain in the centered chart source relative
to the active time set, and the centered chart derivative is a
`HasDerivWithinAt` statement on that same time set. -/
def Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t) ∧
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t

/-- Extract the within-time-set source-neighborhood input from preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.eventuallyWithin_mem_source
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t :=
  (hchart t ht x).1

/-- Extract the within-time-set centered-chart derivative from preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.hasDerivWithinAt_extChartAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t :=
  (hchart t ht x).2

/-- Build within-time-set preferred-chart ODE data from local coordinate curves
that are eventually equal, in the within-filter, to the actual centered
preferred-chart coordinate curves. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_eventuallyEq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {coord : ℝ → M → ℝ → E}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t)
    (hcoord : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt (coord t x)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t)
    (heq : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x)) =ᶠ[𝓝[s] t] coord t x)
    (heq_t : ∀ t ∈ s, ∀ x : M,
      (extChartAt I ((Φ t) x)) ((Φ t) x) = coord t x t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x,
    (hcoord t ht x).congr_of_eventuallyEq (heq t ht x) (heq_t t ht x)⟩

/-- Restrict within-time-set preferred-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  have hsource : (fun σ : ℝ ↦ (Φ σ) x) ⁻¹'
      (extChartAt I ((Φ τ) x)).source ∈ 𝓝[s] τ :=
    (nhdsWithin_mono τ hst) (hchart τ (hst hτ) x).1
  exact ⟨hsource, (hchart τ (hst hτ) x).2.mono hst⟩

/-- Ordinary-at-time derivative form of the intrinsic DeTurck gauge-flow equation
for a `C^3` diffeomorphism family, restricted to times in `s`.

This is the shape produced by Picard-interior ODE arguments after upgrading
closed-interval derivatives to ordinary derivatives on the open time set. -/
def Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))

/-- Ordinary preferred-chart ODE data for the intrinsic DeTurck gauge-flow
equation, restricted to times in `s`.

The source-neighborhood clause is the chart-local continuity input used by the
existence layer: it says the curve stays eventually in the centered chart source
at the time where the ordinary chart derivative is taken. -/
def Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t) ∧
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t

/-- Extract the source-neighborhood input from ordinary preferred-chart ODE
data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.eventually_mem_source
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t :=
  (hchart t ht x).1

/-- Extract the ordinary centered-chart derivative from ordinary preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.hasDerivAt_extChartAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t :=
  (hchart t ht x).2

/-- Restrict ordinary preferred-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact hchart τ (hst hτ) x

/-- Within-time-set preferred-chart ODE data gives ordinary preferred-chart ODE
data whenever the time set is a neighborhood of each of its times. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hsource : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I ((Φ t) x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 (hs ht)] using (hchart t ht x).1
  exact ⟨hsource, (hchart t ht x).2.hasDerivAt (hs ht)⟩

/-- Build ordinary preferred-chart ODE data from local coordinate curves that
are eventually equal to the actual centered preferred-chart coordinate curves.
This is the transfer form used after a chart-local Picard solution has been
identified with the geometric coordinate readout near the time of interest. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_eventuallyEq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {coord : ℝ → M → ℝ → E}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t)
    (hcoord : ∀ t ∈ s, ∀ x : M,
      HasDerivAt (coord t x)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t)
    (heq : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x)) =ᶠ[𝓝 t] coord t x) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x, (hcoord t ht x).congr_of_eventuallyEq (heq t ht x)⟩

/-- Ordinary-at-time derivative data on `s` immediately gives the within-set
derivative data used by the primitive gauge-flow API. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact (hderiv t ht x).hasMFDerivWithinAt

/-- Within-time-set derivative data gives ordinary-at-time data whenever the
time set is a neighborhood of each of its times. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact (hderiv t ht x).hasMFDerivAt (hs ht)

/-- Restrict primitive within-time-set derivative data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact (hderiv τ (hst hτ) x).mono hst

/-- Restrict ordinary-at-time derivative data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact hderiv τ (hst hτ) x

/-- Closed-Picard-interval primitive derivative data gives ordinary derivative
data on the open Picard interior. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax : ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background (Ioo tmin tmax) := by
  intro t ht x
  exact (hderiv t (Ioo_subset_Icc_self ht) x).hasMFDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Closed-Picard-interval preferred-chart ODE data gives ordinary
preferred-chart ODE data on the open Picard interior. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax : ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background (Ioo tmin tmax) := by
  intro t ht x
  have htime : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hsource : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I ((Φ t) x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 htime] using
      (hchart t (Ioo_subset_Icc_self ht) x).1
  exact ⟨hsource, (hchart t (Ioo_subset_Icc_self ht) x).2.hasDerivAt htime⟩

/-- Fixed-IVP primitive derivative data for the intrinsic DeTurck gauges of all
chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP within-time-set preferred-chart ODE data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP ordinary-at-time derivative data for the intrinsic DeTurck gauges
of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP ordinary preferred-chart ODE data for the intrinsic DeTurck gauges
of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Ordinary-at-time fixed-IVP derivative data gives the within-set derivative
view expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_derivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    (I := I) (M := M) (hderiv sol)

/-- Fixed-IVP within-time-set derivative data gives ordinary-at-time derivative
data whenever each chosen solution time set is a neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_derivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    (I := I) (M := M) (hderiv sol) (htime sol)

/-- Fixed-IVP within-time-set preferred-chart ODE data gives ordinary
preferred-chart ODE data whenever each chosen solution time set is a
neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_chartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    (I := I) (M := M) (hchart sol) (htime sol)

/-- A `C^3` diffeomorphism family satisfying the DeTurck gauge-flow equation
also provides the primitive pointwise derivative data expected by the
derivative-level gauge-reduction APIs. -/
theorem SmoothSelfDiffeomorph3Family.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hflow : SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x))) := by
  simpa using hflow.hasMFDerivWithinAt ht x

/-- For `C^3` diffeomorphism families, the geometric intrinsic DeTurck
gauge-flow statement is equivalent to the primitive derivative data used by
the derivative-level theorem packages. -/
theorem SmoothSelfDiffeomorph3Family.satisfiesGaugeFlowOn_intrinsic_iff_derivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s ↔
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  constructor
  · intro hflow t ht x
    exact Φ.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn hflow ht x
  · intro hderiv
    exact SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (Φ := Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (s := s)
      (fun t ht x ↦ hderiv t ht x)

/-- Family-level primitive derivative data for the intrinsic DeTurck gauges of all
chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level within-time-set preferred-chart ODE data for the intrinsic
DeTurck gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level ordinary-at-time derivative data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level ordinary preferred-chart ODE data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Ordinary-at-time family derivative data gives the within-set derivative-family
view expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_derivativeAtFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    (I := I) (M := M) (hderiv ivp sol)

/-- Family-level within-time-set derivative data gives ordinary-at-time
derivative data whenever each chosen solution time set is a neighborhood at its
times. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_derivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3)
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    (I := I) (M := M) (hderiv ivp sol) (htime ivp sol)

/-- Family-level within-time-set preferred-chart ODE data gives ordinary
preferred-chart ODE data whenever each chosen solution time set is a
neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_chartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3)
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    (I := I) (M := M) (hchart ivp sol) (htime ivp sol)

/-- Family-level derivative data extracted from geometric `C^3` gauge-flow
solutions for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) maps3 := by
  intro ivp sol t ht x
  exact (maps3 ivp sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (hflow ivp sol) ht x

/-- A reusable bundle of geometric `C^3` intrinsic DeTurck gauge flows for all
chosen DeTurck local solutions of a fixed initial-value problem. -/
structure ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      (maps3 sol) ivp.initialTime
  satisfies : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- The derivative view of a bundled geometric gauge-flow family for one initial
value problem. -/
theorem derivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (G.maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro sol t ht x
  exact (G.maps3 sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (G.satisfies sol) ht x

/-- The anchored intrinsic DeTurck gauge associated to one solution in a bundled
geometric gauge-flow family for a fixed initial-value problem. -/
def gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 sol) (G.anchored sol) (G.satisfies sol)

/-- The same anchored gauge, constructed through the derivative-family view. -/
def gaugeViaDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 sol) (G.anchored sol) (G.derivativeData sol)

@[simp] theorem gauge_maps
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gauge sol).maps = G.maps3 sol := rfl

@[simp] theorem gaugeViaDerivative_maps
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gaugeViaDerivative sol).maps = G.maps3 sol := rfl

@[simp] theorem gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol) =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gaugeViaDerivative sol) := rfl

/-- Build the actual time derivative of a fixed-IVP gauge-pulled metric from the scalar
inner-product derivative at every fixed pair of tangent vectors. -/
theorem hasTimeDerivativeOn_of_innerHasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M)
    (Φ := G.maps3 sol)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (gdot := sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv sol)

/-- Extract the scalar inner-product derivative data for a fixed-IVP geometric
gauge-flow bundle from a time derivative of the actual gauge-pulled metric. -/
theorem innerHasDerivAt_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ ↦
        (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
          (((G.maps3 sol) τ) x)
          (((G.maps3 sol) τ).pushforwardTangent x u)
          (((G.maps3 sol) τ).pushforwardTangent x v))
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gauge sol) t x u v) t := by
  simpa using
    sol.1.gaugeCorrectedPullbackMetric_inner_hasDerivAt_of_hasTimeDerivativeOn
      (G.gauge sol) (hpullDerivative sol) ht x u v

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- A reusable bundle of geometric `C^3` intrinsic DeTurck gauge flows for all
chosen DeTurck local solutions in a theorem-family argument. -/
structure ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily where
  maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 ivp sol) ivp.initialTime
  satisfies : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- Restrict a theorem-family gauge-flow bundle to one initial-value problem. -/
def forInitialValueProblem
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := G.maps3 ivp
  anchored := G.anchored ivp
  satisfies := G.satisfies ivp

/-- The derivative-family view of a bundled geometric gauge-flow family. -/
theorem derivativeFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) G.maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (I := I) (M := M) G.maps3 G.satisfies

/-- The anchored intrinsic DeTurck gauge associated to one member of a bundled
geometric gauge-flow family. -/
def gauge
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.satisfies ivp sol)

/-- The same anchored gauge, constructed through the derivative-family view.  This
matches derivative-level APIs whose scalar derivative formula references
`of_hasMFDerivWithinAt`. -/
def gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.derivativeFamily ivp sol)

@[simp] theorem gauge_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gauge ivp sol).maps = G.maps3 ivp sol := rfl

@[simp] theorem gaugeViaDerivative_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gaugeViaDerivative ivp sol).maps = G.maps3 ivp sol := rfl

/-- The concrete corrected pullback velocity depends on the underlying `C^3`
diffeomorphism family, not on whether the anchored gauge was constructed from the
geometric flow statement or from its derivative view. -/
@[simp] theorem gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol) =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gaugeViaDerivative ivp sol) := rfl

/-- Build theorem-family time derivatives of the actual gauge-pulled metrics from scalar
inner-product derivative data for the bundled non-identity `C^3` gauges. -/
theorem hasTimeDerivativeOn_of_innerHasDerivAt
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_innerHasDerivAt
    (hderiv ivp) sol

/-- Extract the scalar inner-product derivative data for a theorem-family
geometric gauge-flow bundle from time derivatives of the actual gauge-pulled
metrics. -/
theorem innerHasDerivAt_of_hasTimeDerivativeOn
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ ↦
        (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
          (((G.maps3 ivp sol) τ) x)
          (((G.maps3 ivp sol) τ).pushforwardTangent x u)
          (((G.maps3 ivp sol) τ).pushforwardTangent x v))
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gauge ivp sol) t x u v) t := by
  simpa using
    (G.forInitialValueProblem ivp).innerHasDerivAt_of_hasTimeDerivativeOn
      (hpullDerivative ivp) sol ht x u v

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from a
geometric `C^3` gauge-flow family once the actual gauge-pulled metric has the
concrete corrected velocity as its time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    G.maps3 G.anchored G.derivativeFamily
    (fun ivp sol ↦ by
      simpa using hpullDerivative ivp sol)

/-- Intrinsic Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G hpullDerivative).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G hpullDerivative).toOrdinary

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from a
geometric `C^3` gauge-flow family once the scalar inner-product derivative of the
pulled-back metric has the concrete corrected velocity. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G (G.hasTimeDerivativeOn_of_innerHasDerivAt hderiv)

/-- Intrinsic Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G hderiv).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G hderiv).toOrdinary

/-- A chosen-background DeTurck theorem package becomes gauge-reducible from a
geometric `C^3` gauge-flow bundle once the actual gauge-pulled metric has the
concrete corrected velocity as its time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    G.maps3 G.anchored G.derivativeData
    (fun sol ↦ by
      simpa using hpullDerivative sol)

/-- Intrinsic Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G hpullDerivative).toIntrinsic

/-- Ordinary Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G hpullDerivative).toOrdinary

/-- A chosen-background DeTurck theorem package becomes gauge-reducible from a
geometric `C^3` gauge-flow bundle once the scalar inner-product derivative of the
pulled-back metric has the concrete corrected velocity. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G (G.hasTimeDerivativeOn_of_innerHasDerivAt hderiv)

/-- Intrinsic Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G hderiv).toIntrinsic

/-- Ordinary Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G hderiv).toOrdinary

end RicciFlow
