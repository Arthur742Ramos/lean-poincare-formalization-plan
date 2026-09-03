import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Trace

/-!
# Auditable Ricci--DeTurck transport and metric-cone evolution

This Challenge exposes a small but typed coordinate model of the gauge-reduction
mechanism.  A metric is a continuous bilinear form, its Ricci tensor is the
metric composed with a specified Ricci endomorphism, and scalar curvature is
the finite-dimensional trace of that endomorphism.  The selected differential
statement derives the pullback velocity from independent Fréchet and time
derivative data; it does not assume the derivative it is meant to prove.

The final two declarations package the analytic capstone: Picard--Lindelöf
evolution inside the cone of symmetric positive-definite forms and uniqueness
of cone-valued solutions.  The full project source contains the manifold-level
chart and gauge-flow infrastructure that instantiates this coordinate model.
-/

@[expose] public noncomputable section

open Function intervalIntegral MeasureTheory Metric Set
open scoped NNReal Topology
open ODE

namespace PoincareCurvature.Palomar

abbrev BilinearForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

abbrev MetricFamily (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ → M → BilinearForm E

abbrev RicciEndomorphismFamily
    (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ → M → E →L[ℝ] E

abbrev GaugeFamily (M : Type*) := ℝ → M → M

abbrev TangentTransportFamily
    (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ → M → (E ≃L[ℝ] E)

/-- Compose a continuous bilinear form with independent maps in its two slots. -/
noncomputable def composeBilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) (A B : E →L[ℝ] E) : BilinearForm E :=
  (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) B).comp
    ((ContinuousLinearMap.precompR E g).comp A)

@[simp] theorem composeBilinear_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) (A B : E →L[ℝ] E) (u v : E) :
    composeBilinear g A B u v = g (A u) (B v) := by
  simp [composeBilinear, ContinuousLinearMap.precompR]

/-- The Ricci tensor associated with a metric and a specified Ricci endomorphism. -/
def ricciTensor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) (R : E →L[ℝ] E) : BilinearForm E :=
  g.comp R

/-- Pull back a metric by a gauge map and an invertible tangent transport. -/
noncomputable def pullbackMetric
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) : MetricFamily M E :=
  fun t x ↦ composeBilinear (metric t (φ t x))
    (P t x).toContinuousLinearMap (P t x).toContinuousLinearMap

@[simp] theorem pullbackMetric_apply
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) (t : ℝ) (x : M) (u v : E) :
    pullbackMetric metric φ P t x u v =
      metric t (φ t x) (P t x u) (P t x v) := by
  simp [pullbackMetric]

def ricciTensorFamily
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (R : RicciEndomorphismFamily M E) :
    MetricFamily M E :=
  fun t x ↦ ricciTensor (metric t x) (R t x)

/-- Transport the Ricci endomorphism by the tangent equivalence. -/
noncomputable def conjugatedRicciEndomorphism
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : RicciEndomorphismFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) : RicciEndomorphismFamily M E :=
  fun t x ↦ (P t x).symm.toContinuousLinearMap.comp
    ((R t (φ t x)).comp (P t x).toContinuousLinearMap)

/-- Scalar curvature is the trace of the specified Ricci endomorphism. -/
def scalarCurvatureFamily
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : RicciEndomorphismFamily M E) : ℝ → M → ℝ :=
  fun t x ↦ LinearMap.trace ℝ E (R t x).toLinearMap

def IsSymmetricPositiveDefiniteForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) : Prop :=
  (∀ u v, g u v = g v u) ∧ ∀ u, u ≠ 0 → 0 < g u u

/-- The positive-definite cone in the state space of bilinear forms. -/
def RicciMetricCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : Set (BilinearForm E) :=
  {g | IsSymmetricPositiveDefiniteForm g}

/-- The Ricci vector field on the fixed tangent model. -/
def ricciFlowVectorField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → E →L[ℝ] E) : ℝ → BilinearForm E → BilinearForm E :=
  fun t g ↦ (-2 : ℝ) • ricciTensor g (R t)

/-- The chain-rule velocity of a pulled-back metric. -/
noncomputable def pullbackMetricVelocity
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E)
    (Dmetric : ℝ × M → (ℝ × M) →L[ℝ] BilinearForm E)
    (V : ℝ → M → M) (DP : ℝ → M → E →L[ℝ] E) : MetricFamily M E :=
  fun t x ↦
    composeBilinear (Dmetric (t, φ t x) (1, V t x))
        (P t x).toContinuousLinearMap (P t x).toContinuousLinearMap +
      composeBilinear (metric t (φ t x)) (DP t x)
        (P t x).toContinuousLinearMap +
      composeBilinear (metric t (φ t x)) (P t x).toContinuousLinearMap (DP t x)

/-- The source equation after evaluating at the gauge image. -/
def SatisfiesRicciDeTurckEquation
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (metricVelocity : MetricFamily M E)
    (R : RicciEndomorphismFamily M E) (correction : MetricFamily M E)
    (φ : GaugeFamily M) (P : TangentTransportFamily M E) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    metricVelocity t (φ t x) (P t x u) (P t x v) =
      (-2 : ℝ) * ricciTensorFamily metric R t (φ t x) (P t x u) (P t x v) +
        correction t x u v

/-- Intrinsic Ricci flow, with the metric and Ricci tensor tied by their types. -/
def IsIntrinsicRicciFlow
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric velocity : MetricFamily M E) (R : RicciEndomorphismFamily M E)
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    HasDerivAt (fun τ ↦ metric τ x u v) (velocity t x u v) t ∧
      velocity t x u v = (-2 : ℝ) * ricciTensorFamily metric R t x u v

/-- Independent C¹ data yield the actual derivative of the gauge pullback. -/
theorem gauge_pullback_has_derivAt_of_C1_data
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E)
    (Dmetric : ℝ × M → (ℝ × M) →L[ℝ] BilinearForm E)
    (V : ℝ → M → M) (DP : ℝ → M → E →L[ℝ] E)
    (hmetric : ∀ t x, HasFDerivAt
      (fun q : ℝ × M ↦ metric q.1 q.2) (Dmetric (t, x)) (t, x))
    (hφ : ∀ t x, HasDerivAt (fun τ ↦ φ τ x) (V t x) t)
    (hP : ∀ t x, HasDerivAt (fun τ ↦ (P τ x).toContinuousLinearMap)
      (DP t x) t)
    (t : ℝ) (x : M) (u v : E) :
    HasDerivAt (fun τ ↦ pullbackMetric metric φ P τ x u v)
      (pullbackMetricVelocity metric φ P Dmetric V DP t x u v) t := by
  sorry

/-- The Ricci tensor commutes with pullback when its endomorphism is conjugated. -/
theorem ricciTensor_pullback_transport
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (R : RicciEndomorphismFamily M E)
    (φ : GaugeFamily M) (P : TangentTransportFamily M E) :
    pullbackMetric (ricciTensorFamily metric R) φ P =
      ricciTensorFamily (pullbackMetric metric φ P)
        (conjugatedRicciEndomorphism R φ P) := by
  sorry

/-- The scalar trace is preserved by the same Ricci transport. -/
theorem scalarCurvature_pullback_transport
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (R : RicciEndomorphismFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) :
    scalarCurvatureFamily (conjugatedRicciEndomorphism R φ P) =
      fun t x ↦ scalarCurvatureFamily R t (φ t x) := by
  funext t x
  change LinearMap.trace ℝ E
      (((P t x).symm.toContinuousLinearMap.comp
        ((R t (φ t x)).comp (P t x).toContinuousLinearMap)).toLinearMap) =
    LinearMap.trace ℝ E (R t (φ t x)).toLinearMap
  rw [show
    ((P t x).symm.toContinuousLinearMap.comp
      ((R t (φ t x)).comp (P t x).toContinuousLinearMap)).toLinearMap =
      (P t x).symm.toLinearEquiv.conj (R t (φ t x)).toLinearMap by
        rw [LinearEquiv.conj_apply]
        ext z
        simp]
  exact LinearMap.trace_conj' _ _

/-- The DeTurck correction cancels after the pulled-back evaluation. -/
theorem gauge_corrected_velocity_eq_neg_two_pullbackRicci
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (metricVelocity : MetricFamily M E)
    (R : RicciEndomorphismFamily M E) (correction correctedVelocity : MetricFamily M E)
    (φ : GaugeFamily M) (P : TangentTransportFamily M E) (s : Set ℝ)
    (hsource : SatisfiesRicciDeTurckEquation metric metricVelocity R correction φ P s)
    (hcorrected : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      correctedVelocity t x u v =
        metricVelocity t (φ t x) (P t x u) (P t x v) - correction t x u v)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : E) :
    correctedVelocity t x u v =
      (-2 : ℝ) * ricciTensorFamily metric R t (φ t x) (P t x u) (P t x v) := by
  rw [hcorrected ht x u v, hsource ht x u v]
  ring

/-- Pullback by an invertible tangent transport preserves positive-definiteness. -/
theorem pullbackMetric_preserves_symmetricPositiveDefinite
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) {t : ℝ} {x : M}
    (hmetric : IsSymmetricPositiveDefiniteForm (metric t (φ t x))) :
    IsSymmetricPositiveDefiniteForm (pullbackMetric metric φ P t x) := by
  sorry

/-- C¹ gauge data plus the source equation produce the intrinsic Ricci flow law. -/
theorem ricciDeTurckGaugeReduction
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (metricVelocity : MetricFamily M E)
    (R : RicciEndomorphismFamily M E) (correction correctedVelocity : MetricFamily M E)
    (φ : GaugeFamily M) (P : TangentTransportFamily M E) (s : Set ℝ)
    (Dmetric : ℝ × M → (ℝ × M) →L[ℝ] BilinearForm E)
    (V : ℝ → M → M) (DP : ℝ → M → E →L[ℝ] E)
    (hmetric : ∀ t x, HasFDerivAt
      (fun q : ℝ × M ↦ metric q.1 q.2) (Dmetric (t, x)) (t, x))
    (hφ : ∀ t x, HasDerivAt (fun τ ↦ φ τ x) (V t x) t)
    (hP : ∀ t x, HasDerivAt (fun τ ↦ (P τ x).toContinuousLinearMap)
      (DP t x) t)
    (hvelocity : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x,
      correctedVelocity t x = pullbackMetricVelocity metric φ P Dmetric V DP t x)
    (hsource : SatisfiesRicciDeTurckEquation metric metricVelocity R correction φ P s)
    (hcorrected : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      correctedVelocity t x u v =
        metricVelocity t (φ t x) (P t x u) (P t x v) - correction t x u v) :
    IsIntrinsicRicciFlow (pullbackMetric metric φ P) correctedVelocity
      (conjugatedRicciEndomorphism R φ P) s := by
  sorry

/-- Ricci evolution that remains in the positive-definite metric cone. -/
theorem metricCone_local_flow_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax)
    {g₀ : BilinearForm E} {a L K : ℝ≥0} (R : ℝ → E →L[ℝ] E)
    (hpicard : IsPicardLindelof (ricciFlowVectorField R) t₀ g₀ a 0 L K)
    (hcone : closedBall g₀ a ⊆ RicciMetricCone) :
    ∃ g : ℝ → BilinearForm E, g t₀ = g₀ ∧
      (∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt g (ricciFlowVectorField R t (g t)) (Icc tmin tmax) t) ∧
      ∀ t ∈ Icc tmin tmax, g t ∈ RicciMetricCone := by
  sorry

/-- Uniqueness of two positive-definite Ricci-flow solutions. -/
theorem metricCone_local_flow_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {R : ℝ → E →L[ℝ] E} {tmin tmax : ℝ} {K : ℝ≥0}
    {α β : ℝ → BilinearForm E}
    (hLip : ∀ t ∈ Ico tmin tmax,
      LipschitzOnWith K (ricciFlowVectorField R t) RicciMetricCone)
    (hαcont : ContinuousOn α (Icc tmin tmax))
    (hαderiv : ∀ t ∈ Ico tmin tmax,
      HasDerivWithinAt α (ricciFlowVectorField R t (α t)) (Ici t) t)
    (hαstate : ∀ t ∈ Icc tmin tmax, α t ∈ RicciMetricCone)
    (hβcont : ContinuousOn β (Icc tmin tmax))
    (hβderiv : ∀ t ∈ Ico tmin tmax,
      HasDerivWithinAt β (ricciFlowVectorField R t (β t)) (Ici t) t)
    (hβstate : ∀ t ∈ Icc tmin tmax, β t ∈ RicciMetricCone)
    (hinitial : α tmin = β tmin) :
    EqOn α β (Icc tmin tmax) ∧
      (∀ t ∈ Icc tmin tmax, α t ∈ RicciMetricCone) ∧
      (∀ t ∈ Icc tmin tmax, β t ∈ RicciMetricCone) := by
  sorry

end PoincareCurvature.Palomar
