import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Trace

/-!
# Ricci-DeTurck gauge reduction

The Ricci-DeTurck method replaces the geometric Ricci-flow equation by a
gauge-fixed equation and then removes the gauge correction by pulling the
metric back along an anchored flow.  This Challenge records the auditable
algebraic and differential core of that step: pullback evaluation, cancellation
of the DeTurck term, preservation of the initial tensor, the intrinsic
`-2 Ric` evolution law, and conjugation invariance of the Ricci trace.

The fixed tangent model keeps the statement small while retaining the
mathematical transport identity.  The full project source contains the
corresponding manifold-level gauge-reduction package.
-/

@[expose] public noncomputable section

namespace PoincareCurvature.Palomar

abbrev BilinearFamily (M E : Type*) := ℝ → M → E → E → ℝ
abbrev GaugeFamily (M : Type*) := ℝ → M → M
abbrev TangentMapFamily (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ → M → E →L[ℝ] E

/-- Pull back a time-dependent bilinear tensor by a gauge map and its tangent map. -/
def pullbackBilinear
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearFamily M E) (φ : GaugeFamily M)
    (P : TangentMapFamily M E) : BilinearFamily M E :=
  fun t x u v ↦ g t (φ t x) (P t x u) (P t x v)

/-- The source Ricci--DeTurck equation after evaluating at the gauge image. -/
def SatisfiesDeTurckEquation
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (velocity ricci correction : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    velocity t (φ t x) (P t x u) (P t x v) =
      (-2 : ℝ) * ricci t (φ t x) (P t x u) (P t x v) + correction t x u v

/-- Intrinsic Ricci flow written as scalar time derivatives and the `-2 Ric` law. -/
def IsIntrinsicRicciFlow
    {M E : Type*} (metric velocity ricci : BilinearFamily M E) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    HasDerivAt (fun τ ↦ metric τ x u v) (velocity t x u v) t ∧
      velocity t x u v = (-2 : ℝ) * ricci t x u v

@[simp] theorem pullbackBilinear_apply
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearFamily M E) (φ : GaugeFamily M)
    (P : TangentMapFamily M E) (t : ℝ) (x : M) (u v : E) :
    pullbackBilinear g φ P t x u v =
      g t (φ t x) (P t x u) (P t x v) := by
  sorry

/-- The gauge-corrected velocity is the intrinsic `-2 Ric` velocity after
the DeTurck correction cancels the source equation's gauge term. -/
theorem gauge_corrected_velocity_eq_neg_two_pullbackRicci
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (velocity ricci correction correctedVelocity : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ)
    (hsource : SatisfiesDeTurckEquation velocity ricci correction φ P s)
    (hcorrected : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      correctedVelocity t x u v =
        velocity t (φ t x) (P t x u) (P t x v) - correction t x u v)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : E) :
    correctedVelocity t x u v =
      (-2 : ℝ) * pullbackBilinear ricci φ P t x u v := by
  sorry

/-- The scalar derivative of a gauge-pulled metric is exactly the corrected
velocity supplied by the gauge-flow calculation. -/
theorem gauge_reduction_has_derivAt
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric correctedVelocity : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      HasDerivAt (fun τ ↦ pullbackBilinear metric φ P τ x u v)
        (correctedVelocity t x u v) t)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : E) :
    HasDerivAt (fun τ ↦ pullbackBilinear metric φ P τ x u v)
      (correctedVelocity t x u v) t := by
  sorry

/-- An anchored gauge preserves the initial bilinear tensor. -/
theorem anchored_pullbackBilinear_eq_initial
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : BilinearFamily M E) (φ : GaugeFamily M)
    (P : TangentMapFamily M E) (initialMetric : M → E → E → ℝ)
    (t₀ : ℝ)
    (hanchor : ∀ x : M, φ t₀ x = x)
    (htransport : ∀ (x : M) (u : E), P t₀ x u = u)
    (hinitial : ∀ (x : M) (u v : E), metric t₀ x u v = initialMetric x u v) :
    pullbackBilinear metric φ P t₀ = initialMetric := by
  sorry

/-- The abstract Ricci--DeTurck gauge-reduction theorem: transport data,
the source equation, and the pulled-back metric derivative produce an
intrinsic Ricci flow. -/
theorem ricciDeTurckGaugeReduction
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric velocity ricci correction correctedVelocity : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ)
    (hsource : SatisfiesDeTurckEquation velocity ricci correction φ P s)
    (hcorrected : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      correctedVelocity t x u v =
        velocity t (φ t x) (P t x u) (P t x v) - correction t x u v)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      HasDerivAt (fun τ ↦ pullbackBilinear metric φ P τ x u v)
        (correctedVelocity t x u v) t) :
    IsIntrinsicRicciFlow (pullbackBilinear metric φ P) correctedVelocity
      (pullbackBilinear ricci φ P) s := by
  sorry

/-- The trace of a finite-dimensional endomorphism is invariant under
linear conjugation, the algebraic curvature transport used by the
Ricci--DeTurck reduction. -/
theorem trace_conjugation_invariant
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃ₗ[ℝ] E) (R : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (e.conj R) = LinearMap.trace ℝ E R := by
  sorry

/-- Scalar velocity readout after curvature transport by a tangent
conjugation. -/
theorem gauge_reduction_trace_readout
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (c : ℝ) (e : E ≃ₗ[ℝ] E) (R : E →ₗ[ℝ] E) :
    c * LinearMap.trace ℝ E (e.conj R) =
      c * LinearMap.trace ℝ E R := by
  sorry

end PoincareCurvature.Palomar
