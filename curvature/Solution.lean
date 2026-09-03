import PoincareCurvature.Geometry.Manifold.RicciFlow.ResearchTheorems
import Mathlib.LinearAlgebra.Trace

public noncomputable section

namespace PoincareCurvature.Palomar

abbrev BilinearFamily (M E : Type*) := ℝ → M → E → E → ℝ
abbrev GaugeFamily (M : Type*) := ℝ → M → M
abbrev TangentMapFamily (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ → M → E →L[ℝ] E

def pullbackBilinear
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearFamily M E) (φ : GaugeFamily M)
    (P : TangentMapFamily M E) : BilinearFamily M E :=
  fun t x u v ↦ g t (φ t x) (P t x u) (P t x v)

def SatisfiesDeTurckEquation
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (velocity ricci correction : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    velocity t (φ t x) (P t x u) (P t x v) =
      (-2 : ℝ) * ricci t (φ t x) (P t x u) (P t x v) + correction t x u v

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
  rfl

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
  rw [hcorrected ht x u v, hsource ht x u v, pullbackBilinear]
  ring

theorem gauge_reduction_has_derivAt
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric correctedVelocity : BilinearFamily M E)
    (φ : GaugeFamily M) (P : TangentMapFamily M E) (s : Set ℝ)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
      HasDerivAt (fun τ ↦ pullbackBilinear metric φ P τ x u v)
        (correctedVelocity t x u v) t)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : E) :
    HasDerivAt (fun τ ↦ pullbackBilinear metric φ P τ x u v)
      (correctedVelocity t x u v) t :=
  hderiv ht x u v

theorem anchored_pullbackBilinear_eq_initial
    {M E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : BilinearFamily M E) (φ : GaugeFamily M)
    (P : TangentMapFamily M E) (initialMetric : M → E → E → ℝ)
    (t₀ : ℝ)
    (hanchor : ∀ x : M, φ t₀ x = x)
    (htransport : ∀ (x : M) (u : E), P t₀ x u = u)
    (hinitial : ∀ (x : M) (u v : E), metric t₀ x u v = initialMetric x u v) :
    pullbackBilinear metric φ P t₀ = initialMetric := by
  funext x u v
  simp only [pullbackBilinear, hanchor, htransport, hinitial]

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
  intro t ht x u v
  refine ⟨gauge_reduction_has_derivAt metric correctedVelocity φ P s hderiv ht x u v, ?_⟩
  exact gauge_corrected_velocity_eq_neg_two_pullbackRicci
    velocity ricci correction correctedVelocity φ P s hsource hcorrected ht x u v

theorem trace_conjugation_invariant
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃ₗ[ℝ] E) (R : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (e.conj R) = LinearMap.trace ℝ E R :=
  LinearMap.trace_conj' R e

theorem gauge_reduction_trace_readout
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (c : ℝ) (e : E ≃ₗ[ℝ] E) (R : E →ₗ[ℝ] E) :
    c * LinearMap.trace ℝ E (e.conj R) =
      c * LinearMap.trace ℝ E R := by
  rw [trace_conjugation_invariant e R]

end PoincareCurvature.Palomar
