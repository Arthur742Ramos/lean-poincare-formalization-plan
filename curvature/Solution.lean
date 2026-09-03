import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Trace

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

def ricciTensor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) (R : E →L[ℝ] E) : BilinearForm E :=
  g.comp R

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

noncomputable def conjugatedRicciEndomorphism
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : RicciEndomorphismFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) : RicciEndomorphismFamily M E :=
  fun t x ↦ (P t x).symm.toContinuousLinearMap.comp
    ((R t (φ t x)).comp (P t x).toContinuousLinearMap)

def scalarCurvatureFamily
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (R : RicciEndomorphismFamily M E) : ℝ → M → ℝ :=
  fun t x ↦ LinearMap.trace ℝ E (R t x).toLinearMap

def IsSymmetricPositiveDefiniteForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : BilinearForm E) : Prop :=
  (∀ u v, g u v = g v u) ∧ ∀ u, u ≠ 0 → 0 < g u u

def RicciMetricCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : Set (BilinearForm E) :=
  {g | IsSymmetricPositiveDefiniteForm g}

def ricciFlowVectorField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → E →L[ℝ] E) : ℝ → BilinearForm E → BilinearForm E :=
  fun t g ↦ (-2 : ℝ) • ricciTensor g (R t)

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

def IsIntrinsicRicciFlow
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric velocity : MetricFamily M E) (R : RicciEndomorphismFamily M E)
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ (x : M) (u v : E),
    HasDerivAt (fun τ ↦ metric τ x u v) (velocity t x u v) t ∧
      velocity t x u v = (-2 : ℝ) * ricciTensorFamily metric R t x u v

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
  have hq : HasDerivAt (fun τ : ℝ ↦ (τ, φ τ x)) (1, V t x) t :=
    (hasDerivAt_id' t).prodMk (hφ t x)
  have hgq : HasDerivAt (fun τ : ℝ ↦ metric τ (φ τ x))
      ((Dmetric (t, φ t x)) (1, V t x)) t := by
    have hcomp := HasFDerivAt.comp t
      (f := fun τ : ℝ ↦ (τ, φ τ x))
      (g := fun q : ℝ × M ↦ metric q.1 q.2)
      (hmetric t (φ t x)) hq.hasFDerivAt
    simpa [Function.comp_def] using hcomp.hasDerivAt
  have hPu : HasDerivAt
      (fun τ : ℝ ↦ (P τ x).toContinuousLinearMap u) (DP t x u) t := by
    simpa using (hP t x).clm_apply (hasDerivAt_const t u)
  have hPv : HasDerivAt
      (fun τ : ℝ ↦ (P τ x).toContinuousLinearMap v) (DP t x v) t := by
    simpa using (hP t x).clm_apply (hasDerivAt_const t v)
  have hgp := hgq.clm_apply hPu
  have hgpv := hgp.clm_apply hPv
  simpa [pullbackMetric, pullbackMetricVelocity, composeBilinear,
    ContinuousLinearMap.precompR, add_apply, add_assoc] using hgpv

theorem ricciTensor_pullback_transport
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (R : RicciEndomorphismFamily M E)
    (φ : GaugeFamily M) (P : TangentTransportFamily M E) :
    pullbackMetric (ricciTensorFamily metric R) φ P =
      ricciTensorFamily (pullbackMetric metric φ P)
        (conjugatedRicciEndomorphism R φ P) := by
  funext t x
  ext u v
  simp only [pullbackMetric, ricciTensorFamily, ricciTensor,
    composeBilinear_apply, conjugatedRicciEndomorphism,
    ContinuousLinearMap.comp_apply]
  simp

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

theorem pullbackMetric_preserves_symmetricPositiveDefinite
    {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : MetricFamily M E) (φ : GaugeFamily M)
    (P : TangentTransportFamily M E) {t : ℝ} {x : M}
    (hmetric : IsSymmetricPositiveDefiniteForm (metric t (φ t x))) :
    IsSymmetricPositiveDefiniteForm (pullbackMetric metric φ P t x) := by
  constructor
  · intro u v
    simp only [pullbackMetric, composeBilinear_apply]
    exact hmetric.1 (P t x u) (P t x v)
  · intro u hu
    have hPu : P t x u ≠ 0 := by
      intro hPu
      apply hu
      apply (P t x).injective
      simpa using hPu
    change 0 < metric t (φ t x) (P t x u) (P t x u)
    exact hmetric.2 (P t x u) hPu

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
  intro t ht x u v
  refine ⟨?_, ?_⟩
  · rw [hvelocity ht x]
    exact gauge_pullback_has_derivAt_of_C1_data metric φ P Dmetric V DP
      hmetric hφ hP t x u v
  · calc
      correctedVelocity t x u v =
          (-2 : ℝ) * ricciTensorFamily metric R t (φ t x) (P t x u) (P t x v) :=
        gauge_corrected_velocity_eq_neg_two_pullbackRicci metric metricVelocity R
          correction correctedVelocity φ P s hsource hcorrected ht x u v
      _ = (-2 : ℝ) * pullbackMetric (ricciTensorFamily metric R) φ P t x u v := by
        simp [pullbackMetric, composeBilinear_apply]
      _ = (-2 : ℝ) * ricciTensorFamily (pullbackMetric metric φ P)
          (conjugatedRicciEndomorphism R φ P) t x u v := by
        rw [ricciTensor_pullback_transport metric R φ P]

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
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpicard
    (Metric.mem_closedBall_self le_rfl)
  let β := α.compProj
  refine ⟨β, ?_, ?_, ?_⟩
  · change α.compProj t₀ = g₀
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    change HasDerivWithinAt (α.compProj)
      (ricciFlowVectorField R t (α.compProj t))
      (Icc tmin tmax) t
    rw [ODE.FunSpace.compProj_apply]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hpicard.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ ht' ↦ α.compProj_mem_closedBall hpicard.mul_max_le)
      g₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t ht
    apply hcone
    exact α.compProj_mem_closedBall hpicard.mul_max_le

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
  have heq : EqOn α β (Icc tmin tmax) :=
    ODE_solution_unique_of_mem_Icc_right
      (s := fun _ : ℝ ↦ RicciMetricCone) (K := K)
      (a := tmin) (b := tmax) hLip hαcont hαderiv
      (fun t ht ↦ hαstate t ⟨ht.1, le_of_lt ht.2⟩)
      hβcont hβderiv
      (fun t ht ↦ hβstate t ⟨ht.1, le_of_lt ht.2⟩) hinitial
  exact ⟨heq, hαstate, hβstate⟩

end PoincareCurvature.Palomar
