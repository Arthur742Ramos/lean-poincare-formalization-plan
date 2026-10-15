import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianHeatResolvent

noncomputable section

open Set MeasureTheory Filter RicciFlow.AnalyticPDE
open scoped Topology

abbrev ExpectedActualGaussianResolventDefinition :=
  ∀ {n : ℕ}, ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ →
    BoundedContinuousFunction (Fin n → ℝ) ℝ

def actualGaussianResolventDefinitionFullSignatureAssignment :
    ExpectedActualGaussianResolventDefinition := @actualGaussianHeatResolvent

abbrev ExpectedActualGaussianResolventIntegrable :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      IntegrableOn (actualHeatResolventIntegrand lam f) (Ici (0 : ℝ))

def actualGaussianResolventIntegrableFullSignatureAssignment :
    ExpectedActualGaussianResolventIntegrable := @integrableOn_actualHeatResolventIntegrand

abbrev ExpectedActualGaussianResolventNorm :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      ‖actualGaussianHeatResolvent lam f‖ ≤ ‖f‖ / lam

def actualGaussianResolventNormFullSignatureAssignment :
    ExpectedActualGaussianResolventNorm := @norm_actualGaussianHeatResolvent_le

abbrev ExpectedActualGaussianResolventShift :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      ∀ {h : ℝ}, 0 ≤ h →
        heatFlowPathBcf (actualGaussianHeatResolvent lam f) h =
          Real.exp (lam * h) • (actualGaussianHeatResolvent lam f -
            ∫ t in (0 : ℝ)..h, actualHeatResolventIntegrand lam f t)

def actualGaussianResolventShiftFullSignatureAssignment :
    ExpectedActualGaussianResolventShift := @heatFlowPathBcf_actualGaussianHeatResolvent_shift

abbrev ExpectedActualGaussianResolventRightDerivative :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      HasDerivWithinAt (heatFlowPathBcf (actualGaussianHeatResolvent lam f))
        (lam • actualGaussianHeatResolvent lam f - f) (Ici 0) 0

def actualGaussianResolventRightDerivativeFullSignatureAssignment :
    ExpectedActualGaussianResolventRightDerivative := @hasDerivWithinAt_actualGaussianHeatResolvent_zero

abbrev ExpectedActualGaussianResolventUniformContinuous :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      UniformContinuous (actualGaussianHeatResolvent lam f : (Fin n → ℝ) → ℝ)

def actualGaussianResolventUniformContinuousFullSignatureAssignment :
    ExpectedActualGaussianResolventUniformContinuous := @uniformContinuous_actualGaussianHeatResolvent

abbrev ExpectedActualGaussianResolventRangeWitness :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      ∃ u : BoundedContinuousFunction (Fin n → ℝ) ℝ,
        u = actualGaussianHeatResolvent lam f ∧
        UniformContinuous (u : (Fin n → ℝ) → ℝ) ∧ ‖u‖ ≤ ‖f‖ / lam ∧
        HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0

def actualGaussianResolventRangeWitnessFullSignatureAssignment :
    ExpectedActualGaussianResolventRangeWitness := @exists_actualGaussianHeat_generator_range_witness

-- Empty dimension is included, and no selected coordinate or positive rank is required.
example {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (Fin 0 → ℝ) ℝ) :
    ∃ u : BoundedContinuousFunction (Fin 0 → ℝ) ℝ,
      u = actualGaussianHeatResolvent lam f ∧
      UniformContinuous (u : (Fin 0 → ℝ) → ℝ) ∧ ‖u‖ ≤ ‖f‖ / lam ∧
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 := by
  have hf : UniformContinuous (f : (Fin 0 → ℝ) → ℝ) := by
    apply Metric.uniformContinuous_iff.2
    intro ε hε
    refine ⟨1, one_pos, ?_⟩
    intro x y _
    have hxy : x = y := Subsingleton.elim x y
    subst y
    simpa only [dist_self] using hε
  exact exists_actualGaussianHeat_generator_range_witness hlam f hf

example {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) :
    heatFlowPathBcf (actualGaussianHeatResolvent lam f) 0 = actualGaussianHeatResolvent lam f := by
  simp only [heatFlowPathBcf, dif_neg (lt_irrefl (0 : ℝ))]

set_option pp.universes false
set_option format.width 200
#check @integrableOn_actualHeatResolventIntegrand
#check @norm_actualGaussianHeatResolvent_le
#check @heatFlowPathBcf_actualGaussianHeatResolvent_shift
#check @hasDerivWithinAt_actualGaussianHeatResolvent_zero
#check @uniformContinuous_actualGaussianHeatResolvent
#check @exists_actualGaussianHeat_generator_range_witness

#print axioms RicciFlow.AnalyticPDE.integrableOn_actualHeatResolventIntegrand
#print axioms RicciFlow.AnalyticPDE.norm_actualGaussianHeatResolvent_le
#print axioms RicciFlow.AnalyticPDE.heatFlowPathBcf_actualGaussianHeatResolvent_shift
#print axioms RicciFlow.AnalyticPDE.hasDerivWithinAt_actualGaussianHeatResolvent_zero
#print axioms RicciFlow.AnalyticPDE.uniformContinuous_actualGaussianHeatResolvent
#print axioms RicciFlow.AnalyticPDE.exists_actualGaussianHeat_generator_range_witness
