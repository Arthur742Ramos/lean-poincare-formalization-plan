import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianHeatResolventUniqueness

noncomputable section

open Set Filter MeasureTheory RicciFlow.AnalyticPDE
open scoped Topology

abbrev ExpectedActualHeatPositiveEigenvalueExclusion :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (u : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u) (Ici 0) 0 → u = 0

def actualHeatPositiveEigenvalueExclusionFullSignatureAssignment :
    ExpectedActualHeatPositiveEigenvalueExclusion :=
  @eq_zero_of_actualHeat_right_generator_positive_eigenvalue

abbrev ExpectedActualHeatRightGeneratorUniqueness :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f u v : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 →
      HasDerivWithinAt (heatFlowPathBcf v) (lam • v - f) (Ici 0) 0 → u = v

def actualHeatRightGeneratorUniquenessFullSignatureAssignment :
    ExpectedActualHeatRightGeneratorUniqueness := @actualHeat_right_generator_equation_unique

abbrev ExpectedActualHeatRightGeneratorInverseIdentification :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      ∀ (u : BoundedContinuousFunction (Fin n → ℝ) ℝ),
        HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 →
        u = actualGaussianHeatResolvent lam f

def actualHeatRightGeneratorInverseIdentificationFullSignatureAssignment :
    ExpectedActualHeatRightGeneratorInverseIdentification :=
  @eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation

abbrev ExpectedActualHeatRightGeneratorExistenceUniqueness :=
  ∀ {n : ℕ} {lam : ℝ}, 0 < lam →
    ∀ (f : BoundedContinuousFunction (Fin n → ℝ) ℝ),
      UniformContinuous (f : (Fin n → ℝ) → ℝ) →
      ∃! u : BoundedContinuousFunction (Fin n → ℝ) ℝ,
        HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0

def actualHeatRightGeneratorExistenceUniquenessFullSignatureAssignment :
    ExpectedActualHeatRightGeneratorExistenceUniqueness := @existsUnique_actualHeat_right_generator_equation

example {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (Fin 0 → ℝ) ℝ) :
    ∃! u : BoundedContinuousFunction (Fin 0 → ℝ) ℝ,
      HasDerivWithinAt (heatFlowPathBcf u) (lam • u - f) (Ici 0) 0 := by
  have hf : UniformContinuous (f : (Fin 0 → ℝ) → ℝ) := by
    apply Metric.uniformContinuous_iff.2
    intro ε hε
    refine ⟨1, one_pos, ?_⟩
    intro x y _
    have hxy : x = y := Subsingleton.elim x y
    subst y
    simpa only [dist_self] using hε
  exact existsUnique_actualHeat_right_generator_equation hlam f hf

example {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (u : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hu : HasDerivWithinAt (heatFlowPathBcf u) (lam • u - 0) (Ici 0) 0) : u = 0 := by
  exact eq_zero_of_actualHeat_right_generator_positive_eigenvalue hlam u
    (by simpa only [sub_zero] using hu)

set_option pp.universes false
set_option format.width 200
#check @eq_zero_of_actualHeat_right_generator_positive_eigenvalue
#check @actualHeat_right_generator_equation_unique
#check @eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation
#check @existsUnique_actualHeat_right_generator_equation

#print axioms RicciFlow.AnalyticPDE.eq_zero_of_actualHeat_right_generator_positive_eigenvalue
#print axioms RicciFlow.AnalyticPDE.actualHeat_right_generator_equation_unique
#print axioms RicciFlow.AnalyticPDE.eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation
#print axioms RicciFlow.AnalyticPDE.existsUnique_actualHeat_right_generator_equation
