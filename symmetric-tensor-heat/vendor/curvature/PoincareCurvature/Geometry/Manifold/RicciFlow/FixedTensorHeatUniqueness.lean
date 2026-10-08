module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.TensorHeatNormMaximum

/-!
# Zero-data uniqueness for fixed-metric tensor heat flow

This specializes the scalar maximum principle to a constant Riemannian
metric. The norm and scalar Laplacian then use the same metric, so the
geometric Bochner inequality applies without an assumed differential bridge.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 3000000

open Bundle Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance fixedTensorTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance fixedTensorTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance fixedTensorTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance fixedTensorTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance fixedTensorThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance fixedTensorThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance fixedTensorThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance fixedTensorThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- A classical fixed-metric connection heat field with continuous zero
initial norm vanishes in the open parabolic cylinder. -/
theorem covariantTwoTensor_eq_zero_of_fixedMetric_connectionHeat
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
    ∀ (cov : CovariantDerivative I E TM)
      (h dh : ℝ → ∀ x : M, T₂ x) {t₀ T : ℝ},
      cov.IsMetricCompatibleTangent →
      ContinuousOn
        (fun p : ℝ × M =>
          covariantTwoTensorNormSq (h p.1) p.2)
        (Icc t₀ T ×ˢ (Set.univ : Set M)) →
      (∀ t ∈ Ioo t₀ T, ∀ x : M, ∀ u v : TM x,
        HasDerivAt (fun s => h s x u v) (dh t x u v) t) →
      (∀ t ∈ Ioo t₀ T, ∀ y : M,
        MDiffAt
          (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
            (E := T₂) z (h t z)) y) →
      (∀ t ∈ Ioo t₀ T, ∀ x : M,
        MDiffAt
          (fun y => TotalSpace.mk'
            (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
            (E := T₃) y
              (covariantTwoTensorCovariantDerivative cov (h t) y)) x) →
      (∀ t ∈ Ioo t₀ T, ∀ x : M,
        dh t x = connectionLaplacian cov (h t) x) →
      (∀ x : M, h t₀ x = 0) →
      ∀ t ∈ Ioo t₀ T, ∀ x : M, h t x = 0 := by
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  intro cov h dh t₀ T hmetric hcont htime hspatial hfirst hheat hinitial
  let g : TimeDependentRiemannianMetric (I := I) (M := M) := fun _ => g₀
  let covF : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) := fun _ => cov
  have hbochner : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      2 * covariantTwoTensorPair (h t)
        (fun y => connectionLaplacian cov (h t) y) x ≤
        g.scalarLaplacian covF
          (fun _ => covariantTwoTensorNormSq (h t)) t x := by
    intro t ht x
    change 2 * covariantTwoTensorPair (h t)
      (fun y => connectionLaplacian cov (h t) y) x ≤
        CovariantDerivative.scalarLaplacian cov
          (covariantTwoTensorNormSq (h t)) x
    exact two_mul_pair_le_scalarLaplacian_covariantTwoTensorNormSq
      cov hmetric (h t) (hspatial t ht) (hfirst t ht x)
  have hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      covariantTwoTensorNormTimePair h dh t x ≤
        g.scalarLaplacian covF
          (fun _ => covariantTwoTensorNormSq (h t)) t x +
          0 * covariantTwoTensorNormSq (h t) x := by
    intro t ht x
    rw [covariantTwoTensorNormTimePair_eq_two_mul_pair]
    have hdh : dh t = fun y => connectionLaplacian cov (h t) y := by
      funext y
      exact hheat t ht y
    rw [hdh]
    simpa using hbochner t ht x
  exact covariantTwoTensor_eq_zero_of_norm_subsolution_openInitial_potential
    g covF h dh 0 hcont htime hspatial (fun t ht => hmetric)
      hfirst hpde hinitial

end CovariantDerivative.TimeDependentRiemannianMetric
