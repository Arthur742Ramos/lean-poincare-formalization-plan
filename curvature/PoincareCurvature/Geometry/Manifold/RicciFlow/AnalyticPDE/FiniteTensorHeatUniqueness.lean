module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.FixedTensorHeatUniqueness
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteInterval

/-!
# Geometric uniqueness for finite-interval tensor heat fields

The finite-interval field's totalized carrier is arbitrary at the initial
time.  A closed-time extension is therefore stated explicitly, with its
continuity and zero initial value, rather than reading those properties from
the carrier.  The spatial Bochner inequality used below is proved from the
actual covariant derivatives in `TensorGramCovariantDerivative`.
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

local instance finiteTensorTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance

local instance finiteTensorTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance

local instance finiteTensorTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance

local instance finiteTensorTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

/-- A finite classical tensor heat field with a continuous zero-data
closed-time extension vanishes at every interior time.  Its required spatial
regularity comes directly from `slice_mem`. -/
theorem finiteClassicalTensorHeatField_eq_zero_of_closedExtension
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
    ∀ (cov : CovariantDerivative I E TM) {t₀ T : ℝ}
      (u : FiniteClassicalTensorHeatField (E := E) (I := I) (M := M) cov t₀ T)
      (h : ℝ → ∀ x : M, T₂ x),
      cov.IsMetricCompatibleTangent →
      ContinuousOn
        (fun p : ℝ × M => covariantTwoTensorNormSq (h p.1) p.2)
        (Icc t₀ T ×ˢ (Set.univ : Set M)) →
      (∀ t ∈ Ioc t₀ T, h t = u.toFun t) →
      (∀ x : M, h t₀ x = 0) →
      (∀ t (ht : t ∈ Ioo t₀ T) (x : M),
        u.tensorHeatOperator cov t ht x = 0) →
      ∀ t ∈ Ioo t₀ T, u.toFun t = 0 := by
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  intro cov t₀ T u h hmetric hcont hext hinitial hheat
  have hopen : ∀ t ∈ Ioo t₀ T, h t = u.toFun t := by
    intro t ht
    exact hext t ⟨ht.1, ht.2.le⟩
  have htime : ∀ t ∈ Ioo t₀ T, ∀ x : M, ∀ a b : TM x,
      HasDerivAt (fun s => h s x a b) (u.timeDerivative t x a b) t := by
    intro t ht x a b
    have hev : (fun s => u.toFun s x a b) =ᶠ[𝓝 t]
        (fun s => h s x a b) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [hopen s hs]
    exact (u.hasTimeDerivative t ht x a b).congr_of_eventuallyEq hev.symm
  have hspatial : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) y (h t y)) x := by
    intro t ht x
    rw [hopen t ht]
    exact (u.slice_mem t ⟨ht.1, ht.2.le⟩).1 x
  have hfirst : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk'
          (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
          (E := fun z : M => TM z →L[ℝ] T₂ z) y
            (covariantTwoTensorCovariantDerivative cov (h t) y)) x := by
    intro t ht x
    rw [hopen t ht]
    exact (u.slice_mem t ⟨ht.1, ht.2.le⟩).2 x
  have hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      u.timeDerivative t x = connectionLaplacian cov (h t) x := by
    intro t ht x
    have hz := hheat t ht x
    rw [FiniteClassicalTensorHeatField.tensorHeatOperator_apply] at hz
    exact sub_eq_zero.mp (hopen t ht ▸ hz)
  have hz := covariantTwoTensor_eq_zero_of_fixedMetric_connectionHeat
    g₀ cov h u.timeDerivative hmetric hcont htime hspatial hfirst hpde hinitial
  intro t ht
  rw [← hopen t ht]
  funext x
  exact hz t ht x

end CovariantDerivative.TimeDependentRiemannianMetric
