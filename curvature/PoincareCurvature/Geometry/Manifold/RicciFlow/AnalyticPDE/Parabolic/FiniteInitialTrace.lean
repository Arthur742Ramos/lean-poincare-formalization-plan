module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteSourceExtension

/-!
# Initial traces on finite parabolic cylinders

A parabolic `C^{0,α}` class on `(t₀,T] × X` has a canonical bounded-continuous
trace at the missing initial face.  This file packages that trace as a bounded
linear map and, by projection to the value component, defines the initial trace
of a genuine finite-cylinder `C^{2+α,1+α/2}` jet.

The trace is obtained from the endpoint completion constructed in
`FiniteSourceExtension`; no boundary value is chosen independently of the
positive-time function.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Set

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace ParabolicC0AlphaBanach

variable {X : Type*} [PseudoMetricSpace X]
variable {t₀ T α : ℝ}

/-- The canonical initial trace of finite-cylinder parabolic Hölder data. -/
def finiteInitialTrace (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    BoundedContinuousFunction X E :=
  finiteClosedTimeSlice hT hα q ⟨t₀, le_rfl, hT.le⟩

@[simp]
theorem finiteInitialTrace_zero (hT : t₀ < T) (hα : 0 < α) :
    finiteInitialTrace (X := X) (E := E) hT hα
      (0 : ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X t₀ T)) = 0 := by
  simp [finiteInitialTrace]

@[simp]
theorem finiteInitialTrace_add (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTrace hT hα (q + r) =
      finiteInitialTrace hT hα q + finiteInitialTrace hT hα r := by
  simp [finiteInitialTrace]

@[simp]
theorem finiteInitialTrace_smul (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTrace hT hα (c • q) = c • finiteInitialTrace hT hα q := by
  simp [finiteInitialTrace]

/-- Initial trace has operator bound one in the finite-cylinder Hölder norm. -/
theorem norm_finiteInitialTrace_le (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    ‖finiteInitialTrace hT hα q‖ ≤ ‖q‖ :=
  norm_finiteClosedTimeSlice_le hT hα q ⟨t₀, le_rfl, hT.le⟩

/-- Initial trace as a bounded linear map. -/
def finiteInitialTraceL (hT : t₀ < T) (hα : 0 < α) :
    ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      BoundedContinuousFunction X E :=
  LinearMap.mkContinuous
    { toFun := finiteInitialTrace hT hα
      map_add' := finiteInitialTrace_add hT hα
      map_smul' := finiteInitialTrace_smul hT hα }
    1 (by simpa using norm_finiteInitialTrace_le hT hα)

@[simp]
theorem finiteInitialTraceL_apply (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T)) :
    finiteInitialTraceL hT hα q = finiteInitialTrace hT hα q :=
  rfl

theorem norm_finiteInitialTraceL_le (hT : t₀ < T) (hα : 0 < α) :
    ‖finiteInitialTraceL (X := X) (E := E) hT hα‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The canonical completed slice path is characterized by continuity and
agreement with the datum at positive times. -/
theorem finiteClosedTimeSlice_eq_of_continuous
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction X E)
    (hg : Continuous g)
    (hpositive : ∀ t : positiveTimeInIcc t₀ T,
      g t = finiteTimeSlice hα q t) :
    finiteClosedTimeSlice hT hα q = g := by
  apply (dense_positiveTimeInIcc hT).denseRange_val.equalizer
    (continuous_finiteClosedTimeSlice hT hα q) hg
  funext t
  change finiteClosedTimeSlice hT hα q
    (t : ↥(Set.Icc t₀ T)) = g (t : ↥(Set.Icc t₀ T))
  rw [finiteClosedTimeSlice_apply_positive]
  exact (hpositive t).symm

/-- Endpoint form of the uniqueness characterization: any continuous closed
path agreeing with the positive-time slices has the canonical initial value. -/
theorem finiteInitialTrace_eq_of_continuous
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction X E)
    (hg : Continuous g)
    (hpositive : ∀ t : positiveTimeInIcc t₀ T,
      g t = finiteTimeSlice hα q t) :
    finiteInitialTrace hT hα q = g ⟨t₀, le_rfl, hT.le⟩ := by
  exact congrFun
    (finiteClosedTimeSlice_eq_of_continuous hT hα q g hg hpositive)
    ⟨t₀, le_rfl, hT.le⟩

/-- Quantitative convergence of every positive-time slice to the canonical
initial trace in the bounded-continuous spatial norm. -/
theorem dist_finiteTimeSlice_initial_le
    (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X t₀ T))
    (t : positiveTimeInIcc t₀ T) :
    dist (finiteTimeSlice hα q t) (finiteInitialTrace hT hα q) ≤
      ‖q‖ * |(t : ℝ) - t₀| ^ (α / 2) := by
  simpa [finiteInitialTrace, finiteClosedTimeSlice_apply_positive] using
    dist_finiteClosedTimeSlice_le hT hα q
      (t : ↥(Set.Icc t₀ T)) ⟨t₀, le_rfl, hT.le⟩

end ParabolicC0AlphaBanach

section HigherTrace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

/-- Initial trace of the value component of a genuine finite-cylinder
`C^{2+α,1+α/2}` jet. -/
def initialTraceL (hT : t₀ < T) (hα : 0 < α) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      BoundedContinuousFunction X E :=
  (ParabolicC0AlphaBanach.finiteInitialTraceL hT hα).comp valueComponentL

@[simp]
theorem initialTraceL_apply (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    initialTraceL hT hα u =
      ParabolicC0AlphaBanach.finiteInitialTrace hT hα (valueComponentL u) :=
  rfl

theorem norm_initialTraceL_le (hT : t₀ < T) (hα : 0 < α) :
    ‖initialTraceL (X := X) (E := E) hT hα‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro u
  calc
    ‖initialTraceL hT hα u‖ ≤ ‖valueComponentL u‖ :=
      ParabolicC0AlphaBanach.norm_finiteInitialTrace_le hT hα _
    _ ≤ ‖u‖ := by
      change ‖u.1.1‖ ≤ ‖u.1‖
      exact le_max_left _ _
    _ = 1 * ‖u‖ := by rw [one_mul]

/-- Genuine finite-cylinder higher functions with zero canonical initial
trace.  This is a closed subspace because it is the kernel of a bounded
linear map. -/
def zeroInitialSubmodule (hT : t₀ < T) (hα : 0 < α) :
    Submodule ℝ (FiniteParabolicC2AlphaBanach X E t₀ T α) :=
  (initialTraceL hT hα).ker

@[simp]
theorem mem_zeroInitialSubmodule_iff (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    u ∈ zeroInitialSubmodule hT hα ↔ initialTraceL hT hα u = 0 :=
  LinearMap.mem_ker

end FiniteParabolicC2AlphaBanach

end HigherTrace

end AnalyticPDE
end RicciFlow
