import PoincareCurvature.Analysis.MatrixInverseDerivative
import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
# Time variation of the inverse metric

This file connects the finite inverse-matrix derivative to the actual metric
tensor of a time-dependent Riemannian metric.  In a genuine tangent-bundle
local frame it proves

`\partial_t g^{-1} = -g^{-1} (\partial_t g) g^{-1}`,

and, for an intrinsic Ricci flow, the geometric specialization

`\partial_t g^{ij} = 2 Ric^{ij}`.

The inverse regularity and nonsingularity are derived from the metric
components and positive definiteness; neither is assumed independently.
-/

noncomputable section

open Bundle Matrix
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Metric components in a genuine tangent-bundle local frame. -/
def localFrameMetricMatrix
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => metricTensor (I := I) (M := M) g t x
    (e.localFrame bas i x) (e.localFrame bas j x)

/-- Components of a time-dependent covariant two-tensor in the same local frame. -/
def localFrameTensorMatrix
    (h : MetricTensorFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => h t x (e.localFrame bas i x) (e.localFrame bas j x)

/-- Intrinsic Ricci components in the same genuine local frame. -/
def localFrameIntrinsicRicciMatrix
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (t : ℝ) (x : M) : Matrix ι ι ℝ :=
  fun i j => intrinsicRicciTensor (I := I) (M := M) g t x
    (e.localFrame bas i x) (e.localFrame bas j x)

/-- Positive definiteness makes every local-frame metric matrix nonsingular. -/
theorem localFrameMetricMatrix_det_ne_zero
    (g : MetricFamily (I := I) (M := M))
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (t : ℝ) {x : M} (hx : x ∈ e.baseSet) :
    (localFrameMetricMatrix (I := I) (M := M) g e bas t x).det ≠ 0 := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hmatrix :
      localFrameMetricMatrix (I := I) (M := M) g e bas t x =
        CovariantDerivative.localFrameGramMatrix (I := I) e bas x := by
    ext i j
    rfl
  rw [hmatrix]
  exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
    (I := I) (E := E) e bas hx

/-- A tensorial time derivative differentiates every local-frame metric
component with the corresponding tensor component as velocity. -/
theorem HasTimeDerivativeAt.hasDerivAt_localFrameMetricMatrix
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι]
    (bas : Module.Basis ι ℝ E) (x : M) (i j : ι) :
    HasDerivAt
      (fun s => localFrameMetricMatrix (I := I) (M := M) g e bas s x i j)
      (localFrameTensorMatrix (I := I) (M := M) gdot e bas t x i j) t := by
  exact h x (e.localFrame bas i x) (e.localFrame bas j x)

/-- The inverse metric in a genuine local frame has the expected derivative.
This derives both inverse differentiability and invertibility from the evolving
Riemannian metric itself. -/
theorem HasTimeDerivativeAt.hasDerivAt_localFrameMetricMatrix_inv
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    HasDerivAt
      (fun s => (localFrameMetricMatrix (I := I) (M := M) g e bas s x)⁻¹ i j)
      ((-((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
          localFrameTensorMatrix (I := I) (M := M) gdot e bas t x *
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) : Matrix ι ι ℝ) i j) t := by
  apply PoincareCurvature.hasDerivAt_nonsing_inv_entry
  · intro k l
    exact h.hasDerivAt_localFrameMetricMatrix e bas x k l
  · intro s
    exact localFrameMetricMatrix_det_ne_zero g e bas s hx

section IntrinsicFlow

variable [SigmaCompactSpace M]

/-- Along an intrinsic Ricci flow, the inverse metric evolves by twice the
fully raised intrinsic Ricci tensor, expressed here in a genuine local frame. -/
theorem IsIntrinsicRicciFlowOn.hasDerivAt_localFrameMetricMatrix_inv
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {s : Set ℝ}
    (hflow : IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    HasDerivAt
      (fun τ => (localFrameMetricMatrix (I := I) (M := M) g e bas τ x)⁻¹ i j)
      ((2 : ℝ) *
        (((localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹ *
          localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x *
          (localFrameMetricMatrix (I := I) (M := M) g e bas t x)⁻¹) i j)) t := by
  have hbase := (hflow.1 ht).hasDerivAt_localFrameMetricMatrix_inv e bas hx i j
  convert hbase using 1
  have hvelocity :
      localFrameTensorMatrix (I := I) (M := M) gdot e bas t x =
        (-2 : ℝ) • localFrameIntrinsicRicciMatrix (I := I) (M := M) g e bas t x := by
    ext k l
    simpa [localFrameTensorMatrix, localFrameIntrinsicRicciMatrix,
      intrinsicRicciFlowRHS, ricciFlowRHS, intrinsicRicciTensor] using
      hflow.2 ht x (e.localFrame bas k x) (e.localFrame bas l x)
  rw [hvelocity]
  simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]

end IntrinsicFlow

end RicciFlow
