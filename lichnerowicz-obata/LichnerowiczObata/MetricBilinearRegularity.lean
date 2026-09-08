module

public import LichnerowiczObata.CoordinateMetricVariation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness of the bilinear-valued coordinate metric -/

@[expose] public noncomputable section
open Set Bundle FiberBundle AlmostSchur
open scoped ContDiff Topology BigOperators Manifold

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- In finite dimension, smoothness of all basis pairings gives smoothness
of the whole continuous bilinear form, in its operator norm. -/
theorem contDiffOn_bilinear_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {g : P → E →L[ℝ] E →L[ℝ] ℝ} {S : Set P} {n : ℕ∞ω}
    (hg : ∀ i j, ContDiffOn ℝ n (fun z => g z (b i) (b j)) S) : ContDiffOn ℝ n g S := by
  let q : ι → E →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  let R : ι → ι → E →L[ℝ] E →L[ℝ] ℝ := fun i j => (q i).smulRight (q j)
  have he (z : P) : g z = ∑ i, ∑ j, g z (b i) (b j) • R i j := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp [R, q, Module.Basis.coord_apply, Finsupp.single_apply]
  have hs : ContDiffOn ℝ n (fun z => ∑ i, ∑ j, g z (b i) (b j) • R i j) S := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    let L : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingleton ℝ (R i j)
    have hL : ContDiff ℝ n L := by
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ)
        (F := E →L[ℝ] E →L[ℝ] ℝ) L
    exact hL.comp_contDiffOn (hg i j)
  exact hs.congr (fun z _ => he z)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The actual coordinate metric is C1 as an operator-norm-valued bilinear form. -/
theorem contDiffOn_coordinateMetricBilinear (c : M) :
    ContDiffOn ℝ 1 (coordinateMetricBilinear (I := I) c) (extChartAt I c).target := by
  let b := Module.finBasis ℝ E
  apply contDiffOn_bilinear_of_basis b
  intro i j
  have hm := contDiffOn_coordinateMetric (I := I) b c
  have hij := (contDiffOn_pi.mp (contDiffOn_pi.mp hm i)) j
  simpa only [coordinateMetric, tangentChartGram, tangentTrivializationGram,
    Matrix.gram_apply, coordinateMetricBilinear_apply] using hij

/-- At an interior chart point the bundled coordinate metric is differentiable. -/
theorem differentiableAt_coordinateMetricBilinear (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    DifferentiableAt ℝ (coordinateMetricBilinear (I := I) c) z := by
  exact ((contDiffOn_coordinateMetricBilinear (I := I) c).contDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by simp)

end LichnerowiczObata
