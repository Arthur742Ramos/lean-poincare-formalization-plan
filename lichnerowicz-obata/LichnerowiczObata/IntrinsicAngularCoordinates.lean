module

public import LichnerowiczObata.ObataSphericalMetricProduct

/-! # Angular metric in intrinsic tangent-space parameters -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

omit [I.Boundaryless] in
/-- The forward tangent trivialization identifies the coordinate metric
with the intrinsic inner product at the chart base point. -/
theorem coordinate_metric_trivialization_forward (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (u v : TM ((extChartAt I c).symm z)) :
    coordinateMetricBilinear (I := I) c z
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) u)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) v) =
        inner ℝ u v := by
  have hp : (extChartAt I c).symm z ∈ (chartAt H c).source := by
    simpa using (extChartAt I c).map_target hz
  have hc (w : TM ((extChartAt I c).symm z)) :
      (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
        ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) w) = w :=
    (trivializationAt E TM c).symmL_continuousLinearMapAt hp w
  change inner ℝ
    ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) u))
    ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z)
      ((trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z) v)) = _
  rw [hc, hc]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- A metric-compatible linear parameter change converts the coordinate
angular formula into an intrinsic one for the actual composite derivative. -/
theorem angular_metric_precompose_linear
    (L : P →L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ x y, g (L x) (L y) = inner ℝ x y)
    {ψ : E → M} {u w v : P} {B : ℝ}
    (hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ (L u))
    (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (hmetric : ∀ j k : E, g (L u) j = 0 → g (L u) k = 0 →
      inner ℝ (mfderiv 𝓘(ℝ, E) I ψ (L u) j) (mfderiv 𝓘(ℝ, E) I ψ (L u) k) =
        B * (g j k / g (L u) (L u))) :
    inner ℝ (mfderiv 𝓘(ℝ, P) I (ψ ∘ L) u w) (mfderiv 𝓘(ℝ, P) I (ψ ∘ L) u v) =
      B * (inner ℝ w v / ‖u‖ ^ 2) := by
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, E) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hwc := mfderiv_comp_apply u hψ hL w
  have hvc := mfderiv_comp_apply u hψ hL v
  rw [mfderiv_eq_fderiv, L.fderiv] at hwc hvc
  rw [hwc, hvc]
  convert hmetric (L w) (L v) ((hg u w).trans hw) ((hg u v).trans hv) using 1 <;>
    first | rfl | simp only [hg, real_inner_self_eq_norm_sq]

omit [IsManifold I ∞ M] [I.Boundaryless] in
/-- Passing from a positive-radius tangent sphere to unit directions cancels
the radius-squared factor in the angular metric of the actual map. -/
theorem angular_metric_rescale_unit {Φ : P → M} {u w v : P} {R B : ℝ}
    (hR : R ≠ 0) (hu : ‖u‖ = 1)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P) I Φ (R • u))
    (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (hmetric : ∀ j k : P, inner ℝ (R • u) j = 0 → inner ℝ (R • u) k = 0 →
      inner ℝ (mfderiv 𝓘(ℝ, P) I Φ (R • u) j) (mfderiv 𝓘(ℝ, P) I Φ (R • u) k) =
        B * (inner ℝ j k / ‖R • u‖ ^ 2)) :
    inner ℝ (mfderiv 𝓘(ℝ, P) I (fun y => Φ (R • y)) u w)
      (mfderiv 𝓘(ℝ, P) I (fun y => Φ (R • y)) u v) = B * inner ℝ w v := by
  let L : P →L[ℝ] P := R • ContinuousLinearMap.id ℝ P
  have hL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, P) L u :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hwc := mfderiv_comp_apply (f := (L : P → P)) u hΦ hL w
  have hvc := mfderiv_comp_apply (f := (L : P → P)) u hΦ hL v
  rw [mfderiv_eq_fderiv, L.fderiv] at hwc hvc
  change inner ℝ (mfderiv 𝓘(ℝ, P) I (Φ ∘ L) u w)
    (mfderiv 𝓘(ℝ, P) I (Φ ∘ L) u v) = _
  rw [hwc, hvc]
  have hw' : inner ℝ (R • u) (R • w) = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hw, mul_zero]
  have hv' : inner ℝ (R • u) (R • v) = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hv, mul_zero]
  have he := hmetric (R • w) (R • v) hw' hv'
  have hn : ‖R • u‖ ^ 2 = R ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hi : inner ℝ (R • w) (R • v) = R ^ 2 * inner ℝ w v := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hn, hi] at he
  have hc : R ^ 2 * inner ℝ w v / R ^ 2 = inner ℝ w v := by field_simp
  rw [hc] at he
  exact he

end LichnerowiczObata
