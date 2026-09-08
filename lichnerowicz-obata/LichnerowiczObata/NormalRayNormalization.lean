module

public import LichnerowiczObata.NormalRayMetric
public import LichnerowiczObata.SineMetricLimit

/-! # Pole-normalized angular metric of the geodesic normal map -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- The center derivative fixes the angular metric constant of the actual
geodesic normal map. No limiting angular metric is assumed. -/
theorem geodesic_normal_ray_metric_pole_normalized
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V)
    (hzV : (z, (0 : E)) ∈ V) {δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiffOn ℝ 2 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ r ∈ Metric.ball 0 δ, (α (q, r)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, r))) r)
    (hrest : ∀ r ∈ Metric.ball 0 δ, α ((z, 0), r) = (z, 0))
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ) (htpos : 0 < t) {u : E}
    (hu : 0 < coordinateMetricBilinear (I := I) c z u u)
    {ε : ℝ} (hε : 0 < ε)
    (hdata : ∀ r ∈ Ioo 0 ε, (z, r • u) ∈ V ∧
      Real.sqrt (K * coordinateMetricBilinear (I := I) c z (r • u) (r • u)) * t ∈ Ioo 0 Real.pi)
    {w v : E} (hw : coordinateMetricBilinear (I := I) c z u w = 0)
    (hv : coordinateMetricBilinear (I := I) c z u v = 0)
    {s : ℝ} (hs : s ∈ Ioo 0 ε) :
    let φ := fun q : E × ℝ => (α ((z, q.2 • q.1), t)).1
    let freq := Real.sqrt K * (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u))
    coordinateMetricBilinear (I := I) c (φ (u, s))
      (fderiv ℝ φ (u, s) (w, 0)) (fderiv ℝ φ (u, s) (v, 0)) /
        Real.sin (freq * s) ^ 2 =
      coordinateMetricBilinear (I := I) c z w v /
        (K * coordinateMetricBilinear (I := I) c z u u) := by
  let F := fun y : E => (α ((z, y), t)).1
  let φ := fun q : E × ℝ => F (q.2 • q.1)
  let g := coordinateMetricBilinear (I := I) c z
  let freq := Real.sqrt K * (t * Real.sqrt (g u u))
  let G := fun r : ℝ => coordinateMetricBilinear (I := I) c (F (r • u))
    (fderiv ℝ F (r • u) w) (fderiv ℝ F (r • u) v)
  let Q := fun r => coordinateMetricBilinear (I := I) c (φ (u, r))
    (fderiv ℝ φ (u, r) (w, 0)) (fderiv ℝ φ (u, r) (v, 0))
  have hfreq : freq ≠ 0 :=
    (mul_pos (Real.sqrt_pos.mpr hK) (mul_pos htpos (Real.sqrt_pos.mpr hu))).ne'
  have hlim := tendsto_geodesic_endpoint_metric_at_zero LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion b c hz hV hzV hδ hα
    (fun q hq => ⟨(hsol q hq).1, fun r hr => ((hsol q hq).2 r hr).2⟩) hrest htime w v
  have hline : Filter.Tendsto (fun r : ℝ => r • u) (𝓝[>] 0) (𝓝 (0 : E)) := by
    have hc : ContinuousAt (fun r : ℝ => r • u) 0 := by fun_prop
    simpa only [zero_smul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hG : Filter.Tendsto G (𝓝[>] 0) (𝓝 (t ^ 2 * g w v)) := hlim.comp hline
  have hQ (r : ℝ) (hr : r ∈ Ioo 0 ε) : Q r = r ^ 2 * G r := by
    have hi : ContDiffAt ℝ 2 (fun y : E => ((z, y), t)) (r • u) :=
      (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
    have hF : DifferentiableAt ℝ F (r • u) :=
      (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
        ⟨(hdata r hr).1, htime⟩)).comp (r • u) hi).fst).differentiableAt (by norm_num)
    exact normal_ray_spatial_metric (coordinateMetricBilinear (I := I) c) hF w v
  have he : Q s / Real.sin (freq * s) ^ 2 = (t ^ 2 * g w v) / freq ^ 2 := by
    apply sine_normalized_eq_of_pole_limit hG hfreq hε
    intro r hr
    rw [← hQ r hr]
    exact geodesic_normal_ray_metric_sine_squared_normalized_eq b hf hK ha hb hH c
      hV hα hsol hcrit hmax htime isOpen_Ioo (convex_Ioo 0 ε).isPreconnected
      (fun r hr => ⟨hr.1, hdata r hr⟩) hw hv hr hs
  change Q s / Real.sin (freq * s) ^ 2 = g w v / (K * g u u)
  rw [he]
  have hfreqsq : freq ^ 2 = K * (t ^ 2 * g u u) := by
    dsimp only [freq]
    rw [mul_pow, mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hu.le]
  rw [hfreqsq]
  field_simp [htpos.ne', hK.ne', hu.ne']

end LichnerowiczObata
