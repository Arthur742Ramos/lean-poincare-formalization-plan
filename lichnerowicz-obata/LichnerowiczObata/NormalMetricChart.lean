module

public import LichnerowiczObata.NormalRayNormalization
public import LichnerowiczObata.GeodesicNormalRadial

/-! # One invertible normal chart with its radial and metric identities -/

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

/-- A single constructed local homeomorphism has the radial identity and
the full pole-normalized pullback metric on its source. Thus the metric and
topological constructions refer to the same map, including its derivative. -/
theorem exists_obata_normal_metric_chart
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a) :
    ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
      0 ∈ e.source ∧ e 0 = z ∧
      HasFDerivAt e (t • ContinuousLinearMap.id ℝ E) 0 ∧ ContDiffAt ℝ 2 e.symm z ∧
      (∀ u ∈ e.source, ContDiffAt ℝ 2 e u) ∧
      (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
      (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
        t * ‖(trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm z) u‖) ∧
      (∀ u ∈ e.source,
        Real.sqrt (K * coordinateMetricBilinear (I := I) c z u u) * t ∈ Ioo 0 Real.pi →
        (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (e u))
          (fderiv ℝ e u u) =
          (t * Real.sqrt (coordinateMetricBilinear (I := I) c z u u)) •
            gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (e u))) ∧
      ∀ u ∈ e.source, u ≠ 0 → ∀ w v : E,
        let g := coordinateMetricBilinear (I := I) c z
        let angular := Real.sin (Real.sqrt K * (t * Real.sqrt (g u u))) ^ 2 / (K * g u u)
        coordinateMetricBilinear (I := I) c (e u)
          (fderiv ℝ e u w) (fderiv ℝ e u v) =
            angular * g w v + (t ^ 2 - angular) * (g u w * g u v / g u u) := by
  obtain ⟨V, hV, hzV, δ, hδ, α, hα, hsol, hrest⟩ :=
    exists_stationary_coordinate_geodesic_flow LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htime : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  have hinit : (fun q => α (q, 0)) =ᶠ[𝓝 (z, (0 : E))] id := by
    filter_upwards [hV.mem_nhds hzV] with q hq
    exact (hsol q hq).1
  obtain ⟨e, he, he0, hez, hinv⟩ := exists_geodesic_endpoint_local_inverse LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion b c hz
    (hV.prod Metric.isOpen_ball) hα (fun q hq => ((hsol _ hq.1).2 _ hq.2).2)
    hinit Metric.isOpen_ball (convex_ball (0 : ℝ) δ).isPreconnected
    (Metric.mem_ball_self hδ) (fun s hs => ⟨hzV, hs⟩) hrest htime ht.ne'
  obtain ⟨ε, hε, hmetric⟩ := exists_geodesic_normal_full_metric_ball b hf hK ha hb hH c hz
    hV hzV hδ hα hsol hrest hcrit hmax htime ht
  have hr := coordinate_normal_endpoint_radius_at_zero_eventually b hf hK ha hH c hV hsol
    hzV hcrit hmax htime ht.le
  obtain ⟨η, hη, hrad⟩ := Metric.eventually_nhds_iff.mp hr
  let S := Metric.ball (0 : E) (min ε η) ∩ {u | (z, u) ∈ V}
  have hS : IsOpen S := Metric.isOpen_ball.inter
    (hV.preimage (continuous_const.prodMk continuous_id))
  have hS0 : (0 : E) ∈ S := ⟨Metric.mem_ball_self (lt_min hε hη), hzV⟩
  let d := e.restrOpen S hS
  have hd : (d : E → E) = (fun u => (α ((z, u), t)).1) := he
  refine ⟨t, ht, d, ⟨he0, hS0⟩, hez, ?_, hinv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    exact hasFDerivAt_geodesic_endpoint_zero LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion b c hz (hV.prod Metric.isOpen_ball) hα
      (fun q hq => ((hsol _ hq.1).2 _ hq.2).2) hinit Metric.isOpen_ball
      (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
      (fun s hs => ⟨hzV, hs⟩) hrest htime
  · intro u hu
    rw [hd]
    have hi : ContDiffAt ℝ 2 (fun y : E => ((z, y), t)) u :=
      (contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const
    have hpt : ((z, u), t) ∈ V ×ˢ Metric.ball 0 δ := ⟨hu.2.2, htime⟩
    exact (((hα.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds
      hpt)).comp u hi).fst)
  · intro u hu
    rw [hd]
    exact ((hsol _ hu.2.2).2 t htime).1
  · intro u hu
    rw [hd]
    exact hrad (lt_of_lt_of_le hu.2.1 (min_le_right ε η))
  · intro u hu hphase
    rw [hd]
    exact coordinate_normal_endpoint_radial_gradient b hf hK ha hH c hV
      (hα.of_le (by norm_num)) hsol hu.2.2 hcrit hmax htime hphase
  · intro u hu hune w v
    rw [hd]
    apply hmetric u _ hune w v
    have hnorm : ‖u‖ < min ε η := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu.2.1
    exact lt_of_lt_of_le hnorm (min_le_left ε η)

end LichnerowiczObata
