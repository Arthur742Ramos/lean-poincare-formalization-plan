module

public import LichnerowiczObata.GeodesicScaling
public import LichnerowiczObata.GeodesicRadial

/-! # Intrinsic radial derivatives of the geodesic normal map -/

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

/-- The normal endpoint map sends its radial initial-velocity direction
to the intrinsic radial gradient multiplied by radius. All geodesic and
radial identities are derived from the supplied solution family. -/
theorem coordinate_normal_endpoint_radial_gradient
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (u w : TM y), hessian LC f y u w = -K * f y * inner ℝ u w)
    (c : M) {α : (E × E) × ℝ → E × E} {V : Set (E × E)} (hV : IsOpen V) {δ : ℝ}
    (hα : ContDiffOn ℝ 1 α (V ×ˢ Metric.ball 0 δ))
    (hsol : ∀ q ∈ V, α (q, 0) = q ∧
      ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
        HasDerivAt (fun t => α (q, t)) (coordinateGeodesicSpray LC b c (α (q, s))) s)
    {z v : E} (hq : (z, v) ∈ V)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : f ((extChartAt I c).symm z) = a)
    {t : ℝ} (htime : t ∈ Metric.ball 0 δ)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c z v v) * t ∈ Ioo 0 Real.pi) :
    (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (α ((z, v), t)).1)
      (fderiv ℝ (fun w => (α ((z, w), t)).1) v v) =
      (t * Real.sqrt (coordinateMetricBilinear (I := I) c z v v)) •
        gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (α ((z, v), t)).1) := by
  have hδ : 0 < δ := lt_of_le_of_lt (dist_nonneg) htime
  have hinit := (hsol _ hq).1
  have hv := coordinate_geodesic_velocity_eq_radial (α := fun s => α ((z, v), s))
    b hf hK ha hH c Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected (Metric.mem_ball_self hδ)
    (fun s hs => ((hsol _ hq).2 s hs).1)
    (fun s hs => ((hsol _ hq).2 s hs).2)
    (by rw [hinit]; exact hcrit) (by rw [hinit]; exact hmax)
    htime (by rw [hinit]; exact hphase)
  rw [fderiv_coordinate_geodesic_endpoint_radial LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion b c hV hα hsol hq htime, map_smul, hv, smul_smul]
  simp only [hinit]

end LichnerowiczObata
