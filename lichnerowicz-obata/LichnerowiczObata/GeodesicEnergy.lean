module

public import LichnerowiczObata.GeodesicLinearization
public import LichnerowiczObata.MetricBilinearRegularity

/-! # Conservation of the actual metric energy of coordinate geodesics -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Metric compatibility and the actual geodesic equation imply vanishing
derivative of squared speed in the coordinate metric. -/
theorem hasDerivAt_coordinate_geodesic_energy
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : ℝ → E × E} {t : ℝ} (hz : (α t).1 ∈ (extChartAt I c).target)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (α s).1 (α s).2 (α s).2)
      0 t := by
  let x := (extChartAt I c).symm (α t).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x] using (extChartAt I c).map_target hz
  have hpos : (α t).1 = extChartAt I c x :=
    ((extChartAt I c).right_inv hz).symm
  have hp : HasDerivAt (fun s => (α s).1) (α t).2 t :=
    (hasFDerivAt_fst (p := α t)).comp_hasDerivAt t hα
  have hv : HasDerivAt (fun s => (α s).2)
      (-(frameConnectionCoefficients cov (trivializationAt E TM c) b x
        (α t).2 (α t).2)) t :=
    (hasFDerivAt_snd (p := α t)).comp_hasDerivAt t hα
  have he := hasDerivAt_coordinateMetric_pairing_connection cov hm b c x hx hpos hp hv hv
  simpa using he

/-- Squared speed is constant on a connected open domain of a coordinate
geodesic; no separate energy-conservation assumption is needed. -/
theorem coordinate_geodesic_energy_eq
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : ℝ → E × E} {T : Set ℝ} (hT : IsOpen T) (hconn : IsPreconnected T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    {s t : ℝ} (hs : s ∈ T) (ht : t ∈ T) :
    coordinateMetricBilinear (I := I) c (α s).1 (α s).2 (α s).2 =
      coordinateMetricBilinear (I := I) c (α t).1 (α t).2 (α t).2 := by
  have hd := fun s hs => hasDerivAt_coordinate_geodesic_energy cov hm b c (hz s hs) (hα s hs)
  exact hT.is_const_of_deriv_eq_zero hconn
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hs ht

end LichnerowiczObata
