module

public import LichnerowiczObata.GeodesicEnergy
public import LichnerowiczObata.SmoothODEUniqueness

/-! # Uniqueness and scaling of actual coordinate geodesics -/

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
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Geodesics with time-rescaled initial velocities agree with the
corresponding time-rescaled solution throughout a common connected domain. -/
theorem coordinate_geodesic_rescale_eqOn
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α β : ℝ → E × E} (r : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (β s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α (r * s))) (r * s))
    (hβ : ∀ s ∈ T, HasDerivAt β (coordinateGeodesicSpray cov b c (β s)) s)
    (hinit : β 0 = ((α 0).1, r • (α 0).2)) :
    EqOn β (fun s => ((α (r * s)).1, r • (α (r * s)).2)) T := by
  apply ode_eqOn_of_contDiffAt hT hconn ?_ hβ
    (fun s hs => hasDerivAt_coordinate_geodesic_rescale cov b c r (hα s hs)) hzero
    (by simpa using hinit)
  intro s hs
  exact (contDiffOn_coordinateGeodesicSpray 1 cov hm ht b c).contDiffAt
    (((isOpen_extChartAt_target c).prod isOpen_univ).mem_nhds ⟨hz s hs, mem_univ _⟩)

/-- A solution family obeys the geodesic scaling law wherever both its
original and scaled initial velocities and times lie in its solution domain. -/
theorem coordinate_geodesic_flow_scaling
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M)
    {α : (E × E) × ℝ → E × E} {z v : E} (r : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α ((z, r • v), s)).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt (fun t => α ((z, v), t))
      (coordinateGeodesicSpray cov b c (α ((z, v), r * s))) (r * s))
    (hβ : ∀ s ∈ T, HasDerivAt (fun t => α ((z, r • v), t))
      (coordinateGeodesicSpray cov b c (α ((z, r • v), s))) s)
    (hinit : α ((z, v), 0) = (z, v)) (hscaled : α ((z, r • v), 0) = (z, r • v))
    {t : ℝ} (htime : t ∈ T) :
    α ((z, r • v), t) = ((α ((z, v), r * t)).1, r • (α ((z, v), r * t)).2) := by
  exact coordinate_geodesic_rescale_eqOn cov hm ht b c r hT hconn hzero hz hα hβ
    (by rw [hinit, hscaled]) htime

end LichnerowiczObata
