module

public import LichnerowiczObata.GeodesicHessian

/-! # The radial parameter along geodesics from the maximum pole -/

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

/-- Before the antipodal phase, the radial parameter along a geodesic
from the maximum pole is its initial metric speed times elapsed time. -/
theorem coordinate_geodesic_obataRadial_eq
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T) (htnonneg : 0 ≤ t)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ≤ Real.pi) :
    obataRadial K a f ((extChartAt I c).symm (α t).1) =
      Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2) * t := by
  have hcos := coordinate_geodesic_obata_eq_cos cov hm b hf hK.le hH c
    hT hconn hzero hz hα hcrit ht
  rw [hmax] at hcos
  rw [obataRadial, hcos, mul_div_cancel_left₀ _ ha.ne',
    Real.arccos_cos (mul_nonneg (Real.sqrt_nonneg _) htnonneg) hphase,
    Real.sqrt_mul hK.le]
  field_simp

/-- Positive geodesic phases strictly before the antipodal phase lie in
the regular region of the Obata function. -/
theorem coordinate_geodesic_obata_regular
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ∈ Ioo 0 Real.pi) :
    -a < f ((extChartAt I c).symm (α t).1) ∧
      f ((extChartAt I c).symm (α t).1) < a := by
  have hcos := coordinate_geodesic_obata_eq_cos cov hm b hf hK hH c
    hT hconn hzero hz hα hcrit ht
  rw [hmax] at hcos
  have hlo := Real.strictAntiOn_cos ⟨hphase.1.le, hphase.2.le⟩
    ⟨Real.pi_pos.le, le_rfl⟩ hphase.2
  have hhi := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
    ⟨hphase.1.le, hphase.2.le⟩ hphase.1
  simp only [Real.cos_pi, Real.cos_zero] at hlo hhi
  constructor <;> nlinarith [mul_pos ha (sub_pos.mpr hlo), mul_pos ha (sub_pos.mpr hhi)]

end LichnerowiczObata
