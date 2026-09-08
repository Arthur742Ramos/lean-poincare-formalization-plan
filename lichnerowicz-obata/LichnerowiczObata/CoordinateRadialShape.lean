module

public import LichnerowiczObata.RadialShapeOperator
public import LichnerowiczObata.MetricBilinearRegularity
public import AlmostSchur.DivergenceCoordinates
public import AlmostSchur.TorsionCoordinates

/-! # Radial shape identities in the actual tangent coordinates -/

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
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Torsion freeness converts the linearized vector field plus the flow-direction
connection term into the coordinate representation of the covariant derivative. -/
theorem fderiv_coordinateVectorField_add_connection
    (cov : CovariantDerivative I E TM) (ht : cov.torsion = 0)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (X : Π y : M, TM y) (c x : M) (hx : x ∈ (chartAt H c).source)
    (hX : MDiffAt (T% X) x) (u : E) :
    let e := trivializationAt E TM c
    fderiv ℝ (coordinateVectorField c X) (extChartAt I c x) u +
      frameConnectionCoefficients cov e b x (e.continuousLinearMapAt ℝ x (X x)) u =
      e.continuousLinearMapAt ℝ x (cov X x (e.symmL ℝ x u)) := by
  dsimp only
  rw [frameConnectionCoefficients_symm cov ht b c x hx]
  exact (add_comm _ _).trans (covariantDerivative_chart cov b X c x hx hX u).symm

/-- On angular coordinate vectors, the radial linearization plus its connection
term is exactly multiplication by the spherical shape factor. -/
theorem coordinate_obataRadial_shape {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    (hreg : -a < f x ∧ f x < a) (u : E)
    (hangular : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x u) = 0) :
    let N := gradient (I := I) (obataRadial K a f)
    let e := trivializationAt E TM c
    fderiv ℝ (coordinateVectorField c N) (extChartAt I c x) u +
      frameConnectionCoefficients LC e b x (e.continuousLinearMapAt ℝ x (N x)) u =
      (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) • u := by
  dsimp only
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hreg.2)
  have hN := mdifferentiableAt_gradient (contMDiffAt_obataRadial (K := K) (hf x) hm.ne' hp.ne)
  rw [fderiv_coordinateVectorField_add_connection LC leviCivitaConnection_torsion b
    _ c x hx hN, cov_obataRadial_gradient hK ha hf hb hH hreg]
  simp only [hangular, zero_smul, sub_zero, map_smul,
    (trivializationAt E TM c).continuousLinearMapAt_symmL hx]

/-- The actual metric obeys spherical scaling along a radial coordinate solution
and two angular solutions of its linearized equation. -/
theorem hasDerivAt_coordinate_radial_metric {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hreg : -a < f x ∧ f x < a)
    {z u w : ℝ → E} {t : ℝ} (hz : z t = extChartAt I c x)
    (hd : HasDerivAt z (coordinateVectorField c (gradient (I := I) (obataRadial K a f)) (z t)) t)
    (hu : HasDerivAt u
      (fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (u t)) t)
    (hw : HasDerivAt w
      (fderiv ℝ (coordinateVectorField c (gradient (I := I) (obataRadial K a f))) (z t) (w t)) t)
    (hTu : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (u t)) = 0)
    (hTw : inner ℝ (gradient (I := I) (obataRadial K a f) x)
      ((trivializationAt E TM c).symmL ℝ x (w t)) = 0) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (z s) (u s) (w s))
      (2 * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
          coordinateMetricBilinear (I := I) c (z t) (u t) (w t)) t := by
  have he : (extChartAt I c).symm (extChartAt I c x) = x :=
    (extChartAt I c).left_inv (by simpa using hx)
  have hd' : HasDerivAt z ((trivializationAt E TM c).continuousLinearMapAt ℝ x
      (gradient (I := I) (obataRadial K a f) x)) t := by
    have hd0 := hd
    rw [hz] at hd0
    simp only [coordinateVectorField] at hd0
    rw [he] at hd0
    exact hd0
  have hpair := hasDerivAt_coordinateMetric_pairing_connection LC
    leviCivitaConnection_metricCompatible b c x hx hz hd' hu hw
  have hsu := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (u t) hTu
  have hsw := coordinate_obataRadial_shape hK ha hf hb hH b c x hx hreg (w t) hTw
  dsimp only at hpair hsu hsw
  rw [hz] at hu hw hpair ⊢
  rw [hsu, hsw] at hpair
  convert hpair using 1
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end LichnerowiczObata
