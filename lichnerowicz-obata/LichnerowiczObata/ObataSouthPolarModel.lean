module

public import LichnerowiczObata.ObataReflection
public import LichnerowiczObata.ObataUnitSphericalProduct

/-! # A south-centered metric polar model from the reflected Obata function -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [CompactSpace M] [T2Space M] [Nonempty M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Reflection constructs a metric polar homeomorphism centered at the
minimum pole, with an isometric Cartesian derivative there. Its radial
coordinate is complementary to the original one. Identification with a
previously chosen north-centered global map is a separate requirement. -/
theorem exists_obata_south_polar_model
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hmin : ∀ x, f x = -a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ Φ : TM p × ℝ → M,
      HasRadialPoleModel I Φ p ∧
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = Real.pi / Real.sqrt K - r) ∧
        (∀ u : Metric.sphere (0 : TM p) 1,
          IsMIntegralCurveOn (fun r => Φ (u, r))
            (gradient (I := I) (obataRadial K a (fun y => -f y)))
            (Ioo 0 (Real.pi / Real.sqrt K))) ∧
        ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ (u, r) ∧
          ∀ w v : TM p, inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
            ∀ s t : ℝ,
              inner ℝ (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (w, s))
                (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (v, t)) =
                  (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hn : ∃ x y, -f x ≠ -f y := by
    obtain ⟨x, y, hxy⟩ := hnon
    exact ⟨x, y, fun he => hxy (neg_injective he)⟩
  have hmax : ∀ x, -f x = a ↔ x = (extChartAt I c).symm z := by
    intro x
    rw [← hmin x]
    constructor <;> intro hx <;> linarith
  have hpm : IsMaxOn (fun x => -f x) univ ((extChartAt I c).symm z) := by
    intro x _
    change -f x ≤ -f ((extChartAt I c).symm z)
    rw [(hmax _).mpr rfl]
    linarith [(hb x).1]
  have hcrit : gradient (I := I) (fun x => -f x) ((extChartAt I c).symm z) = 0 :=
    gradient_eq_zero_of_local_extremum
      ((hf2.neg _).mdifferentiableAt (by norm_num)) (Or.inr (hpm.isLocalMax (by simp)))
  obtain ⟨Φ, hmodel, Q, hQ, hρ, hcurves, hmetric⟩ := exists_obata_unit_spherical_product hf.neg hn
    hK ha (obata_hessian_equation_neg hf2 hH) c hz hcrit hmax
  have hU : {x : M | -a < -f x ∧ -f x < a} = {x : M | -a < f x ∧ f x < a} := by
    ext x
    change (-a < -f x ∧ -f x < a) ↔ (-a < f x ∧ f x < a)
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  refine ⟨Φ, hmodel, Q.trans (Homeomorph.setCongr hU), hQ, ?_, hcurves, hmetric⟩
  intro u r hr
  have hh := hρ u r hr
  rw [obataRadial_neg] at hh
  linarith

end LichnerowiczObata
