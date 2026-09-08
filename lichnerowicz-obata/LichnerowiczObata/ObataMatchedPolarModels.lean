module

public import LichnerowiczObata.ObataSouthPolarModel

/-! # Matched north and south polar models constructed from one Obata function -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

/-- The full unit-angular polar metric, including differentiability of
the ambient parameter map. This packages the existing metric identity. -/
def HasUnitPolarMetric {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (K : ℝ) (Φ : P × ℝ → M) : Prop :=
  ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
    MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ (u, r) ∧
    ∀ w v : P, inner ℝ (u : P) w = 0 → inner ℝ (u : P) v = 0 → ∀ s t : ℝ,
      inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (w, s))
        (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (v, t)) =
          (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t

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

/-- Both metric polar models, their isometric pole derivatives, and their
angular matching are constructed together from the Obata equation and the
two unique extrema. No matching homeomorphism is assumed. -/
theorem exists_obata_matched_polar_models
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c d : M) {z z' : E} (hz : z ∈ (extChartAt I c).target) (hz' : z' ∈ (extChartAt I d).target)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z)
    (hmin : ∀ x, f x = -a ↔ x = (extChartAt I d).symm z') :
    let p := (extChartAt I c).symm z
    let q := (extChartAt I d).symm z'
    ∃ Φ : TM p × ℝ → M, ∃ Ψ : TM q × ℝ → M,
      HasRadialPoleModel I Φ p ∧ HasRadialPoleModel I Ψ q ∧
      HasUnitPolarMetric I K Φ ∧ HasUnitPolarMetric I K Ψ ∧
      ∃ N : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
      ∃ S : Metric.sphere (0 : TM q) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        (∀ u, (N u : M) = Φ (u.1, u.2)) ∧
        (∀ u, (S u : M) = Ψ (u.1, u.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = r) ∧
        (∀ u : Metric.sphere (0 : TM q) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Ψ (u, r)) = Real.pi / Real.sqrt K - r) ∧
        ∃ A : Metric.sphere (0 : TM p) 1 ≃ₜ Metric.sphere (0 : TM q) 1,
          ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            Φ (u, Real.pi / Real.sqrt K - r) = Ψ (A u, r) := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpm : IsMaxOn f univ ((extChartAt I c).symm z) := by
    intro x _
    change f x ≤ f ((extChartAt I c).symm z)
    rw [(hmax _).mpr rfl]
    exact (hb x).2
  have hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0 :=
    gradient_eq_zero_of_local_extremum ((hf2 _).mdifferentiableAt (by norm_num))
      (Or.inr (hpm.isLocalMax (by simp)))
  obtain ⟨Φ, hpole, N, hN, hρN, hcN, hmN⟩ :=
    exists_obata_unit_spherical_product hf hnon hK ha hH c hz hcrit hmax
  obtain ⟨Ψ, hspole, S, hS, hρS, hcS, hmS⟩ :=
    exists_obata_south_polar_model hf hnon hK ha hb hH d hz' hmin
  obtain ⟨A, hA⟩ := obata_polar_coordinates_match hf2 hK ha N S
    (fun u : Metric.sphere (0 : TM ((extChartAt I c).symm z)) 1 × ℝ => Φ (u.1, u.2))
    (fun u : Metric.sphere (0 : TM ((extChartAt I d).symm z')) 1 × ℝ => Ψ (u.1, u.2))
    hN hS hρN hρS hcN hcS
  exact ⟨Φ, Ψ, hpole, hspole, hmN, hmS, N, S, hN, hS, hρN, hρS, A, hA⟩

end LichnerowiczObata
