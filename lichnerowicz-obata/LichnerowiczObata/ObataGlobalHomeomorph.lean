module

public import LichnerowiczObata.RoundComparisonExtension

/-! # A global round homeomorphism retaining the regular Obata metric -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
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

/-- The Obata equation supplies a global homeomorphism from the round
sphere, including both poles. The same map retains differentiable ambient
extensions in both regular directions and the regular forward metric.
Differentiability and metric preservation at the poles are not asserted. -/
theorem obata_global_round_homeomorph
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ p q : M,
      p ≠ q ∧ (∀ x, f x = a ↔ x = p) ∧ (∀ x, f x = -a ↔ x = q) ∧
      ∃ H : Metric.sphere (0 : RoundAmbient (TM p)) (1 / Real.sqrt K) ≃ₜ M,
        H (roundNorthPoint (one_div_pos.mpr (Real.sqrt_pos.mpr hK))) = p ∧
        H (roundSouthPoint (one_div_pos.mpr (Real.sqrt_pos.mpr hK))) = q ∧
        ∃ T : M → RoundAmbient (TM p),
          (∀ y : {x : M // -a < f x ∧ f x < a},
            T (y : M) = (H.symm (y : M) : RoundAmbient (TM p)) ∧
            MDifferentiableAt I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) ∧
            ∀ v w : TM (y : M),
              inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) v)
                (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) w) = inner ℝ v w) ∧
          ∃ G : RoundAmbient (TM p) → M,
            ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
              G (x.1 : RoundAmbient (TM p)) = H x.1 ∧
              MDifferentiableAt 𝓘(ℝ, RoundAmbient (TM p)) I G (x.1 : RoundAmbient (TM p)) := by
  obtain ⟨a, ha, hb, p, q, hpq, hmax, hmin, hdist, F, T, hT, hρ, G, hG⟩ :=
    obata_regular_metric_comparison hdim hK hf hnon hH
  have hU : {x : M | -a < f x ∧ f x < a} = {x : M | x ≠ p ∧ x ≠ q} := by
    ext x
    change (-a < f x ∧ f x < a) ↔ (x ≠ p ∧ x ≠ q)
    constructor
    · intro hx
      exact ⟨fun he => (ne_of_lt hx.2) ((hmax x).mpr he),
        fun he => (ne_of_lt hx.1) ((hmin x).mpr he).symm⟩
    · intro hx
      exact ⟨lt_of_le_of_ne (hb x).1 (fun he => hx.2 ((hmin x).mp he.symm)),
        lt_of_le_of_ne (hb x).2 (fun he => hx.1 ((hmax x).mp he))⟩
  obtain ⟨hN, hS⟩ := obata_comparison_inverse_pole_limits (I := I) hK f p q F hdist hρ
  let : FiniteDimensional ℝ (TM p) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨H, hHN, hHS, hHreg⟩ := exists_round_comparison_extension
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK)) p q hpq hU F G
    (fun x => (hG x).1) (fun x => (hG x).2.continuousAt) hN hS
  refine ⟨a, ha, hb, p, q, hpq, hmax, hmin, H, hHN, hHS, T, ?_, G, ?_⟩
  · intro y
    have hy : H.symm (y : M) = (F y).1 := by
      apply H.injective
      rw [H.apply_symm_apply, hHreg (F y)]
      exact (congrArg (fun z : {x : M // -a < f x ∧ f x < a} => (z : M))
        (F.symm_apply_apply y)).symm
    exact ⟨(hT y).1.trans (congrArg Subtype.val hy).symm, (hT y).2⟩
  · intro x
    exact ⟨(hG x).1.trans (hHreg x).symm, (hG x).2⟩

end LichnerowiczObata
