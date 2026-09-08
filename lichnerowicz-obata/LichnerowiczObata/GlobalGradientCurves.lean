module

public import LichnerowiczObata.UniformManifoldODE
public import LichnerowiczObata.RadialCurves

/-! # Complete Obata gradient curves

The original gradient is globally regular, unlike the normalized radial
gradient at the extremal levels. Compactness proves its completeness.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Compactness gives complete curves of the actual gradient. -/
theorem exists_global_gradient_curve {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (gradient (I := I) f) := by
  let : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  exact exists_global_integralCurve_compact (contMDiff_gradient 1 hf) x

/-- The Obata equation gives complete gradient curves whose scalar values
satisfy the exact logistic differential equation for all real times. -/
theorem exists_global_obata_gradient_curves [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (gradient (I := I) f) ∧
      (∀ t, -a ≤ f (γ t) ∧ f (γ t) ≤ a) ∧
      (∀ t, HasDerivAt (f ∘ γ) (K * (a ^ 2 - f (γ t) ^ 2)) t) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, ?_⟩
  intro x
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_gradient_curve hf x
  refine ⟨γ, hγ0, hγ, fun t => hb (γ t), ?_⟩
  intro t
  have hd := hasDerivAt_comp_integralCurve
    ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hγ.isMIntegralCurveAt t)
  rw [← inner_gradient, real_inner_self_eq_norm_sq, hn] at hd
  exact hd

end LichnerowiczObata
