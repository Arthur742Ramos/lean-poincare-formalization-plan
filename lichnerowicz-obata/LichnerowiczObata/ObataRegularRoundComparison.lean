module

public import LichnerowiczObata.ObataUnitSphericalProduct
public import LichnerowiczObata.RoundAmbientDirections

/-! # The regular Obata-to-round comparison and its polar pullback metric -/

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
  [CompactSpace M] [T2Space M] [Nonempty M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A single regular comparison homeomorphism intertwines the constructed
Obata coordinates and the explicit round coordinates. Their pullback metrics
agree on every angular tangent and radial direction. Smoothness of the
comparison itself and extension over the poles are separate remaining steps. -/
theorem exists_obata_regular_round_comparison
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    let Ψ := fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
      roundNorth (roundAngularInclusion q.1) q.2
    ∃ Φ : TM p × ℝ → M,
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
            RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
          (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
          (∀ q, ((F (Q q)).1 : RoundAmbient (TM p)) = Ψ (q.1, q.2)) ∧
          ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ (u, r) ∧
            ∀ w v : TM p, inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
              ∀ s t : ℝ,
                inner ℝ (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (w, s))
                  (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (v, t)) =
                inner ℝ (fderiv ℝ Ψ (u, r) (w, s)) (fderiv ℝ Ψ (u, r) (v, t)) := by
  obtain ⟨Φ, Q, hQ, hmetric⟩ :=
    exists_obata_unit_spherical_product hf hnon hK ha hH c hz hcrit hmax
  let F := Q.symm.trans (curvatureRoundPolarHomeomorph hK)
  refine ⟨Φ, Q, F, hQ, ?_, ?_⟩
  · intro q
    change (((curvatureRoundPolarHomeomorph hK) (Q.symm (Q q))).1 :
      RoundAmbient (TM ((extChartAt I c).symm z))) = _
    rw [Q.symm_apply_apply]
    exact curvatureRoundPolarHomeomorph_apply hK q
  intro u r hr
  refine ⟨(hmetric u r hr).1, ?_⟩
  intro w v hw hv s t
  rw [(hmetric u r hr).2 w v hw hv s t]
  exact (intrinsicRoundPolar_metric hK (u : TM ((extChartAt I c).symm z)) w v
    (mem_sphere_zero_iff_norm.mp u.property) hw hv r s t).symm

end LichnerowiczObata
