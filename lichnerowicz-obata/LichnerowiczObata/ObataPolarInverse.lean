module

public import LichnerowiczObata.ObataRegularRoundComparison
public import LichnerowiczObata.PolarInverseDifferentiability

/-! # Differentiability of the constructed regular Obata coordinates -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur TopologicalSpace
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {n : ℕ} [hDimension : Fact (Module.finrank ℝ E = n + 1)]
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

local instance tangentFinrank (p : M) : Fact (Module.finrank ℝ (TM p) = n + 1) :=
  ⟨show Module.finrank ℝ E = n + 1 from Fact.out⟩

/-- The Obata Hessian equation yields a single regular polar chart whose
inverse is differentiable on the entire regular region. The coordinate
homeomorphism in the conclusion is the one used to construct the chart. -/
theorem exists_obata_differentiable_polar_inverse
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ Φ : TM p × ℝ → M,
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
      ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : TM p) 1 × ℝ) M,
        e.source = {q | q.2 ∈ Ioo 0 (Real.pi / Real.sqrt K)} ∧
        e.target = {x | -a < f x ∧ f x < a} ∧
        (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
        (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
        (∀ y : {x : M // -a < f x ∧ f x < a},
          e.symm (y : M) = ((Q.symm y).1, ((Q.symm y).2 : ℝ))) ∧
        ∀ y, -a < f y ∧ f y < a →
          MDifferentiableAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm y := by
  obtain ⟨Φ, Q, F, G, hG, hQ, hF, hjet⟩ :=
    exists_obata_regular_round_comparison hf hnon hK ha hH c hz hcrit hmax
  let p := (extChartAt I c).symm z
  let J : Opens ℝ := ⟨Ioo 0 (Real.pi / Real.sqrt K), isOpen_Ioo⟩
  let U : Opens M := ⟨{x | -a < f x ∧ f x < a},
    (isOpen_lt continuous_const hf.continuous).inter
      (isOpen_lt hf.continuous continuous_const)⟩
  have hDim : Module.finrank ℝ E = n + 1 := Fact.out
  let : Nontrivial (TM p) := Module.nontrivial_of_finrank_eq_succ (R := ℝ) hDim
  obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (E := TM p) |>.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  let r : J := ⟨(Real.pi / Real.sqrt K) / 2, by change 0 < _ ∧ _ < _; constructor <;> linarith⟩
  obtain ⟨e, hs, ht, he, hi, hd⟩ := exists_differentiable_polar_inverse_on_target
    (I := I) (n := n) J U Q (⟨u, hu⟩, r) Φ hQ hDim
    (fun u r hr => ⟨(hjet u r hr).1, (hjet u r hr).2.1⟩)
  exact ⟨Φ, Q, e, hs, ht, hQ, he, hi, hd⟩

include hDimension in
/-- The regular comparison to the punctured round sphere has an ambient
extension differentiable at every regular point. No assertion is made here
about this extension at the two critical levels. -/
theorem exists_obata_regular_forward_differentiable
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
        RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
      ∃ T : M → RoundAmbient (TM p),
        ∀ y : {x : M // -a < f x ∧ f x < a},
          T (y : M) = ((F y).1 : RoundAmbient (TM p)) ∧
          MDifferentiableAt I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) := by
  obtain ⟨Φ, Q, e, hs, ht, hQ, he, hi, hd⟩ :=
    exists_obata_differentiable_polar_inverse (n := n) hf hnon hK ha hH c hz hcrit hmax
  let p := (extChartAt I c).symm z
  let Ψ := fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
    roundNorth (roundAngularInclusion q.1) q.2
  let Ψₛ := fun q : Metric.sphere (0 : TM p) 1 × ℝ => Ψ (q.1, q.2)
  let F := Q.symm.trans (curvatureRoundPolarHomeomorph hK)
  let T := Ψₛ ∘ e.symm
  refine ⟨F, T, ?_⟩
  intro y
  refine ⟨?_, ?_⟩
  · change Ψₛ (e.symm (y : M)) = _
    rw [hi y]
    exact (curvatureRoundPolarHomeomorph_apply hK (Q.symm y)).symm
  · have hΨ : MDifferentiableAt 𝓘(ℝ, TM p × ℝ) 𝓘(ℝ, RoundAmbient (TM p))
        Ψ ((e.symm (y : M)).1, (e.symm (y : M)).2) := by
      apply mdifferentiableAt_iff_differentiableAt.mpr
      dsimp only [Ψ, roundPolarCurve]
      fun_prop
    have hΨₛ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, RoundAmbient (TM p))
        Ψₛ (e.symm (y : M)) :=
      mdifferentiableAt_sphere_polar_restriction _ _ hΨ
    exact hΨₛ.comp (y : M) (hd y y.property)

end LichnerowiczObata
