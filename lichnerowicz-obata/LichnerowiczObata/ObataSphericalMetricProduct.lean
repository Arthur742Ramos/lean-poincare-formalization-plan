module

public import LichnerowiczObata.GlobalNormalAngularMetric
public import LichnerowiczObata.IntrinsicChartLift
public import LichnerowiczObata.IntrinsicAngularCoordinates

/-! # One spherical product carrying the constructed angular metric -/

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

/-- The global homeomorphism and intrinsic angular metric on its whole
parameter sphere use the same constructed chart and radial family. Starting
point regularity is derived. Unit speed and endpoint limits are retained
for the remaining full-metric and pole-extension arguments. -/
theorem exists_obata_spherical_metric_product
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ η : M × ℝ → M,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ η
        ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) ∧
      (∀ x, -a < f x ∧ f x < a →
        IsMIntegralCurveOn (fun r => η (x, r)) (gradient (I := I) (obataRadial K a f))
          (Ioo 0 (Real.pi / Real.sqrt K)) ∧
        (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), obataRadial K a f (η (x, r)) = r ∧
          ‖mfderiv 𝓘(ℝ, ℝ) I (fun s => η (x, s)) r 1‖ = 1) ∧
        ∃ p q : M,
          Filter.Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
          Filter.Tendsto (fun r => η (x, r))
            (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
          f p = a ∧ f q = -a) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ e : OpenPartialHomeomorph E E,
        0 ∈ e.source ∧ e 0 = z ∧
        (∀ u ∈ e.source, ContDiffAt ℝ 2 e u) ∧
        (∀ u ∈ e.source, e u ∈ (extChartAt I c).target) ∧
        (∀ u ∈ e.source, obataRadial K a f ((extChartAt I c).symm (e u)) =
          t * ‖(trivializationAt E TM c).symmL ℝ p u‖) ∧
        ∃ R : ℝ, 0 < R ∧ t * R ∈ Ioo 0 (Real.pi / Real.sqrt K) ∧
          (∀ v : Metric.sphere (0 : TM p) R,
            (trivializationAt E TM c).continuousLinearMapAt ℝ p v ∈ e.source) ∧
          (∀ v : Metric.sphere (0 : TM p) R,
            let x := (extChartAt I c).symm
              (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p v));
            -a < f x ∧ f x < a) ∧
          ∃ Q : Metric.sphere (0 : TM p) R × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
              {x : M // -a < f x ∧ f x < a},
            (∀ q, (Q q : M) = η ((extChartAt I c).symm
              (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p q.1)), q.2)) ∧
            ∀ u : Metric.sphere (0 : TM p) R, ∀ w v : TM p,
              inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
                ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
                  let Γ := fun y => η ((extChartAt I c).symm
                    (e ((trivializationAt E TM c).continuousLinearMapAt ℝ p y)), r)
                  inner ℝ (mfderiv 𝓘(ℝ, TM p) I Γ u w) (mfderiv 𝓘(ℝ, TM p) I Γ u v) =
                    (Real.sin (Real.sqrt K * r) ^ 2 / K) * (inner ℝ w v / R ^ 2) := by
  obtain ⟨hb, η, hη, hcurves, t, ht, e, he0, hez, hsmooth, htarget, hrad, hmetric⟩ :=
    exists_obata_global_angular_metric hf hnon hK ha hH c hz hcrit ((hmax _).mpr rfl)
  have hcρ : Continuous (obataRadial K a f) := by
    have hfc := hf.continuous
    unfold obataRadial
    fun_prop
  have hn : ∀ x, 0 ≤ obataRadial K a f x :=
    fun x => div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)
  have hzero : ∀ x, obataRadial K a f x = 0 ↔ x = (extChartAt I c).symm z := by
    intro x
    constructor
    · intro hx
      have he := (div_eq_zero_iff.mp hx).resolve_right (Real.sqrt_pos.mpr hK).ne'
      have hle := (le_div_iff₀ ha).mp (Real.arccos_eq_zero.mp he)
      exact (hmax x).mp (le_antisymm (hb x).2 (by simpa using hle))
    · intro hx
      simp [obataRadial, (hmax x).mpr hx, ha.ne']
  have hU : ∀ x, x ∈ {x : M | -a < f x ∧ f x < a} ↔
      obataRadial K a f x ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    intro x
    constructor
    · intro hx
      have hlo : -1 < f x / a := (lt_div_iff₀ ha).mpr (by nlinarith [hx.1])
      have hhi : f x / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hx.2)
      exact ⟨div_pos (Real.arccos_pos.mpr hhi) (Real.sqrt_pos.mpr hK),
        (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr hK)).mpr (Real.arccos_lt_pi.mpr hlo)⟩
    · intro hx
      have he := obataRadial_cos hK ha x (hb x)
      change -a < f x ∧ f x < a
      rw [← he]
      exact obata_cos_level_mem hK ha hx
  obtain ⟨R, hR, htR, hsource, Q, hQ⟩ := exists_coordinate_normal_radial_product_map c hz e
    he0 hez htarget hcρ hn hzero ht (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)) hrad
    {x : M | -a < f x ∧ f x < a} hU η hη.continuousOn
    (fun x hx r hr => ((hcurves x hx).2.2.2.1 r hr).1)
    (fun x hx => (hcurves x hx).1)
    (fun x hx r hr s _ => (hcurves x hx).2.1 r hr s)
  let p := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
  have hp : p ∈ (chartAt H c).source := by simpa [p] using (extChartAt I c).map_target hz
  have hcancel (v : TM p) : (trivializationAt E TM c).symmL ℝ p (L v) = v :=
    (trivializationAt E TM c).symmL_continuousLinearMapAt hp v
  have hnorm (u : Metric.sphere (0 : TM p) R) : ‖(u : TM p)‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.2
  have hradius (u : Metric.sphere (0 : TM p) R) :
      obataRadial K a f ((extChartAt I c).symm (e (L u))) = t * R := by
    rw [hrad _ (hsource u)]
    change t * ‖(trivializationAt E TM c).symmL ℝ p (L u)‖ = t * R
    rw [hcancel, hnorm]
  have hregular (u : Metric.sphere (0 : TM p) R) :
      -a < f ((extChartAt I c).symm (e (L u))) ∧ f ((extChartAt I c).symm (e (L u))) < a := by
    apply (hU _).mpr
    rw [hradius]
    exact htR
  have hnonzero (u : Metric.sphere (0 : TM p) R) : L u ≠ 0 := by
    intro he
    have hh := hcancel u
    rw [he, map_zero] at hh
    have hn := hnorm u
    rw [← hh, norm_zero] at hn
    exact hR.ne' hn.symm
  refine ⟨η, hη, fun x hx => (hcurves x hx).2.2, t, ht, e, he0, hez, hsmooth, htarget, hrad,
    R, hR, htR, hsource, hregular, Q, hQ, ?_⟩
  intro u w v hw hv r hr
  have hone : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤)
  have he := normal_radial_composite_intrinsic_angular_metric hf.continuous (hη.of_le hone)
    c hz ((hsmooth _ (hsource u)).differentiableAt (by norm_num))
    (htarget _ (hsource u)) (hregular u) hr hw hv
    (fun j k hj hk => hmetric _ (hsource u) (hnonzero u) (hregular u) j k hj hk r hr)
  simpa only [hnorm u] using he

end LichnerowiczObata
