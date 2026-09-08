module

public import LichnerowiczObata.RoundPoleGraph
public import LichnerowiczObata.NormalChartRadialFlow
public import LichnerowiczObata.IntrinsicRoundInverse
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Nonsingular first-order round logarithmic coordinates at the north pole -/

@[expose] public noncomputable section
open Set Filter Asymptotics
open scoped Topology Manifold ContDiff
namespace LichnerowiczObata

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The radial logarithm of the north hemisphere, expressed in its
equatorial Cartesian projection. The divided slope fills the value at zero. -/
def roundPoleLog (R : ℝ) (z : P) : P :=
  dslope Real.arcsin 0 (‖z‖ / R) • z

@[simp] theorem roundPoleLog_zero (R : ℝ) : roundPoleLog (P := P) R 0 = 0 := by
  simp [roundPoleLog]

/-- Although the norm alone is not differentiable at zero, its scalar
coefficient tends to one, and the radial logarithm has identity derivative. -/
theorem hasFDerivAt_roundPoleLog_zero (R : ℝ) :
    HasFDerivAt (roundPoleLog (P := P) R) (ContinuousLinearMap.id ℝ P) 0 := by
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have hc : ContinuousAt (fun z : P => dslope Real.arcsin 0 (‖z‖ / R)) 0 := by
    have hh := (continuousAt_dslope_same.mpr hd.differentiableAt)
    have hn : ContinuousAt (fun z : P => ‖z‖ / R) 0 := by fun_prop
    have hh' : ContinuousAt (dslope Real.arcsin 0) (‖(0 : P)‖ / R) := by
      simpa only [norm_zero, zero_div] using hh
    exact ContinuousAt.comp (f := fun z : P => ‖z‖ / R) (g := dslope Real.arcsin 0) hh' hn
  have hv : dslope Real.arcsin 0 (‖(0 : P)‖ / R) = 1 := by
    simp [dslope_same, hd.deriv]
  have ho : (fun z : P => dslope Real.arcsin 0 (‖z‖ / R) - 1) =o[𝓝 0]
      (fun _ : P => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    have hh : ContinuousAt (fun z : P => dslope Real.arcsin 0 (‖z‖ / R) - 1) 0 :=
      hc.sub continuousAt_const
    simpa only [hv, sub_self] using hh.tendsto
  have hh := ho.smul_isBigO (isBigO_refl (fun z : P => z) (𝓝 0))
  rw [hasFDerivAt_iff_isLittleO]
  simpa [roundPoleLog, sub_smul] using hh

/-- The logarithm recovers the geodesic radial vector on the open north
hemisphere; this is an identity of the actual polar curve, not a limit. -/
theorem roundPoleLog_polar_projection {R : ℝ} (hR : 0 < R)
    (u : P) (hu : ‖u‖ = 1) {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi * R / 2)) :
    roundPoleLog R ((WithLp.fstL 2 ℝ P ℝ)
      (roundPolarCurve R roundNorth (roundAngularInclusion u) r)) = r • u := by
  have hrR : 0 < r / R := div_pos hr.1 hR
  have hrhalf : r / R < Real.pi / 2 := (div_lt_iff₀ hR).mpr (by nlinarith [hr.2])
  have hs : 0 < Real.sin (r / R) := Real.sin_pos_of_pos_of_lt_pi hrR
    (lt_trans hrhalf (by linarith [Real.pi_pos]))
  have hproj : (WithLp.fstL 2 ℝ P ℝ)
      (roundPolarCurve R roundNorth (roundAngularInclusion u) r) =
      (R * Real.sin (r / R)) • u := by
    simp [roundPolarCurve, roundNorth, roundAngularInclusion_apply, smul_smul]
  rw [hproj, roundPoleLog]
  have hn : ‖(R * Real.sin (r / R)) • u‖ / R = Real.sin (r / R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hR hs), hu, mul_one]
    field_simp
  rw [hn, dslope_of_ne _ hs.ne', slope, Real.arcsin_zero, vsub_eq_sub, sub_zero, sub_zero,
    smul_eq_mul, Real.arcsin_sin (by linarith [Real.pi_pos]) hrhalf.le, smul_smul]
  congr 1
  field_simp

/-- A Cartesian pole model gives a differentiable ambient extension of
the inverse comparison at the north pole, agreeing with every sufficiently
short actual round polar ray. No south-pole regularity is assumed. -/
theorem HasRadialPoleModel.exists_round_north_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : P × ℝ → M} {p : M} (hmodel : HasRadialPoleModel I Φ p)
    {R : ℝ} (hR : 0 < R) :
    ∃ G : RoundAmbient P → M,
      G (R • roundNorth) = p ∧
      MDifferentiableAt 𝓘(ℝ, RoundAmbient P) I G (R • roundNorth) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 δ,
        G (roundPolarCurve R roundNorth (roundAngularInclusion u) r) = Φ (u, r) := by
  obtain ⟨χ, hχ0, hχ, δ, hδ, hpolar⟩ := hmodel
  let A := WithLp.fstL 2 ℝ P ℝ
  let G := χ ∘ roundPoleLog R ∘ A
  have hA : A (R • roundNorth) = 0 := by simp [A, roundNorth]
  refine ⟨G, ?_, ?_, min δ (Real.pi * R / 2),
    lt_min hδ (div_pos (mul_pos Real.pi_pos hR) (by norm_num)), ?_⟩
  · change χ (roundPoleLog R (A (R • roundNorth))) = p
    rw [hA, roundPoleLog_zero, hχ0]
  · have hlog : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, P) (roundPoleLog R)
        (A (R • roundNorth)) := by
      rw [hA]
      exact mdifferentiableAt_iff_differentiableAt.mpr
        (hasFDerivAt_roundPoleLog_zero R).differentiableAt
    have hc : MDifferentiableAt 𝓘(ℝ, P) I χ (roundPoleLog R (A (R • roundNorth))) := by
      rw [hA, roundPoleLog_zero]
      exact hχ.mdifferentiableAt (by norm_num)
    exact hc.comp (f := roundPoleLog R ∘ A) (R • roundNorth)
      (hlog.comp _ (mdifferentiableAt_iff_differentiableAt.mpr A.differentiableAt))
  · intro u r hr
    change χ (roundPoleLog R (A (roundPolarCurve R roundNorth (roundAngularInclusion u) r))) = _
    rw [roundPoleLog_polar_projection hR (u : P) (mem_sphere_zero_iff_norm.mp u.2)
      ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩]
    exact (hpolar u r ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩).symm

/-- A north-pole extension attached to one specified regular comparison. -/
def HasRoundNorthInverseExtension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (K : ℝ) {U : Set M}
    (F : U ≃ₜ RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P))
    (p : M) : Prop :=
  ∃ N : RoundAmbient P → M,
    N ((1 / Real.sqrt K) • roundNorth) = p ∧
    MDifferentiableAt 𝓘(ℝ, RoundAmbient P) I N ((1 / Real.sqrt K) • roundNorth) ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P),
        (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)).2 < δ →
          N (x.1 : RoundAmbient P) = (F.symm x : M)

/-- The pole model belongs to the exact comparison obtained from its
polar homeomorphism, so it can be carried with that map's metric properties. -/
theorem HasRadialPoleModel.round_north_inverse_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {Φ : P × ℝ → M} {p : M} (hmodel : HasRadialPoleModel I Φ p)
    {K : ℝ} (hK : 0 < K) {U : Set M}
    (Q : Metric.sphere (0 : P) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ U)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2)) :
    HasRoundNorthInverseExtension I K (Q.symm.trans (curvatureRoundPolarHomeomorph hK)) p := by
  obtain ⟨N, hN0, hNd, δ, hδ, hN⟩ := hmodel.exists_round_north_extension
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK))
  refine ⟨N, hN0, hNd, δ, hδ, ?_⟩
  intro x hx
  let q := (curvatureRoundPolarHomeomorph hK).symm x
  have hpoint : (x.1 : RoundAmbient P) =
      roundPolarCurve (1 / Real.sqrt K) roundNorth (roundAngularInclusion (q.1 : P)) q.2 := by
    simpa only [q, Homeomorph.apply_symm_apply] using curvatureRoundPolarHomeomorph_apply hK q
  have hcoords := intrinsicRoundInverseCoordinates_eq_inverse hK x
  have hrδ : (q.2 : ℝ) < δ := by
    have hh : (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient P)).2 =
        (q.2 : ℝ) := congrArg Prod.snd hcoords
    rw [← hh]
    exact hx
  change N (x.1 : RoundAmbient P) = (Q q : M)
  rw [hpoint]
  exact (hN q.1 q.2 ⟨q.2.property.1, hrδ⟩).trans (hQ q).symm

end LichnerowiczObata
