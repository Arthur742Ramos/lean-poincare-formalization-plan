module

public import LichnerowiczObata.SmoothGlobalFlow
public import LichnerowiczObata.RadialFlowFamily

/-! # Smooth gradient flows and their radial time change -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

/-- The logarithmic clock is smooth at every regular level. -/
theorem contDiffAt_obataClock (n : ℕ∞ω) {K a s : ℝ}
    (hs : -a < s ∧ s < a) : ContDiffAt ℝ n (obataClock K a) s := by
  have hp : a + s ≠ 0 := ne_of_gt (by linarith)
  have hm : a - s ≠ 0 := ne_of_gt (sub_pos.2 hs.2)
  exact (((contDiffAt_const.add contDiffAt_id).log hp).sub
    ((contDiffAt_const.sub contDiffAt_id).log hm)).div_const (2 * K * a)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- A smooth complete flow stays jointly smooth after the explicit radial
time change, away from the two extremal levels. -/
theorem contMDiffOn_obataRadialFamily
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {G : M → ℝ → M}
    (hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => G z.1 z.2)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (obataRadialFamily K a f G)
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) := by
  intro z hz
  have hc : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataClock K a (f w.1)) z :=
    (contDiffAt_obataClock ∞ hz.1).contMDiffAt.comp z ((hf.comp contMDiff_fst) z)
  have hcos : ContDiff ℝ ∞ (fun t : ℝ => a * Real.cos (Real.sqrt K * t)) := by fun_prop
  have ht : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataClock K a (a * Real.cos (Real.sqrt K * w.2))) z :=
    (contDiffAt_obataClock ∞ (obata_cos_level_mem hK ha hz.2)).contMDiffAt.comp z
      ((hcos.contMDiff.comp contMDiff_snd) z)
  have htime : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataRadialTime K a (f w.1) w.2) z := ht.sub hc
  exact ((hG _).comp z (contMDiffAt_fst.prodMk htime)).contMDiffWithinAt

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M]

/-- The actual intrinsic gradient of a smooth function has a jointly smooth
complete flow on a compact smooth Riemannian manifold. -/
theorem exists_smooth_global_gradient_flow {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∃ G : M → ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => G z.1 z.2) ∧
      (∀ x, G x 0 = x) ∧ ∀ x, IsMIntegralCurve (G x) (gradient (I := I) f) := by
  exact exists_smooth_global_manifold_flow (contMDiff_gradient_infty hf)

end LichnerowiczObata
