import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroup

/-!
# The heat semigroup restricted to the Hölder Banach space (Point 4 PDE milestone)

This file restricts the Euclidean heat semigroup to the Hölder Banach space
`HolderBCF α n` constructed in `HolderHeatSemigroup.lean`.

Proved here:
* `isHolderConst_heatSemigroupNDbcf` : heat convolution preserves every
  coordinatewise Hölder constant (the constant does not increase).
* `heatSemigroupHolderCLM` : the restriction as a continuous linear map
  `HolderBCF α n →L[ℝ] HolderBCF α n`, with
* `norm_heatSemigroupHolderCLM_le` : operator norm `≤ 1` (both the sup-norm
  and the Hölder seminorm are nonincreasing under heat flow).
* `heatPropagatorHolderCLM` : the propagator on `HolderBCF` (semigroup for
  `t > 0`, identity for `t ≤ 0`) — the candidate for `DuhamelData.S` — with
* `heatPropagatorHolderCLM_hSbound` : the exact `DuhamelData.hSbound`
  statement with `M = 1`.
* `tendsto_heatPropagatorHolderCLM_toBCF_nhdsWithin_zero` : strong continuity
  at heat-time `0` in the **sup-norm** component, for `0 < α`.

Precise analytic obstruction (documented, not proved): a full `DuhamelData`
instance on `HolderBCF α n` would require `DuhamelData.hSjoint`, i.e. joint
continuity of `(t, f) ↦ S t f` on `Icc 0 T ×ˢ univ` in the **full Hölder norm**.
This is *false* at the same Hölder exponent: strong continuity
`‖S t f - f‖_{C^α} → 0` as `t → 0⁺` fails in general (e.g. for a bounded
`α`-Hölder datum that looks like `|x|^α` near the origin, the Hölder
seminorm quotient `[S t f - f]_α` stays bounded away from zero because the
smoothed function is flat to second order at the origin while the datum
itself is only `α`-Hölder). The available estimate
(`norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder`) controls only the
sup-norm component. A full `DuhamelData` instantiation therefore needs a
smaller state space (little-Hölder, where the modulus of continuity vanishes
at small scales) or an exponent loss. We do not fake it here.

No `sorry`, no `admit`, no axioms.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {n : ℕ} {α : ℝ}

/-! ## 1. Hölder preservation under heat convolution -/

/-- Heat convolution preserves every coordinatewise Hölder constant: if `H`
is a Hölder constant for `f`, it is one for `heatSemigroupNDbcf ht f`.
The difference `(S t f)(a) - (S t f)(b)` is the kernel integral of
`f(a - z) - f(b - z)`, and `(a - z) - (b - z) = a - b`, so the Hölder bound
passes under the integral against the probability kernel. -/
theorem isHolderConst_heatSemigroupNDbcf {t : ℝ} (ht : 0 < t)
    {f : BoundedContinuousFunction (Fin n → ℝ) ℝ} {H : ℝ}
    (hH : IsHolderConst α f H) :
    IsHolderConst α (heatSemigroupNDbcf ht f) H := by
  refine ⟨hH.1, fun a b => ?_⟩
  have hint : ∀ x : Fin n → ℝ,
      Integrable (fun z : Fin n → ℝ => heatKernelND t z * f (x - z)) :=
    fun x => (integrable_heatKernelND ht).mul_bdd
      ((f.continuous.comp (continuous_const.sub continuous_id')).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (x - z)))
  have hdiff : heatSemigroupNDbcf ht f a - heatSemigroupNDbcf ht f b =
      ∫ z : Fin n → ℝ, heatKernelND t z * (f (a - z) - f (b - z)) := by
    rw [heatSemigroupNDbcf_apply, heatSemigroupNDbcf_apply,
      heatSemigroupND_eq_integral_kernel_mul_sub _ a,
      heatSemigroupND_eq_integral_kernel_mul_sub _ b,
      ← integral_sub (hint a) (hint b)]
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hpoint : ∀ z : Fin n → ℝ,
      ‖heatKernelND t z * (f (a - z) - f (b - z))‖ ≤
        heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α) := by
    intro z
    have hK : 0 ≤ heatKernelND t z := heatKernelND_nonneg ht z
    have hh := hH.2 (a - z) (b - z)
    rw [sub_sub_sub_cancel_right] at hh
    calc ‖heatKernelND t z * (f (a - z) - f (b - z))‖
        = heatKernelND t z * |f (a - z) - f (b - z)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
      _ ≤ heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
          mul_le_mul_of_nonneg_left hh hK
  have hRHS : Integrable (fun z : Fin n → ℝ =>
      heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α)) :=
    (integrable_heatKernelND ht).mul_const _
  have hint_diff : Integrable (fun z : Fin n → ℝ =>
      heatKernelND t z * (f (a - z) - f (b - z))) := by
    refine Integrable.congr ((hint a).sub (hint b))
      (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Pi.sub_apply, mul_sub]
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∫ z : Fin n → ℝ, heatKernelND t z * (f (a - z) - f (b - z))‖
      ≤ ∫ z : Fin n → ℝ, ‖heatKernelND t z * (f (a - z) - f (b - z))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Fin n → ℝ, heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hRHS
          (Filter.Eventually.of_forall hpoint)
    _ = H * ∑ j : Fin n, |(a - b) j| ^ α := by
        have heq : (fun z : Fin n → ℝ =>
            heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α))
            = fun z => (H * ∑ j : Fin n, |(a - b) j| ^ α) * heatKernelND t z := by
          funext z; ring
        rw [heq, integral_const_mul, integral_heatKernelND ht, mul_one]

/-! ## 2. The heat semigroup as a contraction on `HolderBCF` -/

/-- The underlying function of the restricted heat semigroup. -/
noncomputable def heatSemigroupHolderFun {t : ℝ} (ht : 0 < t)
    (f : HolderBCF α n) : HolderBCF α n :=
  ⟨heatSemigroupNDbcf ht f.toBCF,
    let ⟨H, hH⟩ := f.holderEx; ⟨H, isHolderConst_heatSemigroupNDbcf ht hH⟩⟩

@[simp] theorem heatSemigroupHolderFun_toBCF {t : ℝ} (ht : 0 < t)
    (f : HolderBCF α n) :
    (heatSemigroupHolderFun ht f).toBCF = heatSemigroupNDbcf ht f.toBCF := rfl

/-- The Hölder seminorm does not increase under heat flow: every Hölder
constant of `f` is one of `S t f`, so the infimum can only drop. -/
theorem holderSeminorm_heatSemigroupHolderFun_le {t : ℝ} (ht : 0 < t)
    (f : HolderBCF α n) :
    HolderBCF.holderSeminorm (heatSemigroupHolderFun ht f) ≤ HolderBCF.holderSeminorm f := by
  have hsub : {H : ℝ | IsHolderConst α f.toBCF H} ⊆
      {H : ℝ | IsHolderConst α (heatSemigroupHolderFun ht f).toBCF H} := by
    intro H hH
    show IsHolderConst α (heatSemigroupHolderFun ht f).toBCF H
    rw [heatSemigroupHolderFun_toBCF]
    exact isHolderConst_heatSemigroupNDbcf ht hH
  show sInf {H : ℝ | IsHolderConst α (heatSemigroupHolderFun ht f).toBCF H} ≤
    sInf {H : ℝ | IsHolderConst α f.toBCF H}
  apply le_csInf f.holderEx
  intro H hH
  apply csInf_le (HolderBCF.bddBelow_holderSet (heatSemigroupHolderFun ht f))
  exact hsub hH

/-- The heat semigroup restricts to a continuous linear contraction on the
Hölder space: `‖S t f‖_{C^α} ≤ ‖f‖_{C^α}` since both the sup-norm and the
Hölder seminorm are nonincreasing. -/
noncomputable def heatSemigroupHolderCLM {t : ℝ} (ht : 0 < t) :
    HolderBCF α n →L[ℝ] HolderBCF α n :=
  LinearMap.mkContinuous
    { toFun := heatSemigroupHolderFun ht
      map_add' := fun f g => Subtype.ext (by
        show (heatSemigroupHolderFun ht (f + g)).toBCF
          = (heatSemigroupHolderFun ht f + heatSemigroupHolderFun ht g).toBCF
        rw [heatSemigroupHolderFun_toBCF, HolderBCF.add_toBCF,
          heatSemigroupNDbcf_add ht, HolderBCF.add_toBCF,
          heatSemigroupHolderFun_toBCF, heatSemigroupHolderFun_toBCF])
      map_smul' := fun c f => Subtype.ext (by
        show (heatSemigroupHolderFun ht (c • f)).toBCF
          = (c • heatSemigroupHolderFun ht f).toBCF
        rw [heatSemigroupHolderFun_toBCF, HolderBCF.smul_toBCF,
          heatSemigroupNDbcf_smul ht, HolderBCF.smul_toBCF,
          heatSemigroupHolderFun_toBCF]) }
    1
    (fun f => by
      show ‖heatSemigroupHolderFun ht f‖ ≤ 1 * ‖f‖
      rw [one_mul, HolderBCF.norm_def, HolderBCF.norm_def,
        heatSemigroupHolderFun_toBCF]
      apply add_le_add
      · exact norm_heatSemigroupNDbcf_le ht f.toBCF
      · exact holderSeminorm_heatSemigroupHolderFun_le ht f)

/-- The restricted heat semigroup has operator norm `≤ 1`. -/
theorem norm_heatSemigroupHolderCLM_le {t : ℝ} (ht : 0 < t) :
    ‖heatSemigroupHolderCLM (α := α) (n := n) ht‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## 3. The heat propagator on `HolderBCF` -/

/-- The heat propagator on the Hölder space: the heat semigroup for `t > 0`,
the identity for `t ≤ 0`. This is the candidate for `DuhamelData.S`. -/
noncomputable def heatPropagatorHolderCLM (t : ℝ) :
    HolderBCF α n →L[ℝ] HolderBCF α n :=
  if ht : 0 < t then heatSemigroupHolderCLM ht else ContinuousLinearMap.id ℝ _

@[simp] theorem heatPropagatorHolderCLM_of_pos {t : ℝ} (ht : 0 < t) :
    heatPropagatorHolderCLM (n := n) (α := α) t = heatSemigroupHolderCLM ht := by
  simp only [heatPropagatorHolderCLM, dif_pos ht]

@[simp] theorem heatPropagatorHolderCLM_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatPropagatorHolderCLM (n := n) (α := α) t = ContinuousLinearMap.id ℝ _ := by
  simp only [heatPropagatorHolderCLM, dif_neg (not_lt.mpr ht)]

/-- The propagator has operator norm `≤ 1` at every time. -/
theorem norm_heatPropagatorHolderCLM_le (t : ℝ) :
    ‖heatPropagatorHolderCLM (n := n) (α := α) t‖ ≤ 1 := by
  unfold heatPropagatorHolderCLM
  split
  · next ht => exact norm_heatSemigroupHolderCLM_le ht
  · exact ContinuousLinearMap.norm_id_le

/-- The `DuhamelData.hSbound` bound for the Hölder heat propagator, with `M = 1`. -/
theorem heatPropagatorHolderCLM_hSbound {T : ℝ} (t : ℝ) (_ht : t ∈ Icc 0 T) :
    ‖heatPropagatorHolderCLM (n := n) (α := α) t‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  have h := norm_heatPropagatorHolderCLM_le (n := n) (α := α) t
  simpa using h

@[simp] theorem heatSemigroupHolderCLM_toBCF {t : ℝ} (ht : 0 < t)
    (f : HolderBCF α n) :
    (heatSemigroupHolderCLM ht f).toBCF = heatSemigroupNDbcf ht f.toBCF := rfl

/-! ## 4. Sup-norm strong continuity at heat-time zero -/

/-- Quantitative sup-norm bound for the propagator at small positive times,
from the approximate-identity estimate. -/
theorem norm_heatPropagatorHolderCLM_toBCF_sub_self_le (hα : 0 < α)
    (f : HolderBCF α n) {H : ℝ} (hH : IsHolderConst α f.toBCF H)
    {t : ℝ} (ht : 0 < t) :
    ‖(heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF - f.toBCF‖ ≤
      H * ∑ _j : Fin n, (Real.sqrt t) ^ α * gaussianAbsMoment α := by
  rw [heatPropagatorHolderCLM_of_pos ht, heatSemigroupHolderCLM_toBCF]
  exact norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder ht hα.le f.toBCF hH.1 hH.2

/-- Strong continuity at heat-time `0` in the sup-norm component: for
`0 < α` and Hölder datum `f`, `S t f → f` uniformly as `t → 0⁺`.
This is the honest continuity available; the Hölder-seminorm component
does not vanish at the same exponent (see the module docstring). -/
theorem tendsto_heatPropagatorHolderCLM_toBCF_nhdsWithin_zero (hα : 0 < α)
    (f : HolderBCF α n) :
    Filter.Tendsto (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f.toBCF) := by
  obtain ⟨H, hH⟩ := f.holderEx
  have hbound : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      ‖(heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF - f.toBCF‖ ≤
        H * ∑ _j : Fin n, (Real.sqrt t) ^ α * gaussianAbsMoment α := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact norm_heatPropagatorHolderCLM_toBCF_sub_self_le hα f hH ht
  have hRHS : Filter.Tendsto
      (fun t : ℝ => H * ∑ _j : Fin n, (Real.sqrt t) ^ α * gaussianAbsMoment α)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hsqrt : Filter.Tendsto (fun t : ℝ => Real.sqrt t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
        Real.continuous_sqrt.tendsto 0
      rw [Real.sqrt_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hrpow : Filter.Tendsto (fun t : ℝ => (Real.sqrt t) ^ α)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      hsqrt.rpow_const_nhds_zero hα
    have hsum : Filter.Tendsto
        (fun t : ℝ => ∑ _j : Fin n, (Real.sqrt t) ^ α * gaussianAbsMoment α)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ _j : Fin n, (0 : ℝ) * gaussianAbsMoment α)) :=
      tendsto_finsetSum _ (fun j _ =>
        hrpow.mul (tendsto_const_nhds (x := gaussianAbsMoment α)))
    have hsum0 : (∑ _j : Fin n, (0 : ℝ) * gaussianAbsMoment α) = 0 := by
      simp
    rw [hsum0] at hsum
    have := hsum.const_mul H
    simpa [mul_comm] using this
  have hsub : Filter.Tendsto
      (fun t : ℝ => (heatPropagatorHolderCLM (n := n) (α := α) t f).toBCF - f.toBCF)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero_norm' hbound hRHS
  have hadd := hsub.add_const f.toBCF
  simpa using hadd

end AnalyticPDE
end RicciFlow
