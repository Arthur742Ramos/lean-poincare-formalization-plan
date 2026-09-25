/-
Point 4 — PDE milestone: the Euclidean heat propagator as `DuhamelData.S`.

This file packages the positive-time heat semigroup on bounded continuous
functions (`heatSemigroupNDclm`) as a propagator `S : ℝ → BCF →L[ℝ] BCF`
which equals the semigroup for `t > 0` and the identity for `t ≤ 0`.

Proved here:
* `norm_heatPropagatorCLM_le` : operator norm `≤ 1` for all `t`
  (the `DuhamelData.hSbound` ingredient with `M = 1`).
* `continuousAt_integral_heatKernel_mul` : for `t₀ > 0`, the heat-potential
  integral `t ↦ ∫ z, heatKernelND t z * g z` is continuous at `t₀`,
  by dominated convergence (Gaussian majorant on `Icc (t₀/2) (2*t₀)`).
* `continuousAt_heatPropagatorCLM` : pointwise (in `x`) time-continuity of
  the propagator at `t₀ > 0`.
* `heatPropagatorCLM_hSbound` : the exact `DuhamelData.hSbound` statement.

Analytic obstruction (documented, not proved): full `DuhamelData.hSjoint`,
i.e. joint continuity of `(t,f) ↦ S t f` on `Icc 0 T ×ˢ univ` in the
`C⁰` (sup-norm) topology, is *false* on all bounded continuous functions
on noncompact Euclidean space — strong continuity at `t = 0` fails there.
A full `DuhamelData` instantiation needs a smaller state space (e.g. a
Hölder subspace, where `norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder`
gives strong right-continuity at `0`) or a weakened abstract continuity
requirement. We do not fake it here.
-/

import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {n : ℕ}

/-- The heat propagator: the heat semigroup for `t > 0`, the identity for
`t ≤ 0`. This is the candidate for `DuhamelData.S`. -/
noncomputable def heatPropagatorCLM (t : ℝ) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ →L[ℝ]
      BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  if ht : 0 < t then heatSemigroupNDclm ht else ContinuousLinearMap.id ℝ _

/-- The propagator agrees with the heat semigroup at positive times. -/
@[simp] theorem heatPropagatorCLM_of_pos {t : ℝ} (ht : 0 < t) :
    heatPropagatorCLM (n := n) t = heatSemigroupNDclm ht := by
  rw [heatPropagatorCLM, dif_pos ht]

/-- The propagator is the identity at nonpositive times. -/
@[simp] theorem heatPropagatorCLM_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    heatPropagatorCLM (n := n) t = ContinuousLinearMap.id ℝ _ := by
  rw [heatPropagatorCLM, dif_neg (not_lt.mpr ht)]

/-- The propagator has operator norm `≤ 1` at every time. -/
theorem norm_heatPropagatorCLM_le (t : ℝ) :
    ‖heatPropagatorCLM (n := n) t‖ ≤ 1 := by
  unfold heatPropagatorCLM
  split
  · next ht => exact norm_heatSemigroupNDclm_le ht
  · exact ContinuousLinearMap.norm_id_le

/-- Precomposition of a bounded continuous function with the reflection
`y ↦ x - y` (used to put the heat convolution in fixed-kernel form). -/
noncomputable def bcfSubRight (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ⟨⟨fun y => f (x - y), f.continuous.comp (continuous_const.sub continuous_id')⟩,
    by obtain ⟨C, hC⟩ := f.map_bounded'; exact ⟨C, fun a b => hC _ _⟩⟩

@[simp] theorem bcfSubRight_apply (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x y : Fin n → ℝ) : bcfSubRight f x y = f (x - y) := rfl

/-- Continuity at `t₀ > 0` of the heat-potential integral
`t ↦ ∫ z, heatKernelND t z * g z`, by dominated convergence.
The dominating function is a multiple of the fixed Gaussian
`heatKernelND (2*t₀)`, integrable by `integrable_heatKernelND`. -/
theorem continuousAt_integral_heatKernel_mul {t₀ : ℝ} (ht₀ : 0 < t₀)
    (g : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ContinuousAt
      (fun t : ℝ => ∫ z : Fin n → ℝ, heatKernelND t z * g z) t₀ := by
  rw [ContinuousAt]
  have h2t₀ : (0:ℝ) < 2 * t₀ := by linarith
  have hIcc : Icc (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  -- The domination constant `C(t₀) * ‖g‖`, with `C(t₀)` from
  -- `heatKernelND_le_const_mul_heatKernelND_of_mem_Icc`.
  set C : ℝ := ((4 * Real.pi * (t₀ / 2)) ^ (-(1:ℝ) / 2) *
    (4 * Real.pi * (2 * t₀)) ^ ((1:ℝ) / 2)) ^ n * ‖g‖ with hCdef
  have hbound_int : Integrable
      (fun z : Fin n → ℝ => C * heatKernelND (2 * t₀) z) volume :=
    (integrable_heatKernelND h2t₀).const_mul C
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝 t₀) (μ := volume)
    (fun z : Fin n → ℝ => C * heatKernelND (2 * t₀) z) ?_ ?_ hbound_int ?_
  · -- Each `F t` is AEStronglyMeasurable (it is continuous in `z`).
    filter_upwards with t
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · -- `z ↦ heatKernelND t z` is continuous.
      exact continuous_heatKernelND t
    · -- `z ↦ g z` is continuous.
      exact g.continuous
  · -- Domination on `Icc (t₀/2) (2*t₀)`.
    filter_upwards [hIcc] with t ht
    apply Eventually.of_forall
    intro z
    have hkle := heatKernelND_le_const_mul_heatKernelND_of_mem_Icc (n := n)
      (show (0:ℝ) < t₀ / 2 by linarith) ht.1 ht.2 z
    have hnn : 0 ≤ heatKernelND t z :=
      heatKernelND_nonneg (lt_of_lt_of_le (by linarith) ht.1) z
    have hgbound : ‖g z‖ ≤ ‖g‖ := g.norm_coe_le_norm z
    have h1 : ‖heatKernelND t z * g z‖ = heatKernelND t z * ‖g z‖ := by
      rw [norm_mul, Real.norm_of_nonneg hnn]
    -- The constant is nonnegative.
    have hbase1 : (0:ℝ) < 4 * Real.pi * (t₀ / 2) := by
      have hpi : (0:ℝ) < 4 * Real.pi := by positivity
      have h2 : (0:ℝ) < t₀ / 2 := by linarith
      exact mul_pos hpi h2
    have hbase2 : (0:ℝ) < 4 * Real.pi * (2 * t₀) := by
      have hpi : (0:ℝ) < 4 * Real.pi := by positivity
      have h3 : (0:ℝ) < 2 * t₀ := by linarith
      exact mul_pos hpi h3
    have hCnn : (0:ℝ) ≤ ((4 * Real.pi * (t₀ / 2)) ^ (-(1:ℝ) / 2) *
        (4 * Real.pi * (2 * t₀)) ^ ((1:ℝ) / 2)) ^ n :=
      pow_nonneg (mul_nonneg (Real.rpow_pos_of_pos hbase1 _).le
        (Real.rpow_pos_of_pos hbase2 _).le) n
    have hCKnn : (0:ℝ) ≤ ((4 * Real.pi * (t₀ / 2)) ^ (-(1:ℝ) / 2) *
        (4 * Real.pi * (2 * t₀)) ^ ((1:ℝ) / 2)) ^ n * heatKernelND (2 * t₀) z :=
      mul_nonneg hCnn (heatKernelND_nonneg h2t₀ z)
    rw [h1]
    calc heatKernelND t z * ‖g z‖
        ≤ (((4 * Real.pi * (t₀ / 2)) ^ (-(1:ℝ) / 2) *
              (4 * Real.pi * (2 * t₀)) ^ ((1:ℝ) / 2)) ^ n *
            heatKernelND (2 * t₀) z) * ‖g z‖ :=
          mul_le_mul_of_nonneg_right hkle (norm_nonneg _)
      _ ≤ (((4 * Real.pi * (t₀ / 2)) ^ (-(1:ℝ) / 2) *
              (4 * Real.pi * (2 * t₀)) ^ ((1:ℝ) / 2)) ^ n *
            heatKernelND (2 * t₀) z) * ‖g‖ :=
          mul_le_mul_of_nonneg_left hgbound hCKnn
      _ = C * heatKernelND (2 * t₀) z := by rw [hCdef]; ring
  · -- Pointwise convergence in `t`, by continuity of the kernel in time.
    apply Eventually.of_forall
    intro z
    exact ((continuousAt_heatKernelND_time ht₀ z).mul tendsto_const_nhds)

/-- Pointwise (in `x`) time-continuity of the heat propagator at `t₀ > 0`:
`(S t f) x → (S t₀ f) x` as `t → t₀`. -/
theorem continuousAt_heatPropagatorCLM {t₀ : ℝ} (ht₀ : 0 < t₀)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ) :
    ContinuousAt (fun t : ℝ => (heatPropagatorCLM (n := n) t f) x) t₀ := by
  have heq : ∀ᶠ t in 𝓝 t₀,
      (heatPropagatorCLM (n := n) t f) x =
        ∫ z : Fin n → ℝ, heatKernelND t z * (bcfSubRight f x) z := by
    filter_upwards [eventually_gt_nhds ht₀] with t ht
    rw [heatPropagatorCLM_of_pos ht, heatSemigroupNDclm_apply,
      heatSemigroupNDbcf_apply, heatSemigroupND_eq_integral_kernel_mul_sub]
    simp only [bcfSubRight_apply]
  have hlim : (∫ z : Fin n → ℝ, heatKernelND t₀ z * (bcfSubRight f x) z) =
      (heatPropagatorCLM (n := n) t₀ f) x := by
    rw [heatPropagatorCLM_of_pos ht₀, heatSemigroupNDclm_apply,
      heatSemigroupNDbcf_apply, heatSemigroupND_eq_integral_kernel_mul_sub]
    simp only [bcfSubRight_apply]
  have hcont := continuousAt_integral_heatKernel_mul (n := n) ht₀ (bcfSubRight f x)
  rw [ContinuousAt, hlim] at hcont
  have heq' : (fun t : ℝ => (heatPropagatorCLM (n := n) t f) x) =ᶠ[𝓝 t₀]
      (fun t : ℝ => ∫ z : Fin n → ℝ, heatKernelND t z * (bcfSubRight f x) z) :=
    heq
  have hcont' : Filter.Tendsto
      (fun t : ℝ => ∫ z : Fin n → ℝ, heatKernelND t z * (bcfSubRight f x) z)
      (𝓝 t₀) (𝓝 ((heatPropagatorCLM (n := n) t₀ f) x)) := hcont
  exact hcont'.congr' heq'.symm

/-- The `DuhamelData.hSbound` bound for the heat propagator, with `M = 1`. -/
theorem heatPropagatorCLM_hSbound {T : ℝ} (t : ℝ) (_ht : t ∈ Icc 0 T) :
    ‖heatPropagatorCLM (n := n) t‖ ≤ ((1 : ℝ≥0) : ℝ) := by
  have h := norm_heatPropagatorCLM_le (n := n) t
  simpa using h

end AnalyticPDE
end RicciFlow
