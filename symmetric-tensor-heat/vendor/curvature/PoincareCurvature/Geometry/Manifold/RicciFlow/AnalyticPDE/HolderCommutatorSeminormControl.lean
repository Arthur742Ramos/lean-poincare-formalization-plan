import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TaylorCommutatorPointwise
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroupRestriction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TranslationMeasurability

/-!
# Hölder-seminorm control for the Taylor commutator (Point 4 PDE milestone)

This file lifts the pointwise Taylor commutator estimate to Hölder-seminorm
control, a key analytic ingredient for the Duhamel fixed-point argument.

## Mathematical content

For `F : ℝ → ℝ` with `M`-Lipschitz derivative and `f` Hölder with constant `H`,
the commutator
  `C(t,x) = S(t)(F∘f)(x) - F(S(t)f(x))`
satisfies:

1. **Lipschitz bound for `F` on bounded intervals**
   (`abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc`):
   If `F'` is `M`-Lipschitz, then for `x, y ∈ Icc (-C) C`,
   `|F x - F y| ≤ (|F'(0)| + M*C) * |x - y|`, via the mean value theorem.

2. **Hölder regularity of the commutator** (`isHolderConst_commutator_taylor`):
   `C(t,·)` is `α`-Hölder with explicit constant. The proof decomposes the
   commutator as a difference of two Hölder functions.

3. **Quantitative sup-norm bound** is inherited from
   `commutator_taylor_pointwise`: `‖C(t,·)‖∞ = O(t^α)`.

## Status

**Proved here** (genuine, no sorry):
- `abs_deriv_le_of_lipschitz_deriv_on_Icc`: Bound on `|F'|` over `Icc (-C) C`.
- `abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc`: `F` is Lipschitz on
  `Icc (-C) C` with constant `|F'(0)| + M*C`, via the mean value theorem.
  This is the key estimate needed for Hölder composition with `C^{1,1}`
  nonlinearities.
- `isHolderConst_heatSemigroupND_raw`: Heat semigroup preserves Hölder
  regularity for raw functions (using `aestronglyMeasurable_comp_sub_left`
  from `TranslationMeasurability` to resolve the measurability technicality).
- `isHolderConst_commutator_taylor`: The commutator `C(t,·)` is `α`-Hölder
  with explicit constant `2 * (|F'(0)| + M*C) * H`.

**Not proved here** (documented gaps):
- The sharp vanishing Hölder-seminorm rate (the constant does not vanish as `t → 0`).
- Tensorial (matrix-valued) extension for the genuine Ricci–DeTurck `N`.

No `sorry`, no `admit`, no axioms in the proved results.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory
open scoped NNReal

variable {n : ℕ} {α : ℝ}

/-! ## 1. Lipschitz bound for `F` on `Icc (-C) C` -/

/-- Auxiliary: bound on `|F' x|` for `x ∈ Icc (-C) C` when `F'` is `M`-Lipschitz. -/
theorem abs_deriv_le_of_lipschitz_deriv_on_Icc
    {F' : ℝ → ℝ} {M : ℝ≥0}
    (hLip : LipschitzWith M F')
    {C : ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc (-C) C) :
    |F' x| ≤ |F' 0| + (M : ℝ) * C := by
  rw [Set.mem_Icc] at hx
  have h1 : |F' x - F' 0| ≤ (M : ℝ) * |x - 0| := by
    have h := hLip.dist_le_mul x 0
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs] at h
    simpa using h
  have hx_abs : |x| ≤ C := by
    have hC_nn : 0 ≤ C := by
      have h1 : (0:ℝ) ≤ |x| := abs_nonneg x
      have h2 : |x| ≤ C := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
      linarith
    rw [abs_le]
    exact ⟨hx.1, hx.2⟩
  have h2 : (M : ℝ) * |x| ≤ (M : ℝ) * C :=
    mul_le_mul_of_nonneg_left hx_abs M.coe_nonneg
  calc |F' x| = |(F' x - F' 0) + F' 0| := by ring_nf
    _ ≤ |F' x - F' 0| + |F' 0| := abs_add_le _ _
    _ ≤ (M : ℝ) * |x - 0| + |F' 0| := by linarith [h1]
    _ = |F' 0| + (M : ℝ) * |x| := by rw [sub_zero]; ring
    _ ≤ |F' 0| + (M : ℝ) * C := by linarith [h2]

/-- **Pointwise Lipschitz bound for `F` on `Icc (-C) C` when `F'` is `M`-Lipschitz.**

For `x, y ∈ Icc (-C) C`, the mean value theorem gives `c` between `x` and `y`
with `F y - F x = F'(c) * (y - x)`. Since `c ∈ Icc (-C) C` (convexity),
`|F'(c)| ≤ |F'(0)| + M*C`, hence `|F x - F y| ≤ (|F'(0)| + M*C) * |x - y|`. -/
theorem abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc
    {F F' : ℝ → ℝ} {M : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hLip : LipschitzWith M F')
    {C : ℝ}
    {x y : ℝ} (hx : x ∈ Set.Icc (-C) C) (hy : y ∈ Set.Icc (-C) C) :
    |F x - F y| ≤ (|F' 0| + (M : ℝ) * C) * |x - y| := by
  rw [Set.mem_Icc] at hx hy
  rcases eq_or_ne x y with rfl | hne
  · simp
  · rcases lt_or_gt_of_ne hne with hxy | hyx
    · -- Case x < y
      have hcont : Continuous F := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hF z).continuousAt
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' hxy
        hcont.continuousOn (fun z _ => hF z)
      have hc_mem : c ∈ Set.Ioo x y := hc
      rw [Set.mem_Ioo] at hc_mem
      obtain ⟨hcx, hcy⟩ := hc_mem
      have hc_Icc : c ∈ Set.Icc (-C) C := by
        rw [Set.mem_Icc]
        exact ⟨le_trans hx.1 hcx.le, le_trans hcy.le hy.2⟩
      have hFc : |F' c| ≤ |F' 0| + (M : ℝ) * C :=
        abs_deriv_le_of_lipschitz_deriv_on_Icc hLip hc_Icc
      have hyx_ne : y - x ≠ 0 := by
        intro h
        have : y = x := by linarith
        exact hne this.symm
      have hFyFx : F y - F x = F' c * (y - x) := by
        rw [heq]
        field_simp
      calc |F x - F y| = |F y - F x| := abs_sub_comm _ _
        _ = |F' c * (y - x)| := by rw [hFyFx]
        _ = |F' c| * |y - x| := abs_mul _ _
        _ ≤ (|F' 0| + (M : ℝ) * C) * |y - x| :=
            mul_le_mul_of_nonneg_right hFc (abs_nonneg _)
        _ = (|F' 0| + (M : ℝ) * C) * |x - y| := by rw [abs_sub_comm]
    · -- Case y < x (symmetric)
      have hcont : Continuous F := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hF z).continuousAt
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' hyx
        hcont.continuousOn (fun z _ => hF z)
      have hc_mem : c ∈ Set.Ioo y x := hc
      rw [Set.mem_Ioo] at hc_mem
      obtain ⟨hcy, hcx⟩ := hc_mem
      have hc_Icc : c ∈ Set.Icc (-C) C := by
        rw [Set.mem_Icc]
        exact ⟨le_trans hy.1 hcy.le, le_trans hcx.le hx.2⟩
      have hFc : |F' c| ≤ |F' 0| + (M : ℝ) * C :=
        abs_deriv_le_of_lipschitz_deriv_on_Icc hLip hc_Icc
      have hxy_ne : x - y ≠ 0 := by
        intro h
        have : x = y := by linarith
        exact hne this
      have hFxFy : F x - F y = F' c * (x - y) := by
        rw [heq]
        field_simp
      calc |F x - F y| = |F' c * (x - y)| := by rw [hFxFy]
        _ = |F' c| * |x - y| := abs_mul _ _
        _ ≤ (|F' 0| + (M : ℝ) * C) * |x - y| :=
            mul_le_mul_of_nonneg_right hFc (abs_nonneg _)

/-! ## 2. Heat semigroup Hölder preservation for raw functions -/

/-- **Heat semigroup preserves Hölder regularity for raw functions.**

If `f` is `α`-Hölder with constant `H`, then `S(t)f` is `α`-Hölder with the
same constant `H`. The proof follows the BCF version
(`isHolderConst_heatSemigroupNDbcf`): the difference `S(t)f(a) - S(t)f(b)`
is the kernel integral of `f(a - z) - f(b - z)`, and
`(a - z) - (b - z) = a - b`, so the Hölder bound passes under the integral
against the probability kernel.

The key measurability step uses `aestronglyMeasurable_comp_sub_left` to get
`AEStronglyMeasurable (fun z => f (x - z))` from `AEStronglyMeasurable f`. -/
theorem isHolderConst_heatSemigroupND_raw {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {H C : ℝ}
    (hfm : AEStronglyMeasurable f)
    (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ a b, |f a - f b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α) :
    ∀ a b, |heatSemigroupND t f a - heatSemigroupND t f b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ α := by
  intro a b
  -- Step 1: Integrability of the kernel-weighted shifted function for each x
  have hint : ∀ x : Fin n → ℝ,
      Integrable (fun z : Fin n → ℝ => heatKernelND t z * f (x - z)) := by
    intro x
    apply (integrable_heatKernelND ht).mul_bdd
    · exact aestronglyMeasurable_comp_sub_left x hfm
    · apply Filter.Eventually.of_forall
      intro z
      exact hfb (x - z)
  -- Step 2: The difference as a kernel integral
  have hdiff : heatSemigroupND t f a - heatSemigroupND t f b =
      ∫ z : Fin n → ℝ, heatKernelND t z * (f (a - z) - f (b - z)) := by
    rw [heatSemigroupND_eq_integral_kernel_mul_sub f a,
      heatSemigroupND_eq_integral_kernel_mul_sub f b,
      ← integral_sub (hint a) (hint b)]
    apply integral_congr_ae
    filter_upwards with z
    ring
  -- Step 3: Pointwise bound using the Hölder condition and (a-z)-(b-z) = a-b
  have hpoint : ∀ z : Fin n → ℝ,
      ‖heatKernelND t z * (f (a - z) - f (b - z))‖ ≤
        heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α) := by
    intro z
    have hK : 0 ≤ heatKernelND t z := heatKernelND_nonneg ht z
    have hh := hholder (a - z) (b - z)
    rw [sub_sub_sub_cancel_right] at hh
    calc ‖heatKernelND t z * (f (a - z) - f (b - z))‖
        = heatKernelND t z * |f (a - z) - f (b - z)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
      _ ≤ heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
          mul_le_mul_of_nonneg_left hh hK
  -- Step 4: Integrate the bound; the kernel integrates to 1
  have hRHS : Integrable (fun z : Fin n → ℝ =>
      heatKernelND t z * (H * ∑ j : Fin n, |(a - b) j| ^ α)) :=
    (integrable_heatKernelND ht).mul_const _
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

/-! ## 3. Commutator Hölder bound -/

/-- **Commutator is Hölder.**

For `F : ℝ → ℝ` with `M`-Lipschitz derivative and `f` Hölder with constant `H`,
the commutator `C(t,x) = S(t)(F∘f)(x) - F(S(t)f(x))` is `α`-Hölder with
explicit constant `2 * L_F * H`, where `L_F = |F'(0)| + M*C` is the Lipschitz
constant of `F` on `Icc (-C) C`.

The proof decomposes the commutator as a difference of two Hölder functions:
1. `F∘f` is Hölder with `L_F * H` (Lipschitz `F` ∘ Hölder `f`).
2. `S(t)(F∘f)` is Hölder with `L_F * H` (preservation).
3. `S(t)f` is Hölder with `H` (preservation).
4. `F(S(t)f)` is Hölder with `L_F * H` (Lipschitz `F` ∘ Hölder `S(t)f`).
5. Difference is Hölder with `2 * L_F * H` (triangle inequality). -/
theorem isHolderConst_commutator_taylor
    {n : ℕ} {t α : ℝ} (ht : 0 < t)
    {F F' : ℝ → ℝ} {M : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hLip : LipschitzWith M F')
    {f : (Fin n → ℝ) → ℝ} {C H : ℝ} (_hH : 0 ≤ H) (hC : 0 ≤ C)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ a b, |f a - f b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α) :
    ∀ a b, |heatSemigroupND t (fun y => F (f y)) a - F (heatSemigroupND t f a)
            - (heatSemigroupND t (fun y => F (f y)) b - F (heatSemigroupND t f b))| ≤
      2 * (|F' 0| + (M : ℝ) * C) * H * ∑ j : Fin n, |(a - b) j| ^ α := by
  -- Lipschitz constant of F on Icc (-C) C
  set L_F := |F' 0| + (M : ℝ) * C with hL_F
  have hL_F_nn : 0 ≤ L_F := by
    apply add_nonneg (abs_nonneg _)
    exact mul_nonneg M.coe_nonneg hC
  -- Helper: membership in Icc (-C) C from norm bound
  have hmem_Icc : ∀ z : ℝ, ‖z‖ ≤ C → z ∈ Set.Icc (-C) C := by
    intro z hz
    rw [Set.mem_Icc, ← abs_le]
    calc |z| = ‖z‖ := (Real.norm_eq_abs z).symm
      _ ≤ C := hz
  -- Step 1: F∘f is Hölder with L_F * H
  have hFoF_holder : ∀ a b : Fin n → ℝ,
      |F (f a) - F (f b)| ≤ L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by
    intro a b
    have h1 : |F (f a) - F (f b)| ≤ L_F * |f a - f b| :=
      abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc hF hLip
        (hmem_Icc _ (hfb a)) (hmem_Icc _ (hfb b))
    have h2 : |f a - f b| ≤ H * ∑ j : Fin n, |(a - b) j| ^ α := hholder a b
    calc |F (f a) - F (f b)| ≤ L_F * |f a - f b| := h1
      _ ≤ L_F * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
          mul_le_mul_of_nonneg_left h2 hL_F_nn
      _ = L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by ring
  -- Boundedness of F∘f (needed for preservation)
  obtain ⟨B, hB_Icc⟩ := bdd_on_Icc_of_hasDerivAt hF (C := C)
  have hFoF_bdd : ∀ y, ‖F (f y)‖ ≤ B := fun y =>
    hB_Icc _ (hmem_Icc _ (hfb y))
  have hFoF_meas : AEStronglyMeasurable (fun y => F (f y)) :=
    aestronglyMeasurable_comp_of_hasDerivAt hF hfm
  -- Step 2: S(t)(F∘f) is Hölder with L_F * H
  have hS_FoF_holder := isHolderConst_heatSemigroupND_raw ht hFoF_meas hFoF_bdd
    (fun a b => by
      have h := hFoF_holder a b
      rw [show L_F * H * _ = (L_F * H) * _ from rfl] at h ⊢
      exact h)
  -- Step 3: S(t)f is Hölder with H
  have hS_f_holder := isHolderConst_heatSemigroupND_raw ht hfm hfb hholder
  -- Step 4: F(S(t)f) is Hölder with L_F * H
  -- (S(t)f(x) stays in Icc (-C) C by abs_heatSemigroupND_bound)
  have hF_Sf_holder : ∀ a b : Fin n → ℝ,
      |F (heatSemigroupND t f a) - F (heatSemigroupND t f b)| ≤
        L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by
    intro a b
    have hSa_mem : heatSemigroupND t f a ∈ Set.Icc (-C) C := by
      apply hmem_Icc
      rw [Real.norm_eq_abs]
      exact abs_heatSemigroupND_bound ht hfb a
    have hSb_mem : heatSemigroupND t f b ∈ Set.Icc (-C) C := by
      apply hmem_Icc
      rw [Real.norm_eq_abs]
      exact abs_heatSemigroupND_bound ht hfb b
    have h1 : |F (heatSemigroupND t f a) - F (heatSemigroupND t f b)| ≤
        L_F * |heatSemigroupND t f a - heatSemigroupND t f b| :=
      abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc hF hLip hSa_mem hSb_mem
    have h2 : |heatSemigroupND t f a - heatSemigroupND t f b| ≤
        H * ∑ j : Fin n, |(a - b) j| ^ α := hS_f_holder a b
    calc |F (heatSemigroupND t f a) - F (heatSemigroupND t f b)|
        ≤ L_F * |heatSemigroupND t f a - heatSemigroupND t f b| := h1
      _ ≤ L_F * (H * ∑ j : Fin n, |(a - b) j| ^ α) :=
          mul_le_mul_of_nonneg_left h2 hL_F_nn
      _ = L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by ring
  -- Step 5: Commutator via triangle inequality
  intro a b
  have h1 := hS_FoF_holder a b
  have h2 := hF_Sf_holder a b
  -- |C(a) - C(b)| = |(S(F∘f)(a) - S(F∘f)(b)) - (F(Sf(a)) - F(Sf(b)))|
  have heq : heatSemigroupND t (fun y => F (f y)) a - F (heatSemigroupND t f a)
      - (heatSemigroupND t (fun y => F (f y)) b - F (heatSemigroupND t f b))
      = (heatSemigroupND t (fun y => F (f y)) a - heatSemigroupND t (fun y => F (f y)) b)
        - (F (heatSemigroupND t f a) - F (heatSemigroupND t f b)) := by ring
  rw [heq]
  have htri : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := by
    intro X Y
    calc |X - Y| = |X + (-Y)| := by rw [sub_eq_add_neg]
      _ ≤ |X| + |-Y| := abs_add_le _ _
      _ = |X| + |Y| := by rw [abs_neg]
  calc |(heatSemigroupND t (fun y => F (f y)) a - heatSemigroupND t (fun y => F (f y)) b)
        - (F (heatSemigroupND t f a) - F (heatSemigroupND t f b))|
      ≤ |heatSemigroupND t (fun y => F (f y)) a - heatSemigroupND t (fun y => F (f y)) b|
        + |F (heatSemigroupND t f a) - F (heatSemigroupND t f b)| :=
          htri _ _
    _ ≤ L_F * H * ∑ j : Fin n, |(a - b) j| ^ α
        + L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by
          apply add_le_add h1 h2
    _ = 2 * L_F * H * ∑ j : Fin n, |(a - b) j| ^ α := by ring
    _ = 2 * (|F' 0| + (M : ℝ) * C) * H * ∑ j : Fin n, |(a - b) j| ^ α := by rw [hL_F]

/-! ## 4. Resolution of the measurability technicality -/

/-
**Resolved:** The heat semigroup Hölder preservation for raw functions is now
proved as `isHolderConst_heatSemigroupND_raw` (Section 2 above).

The measurability technicality is resolved via `TranslationMeasurability`:
`aestronglyMeasurable_comp_sub_left` gives
`AEStronglyMeasurable (fun z => f (x - z))` from `AEStronglyMeasurable f`,
using that `z ↦ x - z` is measure-preserving for `volume`
(via Haar regularity for negation and translation-invariance for shifts).

**Sup-norm vanishing** (already available):
- `commutator_taylor_pointwise` gives `|C(t,x)| ≤ O(t^α)`, so `‖C(t,·)‖∞ → 0`.
-/

end AnalyticPDE
end RicciFlow
