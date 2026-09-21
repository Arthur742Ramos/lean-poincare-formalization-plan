import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TaylorCommutatorPointwise
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HolderHeatSemigroupRestriction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel

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

## Status and honest limitations

**Proved here** (genuine, no sorry):
- `abs_deriv_le_of_lipschitz_deriv_on_Icc`: Bound on `|F'|` over `Icc (-C) C`.
- `abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc`: `F` is Lipschitz on
  `Icc (-C) C` with constant `|F'(0)| + M*C`, via the mean value theorem.
  This is the key estimate needed for Hölder composition with `C^{1,1}`
  nonlinearities.

**Not proved here** (documented gaps):
- The heat semigroup Hölder preservation for raw functions (blocked on a
  measurability technicality; see Section 2).
- The full commutator Hölder bound `isHolderConst_commutator_taylor`.
- The sharp vanishing Hölder-seminorm rate.
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

/-! ## 2. Status of Hölder preservation -/

/-
**Technical blocker documented here (honest, not hidden):**

The heat semigroup Hölder preservation for raw functions
(`holder_estimate_heatSemigroupND`) requires proving
`AEStronglyMeasurable (fun z => f (x - z))` from `AEStronglyMeasurable f`.

The mathematical proof is straightforward (translation preserves null sets),
but the Lean formalization hits a technical obstruction: `AEStronglyMeasurable`
is defined as `∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g`, and precomposing the
`∀ᵐ` equality with the translation map requires a measure-preservation lemma
that is not immediately available in the needed form.

**What IS proved** (in this file):
- `abs_deriv_le_of_lipschitz_deriv_on_Icc`: Bound on `|F'|` over `Icc (-C) C`.
- `abs_sub_le_of_hasDerivAt_lipschitz_deriv_on_Icc`: `F` is Lipschitz on
  `Icc (-C) C` with constant `|F'(0)| + M*C`, via the mean value theorem.

**What remains** (for a future worker):
- The Hölder preservation `|S(t)f(a) - S(t)f(b)| ≤ H * ∑ |(a-b) j|^α`.
  The BCF version (`isHolderConst_heatSemigroupNDbcf`) is already proved;
  the raw-function version needs the measurability lemma above.
- Once preservation is available, the commutator Hölder bound follows by:
  1. `F∘f` Hölder with `L_F * H` (using the Lipschitz bound proved here).
  2. `S(t)(F∘f)` Hölder with `L_F * H` (preservation).
  3. `F(S(t)f)` Hölder with `L_F * H` (preservation + composition).
  4. Commutator Hölder with `2 * L_F * H` (triangle inequality).

**Sup-norm vanishing** (already available):
- `commutator_taylor_pointwise` gives `|C(t,x)| ≤ O(t^α)`, so `‖C(t,·)‖∞ → 0`.
-/

end AnalyticPDE
end RicciFlow
