import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
import Mathlib.Analysis.MeanInequalities

/-!
# Parabolic Hölder AM–GM (Young) interpolation (roadmap point 4, Item 3)

`AnalyticPDE/ParabolicHolder.lean` proves the multiplicative interpolation inequality
`parabolicHolderWith_interpolation`:

  `[u]_{α θ} ≤ (2 · sup)^{1 − θ} · [u]_α^θ`.

This module refines that multiplicative bound into the **additive (Young / weighted arithmetic–
geometric mean) form** that parabolic Schauder estimates use to *absorb lower-order terms*.  Applying
the weighted AM–GM inequality `p₁^{w₁} · p₂^{w₂} ≤ w₁ p₁ + w₂ p₂` (with weights `w₁ = 1 − θ`,
`w₂ = θ`) to the two interpolation factors turns the product into a convex combination:

  `[u]_{α θ} ≤ (1 − θ) · (2 · sup) + θ · [u]_α`,

and — genuinely load-bearing for the fixed point — with a free scaling parameter `κ > 0`, the
*absorbing* form

  `[u]_{α θ} ≤ (1 − θ) · κ^{−θ/(1−θ)} · (2 · sup) + θ κ · [u]_α`,

whose coefficient `θ κ` on the top seminorm `[u]_α` can be made arbitrarily small at the cost of a
large multiple of the sup norm — exactly the mechanism that lets an intermediate parabolic Hölder
seminorm be swallowed by a small fraction of the leading seminorm plus a controlled `C^0` remainder.

This is a leaf module (nothing in the project imports it yet): the only heavy dependency is
`Mathlib.Analysis.MeanInequalities`, kept out of the widely-imported `ParabolicHolder` file so that
adding it does not trigger a rebuild of the downstream parabolic function-space tower.

* `parabolicHolderWith_interpolation_add` / `_le` — the additive and uniform (`≤ 2·sup + [u]_α`)
  interpolation constants at the `ParabolicHolderWith` level.
* `parabolicHolderSeminorm_interpolation_add_le` — the additive interpolation at the seminorm-
  functional level.
* `parabolicHolderWith_interpolation_absorb` / `parabolicHolderSeminorm_interpolation_absorb_le` —
  the `κ`-scaled *absorbing* form and its seminorm functional.

All proofs are pure norm/rpow/AM–GM algebra; no Schauder or heat-kernel content.  Axiom-clean
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

set_option linter.unusedSectionVars false

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]

/-- **Scalar weighted-AM–GM absorbing inequality.**  For nonnegative `a, b`, weight `0 ≤ θ < 1`, and
a free scaling parameter `κ > 0`,
`a^{1−θ} · b^θ ≤ (1 − θ) · κ^{−θ/(1−θ)} · a + θ · κ · b`.
Obtained from the weighted AM–GM inequality applied to the rescaled values
`p₁ = κ^{−θ/(1−θ)} · a` and `p₂ = κ · b` (weights `1 − θ`, `θ`), whose weighted geometric mean is
exactly `a^{1−θ} b^θ`.  The `θ κ` coefficient on `b` is the tunable one. -/
theorem rpow_mul_rpow_le_absorb {a b θ κ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ) :
    a ^ (1 - θ) * b ^ θ ≤ (1 - θ) * (κ ^ (-(θ / (1 - θ))) * a) + θ * (κ * b) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hp1nn : 0 ≤ κ ^ (-(θ / (1 - θ))) * a := mul_nonneg (Real.rpow_nonneg hκ.le _) ha
  have hp2nn : 0 ≤ κ * b := mul_nonneg hκ.le hb
  have hkey : (κ ^ (-(θ / (1 - θ))) * a) ^ (1 - θ) * (κ * b) ^ θ = a ^ (1 - θ) * b ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _) ha, Real.mul_rpow hκ.le hb,
      ← Real.rpow_mul hκ.le]
    have he : (-(θ / (1 - θ))) * (1 - θ) = -θ := by
      field_simp
    rw [he,
      show κ ^ (-θ) * a ^ (1 - θ) * (κ ^ θ * b ^ θ)
          = κ ^ (-θ) * κ ^ θ * (a ^ (1 - θ) * b ^ θ) by ring,
      ← Real.rpow_add hκ, show (-θ) + θ = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
  have hAMGM := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - θ)
    hθ0 hp1nn hp2nn (by ring : (1 - θ) + θ = 1)
  rw [hkey] at hAMGM
  exact hAMGM

/-- **Parabolic Hölder interpolation, additive (Young) form.**  A parabolically bounded (`B`) and
`α`-Hölder (`H`) function is, for every weight `0 ≤ θ ≤ 1`, parabolic Hölder with the intermediate
exponent `α · θ` and the *convex-combination* constant `(1 − θ) · (2 · B) + θ · H`.  The additive
form of `parabolicHolderWith_interpolation`, obtained by dominating the multiplicative constant
`(2B)^{1−θ} H^θ` through the weighted AM–GM inequality. -/
theorem parabolicHolderWith_interpolation_add
    {B H α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith ((1 - θ) * (2 * B) + θ * H) (α * θ) u s := by
  have hamgm : (2 * B) ^ (1 - θ) * H ^ θ ≤ (1 - θ) * (2 * B) + θ * H :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) hθ0 (by linarith) hH0 (by ring)
  exact (parabolicHolderWith_interpolation hB0 hH0 hθ0 hθ1 hbdd hhol).mono_const hamgm

/-- **Uniform interpolation constant.**  The convex-combination constant of
`parabolicHolderWith_interpolation_add` is bounded by the uniform value `2 · B + H`. -/
theorem parabolicHolderWith_interpolation_add_le
    {B H α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith (2 * B + H) (α * θ) u s := by
  refine (parabolicHolderWith_interpolation_add hB0 hH0 hθ0 hθ1 hbdd hhol).mono_const ?_
  have h1 : (1 - θ) * (2 * B) ≤ 2 * B := by nlinarith
  have h2 : θ * H ≤ H := by nlinarith
  linarith

/-- **Parabolic Hölder interpolation, absorbing form.**  For a parabolically bounded (`B`) and
`α`-Hölder (`H`) function, every weight `0 ≤ θ < 1`, and every scaling parameter `κ > 0`, the
intermediate `α · θ`-Hölder control holds with the *absorbing* constant
`(1 − θ) · κ^{−θ/(1−θ)} · (2 · B) + θ κ · H`, whose `θ κ` coefficient on `H` is tunable to any
target. -/
theorem parabolicHolderWith_interpolation_absorb
    {B H α θ κ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith
      ((1 - θ) * (κ ^ (-(θ / (1 - θ))) * (2 * B)) + θ * (κ * H)) (α * θ) u s := by
  refine (parabolicHolderWith_interpolation hB0 hH0 hθ0 (le_of_lt hθ1) hbdd hhol).mono_const ?_
  exact rpow_mul_rpow_le_absorb (by linarith) hH0 hθ0 hθ1 hκ

/-- **Additive interpolation at the seminorm level.**  For a function in the parabolic `C^{0,α}`
class and every weight `0 ≤ θ ≤ 1`,
`[u]_{α θ} ≤ (1 − θ) · (2 · ‖u‖_{C^0}) + θ · [u]_α`. -/
theorem parabolicHolderSeminorm_interpolation_add_le
    {α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicC0AlphaOn α u s) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ (1 - θ) * (2 * parabolicSupNorm u s) + θ * parabolicHolderSeminorm α u s := by
  obtain ⟨hbdd, hhol⟩ :=
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu
  refine parabolicHolderSeminorm_le ?_ ?_
  · exact add_nonneg
      (mul_nonneg (by linarith)
        (by have := parabolicSupNorm_nonneg u s; linarith))
      (mul_nonneg hθ0 (parabolicHolderSeminorm_nonneg α u s))
  · exact parabolicHolderWith_interpolation_add (parabolicSupNorm_nonneg u s)
      (parabolicHolderSeminorm_nonneg α u s) hθ0 hθ1 hbdd hhol

/-- **Absorbing interpolation at the seminorm level.**  For a function in the parabolic `C^{0,α}`
class, every weight `0 ≤ θ < 1`, and every `κ > 0`,
`[u]_{α θ} ≤ (1 − θ) · κ^{−θ/(1−θ)} · (2 · ‖u‖_{C^0}) + θ κ · [u]_α`.  The functional form of the
absorbing interpolation. -/
theorem parabolicHolderSeminorm_interpolation_absorb_le
    {α θ κ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hu : ParabolicC0AlphaOn α u s) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ (1 - θ) * (κ ^ (-(θ / (1 - θ))) * (2 * parabolicSupNorm u s))
        + θ * (κ * parabolicHolderSeminorm α u s) := by
  obtain ⟨hbdd, hhol⟩ :=
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu
  refine parabolicHolderSeminorm_le ?_ ?_
  · exact add_nonneg
      (mul_nonneg (by linarith)
        (mul_nonneg (Real.rpow_nonneg hκ.le _)
          (by have := parabolicSupNorm_nonneg u s; linarith)))
      (mul_nonneg hθ0 (mul_nonneg hκ.le (parabolicHolderSeminorm_nonneg α u s)))
  · exact parabolicHolderWith_interpolation_absorb (parabolicSupNorm_nonneg u s)
      (parabolicHolderSeminorm_nonneg α u s) hθ0 hθ1 hκ hbdd hhol

/-- **Short-time smallness of the intermediate Hölder seminorm.**  If `u` is parabolic `α`-Hölder on
`s`, every time-coordinate of `s` lies within `T` of the initial time `t₀`, `s` is closed under
dropping to the initial-time slice, and `u` vanishes on that slice, then for every weight
`0 ≤ θ ≤ 1` the intermediate `α · θ`-Hölder seminorm is a *small* multiple of the leading
`α`-seminorm:

  `[u]_{α θ} ≤ 2^{1−θ} · (√T)^{α (1−θ)} · [u]_α`.

Since `(√T)^{α (1−θ)} = T^{α (1−θ)/2} → 0` as the slab thickness `T → 0`, the intermediate seminorm
is dominated by an arbitrarily small fraction of the top seminorm on a thin time-slab — the
mechanism by which the Ricci–DeTurck solution map contracts in the *intermediate* seminorms too, not
merely the sup norm.  Obtained by feeding the initial-vanishing sup bound
`parabolicSupNorm ≤ [u]_α · (√T)^α` into the multiplicative interpolation
`parabolicHolderSeminorm_interpolation_le`. -/
theorem parabolicHolderSeminorm_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicHolderOn α u s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hu0 : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = 0) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s := by
  have hH0 : 0 ≤ parabolicHolderSeminorm α u s := parabolicHolderSeminorm_nonneg α u s
  have hsqrt0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hrpow0 : 0 ≤ Real.sqrt T ^ α := Real.rpow_nonneg hsqrt0 α
  have hne : (1 - θ) + θ ≠ 0 := by rw [show (1 - θ) + θ = 1 by ring]; norm_num
  have hhol : ParabolicHolderWith (parabolicHolderSeminorm α u s) α u s :=
    parabolicHolderWith_parabolicHolderSeminorm hu
  have hbdd : ParabolicBoundedWith (parabolicHolderSeminorm α u s * Real.sqrt T ^ α) u s := by
    rintro ⟨t, x⟩ hp
    have hp0 : (t₀, x) ∈ s := hcyl (t, x) hp
    exact norm_le_of_parabolicHolderWith_of_initial_zero hH0 hα hhol hp hp0
      (hu0 x hp0) (hslab (t, x) hp)
  have hCOA : ParabolicC0AlphaOn α u s :=
    ⟨parabolicHolderSeminorm α u s * Real.sqrt T ^ α, mul_nonneg hH0 hrpow0,
      parabolicHolderSeminorm α u s, hH0, hbdd, hhol⟩
  have hst : parabolicSupNorm u s ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α :=
    parabolicSupNorm_le_holderSeminorm_mul_of_initial_zero hα hu hslab hcyl hu0
  have hinterp := parabolicHolderSeminorm_interpolation_le hθ0 hθ1 hCOA
  refine hinterp.trans ?_
  have e1 : (2 * (parabolicHolderSeminorm α u s * Real.sqrt T ^ α)) ^ (1 - θ)
      = 2 ^ (1 - θ) * parabolicHolderSeminorm α u s ^ (1 - θ)
        * Real.sqrt T ^ (α * (1 - θ)) := by
    rw [Real.mul_rpow (by norm_num) (mul_nonneg hH0 hrpow0), Real.mul_rpow hH0 hrpow0,
        ← Real.rpow_mul hsqrt0]
    ring
  have e2 : parabolicHolderSeminorm α u s ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ
      = parabolicHolderSeminorm α u s := by
    rw [← Real.rpow_add' hH0 hne, show (1 - θ) + θ = 1 by ring, Real.rpow_one]
  calc (2 * parabolicSupNorm u s) ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ
      ≤ (2 * (parabolicHolderSeminorm α u s * Real.sqrt T ^ α)) ^ (1 - θ)
          * parabolicHolderSeminorm α u s ^ θ := by
        apply mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by have := parabolicSupNorm_nonneg u s; linarith)
            (by linarith [hst]) (by linarith)) (Real.rpow_nonneg hH0 θ)
    _ = 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ))
          * (parabolicHolderSeminorm α u s ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ) := by
        rw [e1]; ring
    _ = 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s := by rw [e2]

/-- **Short-time smallness of the full intermediate `C^{0,α θ}` norm.**  For an initial-vanishing,
`α`-Hölder function on a thin time-slab, the *full* intermediate parabolic `C^{0,α θ}` norm is
controlled by a short-time-small multiple of the leading `α`-seminorm:

  `‖u‖_{C^{0,α θ}} ≤ ((√T)^α + 2^{1−θ} (√T)^{α (1−θ)}) · [u]_α`.

Both terms of the factor carry a positive power of the slab thickness `T`, so the whole intermediate
norm `→ 0` as `T → 0`.  Sum of the initial-vanishing sup bound and the intermediate-seminorm bound
`parabolicHolderSeminorm_interpolation_short_time_le`. -/
theorem parabolicC0AlphaNorm_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicHolderOn α u s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hu0 : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = 0) :
    parabolicC0AlphaNorm (α * θ) u s
      ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α u s := by
  have hsup : parabolicSupNorm u s ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α :=
    parabolicSupNorm_le_holderSeminorm_mul_of_initial_zero hα hu hslab hcyl hu0
  have hsemi : parabolicHolderSeminorm (α * θ) u s
      ≤ 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s :=
    parabolicHolderSeminorm_interpolation_short_time_le hα hθ0 hθ1 hu hslab hcyl hu0
  unfold parabolicC0AlphaNorm
  calc parabolicSupNorm u s + parabolicHolderSeminorm (α * θ) u s
      ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α
        + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s :=
        add_le_add hsup hsemi
    _ = (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α u s := by ring

/-- **Short-time intermediate `C^{0,α θ}` contraction for a difference (initial-agreement form).**
The form the Ricci–DeTurck fixed point consumes: if `u` and `v` agree on the initial-time slice and
their difference is `α`-Hölder on a thin slab, then the intermediate `C^{0,α θ}` norm of the
difference is short-time small relative to its own leading `α`-seminorm:

  `‖u − v‖_{C^{0,α θ}} ≤ ((√T)^α + 2^{1−θ} (√T)^{α (1−θ)}) · [u − v]_α`.

Immediate from `parabolicC0AlphaNorm_interpolation_short_time_le` applied to `u − v`, which vanishes
on the initial slice by agreement.  As `T → 0` the factor `→ 0`, so on a sufficiently thin time-slab
the map `u ↦ (solution)` is a contraction in the intermediate norm. -/
theorem parabolicC0AlphaNorm_sub_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u v : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (huv : ParabolicHolderOn α (fun z => u z - v z) s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hagree : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = v (t₀, x)) :
    parabolicC0AlphaNorm (α * θ) (fun z => u z - v z) s
      ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α (fun z => u z - v z) s := by
  refine parabolicC0AlphaNorm_interpolation_short_time_le hα hθ0 hθ1 huv hslab hcyl ?_
  intro x hx
  exact sub_eq_zero.mpr (hagree x hx)

end AnalyticPDE
end RicciFlow
