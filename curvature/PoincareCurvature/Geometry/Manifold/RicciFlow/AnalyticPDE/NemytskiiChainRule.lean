import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorialCommutator

/-!
# Nemytskii chain rule for the Ricci–DeTurck nonlinearity (Point 4 PDE milestone)

## Mathematical context

The genuine Ricci–DeTurck nonlinearity has the form
  `N_RD(g)(x) = Φ(j²g(x))`
where `j²g(x)` is the 2-jet of the metric and `Φ` is a smooth fiber map
(the Ricci–DeTurck remainder after the heat principal part is absorbed).
This file proves the **chain rule in Hölder spaces**: composition with a `C¹`
fiber map preserves Hölder regularity, with an explicit locally-Lipschitz
dependence on the base function.

## Results proved here (genuine, no sorry)

1. **`fderiv_sub_eq_integral`**: integral representation of a `C¹` difference
   on a convex set,
     `Φ p - Φ q = ∫₀¹ Φ'(lineMap q p t) (p - q) dt`.
2. **`fderiv_comp_sub_le`**: pointwise difference estimate
     `‖(Φ a - Φ b) - (Φ c - Φ d)‖`
       `≤ L * max ‖a-c‖ ‖b-d‖ * ‖a-b‖ + B * ‖(a-c) - (b-d)‖`
   when `Φ'` is `L`-Lipschitz and `‖Φ'‖ ≤ B` on a convex set.
3. **`isHolderNorm_comp`**: Hölder preservation — `Φ ∘ u` is Hölder.
4. **`isHolderNorm_comp_sub`**: Hölder difference estimate —
   `Φ ∘ u - Φ ∘ v` is Hölder with constant controlled by `‖u - v‖`.
5. **`NemytskiiData`** + **`isHolderNorm_nemytskii_sub_coarse`**: the Nemytskii
   operator `u ↦ Φ ∘ u`; a coarse Hölder estimate for differences
   (the sharp form is `isHolderNorm_comp_sub` with separate `H₁`).
6. **`Jet2` normed space**: the 2-jet fiber `Jet2 n d` is a `NormedSpace ℝ`,
   via a sum-of-entries matrix norm, making it a valid Nemytskii fiber.
7. **`Jet2NemytskiiData`**: the Nemytskii machine specialized to 2-jet
   fibers, i.e. operators of the form `(N u) x = Φ (j²u x)`.

## Honest limitations

- The fiber map `Φ` is abstract `C¹` data (not the explicit Ricci formula).
  The genuine Ricci–DeTurck `Φ` (a smooth function of the 2-jet built from
  the actual Ricci curvature) is future work; this file provides the exact
  analytic machine it will plug into.
- The 2-jet extraction `g ↦ j²g` from a genuine `C^{2,α}` space is not built
  here. The theorems are stated fiber-generally, so they apply verbatim once
  a Hölder jet-extraction map is available (see `ricciDeTurckNemytskii`).
- Little-Hölder (`IsGoodHolder`) preservation under nonlinear composition
  needs the heat-semigroup commutator and is not addressed here.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal Interval

/-! ## 1. Integral representation of a C¹ difference -/

section IntegralRepresentation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Integral representation of a `C¹` difference on a convex set.**

For `Φ` differentiable within the convex set `K` with derivative `Φ'`
continuous on `K`, and `p q ∈ K`:
  `Φ p - Φ q = ∫₀¹ Φ'(lineMap q p t) (p - q) dt`.

Proof: apply the fundamental theorem of calculus to `γ = Φ ∘ lineMap q p`
on `[0,1]`, using the chain rule within `K`. -/
theorem fderiv_sub_eq_integral
    {Φ : E → F} {Φ' : E → E →L[ℝ] F} {K : Set E}
    (hconv : Convex ℝ K)
    (hderiv : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    (hcont : ContinuousOn Φ' K)
    {p q : E} (hp : p ∈ K) (hq : q ∈ K) :
    Φ p - Φ q = ∫ t in (0:ℝ)..1, Φ' (AffineMap.lineMap q p t) (p - q) := by
  set g : ℝ → E := fun t => AffineMap.lineMap q p t with hg
  have segm : MapsTo g (Icc (0:ℝ) 1) K := hconv.mapsTo_lineMap hq hp
  -- Derivative of the composition `Φ ∘ g` within `[0,1]`.
  have hD : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (Φ ∘ g) (Φ' (g t) (p - q)) (Icc (0:ℝ) 1) t :=
    fun t ht => (hderiv (g t) (segm ht)).comp_hasDerivWithinAt t
      AffineMap.hasDerivWithinAt_lineMap segm
  -- Continuity of `Φ ∘ g` on `[0,1]`.
  have hΦcont : ContinuousOn Φ K :=
    fun x hx => (hderiv x hx).continuousWithinAt
  have hgcont : Continuous g := by
    have hform : ∀ t : ℝ, g t = t • (p - q) + q := by
      intro t
      simp [hg, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have : Continuous (fun t : ℝ => t • (p - q) + q) :=
      (continuous_id.smul continuous_const).add continuous_const
    exact this.congr (fun t => (hform t).symm)
  have hcomp_cont : ContinuousOn (Φ ∘ g) (Icc (0:ℝ) 1) :=
    hΦcont.comp hgcont.continuousOn segm
  -- Integrability of the derivative integrand.
  have hΦ'_comp : ContinuousOn (fun t : ℝ => Φ' (g t)) (Icc (0:ℝ) 1) :=
    hcont.comp hgcont.continuousOn segm
  have hint : IntervalIntegrable (fun t : ℝ => Φ' (g t) (p - q)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hΦ'_comp.clm_apply continuousOn_const
  -- Fundamental theorem of calculus.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) hcomp_cont
    (fun t ht => ((hD t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)))
    hint
  -- Identify the endpoints `g 1 = p`, `g 0 = q`.
  have hg1 : (Φ ∘ g) 1 = Φ p := by
    simp [Function.comp_apply, hg, AffineMap.lineMap_apply_one]
  have hg0 : (Φ ∘ g) 0 = Φ q := by
    simp [Function.comp_apply, hg, AffineMap.lineMap_apply_zero]
  rw [hg1, hg0] at hFTC
  exact hFTC.symm

end IntegralRepresentation

/-! ## 2. Pointwise difference estimate -/

section DifferenceEstimate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Auxiliary: the segment difference is controlled by the endpoint maxima. -/
theorem norm_lineMap_sub_lineMap_le {a b c d : E} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖AffineMap.lineMap b a t - AffineMap.lineMap d c t‖ ≤
      max ‖a - c‖ ‖b - d‖ := by
  have hform : ∀ (p₀ p₁ : E) (s : ℝ),
      AffineMap.lineMap p₀ p₁ s = s • (p₁ - p₀) + p₀ := by
    intro p₀ p₁ s
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [hform b a t, hform d c t]
  have hdecomp : (t • (a - b) + b) - (t • (c - d) + d)
      = (1 - t) • (b - d) + t • (a - c) := by
    module
  rw [hdecomp]
  have h1 : (0:ℝ) ≤ 1 - t := by linarith
  calc ‖(1 - t) • (b - d) + t • (a - c)‖
      ≤ ‖(1 - t) • (b - d)‖ + ‖t • (a - c)‖ := norm_add_le _ _
    _ = (1 - t) * ‖b - d‖ + t * ‖a - c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1, abs_of_nonneg ht0]
    _ ≤ (1 - t) * max ‖a - c‖ ‖b - d‖ + t * max ‖a - c‖ ‖b - d‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) h1
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) ht0
    _ = max ‖a - c‖ ‖b - d‖ := by ring

/-- **Pointwise difference estimate for `C¹` maps with Lipschitz derivative.**

If `Φ'` is `L`-Lipschitz and `‖Φ'‖ ≤ B` on the convex set `K`, then for
`a b c d ∈ K`:
  `‖(Φ a - Φ b) - (Φ c - Φ d)‖`
    `≤ L * max ‖a-c‖ ‖b-d‖ * ‖a-b‖ + B * ‖(a-c) - (b-d)‖`.

Proof: subtract the two integral representations and estimate the integrand
using the Lipschitz bound on `Φ'` and the bound `B`. -/
theorem fderiv_comp_sub_le
    {Φ : E → F} {Φ' : E → E →L[ℝ] F} {K : Set E}
    (hconv : Convex ℝ K)
    (hderiv : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    {B : ℝ} (hB : ∀ x ∈ K, ‖Φ' x‖ ≤ B)
    {L : ℝ≥0} (hL : LipschitzOnWith L Φ' K)
    {a b c d : E} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) :
    ‖(Φ a - Φ b) - (Φ c - Φ d)‖ ≤
      (L : ℝ) * max ‖a - c‖ ‖b - d‖ * ‖a - b‖ + B * ‖(a - c) - (b - d)‖ := by
  have hcont : ContinuousOn Φ' K := hL.continuousOn
  -- The two integral representations.
  have h1 : Φ a - Φ b
      = ∫ t in (0:ℝ)..1, Φ' (AffineMap.lineMap b a t) (a - b) :=
    fderiv_sub_eq_integral hconv hderiv hcont ha hb
  have h2 : Φ c - Φ d
      = ∫ t in (0:ℝ)..1, Φ' (AffineMap.lineMap d c t) (c - d) :=
    fderiv_sub_eq_integral hconv hderiv hcont hc hd
  -- Integrability of both integrands.
  have segm1 : MapsTo (fun t : ℝ => AffineMap.lineMap b a t) (Icc (0:ℝ) 1) K :=
    hconv.mapsTo_lineMap hb ha
  have segm2 : MapsTo (fun t : ℝ => AffineMap.lineMap d c t) (Icc (0:ℝ) 1) K :=
    hconv.mapsTo_lineMap hd hc
  have hgcont1 : Continuous (fun t : ℝ => AffineMap.lineMap b a t) := by
    have hform : ∀ t : ℝ, AffineMap.lineMap b a t = t • (a - b) + b := by
      intro t
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have : Continuous (fun t : ℝ => t • (a - b) + b) :=
      (continuous_id.smul continuous_const).add continuous_const
    exact this.congr (fun t => (hform t).symm)
  have hgcont2 : Continuous (fun t : ℝ => AffineMap.lineMap d c t) := by
    have hform : ∀ t : ℝ, AffineMap.lineMap d c t = t • (c - d) + d := by
      intro t
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have : Continuous (fun t : ℝ => t • (c - d) + d) :=
      (continuous_id.smul continuous_const).add continuous_const
    exact this.congr (fun t => (hform t).symm)
  have hint1 : IntervalIntegrable
      (fun t : ℝ => Φ' (AffineMap.lineMap b a t) (a - b)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (hcont.comp hgcont1.continuousOn segm1).clm_apply continuousOn_const
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Φ' (AffineMap.lineMap d c t) (c - d)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (hcont.comp hgcont2.continuousOn segm2).clm_apply continuousOn_const
  -- Subtract the representations.
  have hInt : (Φ a - Φ b) - (Φ c - Φ d)
      = ∫ t in (0:ℝ)..1,
        (Φ' (AffineMap.lineMap b a t) (a - b) - Φ' (AffineMap.lineMap d c t) (c - d)) := by
    rw [h1, h2, ← intervalIntegral.integral_sub hint1 hint2]
  -- Pointwise integrand bound.
  have hpoint : ∀ t ∈ Icc (0:ℝ) 1,
      ‖Φ' (AffineMap.lineMap b a t) (a - b) - Φ' (AffineMap.lineMap d c t) (c - d)‖ ≤
        (L : ℝ) * max ‖a - c‖ ‖b - d‖ * ‖a - b‖ + B * ‖(a - c) - (b - d)‖ := by
    intro t ht
    have hmem1 : AffineMap.lineMap b a t ∈ K := segm1 ht
    have hmem2 : AffineMap.lineMap d c t ∈ K := segm2 ht
    have hseg : ‖AffineMap.lineMap b a t - AffineMap.lineMap d c t‖ ≤
        max ‖a - c‖ ‖b - d‖ :=
      norm_lineMap_sub_lineMap_le ht.1 ht.2
    -- Lipschitz bound on the derivative difference.
    have hLip := hL.dist_le_mul _ hmem1 _ hmem2
    rw [dist_eq_norm, dist_eq_norm] at hLip
    -- Decompose the integrand.
    have hdecomp : Φ' (AffineMap.lineMap b a t) (a - b)
          - Φ' (AffineMap.lineMap d c t) (c - d)
        = (Φ' (AffineMap.lineMap b a t) - Φ' (AffineMap.lineMap d c t)) (a - b)
          + Φ' (AffineMap.lineMap d c t) ((a - b) - (c - d)) := by
      simp only [sub_apply, map_sub]
      abel
    have hnorm1 : ‖(Φ' (AffineMap.lineMap b a t) - Φ' (AffineMap.lineMap d c t)) (a - b)‖ ≤
        (L : ℝ) * max ‖a - c‖ ‖b - d‖ * ‖a - b‖ := by
      calc ‖(Φ' (AffineMap.lineMap b a t) - Φ' (AffineMap.lineMap d c t)) (a - b)‖
          ≤ ‖Φ' (AffineMap.lineMap b a t) - Φ' (AffineMap.lineMap d c t)‖ * ‖a - b‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((L : ℝ) * ‖AffineMap.lineMap b a t - AffineMap.lineMap d c t‖) * ‖a - b‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            -- `hLip : ‖Φ'(σ₁) - Φ'(σ₂)‖ ≤ ↑L * ‖σ₁ - σ₂‖`
            have hLr : ((L : ℝ≥0) : ℝ) = (L : ℝ) := rfl
            rw [hLr] at hLip
            exact hLip
        _ ≤ ((L : ℝ) * max ‖a - c‖ ‖b - d‖) * ‖a - b‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hseg (NNReal.coe_nonneg L)
    have hnorm2 : ‖Φ' (AffineMap.lineMap d c t) ((a - b) - (c - d))‖ ≤
        B * ‖(a - c) - (b - d)‖ := by
      have h1 : ‖Φ' (AffineMap.lineMap d c t) ((a - b) - (c - d))‖ ≤
          ‖Φ' (AffineMap.lineMap d c t)‖ * ‖(a - b) - (c - d)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h2 : ‖(a - b) - (c - d)‖ = ‖(a - c) - (b - d)‖ := by
        congr 1
        module
      rw [h2] at h1
      calc ‖Φ' (AffineMap.lineMap d c t) ((a - b) - (c - d))‖
          ≤ ‖Φ' (AffineMap.lineMap d c t)‖ * ‖(a - c) - (b - d)‖ := h1
        _ ≤ B * ‖(a - c) - (b - d)‖ :=
            mul_le_mul_of_nonneg_right (hB _ hmem2) (norm_nonneg _)
    rw [hdecomp]
    exact le_trans (norm_add_le _ _) (add_le_add hnorm1 hnorm2)
  -- Integrate the pointwise bound.
  rw [hInt]
  have hint_norm : IntervalIntegrable
      (fun t : ℝ => ‖Φ' (AffineMap.lineMap b a t) (a - b)
        - Φ' (AffineMap.lineMap d c t) (c - d)‖) volume (0:ℝ) 1 :=
    (hint1.sub hint2).norm
  calc ‖∫ t in (0:ℝ)..1,
        (Φ' (AffineMap.lineMap b a t) (a - b) - Φ' (AffineMap.lineMap d c t) (c - d))‖
      ≤ ∫ t in (0:ℝ)..1,
        ‖Φ' (AffineMap.lineMap b a t) (a - b) - Φ' (AffineMap.lineMap d c t) (c - d)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _ in (0:ℝ)..1,
        ((L : ℝ) * max ‖a - c‖ ‖b - d‖ * ‖a - b‖ + B * ‖(a - c) - (b - d)‖) :=
        intervalIntegral.integral_mono_on (by norm_num) hint_norm
          intervalIntegrable_const hpoint
    _ = (L : ℝ) * max ‖a - c‖ ‖b - d‖ * ‖a - b‖ + B * ‖(a - c) - (b - d)‖ := by
        rw [intervalIntegral.integral_const]
        simp

end DifferenceEstimate
/-! ## 3. Hölder predicate, preservation, and difference estimate -/

section HolderNemytskii

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Hölder estimate with explicit constant, using the `∑ |xⱼ - yⱼ|^α` modulus.
This matches the `TensorialCommutator.IsHolderConstMatrix` convention
(componentwise, uniform constant), but for general normed fibers. -/
def IsHolderNorm {n : ℕ} (α : ℝ) (u : (Fin n → ℝ) → E) (H : ℝ) : Prop :=
  0 ≤ H ∧ ∀ x y : Fin n → ℝ, ‖u x - u y‖ ≤ H * ∑ j : Fin n, |(x - y) j| ^ α

/-- Difference of Hölder maps is Hölder (constant doubles). -/
theorem IsHolderNorm.sub {n : ℕ} {α H₀ : ℝ} {u v : (Fin n → ℝ) → E}
    (hu : IsHolderNorm α u H₀) (hv : IsHolderNorm α v H₀) :
    IsHolderNorm α (fun x => u x - v x) (H₀ + H₀) := by
  refine ⟨add_nonneg hu.1 hu.1, fun x y => ?_⟩
  have h1 := hu.2 x y
  have h2 := hv.2 x y
  calc ‖(u x - v x) - (u y - v y)‖
      = ‖(u x - u y) - (v x - v y)‖ := by congr 1; abel
    _ ≤ ‖u x - u y‖ + ‖v x - v y‖ := norm_sub_le _ _
    _ ≤ H₀ * ∑ j : Fin n, |(x - y) j| ^ α + H₀ * ∑ j : Fin n, |(x - y) j| ^ α :=
        add_le_add h1 h2
    _ = (H₀ + H₀) * ∑ j : Fin n, |(x - y) j| ^ α := by ring

/-- **Hölder preservation under `C¹` postcomposition.**

If `Φ` is differentiable within the convex set `K` with `‖Φ'‖ ≤ B` there,
and `u` is Hölder with range in `K`, then `Φ ∘ u` is Hölder with constant
`B * H`. This is the chain rule in Hölder spaces. -/
theorem isHolderNorm_comp
    {Φ : E → F} {Φ' : E → E →L[ℝ] F} {K : Set E}
    (hconv : Convex ℝ K)
    (hderiv : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hB : ∀ x ∈ K, ‖Φ' x‖ ≤ B)
    {n : ℕ} {α H : ℝ} {u : (Fin n → ℝ) → E}
    (hu : IsHolderNorm α u H) (hrange : ∀ x, u x ∈ K) :
    IsHolderNorm α (fun x => Φ (u x)) (B * H) := by
  refine ⟨mul_nonneg hB_nonneg hu.1, fun x y => ?_⟩
  have hMVT := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hB
    (hrange x) (hrange y)
  show ‖Φ (u x) - Φ (u y)‖ ≤ (B * H) * ∑ j : Fin n, |(x - y) j| ^ α
  calc ‖Φ (u x) - Φ (u y)‖
      = ‖Φ (u y) - Φ (u x)‖ := norm_sub_rev _ _
    _ ≤ B * ‖u y - u x‖ := hMVT
    _ = B * ‖u x - u y‖ := by rw [norm_sub_rev]
    _ ≤ B * (H * ∑ j : Fin n, |(x - y) j| ^ α) :=
        mul_le_mul_of_nonneg_left (hu.2 x y) hB_nonneg
    _ = (B * H) * ∑ j : Fin n, |(x - y) j| ^ α := by ring

/-- **Hölder difference estimate for `C¹` postcomposition.**

If `Φ'` is `L`-Lipschitz and `‖Φ'‖ ≤ B` on the convex set `K`, and
`u, v` are Hölder with constant `H₀`, `u - v` is Hölder with constant `H₁`,
all with range in `K`, and `‖u - v‖ ≤ M` pointwise, then `Φ ∘ u - Φ ∘ v`
is Hölder with constant `L * H₀ * M + B * H₁`.

This is the quantitative chain rule that makes the Nemytskii operator
`u ↦ Φ ∘ u` locally Lipschitz in Hölder spaces: the constant is affine
in `M = ‖u - v‖∞`. -/
theorem isHolderNorm_comp_sub
    {Φ : E → F} {Φ' : E → E →L[ℝ] F} {K : Set E}
    (hconv : Convex ℝ K)
    (hderiv : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hB : ∀ x ∈ K, ‖Φ' x‖ ≤ B)
    {L : ℝ≥0} (hL : LipschitzOnWith L Φ' K)
    {n : ℕ} {α H₀ H₁ M : ℝ} {u v : (Fin n → ℝ) → E}
    (hu : IsHolderNorm α u H₀)
    (huv : IsHolderNorm α (fun x => u x - v x) H₁)
    (hrange_u : ∀ x, u x ∈ K) (hrange_v : ∀ x, v x ∈ K)
    (hM : ∀ x, ‖u x - v x‖ ≤ M) :
    IsHolderNorm α (fun x => Φ (u x) - Φ (v x))
      ((L : ℝ) * H₀ * M + B * H₁) := by
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨?_, fun x y => ?_⟩
  · apply add_nonneg
    · exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg L) hu.1) hM_nonneg
    · exact mul_nonneg hB_nonneg huv.1
  · show ‖(Φ (u x) - Φ (v x)) - (Φ (u y) - Φ (v y))‖ ≤
      ((L : ℝ) * H₀ * M + B * H₁) * ∑ j : Fin n, |(x - y) j| ^ α
    have hest := fderiv_comp_sub_le hconv hderiv hB hL
      (hrange_u x) (hrange_u y) (hrange_v x) (hrange_v y)
    set S : ℝ := ∑ j : Fin n, |(x - y) j| ^ α with hS
    have hS_nonneg : 0 ≤ S := by
      apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (abs_nonneg _) α
    have hmax : max ‖u x - v x‖ ‖u y - v y‖ ≤ M := max_le (hM x) (hM y)
    have hu_xy : ‖u x - u y‖ ≤ H₀ * S := hu.2 x y
    have huv_xy : ‖(u x - v x) - (u y - v y)‖ ≤ H₁ * S := huv.2 x y
    calc ‖(Φ (u x) - Φ (v x)) - (Φ (u y) - Φ (v y))‖
        = ‖(Φ (u x) - Φ (u y)) - (Φ (v x) - Φ (v y))‖ := by congr 1; abel
      _ ≤ (L : ℝ) * max ‖u x - v x‖ ‖u y - v y‖ * ‖u x - u y‖
            + B * ‖(u x - v x) - (u y - v y)‖ := hest
      _ ≤ (L : ℝ) * M * (H₀ * S) + B * (H₁ * S) := by
          apply add_le_add
          · calc (L : ℝ) * max ‖u x - v x‖ ‖u y - v y‖ * ‖u x - u y‖
                ≤ (L : ℝ) * M * ‖u x - u y‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  exact mul_le_mul_of_nonneg_left hmax (NNReal.coe_nonneg L)
              _ ≤ (L : ℝ) * M * (H₀ * S) :=
                  mul_le_mul_of_nonneg_left hu_xy
                    (mul_nonneg (NNReal.coe_nonneg L) hM_nonneg)
          · exact mul_le_mul_of_nonneg_left huv_xy hB_nonneg
      _ = ((L : ℝ) * H₀ * M + B * H₁) * S := by ring

end HolderNemytskii

/-! ## 4. The Nemytskii operator and its local Lipschitz property -/

section NemytskiiOperator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Data for a Nemytskii (postcomposition) operator on a convex fiber set.

Packages a `C¹` fiber map `Φ` with:
- `B`: uniform bound on `‖Φ'‖` over `K` (controls Hölder preservation),
- `L`: Lipschitz constant of `Φ'` over `K` (controls the difference estimate).

For the Ricci–DeTurck application, `E` is the 2-jet fiber `Jet2 n d`,
`F` is the space of symmetric 2-tensors, and `Φ` is the smooth remainder
after the heat principal part is absorbed. -/
structure NemytskiiData (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  Φ : E → F
  Φ' : E → E →L[ℝ] F
  K : Set E
  hconv : Convex ℝ K
  hderiv : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x
  B : ℝ
  hB_nonneg : 0 ≤ B
  hB : ∀ x ∈ K, ‖Φ' x‖ ≤ B
  L : ℝ≥0
  hL : LipschitzOnWith L Φ' K

/-- The Nemytskii operator: postcomposition `u ↦ Φ ∘ u`. -/
def NemytskiiData.nemytskii (D : NemytskiiData E F) {n : ℕ}
    (u : (Fin n → ℝ) → E) : (Fin n → ℝ) → F :=
  fun x => D.Φ (u x)

/-- The Nemytskii operator preserves Hölder regularity. -/
theorem NemytskiiData.isHolderNorm_nemytskii (D : NemytskiiData E F)
    {n : ℕ} {α H : ℝ} {u : (Fin n → ℝ) → E}
    (hu : IsHolderNorm α u H) (hrange : ∀ x, u x ∈ D.K) :
    IsHolderNorm α (D.nemytskii u) (D.B * H) :=
  isHolderNorm_comp D.hconv D.hderiv D.hB_nonneg D.hB hu hrange

/-- **Coarse Hölder estimate for the Nemytskii difference.**

The Hölder constant of `Φ ∘ u - Φ ∘ v` is bounded by
  `L * H₀ * M + B * (H₀ + H₀)`
where `M = ‖u - v‖∞`. This uses the coarse bound `H₀ + H₀` for the
Hölder constant of `u - v` (from `IsHolderNorm.sub`), so the constant
does *not* tend to zero with `u - v`: this is not a genuine
local-Lipschitz estimate in Hölder norm. The sharp form is
`isHolderNorm_comp_sub`, which takes a separate Hölder constant `H₁`
for `u - v`. A full local-Lipschitz theorem would require a Hölder
norm (sup + seminorm) on the section space, not yet formalized. -/
theorem NemytskiiData.isHolderNorm_nemytskii_sub_coarse (D : NemytskiiData E F)
    {n : ℕ} {α H₀ M : ℝ} {u v : (Fin n → ℝ) → E}
    (hu : IsHolderNorm α u H₀) (hv : IsHolderNorm α v H₀)
    (hrange_u : ∀ x, u x ∈ D.K) (hrange_v : ∀ x, v x ∈ D.K)
    (hM : ∀ x, ‖u x - v x‖ ≤ M) :
    IsHolderNorm α (fun x => D.nemytskii u x - D.nemytskii v x)
      ((D.L : ℝ) * H₀ * M + D.B * (H₀ + H₀)) := by
  have h := isHolderNorm_comp_sub D.hconv D.hderiv D.hB_nonneg D.hB D.hL
    hu (hu.sub hv) hrange_u hrange_v hM
  -- `D.nemytskii u x` unfolds to `D.Φ (u x)`
  simpa [NemytskiiData.nemytskii] using h

end NemytskiiOperator

/-! ## 5. The 2-jet fiber as a normed space -/

/-!
The `Jet2 n d` structure (from `TensorialCommutator`) carries a natural
normed space structure. Since Mathlib's matrix norms are local-only, we
define the sum-of-entries norm directly. This makes `Jet2 n d` a valid
fiber for the Nemytskii machine above.
-/

section MatrixNorm

variable {d : ℕ}

/-- Sum-of-entries norm on square matrices. -/
noncomputable instance matrixNorm : Norm (Matrix (Fin d) (Fin d) ℝ) :=
  ⟨fun M => ∑ i : Fin d, ∑ j : Fin d, |M i j|⟩

theorem matrix_norm_eq (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖M‖ = ∑ i : Fin d, ∑ j : Fin d, |M i j| := rfl

theorem matrix_norm_zero : ‖(0 : Matrix (Fin d) (Fin d) ℝ)‖ = 0 := by
  rw [matrix_norm_eq]
  simp

theorem matrix_norm_neg (M : Matrix (Fin d) (Fin d) ℝ) : ‖-M‖ = ‖M‖ := by
  rw [matrix_norm_eq, matrix_norm_eq]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp [Matrix.neg_apply, abs_neg]

theorem matrix_norm_add_le (M N : Matrix (Fin d) (Fin d) ℝ) :
    ‖M + N‖ ≤ ‖M‖ + ‖N‖ := by
  rw [matrix_norm_eq, matrix_norm_eq, matrix_norm_eq]
  calc ∑ i : Fin d, ∑ j : Fin d, |M i j + N i j|
      ≤ ∑ i : Fin d, ∑ j : Fin d, (|M i j| + |N i j|) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        simp [Matrix.add_apply, abs_add_le]
    _ = (∑ i : Fin d, ∑ j : Fin d, |M i j|) +
        (∑ i : Fin d, ∑ j : Fin d, |N i j|) := by
        simp [Finset.sum_add_distrib]

theorem matrix_eq_zero_of_norm_eq_zero (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ‖M‖ = 0) : M = 0 := by
  rw [matrix_norm_eq] at hM
  have hinner_zero : ∀ i : Fin d, (∑ j : Fin d, |M i j|) = 0 := by
    have hinner_nonneg : ∀ i : Fin d, 0 ≤ ∑ j : Fin d, |M i j| := by
      intro i
      apply Finset.sum_nonneg; intro j _
      exact abs_nonneg _
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hinner_nonneg i)).mp hM i
      (Finset.mem_univ i)
  have hall : ∀ i : Fin d, ∀ j : Fin d, M i j = 0 := by
    intro i j
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (M i j))).mp
      (hinner_zero i) j (Finset.mem_univ j)
    simpa using h
  ext i j
  simp [hall i j]

noncomputable instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ) where
  dist_eq := fun _ _ => rfl
  dist_self := by
    intro M
    show ‖-M + M‖ = 0
    rw [neg_add_cancel]
    exact matrix_norm_zero
  dist_comm := by
    intro M N
    show ‖-M + N‖ = ‖-N + M‖
    have h : -M + N = -(-N + M) := by abel
    rw [h, matrix_norm_neg]
  dist_triangle := by
    intro M N P
    show ‖-M + P‖ ≤ ‖-M + N‖ + ‖-N + P‖
    have h : (-M + P) = (-M + N) + (-N + P) := by abel
    rw [h]
    exact matrix_norm_add_le _ _
  eq_of_dist_eq_zero := by
    intro M N h
    have h' : -M + N = 0 := matrix_eq_zero_of_norm_eq_zero _ h
    calc M = M + 0 := by abel
      _ = M + (-M + N) := by rw [h']
      _ = N := by abel

theorem matrix_norm_smul_le (r : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖r • M‖ ≤ |r| * ‖M‖ := by
  rw [matrix_norm_eq, matrix_norm_eq]
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
  apply le_of_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

noncomputable instance matrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin d) (Fin d) ℝ) where
  norm_smul_le r M := matrix_norm_smul_le r M

end MatrixNorm

namespace Jet2

variable {n d : ℕ}

instance : Zero (Jet2 n d) := ⟨⟨0, 0, 0⟩⟩

instance : Add (Jet2 n d) :=
  ⟨fun j₁ j₂ => ⟨j₁.val + j₂.val, j₁.deriv1 + j₂.deriv1, j₁.deriv2 + j₂.deriv2⟩⟩

instance : Neg (Jet2 n d) :=
  ⟨fun j => ⟨-j.val, -j.deriv1, -j.deriv2⟩⟩

instance : Sub (Jet2 n d) :=
  ⟨fun j₁ j₂ => ⟨j₁.val - j₂.val, j₁.deriv1 - j₂.deriv1, j₁.deriv2 - j₂.deriv2⟩⟩

instance : SMul ℝ (Jet2 n d) :=
  ⟨fun r j => ⟨r • j.val, r • j.deriv1, r • j.deriv2⟩⟩

noncomputable instance : Norm (Jet2 n d) :=
  ⟨fun j => ‖j.val‖ + ∑ i : Fin n, ‖j.deriv1 i‖ + ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖⟩

theorem jet2_norm_eq (j : Jet2 n d) :
    ‖j‖ = ‖j.val‖ + ∑ i : Fin n, ‖j.deriv1 i‖ + ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ := rfl

@[ext]
theorem ext' {j₁ j₂ : Jet2 n d} (hv : j₁.val = j₂.val)
    (hd1 : j₁.deriv1 = j₂.deriv1) (hd2 : j₁.deriv2 = j₂.deriv2) : j₁ = j₂ := by
  cases j₁ with
  | mk v₁ d₁ h₁ =>
    cases j₂ with
    | mk v₂ d₂ h₂ =>
      simp at hv hd1 hd2 ⊢
      exact ⟨hv, hd1, hd2⟩

instance : AddCommGroup (Jet2 n d) where
  add_assoc := by
    intro j₁ j₂ j₃
    obtain ⟨v₁, d₁, h₁⟩ := j₁
    obtain ⟨v₂, d₂, h₂⟩ := j₂
    obtain ⟨v₃, d₃, h₃⟩ := j₃
    apply ext'
    · show (v₁ + v₂) + v₃ = v₁ + (v₂ + v₃); exact add_assoc _ _ _
    · show (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃); exact add_assoc _ _ _
    · show (h₁ + h₂) + h₃ = h₁ + (h₂ + h₃); exact add_assoc _ _ _
  zero_add := by
    intro j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show (0 : Matrix _ _ _) + v = v; exact zero_add _
    · show (0 : Fin n → Matrix _ _ _) + d = d; exact zero_add _
    · show (0 : Fin n → Fin n → Matrix _ _ _) + h = h; exact zero_add _
  add_zero := by
    intro j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show v + (0 : Matrix _ _ _) = v; exact add_zero _
    · show d + (0 : Fin n → Matrix _ _ _) = d; exact add_zero _
    · show h + (0 : Fin n → Fin n → Matrix _ _ _) = h; exact add_zero _
  add_comm := by
    intro j₁ j₂
    obtain ⟨v₁, d₁, h₁⟩ := j₁
    obtain ⟨v₂, d₂, h₂⟩ := j₂
    apply ext'
    · show v₁ + v₂ = v₂ + v₁; exact add_comm _ _
    · show d₁ + d₂ = d₂ + d₁; exact add_comm _ _
    · show h₁ + h₂ = h₂ + h₁; exact add_comm _ _
  neg_add_cancel := by
    intro j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show -v + v = (0 : Matrix _ _ _); exact neg_add_cancel _
    · show -d + d = (0 : Fin n → Matrix _ _ _); exact neg_add_cancel _
    · show -h + h = (0 : Fin n → Fin n → Matrix _ _ _); exact neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by
    intro j₁ j₂
    obtain ⟨v₁, d₁, h₁⟩ := j₁
    obtain ⟨v₂, d₂, h₂⟩ := j₂
    apply ext'
    · show v₁ - v₂ = v₁ + -v₂; exact sub_eq_add_neg _ _
    · show d₁ - d₂ = d₁ + -d₂; exact sub_eq_add_neg _ _
    · show h₁ - h₂ = h₁ + -h₂; exact sub_eq_add_neg _ _

theorem jet2_add_val (j₁ j₂ : Jet2 n d) : (j₁ + j₂).val = j₁.val + j₂.val := rfl

theorem jet2_add_deriv1 (j₁ j₂ : Jet2 n d) :
    (j₁ + j₂).deriv1 = j₁.deriv1 + j₂.deriv1 := rfl

theorem jet2_add_deriv2 (j₁ j₂ : Jet2 n d) :
    (j₁ + j₂).deriv2 = j₁.deriv2 + j₂.deriv2 := rfl

theorem jet2_norm_add_le (j₁ j₂ : Jet2 n d) : ‖j₁ + j₂‖ ≤ ‖j₁‖ + ‖j₂‖ := by
  rw [jet2_norm_eq, jet2_norm_eq, jet2_norm_eq, jet2_add_val, jet2_add_deriv1,
    jet2_add_deriv2]
  simp only [Pi.add_apply]
  have h1 : ‖j₁.val + j₂.val‖ ≤ ‖j₁.val‖ + ‖j₂.val‖ := matrix_norm_add_le _ _
  have h2 : ∑ i : Fin n, ‖j₁.deriv1 i + j₂.deriv1 i‖ ≤
      ∑ i : Fin n, ‖j₁.deriv1 i‖ + ∑ i : Fin n, ‖j₂.deriv1 i‖ := by
    calc ∑ i : Fin n, ‖j₁.deriv1 i + j₂.deriv1 i‖
        ≤ ∑ i : Fin n, (‖j₁.deriv1 i‖ + ‖j₂.deriv1 i‖) := by
          apply Finset.sum_le_sum; intro i _
          exact matrix_norm_add_le _ _
      _ = _ := by simp [Finset.sum_add_distrib]
  have h3 : ∑ i : Fin n, ∑ k : Fin n, ‖j₁.deriv2 i k + j₂.deriv2 i k‖ ≤
      ∑ i : Fin n, ∑ k : Fin n, ‖j₁.deriv2 i k‖ +
      ∑ i : Fin n, ∑ k : Fin n, ‖j₂.deriv2 i k‖ := by
    calc ∑ i : Fin n, ∑ k : Fin n, ‖j₁.deriv2 i k + j₂.deriv2 i k‖
        ≤ ∑ i : Fin n, ∑ k : Fin n, (‖j₁.deriv2 i k‖ + ‖j₂.deriv2 i k‖) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro k _
          exact matrix_norm_add_le _ _
      _ = _ := by simp [Finset.sum_add_distrib]
  linarith

theorem jet2_eq_zero_of_norm_eq_zero (j : Jet2 n d) (hj : ‖j‖ = 0) : j = 0 := by
  rw [jet2_norm_eq] at hj
  have hB : 0 ≤ ∑ i : Fin n, ‖j.deriv1 i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hC : 0 ≤ ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  have hA : 0 ≤ ‖j.val‖ := norm_nonneg _
  have h1 : ‖j.val‖ = 0 := by linarith
  have h2sum : ∑ i : Fin n, ‖j.deriv1 i‖ = 0 := by linarith
  have h3sum : ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ = 0 := by linarith
  have h2 : ∀ i : Fin n, ‖j.deriv1 i‖ = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _)).mp h2sum i
      (Finset.mem_univ i)
  have h3 : ∀ i : Fin n, ∀ k : Fin n, ‖j.deriv2 i k‖ = 0 := by
    intro i k
    have hi : (∑ k : Fin n, ‖j.deriv2 i k‖) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun k _ => norm_nonneg _))).mp h3sum i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => norm_nonneg _)).mp hi k
      (Finset.mem_univ k)
  have hv : j.val = 0 := matrix_eq_zero_of_norm_eq_zero _ h1
  have hd1 : j.deriv1 = 0 := by
    funext i
    exact matrix_eq_zero_of_norm_eq_zero _ (h2 i)
  have hd2 : j.deriv2 = 0 := by
    funext i k
    exact matrix_eq_zero_of_norm_eq_zero _ (h3 i k)
  exact ext' hv hd1 hd2

theorem jet2_norm_neg (j : Jet2 n d) : ‖-j‖ = ‖j‖ := by
  rw [jet2_norm_eq, jet2_norm_eq]
  have h1 : ‖(-j).val‖ = ‖j.val‖ := by
    show ‖-j.val‖ = ‖j.val‖
    exact matrix_norm_neg _
  have h2 : ∑ i : Fin n, ‖(-j).deriv1 i‖ = ∑ i : Fin n, ‖j.deriv1 i‖ := by
    apply Finset.sum_congr rfl; intro i _
    show ‖-j.deriv1 i‖ = ‖j.deriv1 i‖
    exact matrix_norm_neg _
  have h3 : ∑ i : Fin n, ∑ k : Fin n, ‖(-j).deriv2 i k‖ =
      ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    show ‖-j.deriv2 i k‖ = ‖j.deriv2 i k‖
    exact matrix_norm_neg _
  linarith

noncomputable instance : NormedAddCommGroup (Jet2 n d) where
  dist_eq := fun _ _ => rfl
  dist_self := by
    intro j
    show ‖-j + j‖ = 0
    have h : -j + j = 0 := neg_add_cancel j
    rw [h, jet2_norm_eq]
    have h1 : (0 : Jet2 n d).val = (0 : Matrix (Fin d) (Fin d) ℝ) := rfl
    have h2 : (0 : Jet2 n d).deriv1 = (0 : Fin n → Matrix (Fin d) (Fin d) ℝ) := rfl
    have h3 : (0 : Jet2 n d).deriv2 =
        (0 : Fin n → Fin n → Matrix (Fin d) (Fin d) ℝ) := rfl
    rw [h1, h2, h3]
    simp [matrix_norm_zero, Pi.zero_apply]
  dist_comm := by
    intro j₁ j₂
    show ‖-j₁ + j₂‖ = ‖-j₂ + j₁‖
    have h : -j₁ + j₂ = -(-j₂ + j₁) := by abel
    rw [h, jet2_norm_neg]
  dist_triangle := by
    intro j₁ j₂ j₃
    show ‖-j₁ + j₃‖ ≤ ‖-j₁ + j₂‖ + ‖-j₂ + j₃‖
    have h : (-j₁ + j₃) = (-j₁ + j₂) + (-j₂ + j₃) := by abel
    rw [h]
    exact jet2_norm_add_le _ _
  eq_of_dist_eq_zero := by
    intro j₁ j₂ h
    have h' : -j₁ + j₂ = 0 := jet2_eq_zero_of_norm_eq_zero _ h
    calc j₁ = j₁ + 0 := by abel
      _ = j₁ + (-j₁ + j₂) := by rw [h']
      _ = j₂ := by abel

theorem jet2_norm_smul_le (r : ℝ) (j : Jet2 n d) : ‖r • j‖ ≤ |r| * ‖j‖ := by
  rw [jet2_norm_eq, jet2_norm_eq]
  have h1 : ‖(r • j).val‖ ≤ |r| * ‖j.val‖ := by
    show ‖r • j.val‖ ≤ |r| * ‖j.val‖
    exact matrix_norm_smul_le _ _
  have h2 : ∑ i : Fin n, ‖(r • j).deriv1 i‖ ≤ |r| * ∑ i : Fin n, ‖j.deriv1 i‖ := by
    have : ∀ i : Fin n, ‖(r • j).deriv1 i‖ ≤ |r| * ‖j.deriv1 i‖ := by
      intro i
      show ‖r • j.deriv1 i‖ ≤ |r| * ‖j.deriv1 i‖
      exact matrix_norm_smul_le _ _
    calc ∑ i : Fin n, ‖(r • j).deriv1 i‖
        ≤ ∑ i : Fin n, (|r| * ‖j.deriv1 i‖) := by
          apply Finset.sum_le_sum; intro i _
          exact this i
      _ = |r| * ∑ i : Fin n, ‖j.deriv1 i‖ := by rw [Finset.mul_sum]
  have h3 : ∑ i : Fin n, ∑ k : Fin n, ‖(r • j).deriv2 i k‖ ≤
      |r| * ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ := by
    have : ∀ i : Fin n, ∀ k : Fin n, ‖(r • j).deriv2 i k‖ ≤ |r| * ‖j.deriv2 i k‖ := by
      intro i k
      show ‖r • j.deriv2 i k‖ ≤ |r| * ‖j.deriv2 i k‖
      exact matrix_norm_smul_le _ _
    calc ∑ i : Fin n, ∑ k : Fin n, ‖(r • j).deriv2 i k‖
        ≤ ∑ i : Fin n, ∑ k : Fin n, (|r| * ‖j.deriv2 i k‖) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro k _
          exact this i k
      _ = |r| * ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
  calc ‖(r • j).val‖ + ∑ i : Fin n, ‖(r • j).deriv1 i‖ +
        ∑ i : Fin n, ∑ k : Fin n, ‖(r • j).deriv2 i k‖
      ≤ |r| * ‖j.val‖ + |r| * ∑ i : Fin n, ‖j.deriv1 i‖ +
        |r| * ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖ := by
        apply add_le_add (add_le_add h1 h2) h3
    _ = |r| * (‖j.val‖ + ∑ i : Fin n, ‖j.deriv1 i‖ +
        ∑ i : Fin n, ∑ k : Fin n, ‖j.deriv2 i k‖) := by ring

instance : Module ℝ (Jet2 n d) where
  smul_add := by
    intro r j₁ j₂
    obtain ⟨v₁, d₁, h₁⟩ := j₁
    obtain ⟨v₂, d₂, h₂⟩ := j₂
    apply ext'
    · show r • (v₁ + v₂) = r • v₁ + r • v₂; exact smul_add _ _ _
    · show r • (d₁ + d₂) = r • d₁ + r • d₂; exact smul_add _ _ _
    · show r • (h₁ + h₂) = r • h₁ + r • h₂; exact smul_add _ _ _
  add_smul := by
    intro r s j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show (r + s) • v = r • v + s • v; exact add_smul _ _ _
    · show (r + s) • d = r • d + s • d; exact add_smul _ _ _
    · show (r + s) • h = r • h + s • h; exact add_smul _ _ _
  mul_smul := by
    intro r s j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show (r * s) • v = r • s • v; exact mul_smul _ _ _
    · show (r * s) • d = r • s • d; exact mul_smul _ _ _
    · show (r * s) • h = r • s • h; exact mul_smul _ _ _
  one_smul := by
    intro j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show (1 : ℝ) • v = v; exact one_smul _ _
    · show (1 : ℝ) • d = d; exact one_smul _ _
    · show (1 : ℝ) • h = h; exact one_smul _ _
  zero_smul := by
    intro j
    obtain ⟨v, d, h⟩ := j
    apply ext'
    · show (0 : ℝ) • v = 0; exact zero_smul _ _
    · show (0 : ℝ) • d = 0; exact zero_smul _ _
    · show (0 : ℝ) • h = 0; exact zero_smul _ _
  smul_zero := by
    intro r
    apply ext'
    · show r • (0 : Matrix _ _ _) = 0; exact smul_zero _
    · show r • (0 : Fin n → Matrix _ _ _) = 0; exact smul_zero _
    · show r • (0 : Fin n → Fin n → Matrix _ _ _) = 0; exact smul_zero _

noncomputable instance : NormedSpace ℝ (Jet2 n d) where
  norm_smul_le r j := jet2_norm_smul_le r j

end Jet2

/-! ## 6. Nemytskii operators on 2-jet fibers -/

/-!
With `Jet2 n d` established as a `NormedSpace ℝ`, the abstract Nemytskii
machine from Sections 1–4 applies directly to 2-jet fibers. For a `C¹`
fiber map `Φ : Jet2 n d → F` with bounded, Lipschitz derivative on a
convex set of 2-jets, the composition
  `(N u) x = Φ (j²u x)`
preserves Hölder regularity, where `j²u x : Jet2 n d` is the 2-jet of
the section `u` at `x`.

This is the analytic backbone for the Ricci–DeTurck nonlinearity
  `N_RD(g)(x) = Φ_RD (j²g(x))`
as a Nemytskii operator on 2-jets. The genuine geometric `Φ_RD` (a
smooth function of the 2-jet built from actual Ricci curvature) is not
yet formalized; what is proved here is that *any* fiber map satisfying
the analytic hypotheses yields a Hölder-continuous Nemytskii operator
on 2-jet sections. No claim is made about real jet extraction from
`C^{2,α}` metrics — that bridge remains future work.
-/

namespace Jet2Nemytskii

variable {n d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Nemytskii data on 2-jet fibers: a `C¹` fiber map `Φ : Jet2 n d → F`
with bounded, Lipschitz derivative on a convex set `K` of 2-jets. -/
structure Jet2NemytskiiData (n d : ℕ) (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] where
  toNemytskii : NemytskiiData (Jet2 n d) F

namespace Jet2NemytskiiData

variable {D : Jet2NemytskiiData n d F}

/-- The Nemytskii operator on 2-jet sections: `(N u) x = Φ (j²u x)`. -/
noncomputable def nemytskiiJet (D : Jet2NemytskiiData n d F)
    (u : (Fin n → ℝ) → Jet2 n d) : (Fin n → ℝ) → F :=
  D.toNemytskii.nemytskii u

/-- The 2-jet Nemytskii operator preserves Hölder regularity. -/
theorem isHolderNorm_nemytskiiJet (D : Jet2NemytskiiData n d F)
    {α H₀ : ℝ} {u : (Fin n → ℝ) → Jet2 n d}
    (hu : IsHolderNorm α u H₀) (hrange : ∀ x, u x ∈ D.toNemytskii.K) :
    IsHolderNorm α (D.nemytskiiJet u) (D.toNemytskii.B * H₀) :=
  D.toNemytskii.isHolderNorm_nemytskii hu hrange

/-- Coarse Hölder difference estimate for the 2-jet Nemytskii operator.
See `NemytskiiData.isHolderNorm_nemytskii_sub_coarse` for the honest
limitation: this is not a genuine local-Lipschitz estimate. -/
theorem isHolderNorm_nemytskiiJet_sub_coarse (D : Jet2NemytskiiData n d F)
    {α H₀ M : ℝ} {u v : (Fin n → ℝ) → Jet2 n d}
    (hu : IsHolderNorm α u H₀) (hv : IsHolderNorm α v H₀)
    (hrange_u : ∀ x, u x ∈ D.toNemytskii.K)
    (hrange_v : ∀ x, v x ∈ D.toNemytskii.K)
    (hM : ∀ x, ‖u x - v x‖ ≤ M) :
    IsHolderNorm α (fun x => D.nemytskiiJet u x - D.nemytskiiJet v x)
      (((D.toNemytskii.L : ℝ≥0) : ℝ) * H₀ * M +
        D.toNemytskii.B * (H₀ + H₀)) :=
  D.toNemytskii.isHolderNorm_nemytskii_sub_coarse hu hv hrange_u hrange_v hM

end Jet2NemytskiiData

end Jet2Nemytskii
