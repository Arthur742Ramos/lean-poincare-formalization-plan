module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarOpenInitialPotential
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorNormSq

/-!
# Tensor heat uniqueness from a scalar norm inequality

This reduction uses the complete Hilbert--Schmidt norm of a covariant
two-tensor and allows bounded zero-order growth. The spatial Bochner
inequality remains an explicit, unproved input here; this theorem does not
supply it or assert tensor-heat uniqueness without it.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Bundle Set Topology
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [Nonempty M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Twice the pointwise Hilbert--Schmidt pairing with the genuine tensor
time derivative, for a fixed spatial Riemannian metric. -/
def covariantTwoTensorNormTimePair
    (h dh : ℝ → ∀ x : M, T₂ x) (t : ℝ) (x : M) : ℝ := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, ∑ j,
    2 * h t x (b i) (b j) * dh t x (b i) (b j)

theorem covariantTwoTensorNormTimePair_eq_two_mul_pair
    (h dh : ℝ → ∀ x : M, T₂ x) (t : ℝ) (x : M) :
    covariantTwoTensorNormTimePair h dh t x =
      2 * CovariantDerivative.covariantTwoTensorPair (h t) (dh t) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  change (∑ i, ∑ j,
      2 * h t x (b i) (b j) * dh t x (b i) (b j)) =
    2 * (∑ i, ∑ j,
      h t x (b i) (b j) * dh t x (b i) (b j))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A spatial norm subsolution with zero initial tensor forces the
entire tensor to vanish, including its off-diagonal components. The needed
spatial differential inequality and zero-order bound are visible as `hpde`;
proving them from a geometric connection Laplacian is the remaining Bochner
step. -/
theorem covariantTwoTensor_eq_zero_of_norm_subsolution_openInitial_potential
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (h dh : ℝ → ∀ x : M, T₂ x) (K : ℝ) {t₀ T : ℝ}
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        CovariantDerivative.covariantTwoTensorNormSq (h p.1) p.2)
      (Icc t₀ T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Ioo t₀ T, ∀ x : M, ∀ u v : TM x,
      HasDerivAt (fun s => h s x u v) (dh t x u v) t)
    (hspatial : ∀ t ∈ Ioo t₀ T, ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) z (h t z)) y)
    (hgradient : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (CovariantDerivative.covariantTwoTensorNormSq (h t)) y)) x)
    (hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      covariantTwoTensorNormTimePair h dh t x ≤
        g.scalarLaplacian cov
          (fun _ => CovariantDerivative.covariantTwoTensorNormSq (h t)) t x +
          K * CovariantDerivative.covariantTwoTensorNormSq (h t) x)
    (hinitial : ∀ x : M, h t₀ x = 0) :
    ∀ t ∈ Ioo t₀ T, ∀ x : M, h t x = 0 := by
  have hnormTime : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      HasDerivAt
        (fun s => CovariantDerivative.covariantTwoTensorNormSq (h s) x)
        (covariantTwoTensorNormTimePair h dh t x) t := by
    intro t ht x
    simpa only [covariantTwoTensorNormTimePair] using
      (CovariantDerivative.hasDerivAt_covariantTwoTensorNormSq
        h dh t x (htime t ht x))
  have hnormInitial : ∀ x : M,
      CovariantDerivative.covariantTwoTensorNormSq (h t₀) x ≤ 0 := by
    intro x
    rw [(CovariantDerivative.covariantTwoTensorNormSq_eq_zero_iff
      (h t₀) x).2 (hinitial x)]
  have hnormSpatial : ∀ t ∈ Ioo t₀ T, ∀ y : M,
      MDiffAt (CovariantDerivative.covariantTwoTensorNormSq (h t)) y := by
    intro t ht y
    exact CovariantDerivative.covariantTwoTensorNormSq_mdifferentiableAt
      (hspatial t ht y)
  have hnonpos := g.parabolicSubsolution_nonpositive_openInitial_potential cov
    (fun t x => CovariantDerivative.covariantTwoTensorNormSq (h t) x)
    (covariantTwoTensorNormTimePair h dh) K
    hcont hnormTime hnormSpatial hgradient hpde hnormInitial
  intro t ht x
  apply (CovariantDerivative.covariantTwoTensorNormSq_eq_zero_iff (h t) x).1
  exact le_antisymm (hnonpos t ht x)
    (CovariantDerivative.covariantTwoTensorNormSq_nonneg (h t) x)

/-- The exact geometric heat equation reduces to zero-data uniqueness once
the metric Bochner inequality and a fibrewise bound on its lower-order
reaction have been established. The Bochner inequality remains a named
premise; no connection identity is assumed by a disguised definition. -/
theorem covariantTwoTensor_eq_zero_of_connectionHeat_bochner
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (h dh reaction : ℝ → ∀ x : M, T₂ x) (C : ℝ) {t₀ T : ℝ}
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        CovariantDerivative.covariantTwoTensorNormSq (h p.1) p.2)
      (Icc t₀ T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Ioo t₀ T, ∀ x : M, ∀ u v : TM x,
      HasDerivAt (fun s => h s x u v) (dh t x u v) t)
    (hspatial : ∀ t ∈ Ioo t₀ T, ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) z (h t z)) y)
    (hgradient : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (CovariantDerivative.covariantTwoTensorNormSq (h t)) y)) x)
    (hheat : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      dh t x = CovariantDerivative.connectionLaplacian (cov t) (h t) x +
        reaction t x)
    (hbochner : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      2 * CovariantDerivative.covariantTwoTensorPair (h t)
        (fun y => CovariantDerivative.connectionLaplacian (cov t) (h t) y) x ≤
          g.scalarLaplacian cov
            (fun _ => CovariantDerivative.covariantTwoTensorNormSq (h t)) t x)
    (hreaction : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      CovariantDerivative.covariantTwoTensorNormSq (reaction t) x ≤
        C * CovariantDerivative.covariantTwoTensorNormSq (h t) x)
    (hinitial : ∀ x : M, h t₀ x = 0) :
    ∀ t ∈ Ioo t₀ T, ∀ x : M, h t x = 0 := by
  have hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      covariantTwoTensorNormTimePair h dh t x ≤
        g.scalarLaplacian cov
          (fun _ => CovariantDerivative.covariantTwoTensorNormSq (h t)) t x +
          (1 + C) * CovariantDerivative.covariantTwoTensorNormSq (h t) x := by
    intro t ht x
    rw [covariantTwoTensorNormTimePair_eq_two_mul_pair]
    have hdh : dh t = fun y =>
        CovariantDerivative.connectionLaplacian (cov t) (h t) y +
          reaction t y := by
      funext y
      exact hheat t ht y
    rw [hdh, CovariantDerivative.covariantTwoTensorPair_add_right]
    have hspatialBound := hbochner t ht x
    have hreactBound :=
      CovariantDerivative.two_mul_covariantTwoTensorPair_le_potential
        (h t) (reaction t) x C (hreaction t ht x)
    linarith
  exact covariantTwoTensor_eq_zero_of_norm_subsolution_openInitial_potential
    g cov h dh (1 + C) hcont htime hspatial hgradient hpde hinitial

end CovariantDerivative.TimeDependentRiemannianMetric
