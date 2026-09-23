module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarOpenInitialInvariant

/-!
# Open-initial scalar comparison with a bounded potential

Multiplication by an exponential integrating factor reduces a scalar
subsolution with a constant upper bound on its zero-order coefficient to the
open-initial comparison principle. This is the form needed after estimating
the curvature reaction in a tensor heat equation.
-/

@[expose] public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- A compact-manifold scalar subsolution with bounded zero-order growth and
nonpositive continuous initial trace stays nonpositive. The PDE is required
only for positive time. -/
theorem parabolicSubsolution_nonpositive_openInitial_potential
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f ft : ℝ → M → ℝ) (K : ℝ) {t₀ T : ℝ}
    (hcont : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (Icc t₀ T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      HasDerivAt (fun s => f s x) (ft t x) t)
    (hf : ∀ t ∈ Ioo t₀ T, ∀ y : M, MDiffAt (f t) y)
    (hdf : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I) (f t) y)) x)
    (hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      ft t x ≤ g.scalarLaplacian cov f t x + K * f t x)
    (hinitial : ∀ x : M, f t₀ x ≤ 0) :
    ∀ t ∈ Ioo t₀ T, ∀ x : M, f t x ≤ 0 := by
  let w : ℝ → ℝ := fun t => Real.exp (-K * (t - t₀))
  let q : ℝ → M → ℝ := fun t x => w t * f t x
  let qt : ℝ → M → ℝ := fun t x => w t * (ft t x - K * f t x)
  have hwpos (t : ℝ) : 0 < w t := Real.exp_pos _
  have hwderiv (t : ℝ) : HasDerivAt w (-K * w t) t := by
    convert ((hasDerivAt_id t).sub_const t₀).const_mul (-K) |>.exp using 1 <;>
      simp [w, mul_sub, mul_comm]
  have hqcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2)
      (Icc t₀ T ×ˢ (Set.univ : Set M)) := by
    have hw : Continuous (fun p : ℝ × M => w p.1) := by
      dsimp [w]
      fun_prop
    exact hw.continuousOn.mul hcont
  have hqtime : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      HasDerivAt (fun s => q s x) (qt t x) t := by
    intro t ht x
    change HasDerivAt (w * fun s => f s x)
      (w t * (ft t x - K * f t x)) t
    have hvalue : w t * (ft t x - K * f t x) =
        -K * w t * f t x + w t * ft t x := by ring
    rw [hvalue]
    exact (hwderiv t).mul (htime t ht x)
  have hqspatial : ∀ t ∈ Ioo t₀ T, ∀ y : M, MDiffAt (q t) y := by
    intro t ht y
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => w t) y).mul
      (hf t ht y)
  have hqgradient : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I) (q t) y)) x := by
    intro t ht x
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    have hqeq : q t = w t • f t := by
      funext y
      simp [q, Pi.smul_apply, smul_eq_mul]
    have hdiff := CovariantDerivative.scalarDifferential_smul_const
      (I := I) (w t) (hf t ht)
    rw [hqeq, hdiff]
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => w t) x).smul_section
      (hdf t ht x)
  have hqlap : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      g.scalarLaplacian cov q t x =
        w t * g.scalarLaplacian cov f t x := by
    intro t ht x
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    change CovariantDerivative.scalarLaplacian (cov t) (q t) x = _
    have hqeq : q t = w t • f t := by
      funext y
      simp [q, Pi.smul_apply, smul_eq_mul]
    rw [hqeq]
    exact CovariantDerivative.scalarLaplacian_smul_const (cov t) (w t)
      (hf t ht) (hdf t ht x)
  have hqpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      qt t x ≤ g.scalarLaplacian cov q t x := by
    intro t ht x
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    rw [hqlap t ht x]
    dsimp [qt]
    have hbase : ft t x - K * f t x ≤
        CovariantDerivative.scalarLaplacian (cov t) (f t) x := by
      have h := hpde t ht x
      change ft t x ≤
        CovariantDerivative.scalarLaplacian (cov t) (f t) x + K * f t x at h
      linarith
    exact mul_le_mul_of_nonneg_left hbase (hwpos t).le
  have hqinitial : ∀ x : M, q t₀ x ≤ 0 := by
    intro x
    simpa [q, w] using hinitial x
  have hqnonpos := g.parabolicSubsolution_nonpositive_openInitial cov
    q qt hqcont hqtime hqspatial hqgradient hqpde hqinitial
  intro t ht x
  by_contra hnot
  have hfpos : 0 < f t x := lt_of_not_ge hnot
  have hqpos : 0 < q t x := mul_pos (hwpos t) hfpos
  exact not_lt_of_ge (hqnonpos t ht x) hqpos

end CovariantDerivative.TimeDependentRiemannianMetric
