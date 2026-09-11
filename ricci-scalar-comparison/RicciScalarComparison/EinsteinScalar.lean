module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.Einstein

/-!
# Scalar curvature of the homothetic Einstein Ricci flow

This module derives the exact scalar-curvature law of the genuine intrinsic
Ricci-flow solution constructed from Einstein initial data.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Bundle
open scoped Manifold ContDiff

namespace RicciScalarComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

open RicciFlow CovariantDerivative

/-- The singular time of a shrinking Einstein solution with `lam > 0`. -/
def extinctionTime (lam t₀ : ℝ) : ℝ := t₀ + 1 / (2 * lam)

/-- The standard scalar-curvature comparison profile solving
`r' = (2/n) r²` with initial value `r₀`. -/
def quadraticScalarBarrier (n r₀ t₀ t : ℝ) : ℝ :=
  r₀ / (1 - (2 / n) * r₀ * (t - t₀))

lemma homotheticFactor_extinctionTime_eq_zero (lam t₀ : ℝ) (hlam : 0 < lam) :
    homotheticFactor lam t₀ (extinctionTime lam t₀) = 0 := by
  have hne : 2 * lam ≠ 0 := by positivity
  rw [homotheticFactor, extinctionTime]
  field_simp
  ring

/-- For positive Einstein constant, positivity of the homothetic metric is
equivalent to being strictly before the singular time. -/
theorem homotheticFactor_pos_iff_lt_extinctionTime
    (lam t₀ t : ℝ) (hlam : 0 < lam) :
    0 < homotheticFactor lam t₀ t ↔ t < extinctionTime lam t₀ := by
  have htwo : 0 < 2 * lam := by positivity
  constructor
  · intro h
    have hmul : (t - t₀) * (2 * lam) < 1 := by
      rw [mul_comm]
      simpa [homotheticFactor] using h
    have hdiv : t - t₀ < 1 / (2 * lam) := (lt_div_iff₀ htwo).2 hmul
    simpa [extinctionTime, add_comm] using (sub_lt_iff_lt_add.mp hdiv)
  · intro h
    have hdiv : t - t₀ < 1 / (2 * lam) := by
      apply sub_lt_iff_lt_add.mpr
      simpa [extinctionTime, add_comm] using h
    have hmul : (t - t₀) * (2 * lam) < 1 := (lt_div_iff₀ htwo).1 hdiv
    rw [mul_comm] at hmul
    simpa [homotheticFactor] using hmul

/-- The scalar curvature of a homothetic Einstein slice is spatially constant
and equals `n λ / (1 - 2 λ (t - t₀))`. -/
theorem scalarCurvature_homotheticMetricFamily
    (lam t₀ : ℝ) (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hEinstein : ∀ (x : M) (u v : TM x),
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) =
        lam * g₀.inner x u v)
    (t : ℝ) (ht : 0 < homotheticFactor lam t₀ t) (x : M) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(homotheticMetricFamily (I := I) (M := M) lam t₀ g₀ t).toRiemannianMetric⟩
     CovariantDerivative.scalarCurvature (cov := cov₀) x) =
        (Module.finrank ℝ E : ℝ) * (lam / homotheticFactor lam t₀ t) := by
  let g := homotheticMetricFamily (I := I) (M := M) lam t₀ g₀
  have _hLeviFamily := RicciFlow.isLeviCivita_const_homotheticMetricFamily
    (I := I) (M := M) lam t₀ g₀ cov₀ hLevi
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [CovariantDerivative.scalarCurvature_eq_sum]
  have hterm : ∀ i : Fin (Module.finrank ℝ (TM x)),
      CovariantDerivative.ricciCurvature (cov := cov₀) x
          ((stdOrthonormalBasis ℝ (TM x)) i)
          ((stdOrthonormalBasis ℝ (TM x)) i) =
        lam / homotheticFactor lam t₀ t := by
    intro i
    let e := (stdOrthonormalBasis ℝ (TM x)) i
    rw [RicciFlow.ricciCurvature_riemannianBundle_irrelevant
      (I := I) (M := M) (g t) g₀ cov₀ x e e]
    rw [hEinstein x e e]
    have hs := RicciFlow.homotheticMetricFamily_inner_of_pos
      (I := I) (M := M) lam t₀ g₀ ht x e e
    have hone : (g t).inner x e e = 1 := by
      change inner ℝ e e = 1
      rw [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one]
      norm_num
    have hprod : homotheticFactor lam t₀ t * g₀.inner x e e = 1 := by
      rw [← hs]
      exact hone
    have hne : homotheticFactor lam t₀ t ≠ 0 := ne_of_gt ht
    have hg : g₀.inner x e e = 1 / homotheticFactor lam t₀ t := by
      apply (eq_div_iff hne).2
      simpa [mul_comm] using hprod
    rw [hg]
    ring
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (Module.finrank ℝ E : ℝ) * (lam / homotheticFactor lam t₀ t) = _
  rfl

/-- On an Einstein solution the general quadratic scalar comparison profile is
attained with equality. This is the sharp model for the compact Ricci-flow
lower-barrier estimate. -/
theorem scalarCurvature_eq_quadraticScalarBarrier
    [Nontrivial E]
    (lam t₀ : ℝ) (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hEinstein : ∀ (x : M) (u v : TM x),
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) =
        lam * g₀.inner x u v)
    (t : ℝ) (ht : 0 < homotheticFactor lam t₀ t) (x : M) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(homotheticMetricFamily (I := I) (M := M) lam t₀ g₀ t).toRiemannianMetric⟩
     CovariantDerivative.scalarCurvature (cov := cov₀) x) =
      quadraticScalarBarrier (Module.finrank ℝ E : ℝ)
        ((Module.finrank ℝ E : ℝ) * lam) t₀ t := by
  rw [scalarCurvature_homotheticMetricFamily
    (I := I) (M := M) lam t₀ g₀ cov₀ hLevi hEinstein t ht x]
  have hnNat : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hn : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hnNat.ne'
  have hf : homotheticFactor lam t₀ t ≠ 0 := ne_of_gt ht
  unfold quadraticScalarBarrier homotheticFactor
  field_simp

/-- The homothetic Einstein family is an intrinsic Ricci-flow solution on its
entire positive-definite time set. -/
noncomputable def maximalEinsteinHomotheticIntrinsicSolution
    (lam t₀ : ℝ) (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hEinstein : ∀ (x : M) (u v : TM x),
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) =
        lam * g₀.inner x u v) :
    IntrinsicSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := {t | 0 < homotheticFactor lam t₀ t}
  metric := homotheticMetricFamily (I := I) (M := M) lam t₀ g₀
  metricVelocity := fun _ x u v ↦ -(2 * lam) * g₀.inner x u v
  isRicciFlow := by
    constructor
    · intro t ht
      exact RicciFlow.hasTimeDerivativeAt_homotheticMetricFamily
        (I := I) (M := M) lam t₀ g₀ ht
    · intro t _ht x u v
      show -(2 * lam) * g₀.inner x u v =
        intrinsicRicciFlowRHS (I := I) (M := M)
          (homotheticMetricFamily (I := I) (M := M) lam t₀ g₀) t x u v
      rw [RicciFlow.intrinsicRicciFlowRHS_apply]
      show -(2 * lam) * g₀.inner x u v =
        (-2 : ℝ) * intrinsicRicciTensor (I := I) (M := M)
          (homotheticMetricFamily (I := I) (M := M) lam t₀ g₀) t x u v
      rw [RicciFlow.intrinsicRicciTensor_homotheticMetricFamily
        (I := I) (M := M) lam t₀ g₀ cov₀ hLevi hEinstein t u v]
      ring

/-- For `lam > 0`, the exact solution's time set is precisely the half-line
strictly preceding the singular time. -/
theorem maximalEinsteinHomotheticIntrinsicSolution_timeSet
    (lam t₀ : ℝ) (hlam : 0 < lam)
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hEinstein : ∀ (x : M) (u v : TM x),
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩;
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) =
        lam * g₀.inner x u v) :
    (maximalEinsteinHomotheticIntrinsicSolution
      (I := I) (M := M) lam t₀ g₀ cov₀ hLevi hEinstein).timeSet =
        Set.Iio (extinctionTime lam t₀) := by
  ext t
  exact homotheticFactor_pos_iff_lt_extinctionTime lam t₀ t hlam

/-- Every closed interval ending strictly before the singular time carries a
genuine intrinsic local Ricci-flow solution with the Einstein initial metric. -/
noncomputable def einsteinIntrinsicLocalSolutionBeforeExtinction
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (lam : ℝ) (hlam : 0 < lam) (T : ℝ)
    (hforward : ivp.initialTime < T)
    (hbefore : T < extinctionTime lam ivp.initialTime)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM :=
      ⟨ivp.initialMetric.toRiemannianMetric⟩; cov₀.IsLeviCivita)
    (hEinstein : ∀ (x : M) (u v : TM x),
      (letI : Bundle.RiemannianBundle TM :=
        ⟨ivp.initialMetric.toRiemannianMetric⟩;
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) =
        lam * ivp.initialMetric.inner x u v) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := T
  initial_lt_terminal := hforward
  toIntrinsicSolution := maximalEinsteinHomotheticIntrinsicSolution
    (I := I) (M := M) lam ivp.initialTime ivp.initialMetric cov₀ hLevi hEinstein
  interval_subset := by
    intro t ht
    exact (homotheticFactor_pos_iff_lt_extinctionTime
      lam ivp.initialTime t hlam).2 (lt_of_le_of_lt ht.2 hbefore)
  matchesInitialMetric := by
    intro x u v
    show metricTensor (I := I) (M := M)
      (homotheticMetricFamily (I := I) (M := M) lam ivp.initialTime ivp.initialMetric)
      ivp.initialTime x u v = ivp.initialMetric.inner x u v
    have hpos : 0 < homotheticFactor lam ivp.initialTime ivp.initialTime := by
      simp [homotheticFactor]
    simp only [metricTensor]
    rw [RicciFlow.homotheticMetricFamily_inner_of_pos
      (I := I) (M := M) lam ivp.initialTime ivp.initialMetric hpos x u v,
      RicciFlow.homotheticFactor_self, one_mul]

/-- At the singular time the formal homothetic tensor is zero, so it cannot be
a Riemannian metric on a positive-dimensional nonempty manifold. -/
theorem no_riemannian_metric_agrees_at_extinction
    [Nontrivial E] [Nonempty M]
    (lam t₀ : ℝ) (hlam : 0 < lam)
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    ¬ ∃ gstar : Bundle.ContMDiffRiemannianMetric I 2 E TM,
      ∀ (x : M) (u v : TM x),
        gstar.inner x u v =
          homotheticFactor lam t₀ (extinctionTime lam t₀) * g₀.inner x u v := by
  rintro ⟨gstar, hagree⟩
  let x : M := Classical.choice (inferInstance : Nonempty M)
  haveI : Nontrivial (TM x) := inferInstanceAs (Nontrivial E)
  obtain ⟨v, hv⟩ : ∃ v : TM x, v ≠ 0 := exists_ne 0
  have hpos := gstar.pos x v hv
  rw [hagree x v v, homotheticFactor_extinctionTime_eq_zero lam t₀ hlam, zero_mul] at hpos
  exact (lt_irrefl 0) hpos

end RicciScalarComparison
