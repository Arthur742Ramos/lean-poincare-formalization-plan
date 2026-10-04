/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.MetricBilinearContraction
import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck

/-!
# The conventional metric-contracted DeTurck field

This field contracts the two input slots of the actual connection difference
with the inverse metric. The legacy `intrinsicDeTurckVectorField` instead raises
the ordinary trace of an output/input contraction; it is deliberately left
unchanged here. The new field's exact inverse-Gram frame formula is proved.

This repairs the field-definition layer only. Joint regularity, the fixed-
background quasilinear PDE, gauge recovery, and canonical Point-4 closure are
not asserted by these definitions and algebraic identities.
-/

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual connection difference, retaining both covariant slots. -/
def metricConnectionDifferenceBilinear
    (cov cov' : CovariantDerivative I E TM) (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x where
  toFun u := (CovariantDerivative.difference cov cov' x u).toLinearMap
  map_add' u v := by
    ext w
    exact congrArg (fun A : TM x →L[ℝ] TM x => A w)
      ((CovariantDerivative.difference cov cov' x).map_add u v)
  map_smul' c u := by
    ext w
    exact congrArg (fun A : TM x →L[ℝ] TM x => A w)
      ((CovariantDerivative.difference cov cov' x).map_smul c u)

@[simp] theorem metricConnectionDifferenceBilinear_apply
    (cov cov' : CovariantDerivative I E TM) (x : M) (u v : TM x) :
    metricConnectionDifferenceBilinear cov cov' x u v =
      CovariantDerivative.difference cov cov' x u v := rfl

variable [RiemannianBundle TM]

/-- The inverse-metric trace of the connection-difference bilinear tensor. -/
noncomputable def metricConnectionDifferenceVector
    (cov cov' : CovariantDerivative I E TM) (x : M) : TM x := by
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  exact PoincareCurvature.metricBilinearContraction
    (metricConnectionDifferenceBilinear cov cov' x)

theorem metricConnectionDifferenceVector_eq_sum_orthonormalBasis
    (cov cov' : CovariantDerivative I E TM) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    metricConnectionDifferenceVector cov cov' x =
      ∑ i, CovariantDerivative.difference cov cov' x (b i) (b i) := by
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  exact PoincareCurvature.metricBilinearContraction_eq_sum_orthonormalBasis
    (metricConnectionDifferenceBilinear cov cov' x) b

theorem metricConnectionDifferenceVector_eq_sum_inverseGram
    (cov cov' : CovariantDerivative I E TM) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ (TM x)) :
    metricConnectionDifferenceVector cov cov' x =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j •
        CovariantDerivative.difference cov cov' x (b i) (b j) := by
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  exact PoincareCurvature.metricBilinearContraction_eq_sum_inverseGram
    (metricConnectionDifferenceBilinear cov cov' x) b

/-- The genuine local-frame formula has the conventional `g^{ij} D^k_{ij}`
contraction, with the inverse of the actual local metric Gram matrix. -/
theorem metricConnectionDifferenceVector_localFrameCoeff
    (cov cov' : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (k : ι) :
    e.localFrameCoeff I b k x (metricConnectionDifferenceVector cov cov' x) =
      ∑ i, ∑ j, (localFrameGramMatrix (I := I) e b x)⁻¹ i j *
        e.localFrameCoeff I b k x
          (CovariantDerivative.difference cov cov' x
            (e.localFrame b i x) (e.localFrame b j x)) := by
  let basis := e.basisAt b hx
  have hframe (i : ι) : basis i = e.localFrame b i x := by
    simp [basis, Bundle.Trivialization.basisAt,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
  have hG : Matrix.gram ℝ basis = localFrameGramMatrix (I := I) e b x := by
    ext i j
    simp [Matrix.gram_apply, hframe, localFrameGramMatrix]
  have hcoeff (i : ι) (v : TM x) :
      e.localFrameCoeff I b i x v = basis.repr v i := by
    let he := e.isLocalFrameOn_localFrame_baseSet I 1 b
    have hbasis : e.basisAt b hx = he.toBasisAt hx := by
      ext j
      simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, hx]
    simp [Bundle.Trivialization.localFrameCoeff, IsLocalFrameOn.coeff,
      hx, hbasis, basis]
  rw [hcoeff k]
  change (basis.coord k) (metricConnectionDifferenceVector cov cov' x) = _
  rw [metricConnectionDifferenceVector_eq_sum_inverseGram cov cov' x basis]
  simp_rw [map_sum, map_smul, smul_eq_mul, hG, hframe,
    Module.Basis.coord_apply, ← hcoeff]

/-- Equal Levi-Civita connections give zero metric contraction, as required
for the existing Ricci-flat and chosen-background special cases. -/
theorem metricConnectionDifferenceVector_eq_zero_of_isLeviCivita
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita) (x : M) :
    metricConnectionDifferenceVector cov cov' x = 0 := by
  have hD := difference_eq_zero_of_isLeviCivita cov cov' hcov hcov'
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  have hB : metricConnectionDifferenceBilinear cov cov' x = 0 := by
    ext u v
    change CovariantDerivative.difference cov cov' x u v = 0
    rw [hD]
    rfl
  rw [metricConnectionDifferenceVector, hB]
  exact PoincareCurvature.metricBilinearContraction_zero

end CovariantDerivative

namespace RicciFlow

variable [SigmaCompactSpace M]

/-- The conventional positive DeTurck vector, using the actual chosen
Levi-Civita connection of the metric and the caller's background connection. -/
noncomputable def metricContractedDeTurckVectorField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  fun t x => by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    exact CovariantDerivative.metricConnectionDifferenceVector
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x

/-- The recovery gauge has the negative sign. Its analytic flow is a separate
construction, not supplied by this abbreviation. -/
noncomputable def metricContractedDeTurckGaugeField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  -metricContractedDeTurckVectorField g background

/-- For an evolving Levi-Civita background the conventional field vanishes
too. This special case does not construct a fixed-background parabolic flow. -/
theorem metricContractedDeTurckVectorField_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    metricContractedDeTurckVectorField (I := I) (M := M) g background = 0 := by
  funext t x
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) := by
    infer_instance
  letI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) := by
    infer_instance
  change CovariantDerivative.metricConnectionDifferenceVector
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x = 0
  exact CovariantDerivative.metricConnectionDifferenceVector_eq_zero_of_isLeviCivita
    _ _ ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g) t)
    (hbackground t) x

end RicciFlow
