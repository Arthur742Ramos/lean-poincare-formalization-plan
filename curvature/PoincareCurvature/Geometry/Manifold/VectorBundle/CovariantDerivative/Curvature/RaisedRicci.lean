module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.EndomorphismTrace
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional

/-!
# The metric-raised Ricci endomorphism

This file packages the Ricci tensor as a genuine tangent-bundle endomorphism by
raising its second covariant index with the Riemannian metric. Its trace is
proved to be the scalar curvature already defined from the curvature tensor.
For a torsion-free metric-compatible connection, the endomorphism is symmetric,
so it is the appropriate intrinsic input to finite-dimensional spectral
arguments.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [hContTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Ricci curvature with its second index raised by the Riemannian metric.
No symmetrization or projection occurs in this definition. -/
def raisedRicciEndomorphism
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) : TM x →L[ℝ] TM x :=
  (rieszMap (I := I) x).comp (ricciCovariantTwoTensor cov x)

/-- The defining pairing identity for the raised Ricci endomorphism. -/
@[simp] theorem inner_raisedRicciEndomorphism
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u v : TM x) :
    inner ℝ (raisedRicciEndomorphism cov x u) v =
      ricciCurvature (cov := cov) x u v := by
  change inner ℝ ((InnerProductSpace.toDual ℝ (TM x)).symm _) v = _
  exact InnerProductSpace.toDual_symm_apply

/-- The ordinary endomorphism trace of raised Ricci is the geometric scalar
curvature obtained by contracting the actual connection curvature. -/
theorem endomorphismTrace_raisedRicciEndomorphism_eq_scalarCurvature
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) :
    endomorphismTrace (F := E) (V := TM) (raisedRicciEndomorphism cov) x =
      scalarCurvature (cov := cov) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [endomorphismTrace, LinearMap.trace_eq_sum_inner _ b,
    scalarCurvature_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [raisedRicciEndomorphism, real_inner_comm] using
    inner_raisedRicciEndomorphism cov x (b i) (b i)

/-- Scalar curvature is the sum of Ricci diagonal entries in every
orthonormal basis, not only the basis chosen in its original definition. -/
theorem scalarCurvature_eq_sum_ricci_orthonormalBasis
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) :
    scalarCurvature (cov := cov) x =
      ∑ i, ricciCurvature (cov := cov) x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [← endomorphismTrace_raisedRicciEndomorphism_eq_scalarCurvature cov x,
    endomorphismTrace, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    inner ℝ (b i) (raisedRicciEndomorphism cov x (b i)) =
        inner ℝ (raisedRicciEndomorphism cov x (b i)) (b i) :=
      real_inner_comm _ _
    _ = ricciCurvature (cov := cov) x (b i) (b i) :=
      inner_raisedRicciEndomorphism cov x (b i) (b i)

/-! ## Differentiating the Ricci trace

The tangent bundle carries both its model-space norm and the norm induced by
the Riemannian metric.  They induce the same finite-dimensional topology but
are not definitionally equal in Lean.  The next two definitions keep the
model-space choice internal, so the mathematical statement does not expose an
implementation-dependent norm instance. -/

section DifferentiatedTrace

variable [IsManifold I 1 M]

/-- The covariant derivative of raised Ricci, evaluated on its derivative and
endomorphism arguments.  The model-space tangent norm is kept internal to
avoid exposing the equivalent Riemannian/model norm implementations. -/
def raisedRicciCovariantDerivativeApply
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u v : TM x) : TM x := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TM y →L[ℝ] TM y := fun y => @raisedRicciEndomorphism
    E _ _ _ _ H _ I M _ _ _ _ hContTangent _ cov _ y
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  exact d A x u v

/-- The fibre trace of the covariant derivative of raised Ricci. -/
def raisedRicciTraceCovariantDerivative
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u : TM x) : ℝ := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TM y →L[ℝ] TM y := fun y => @raisedRicciEndomorphism
    E _ _ _ _ H _ I M _ _ _ _ hContTangent _ cov _ y
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  exact LinearMap.trace ℝ (TM x) ((d A x u).toLinearMap)

/-- In every finite basis, the trace of the covariant derivative of raised
Ricci is the sum of its diagonal coefficients. -/
theorem raisedRicciTraceCovariantDerivative_eq_sum_basis
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u : TM x) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (TM x)) :
    raisedRicciTraceCovariantDerivative cov x u =
      ∑ i, b.repr (raisedRicciCovariantDerivativeApply cov x u (b i)) i := by
  classical
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TM y →L[ℝ] TM y := fun y => @raisedRicciEndomorphism
    E _ _ _ _ H _ I M _ _ _ _ hContTangent _ cov _ y
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  let L : TM x →ₗ[ℝ] TM x := (d A x u).toLinearMap
  change LinearMap.trace ℝ (TM x) L = ∑ i, b.repr (L (b i)) i
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  apply Finset.sum_congr rfl
  intro i hi
  change LinearMap.toMatrix b b L i i = _
  rw [LinearMap.toMatrix_apply]

/-- Regularity of the genuine metric-raised Ricci endomorphism at a point. -/
def raisedRicciEndomorphismMDiffAt
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) : Prop := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TM y →L[ℝ] TM y := fun y => @raisedRicciEndomorphism
    E _ _ _ _ H _ I M _ _ _ _ hContTangent _ cov _ y
  exact MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun z : M => TM z →L[ℝ] TM z) y (A y)) x

/-- Differentiating the geometric identity `tr Ric♯ = R` shows that the
scalar differential is the trace of the induced covariant derivative of
raised Ricci. -/
theorem scalarDifferential_scalarCurvature_eq_raisedRicciTrace
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (hRicci : raisedRicciEndomorphismMDiffAt cov x) (u : TM x) :
    scalarDifferential (I := I) (scalarCurvature (cov := cov)) x u =
      raisedRicciTraceCovariantDerivative cov x u := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TM y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TM y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TM y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TM y →L[ℝ] TM y := fun y => @raisedRicciEndomorphism
    E _ _ _ _ H _ I M _ _ _ _ hContTangent _ cov _ y
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    TM TM _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  let trA : M → ℝ := @endomorphismTrace
    E _ _ M _ _ TM nTM sTM _
    TangentSpace.fiberBundle TangentSpace.vectorBundle A
  change MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TM z →L[ℝ] TM z) y (A y)) x at hRicci
  change scalarDifferential (I := I) (scalarCurvature (cov := cov)) x u =
    LinearMap.trace ℝ (TM x) ((d A x u).toLinearMap)
  have heq : scalarCurvature (cov := cov) = trA := by
    funext y
    exact (endomorphismTrace_raisedRicciEndomorphism_eq_scalarCurvature
      cov y).symm
  change mvfderiv (I := I) (scalarCurvature (cov := cov)) x u = _
  rw [heq]
  exact @mvfderiv_endomorphismTrace_eq_trace_inducedHom
    E E _ _ _ _ H _ I M _ _ _ _ _ _ _ _
    TM nTM sTM _ TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent _ fTM cov A x hRicci u

end DifferentiatedTrace

/-- Ricci curvature is the first/output trace of the actual curvature tensor
in every orthonormal basis. -/
theorem ricciCurvature_eq_sum_curvature_orthonormalBasis
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) (u v : TM x) :
    ricciCurvature (cov := cov) x u v =
      ∑ i, inner ℝ (b i) (curvatureTensor (cov := cov) x (b i) u v) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [ricciCurvature_apply, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- For a metric-compatible connection, a diagonal Ricci component is the
sum of the sectional-curvature numerators through that unit basis vector. -/
theorem ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) (j : ι) :
    ricciCurvature (cov := cov) x (b j) (b j) =
      ∑ i, sectionalCurvatureNumerator (cov := cov) x (b j) (b i) := by
  rw [ricciCurvature_eq_sum_curvature_orthonormalBasis cov x b]
  apply Finset.sum_congr rfl
  intro i hi
  have hswap := curvatureTensor_swap (cov := cov) x (b i) (b j) (b j)
  have hskew :=
    curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
      (covTM := cov) hmetric x (b j) (b i) (b j) (b i)
  rw [sectionalCurvatureNumerator_def]
  rw [hswap, inner_neg_right]
  have hcomm₁ : inner ℝ (b i)
      (curvatureTensor (cov := cov) x (b j) (b i) (b j)) =
      inner ℝ (curvatureTensor (cov := cov) x (b j) (b i) (b j)) (b i) :=
    real_inner_comm _ _
  have hcomm₂ : inner ℝ (b j)
      (curvatureTensor (cov := cov) x (b j) (b i) (b i)) =
      inner ℝ (curvatureTensor (cov := cov) x (b j) (b i) (b i)) (b j) :=
    real_inner_comm _ _
  linarith

/-- Metric compatibility makes the sectional-curvature numerator independent
of the ordering of the spanning pair. -/
theorem sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M) (u v : TM x) :
    sectionalCurvatureNumerator (cov := cov) x u v =
      sectionalCurvatureNumerator (cov := cov) x v u := by
  have hswap := curvatureTensor_swap (cov := cov) x v u u
  have hskew :=
    curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
      (covTM := cov) hmetric x u v u v
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
    hswap, inner_neg_left]
  have hcomm : inner ℝ u (curvatureTensor (cov := cov) x u v v) =
      inner ℝ (curvatureTensor (cov := cov) x u v v) u :=
    real_inner_comm _ _
  linarith

private theorem ricciCurvature_basis_zero_finrank_three
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M)
    (b : OrthonormalBasis (Fin 3) ℝ (TM x)) :
    ricciCurvature (cov := cov) x (b 0) (b 0) =
      sectionalCurvatureNumerator (cov := cov) x (b 0) (b 1) +
        sectionalCurvatureNumerator (cov := cov) x (b 0) (b 2) := by
  rw [ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 0]
  simp [Fin.sum_univ_succ]

/-- For a torsion-free metric-compatible connection, raised Ricci is a
symmetric endomorphism. The proof uses the geometric Ricci-symmetry theorem,
not a symmetrized definition. -/
theorem raisedRicciEndomorphism_isSymmetric
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) :
    (raisedRicciEndomorphism cov x).toLinearMap.IsSymmetric := by
  intro u v
  calc
    inner ℝ ((raisedRicciEndomorphism cov x) u) v =
        ricciCurvature (cov := cov) x u v :=
      inner_raisedRicciEndomorphism cov x u v
    _ = ricciCurvature (cov := cov) x v u :=
      ricciCurvature_symm_of_metricCompatibleTangent_of_torsion_eq_zero
        (cov := cov) hT hmetric x u v
    _ = inner ℝ ((raisedRicciEndomorphism cov x) v) u :=
      (inner_raisedRicciEndomorphism cov x v u).symm
    _ = inner ℝ u ((raisedRicciEndomorphism cov x) v) := real_inner_comm _ _

/-! ## The Ricci-complement operator -/

/-- The Ricci-complement endomorphism `R Id - 2 Ric♯`. In dimension three,
identifying this operator's spectrum with the curvature-operator spectrum is
the remaining algebraic bridge to the Hamilton--Ivey normalization. -/
def ricciComplementEndomorphism
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) : TM x →L[ℝ] TM x :=
  scalarCurvature (cov := cov) x • ContinuousLinearMap.id ℝ (TM x) -
    (2 : ℝ) • raisedRicciEndomorphism cov x

@[simp] theorem ricciComplementEndomorphism_apply
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u : TM x) :
    ricciComplementEndomorphism cov x u =
      scalarCurvature (cov := cov) x • u -
        (2 : ℝ) • (raisedRicciEndomorphism cov x u) := by
  simp [ricciComplementEndomorphism]

/-- The quadratic form of the Ricci-complement endomorphism is
`R |u|² - 2 Ric(u,u)`. -/
theorem inner_ricciComplementEndomorphism
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u : TM x) :
    inner ℝ (ricciComplementEndomorphism cov x u) u =
      scalarCurvature (cov := cov) x * ‖u‖ ^ 2 -
        2 * ricciCurvature (cov := cov) x u u := by
  rw [ricciComplementEndomorphism_apply, inner_sub_left,
    real_inner_smul_left, real_inner_smul_left,
    inner_raisedRicciEndomorphism,
    real_inner_self_eq_norm_sq]

/-- In an orthonormal three-frame, the Ricci-complement quadratic form on the
first basis vector is twice the sectional curvature numerator of the
complementary plane. This is the first explicit geometric bridge to the
Hamilton--Ivey curvature-operator normalization. -/
theorem inner_ricciComplementEndomorphism_basis_zero_finrank_three
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M)
    (b : OrthonormalBasis (Fin 3) ℝ (TM x)) :
    inner ℝ (ricciComplementEndomorphism cov x (b 0)) (b 0) =
      2 * sectionalCurvatureNumerator (cov := cov) x (b 1) (b 2) := by
  have hscalar := scalarCurvature_eq_sum_ricci_orthonormalBasis cov x b
  have hr0 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 0
  have hr1 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 1
  have hr2 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 2
  rw [Fin.sum_univ_three] at hscalar hr0 hr1 hr2
  have h01 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 1)
  have h02 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 2)
  have h12 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 1) (b 2)
  have h00 : sectionalCurvatureNumerator (cov := cov) x (b 0) (b 0) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h11 : sectionalCurvatureNumerator (cov := cov) x (b 1) (b 1) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h22 : sectionalCurvatureNumerator (cov := cov) x (b 2) (b 2) = 0 := by
    simp [sectionalCurvatureNumerator]
  rw [inner_ricciComplementEndomorphism]
  have hnorm : ‖b 0‖ ^ 2 = 1 := by simp
  rw [hnorm]
  linarith

/-- The corresponding complementary-plane formula for the second vector of
an orthonormal three-frame. -/
theorem inner_ricciComplementEndomorphism_basis_one_finrank_three
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M)
    (b : OrthonormalBasis (Fin 3) ℝ (TM x)) :
    inner ℝ (ricciComplementEndomorphism cov x (b 1)) (b 1) =
      2 * sectionalCurvatureNumerator (cov := cov) x (b 0) (b 2) := by
  have hscalar := scalarCurvature_eq_sum_ricci_orthonormalBasis cov x b
  have hr0 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 0
  have hr1 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 1
  have hr2 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 2
  rw [Fin.sum_univ_three] at hscalar hr0 hr1 hr2
  have h01 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 1)
  have h02 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 2)
  have h12 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 1) (b 2)
  have h00 : sectionalCurvatureNumerator (cov := cov) x (b 0) (b 0) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h11 : sectionalCurvatureNumerator (cov := cov) x (b 1) (b 1) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h22 : sectionalCurvatureNumerator (cov := cov) x (b 2) (b 2) = 0 := by
    simp [sectionalCurvatureNumerator]
  rw [inner_ricciComplementEndomorphism]
  have hnorm : ‖b 1‖ ^ 2 = 1 := by simp
  rw [hnorm]
  linarith

/-- The corresponding complementary-plane formula for the third vector of
an orthonormal three-frame. -/
theorem inner_ricciComplementEndomorphism_basis_two_finrank_three
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent) (x : M)
    (b : OrthonormalBasis (Fin 3) ℝ (TM x)) :
    inner ℝ (ricciComplementEndomorphism cov x (b 2)) (b 2) =
      2 * sectionalCurvatureNumerator (cov := cov) x (b 0) (b 1) := by
  have hscalar := scalarCurvature_eq_sum_ricci_orthonormalBasis cov x b
  have hr0 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 0
  have hr1 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 1
  have hr2 := ricciCurvature_eq_sum_sectionalCurvatureNumerator_orthonormalBasis
    cov hmetric x b 2
  rw [Fin.sum_univ_three] at hscalar hr0 hr1 hr2
  have h01 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 1)
  have h02 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 0) (b 2)
  have h12 := sectionalCurvatureNumerator_comm_of_isMetricCompatibleTangent
    cov hmetric x (b 1) (b 2)
  have h00 : sectionalCurvatureNumerator (cov := cov) x (b 0) (b 0) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h11 : sectionalCurvatureNumerator (cov := cov) x (b 1) (b 1) = 0 := by
    simp [sectionalCurvatureNumerator]
  have h22 : sectionalCurvatureNumerator (cov := cov) x (b 2) (b 2) = 0 := by
    simp [sectionalCurvatureNumerator]
  rw [inner_ricciComplementEndomorphism]
  have hnorm : ‖b 2‖ ^ 2 = 1 := by simp
  rw [hnorm]
  linarith

/-- In tangent dimension three, the Ricci-complement operator has trace equal
to scalar curvature. -/
theorem endomorphismTrace_ricciComplementEndomorphism_eq_scalarCurvature_of_finrank_eq_three
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    endomorphismTrace (F := E) (V := TM)
        (ricciComplementEndomorphism cov) x =
      scalarCurvature (cov := cov) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [endomorphismTrace, ricciComplementEndomorphism]
  change LinearMap.trace ℝ (TM x)
      (scalarCurvature (cov := cov) x • LinearMap.id -
        (2 : ℝ) • (raisedRicciEndomorphism cov x).toLinearMap) = _
  have htrace : LinearMap.trace ℝ (TM x)
      (raisedRicciEndomorphism cov x).toLinearMap =
        scalarCurvature (cov := cov) x := by
    simpa only [endomorphismTrace] using
      endomorphismTrace_raisedRicciEndomorphism_eq_scalarCurvature cov x
  rw [map_sub, map_smul, map_smul, LinearMap.trace_id, htrace]
  rw [hdim]
  ring

/-- The Ricci-complement curvature endomorphism is symmetric whenever Ricci is
symmetric. -/
theorem ricciComplementEndomorphism_isSymmetric
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) :
    (ricciComplementEndomorphism cov x).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ
      (scalarCurvature (cov := cov) x • u -
        (2 : ℝ) • (raisedRicciEndomorphism cov x u)) v =
    inner ℝ u
      (scalarCurvature (cov := cov) x • v -
        (2 : ℝ) • (raisedRicciEndomorphism cov x v))
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  have hright : inner ℝ u (raisedRicciEndomorphism cov x v) =
      ricciCurvature (cov := cov) x v u := by
    rw [real_inner_comm]
    exact inner_raisedRicciEndomorphism cov x v u
  rw [inner_raisedRicciEndomorphism cov x u v,
    ricciCurvature_symm_of_metricCompatibleTangent_of_torsion_eq_zero
      (cov := cov) hT hmetric x u v,
    hright]

/-- In dimension three, the three eigenvalues of the Ricci-complement
endomorphism, sorted in decreasing order. -/
def ricciComplementEigenvalues
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) : Fin 3 → ℝ :=
  (ricciComplementEndomorphism_isSymmetric cov hT hmetric x).eigenvalues hdim

/-- The corresponding orthonormal eigenbasis, ordered by decreasing
Ricci-complement eigenvalue. -/
def ricciComplementEigenbasis
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    OrthonormalBasis (Fin 3) ℝ (TM x) :=
  (ricciComplementEndomorphism_isSymmetric cov hT hmetric x).eigenvectorBasis hdim

/-- Each vector of the selected orthonormal basis is an eigenvector with the
correspondingly ordered eigenvalue. -/
@[simp] theorem ricciComplementEndomorphism_apply_eigenbasis
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) (i : Fin 3) :
    ricciComplementEndomorphism cov x
        (ricciComplementEigenbasis cov hT hmetric x hdim i) =
      ricciComplementEigenvalues cov hT hmetric x hdim i •
        ricciComplementEigenbasis cov hT hmetric x hdim i := by
  exact (ricciComplementEndomorphism_isSymmetric cov hT hmetric x).apply_eigenvectorBasis
    hdim i

/-- The largest Ricci-complement eigenvalue is twice the sectional curvature
of the plane complementary to its eigenvector in the selected eigenframe. -/
theorem ricciComplementEigenvalue_zero_eq_two_sectionalCurvatureNumerator
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    ricciComplementEigenvalues cov hT hmetric x hdim 0 =
      2 * sectionalCurvatureNumerator (cov := cov) x
        (ricciComplementEigenbasis cov hT hmetric x hdim 1)
        (ricciComplementEigenbasis cov hT hmetric x hdim 2) := by
  let b := ricciComplementEigenbasis cov hT hmetric x hdim
  have hdiag := inner_ricciComplementEndomorphism_basis_zero_finrank_three
    cov hmetric x b
  have happ := ricciComplementEndomorphism_apply_eigenbasis
    cov hT hmetric x hdim 0
  have hinner := congrArg (fun z : TM x => inner ℝ z (b 0)) happ
  have hnorm : inner ℝ (b 0) (b 0) = 1 := by simp
  rw [real_inner_smul_left, hnorm, mul_one] at hinner
  exact hinner.symm.trans hdiag

/-- The middle Ricci-complement eigenvalue is twice the sectional curvature
of its complementary eigenplane. -/
theorem ricciComplementEigenvalue_one_eq_two_sectionalCurvatureNumerator
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    ricciComplementEigenvalues cov hT hmetric x hdim 1 =
      2 * sectionalCurvatureNumerator (cov := cov) x
        (ricciComplementEigenbasis cov hT hmetric x hdim 0)
        (ricciComplementEigenbasis cov hT hmetric x hdim 2) := by
  let b := ricciComplementEigenbasis cov hT hmetric x hdim
  have hdiag := inner_ricciComplementEndomorphism_basis_one_finrank_three
    cov hmetric x b
  have happ := ricciComplementEndomorphism_apply_eigenbasis
    cov hT hmetric x hdim 1
  have hinner := congrArg (fun z : TM x => inner ℝ z (b 1)) happ
  have hnorm : inner ℝ (b 1) (b 1) = 1 := by simp
  rw [real_inner_smul_left, hnorm, mul_one] at hinner
  exact hinner.symm.trans hdiag

/-- The least Ricci-complement eigenvalue is twice the sectional curvature
of its complementary eigenplane. -/
theorem ricciComplementEigenvalue_two_eq_two_sectionalCurvatureNumerator
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    ricciComplementEigenvalues cov hT hmetric x hdim 2 =
      2 * sectionalCurvatureNumerator (cov := cov) x
        (ricciComplementEigenbasis cov hT hmetric x hdim 0)
        (ricciComplementEigenbasis cov hT hmetric x hdim 1) := by
  let b := ricciComplementEigenbasis cov hT hmetric x hdim
  have hdiag := inner_ricciComplementEndomorphism_basis_two_finrank_three
    cov hmetric x b
  have happ := ricciComplementEndomorphism_apply_eigenbasis
    cov hT hmetric x hdim 2
  have hinner := congrArg (fun z : TM x => inner ℝ z (b 2)) happ
  have hnorm : inner ℝ (b 2) (b 2) = 1 := by simp
  rw [real_inner_smul_left, hnorm, mul_one] at hinner
  exact hinner.symm.trans hdiag

/-- The three Ricci-complement eigenvalues are ordered decreasingly. -/
theorem ricciComplementEigenvalues_antitone
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    Antitone (ricciComplementEigenvalues cov hT hmetric x hdim) :=
  (ricciComplementEndomorphism_isSymmetric cov hT hmetric x).eigenvalues_antitone hdim

/-- Hamilton--Ivey's largest curvature-operator eigenvalue in the convention
where an eigenvalue is twice the corresponding sectional curvature. -/
def threeDimensionalCurvatureLambda
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) : ℝ :=
  ricciComplementEigenvalues cov hT hmetric x hdim 0

/-- Hamilton--Ivey's middle curvature-operator eigenvalue. -/
def threeDimensionalCurvatureMu
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) : ℝ :=
  ricciComplementEigenvalues cov hT hmetric x hdim 1

/-- Hamilton--Ivey's least curvature-operator eigenvalue. -/
def threeDimensionalCurvatureNu
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) : ℝ :=
  ricciComplementEigenvalues cov hT hmetric x hdim 2

/-- The largest curvature eigenvalue dominates the middle one. -/
theorem threeDimensionalCurvatureLambda_ge_mu
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    threeDimensionalCurvatureMu cov hT hmetric x hdim ≤
      threeDimensionalCurvatureLambda cov hT hmetric x hdim := by
  exact ricciComplementEigenvalues_antitone cov hT hmetric x hdim (by decide)

/-- The middle curvature eigenvalue dominates the least one. -/
theorem threeDimensionalCurvatureMu_ge_nu
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    threeDimensionalCurvatureNu cov hT hmetric x hdim ≤
      threeDimensionalCurvatureMu cov hT hmetric x hdim := by
  exact ricciComplementEigenvalues_antitone cov hT hmetric x hdim (by decide)

/-- The sum of the three Ricci-complement eigenvalues is scalar curvature. -/
theorem sum_ricciComplementEigenvalues_eq_scalarCurvature
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    (∑ i : Fin 3, ricciComplementEigenvalues cov hT hmetric x hdim i) =
      scalarCurvature (cov := cov) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let hs := ricciComplementEndomorphism_isSymmetric cov hT hmetric x
  have htrace := hs.trace_eq_sum_eigenvalues hdim
  have hgeom :=
    endomorphismTrace_ricciComplementEndomorphism_eq_scalarCurvature_of_finrank_eq_three
      cov x hdim
  rw [endomorphismTrace] at hgeom
  exact htrace.symm.trans hgeom

/-- In the Hamilton--Ivey normalization, scalar curvature is exactly
`lambda + mu + nu`. -/
theorem threeDimensionalCurvatureLambda_add_mu_add_nu_eq_scalarCurvature
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    threeDimensionalCurvatureLambda cov hT hmetric x hdim +
        threeDimensionalCurvatureMu cov hT hmetric x hdim +
        threeDimensionalCurvatureNu cov hT hmetric x hdim =
      scalarCurvature (cov := cov) x := by
  have hsum := sum_ricciComplementEigenvalues_eq_scalarCurvature
    cov hT hmetric x hdim
  rw [Fin.sum_univ_three] at hsum
  exact hsum

end CovariantDerivative
