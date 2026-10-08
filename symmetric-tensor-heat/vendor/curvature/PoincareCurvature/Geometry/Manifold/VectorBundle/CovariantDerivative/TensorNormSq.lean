module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TraceLaplacian

/-!
# Pointwise norm square of a covariant two-tensor

The Hilbert--Schmidt square is the sum of squared tensor components in a
fibrewise orthonormal basis. Its nonnegativity and definiteness are the
algebraic part of the tensor-heat maximum-principle argument. The Bochner
evolution identity remains a separate differential theorem.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

local instance tensorNormTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance tensorNormTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance tensorNormTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance tensorNormTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance tensorNormThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance tensorNormThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance tensorNormThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance tensorNormThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- Pointwise Hilbert--Schmidt square of an arbitrary covariant two-tensor. -/
def covariantTwoTensorNormSq (h : ∀ x : M, T₂ x) (x : M) : ℝ := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, ∑ j, (h x (b i) (b j)) ^ 2

theorem covariantTwoTensorNormSq_eq_sum
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x =
      (by
        let _ : FiniteDimensional ℝ (TM x) :=
          VectorBundle.finiteDimensional ℝ E TM x
        let b := stdOrthonormalBasis ℝ (TM x)
        exact ∑ i, ∑ j, (h x (b i) (b j)) ^ 2) := by
  rfl

theorem covariantTwoTensorNormSq_nonneg
    (h : ∀ x : M, T₂ x) (x : M) :
    0 ≤ covariantTwoTensorNormSq h x := by
  rw [covariantTwoTensorNormSq_eq_sum]
  positivity

/-- The norm square is the intrinsic trace of the adjoint-square of the
raised tensor. In particular, the orthonormal-basis formula is independent of
the basis chosen at the point. -/
theorem covariantTwoTensorNormSq_eq_trace_adjoint_comp
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x =
      (by
        let _ : FiniteDimensional ℝ (TM x) :=
          VectorBundle.finiteDimensional ℝ E TM x
        let A : TM x →ₗ[ℝ] TM x :=
          (raisedCovariantTwoTensor (I := I) (E := E) h x).toLinearMap
        exact LinearMap.trace ℝ (TM x) (A.adjoint.comp A)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x :=
    (raisedCovariantTwoTensor (I := I) (E := E) h x).toLinearMap
  have hnorm : covariantTwoTensorNormSq h x =
      ∑ i, ‖A (b i)‖ ^ 2 := by
    rw [covariantTwoTensorNormSq_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hparse := b.sum_sq_inner_left (A (b i))
    calc
      ∑ j, (h x (b i) (b j)) ^ 2 =
          ∑ j, (inner ℝ (A (b i)) (b j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        change h x (b i) (b j) =
          inner ℝ (rieszMap (I := I) x (h x (b i))) (b j)
        exact (rieszMap_apply_inner (I := I) x (h x (b i)) (b j)).symm
      _ = ‖A (b i)‖ ^ 2 := hparse
  rw [hnorm, LinearMap.trace_eq_sum_inner (A.adjoint.comp A) b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm]
  change ‖A (b i)‖ ^ 2 =
    inner ℝ (LinearMap.adjoint A (A (b i))) (b i)
  rw [LinearMap.adjoint_inner_left]
  exact (real_inner_self_eq_norm_sq _).symm

/-- The pointwise norm square vanishes exactly when the complete bilinear
form vanishes, including all off-diagonal tensor slots. -/
theorem covariantTwoTensorNormSq_eq_zero_iff
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x = 0 ↔ h x = 0 := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  constructor
  · intro hzero
    rw [covariantTwoTensorNormSq_eq_sum] at hzero
    have hrow (i : Fin (Module.finrank ℝ (TM x))) :
        (∑ j, (h x (b i) (b j)) ^ 2) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => by positivity)).1 hzero i (Finset.mem_univ i)
    have hcoeff (i j : Fin (Module.finrank ℝ (TM x))) :
        h x (b i) (b j) = 0 := by
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (h x (b i) (b k)))).1
          (hrow i) j (Finset.mem_univ j)
      nlinarith only [hsq]
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext (fun i => ?_)
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext (fun j => ?_)
    exact hcoeff i j
  · intro hzero
    rw [covariantTwoTensorNormSq_eq_sum]
    simp [hzero]

/-- The Gram two-tensor of the metric-raised covariant tensor. Its trace is
the complete Hilbert--Schmidt square. -/
def covariantTwoTensorGram (h : ∀ x : M, T₂ x) : ∀ x : M, T₂ x :=
  fun x =>
    let A := raisedCovariantTwoTensor (I := I) (E := E) h x
    ((ContinuousLinearMap.compL ℝ (TM x) (TM x) ℝ).flip A).comp
      ((innerSL ℝ).comp A)

@[simp] theorem covariantTwoTensorGram_apply
    (h : ∀ x : M, T₂ x) (x : M) (u v : TM x) :
    covariantTwoTensorGram h x u v =
      inner ℝ (raisedCovariantTwoTensor (I := I) (E := E) h x u)
        (raisedCovariantTwoTensor (I := I) (E := E) h x v) := by
  rfl

/-- A differentiable covariant tensor has a differentiable Gram tensor when
the Riemannian metric is differentiable. The proof evaluates the Gram tensor
on genuine local frames in both slots. -/
theorem covariantTwoTensorGram_mdifferentiableAt
    [IsContMDiffRiemannianBundle I 2 E TM]
    {h : ∀ y : M, T₂ y} {x₀ : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x₀) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (covariantTwoTensorGram (I := I) (E := E) h y)) x₀ := by
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  have hA := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) hh
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM)
    (E₂ := fun y : M => TM y →L[ℝ] ℝ) x₀ b ?_
  intro i
  let U : ∀ y : M, TM y := fun y => e.localFrame b i y
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hU : MDiffAt (T% U) x₀ :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hAU : MDiffAt (T% (fun y => A y (U y))) x₀ :=
    hA.clm_bundle_apply hU
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (E₂ := Bundle.Trivial M ℝ) x₀ b ?_
  intro j
  let V : ∀ y : M, TM y := fun y => e.localFrame b j y
  have hV : MDiffAt (T% V) x₀ :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := j) (hx := hx)).mdifferentiableAt one_ne_zero
  have hAV : MDiffAt (T% (fun y => A y (V y))) x₀ :=
    hA.clm_bundle_apply hV
  have hscalar : MDiffAt
      (fun y => inner ℝ (A y (U y)) (A y (V y))) x₀ :=
    MDifferentiableAt.inner_bundle (IB := I) (IM := I)
      (F := E) (E := TM) (b := id) hAU hAV
  rw [mdifferentiableAt_section]
  simpa [Bundle.Trivial.eq_trivialization M ℝ, U, V,
    covariantTwoTensorGram_apply, A] using hscalar

/-- The tensor energy is an ordinary metric trace of a genuine Gram
two-tensor. This form can be fed into the existing intrinsic trace--Laplacian
theorem when proving the spatial Bochner identity. -/
theorem covariantTwoTensorNormSq_eq_trace_gram
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorNormSq h x =
      covariantTwoTensorTraceFunction (I := I) (E := E)
        (covariantTwoTensorGram (I := I) (E := E) h) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x :=
    (raisedCovariantTwoTensor (I := I) (E := E) h x).toLinearMap
  rw [covariantTwoTensorNormSq_eq_trace_adjoint_comp,
    LinearMap.trace_eq_sum_inner (A.adjoint.comp A) b]
  rw [covariantTwoTensorTraceFunction,
    covariantTwoTensorTrace_eq_sum_orthonormalBasis
      (I := I) (E := E) (M := M)
      (covariantTwoTensorLinear (I := I) (M := M)
        (covariantTwoTensorGram (I := I) (E := E) h)) x b]
  apply Finset.sum_congr rfl
  intro i hi
  change inner ℝ (b i) (A.adjoint (A (b i))) =
    inner ℝ (A (b i)) (A (b i))
  rw [LinearMap.adjoint_inner_right]

/-- Spatial differentiability of the complete tensor norm square follows
from differentiability of the tensor and the Riemannian metric. -/
theorem covariantTwoTensorNormSq_mdifferentiableAt
    [IsContMDiffRiemannianBundle I 2 E TM]
    {h : ∀ y : M, T₂ y} {x₀ : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x₀) :
    MDiffAt (covariantTwoTensorNormSq (I := I) (E := E) h) x₀ := by
  let gram := covariantTwoTensorGram (I := I) (E := E) h
  have hgram := covariantTwoTensorGram_mdifferentiableAt
    (I := I) (E := E) (M := M) hh
  have hraised := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) hgram
  have htrace := mdifferentiableAt_endomorphismTrace
    (F := E) (V := TM) hraised
  have heq : covariantTwoTensorNormSq (I := I) (E := E) h =
      covariantTwoTensorTraceFunction (I := I) (E := E) gram := by
    funext x
    exact covariantTwoTensorNormSq_eq_trace_gram h x
  rw [heq, covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised]
  exact htrace

/-- Metric compatibility and differentiability of the covariant derivative
of the Gram tensor give differentiability of the energy's scalar gradient. -/
theorem mdifferentiableAt_scalarDifferential_covariantTwoTensorNormSq
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) z (h z)) y)
    {x : M}
    (hfirstGram : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorNormSq (I := I) (E := E) h) y)) x := by
  let gram := covariantTwoTensorGram (I := I) (E := E) h
  have hraised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E) gram z)) y := by
    intro y
    exact raisedCovariantTwoTensor_mdifferentiableAt
      (covariantTwoTensorGram_mdifferentiableAt (hh y))
  have heq : covariantTwoTensorNormSq (I := I) (E := E) h =
      covariantTwoTensorTraceFunction (I := I) (E := E) gram := by
    funext y
    exact covariantTwoTensorNormSq_eq_trace_gram h y
  rw [heq]
  exact mdifferentiableAt_scalarDifferential_covariantTwoTensorTraceFunction
    cov hmetric gram hraised hfirstGram

/-- The scalar Laplacian of the complete tensor energy is the metric trace
of the genuine connection Laplacian of its Gram tensor. This follows from the
existing intrinsic trace--Laplacian theorem; expanding the Laplacian of the
Gram tensor into the tensor Bochner formula is a separate step. -/
theorem scalarLaplacian_covariantTwoTensorNormSq_eq_trace_laplacian_gram
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) z (h z)) y)
    {x : M}
    (hfirstGram : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x) :
    scalarLaplacian cov (covariantTwoTensorNormSq (I := I) (E := E) h) x =
      covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x := by
  let gram := covariantTwoTensorGram (I := I) (E := E) h
  have hgram : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
          (E := T₂) z (gram z)) y := by
    intro y
    exact covariantTwoTensorGram_mdifferentiableAt (hh y)
  have hraised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E) gram z)) y := by
    intro y
    exact raisedCovariantTwoTensor_mdifferentiableAt (hgram y)
  have hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) gram) y)) x :=
    mdifferentiableAt_scalarDifferential_covariantTwoTensorTraceFunction
      cov hmetric gram hraised hfirstGram
  have hsecondRaised (Y : TM x) :
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E)
            (covariantTwoTensorDerivativeAlong cov gram
              (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x := by
    have hY : MDiffAt
        (T% (smoothExtend (I := I) (F := E) (V := TM) x Y)) x :=
      ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y).of_le
        (by norm_num) x).mdifferentiableAt one_ne_zero
    have hderiv := hfirstGram.clm_bundle_apply hY
    exact raisedCovariantTwoTensor_mdifferentiableAt hderiv
  have heq : covariantTwoTensorNormSq (I := I) (E := E) h =
      covariantTwoTensorTraceFunction (I := I) (E := E) gram := by
    funext y
    exact covariantTwoTensorNormSq_eq_trace_gram h y
  rw [heq]
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  exact scalarLaplacian_covariantTwoTensorTraceFunction_eq_covariantTwoTensorTrace_connectionLaplacian
    cov hmetric gram hraised hfirstGram hdf hsecondRaised
      (stdOrthonormalBasis ℝ (TM x))

/-- The fibrewise Hilbert--Schmidt pairing of complete covariant two-tensors. -/
def covariantTwoTensorPair
    (h k : ∀ x : M, T₂ x) (x : M) : ℝ := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, ∑ j, h x (b i) (b j) * k x (b i) (b j)

theorem covariantTwoTensorPair_self
    (h : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorPair h h x = covariantTwoTensorNormSq h x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  unfold covariantTwoTensorPair covariantTwoTensorNormSq
  simp only [← sq]

theorem covariantTwoTensorPair_add_right
    (h k l : ∀ x : M, T₂ x) (x : M) :
    covariantTwoTensorPair h (fun y => k y + l y) x =
      covariantTwoTensorPair h k x + covariantTwoTensorPair h l x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  unfold covariantTwoTensorPair
  simp only [add_apply, mul_add, Finset.sum_add_distrib]

/-- The elementary energy bound used to estimate a bounded curvature
reaction: twice the tensor pairing is at most the sum of the two complete
tensor squares. -/
theorem two_mul_covariantTwoTensorPair_le_normSq_add
    (h k : ∀ x : M, T₂ x) (x : M) :
    2 * covariantTwoTensorPair h k x ≤
      covariantTwoTensorNormSq h x + covariantTwoTensorNormSq k x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  change 2 * (∑ i, ∑ j, h x (b i) (b j) * k x (b i) (b j)) ≤
    (∑ i, ∑ j, (h x (b i) (b j)) ^ 2) +
      ∑ i, ∑ j, (k x (b i) (b j)) ^ 2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  nlinarith only [sq_nonneg (h x (b i) (b j) - k x (b i) (b j))]

/-- A fibrewise square bound on a linear reaction tensor gives the scalar
zero-order bound required by the norm maximum principle. -/
theorem two_mul_covariantTwoTensorPair_le_potential
    (h k : ∀ x : M, T₂ x) (x : M) (C : ℝ)
    (hk : covariantTwoTensorNormSq k x ≤
      C * covariantTwoTensorNormSq h x) :
    2 * covariantTwoTensorPair h k x ≤
      (1 + C) * covariantTwoTensorNormSq h x := by
  calc
    2 * covariantTwoTensorPair h k x ≤
        covariantTwoTensorNormSq h x + covariantTwoTensorNormSq k x :=
      two_mul_covariantTwoTensorPair_le_normSq_add h k x
    _ ≤ covariantTwoTensorNormSq h x +
        C * covariantTwoTensorNormSq h x := add_le_add_right hk _
    _ = (1 + C) * covariantTwoTensorNormSq h x := by ring

/-- The time derivative of the pointwise tensor norm square is twice the
Hilbert--Schmidt pairing with the tensor's genuine time derivative. The
Riemannian metric is fixed in time here. -/
theorem hasDerivAt_covariantTwoTensorNormSq
    (h dh : ℝ → ∀ x : M, T₂ x) (t : ℝ) (x : M)
    (htime : ∀ u v : TM x,
      HasDerivAt (fun s => h s x u v) (dh t x u v) t) :
    HasDerivAt (fun s => covariantTwoTensorNormSq (h s) x)
      (by
        let _ : FiniteDimensional ℝ (TM x) :=
          VectorBundle.finiteDimensional ℝ E TM x
        let b := stdOrthonormalBasis ℝ (TM x)
        exact ∑ i, ∑ j,
          2 * h t x (b i) (b j) * dh t x (b i) (b j)) t := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  change HasDerivAt
    (fun s => ∑ i, ∑ j, (h s x (b i) (b j)) ^ 2)
    (∑ i, ∑ j,
      2 * h t x (b i) (b j) * dh t x (b i) (b j)) t
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  have hpow := (htime (b i) (b j)).pow 2
  convert hpow using 1 <;> try rfl
  norm_num [Nat.reduceSub, pow_one]

end CovariantDerivative
