module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorNormSq
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.RieszCovariantDerivative
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation

/-!
# The covariant derivative of a tensor Gram form

This is the first differential product rule behind the Bochner identity for
the complete norm square of a covariant two-tensor.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 3000000

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance tensorGramTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance tensorGramTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance tensorGramTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance tensorGramTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance tensorGramThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance tensorGramThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance tensorGramThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance tensorGramThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- Metric compatibility differentiates both factors of the Gram tensor.
The two correction terms remove the derivatives of the chosen smooth
extensions of the tensor slots. -/
theorem covariantTwoTensorCovariantDerivative_gram_apply
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    {h : ∀ y : M, T₂ y} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x)
    (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov
        (covariantTwoTensorGram (I := I) (E := E) h) x X u v =
      inner ℝ
        (cov (fun y =>
          raisedCovariantTwoTensor (I := I) (E := E) h y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)) x X -
          raisedCovariantTwoTensor (I := I) (E := E) h x
            (cov (smoothExtend (I := I) (F := E) (V := TM) x u) x X))
        (raisedCovariantTwoTensor (I := I) (E := E) h x v) +
      inner ℝ
        (raisedCovariantTwoTensor (I := I) (E := E) h x u)
        (cov (fun y =>
          raisedCovariantTwoTensor (I := I) (E := E) h y
            (smoothExtend (I := I) (F := E) (V := TM) x v y)) x X -
          raisedCovariantTwoTensor (I := I) (E := E) h x
            (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x X)) := by
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  let G : ∀ y : M, T₂ y := covariantTwoTensorGram (I := I) (E := E) h
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x v
  have hG := covariantTwoTensorGram_mdifferentiableAt
    (I := I) (E := E) (M := M) hh
  have hA := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) hh
  have hU : MDiffAt (T% U) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hAU : MDiffAt (T% (fun y => A y (U y))) x :=
    hA.clm_bundle_apply hU
  have hAV : MDiffAt (T% (fun y => A y (V y))) x :=
    hA.clm_bundle_apply hV
  have hbil := realLineCovariantDerivative_bilinear
    cov hG hU hV X
  have hinner := hmetric hAU hAV X
  have hbil' : mvfderiv (I := I)
      (fun y => G y (U y) (V y)) x X =
        covariantTwoTensorCovariantDerivative cov G x X u v +
          G x (cov U x X) v + G x u (cov V x X) := by
    simpa [realLineCovariantDerivative, trivialCovariantDerivative_apply,
      G, U, V, smoothExtend_apply] using hbil
  have heval : (fun y => G y (U y) (V y)) =
      (fun y => inner ℝ (A y (U y)) (A y (V y))) := by
    funext y
    rfl
  rw [heval] at hbil'
  simp only [G, covariantTwoTensorGram_apply, A, U, V] at hbil'
  simp only [A, U, V, smoothExtend_apply] at hinner
  simpa [G, A, covariantTwoTensorGram_apply, U, V, smoothExtend_apply]
    using (show _ from by
      simp only [inner_sub_left, inner_sub_right]
      linarith [hbil', hinner])

/-- The intrinsic first derivative of the Gram form, expressed entirely
through the covariant derivative of the original tensor. -/
theorem covariantTwoTensorCovariantDerivative_gram_eq
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    {h : ∀ y : M, T₂ y} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x)
    (X u v : TM x) :
    covariantTwoTensorCovariantDerivative cov
        (covariantTwoTensorGram (I := I) (E := E) h) x X u v =
      covariantTwoTensorCovariantDerivative cov h x X u
        (raisedCovariantTwoTensor (I := I) (E := E) h x v) +
      covariantTwoTensorCovariantDerivative cov h x X v
        (raisedCovariantTwoTensor (I := I) (E := E) h x u) := by
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x v
  have hA := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) hh
  have hEndU :
      endomorphismCovariantDerivativeApply cov A x X u =
        cov (fun y => A y (U y)) x X - A x (cov U x X) := by
    unfold endomorphismCovariantDerivativeApply endomorphismCovariantDerivativeAt
    dsimp only [inducedHomCovariantDerivative]
    split
    next _ => rfl
    next hnot => exact (hnot hA).elim
  have hEndV :
      endomorphismCovariantDerivativeApply cov A x X v =
        cov (fun y => A y (V y)) x X - A x (cov V x X) := by
    unfold endomorphismCovariantDerivativeApply endomorphismCovariantDerivativeAt
    dsimp only [inducedHomCovariantDerivative]
    split
    next _ => rfl
    next hnot => exact (hnot hA).elim
  have hdefect : ∀ (a b : TM x), cov.metricDefect x a b = 0 :=
    (isMetricCompatibleTangent_iff_metricDefect_eq_zero cov).mp hmetric x
  have hu := inner_endomorphismCovariantDerivative_raisedCovariantTwoTensor_eq
    (I := I) (E := E) (M := M) cov hh X u (A x v)
  have hv := inner_endomorphismCovariantDerivative_raisedCovariantTwoTensor_eq
    (I := I) (E := E) (M := M) cov hh X v (A x u)
  have hgram := covariantTwoTensorCovariantDerivative_gram_apply
    (I := I) (E := E) (M := M) cov hmetric hh X u v
  change inner ℝ (endomorphismCovariantDerivativeApply cov A x X u) (A x v) = _ at hu
  change inner ℝ (endomorphismCovariantDerivativeApply cov A x X v) (A x u) = _ at hv
  rw [hEndU] at hu
  rw [hEndV] at hv
  simp only [hdefect, zero_apply, sub_zero] at hu hv
  change _ = inner ℝ
      (cov (fun y => A y (U y)) x X - A x (cov U x X)) (A x v) +
      inner ℝ (A x u)
        (cov (fun y => A y (V y)) x X - A x (cov V x X)) at hgram
  have hv' : inner ℝ (A x u)
      (cov (fun y => A y (V y)) x X - A x (cov V x X)) =
        covariantTwoTensorCovariantDerivative cov h x X v (A x u) := by
    rw [real_inner_comm]
    exact hv
  rw [hu, hv'] at hgram
  simpa [A] using hgram

/-- Second-order regularity of the original tensor supplies the first
covariant-derivative regularity of its Gram tensor. -/
theorem covariantTwoTensorCovariantDerivative_gram_mdifferentiableAt
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) z (h z)) y)
    {x₀ : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov h y)) x₀) :
    MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x₀ := by
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  have hA := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) (hh x₀)
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (E₂ := T₂) x₀ b ?_
  intro i
  let X : ∀ y : M, TM y := fun y => e.localFrame b i y
  have hX : MDiffAt (T% X) x₀ :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hfirstX := hfirst.clm_bundle_apply hX
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (E₂ := fun y : M => TM y →L[ℝ] ℝ) x₀ b ?_
  intro j
  let U : ∀ y : M, TM y := fun y => e.localFrame b j y
  have hU : MDiffAt (T% U) x₀ :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := j) (hx := hx)).mdifferentiableAt one_ne_zero
  have hfirstXU := hfirstX.clm_bundle_apply hU
  have hAU := hA.clm_bundle_apply hU
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (E₂ := Bundle.Trivial M ℝ) x₀ b ?_
  intro k
  let V : ∀ y : M, TM y := fun y => e.localFrame b k y
  have hV : MDiffAt (T% V) x₀ :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := k) (hx := hx)).mdifferentiableAt one_ne_zero
  have hAV := hA.clm_bundle_apply hV
  have hfirstXV := hfirstX.clm_bundle_apply hV
  have hterm1 := hfirstXU.clm_bundle_apply hAV
  have hterm2 := hfirstXV.clm_bundle_apply hAU
  rw [mdifferentiableAt_section] at hterm1 hterm2
  have hscalar : MDiffAt
      (fun y => covariantTwoTensorCovariantDerivative cov h y (X y) (U y) (A y (V y)) +
        covariantTwoTensorCovariantDerivative cov h y (X y) (V y) (A y (U y))) x₀ := by
    exact hterm1.add hterm2
  rw [mdifferentiableAt_section]
  have heq : (fun y =>
      covariantTwoTensorCovariantDerivative cov
        (covariantTwoTensorGram (I := I) (E := E) h) y (X y) (U y) (V y)) =
      (fun y => covariantTwoTensorCovariantDerivative cov h y (X y) (U y) (A y (V y)) +
        covariantTwoTensorCovariantDerivative cov h y (X y) (V y) (A y (U y))) := by
    funext y
    exact covariantTwoTensorCovariantDerivative_gram_eq
      (I := I) (E := E) (M := M) cov hmetric (hh y) (X y) (U y) (V y)
  change MDiffAt (fun y =>
    covariantTwoTensorCovariantDerivative cov
      (covariantTwoTensorGram (I := I) (E := E) h) y (X y) (U y) (V y)) x₀
  rw [heq]
  exact hscalar

/-- The scalar Laplacian of tensor energy is the trace of the Gram
connection Laplacian under second-order regularity of the original tensor. -/
theorem scalarLaplacian_covariantTwoTensorNormSq_eq_trace_laplacian_gram_of_tensor_regular
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) z (h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov h y)) x) :
    scalarLaplacian cov (covariantTwoTensorNormSq (I := I) (E := E) h) x =
      covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x := by
  have hfirstGram := covariantTwoTensorCovariantDerivative_gram_mdifferentiableAt
    (I := I) (E := E) (M := M) cov hmetric h hh hfirst
  exact scalarLaplacian_covariantTwoTensorNormSq_eq_trace_laplacian_gram
    cov hmetric h hh hfirstGram

/-- The full second covariant derivative of the Gram tensor. The last two
terms are the derivatives of the two tensor factors and produce the positive
energy term after taking the metric trace. -/
theorem covariantHessianTwoTensor_gram_eq
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) z (h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov h y)) x)
    (X₁ X₂ u v : TM x) :
    covariantHessianTwoTensor cov
        (covariantTwoTensorGram (I := I) (E := E) h) x X₁ X₂ u v =
      covariantHessianTwoTensor cov h x X₁ X₂ u
          (raisedCovariantTwoTensor (I := I) (E := E) h x v) +
        covariantHessianTwoTensor cov h x X₁ X₂ v
          (raisedCovariantTwoTensor (I := I) (E := E) h x u) +
        covariantTwoTensorCovariantDerivative cov h x X₂ u
          (endomorphismCovariantDerivativeApply cov
            (raisedCovariantTwoTensor (I := I) (E := E) h) x X₁ v) +
        covariantTwoTensorCovariantDerivative cov h x X₂ v
          (endomorphismCovariantDerivativeApply cov
            (raisedCovariantTwoTensor (I := I) (E := E) h) x X₁ u) := by
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  let S : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x X₂
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x v
  have hS : MDiffAt (T% S) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x X₂).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hU : MDiffAt (T% U) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hA := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) (hh x)
  have hAU := hA.clm_bundle_apply hU
  have hAV := hA.clm_bundle_apply hV
  have hfirstGram := covariantTwoTensorCovariantDerivative_gram_mdifferentiableAt
    (I := I) (E := E) (M := M) cov hmetric h hh hfirst
  have hfirstS := hfirst.clm_bundle_apply hS
  have hfirstSU := hfirstS.clm_bundle_apply hU
  have hfirstSV := hfirstS.clm_bundle_apply hV
  have hterm1 := hfirstSU.clm_bundle_apply hAV
  have hterm2 := hfirstSV.clm_bundle_apply hAU
  rw [mdifferentiableAt_section] at hterm1 hterm2
  have hterm1' : MDiffAt
      (fun y => covariantTwoTensorCovariantDerivative cov h y
        (S y) (U y) (A y (V y))) x := by
    simpa [Bundle.Trivial.eq_trivialization M ℝ, A] using hterm1
  have hterm2' : MDiffAt
      (fun y => covariantTwoTensorCovariantDerivative cov h y
        (S y) (V y) (A y (U y))) x := by
    simpa [Bundle.Trivial.eq_trivialization M ℝ, A] using hterm2
  have hG := realLineCovariantDerivative_trilinear cov
    hfirstGram hS hU hV X₁
  have hT1 := realLineCovariantDerivative_trilinear cov
    hfirst hS hU hAV X₁
  have hT2 := realLineCovariantDerivative_trilinear cov
    hfirst hS hV hAU X₁
  have hpoint :
      (fun y => covariantTwoTensorCovariantDerivative cov
        (covariantTwoTensorGram (I := I) (E := E) h) y
          (S y) (U y) (V y)) =
      (fun y => covariantTwoTensorCovariantDerivative cov h y
          (S y) (U y) (A y (V y)) +
        covariantTwoTensorCovariantDerivative cov h y
          (S y) (V y) (A y (U y))) := by
    funext y
    exact covariantTwoTensorCovariantDerivative_gram_eq
      (I := I) (E := E) (M := M) cov hmetric (hh y) (S y) (U y) (V y)
  have hderiv :
      realLineCovariantDerivative (I := I) (M := M)
        (fun y => covariantTwoTensorCovariantDerivative cov
          (covariantTwoTensorGram (I := I) (E := E) h) y
            (S y) (U y) (V y)) x X₁ =
      realLineCovariantDerivative (I := I) (M := M)
        (fun y => covariantTwoTensorCovariantDerivative cov h y
          (S y) (U y) (A y (V y))) x X₁ +
      realLineCovariantDerivative (I := I) (M := M)
        (fun y => covariantTwoTensorCovariantDerivative cov h y
          (S y) (V y) (A y (U y))) x X₁ := by
    rw [hpoint]
    change (mvfderiv (I := I)
      ((fun y => covariantTwoTensorCovariantDerivative cov h y
          (S y) (U y) (A y (V y))) +
        (fun y => covariantTwoTensorCovariantDerivative cov h y
          (S y) (V y) (A y (U y)))) x) X₁ = _
    rw [mvfderiv_add (I := I) hterm1' hterm2']
    rfl
  have hEndU :
      endomorphismCovariantDerivativeApply cov A x X₁ u =
        cov (fun y => A y (U y)) x X₁ - A x (cov U x X₁) := by
    unfold endomorphismCovariantDerivativeApply endomorphismCovariantDerivativeAt
    dsimp only [inducedHomCovariantDerivative]
    split
    next _ => rfl
    next hnot => exact (hnot hA).elim
  have hEndV :
      endomorphismCovariantDerivativeApply cov A x X₁ v =
        cov (fun y => A y (V y)) x X₁ - A x (cov V x X₁) := by
    unfold endomorphismCovariantDerivativeApply endomorphismCovariantDerivativeAt
    dsimp only [inducedHomCovariantDerivative]
    split
    next _ => rfl
    next hnot => exact (hnot hA).elim
  have hcovAU : cov (fun y => A y (U y)) x X₁ =
      endomorphismCovariantDerivativeApply cov A x X₁ u +
        A x (cov U x X₁) := by
    rw [hEndU]
    abel
  have hcovAV : cov (fun y => A y (V y)) x X₁ =
      endomorphismCovariantDerivativeApply cov A x X₁ v +
        A x (cov V x X₁) := by
    rw [hEndV]
    abel
  have hG' := hG
  rw [hderiv] at hG'
  rw [hT1, hT2] at hG'
  rw [hcovAU, hcovAV] at hG'
  simp only [map_add, S, U, V, smoothExtend_apply] at hG'
  have hCorrS := covariantTwoTensorCovariantDerivative_gram_eq
    (I := I) (E := E) (M := M) cov hmetric (hh x)
      (cov S x X₁) u v
  have hCorrU := covariantTwoTensorCovariantDerivative_gram_eq
    (I := I) (E := E) (M := M) cov hmetric (hh x)
      X₂ (cov U x X₁) v
  have hCorrV := covariantTwoTensorCovariantDerivative_gram_eq
    (I := I) (E := E) (M := M) cov hmetric (hh x)
      X₂ u (cov V x X₁)
  simp only [S, U, V] at hCorrS hCorrU hCorrV
  simp only [A] at hG'
  unfold covariantHessianTwoTensor
  linarith [hG', hCorrS, hCorrU, hCorrV]

/-- The complete Hilbert--Schmidt pairing is contraction against the raised
first tensor in the second slot of the other tensor. -/
theorem covariantTwoTensorPair_eq_sum_raised
    (h k : ∀ y : M, T₂ y) (x : M) :
    covariantTwoTensorPair h k x =
      letI : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let b := stdOrthonormalBasis ℝ (TM x)
      ∑ i, k x (b i)
        (raisedCovariantTwoTensor (I := I) (E := E) h x (b i)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let A := raisedCovariantTwoTensor (I := I) (E := E) h x
  let B := raisedCovariantTwoTensor (I := I) (E := E) k x
  change (∑ i, ∑ j, h x (b i) (b j) * k x (b i) (b j)) =
    ∑ i, k x (b i) (A (b i))
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ j, h x (b i) (b j) * k x (b i) (b j) =
        ∑ j, inner ℝ (A (b i)) (b j) *
          inner ℝ (b j) (B (b i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hAij : h x (b i) (b j) = inner ℝ (A (b i)) (b j) := by
        change h x (b i) (b j) =
          inner ℝ (rieszMap (I := I) x (h x (b i))) (b j)
        exact (rieszMap_apply_inner (I := I) x (h x (b i)) (b j)).symm
      have hBij : k x (b i) (b j) = inner ℝ (b j) (B (b i)) := by
        calc
          k x (b i) (b j) = inner ℝ (B (b i)) (b j) := by
            change k x (b i) (b j) =
              inner ℝ (rieszMap (I := I) x (k x (b i))) (b j)
            exact (rieszMap_apply_inner (I := I) x (k x (b i)) (b j)).symm
          _ = inner ℝ (b j) (B (b i)) := real_inner_comm _ _
      rw [hAij, hBij]
    _ = inner ℝ (A (b i)) (B (b i)) := b.sum_inner_mul_inner _ _
    _ = k x (b i) (A (b i)) := by
      calc
        inner ℝ (A (b i)) (B (b i)) =
            inner ℝ (B (b i)) (A (b i)) := real_inner_comm _ _
        _ = k x (b i) (A (b i)) := by
          change inner ℝ (rieszMap (I := I) x (k x (b i))) (A (b i)) = _
          exact rieszMap_apply_inner (I := I) x (k x (b i)) (A (b i))

/-- Each mixed term in the Gram Hessian is a nonnegative square for a
metric-compatible connection. -/
theorem covariantTwoTensorCovariantDerivative_raised_self_nonneg
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    {h : ∀ y : M, T₂ y} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x)
    (X u : TM x) :
    0 ≤ covariantTwoTensorCovariantDerivative cov h x X u
      (endomorphismCovariantDerivativeApply cov
        (raisedCovariantTwoTensor (I := I) (E := E) h) x X u) := by
  let D := endomorphismCovariantDerivativeApply cov
    (raisedCovariantTwoTensor (I := I) (E := E) h) x X u
  have hdefect :=
    (isMetricCompatibleTangent_iff_metricDefect_eq_zero cov).mp hmetric x
      (raisedCovariantTwoTensor (I := I) (E := E) h x u) D
  have hinner := inner_endomorphismCovariantDerivative_raisedCovariantTwoTensor_eq
    (I := I) (E := E) (M := M) cov hh X u D
  simp only [hdefect, zero_apply, sub_zero] at hinner
  change 0 ≤ covariantTwoTensorCovariantDerivative cov h x X u D
  rw [← hinner]
  exact real_inner_self_nonneg

/-- The spatial Bochner inequality for the complete covariant two-tensor
norm. This is a geometric consequence of the Gram Hessian product identity. -/
theorem two_mul_pair_le_trace_connectionLaplacian_gram
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) z (h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov h y)) x) :
    2 * covariantTwoTensorPair h
      (fun y => connectionLaplacian cov h y) x ≤
      covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  let A := raisedCovariantTwoTensor (I := I) (E := E) h x
  have hleft : 2 * covariantTwoTensorPair h
      (fun y => connectionLaplacian cov h y) x =
      ∑ j, ∑ i, 2 * covariantHessianTwoTensor cov h x
        (b i) (b i) (b j) (A (b j)) := by
    rw [covariantTwoTensorPair_eq_sum_raised]
    change 2 * (∑ j, connectionLaplacian cov h x (b j) (A (b j))) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [connectionLaplacian_apply]
    simp only [Finset.mul_sum]
    rfl
  have hright : covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian cov
            (covariantTwoTensorGram (I := I) (E := E) h) y)) x =
      ∑ j, ∑ i, covariantHessianTwoTensor cov
        (covariantTwoTensorGram (I := I) (E := E) h) x
        (b i) (b i) (b j) (b j) := by
    rw [covariantTwoTensorTrace_eq_sum_orthonormalBasis
      (I := I) (E := E) (M := M) _ x b]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [covariantTwoTensorLinear_apply, connectionLaplacian_apply]
    rfl
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  have hess := covariantHessianTwoTensor_gram_eq
    cov hmetric h hh hfirst (b i) (b i) (b j) (b j)
  have hnonneg := covariantTwoTensorCovariantDerivative_raised_self_nonneg
    cov hmetric (hh x) (b i) (b j)
  linarith

/-- The geometric Bochner inequality in the scalar form needed by the tensor
heat maximum principle. No spatial differential inequality is assumed. -/
theorem two_mul_pair_le_scalarLaplacian_covariantTwoTensorNormSq
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hh : ∀ y : M, MDiffAt
      (fun z => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) z (h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
        (E := T₃) y
          (covariantTwoTensorCovariantDerivative cov h y)) x) :
    2 * covariantTwoTensorPair h
      (fun y => connectionLaplacian cov h y) x ≤
      scalarLaplacian cov (covariantTwoTensorNormSq (I := I) (E := E) h) x := by
  rw [scalarLaplacian_covariantTwoTensorNormSq_eq_trace_laplacian_gram_of_tensor_regular
    cov hmetric h hh hfirst]
  exact two_mul_pair_le_trace_connectionLaplacian_gram
    cov hmetric h hh hfirst

end CovariantDerivative
