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

end CovariantDerivative
