module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation

/-!
# Covariant differentiation of evaluated bilinear forms

This file proves the intrinsic Leibniz rule for a covariant two-tensor
evaluated on a moving tangent field.  It is the first-order input for the
contact-Hessian calculation in the Hamilton--Ivey tensor maximum principle.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance bilinearEvalTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance bilinearEvalTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance bilinearEvalTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance bilinearEvalTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance

/-- Intrinsic Leibniz rule for evaluating a covariant three-tensor on three
independently moving tangent fields. -/
theorem realLineCovariantDerivative_trilinear
    (cov : CovariantDerivative I E TM)
    {A : ∀ x : M, T₃ x} {X U V : ∀ x : M, TM x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y (A y)) x)
    (hX : MDiffAt (T% X) x) (hU : MDiffAt (T% U) x)
    (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => A y (X y) (U y) (V y)) x u =
      covariantThreeTensorCovariantDerivative cov A x u
          (X x) (U x) (V x) +
        A x (cov X x u) (U x) (V x) +
        A x (X x) (cov U x u) (V x) +
        A x (X x) (U x) (cov V x u) := by
  let φ : ∀ y : M, T₂ y := fun y => A y (X y)
  let ψ : ∀ y : M, T₁ y := fun y => φ y (U y)
  have hφ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (φ y)) x :=
    hA.clm_bundle_apply hX
  have hψ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (ψ y)) x :=
    hφ.clm_bundle_apply hU
  have houter :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] (E →L[ℝ] ℝ)) _ _ _ _ _ _
      TM T₂ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covariantTwoTensorCovariantDerivative cov) A X x hA hX u
  have houterUV := congrArg (fun q : T₂ x => q (U x) (V x)) houter
  have hmiddle :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) φ U x hφ hU u
  have hmiddleV := congrArg (fun q : T₁ x => q (V x)) hmiddle
  have hinner :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M)) ψ V x hψ hV u
  change covariantThreeTensorCovariantDerivative cov A x u
      (X x) (U x) (V x) = _ at houterUV
  change covariantTwoTensorCovariantDerivative cov φ x u
      (U x) (V x) = _ at hmiddleV
  change covectorCovariantDerivative cov ψ x u (V x) = _ at hinner
  change realLineCovariantDerivative (I := I) (M := M)
      (fun y => A y (X y) (U y) (V y)) x u = _
  dsimp [φ, ψ] at houterUV hmiddleV hinner
  simp only [sub_apply] at houterUV hmiddleV
  rw [hinner] at hmiddleV
  rw [hmiddleV] at houterUV
  linarith

/-- When all three moving fields are covariantly stationary at the evaluation
point, differentiating their trilinear contraction differentiates only the
tensor. -/
theorem realLineCovariantDerivative_trilinear_of_covariantDerivative_eq_zero
    (cov : CovariantDerivative I E TM)
    {A : ∀ x : M, T₃ x} {X U V : ∀ x : M, TM x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y (A y)) x)
    (hX : MDiffAt (T% X) x) (hU : MDiffAt (T% U) x)
    (hV : MDiffAt (T% V) x)
    (hXzero : cov X x = 0) (hUzero : cov U x = 0)
    (hVzero : cov V x = 0) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => A y (X y) (U y) (V y)) x u =
      covariantThreeTensorCovariantDerivative cov A x u
        (X x) (U x) (V x) := by
  rw [realLineCovariantDerivative_trilinear cov hA hX hU hV u,
    hXzero, hUzero, hVzero]
  simp

/-- Intrinsic Leibniz rule for evaluating a covariant two-tensor on two
independently moving tangent fields. -/
theorem realLineCovariantDerivative_bilinear
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {U V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (U y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (U x) (V x) +
        h x (cov U x u) (V x) + h x (U x) (cov V x u) := by
  let φ : ∀ y : M, T₁ y := fun y => h y (U y)
  have hφ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (φ y)) x :=
    hh.clm_bundle_apply hU
  have houter :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) h U x hh hU u
  have houterV := congrArg (fun q : T₁ x => q (V x)) houter
  have hinner :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M)) φ V x hφ hV u
  change covariantTwoTensorCovariantDerivative cov h x u (U x) (V x) = _ at houterV
  change covectorCovariantDerivative cov φ x u (V x) = _ at hinner
  change realLineCovariantDerivative (I := I) (M := M)
      (fun y => h y (U y) (V y)) x u = _
  dsimp [φ] at houterV hinner
  simp only [sub_apply] at houterV
  rw [hinner] at houterV
  linarith

/-- Intrinsic Leibniz rule when the same moving tangent field is used in both
slots. -/
theorem realLineCovariantDerivative_bilinear_self
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hV : MDiffAt (T% V) x) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (V y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (V x) (V x) +
        h x (cov V x u) (V x) + h x (V x) (cov V x u) := by
  exact realLineCovariantDerivative_bilinear cov hh hV hV u

/-- If the moving field is covariantly stationary at the evaluation point,
only the covariant derivative of the tensor contributes. -/
theorem realLineCovariantDerivative_bilinear_self_of_covariantDerivative_eq_zero
    (cov : CovariantDerivative I E TM)
    {h : ∀ x : M, T₂ x} {V : ∀ x : M, TM x} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (hV : MDiffAt (T% V) x) (hparallel : cov V x = 0) (u : TM x) :
    realLineCovariantDerivative (I := I) (M := M)
        (fun y => h y (V y) (V y)) x u =
      covariantTwoTensorCovariantDerivative cov h x u (V x) (V x) := by
  rw [realLineCovariantDerivative_bilinear_self cov hh hV u, hparallel]
  simp

end CovariantDerivative
