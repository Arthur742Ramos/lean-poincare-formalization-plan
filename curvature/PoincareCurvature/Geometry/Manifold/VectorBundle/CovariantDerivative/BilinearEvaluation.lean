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

/-- Intrinsic Leibniz rule for evaluating a covariant two-tensor on the same
moving tangent field in both slots. -/
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
  let φ : ∀ y : M, T₁ y := fun y => h y (V y)
  have hφ : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (φ y)) x :=
    hh.clm_bundle_apply hV
  have houter :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) h V x hh hV u
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
  change covariantTwoTensorCovariantDerivative cov h x u (V x) (V x) = _ at houterV
  change covectorCovariantDerivative cov φ x u (V x) = _ at hinner
  change realLineCovariantDerivative (I := I) (M := M)
      (fun y => h y (V y) (V y)) x u = _
  dsimp [φ] at houterV hinner
  simp only [sub_apply] at houterV
  rw [hinner] at houterV
  linarith

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
