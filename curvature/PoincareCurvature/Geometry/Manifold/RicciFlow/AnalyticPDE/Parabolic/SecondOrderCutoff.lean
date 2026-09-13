import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteLowerOrder

/-!
# Lower-order coefficients produced by a scalar cutoff

This file isolates the elementary operator algebra behind a second-order
cutoff commutator.  If `u` is multiplied by a scalar `χ`, the second spatial
jet contains the original jet multiplied by `χ`, two gradient cross terms,
and a Hessian-times-value term.  Consequently every second-order linear
operator loses its principal part in the commutator and leaves a canonical
first-plus-zeroth-order operator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RicciFlow
namespace AnalyticPDE

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The first-jet contribution `v ↦ dχ(v) u`. -/
def cutoffGradientValueL (dχ : X →L[ℝ] ℝ) :
    W →L[ℝ] X →L[ℝ] W :=
  (ContinuousLinearMap.smulRightL ℝ X W) dχ

@[simp] theorem cutoffGradientValueL_apply
    (dχ : X →L[ℝ] ℝ) (u : W) (v : X) :
    cutoffGradientValueL dχ u v = dχ v • u := by
  rfl

/-- The symmetric first-jet cross term
`(v,w) ↦ dχ(v) Du(w) + dχ(w) Du(v)`. -/
def cutoffGradientCrossL (dχ : X →L[ℝ] ℝ) :
    (X →L[ℝ] W) →L[ℝ] X →L[ℝ] X →L[ℝ] W :=
  let A := (ContinuousLinearMap.smulRightL ℝ X (X →L[ℝ] W)) dχ
  A + (ContinuousLinearMap.flipₗᵢ ℝ X X W).toContinuousLinearEquiv.toContinuousLinearMap.comp A

@[simp] theorem cutoffGradientCrossL_apply
    (dχ : X →L[ℝ] ℝ) (Du : X →L[ℝ] W) (v w : X) :
    cutoffGradientCrossL dχ Du v w =
      dχ v • Du w + dχ w • Du v := by
  rfl

/-- The Hessian-times-value contribution
`(v,w) ↦ D²χ(v,w) u`. -/
def cutoffHessianValueL (ddχ : X →L[ℝ] X →L[ℝ] ℝ) :
    W →L[ℝ] X →L[ℝ] X →L[ℝ] W :=
  (ContinuousLinearMap.flipₗᵢ ℝ X W (X →L[ℝ] W)).toContinuousLinearEquiv.toContinuousLinearMap
      ((ContinuousLinearMap.smulRightL ℝ X W).comp ddχ)

@[simp] theorem cutoffHessianValueL_apply
    (ddχ : X →L[ℝ] X →L[ℝ] ℝ) (u : W) (v w : X) :
    cutoffHessianValueL ddχ u v w = ddχ v w • u := by
  rfl

/-- The canonical first-order coefficient in the commutator of a principal
coefficient `P` with multiplication by `χ`. -/
def secondOrderCutoffFirstCoefficient
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) : (X →L[ℝ] W) →L[ℝ] W :=
  P.comp (cutoffGradientCrossL dχ)

@[simp] theorem secondOrderCutoffFirstCoefficient_apply
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (Du : X →L[ℝ] W) :
    secondOrderCutoffFirstCoefficient P dχ Du =
      P (cutoffGradientCrossL dχ Du) := by
  rfl

/-- The canonical zeroth-order coefficient in the cutoff commutator.  It
contains the Hessian of the cutoff through the principal coefficient and
its gradient through the original first-order coefficient. -/
def secondOrderCutoffZeroCoefficient
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ) : W →L[ℝ] W :=
  P.comp (cutoffHessianValueL ddχ) +
    B.comp (cutoffGradientValueL dχ)

@[simp] theorem secondOrderCutoffZeroCoefficient_apply
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ) (u : W) :
    secondOrderCutoffZeroCoefficient P B dχ ddχ u =
      P (cutoffHessianValueL ddχ u) +
        B (cutoffGradientValueL dχ u) := by
  rfl

/-- Pure operator identity showing cancellation of every second derivative
of the unknown in a cutoff commutator. -/
theorem secondOrder_cutoff_expansion
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W) (C : W →L[ℝ] W)
    (χ : ℝ) (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ)
    (u : W) (Du : X →L[ℝ] W) (D2u : X →L[ℝ] X →L[ℝ] W) :
    P (χ • D2u + cutoffGradientCrossL dχ Du +
          cutoffHessianValueL ddχ u) +
        B (χ • Du + cutoffGradientValueL dχ u) + C (χ • u) =
      χ • (P D2u + B Du + C u) +
        secondOrderCutoffFirstCoefficient P dχ Du +
        secondOrderCutoffZeroCoefficient P B dχ ddχ u := by
  simp [secondOrderCutoffFirstCoefficient,
    secondOrderCutoffZeroCoefficient, map_add, map_smul]
  abel

/-- The first and second Fréchet jets of a scalar multiple, written in the
same canonical cross-term operators used by the cutoff expansion. -/
theorem secondOrder_cutoff_product_jet
    {χ : X → ℝ} {u : X → W} {s : Set X} {x : X}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hχ : DifferentiableOn ℝ χ s) (hu : DifferentiableOn ℝ u s)
    {ddχ : X →L[ℝ] X →L[ℝ] ℝ} {D2u : X →L[ℝ] X →L[ℝ] W}
    (hdχ : HasFDerivWithinAt
      (fun y => fderivWithin ℝ χ s y) ddχ s x)
    (hDu : HasFDerivWithinAt
      (fun y => fderivWithin ℝ u s y) D2u s x) :
    let dχ := fderivWithin ℝ χ s x
    let Du := fderivWithin ℝ u s x
    fderivWithin ℝ (fun y => χ y • u y) s x =
        χ x • Du + cutoffGradientValueL dχ (u x) ∧
      fderivWithin ℝ
          (fun y => fderivWithin ℝ (fun z => χ z • u z) s y) s x =
        χ x • D2u + cutoffGradientCrossL dχ Du +
          cutoffHessianValueL ddχ (u x) := by
  dsimp only
  let dχ := fderivWithin ℝ χ s x
  let Du := fderivWithin ℝ u s x
  have hχx : HasFDerivWithinAt χ dχ s x :=
    (hχ x hx).hasFDerivWithinAt
  have hux : HasFDerivWithinAt u Du s x :=
    (hu x hx).hasFDerivWithinAt
  have hfirst : HasFDerivWithinAt (fun y => χ y • u y)
      (χ x • Du + cutoffGradientValueL dχ (u x)) s x := by
    change HasFDerivWithinAt (χ • u)
      (χ x • Du + dχ.smulRight (u x)) s x
    exact hχx.smul hux
  constructor
  · exact hfirst.fderivWithin (hs x hx)
  · let S := ContinuousLinearMap.smulRightL ℝ X W
    let F : X → X →L[ℝ] W := fun y =>
      χ y • fderivWithin ℝ u s y +
        cutoffGradientValueL (fderivWithin ℝ χ s y) (u y)
    have hEq : Set.EqOn
        (fun y => fderivWithin ℝ (fun z => χ z • u z) s y) F s := by
      intro y hy
      exact fderivWithin_fun_smul (hs y hy) (hχ y hy) (hu y hy)
    have hterm1 : HasFDerivWithinAt
        (fun y => χ y • fderivWithin ℝ u s y)
        (χ x • D2u + dχ.smulRight Du) s x := hχx.smul hDu
    have hS : HasFDerivAt (fun L => S L) S
        (fderivWithin ℝ χ s x) := S.hasFDerivAt
    have hc := hS.comp_hasFDerivWithinAt
      (f := fun y => fderivWithin ℝ χ s y)
      (g := fun L => S L) (f' := ddχ) (g' := S) x hdχ
    have hterm2raw := hc.clm_apply hux
    have hterm2 : HasFDerivWithinAt
        (fun y => cutoffGradientValueL
          (fderivWithin ℝ χ s y) (u y))
        ((S dχ).comp Du + (S.comp ddχ).flip (u x)) s x := by
      simpa only [S, cutoffGradientValueL, Function.comp_apply] using
        hterm2raw
    have hF : HasFDerivWithinAt F
        ((χ x • D2u + dχ.smulRight Du) +
          ((S dχ).comp Du + (S.comp ddχ).flip (u x))) s x := by
      change HasFDerivWithinAt
        ((fun y => χ y • fderivWithin ℝ u s y) +
          fun y => cutoffGradientValueL
            (fderivWithin ℝ χ s y) (u y)) _ s x
      exact hterm1.add hterm2
    have hactual := hF.congr' hEq hx
    rw [hactual.fderivWithin (hs x hx)]
    ext v w
    simp [S, cutoffGradientCrossL, cutoffHessianValueL]
    abel

end AnalyticPDE
end RicciFlow
