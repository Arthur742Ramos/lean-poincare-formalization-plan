/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual coordinate derivatives of a matrix-valued field

The matrix-entry space is the explicit finite Pi space with its sup norm.
The slots below are evaluated Fréchet derivatives of the actual component
functions, not freely supplied arrays. On an open real coordinate domain, C²
regularity gives the derivative-slot Hessian symmetry by Schwarz. Symmetry of
the matrix field on that domain gives tensor-slot symmetry by differentiating
local component equalities. No invertibility or manifold identity is asserted.
-/

open Filter Set
open scoped Topology

namespace PoincareCurvature.CoordinateMatrixJet

noncomputable section

variable {n d : ℕ}

/-- The standard coordinate vector, including the dimension-zero case. -/
def coordinateVector (a : Fin n) : Fin n → ℝ := Pi.single a 1

/-- Actual first coordinate derivative, evaluated componentwise. -/
def first (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin n → ℝ) (a : Fin n) : (Fin d → Fin d → ℝ) :=
  fun i k => fderiv ℝ (fun y => g y i k) x (coordinateVector a)

/-- Actual second coordinate derivative: differentiate the component differential
and evaluate its two arguments on standard coordinate vectors. -/
def second (g : (Fin n → ℝ) → (Fin d → Fin d → ℝ))
    (x : Fin n → ℝ) (a b : Fin n) : (Fin d → Fin d → ℝ) :=
  fun i k => fderiv ℝ (fderiv ℝ (fun y => g y i k)) x
    (coordinateVector a) (coordinateVector b)

variable {g : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin n → ℝ)} {x : Fin n → ℝ}

/-- Open-domain C² regularity supplies actual component C² regularity. -/
theorem component_contDiffAt (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (i k : Fin d) :
    ContDiffAt ℝ 2 (fun y => g y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp (hg.contDiffAt (hU.mem_nhds hx)) i) k

/-- The first slot comes with a genuine derivative-existence certificate. -/
theorem component_hasFDerivAt (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (i k : Fin d) :
    HasFDerivAt (fun y => g y i k) (fderiv ℝ (fun y => g y i k) x) x :=
  ((component_contDiffAt hU hg hx i k).differentiableAt (by norm_num)).hasFDerivAt

/-- The componentwise first slot is the actual matrix-valued differential
applied to the coordinate vector. -/
theorem first_eq_matrix_fderiv (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (a : Fin n) (i k : Fin d) :
    first g x a i k = (fderiv ℝ g x (coordinateVector a)) i k := by
  have hd : DifferentiableAt ℝ g x :=
    (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdi := differentiableAt_pi.mp hd i
  unfold first
  rw [fderiv_apply hdi k, fderiv_apply hd i]
  rfl

/-- The second slot comes with a genuine derivative of the component differential. -/
theorem component_differential_hasFDerivAt
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U) (i k : Fin d) :
    HasFDerivAt (fderiv ℝ (fun y => g y i k))
      (fderiv ℝ (fderiv ℝ (fun y => g y i k)) x) x := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ (fun y => g y i k)) x :=
    (component_contDiffAt hU hg hx i k).fderiv_right (by norm_num)
  exact (h.differentiableAt (by norm_num)).hasFDerivAt

/-- Genuine derivative existence for a produced first-coordinate component. -/
theorem first_component_hasFDerivAt
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hx : x ∈ U)
    (b : Fin n) (i k : Fin d) :
    HasFDerivAt (fun y => first g y b i k)
      ((fderiv ℝ (fderiv ℝ (fun y => g y i k)) x).flip (coordinateVector b)) x := by
  simpa [first] using
    (component_differential_hasFDerivAt hU hg hx i k).clm_apply
      (hasFDerivAt_const x (coordinateVector b))

/-- Compatibility of the actual first and second slots. The differentiated
first-coordinate component has precisely the second-slot evaluation. -/
theorem fderiv_first_apply (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (a b : Fin n) (i k : Fin d) :
    fderiv ℝ (fun y => first g y b i k) x (coordinateVector a) =
      second g x a b i k := by
  rw [(first_component_hasFDerivAt hU hg hx b i k).fderiv]
  rfl

/-- Schwarz symmetry, derived from C² regularity on the actual open domain. -/
theorem second_derivative_symm (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (a b : Fin n) (i k : Fin d) :
    second g x a b i k = second g x b a i k := by
  exact ((component_contDiffAt hU hg hx i k).isSymmSndFDerivAt (by simp)).eq
    (coordinateVector a) (coordinateVector b)

/-- Differentiating an actual local symmetry equality gives first-slot tensor
symmetry; no derivative symmetry certificate is supplied as a premise. -/
theorem first_tensor_symm (hU : IsOpen U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (a : Fin n) (i k : Fin d) : first g x a i k = first g x a k i := by
  have heq : (fun y => g y i k) =ᶠ[𝓝 x] (fun y => g y k i) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hsymm y hy i k
  exact congrArg (fun D => D (coordinateVector a)) (heq.fderiv_eq (𝕜 := ℝ))

/-- Differentiating the local component equality twice gives Hessian tensor-slot
symmetry. Regularity is unnecessary for this congruence of total fderiv readouts;
the C² hypotheses above separately ensure these readouts are actual derivatives. -/
theorem second_tensor_symm (hU : IsOpen U) (hx : x ∈ U)
    (hsymm : ∀ y ∈ U, ∀ i k : Fin d, g y i k = g y k i)
    (a b : Fin n) (i k : Fin d) : second g x a b i k = second g x a b k i := by
  have heq : (fun y => g y i k) =ᶠ[𝓝 x] (fun y => g y k i) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hsymm y hy i k
  exact congrArg (fun D => D (coordinateVector a) (coordinateVector b))
    ((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ))

end

end PoincareCurvature.CoordinateMatrixJet
