/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CoordinateMatrixConnection

/-!
# Actual coordinate Ricci--DeTurck spatial operator

All spatial derivative readouts in this file are evaluations of `fderiv` on
coordinate vectors. Open-domain C² metric and C¹ background regularity supply
derivative existence. The conventional positive vector is differentiated by
actual finite-sum/product rules, including the derivative of the background.
The Ricci and Lie expressions are coordinate readouts; identification with
manifold curvature or a manifold Lie derivative is a separate obligation.
-/

noncomputable section

open Matrix

namespace PoincareCurvature.CoordinateMatrixJet

variable {d : ℕ}

/-- Actual component differential of a spatially varying background array. -/
def backgroundFirst (B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (m k i j : Fin d) : ℝ :=
  fderiv ℝ (fun y => B y k i j) x (coordinateVector m)

/-- The conventional positive, inverse-metric-contracted coordinate vector. -/
def deTurck (g : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d, inverse g x a b * (christoffel g x k a b - B x k a b)

/-- The actual directional differential of the conventional coordinate vector. -/
def deTurckFirst (g : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (m k : Fin d) : ℝ :=
  fderiv ℝ (fun y => deTurck g B y k) x (coordinateVector m)

/-- Coordinate Ricci readout using actual Christoffel differentials. -/
def coordinateRicci (g : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (i j : Fin d) : ℝ :=
  (∑ k : Fin d,
    (fderiv ℝ (fun y => christoffel g y k i j) x (coordinateVector k) -
      fderiv ℝ (fun y => christoffel g y k i k) x (coordinateVector j))) +
    ∑ k : Fin d, ∑ l : Fin d,
      (christoffel g x k k l * christoffel g x l i j -
        christoffel g x k j l * christoffel g x l i k)

/-- Coordinate Lie readout using actual vector and metric differentials. -/
def coordinateLie (g : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (i j : Fin d) : ℝ :=
  ∑ k : Fin d,
    (g x k j * deTurckFirst g B x i k + g x i k * deTurckFirst g B x j k +
      deTurck g B x k * first g x k i j)

/-- The corrected actual coordinate spatial operator, including varying B. -/
def coordinateRD (g : (Fin d → ℝ) → Fin d → Fin d → ℝ)
    (B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (i j : Fin d) : ℝ :=
  -2 * coordinateRicci g x i j + coordinateLie g B x i j

variable {g : (Fin d → ℝ) → Fin d → Fin d → ℝ}
    {B : (Fin d → ℝ) → Fin d → Fin d → Fin d → ℝ}
    {U : Set (Fin d → ℝ)} {x : Fin d → ℝ}

/-- C¹ background regularity supplies actual component derivative certificates. -/
theorem background_component_hasFDerivAt
    (hU : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hx : x ∈ U)
    (k i j : Fin d) :
    HasFDerivAt (fun y => B y k i j) (fderiv ℝ (fun y => B y k i j) x) x := by
  have h : ContDiffAt ℝ 1 (fun y => B y k i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp
      (contDiffAt_pi.mp (hB.contDiffAt (hU.mem_nhds hx)) k) i) j
  exact (h.differentiableAt (by norm_num)).hasFDerivAt

/-- Genuine differentiability of the positive conventional coordinate vector. -/
theorem differentiableAt_deTurck
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (k : Fin d) : DifferentiableAt ℝ (fun y => deTurck g B y k) x := by
  unfold deTurck
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (differentiableAt_inverse_entry hU hg hx hdet a b).mul
    ((differentiableAt_christoffel hU hg hx hdet k a b).sub
      (background_component_hasFDerivAt hU hB hx k a b).differentiableAt)

/-- Actual product differentiation, with both inverse-derivative and
background-derivative contributions retained. -/
theorem deTurckFirst_eq_productRule
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (hB : ContDiffOn ℝ 1 B U)
    (hx : x ∈ U) (hdet : (show Matrix (Fin d) (Fin d) ℝ from g x).det ≠ 0)
    (m k : Fin d) :
    deTurckFirst g B x m k = ∑ a : Fin d, ∑ b : Fin d,
      (inverseFirst g x m a b * (christoffel g x k a b - B x k a b) +
        inverse g x a b * (christoffelFirst g x m k a b - backgroundFirst B x m k a b)) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun b _ =>
      (differentiableAt_inverse_entry hU hg hx hdet a b).hasFDerivAt.mul
        ((differentiableAt_christoffel hU hg hx hdet k a b).hasFDerivAt.sub
          (background_component_hasFDerivAt hU hB hx k a b))
  simp only [Pi.mul_apply, Pi.sub_apply] at h
  unfold deTurckFirst deTurck
  rw [h.fderiv]
  simp [fderiv_inverse_apply hU hg hx hdet, fderiv_christoffel_apply hU hg hx hdet,
    backgroundFirst, mul_comm, add_comm]

end PoincareCurvature.CoordinateMatrixJet
