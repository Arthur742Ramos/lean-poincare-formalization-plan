/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Pointwise Koszul identity from actual Levi--Civita predicates

Adapted from `HamiltonIveyKoszul.lean` in the repository. This file derives the
pointwise Koszul identity directly from the actual torsion-free and
metric-compatible predicates using only differentiability of the three tangent
sections at the evaluation point. It introduces no replacement norm or topology
instances: the inner product is the ambient `RiemannianBundle` inner product and
`MDiffAt (T% X) x` uses the existing tangent total-space topology.

This is source-only proof work. It has not been compiled, and verification under
the repository's exact Lean 4.33 toolchain remains required.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The classical Koszul formula for an actual torsion-free, metric-compatible
connection on the tangent bundle, requiring only pointwise differentiability of
the three sections. Directional derivatives are the manifold `mvfderiv`, and
the brackets are the manifold Lie brackets. -/
theorem koszul_formula_at
    (cov : CovariantDerivative I E TM)
    (hLevi : cov.IsLeviCivita)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * ⟪cov.along X Y x, Z x⟫ =
      mvfderiv (I := I) (fun y ↦ ⟪Y y, Z y⟫) x (X x) +
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) -
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) -
      ⟪X x, VectorField.mlieBracket I Y Z x⟫ +
      ⟪Y x, VectorField.mlieBracket I Z X x⟫ +
      ⟪Z x, VectorField.mlieBracket I X Y x⟫ := by
  have hmetric₁ :
      mvfderiv (I := I) (fun y ↦ ⟪Y y, Z y⟫) x (X x) =
        ⟪cov.along X Y x, Z x⟫ + ⟪Y x, cov.along X Z x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 hY hZ (X x)
  have hmetric₂ :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) =
        ⟪cov.along Y X x, Z x⟫ + ⟪X x, cov.along Y Z x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 hX hZ (Y x)
  have hmetric₃ :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) =
        ⟪cov.along Z X x, Y x⟫ + ⟪X x, cov.along Z Y x⟫ := by
    simpa [CovariantDerivative.along] using hLevi.2 hX hY (Z x)
  have htorsionXY : cov.along X Y x - cov.along Y X x =
      VectorField.mlieBracket I X Y x := by
    simpa [CovariantDerivative.along] using
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hLevi.1
        (X := X) (Y := Y) (x := x) hX hY
  have htorsionYZ : cov.along Y Z x - cov.along Z Y x =
      VectorField.mlieBracket I Y Z x := by
    simpa [CovariantDerivative.along] using
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hLevi.1
        (X := Y) (Y := Z) (x := x) hY hZ
  have htorsionZX : cov.along Z X x - cov.along X Z x =
      VectorField.mlieBracket I Z X x := by
    simpa [CovariantDerivative.along] using
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hLevi.1
        (X := Z) (Y := X) (x := x) hZ hX
  have hYX : cov.along Y X x =
      cov.along X Y x - VectorField.mlieBracket I X Y x := by
    have h : cov.along X Y x - cov.along Y X x =
        VectorField.mlieBracket I X Y x := by
      exact htorsionXY
    rw [← h]
    abel
  have hYZ : cov.along Y Z x =
      cov.along Z Y x + VectorField.mlieBracket I Y Z x := by
    have h : cov.along Y Z x - cov.along Z Y x =
        VectorField.mlieBracket I Y Z x := by
      exact htorsionYZ
    rw [← h]
    abel
  have hZX : cov.along Z X x =
      cov.along X Z x + VectorField.mlieBracket I Z X x := by
    have h : cov.along Z X x - cov.along X Z x =
        VectorField.mlieBracket I Z X x := by
      exact htorsionZX
    rw [← h]
    abel
  have hmetric₂' :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Z y⟫) x (Y x) =
        ⟪cov.along X Y x, Z x⟫ - ⟪VectorField.mlieBracket I X Y x, Z x⟫ +
          ⟪cov.along Z Y x, X x⟫ + ⟪VectorField.mlieBracket I Y Z x, X x⟫ := by
    calc
      _ = ⟪cov.along Y X x, Z x⟫ + ⟪X x, cov.along Y Z x⟫ := hmetric₂
      _ = ⟪cov.along X Y x - VectorField.mlieBracket I X Y x, Z x⟫ +
          ⟪X x, cov.along Z Y x + VectorField.mlieBracket I Y Z x⟫ := by
            rw [hYX, hYZ]
      _ = _ := by
        simp [inner_sub_left, inner_add_right, real_inner_comm]
        abel
  have hmetric₃' :
      mvfderiv (I := I) (fun y ↦ ⟪X y, Y y⟫) x (Z x) =
        ⟪cov.along X Z x, Y x⟫ + ⟪VectorField.mlieBracket I Z X x, Y x⟫ +
          ⟪cov.along Z Y x, X x⟫ := by
    calc
      _ = ⟪cov.along Z X x, Y x⟫ + ⟪X x, cov.along Z Y x⟫ := hmetric₃
      _ = ⟪cov.along X Z x + VectorField.mlieBracket I Z X x, Y x⟫ +
          ⟪X x, cov.along Z Y x⟫ := by rw [hZX]
      _ = _ := by simp [inner_add_left, real_inner_comm]
  rw [hmetric₁, hmetric₂', hmetric₃']
  rw [real_inner_comm (Y x) (cov.along X Z x),
    real_inner_comm (X x) (cov.along Z Y x),
    real_inner_comm (X x) (VectorField.mlieBracket I Y Z x),
    real_inner_comm (Z x) (VectorField.mlieBracket I X Y x),
    real_inner_comm (Y x) (VectorField.mlieBracket I Z X x)]
  ring

end CovariantDerivative
