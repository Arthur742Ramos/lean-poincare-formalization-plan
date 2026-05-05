module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic

set_option linter.unusedSectionVars false

/-!
# Higher parabolic Holder function spaces

This module starts the coordinate-level `C^{2+α,1+α/2}` side of the
Ricci-DeTurck analytic setup.  It records actual spatial and time derivative
witnesses together with the `ParabolicC0AlphaNormLe` controls that the matrix
RHS estimates consume.  It deliberately does not assert Schauder estimates.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

/-- Time slice of a time-space set at a fixed spatial point. -/
def timeSliceDomain {X : Type*} (s : Set (ℝ × X)) (x : X) : Set ℝ :=
  {t | (t, x) ∈ s}

/-- Spatial slice of a time-space set at a fixed time. -/
def spaceSliceDomain {X : Type*} (s : Set (ℝ × X)) (t : ℝ) : Set X :=
  {x | (t, x) ∈ s}

@[simp]
theorem mem_timeSliceDomain {X : Type*} {s : Set (ℝ × X)} {x : X} {t : ℝ} :
    t ∈ timeSliceDomain s x ↔ (t, x) ∈ s :=
  Iff.rfl

@[simp]
theorem mem_spaceSliceDomain {X : Type*} {s : Set (ℝ × X)} {t : ℝ} {x : X} :
    x ∈ spaceSliceDomain s t ↔ (t, x) ∈ s :=
  Iff.rfl

variable {X E : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate parabolic second jet for a time-space function on a domain.

The fields are genuine derivative witnesses on the natural time and spatial
slices of the domain.  The second spatial derivative is the derivative of the
first spatial derivative as a `ContinuousLinearMap`-valued function. -/
structure ParabolicSecondJet (u : ℝ × X → E) (s : Set (ℝ × X)) where
  timeDeriv : ℝ × X → E
  spaceDeriv : ℝ × X → X →L[ℝ] E
  spaceSecondDeriv : ℝ × X → X →L[ℝ] (X →L[ℝ] E)
  hasTimeDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (timeDeriv z)
      (timeSliceDomain s z.2) z.1
  hasSpaceDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasFDerivWithinAt (fun x : X => u (z.1, x)) (spaceDeriv z)
      (spaceSliceDomain s z.1) z.2
  hasSpaceSecondDeriv : ∀ ⦃z : ℝ × X⦄, z ∈ s →
    HasFDerivWithinAt (fun x : X => spaceDeriv (z.1, x)) (spaceSecondDeriv z)
      (spaceSliceDomain s z.1) z.2

namespace ParabolicSecondJet

variable {u : ℝ × X → E} {s : Set (ℝ × X)}

theorem timeDeriv_hasDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (J.timeDeriv z)
      (timeSliceDomain s z.2) z.1 :=
  J.hasTimeDeriv hz

theorem spaceDeriv_hasFDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasFDerivWithinAt (fun x : X => u (z.1, x)) (J.spaceDeriv z)
      (spaceSliceDomain s z.1) z.2 :=
  J.hasSpaceDeriv hz

theorem spaceSecondDeriv_hasFDerivWithinAt (J : ParabolicSecondJet u s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    HasFDerivWithinAt (fun x : X => J.spaceDeriv (z.1, x)) (J.spaceSecondDeriv z)
      (spaceSliceDomain s z.1) z.2 :=
  J.hasSpaceSecondDeriv hz

end ParabolicSecondJet

/-- Coordinate parabolic `C^{2+α,1+α/2}` single-radius control.

The radius dominates the sum of four `C^{0,α}` norm-ball radii: the value, the
spatial derivative, the second spatial derivative, and the time derivative of a
chosen parabolic second jet. -/
def ParabolicC2AlphaNormLe (N α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ J : ParabolicSecondJet u s,
    ∃ Nu ≥ 0, ∃ Nx ≥ 0, ∃ Nxx ≥ 0, ∃ Nt ≥ 0,
      Nu + Nx + Nxx + Nt ≤ N ∧
        ParabolicC0AlphaNormLe Nu α u s ∧
        ParabolicC0AlphaNormLe Nx α J.spaceDeriv s ∧
        ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s ∧
        ParabolicC0AlphaNormLe Nt α J.timeDeriv s

namespace ParabolicC2AlphaNormLe

variable {N N' α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}

theorem nonneg (h : ParabolicC2AlphaNormLe N α u s) : 0 ≤ N := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, _hu, _hx, _hxx, _ht⟩
  exact (add_nonneg (add_nonneg (add_nonneg hNu hNx) hNxx) hNt).trans hsum

theorem of_secondJet {J : ParabolicSecondJet u s} {Nu Nx Nxx Nt : ℝ}
    (hNu : 0 ≤ Nu) (hNx : 0 ≤ Nx) (hNxx : 0 ≤ Nxx) (hNt : 0 ≤ Nt)
    (hu : ParabolicC0AlphaNormLe Nu α u s)
    (hx : ParabolicC0AlphaNormLe Nx α J.spaceDeriv s)
    (hxx : ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s)
    (ht : ParabolicC0AlphaNormLe Nt α J.timeDeriv s) :
    ParabolicC2AlphaNormLe (Nu + Nx + Nxx + Nt) α u s := by
  exact ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, le_rfl, hu, hx, hxx, ht⟩

theorem mono_const (h : ParabolicC2AlphaNormLe N α u s) (hNN : N ≤ N') :
    ParabolicC2AlphaNormLe N' α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum.trans hNN, hu, hx, hxx, ht⟩

theorem value_c0AlphaNormLe (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Nu ≥ 0, ParabolicC0AlphaNormLe Nu α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨Nu, hNu, hu⟩

theorem exists_secondJet (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α J.spaceDeriv s) ∧
      (∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s) ∧
      (∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α J.timeDeriv s) := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J, ⟨Nx, hNx, hx⟩, ⟨Nxx, hNxx, hxx⟩, ⟨Nt, hNt, ht⟩⟩

theorem value_c0AlphaOn (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaOn α u s := by
  rcases h.value_c0AlphaNormLe with ⟨Nu, _hNu, hu⟩
  exact hu.c0AlphaOn

theorem exists_timeDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α Dt s := by
  rcases h.exists_secondJet with ⟨J, _hx, _hxx, ⟨Nt, hNt, ht⟩⟩
  exact ⟨J.timeDeriv, J.hasTimeDeriv, Nt, hNt, ht⟩

theorem exists_spaceDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α Dx s := by
  rcases h.exists_secondJet with ⟨J, ⟨Nx, hNx, hx⟩, _hxx, _ht⟩
  exact ⟨J.spaceDeriv, J.hasSpaceDeriv, Nx, hNx, hx⟩

theorem exists_spaceSecondDeriv (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      ∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s := by
  rcases h.exists_secondJet with ⟨J, _hx, ⟨Nxx, hNxx, hxx⟩, _ht⟩
  exact ⟨J, Nxx, hNxx, hxx⟩

end ParabolicC2AlphaNormLe

end AnalyticPDE
end RicciFlow
