module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

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

/-- Constant parabolic second jet. -/
def const (c : E) : ParabolicSecondJet (fun _ : ℝ × X => c) s where
  timeDeriv := fun _ => 0
  spaceDeriv := fun _ => 0
  spaceSecondDeriv := fun _ => 0
  hasTimeDeriv := by
    intro z _hz
    simpa using hasDerivWithinAt_const (𝕜 := ℝ) z.1 (timeSliceDomain s z.2) c
  hasSpaceDeriv := by
    intro z _hz
    simpa using hasFDerivWithinAt_const (𝕜 := ℝ) c z.2 (spaceSliceDomain s z.1)
  hasSpaceSecondDeriv := by
    intro z _hz
    simpa using
      hasFDerivWithinAt_const (𝕜 := ℝ) (0 : X →L[ℝ] E) z.2 (spaceSliceDomain s z.1)

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

/-- Sum of two parabolic second jets, with derivative witnesses added componentwise. -/
def add {v : ℝ × X → E} (Ju : ParabolicSecondJet u s) (Jv : ParabolicSecondJet v s) :
    ParabolicSecondJet (fun z : ℝ × X => u z + v z) s where
  timeDeriv := fun z => Ju.timeDeriv z + Jv.timeDeriv z
  spaceDeriv := fun z => Ju.spaceDeriv z + Jv.spaceDeriv z
  spaceSecondDeriv := fun z => Ju.spaceSecondDeriv z + Jv.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    simpa using (Ju.hasTimeDeriv hz).add (Jv.hasTimeDeriv hz)
  hasSpaceDeriv := by
    intro z hz
    simpa using (Ju.hasSpaceDeriv hz).add (Jv.hasSpaceDeriv hz)
  hasSpaceSecondDeriv := by
    intro z hz
    simpa [Pi.add_apply] using (Ju.hasSpaceSecondDeriv hz).add (Jv.hasSpaceSecondDeriv hz)

/-- Negation of a parabolic second jet. -/
def neg (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => -u z) s where
  timeDeriv := fun z => -J.timeDeriv z
  spaceDeriv := fun z => -J.spaceDeriv z
  spaceSecondDeriv := fun z => -J.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    simpa using (J.hasTimeDeriv hz).fun_neg
  hasSpaceDeriv := by
    intro z hz
    simpa using (J.hasSpaceDeriv hz).fun_neg
  hasSpaceSecondDeriv := by
    intro z hz
    simpa using (J.hasSpaceSecondDeriv hz).fun_neg

/-- Scalar multiplication of a parabolic second jet. -/
def smul (c : ℝ) (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => c • u z) s where
  timeDeriv := fun z => c • J.timeDeriv z
  spaceDeriv := fun z => c • J.spaceDeriv z
  spaceSecondDeriv := fun z => c • J.spaceSecondDeriv z
  hasTimeDeriv := by
    intro z hz
    simpa using HasDerivWithinAt.fun_const_smul c (J.hasTimeDeriv hz)
  hasSpaceDeriv := by
    intro z hz
    simpa using (J.hasSpaceDeriv hz).fun_const_smul c
  hasSpaceSecondDeriv := by
    intro z hz
    simpa [Pi.smul_apply] using (J.hasSpaceSecondDeriv hz).fun_const_smul c

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

theorem const (c : E) :
    ParabolicC2AlphaNormLe ‖c‖ α (fun _ : ℝ × X => c) s := by
  refine ⟨ParabolicSecondJet.const (X := X) (s := s) c, ‖c‖, norm_nonneg c,
    0, le_rfl, 0, le_rfl, 0, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · exact ParabolicC0AlphaNormLe.const (X := X) (α := α) (s := s) c
  · exact ParabolicC0AlphaNormLe.zero (X := X) (E := X →L[ℝ] E) (α := α) (s := s)
  · exact
      ParabolicC0AlphaNormLe.zero
        (X := X) (E := X →L[ℝ] (X →L[ℝ] E)) (α := α) (s := s)
  · exact ParabolicC0AlphaNormLe.zero (X := X) (E := E) (α := α) (s := s)

theorem zero :
    ParabolicC2AlphaNormLe 0 α (fun _ : ℝ × X => (0 : E)) s := by
  simpa using (const (X := X) (E := E) (α := α) (s := s) (0 : E))

theorem mono_const (h : ParabolicC2AlphaNormLe N α u s) (hNN : N ≤ N') :
    ParabolicC2AlphaNormLe N' α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum.trans hNN, hu, hx, hxx, ht⟩

theorem add {v : ℝ × X → E} {M : ℝ}
    (hu : ParabolicC2AlphaNormLe N α u s) (hv : ParabolicC2AlphaNormLe M α v s) :
    ParabolicC2AlphaNormLe (N + M) α (fun z : ℝ × X => u z + v z) s := by
  rcases hu with
    ⟨Ju, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsumu, huu, hxu, hxxu, htu⟩
  rcases hv with
    ⟨Jv, Mu, hMu, Mx, hMx, Mxx, hMxx, Mt, hMt, hsumv, huv, hxv, hxxv, htv⟩
  refine ⟨Ju.add Jv, Nu + Mu, add_nonneg hNu hMu, Nx + Mx, add_nonneg hNx hMx,
    Nxx + Mxx, add_nonneg hNxx hMxx, Nt + Mt, add_nonneg hNt hMt, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · simpa using huu.add huv
  · simpa [ParabolicSecondJet.add] using hxu.add hxv
  · simpa [ParabolicSecondJet.add] using hxxu.add hxxv
  · simpa [ParabolicSecondJet.add] using htu.add htv

theorem neg (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe N α (fun z : ℝ × X => -u z) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J.neg, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum,
    hu.neg, by simpa [ParabolicSecondJet.neg] using hx.neg,
    by simpa [ParabolicSecondJet.neg] using hxx.neg,
    by simpa [ParabolicSecondJet.neg] using ht.neg⟩

theorem sub {v : ℝ × X → E} {M : ℝ}
    (hu : ParabolicC2AlphaNormLe N α u s) (hv : ParabolicC2AlphaNormLe M α v s) :
    ParabolicC2AlphaNormLe (N + M) α (fun z : ℝ × X => u z - v z) s := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem smul (c : ℝ) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe (‖c‖ * N) α (fun z : ℝ × X => c • u z) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  refine ⟨J.smul c, ‖c‖ * Nu, mul_nonneg (norm_nonneg c) hNu,
    ‖c‖ * Nx, mul_nonneg (norm_nonneg c) hNx,
    ‖c‖ * Nxx, mul_nonneg (norm_nonneg c) hNxx,
    ‖c‖ * Nt, mul_nonneg (norm_nonneg c) hNt, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      ‖c‖ * Nu + ‖c‖ * Nx + ‖c‖ * Nxx + ‖c‖ * Nt =
          ‖c‖ * (Nu + Nx + Nxx + Nt) := by ring
      _ ≤ ‖c‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg c)
  · simpa using hu.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using hx.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using hxx.smul (𝕜 := ℝ) c
  · simpa [ParabolicSecondJet.smul] using ht.smul (𝕜 := ℝ) c

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
