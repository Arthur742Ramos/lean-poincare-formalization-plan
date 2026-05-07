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

/-- Compose a parabolic second jet with a continuous linear value map. -/
def continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (J : ParabolicSecondJet u s) :
    ParabolicSecondJet (fun z : ℝ × X => L (u z)) s where
  timeDeriv := fun z => L (J.timeDeriv z)
  spaceDeriv := fun z => L.comp (J.spaceDeriv z)
  spaceSecondDeriv := fun z =>
    (ContinuousLinearMap.compL ℝ X (X →L[ℝ] E) (X →L[ℝ] F)
      (ContinuousLinearMap.compL ℝ X E F L)) (J.spaceSecondDeriv z)
  hasTimeDeriv := by
    intro z hz
    have hcomp :=
      L.hasFDerivAt.comp_hasFDerivWithinAt z.1 (J.hasTimeDeriv hz).hasFDerivWithinAt
    simpa [Function.comp] using hcomp.hasDerivWithinAt
  hasSpaceDeriv := by
    intro z hz
    have hcomp := L.hasFDerivAt.comp_hasFDerivWithinAt z.2 (J.hasSpaceDeriv hz)
    simpa [Function.comp] using hcomp
  hasSpaceSecondDeriv := by
    intro z hz
    let A : (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] F) :=
      ContinuousLinearMap.compL ℝ X E F L
    have hcomp := A.hasFDerivAt.comp_hasFDerivWithinAt z.2 (J.hasSpaceSecondDeriv hz)
    simpa [Function.comp, A] using hcomp

/-- Restrict a parabolic second jet to a smaller time-space domain. -/
def restrict {t : Set (ℝ × X)} (J : ParabolicSecondJet u s) (hst : t ⊆ s) :
    ParabolicSecondJet u t where
  timeDeriv := J.timeDeriv
  spaceDeriv := J.spaceDeriv
  spaceSecondDeriv := J.spaceSecondDeriv
  hasTimeDeriv := by
    intro z hz
    refine (J.hasTimeDeriv (hst hz)).mono ?_
    intro τ hτ
    exact hst hτ
  hasSpaceDeriv := by
    intro z hz
    refine (J.hasSpaceDeriv (hst hz)).mono ?_
    intro x hx
    exact hst hx
  hasSpaceSecondDeriv := by
    intro z hz
    refine (J.hasSpaceSecondDeriv (hst hz)).mono ?_
    intro x hx
    exact hst hx

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

theorem mono_set {t : Set (ℝ × X)} (h : ParabolicC2AlphaNormLe N α u s) (hst : t ⊆ s) :
    ParabolicC2AlphaNormLe N α u t := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨J.restrict hst, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum,
    hu.mono_set hst, hx.mono_set hst, hxx.mono_set hst, ht.mono_set hst⟩

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

theorem finset_sum {ι : Type*} (S : Finset ι) {N : ι → ℝ}
    {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC2AlphaNormLe (N i) α (u i) s) :
    ParabolicC2AlphaNormLe (∑ i ∈ S, N i) α
      (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC2AlphaNormLe (N a) α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC2AlphaNormLe (∑ i ∈ S, N i) α
          (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

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

/-- Radius multiplier for composing a higher parabolic function with a continuous linear
value map.  The spatial first- and second-derivative components both use postcomposition by
`L` on `X →L[ℝ] E`. -/
def continuousLinearMapRadius {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : ℝ :=
  ‖L‖ + ‖ContinuousLinearMap.compL ℝ X E F L‖ +
    ‖ContinuousLinearMap.compL ℝ X E F L‖ + ‖L‖

theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaNormLe
      (continuousLinearMapRadius (X := X) (E := E) L * N) α
      (fun z : ℝ × X => L (u z)) s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  let Lx : (X →L[ℝ] E) →L[ℝ] X →L[ℝ] F :=
    ContinuousLinearMap.compL ℝ X E F L
  have hxx_comp : ParabolicC0AlphaNormLe (‖Lx‖ * Nxx) α
      (fun z : ℝ × X => Lx.comp (J.spaceSecondDeriv z)) s := by
    rcases hxx with ⟨Bxx, hBxx, Hxx, hHxx, hxx_sum, hxx_ctrl⟩
    refine ⟨‖Lx‖ * Bxx, mul_nonneg (norm_nonneg Lx) hBxx,
      ‖Lx‖ * Hxx, mul_nonneg (norm_nonneg Lx) hHxx, ?_, ?_⟩
    · calc
        ‖Lx‖ * Bxx + ‖Lx‖ * Hxx = ‖Lx‖ * (Bxx + Hxx) := by ring
        _ ≤ ‖Lx‖ * Nxx := mul_le_mul_of_nonneg_left hxx_sum (norm_nonneg Lx)
    · constructor
      · intro p hp
        exact (Lx.opNorm_comp_le (J.spaceSecondDeriv p)).trans
          (mul_le_mul_of_nonneg_left (hxx_ctrl.bounded hp) (norm_nonneg Lx))
      · intro p hp q hq
        calc
          ‖Lx.comp (J.spaceSecondDeriv p) - Lx.comp (J.spaceSecondDeriv q)‖ =
              ‖Lx.comp (J.spaceSecondDeriv p - J.spaceSecondDeriv q)‖ := by
            congr 1
            ext x y
            simp [Pi.sub_apply]
          _ ≤ ‖Lx‖ * ‖J.spaceSecondDeriv p - J.spaceSecondDeriv q‖ :=
            Lx.opNorm_comp_le (J.spaceSecondDeriv p - J.spaceSecondDeriv q)
          _ ≤ ‖Lx‖ * (Hxx * (parabolicDistance p q) ^ α) :=
            mul_le_mul_of_nonneg_left (hxx_ctrl.holder hp hq) (norm_nonneg Lx)
          _ = (‖Lx‖ * Hxx) * (parabolicDistance p q) ^ α := by ring
  refine ⟨J.continuousLinearMap L, ‖L‖ * Nu, mul_nonneg (norm_nonneg L) hNu,
    ‖Lx‖ * Nx, mul_nonneg (norm_nonneg Lx) hNx,
    ‖Lx‖ * Nxx, mul_nonneg (norm_nonneg Lx) hNxx,
    ‖L‖ * Nt, mul_nonneg (norm_nonneg L) hNt, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      ‖L‖ * Nu + ‖Lx‖ * Nx + ‖Lx‖ * Nxx + ‖L‖ * Nt ≤
          ‖L‖ * N + ‖Lx‖ * N + ‖Lx‖ * N + ‖L‖ * N := by
        have hNu_le : Nu ≤ N := by linarith
        have hNx_le : Nx ≤ N := by linarith
        have hNxx_le : Nxx ≤ N := by linarith
        have hNt_le : Nt ≤ N := by linarith
        have hNu_bound : ‖L‖ * Nu ≤ ‖L‖ * N :=
          mul_le_mul_of_nonneg_left hNu_le (norm_nonneg L)
        have hNx_bound : ‖Lx‖ * Nx ≤ ‖Lx‖ * N :=
          mul_le_mul_of_nonneg_left hNx_le (norm_nonneg Lx)
        have hNxx_bound : ‖Lx‖ * Nxx ≤ ‖Lx‖ * N :=
          mul_le_mul_of_nonneg_left hNxx_le (norm_nonneg Lx)
        have hNt_bound : ‖L‖ * Nt ≤ ‖L‖ * N :=
          mul_le_mul_of_nonneg_left hNt_le (norm_nonneg L)
        linarith
      _ = continuousLinearMapRadius (X := X) (E := E) L * N := by
        simp [continuousLinearMapRadius, Lx]
        ring
  · simpa using hu.continuousLinearMap L
  · exact (by
      have hxL : ParabolicC0AlphaNormLe (‖Lx‖ * Nx) α (fun z => Lx (J.spaceDeriv z)) s :=
        hx.continuousLinearMap Lx
      simpa [ParabolicSecondJet.continuousLinearMap, Lx] using hxL)
  · exact (by
      simpa [ParabolicSecondJet.continuousLinearMap, Lx, ContinuousLinearMap.comp_apply]
        using hxx_comp)
  · simpa [ParabolicSecondJet.continuousLinearMap] using ht.continuousLinearMap L

/-- A full higher parabolic norm ball for a finite Pi-valued function projects to each
coordinate as a full higher parabolic norm ball. -/
theorem pi_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × X → ι → F} (h : ParabolicC2AlphaNormLe N α u s) (i : ι) :
    ParabolicC2AlphaNormLe
      (continuousLinearMapRadius (X := X) (E := ι → F)
        (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F) * N) α
      (fun z : ℝ × X => u z i) s := by
  simpa using h.continuousLinearMap (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

theorem value_c0AlphaNormLe (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ Nu ≥ 0, ParabolicC0AlphaNormLe Nu α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  exact ⟨Nu, hNu, hu⟩

theorem value_c0AlphaNormLe_self (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α u s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  have hNu_le : Nu ≤ N := by linarith
  exact hu.mono_const hNu_le

/-- A higher single-radius bound supplies one chosen second jet whose value and derivative
components are all controlled by the same higher radius at the `C^{0,α}` level. -/
theorem exists_secondJet_c0AlphaNormLe_self (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      ParabolicC0AlphaNormLe N α u s ∧
        ParabolicC0AlphaNormLe N α J.spaceDeriv s ∧
          ParabolicC0AlphaNormLe N α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaNormLe N α J.timeDeriv s := by
  rcases h with
    ⟨J, Nu, hNu, Nx, hNx, Nxx, hNxx, Nt, hNt, hsum, hu, hx, hxx, ht⟩
  have hNu_le : Nu ≤ N := by linarith
  have hNx_le : Nx ≤ N := by linarith
  have hNxx_le : Nxx ≤ N := by linarith
  have hNt_le : Nt ≤ N := by linarith
  exact ⟨J, hu.mono_const hNu_le, hx.mono_const hNx_le,
    hxx.mono_const hNxx_le, ht.mono_const hNt_le⟩

/-- A higher single-radius bound supplies one chosen second jet whose value and
derivative components are pointwise bounded by the same higher radius. -/
theorem exists_secondJet_norm_le_self (h : ParabolicC2AlphaNormLe N α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖u z‖ ≤ N) ∧
        (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceDeriv z‖ ≤ N) ∧
          (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceSecondDeriv z‖ ≤ N) ∧
            (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.timeDeriv z‖ ≤ N) := by
  rcases h.exists_secondJet_c0AlphaNormLe_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨J,
    (fun {_z} hz ↦ hu.norm_le hz),
    (fun {_z} hz ↦ hx.norm_le hz),
    (fun {_z} hz ↦ hxx.norm_le hz),
    (fun {_z} hz ↦ ht.norm_le hz)⟩

/-- The higher single radius controls the pointwise value norm on the domain. -/
theorem norm_le (h : ParabolicC2AlphaNormLe N α u s) ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z‖ ≤ N :=
  h.value_c0AlphaNormLe_self.norm_le hz

/-- A higher single-radius bound on a difference gives the corresponding pointwise value
distance bound. -/
theorem dist_le_of_sub {v : ℝ × X → E}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ N :=
  h.value_c0AlphaNormLe_self.dist_le_of_sub hz

/-- Continuous-linear value readouts of a higher single-radius norm ball inherit value-level
`C^{0,α}` control. -/
theorem value_continuousLinearMap_c0AlphaNormLe {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖L‖ * N) α (fun z => L (u z)) s :=
  h.value_c0AlphaNormLe_self.continuousLinearMap L

/-- Positive-exponent higher norm-ball control gives value-level continuity on the domain. -/
theorem continuousOn (h : ParabolicC2AlphaNormLe N α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.value_c0AlphaNormLe_self.continuousOn hα

/-- Positive-exponent higher norm-ball control gives value-level uniform continuity on the
domain. -/
theorem uniformContinuousOn (h : ParabolicC2AlphaNormLe N α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.value_c0AlphaNormLe_self.uniformContinuousOn hα

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
  exact h.value_c0AlphaNormLe_self.c0AlphaOn

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

/-- Coordinate parabolic `C^{2+α,1+α/2}` membership with some finite single-radius control. -/
def ParabolicC2AlphaOn (α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ N ≥ 0, ParabolicC2AlphaNormLe N α u s

namespace ParabolicC2AlphaOn

variable {α : ℝ} {u v : ℝ × X → E} {s : Set (ℝ × X)}

theorem of_normLe {N : ℝ} (h : ParabolicC2AlphaNormLe N α u s) :
    ParabolicC2AlphaOn α u s :=
  ⟨N, h.nonneg, h⟩

theorem c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨N, _hN, hN⟩
  exact hN.value_c0AlphaOn

theorem continuousOn (h : ParabolicC2AlphaOn α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.c0AlphaOn.continuousOn hα

theorem uniformContinuousOn (h : ParabolicC2AlphaOn α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.c0AlphaOn.uniformContinuousOn hα

theorem exists_secondJet (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      (∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α J.spaceDeriv s) ∧
      (∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s) ∧
      (∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α J.timeDeriv s) := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_secondJet

/-- Higher parabolic membership supplies one chosen second jet whose value and derivative
components are all `C^{0,α}`. -/
theorem exists_secondJet_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      ParabolicC0AlphaOn α u s ∧
        ParabolicC0AlphaOn α J.spaceDeriv s ∧
          ParabolicC0AlphaOn α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaOn α J.timeDeriv s := by
  rcases h with ⟨N, _hN, hNu⟩
  rcases hNu.exists_secondJet_c0AlphaNormLe_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨J, hu.c0AlphaOn, hx.c0AlphaOn, hxx.c0AlphaOn, ht.c0AlphaOn⟩

/-- Higher parabolic membership supplies one chosen second jet and one common
finite bound for the value, spatial derivative, second spatial derivative, and
time derivative components. -/
theorem exists_secondJet_norm_le (h : ParabolicC2AlphaOn α u s) :
    ∃ N ≥ 0, ∃ J : ParabolicSecondJet u s,
      (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖u z‖ ≤ N) ∧
        (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceDeriv z‖ ≤ N) ∧
          (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.spaceSecondDeriv z‖ ≤ N) ∧
            (∀ ⦃z : ℝ × X⦄, z ∈ s → ‖J.timeDeriv z‖ ≤ N) := by
  rcases h with ⟨N, hN, hNu⟩
  rcases hNu.exists_secondJet_norm_le_self with ⟨J, hu, hx, hxx, ht⟩
  exact ⟨N, hN, J, hu, hx, hxx, ht⟩

theorem exists_timeDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ∃ Nt ≥ 0, ParabolicC0AlphaNormLe Nt α Dt s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_timeDeriv

theorem exists_spaceDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ∃ Nx ≥ 0, ParabolicC0AlphaNormLe Nx α Dx s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_spaceDeriv

theorem exists_spaceSecondDeriv (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s,
      ∃ Nxx ≥ 0, ParabolicC0AlphaNormLe Nxx α J.spaceSecondDeriv s := by
  rcases h with ⟨N, _hN, hNu⟩
  exact hNu.exists_spaceSecondDeriv

theorem exists_timeDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ParabolicC0AlphaOn α Dt s := by
  rcases h.exists_timeDeriv with ⟨Dt, hDt, Nt, _hNt, hNt⟩
  exact ⟨Dt, hDt, hNt.c0AlphaOn⟩

theorem exists_spaceDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ParabolicC0AlphaOn α Dx s := by
  rcases h.exists_spaceDeriv with ⟨Dx, hDx, Nx, _hNx, hNx⟩
  exact ⟨Dx, hDx, hNx.c0AlphaOn⟩

theorem exists_spaceSecondDeriv_c0AlphaOn (h : ParabolicC2AlphaOn α u s) :
    ∃ J : ParabolicSecondJet u s, ParabolicC0AlphaOn α J.spaceSecondDeriv s := by
  rcases h.exists_spaceSecondDeriv with ⟨J, Nxx, _hNxx, hNxx⟩
  exact ⟨J, hNxx.c0AlphaOn⟩

theorem const (c : E) : ParabolicC2AlphaOn α (fun _ : ℝ × X => c) s :=
  of_normLe (ParabolicC2AlphaNormLe.const (X := X) (α := α) (s := s) c)

theorem zero : ParabolicC2AlphaOn α (fun _ : ℝ × X => (0 : E)) s :=
  of_normLe (ParabolicC2AlphaNormLe.zero (X := X) (E := E) (α := α) (s := s))

theorem add (hu : ParabolicC2AlphaOn α u s) (hv : ParabolicC2AlphaOn α v s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z + v z) s := by
  rcases hu with ⟨Nu, hNu, huN⟩
  rcases hv with ⟨Nv, hNv, hvN⟩
  exact ⟨Nu + Nv, add_nonneg hNu hNv, huN.add hvN⟩

theorem finset_sum {ι : Type*} (S : Finset ι) {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC2AlphaOn α (u i) s) :
    ParabolicC2AlphaOn α (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC2AlphaOn α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC2AlphaOn α (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

theorem neg (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => -u z) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨N, hN, huN.neg⟩

theorem sub (hu : ParabolicC2AlphaOn α u s) (hv : ParabolicC2AlphaOn α v s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z - v z) s := by
  rcases hu with ⟨Nu, hNu, huN⟩
  rcases hv with ⟨Nv, hNv, hvN⟩
  exact ⟨Nu + Nv, add_nonneg hNu hNv, huN.sub hvN⟩

theorem smul (c : ℝ) (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => c • u z) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨‖c‖ * N, mul_nonneg (norm_nonneg c) hN, huN.smul c⟩

theorem continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC2AlphaOn α u s) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => L (u z)) s := by
  rcases hu with ⟨N, hN, huN⟩
  exact ⟨_, (huN.continuousLinearMap L).nonneg, huN.continuousLinearMap L⟩

/-- A finite Pi-valued higher parabolic function projects to each coordinate as a higher
parabolic function. -/
theorem pi_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × X → ι → F} (hu : ParabolicC2AlphaOn α u s) (i : ι) :
    ParabolicC2AlphaOn α (fun z : ℝ × X => u z i) s := by
  simpa using hu.continuousLinearMap (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

theorem mono_set {t : Set (ℝ × X)} (h : ParabolicC2AlphaOn α u s) (hst : t ⊆ s) :
    ParabolicC2AlphaOn α u t := by
  rcases h with ⟨N, hN, hNu⟩
  exact ⟨N, hN, hNu.mono_set hst⟩

end ParabolicC2AlphaOn

/-- Coordinate parabolic `C^{2+α,1+α/2}` functions form a real submodule of all time-space
functions. -/
def parabolicC2AlphaSubmodule
    (X E : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Submodule ℝ ((ℝ × X) → E) where
  carrier := {u | ParabolicC2AlphaOn α u s}
  zero_mem' := by
    simpa using (ParabolicC2AlphaOn.zero (X := X) (E := E) (α := α) (s := s))
  add_mem' := by
    intro u v hu hv
    simpa [Pi.add_apply] using
      (ParabolicC2AlphaOn.add (X := X) (E := E) (α := α) (s := s) hu hv)
  smul_mem' := by
    intro c u hu
    simpa [Pi.smul_apply] using
      (ParabolicC2AlphaOn.smul (X := X) (E := E) (α := α) (s := s) c hu)

namespace parabolicC2AlphaSubmodule

variable {α : ℝ} {s : Set (ℝ × X)}

instance :
    CoeFun (parabolicC2AlphaSubmodule X E α s) (fun _ => (ℝ × X) → E) :=
  ⟨fun u => u.1⟩

@[simp]
theorem mem_iff {u : (ℝ × X) → E} :
    u ∈ parabolicC2AlphaSubmodule X E α s ↔ ParabolicC2AlphaOn α u s :=
  Iff.rfl

/-- Compose coordinate parabolic `C^{2+α,1+α/2}` functions with a continuous linear value map. -/
def continuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC2AlphaSubmodule X F α s where
  toFun u := ⟨fun z => L (u z), ParabolicC2AlphaOn.continuousLinearMap L u.2⟩
  map_add' := by
    intro u v
    ext z
    simp
  map_smul' := by
    intro c u
    ext z
    simp

@[simp]
theorem continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    continuousLinearMap (X := X) (E := E) (α := α) (s := s) L u z = L (u z) :=
  rfl

/-- Coordinate projection from a finite Pi-valued higher parabolic submodule. -/
def piApplyLinearMap {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : ι) :
    parabolicC2AlphaSubmodule X (ι → F) α s →ₗ[ℝ]
      parabolicC2AlphaSubmodule X F α s :=
  continuousLinearMap (X := X) (E := ι → F) (α := α) (s := s)
    (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F)

@[simp]
theorem piApplyLinearMap_apply {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ι) (u : parabolicC2AlphaSubmodule X (ι → F) α s)
    (z : ℝ × X) :
    piApplyLinearMap (X := X) (α := α) (s := s) i u z = u z i :=
  rfl

theorem c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ParabolicC0AlphaOn α (u : (ℝ × X) → E) s :=
  u.2.c0AlphaOn

/-- A higher submodule element has a chosen second jet whose value and derivative components
are all `C^{0,α}`. -/
theorem exists_secondJet_c0AlphaOn (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ J : ParabolicSecondJet (u : (ℝ × X) → E) s,
      ParabolicC0AlphaOn α (u : (ℝ × X) → E) s ∧
        ParabolicC0AlphaOn α J.spaceDeriv s ∧
          ParabolicC0AlphaOn α J.spaceSecondDeriv s ∧
            ParabolicC0AlphaOn α J.timeDeriv s :=
  u.2.exists_secondJet_c0AlphaOn

theorem exists_timeDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ Dt : ℝ × X → E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasDerivWithinAt (fun t : ℝ => u (t, z.2)) (Dt z)
          (timeSliceDomain s z.2) z.1) ∧
      ParabolicC0AlphaOn α Dt s :=
  u.2.exists_timeDeriv_c0AlphaOn

theorem exists_spaceDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ Dx : ℝ × X → X →L[ℝ] E,
      (∀ ⦃z : ℝ × X⦄, z ∈ s →
        HasFDerivWithinAt (fun x : X => u (z.1, x)) (Dx z)
          (spaceSliceDomain s z.1) z.2) ∧
      ParabolicC0AlphaOn α Dx s :=
  u.2.exists_spaceDeriv_c0AlphaOn

theorem exists_spaceSecondDeriv (u : parabolicC2AlphaSubmodule X E α s) :
    ∃ J : ParabolicSecondJet (u : (ℝ × X) → E) s,
      ParabolicC0AlphaOn α J.spaceSecondDeriv s :=
  u.2.exists_spaceSecondDeriv_c0AlphaOn

/-- Forget a coordinate parabolic `C^{2+α,1+α/2}` function to its value-level
`C^{0,α}` function. -/
def toC0AlphaSubmoduleLinearMap :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule X E α s where
  toFun u := ⟨u.1, u.2.c0AlphaOn⟩
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem toC0AlphaSubmoduleLinearMap_apply
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u z = u z :=
  rfl

/-- Read a coordinate parabolic `C^{2+α,1+α/2}` function as a continuous map on a compact
time-space piece, using its value-level `C^{0,α}` component. -/
def toContinuousMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : C(K, E) :=
  parabolicC0AlphaSubmodule.toContinuousMap
    (X := X) (E := E) (α := α) (s := s) hK hα
    (toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u)

@[simp]
theorem toContinuousMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (z : K) :
    toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z = u z.1 :=
  rfl

/-- Compact-piece value readout of a coordinate parabolic `C^{2+α,1+α/2}` function as a
linear map. -/
def toContinuousMapLinearMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] C(K, E) where
  toFun := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem toContinuousMapLinearMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    toContinuousMapLinearMap (X := X) (E := E) (α := α) (s := s) hK hα u =
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u :=
  rfl

/-- A single-radius `C^{2+α,1+α/2}` bound on a difference controls the compact value
readout sup norm. -/
theorem norm_toContinuousMap_sub_le_of_normLe {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  have h0 :
      ParabolicC0AlphaNormLe N α
        (fun z =>
          toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) u z -
            toC0AlphaSubmoduleLinearMap (X := X) (E := E) (α := α) (s := s) v z) s := by
    simpa using h.value_c0AlphaNormLe_self
  simpa [toContinuousMap] using
    parabolicC0AlphaSubmodule.norm_toContinuousMap_sub_le_of_normLe
      (X := X) (E := E) (α := α) (s := s) hK hα h0

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for one compact value readout. -/
theorem lipschitzOnWith_toContinuousMap_of_normLe_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) hK hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Read a coordinate parabolic `C^{2+α,1+α/2}` function on every compact piece of a chosen
cover, using its value-level `C^{0,α}` component. -/
def toCompactCoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) : ∀ i, C(Kc i, E) :=
  fun i => toContinuousMap (X := X) (E := E) (α := α) (s := s) (hKc i) hα u

@[simp]
theorem toCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      u z.1 :=
  rfl

/-- Finite-cover value readout as a linear map from coordinate parabolic
`C^{2+α,1+α/2}` functions into compact continuous-map pieces. -/
def toCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, E)) where
  toFun := toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    ext i z
    rfl
  map_smul' := by
    intro c u
    ext i z
    rfl

@[simp]
theorem toCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC2AlphaSubmodule X E α s) :
    toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u =
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- A single-radius `C^{2+α,1+α/2}` difference bound controls each compact-family value
readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_normLe {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα h

/-- A single-radius `C^{2+α,1+α/2}` difference bound controls the finite product of
compact-family value readouts in the product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg h.nonneg).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h i

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for the finite product of compact-family value readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- A finite compact-family value-readout Lipschitz estimate gives pointwise compact-coordinate
distance estimates. -/
theorem forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet) :
    ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ i (z : Kc i),
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i z)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i z)
        ≤ (L : ℝ) * dist u v := by
  intro u hu v hv i z
  have hC : 0 ≤ (L : ℝ) * dist u v :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist := h.dist_le_mul u hu v hv
  have hi :
      dist
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u) i)
        (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A v) i)
        ≤ (L : ℝ) * dist u v :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi z

/-- The linear compact-family value readout inherits the same finite product sup-norm
estimate from `C^{2+α,1+α/2}` difference control. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC2AlphaSubmodule X E α s}
    (h : ParabolicC2AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- Pairwise single-radius `C^{2+α,1+α/2}` difference estimates give a Lipschitz estimate
for the linear finite-cover value readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC2AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC2AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Equality of all compact-piece value readouts identifies two coordinate parabolic
`C^{2+α,1+α/2}` functions on the covered set. -/
theorem eqOn_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    (hcover : s ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC2AlphaSubmodule X E α s}
    (h :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v) :
    EqOn u v s := by
  intro z hz
  rcases mem_iUnion.mp (hcover hz) with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- Compact value readout is injective on coordinate parabolic `C^{2+α,1+α/2}` functions
when the chosen compact pieces cover all time-space. -/
theorem toCompactCoordFamily_injective_of_iUnion_eq_univ {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (hcover : (⋃ i, (Kc i : Set (ℝ × X))) = Set.univ) :
    Function.Injective
      (toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα) := by
  intro u v h
  ext z
  have hzcover : z ∈ ⋃ i, (Kc i : Set (ℝ × X)) := by
    simp [hcover]
  rcases mem_iUnion.mp hzcover with ⟨i, hzi⟩
  have hz_eq :
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i ⟨z, hzi⟩ =
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i ⟨z, hzi⟩ := by
    rw [h]
  simpa using hz_eq

/-- Restriction to a smaller set as a linear map between coordinate parabolic
`C^{2+α,1+α/2}` spaces. -/
def restrictLinearMap {t : Set (ℝ × X)} (hst : t ⊆ s) :
    parabolicC2AlphaSubmodule X E α s →ₗ[ℝ] parabolicC2AlphaSubmodule X E α t where
  toFun u := ⟨u.1, u.2.mono_set hst⟩
  map_add' := by
    intro u v
    ext z
    rfl
  map_smul' := by
    intro c u
    ext z
    rfl

@[simp]
theorem restrictLinearMap_apply {t : Set (ℝ × X)} (hst : t ⊆ s)
    (u : parabolicC2AlphaSubmodule X E α s) (z : ℝ × X) :
    restrictLinearMap (X := X) (E := E) (α := α) hst u z = u z :=
  rfl

end parabolicC2AlphaSubmodule

end AnalyticPDE
end RicciFlow
