module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
public import Mathlib.Topology.ContinuousMap.Compact

set_option linter.unusedSectionVars false

/-!
# Parabolic Holder function spaces

This module packages the parabolic `C^{0,α}` predicate as a linear function
space and gives the basic compact-piece readouts used by later Schauder and
Banach-chart constructions.  The norms and Schauder estimates are intentionally
not asserted here; this file only records the algebraic function-space layer
that follows from the existing Holder API.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

/-- Single-radius parabolic `C^{0,α}` control.  The radius `N` dominates the sum of a sup
constant and a Holder constant.  This is the closed-ball predicate for the eventual
`C^{0,α}` norm, kept constructive so later estimates can choose explicit constants. -/
def ParabolicC0AlphaNormLe {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    (N α : ℝ) (u : ℝ × X → E) (s : Set (ℝ × X)) : Prop :=
  ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧ ParabolicC0AlphaWith B H α u s

namespace ParabolicC0AlphaNormLe

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {N N₁ N₂ α : ℝ} {u v : ℝ × X → E} {s t : Set (ℝ × X)}

theorem nonneg (h : ParabolicC0AlphaNormLe N α u s) : 0 ≤ N := by
  rcases h with ⟨B, hB, H, hH, hBH, _⟩
  exact (add_nonneg hB hH).trans hBH

theorem c0AlphaOn (h : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaOn α u s := by
  rcases h with ⟨B, hB, H, hH, _, hBH⟩
  exact ⟨B, hB, H, hH, hBH⟩

theorem c0AlphaWith_self (h : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaWith N N α u s := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  have hB_le : B ≤ N := by linarith
  have hH_le : H ≤ N := by linarith
  exact hBH.mono_const hB_le hH_le

/-- The single radius controls the pointwise norm on the domain. -/
theorem norm_le (h : ParabolicC0AlphaNormLe N α u s) ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖u z‖ ≤ N := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  have hB_le : B ≤ N := by linarith
  exact (hBH.bounded hz).trans hB_le

/-- A single-radius bound on a difference gives the corresponding pointwise distance bound. -/
theorem dist_le_of_sub (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    dist (u z) (v z) ≤ N := by
  simpa [dist_eq_norm] using h.norm_le hz

theorem of_c0AlphaWith {B H : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H)
    (h : ParabolicC0AlphaWith B H α u s) :
    ParabolicC0AlphaNormLe (B + H) α u s :=
  ⟨B, hB, H, hH, le_rfl, h⟩

theorem exists_of_c0AlphaOn (h : ParabolicC0AlphaOn α u s) :
    ∃ N ≥ 0, ParabolicC0AlphaNormLe N α u s := by
  rcases h with ⟨B, hB, H, hH, hBH⟩
  exact ⟨B + H, add_nonneg hB hH, of_c0AlphaWith hB hH hBH⟩

theorem mono_const (h : ParabolicC0AlphaNormLe N₁ α u s) (hNN : N₁ ≤ N₂) :
    ParabolicC0AlphaNormLe N₂ α u s := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  exact ⟨B, hB, H, hH, hsum.trans hNN, hBH⟩

theorem mono_set (h : ParabolicC0AlphaNormLe N α u s) (hst : t ⊆ s) :
    ParabolicC0AlphaNormLe N α u t := by
  rcases h with ⟨B, hB, H, hH, hsum, hBH⟩
  exact ⟨B, hB, H, hH, hsum, hBH.mono_set hst⟩

theorem zero :
    ParabolicC0AlphaNormLe 0 α (fun _ : ℝ × X => (0 : E)) s := by
  refine ⟨0, le_rfl, 0, le_rfl, by simp, ?_⟩
  simpa using
    (ParabolicC0AlphaWith.const (X := X) (E := E) (α := α) (s := s) (0 : E)
      (by simp) le_rfl)

theorem const (c : E) :
    ParabolicC0AlphaNormLe ‖c‖ α (fun _ : ℝ × X => c) s := by
  refine ⟨‖c‖, norm_nonneg c, 0, le_rfl, by simp, ?_⟩
  exact ParabolicC0AlphaWith.const (X := X) (α := α) (s := s) c le_rfl le_rfl

theorem add (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ + N₂) α (fun z => u z + v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  refine ⟨Bu + Bv, add_nonneg hBu hBv, Hu + Hv, add_nonneg hHu hHv, ?_,
    hu_ctrl.add hv_ctrl⟩
  linarith

theorem finset_sum {ι : Type*} (S : Finset ι) {N : ι → ℝ}
    {u : ι → ℝ × X → E}
    (h : ∀ i ∈ S, ParabolicC0AlphaNormLe (N i) α (u i) s) :
    ParabolicC0AlphaNormLe (∑ i ∈ S, N i) α
      (fun z => ∑ i ∈ S, u i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (zero (X := X) (E := E) (α := α) (s := s))
  | insert a S ha ih =>
      have ha_ctrl : ParabolicC0AlphaNormLe (N a) α (u a) s := h a (by simp)
      have hS_ctrl : ParabolicC0AlphaNormLe (∑ i ∈ S, N i) α
          (fun z => ∑ i ∈ S, u i z) s := by
        exact ih fun i hi => h i (by simp [hi])
      have hadd := add ha_ctrl hS_ctrl
      simpa [Finset.sum_insert, ha] using hadd

theorem neg (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α (fun z => -u z) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  exact ⟨B, hB, H, hH, hsum, hctrl.neg⟩

theorem sub (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ + N₂) α (fun z => u z - v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  refine ⟨Bu + Bv, add_nonneg hBu hBv, Hu + Hv, add_nonneg hHu hHv, ?_,
    hu_ctrl.sub hv_ctrl⟩
  linarith

theorem norm (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe N α (fun z => ‖u z‖) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  exact ⟨B, hB, H, hH, hsum, hctrl.norm⟩

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    (c : 𝕜) (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖c‖ * N) α (fun z => c • u z) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB,
    ‖c‖ * H, mul_nonneg (norm_nonneg c) hH, ?_, hctrl.smul c⟩
  calc
    ‖c‖ * B + ‖c‖ * H = ‖c‖ * (B + H) := by ring
    _ ≤ ‖c‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg c)

theorem continuousLinearMap {F : Type*} [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hu : ParabolicC0AlphaNormLe N α u s) :
    ParabolicC0AlphaNormLe (‖L‖ * N) α (fun z => L (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨‖L‖ * B, mul_nonneg (norm_nonneg L) hB,
    ‖L‖ * H, mul_nonneg (norm_nonneg L) hH, ?_, hctrl.continuousLinearMap L⟩
  calc
    ‖L‖ * B + ‖L‖ * H = ‖L‖ * (B + H) := by ring
    _ ≤ ‖L‖ * N := mul_le_mul_of_nonneg_left hsum (norm_nonneg L)

theorem pi {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    {N : ι → ℝ} {u : ℝ × X → ι → F}
    (h : ∀ i, ParabolicC0AlphaNormLe (N i) α (fun z => u z i) s) :
    ParabolicC0AlphaNormLe (∑ i, N i) α u s := by
  classical
  choose B hB H hH hsum hctrl using h
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB i,
    ∑ i, H i, Finset.sum_nonneg fun i _ => hH i, ?_,
    ParabolicC0AlphaWith.pi (X := X) (E := F) (α := α) (s := s)
      (B := B) (H := H) hB hH hctrl⟩
  calc
    (∑ i, B i) + ∑ i, H i = ∑ i, (B i + H i) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ i, N i := Finset.sum_le_sum fun i _ => hsum i

theorem mul {A : Type*} [NormedRing A] {N₁ N₂ α : ℝ}
    {u v : ℝ × X → A} {s : Set (ℝ × X)}
    (hu : ParabolicC0AlphaNormLe N₁ α u s)
    (hv : ParabolicC0AlphaNormLe N₂ α v s) :
    ParabolicC0AlphaNormLe (N₁ * N₂) α (fun z => u z * v z) s := by
  rcases hu with ⟨Bu, hBu, Hu, hHu, hu_sum, hu_ctrl⟩
  rcases hv with ⟨Bv, hBv, Hv, hHv, hv_sum, hv_ctrl⟩
  have hNu : 0 ≤ N₁ := (add_nonneg hBu hHu).trans hu_sum
  refine ⟨Bu * Bv, mul_nonneg hBu hBv, Bu * Hv + Bv * Hu,
    add_nonneg (mul_nonneg hBu hHv) (mul_nonneg hBv hHu), ?_,
    hu_ctrl.mul hv_ctrl hBu⟩
  have hleft :
      Bu * Bv + (Bu * Hv + Bv * Hu) ≤ (Bu + Hu) * (Bv + Hv) := by
    nlinarith [mul_nonneg hHu hHv]
  have hright : (Bu + Hu) * (Bv + Hv) ≤ N₁ * N₂ :=
    mul_le_mul hu_sum hv_sum (add_nonneg hBv hHv) hNu
  exact hleft.trans hright

theorem comp_lipschitzOnWith {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ)
    (hφL : LipschitzOnWith K φ (u '' s)) :
    ParabolicC0AlphaNormLe (Bφ + (K : ℝ) * N) α (fun z => φ (u z)) s := by
  rcases hu with ⟨B, hB, H, hH, hsum, hctrl⟩
  refine ⟨Bφ, hBφ, (K : ℝ) * H, mul_nonneg (NNReal.coe_nonneg K) hH, ?_,
    hctrl.comp_lipschitzOnWith hφB hφL⟩
  have hH_le_N : H ≤ N := by linarith
  have hKH_le_KN : (K : ℝ) * H ≤ (K : ℝ) * N :=
    mul_le_mul_of_nonneg_left hH_le_N (NNReal.coe_nonneg K)
  linarith

theorem comp_lipschitzWith {F : Type*} [NormedAddCommGroup F]
    {Bφ : ℝ} {K : ℝ≥0} {φ : E → F}
    (hu : ParabolicC0AlphaNormLe N α u s) (hBφ : 0 ≤ Bφ)
    (hφB : ∀ y ∈ u '' s, ‖φ y‖ ≤ Bφ) (hφ : LipschitzWith K φ) :
    ParabolicC0AlphaNormLe (Bφ + (K : ℝ) * N) α (fun z => φ (u z)) s :=
  hu.comp_lipschitzOnWith hBφ hφB hφ.lipschitzOnWith

theorem continuousOn (h : ParabolicC0AlphaNormLe N α u s) (hα : 0 < α) :
    ContinuousOn u s :=
  h.c0AlphaOn.continuousOn hα

theorem uniformContinuousOn (h : ParabolicC0AlphaNormLe N α u s) (hα : 0 < α) :
    UniformContinuousOn u s :=
  h.c0AlphaOn.uniformContinuousOn hα

end ParabolicC0AlphaNormLe

/-- Scalar multiples and sums of parabolic `C^{0,α}` functions form a real submodule of all
time-space functions. -/
def parabolicC0AlphaSubmodule
    (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Submodule ℝ ((ℝ × X) → E) where
  carrier := {u | ParabolicC0AlphaOn α u s}
  zero_mem' := by
    simpa using (ParabolicC0AlphaOn.const (X := X) (α := α) (s := s) (0 : E))
  add_mem' := by
    intro u v hu hv
    simpa [Pi.add_apply] using
      (ParabolicC0AlphaOn.add (X := X) (α := α) (s := s) hu hv)
  smul_mem' := by
    intro c u hu
    simpa [Pi.smul_apply] using
      (ParabolicC0AlphaOn.smul (X := X) (α := α) (s := s) (𝕜 := ℝ) c hu)

namespace parabolicC0AlphaSubmodule

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : ℝ} {s t : Set (ℝ × X)}

instance :
    CoeFun (parabolicC0AlphaSubmodule X E α s) (fun _ => (ℝ × X) → E) :=
  ⟨fun u => u.1⟩

@[simp]
theorem mem_iff {u : (ℝ × X) → E} :
    u ∈ parabolicC0AlphaSubmodule X E α s ↔ ParabolicC0AlphaOn α u s :=
  Iff.rfl

/-- Restriction to a smaller set as a linear map between parabolic Holder function spaces. -/
def restrictLinearMap (hst : t ⊆ s) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule X E α t where
  toFun u := ⟨u.1, u.2.mono_set hst⟩
  map_add' := by
    intro u v
    ext z
    simp
  map_smul' := by
    intro c u
    ext z
    simp

@[simp]
theorem restrictLinearMap_apply (hst : t ⊆ s)
    (u : parabolicC0AlphaSubmodule X E α s) (z : ℝ × X) :
    restrictLinearMap (X := X) (E := E) (α := α) hst u z = u z :=
  rfl

/-- Read a parabolic `C^{0,α}` function as a continuous map on a compact time-space piece. -/
def toContinuousMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) : C(K, E) where
  toFun z := u z.1
  continuous_toFun := by
    have hu_cont : ContinuousOn u.1 s := u.2.continuousOn hα
    exact continuousOn_iff_continuous_restrict.mp (hu_cont.mono hK)

@[simp]
theorem toContinuousMap_apply {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) (z : K) :
    toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u z = u z.1 :=
  rfl

/-- Compact-piece readout of a parabolic `C^{0,α}` function as a linear map. -/
def toContinuousMapLinearMap {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] C(K, E) where
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
    (u : parabolicC0AlphaSubmodule X E α s) :
    toContinuousMapLinearMap (X := X) (E := E) (α := α) (s := s) hK hα u =
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u :=
  rfl

/-- A single-radius `C^{0,α}` bound on a difference controls the compact readout sup norm. -/
theorem norm_toContinuousMap_sub_le_of_normLe {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  rcases h with ⟨B, hB, H, hH, hsum, hctrl⟩
  have hN : 0 ≤ N := (add_nonneg hB hH).trans hsum
  have hB_le_N : B ≤ N := by linarith
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) hN).mpr ?_
  intro z
  have hz : z.1 ∈ s := hK z.2
  calc
    ‖(toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ B := hctrl.bounded hz
    _ ≤ N := hB_le_N

/-- A sup-bound on a difference controls the compact readout sup norm.  This lower-level
readout is useful when an estimate gives only the `C⁰` part of the parabolic norm. -/
theorem norm_toContinuousMap_sub_le_of_bounded {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v‖ ≤ N := by
  refine (ContinuousMap.norm_le
    (f := toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
      toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) hN).mpr ?_
  intro z
  have hz : z.1 ∈ s := hK z.2
  calc
    ‖(toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα u -
        toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα v) z‖ =
        ‖u z.1 - v z.1‖ := by
          rfl
    _ ≤ N := h hz

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for one
compact-piece readout. -/
theorem lipschitzOnWith_toContinuousMap_of_normLe_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) hK hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for one compact-piece
readout. -/
theorem lipschitzOnWith_toContinuousMap_of_bounded_sub {Y : Type*} [PseudoMetricSpace Y]
    {K : TopologicalSpace.Compacts (ℝ × X)}
    (hK : (K : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y => toContinuousMap (X := X) (E := E) (α := α) (s := s) hK hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toContinuousMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) hK hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Read a parabolic `C^{0,α}` function on every compact piece of a chosen cover. -/
def toCompactCoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) : ∀ i, C(Kc i, E) :=
  fun i => toContinuousMap (X := X) (E := E) (α := α) (s := s) (hKc i) hα u

@[simp]
theorem toCompactCoordFamily_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) (i : κ) (z : Kc i) :
    toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i z =
      u z.1 :=
  rfl

/-- Finite-cover coordinate readout as a linear map into the product of compact continuous-map
pieces. -/
def toCompactCoordFamilyLinearMap {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] (∀ i, C(Kc i, E)) where
  toFun := toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα
  map_add' := by
    intro u v
    ext i z
    simp [toCompactCoordFamily, toContinuousMap]
  map_smul' := by
    intro c u
    ext i z
    simp [toCompactCoordFamily, toContinuousMap]

@[simp]
theorem toCompactCoordFamilyLinearMap_apply {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    (u : parabolicC0AlphaSubmodule X E α s) :
    toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u =
      toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u :=
  rfl

/-- A single-radius `C^{0,α}` bound on a difference controls each compact-family readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_normLe {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα h

/-- A sup-bound on a difference controls each compact-family readout. -/
theorem norm_toCompactCoordFamily_sub_le_of_bounded {κ : Type*}
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) (i : κ) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u i -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v i‖ ≤ N :=
  norm_toContinuousMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) (hKc i) hα hN h

/-- A single-radius `C^{0,α}` difference bound controls the finite product of compact-family
readouts in the product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg h.nonneg).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h i

/-- A sup-bound on a difference controls the finite product of compact-family readouts in the
product sup norm. -/
theorem norm_toCompactCoordFamily_family_sub_le_of_bounded {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα u -
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα v‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg hN).2 fun i => ?_
  exact norm_toCompactCoordFamily_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα hN h i

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for the
finite product of compact-family readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for the finite product of
compact-family readouts. -/
theorem lipschitzOnWith_toCompactCoordFamily_of_bounded_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamily (X := X) (E := E) (α := α) (s := s) Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamily_family_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- A finite compact-family readout Lipschitz estimate gives pointwise compact-coordinate
distance estimates. -/
theorem forall_compactCoord_dist_le_of_toCompactCoordFamily_lipschitzOnWith {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
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

/-- The linear compact-family readout inherits the same finite product sup-norm estimate. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_normLe {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicC0AlphaNormLe N α (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_normLe
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα h

/-- The linear compact-family readout inherits the same finite product sup-norm estimate from a
sup-bound on the difference. -/
theorem norm_toCompactCoordFamilyLinearMap_sub_le_of_bounded {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {N : ℝ} (hN : 0 ≤ N) {u v : parabolicC0AlphaSubmodule X E α s}
    (h : ParabolicBoundedWith N (fun z => u z - v z) s) :
    ‖toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα u -
      toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
        Kc hKc hα v‖ ≤ N := by
  simpa using norm_toCompactCoordFamily_family_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα hN h

/-- Pairwise single-radius `C^{0,α}` difference estimates give a Lipschitz estimate for the
linear finite-cover readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_normLe_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicC0AlphaNormLe ((L : ℝ) * dist u v) α (fun z => A u z - A v z) s) :
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

/-- Pairwise sup-bound difference estimates give a Lipschitz estimate for the linear finite-cover
readout. -/
theorem lipschitzOnWith_toCompactCoordFamilyLinearMap_of_bounded_sub {Y κ : Type*}
    [PseudoMetricSpace Y] [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts (ℝ × X))
    (hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {stateSet : Set Y} {L : ℝ≥0} {A : Y → parabolicC0AlphaSubmodule X E α s}
    (h : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ParabolicBoundedWith ((L : ℝ) * dist u v) (fun z => A u z - A v z) s) :
    LipschitzOnWith L
      (fun u : Y =>
        toCompactCoordFamilyLinearMap (X := X) (E := E) (α := α) (s := s)
          Kc hKc hα (A u))
      stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hnorm := norm_toCompactCoordFamilyLinearMap_sub_le_of_bounded
    (X := X) (E := E) (α := α) (s := s) Kc hKc hα
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg) (h hu hv)
  simpa [dist_eq_norm] using hnorm

/-- Equality of all compact-piece readouts identifies the two functions on the covered set. -/
theorem eqOn_of_toCompactCoordFamily_eq {κ : Type*}
    {Kc : κ → TopologicalSpace.Compacts (ℝ × X)}
    {hKc : ∀ i, (Kc i : Set (ℝ × X)) ⊆ s} {hα : 0 < α}
    (hcover : s ⊆ ⋃ i, (Kc i : Set (ℝ × X)))
    {u v : parabolicC0AlphaSubmodule X E α s}
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

/-- Compact-piece readout is injective when the chosen compact pieces cover all time-space. -/
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

end parabolicC0AlphaSubmodule

end AnalyticPDE
end RicciFlow
