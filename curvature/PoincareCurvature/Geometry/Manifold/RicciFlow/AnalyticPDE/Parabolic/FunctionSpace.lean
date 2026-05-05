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
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

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
