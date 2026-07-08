import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionPicardTangent
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.AutonomousResolventExp

/-!
# The frozen (affine) Ricci–DeTurck chart operator's explicit global evolution

The **frozen** geometric Ricci–DeTurck chart operator is *affine*: with the DeTurck coefficient
`P := ∇W` frozen at the initial data and the principal Ricci source `b` frozen as a fixed
`ContinuousSectionSpace` value, it acts as

`A τ s = deTurckReactionSectionMap P s + b = L s + b`,

where `L := deTurckReactionSectionMapL … hP : CSS →L[ℝ] CSS` is the bounded-linear reaction
generator (`GeometricReactionPicardTangent`).  Since the continuous section space `CSS` is a
**complete** normed `ℝ`-space, the abstract affine autonomous ODE machinery
(`AutonomousResolventExp`: `affineFundamentalSolution` via the augmentation trick, its
`HasDerivAt`, initial value, and uniqueness) applies verbatim.

This module performs the **Duhamel assembly** the plan named as NEXT: it imports both frontier
files and specialises the abstract affine resolvent to `L` and a general frozen source `b`, giving
the concrete frozen chart operator a genuine, *explicit and global* solution
`deTurckFrozenAffineEvolution`.  We prove it starts at `σ₀`, solves the exact frozen ODE
`σ' = deTurckReactionSectionMap P σ + b`, and is the **unique** such global solution — the
existence-and-uniqueness core the chart-closure `realization`/`encode` fields consume for the
frozen (autonomous) chart.  A geometric corollary specialises `P`/`b` to the genuine geometric
data `∇W` / `intrinsicRicciFlowRHSSectionSpace g t`, matching the operator solved by
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`.

No parabolic Schauder content is used: the frozen operator is bounded-linear, so its evolution is
the operator exponential of the augmented generator.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Bundle RicciFlow
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization
open RicciFlow.AnalyticPDE.SmoothDependenceCk

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := TM))

/-- **The frozen (affine) Ricci–DeTurck chart operator's explicit global evolution.**  With the
bounded-linear reaction generator `L := deTurckReactionSectionMapL … hP` and a fixed source
`b : CSS`, this is the affine autonomous fundamental solution `t ↦ affineFundamentalSolution L b t₀ σ₀`
on the complete section space `CSS`.  It is the global-in-time explicit solution of the frozen chart
ODE `σ' = L σ + b`, `σ t₀ = σ₀`. -/
noncomputable def deTurckFrozenAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
  affineFundamentalSolution
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0

/-- The frozen affine evolution starts at the initial section `σ₀`. -/
theorem deTurckFrozenAffineEvolution_initial
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t₀ = σ0 :=
  affineFundamentalSolution_initial
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0

/-- **The frozen affine evolution solves the frozen chart ODE
`σ' = deTurckReactionSectionMap P σ + b`.**  Immediate from the abstract affine ODE solution
(`hasDerivAt_affineFundamentalSolution`) once the bounded-linear generator's value is decoded to the
raw reaction self-map (`deTurckReactionSectionMapL_apply`). -/
theorem hasDerivAt_deTurckFrozenAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) :
    HasDerivAt (deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0)
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP
          (deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t)
        + b) t := by
  have h := hasDerivAt_affineFundamentalSolution
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 t
  rwa [deTurckReactionSectionMapL_apply] at h

/-- **Uniqueness for the frozen chart ODE.**  Any global solution `σ` of
`σ' = deTurckReactionSectionMap P σ + b` with `σ t₀ = σ₀` coincides with the explicit affine
evolution.  The uniqueness half of the frozen chart's Cauchy problem, consumed by the `encode`
field. -/
theorem deTurckFrozenAffineEvolution_unique
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {y : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    (hy : ∀ t, HasDerivAt y
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP (y t) + b) t)
    (h0 : y t₀ = σ0) (t : ℝ) :
    y t = deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t := by
  refine eq_affineFundamentalSolution_of_hasDerivAt
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 ?_ h0 t
  intro s
  rw [deTurckReactionSectionMapL_apply]
  exact hy s

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
