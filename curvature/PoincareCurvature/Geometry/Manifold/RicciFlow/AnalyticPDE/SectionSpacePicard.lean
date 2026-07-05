module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D

/-!
# Section-space Picard–Lindelöf constructor (route (ii))

The `picard` field of a `TimeDependentGeometricRicciDeTurckBanachChart` asks for
`IsPicardLindelof A` for the time-dependent Banach representative `A` on the
`ContinuousSectionSpace`.  Roadmap point 4 route (ii) supplies this through the
Banach-space Picard–Lindelöf foundation
`RicciFlow.AnalyticPDE.isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`, whose
hypotheses are boundedness, uniform Lipschitzness and time-continuity of `A`.

This module assembles the three coordinate→section handoffs proved in `ContinuousSection.lean`
(`norm_le_of_forall_coord_norm_le`, `lipschitzWith_of_forall_coord_dist_le`,
`continuousOn_of_forall_coord_continuousOn`) with that foundation into a single constructor
`isPicardLindelof_continuousSectionSpace_of_forall_coord`: from *coordinatewise* (local
trivialization readout) boundedness, Lipschitz and continuity data it produces
`IsPicardLindelof A` in exactly the interval/anchor/constant shape consumed by the chart's
`picard` field.  This is the section-space `picard`-field constructor for the mild/regularised
Ricci–DeTurck chart.
-/

@[expose] public noncomputable section

open scoped NNReal Topology
open RicciFlow.AnalyticPDE

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

/-- **Section-space Picard–Lindelöf constructor (route (ii)).**  A time-dependent operator `A` on
the `ContinuousSectionSpace` whose local trivialization readouts are, uniformly over sections,
bounded by `L`, `K`-Lipschitz in the section, and time-continuous on `[t₀, T]`, is
`IsPicardLindelof` with anchor `t₀`, initial datum `x0`, radius `L·(T−t₀)₊ + 1`, and Lipschitz
constant `K` — exactly the shape demanded by the
`TimeDependentGeometricRicciDeTurckBanachChart.picard` field.  Assembles the coordinate→section
boundedness / Lipschitz / continuity handoffs with the Banach ODE foundation
`isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Bundle.Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x0 : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ T : ℝ) (hT : t₀ < T) (L K : ℝ≥0)
    (hbound : ∀ (t : ℝ)
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x‖ ≤ (L : ℝ))
    (hlip : ∀ (t : ℝ)
        (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)
        (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀
        (s : ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
        (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 (L * (T - t₀).toNNReal + 1) 0 L K := by
  refine isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc A x0 t₀ T hT L K ?_ ?_ ?_
  · intro t s
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L) (fun i x => hbound t s i x)
  · intro t
    exact lipschitzWith_of_forall_coord_dist_le (fun s s' i x => hlip t s s' i x)
  · intro s
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s i)

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
