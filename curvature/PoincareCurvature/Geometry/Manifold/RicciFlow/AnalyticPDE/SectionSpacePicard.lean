module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE

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

/-- **Section-space bounded–Lipschitz evolution existence & uniqueness (transport step (a)).**
From coordinatewise (local trivialization readout) boundedness ≤ `L`, `K`-Lipschitz-in-section and
time-continuity on `[t₀, T]`, the time-dependent operator `A` on the (complete) section space admits
a unique `[t₀, T]`-evolution `α` with `α t₀ = x0` solving `α'(t) = A t (α t)`.  This lifts the model
`ℝⁿ` mild-solution existence–uniqueness to the manifold-bundle section space (`CompleteSpace` from
`CompleteSpace F`), the state space of the chart's `A`, by assembling the coordinate→section handoffs
with the Banach evolution foundation `bounded_lipschitz_evolution_exists_unique_timeDependent_Icc`. -/
theorem sectionSpace_evolution_exists_unique_of_forall_coord
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
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
    (∃ α : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = x0 ∧
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t)) ∧
    (∀ α β : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = β t₀ →
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t) →
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt β (A t (β t)) (Set.Icc t₀ T) t) →
      ∀ t ∈ Set.Icc t₀ T, α t = β t) := by
  refine bounded_lipschitz_evolution_exists_unique_timeDependent_Icc
    A x0 hT (L := L) (K := K) ?_ ?_ ?_
  · intro t s
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L) (fun i x => hbound t s i x)
  · intro t
    exact lipschitzWith_of_forall_coord_dist_le (fun s s' i x => hlip t s s' i x)
  · intro s
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s i)

/-- **Section-space ball-local (superset) Picard–Lindelöf constructor (route (ii), honest form).**
The globally-`C⁰`-unbounded second-order Ricci–DeTurck operator cannot satisfy the *global* bound of
`isPicardLindelof_continuousSectionSpace_of_forall_coord`; the honest `picard` datum is only
ball-local.  From coordinatewise (local trivialization readout) boundedness ≤ `L` and
`K`-Lipschitz-in-section control over a set `S ⊇ closedBall x0 a` (e.g. the positive-definite locus),
together with time-continuity on `[t₀, T]` at each point of the ball and the compatibility
`L·(T − t₀) ≤ a`, the time-dependent operator `A` is `IsPicardLindelof` with anchor `t₀`, initial
datum `x0`, radius **`a`** (the chart's own radius, not the global `L·(T−t₀)₊+1`) and Lipschitz
constant `K` — exactly the shape `IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 L K` demanded by the
`TimeDependentGeometricRicciDeTurckBanachChart.picard` field.  Assembles the coordinate→section
boundedness / Lipschitz / continuity handoffs with the ball-local Banach ODE foundation
`isPicardLindelof_of_boundedOn_lipschitzOn_superset_timeDependent_Icc`. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord_superset
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
    (t₀ T : ℝ) (hT : t₀ < T) (a L K : ℝ≥0)
    (S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (hball : Metric.closedBall x0 (a : ℝ) ⊆ S)
    (hbound : ∀ t ∈ Set.Icc t₀ T, ∀ s ∈ S, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x‖ ≤ (L : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ S → ∀ ⦃s'⦄, s' ∈ S → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hLa : (L : ℝ) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 L K := by
  refine isPicardLindelof_of_boundedOn_lipschitzOn_superset_timeDependent_Icc
    A x0 t₀ T hT a L K hball ?_ ?_ ?_ hLa
  · intro t ht
    exact lipschitzOnWith_of_forall_coord_dist_le
      (fun s hs s' hs' i x => hlip t ht hs hs' i x)
  · intro s hs
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s hs i)
  · intro t ht s hs
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg L)
      (fun i x => hbound t ht s hs i x)

/-- **Section-space centre-bound ball-local Picard–Lindelöf constructor (route (ii), sharpest
honest form).**  The most economical `picard` datum: the only norm information required about the
`C⁰`-unbounded operator is its coordinatewise readout size at the **fixed centre** `x0` (the initial
metric `g₀`), not a bound over a whole ball — the ball bound `Mc + K·a` is *derived* from the
`K`-Lipschitz control on `closedBall x0 a`.  From coordinatewise `K`-Lipschitz-in-section control on
the ball, time-continuity on `[t₀, T]` at each ball point, the centre readout bound
`‖(A t x0)ᵢ x‖ ≤ Mc`, and the compatibility `(Mc + K·a)·(T − t₀) ≤ a`, the time-dependent operator
`A` is `IsPicardLindelof` with anchor `t₀`, initial datum `x0`, radius `a`, bound `Mc + K·a` and
Lipschitz constant `K` — the exact shape of `TimeDependentGeometricRicciDeTurckBanachChart.picard`.
Assembles the coordinate→section handoffs with the centre-bound Banach ODE foundation
`isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc`; this is the form where the
only genuinely analytic input is the size of the Ricci–DeTurck operator applied to the initial
metric. -/
theorem isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
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
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  refine isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc
    A x0 t₀ T hT a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact lipschitzOnWith_of_forall_coord_dist_le
      (fun s hs s' hs' i x => hlip t ht hs hs' i x)
  · intro s hs
    exact continuousOn_of_forall_coord_continuousOn (fun i => hcont s hs i)
  · intro t ht
    exact norm_le_of_forall_coord_norm_le (NNReal.coe_nonneg Mc)
      (fun i x => hcenter t ht i x)

/-- **Section-space centre-bound Picard endpoint chooser (route (ii) capstone).**  The
`TimeDependentGeometricRicciDeTurckBanachChart`'s only `T`-dependent data are `hT : t₀ < T` and the
`picard` field (its `lipschitz`/`geometric` fields quantify over *all* times).  This lemma supplies
both at once: from *forward*-time-uniform (on `Set.Ici t₀`) coordinatewise `K`-Lipschitz-in-section
control on `closedBall x0 a`, continuity there, and the centre readout bound `‖(A t x0)ᵢ x‖ ≤ Mc`
(for a genuinely positive radius `a`), there **exists** a forward endpoint `T > t₀` for which `A` is
`IsPicardLindelof` with radius `a`, bound `Mc + K·a`, Lipschitz `K` — the chart's exact `picard`
shape.  The endpoint is produced by `exists_forwardTime_mul_sub_le` (satisfying the time-radius
compatibility `(Mc + K·a)·(T − t₀) ≤ a` automatically), letting the chart *choose* its per-IVP Picard
window from the analytic size constants `Mc` (centre bound) and `K` (Lipschitz constant) alone. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
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
    (t₀ : ℝ) (a K Mc : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Ici t₀, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Ici t₀))
    (hcenter : ∀ t ∈ Set.Ici t₀, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  obtain ⟨T, hT, hLa⟩ := RicciFlow.AnalyticPDE.exists_forwardTime_mul_sub_le t₀ a K Mc ha
  refine ⟨T, hT, ?_⟩
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ T hT a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact hlip t (Set.Icc_subset_Ici_self ht)
  · intro s hs i
    exact (hcont s hs i).mono Set.Icc_subset_Ici_self
  · intro t ht
    exact hcenter t (Set.Icc_subset_Ici_self ht)

/-- **Section-space evolution existence from centre-bound ball-local data (honest form).**  The
ball-local companion of `sectionSpace_evolution_exists_unique_of_forall_coord` (which assumes the
unattainable *global* bound): from the honest centre-bound ball-local coordinatewise data — `K`-
Lipschitz-in-section on `closedBall x0 a`, time-continuity there, centre readout bound
`‖(A t x0)ᵢ x‖ ≤ Mc`, and `(Mc + K·a)·(T − t₀) ≤ a` — the time-dependent operator `A` on the complete
section space admits a `[t₀, T]`-evolution `α` with `α t₀ = x0` solving `α'(t) = A t (α t)`.  Combines
the centre-bound section-space Picard constructor with the Mathlib differential Picard–Lindelöf
theorem `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.  This is the raw evolution
curve a downstream `realization` decode into a genuine intrinsic De Turck local solution consumes,
now available from the honest (not globally bounded) analytic input. -/
theorem sectionSpace_evolution_exists_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
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
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ)) :
    ∃ α : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      α t₀ = x0 ∧
      (∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt α (A t (α t)) (Set.Icc t₀ T) t) :=
  (isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ T hT a K Mc hlip hcont hcenter hLa).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Single-solution Picard–Lindelöf with closed-ball state membership.**  Mathlib's differential
Picard–Lindelöf theorem `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` produces the
local integral curve `α` but discards the a-priori bound that `α` stays inside the closed ball
`closedBall x₀ a`, on which the vector-field hypotheses hold — a bound its own proof establishes
(`ODE.FunSpace.compProj_mem_closedBall`).  This variant *retains* that state-membership readout on
the whole interval, which is exactly what upgrades a raw evolution curve to a state-constrained
`BanachEvolutionLocalSolutionIn` without shrinking the interval or assuming the state set is open. -/
theorem _root_.IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) :
    ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Set.Icc tmin tmax, α t ∈ Metric.closedBall x₀ (a : ℝ)) ∧
      ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Set.Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj,
    by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t _ => α.compProj_mem_closedBall hf.mul_max_le, fun t ht => ?_⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn
    (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- **Closed-ball Picard–Lindelöf gives a state-constrained forward local solution.**  When the
Picard state ball `closedBall u₀ a` is contained in the prescribed state set `stateSet`, the forward
Picard–Lindelöf solution — which provably stays in that ball on the *whole* interval `[t₀, T]` — is a
genuine `BanachEvolutionLocalSolutionIn` on the full window, with **no** interval shrinking and **no**
openness hypothesis on `stateSet` (contrast `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_mem_isOpen`,
which shrinks the terminal time to keep the curve inside an open set).  This is the a-posteriori
ball-membership route that the honest ball-local section-space Picard data feeds directly into a
`realization` decode. -/
theorem _root_.IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hsub : Metric.closedBall u₀ (a : ℝ) ⊆ stateSet) :
    Nonempty (BanachEvolutionLocalSolutionIn F stateSet t₀ u₀) := by
  obtain ⟨α, hα0, hmem, hderiv⟩ :=
    hF.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall (x := u₀) (by simp)
  exact ⟨{
    terminalTime := T
    initial_lt_terminal := hT
    curve := α
    initial_eq := hα0
    equation := by intro t ht; exact hderiv t ht
    mem_state := by intro t ht; exact hsub (hmem t ht) }⟩

/-- **Section-space state-constrained local solution from centre-bound ball-local data.**  The
capstone of the honest route (ii): from the same centre-bound coordinatewise analytic control that
supplies the chart's `picard` field (`K`-Lipschitz-in-section on `closedBall x0 a`, time-continuity
there, centre readout bound `‖(A t x0)ᵢ x‖ ≤ Mc`, and the time-radius compatibility
`(Mc + K·a)·(T − t₀) ≤ a`), together with the a-priori containment `closedBall x0 a ⊆ locus` of the
Picard ball in the prescribed state locus (e.g. the positive-definite / Riemannian metric cone), the
time-dependent operator `A` on the complete section space admits a genuine
`BanachEvolutionLocalSolutionIn A locus t₀ x0` on the full window `[t₀, T]`.  Combines the centre-bound
section-space Picard constructor `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`
with the closed-ball a-posteriori bridge
`IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`.  This is precisely the
state-constrained Banach solution a downstream `realization` decode into a genuine intrinsic De Turck
local solution consumes, now available from the honest (not globally bounded) analytic input. -/
theorem sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound
    {M : Type*} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
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
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover))
    (t₀ T : ℝ) (hT : t₀ < T) (a K Mc : ℝ≥0)
    (hlip : ∀ t ∈ Set.Icc t₀ T, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T))
    (hcenter : ∀ t ∈ Set.Icc t₀ T, ∀ (i : κ) (x : Kc i),
        ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t x0)).1 i x‖ ≤ (Mc : ℝ))
    (hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T - t₀) ≤ (a : ℝ))
    (hsub : Metric.closedBall x0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn A locus t₀ x0) :=
  IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT
    (isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
      A x0 t₀ T hT a K Mc hlip hcont hcenter hLa) hsub

/-- **Section-space Picard endpoint chooser from Lipschitz + time-continuity alone (no hand-supplied
centre bound).**  A convenience strengthening of
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`: the centre
readout size `Mc` need not be supplied by hand.  On a reference window `Icc t₀ T₀`, from
coordinatewise `K`-Lipschitz-in-section control on `closedBall x0 a` and mere *time-continuity* of the
compact coordinate readouts there, the uniform centre bound is *derived*
(`exists_forall_mem_Icc_coord_norm_le_of_continuousOn`, using compactness of `Icc t₀ T₀` and of the
base pieces), and a forward Picard endpoint `T ∈ (t₀, T₀]` is chosen (`exists_forwardTime_mul_sub_le`
intersected with the window `min T' T₀`) for which `A` is `IsPicardLindelof` with radius `a`,
Lipschitz `K`, and the internally produced bound `Mc + K·a`.  This is the honest section-space
`picard`-field shape whose only analytic inputs are the operator's ball-local Lipschitz constant and
the continuity of its coordinate readout — no separately quantified size constant, the centre bound
`Mc` coming for free from continuity of the readout at the initial metric on a compact window. -/
theorem exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn
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
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a K : ℝ≥0) (ha : 0 < (a : ℝ))
    (hlip : ∀ t ∈ Set.Icc t₀ T₀, ∀ ⦃s⦄, s ∈ Metric.closedBall x0 (a : ℝ) →
        ∀ ⦃s'⦄, s' ∈ Metric.closedBall x0 (a : ℝ) → ∀ (i : κ) (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s')).1 i x)
          ≤ (K : ℝ) * dist s s')
    (hcont : ∀ s ∈ Metric.closedBall x0 (a : ℝ), ∀ (i : κ),
        ContinuousOn
          (fun t => (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t s)).1 i)
          (Set.Icc t₀ T₀)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof A (tmin := t₀) (tmax := T)
        ⟨t₀, ⟨le_rfl, hT.le⟩⟩ x0 a 0 (Mc + K * a) K := by
  obtain ⟨C, hC0, hCbound⟩ :=
    exists_forall_mem_Icc_coord_norm_le_of_continuousOn
      (f := fun t => A t x0) (t₀ := t₀) (T := T₀)
      (hcont x0 (Metric.mem_closedBall_self ha.le))
  set Mc : ℝ≥0 := C.toNNReal with hMc
  have hCMc : C ≤ (Mc : ℝ) := by
    rw [hMc]; exact (Real.coe_toNNReal C hC0).ge
  obtain ⟨T', hT', hLa'⟩ :=
    RicciFlow.AnalyticPDE.exists_forwardTime_mul_sub_le t₀ a K Mc ha
  have hTle : min T' T₀ ≤ T₀ := min_le_right T' T₀
  have hstep : (min T' T₀ - t₀) ≤ (T' - t₀) := by
    have := min_le_left T' T₀; linarith
  refine ⟨min T' T₀, lt_min hT' hT₀, Mc, ?_⟩
  have hLa : ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀) ≤ (a : ℝ) := by
    calc ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (min T' T₀ - t₀)
        ≤ ((Mc : ℝ) + (K : ℝ) * (a : ℝ)) * (T' - t₀) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (a : ℝ) := hLa'
  refine isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound
    A x0 t₀ (min T' T₀) (lt_min hT' hT₀) a K Mc ?_ ?_ ?_ hLa
  · intro t ht
    exact hlip t ⟨ht.1, le_trans ht.2 hTle⟩
  · intro s hs i
    exact (hcont s hs i).mono (Set.Icc_subset_Icc le_rfl hTle)
  · intro t ht i x
    exact le_trans (hCbound t ⟨ht.1, le_trans ht.2 hTle⟩ i x) hCMc

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
