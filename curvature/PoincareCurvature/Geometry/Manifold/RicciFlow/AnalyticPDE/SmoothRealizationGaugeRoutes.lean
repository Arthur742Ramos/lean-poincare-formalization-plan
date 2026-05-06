module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative

set_option linter.unusedSectionVars false
set_option linter.all false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

/-!
# Raw-gauge routes from smooth Ricci-DeTurck realizations

This thin module keeps the heavy smooth-realization construction unchanged and
adds endpoint projections that explicitly pass through the raw identity `C^3`
gauge-flow and named scalar time-derivative interfaces.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance gaugeRoutesBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance gaugeRoutesBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))

private theorem continuousMap_moving_eval_sub_const_hasDerivWithinAt
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝[s] t) (𝓝 (x t))) :
    HasDerivWithinAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) s t := by
  have hrem :
      (fun τ : ℝ ↦ (u τ - u t - (τ - t) • u') (x τ)) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    filter_upwards [Asymptotics.IsLittleO.bound hu.isLittleO hc] with τ hτ
    exact (ContinuousMap.norm_coe_le_norm (u τ - u t - (τ - t) • u') (x τ)).trans hτ
  have hderiv_eval_tendsto :
      Filter.Tendsto (fun τ : ℝ ↦ u' (x τ) - u' (x t)) (𝓝[s] t) (𝓝 0) := by
    have hu'_tendsto :
        Filter.Tendsto (fun y : K ↦ u' y) (𝓝 (x t)) (𝓝 (u' (x t))) :=
      map_continuousAt u' (x t)
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ u' (x t)) (𝓝[s] t) (𝓝 (u' (x t))) :=
      tendsto_const_nhds
    simpa using (hu'_tendsto.comp hx).sub hconst
  have hderiv_eval :
      (fun τ : ℝ ↦ u' (x τ) - u' (x t)) =o[𝓝[s] t]
        fun _ : ℝ ↦ (1 : ℝ) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hderiv_eval_tendsto
  have htime :
      (fun τ : ℝ ↦ τ - t) =O[𝓝[s] t] fun τ : ℝ ↦ τ - t :=
    Asymptotics.isBigO_refl _ _
  have hmove :
      (fun τ : ℝ ↦ (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t := by
    simpa using htime.smul_isLittleO hderiv_eval
  have htotal :
      (fun τ : ℝ ↦
        (u τ - u t - (τ - t) • u') (x τ) +
          (τ - t) • (u' (x τ) - u' (x t))) =o[𝓝[s] t]
        fun τ : ℝ ↦ τ - t :=
    hrem.add hmove
  refine HasDerivWithinAt.of_isLittleO ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_sub] using htotal

private theorem continuousMap_moving_eval_sub_const_hasDerivAt
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → C(K, E)} {u' : C(K, E)} {t : ℝ}
    (hu : HasDerivAt u u' t)
    {x : ℝ → K} (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt (fun τ : ℝ ↦ u τ (x τ) - u t (x τ)) (u' (x t)) t := by
  rw [← hasDerivWithinAt_univ] at hu ⊢
  exact continuousMap_moving_eval_sub_const_hasDerivWithinAt hu (by simpa using hx)

section MovingCoordinateHelpers

variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := W))

private theorem coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo_forGaugeRoutes
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using continuousMap_moving_eval_sub_const_hasDerivAt hcomponent hx

private theorem coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico_forGaugeRoutes
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {g₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (sol : BanachEvolutionLocalSolutionIn A stateSet t₀ g₀)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico t₀ sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(Kc i, BilF) :=
    (ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover))
  have hcomponent :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ))
        (L (A t (sol.curve t))) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht
  simpa [L] using continuousMap_moving_eval_sub_const_hasDerivWithinAt hcomponent hx

end MovingCoordinateHelpers

private noncomputable def compactCurveOfEventuallyMem
    (K : Set M) (y : ℝ → M) (t : ℝ) (hy_t : y t ∈ K) : ℝ → K :=
  by
    classical
    exact fun τ ↦ if hτ : y τ ∈ K then ⟨y τ, hτ⟩ else ⟨y t, hy_t⟩

private theorem compactCurveOfEventuallyMem_eventually_val_eq
    {K : Set M} {y : ℝ → M} {t : ℝ} {hy_t : y t ∈ K}
    {l : Filter ℝ} (hmem : ∀ᶠ τ in l, y τ ∈ K) :
    (fun τ : ℝ ↦ (compactCurveOfEventuallyMem K y t hy_t τ).1) =ᶠ[l] y := by
  filter_upwards [hmem] with τ hτ
  simp [compactCurveOfEventuallyMem, hτ]

private theorem compactCurveOfEventuallyMem_tendsto
    {K : Set M} {y : ℝ → M} {t : ℝ} {hy_t : y t ∈ K}
    {l : Filter ℝ}
    (hy : Filter.Tendsto y l (𝓝 (y t)))
    (hmem : ∀ᶠ τ in l, y τ ∈ K) :
    Filter.Tendsto (compactCurveOfEventuallyMem K y t hy_t)
      l (𝓝 (compactCurveOfEventuallyMem K y t hy_t t)) := by
  rw [tendsto_subtype_rng]
  have htarget :
      (compactCurveOfEventuallyMem K y t hy_t t).1 = y t := by
    simp [compactCurveOfEventuallyMem, hy_t]
  rw [htarget]
  exact Filter.Tendsto.congr'
    (compactCurveOfEventuallyMem_eventually_val_eq (K := K) (y := y) (t := t)
      (hy_t := hy_t) hmem).symm hy

private theorem eventually_mem_of_tendsto_of_mem_interior
    {K : Set M} {y : ℝ → M} {t : ℝ} {l : Filter ℝ}
    (hy : Filter.Tendsto y l (𝓝 (y t)))
    (hmem : y t ∈ interior K) :
    ∀ᶠ τ in l, y τ ∈ K := by
  filter_upwards [hy (isOpen_interior.mem_nhds hmem)] with τ hτ
  exact interior_subset hτ

/-- A point in the interior of a compact-cover piece and in an open target
patch admits a smaller compact neighborhood contained in both.  This is the
topological selection step needed by the target-centered gauge readout. -/
private theorem exists_compact_subset_interior_inter_open
    [LocallyCompactSpace M] {p : M} {K₀ U : Set M}
    (hpK : p ∈ interior K₀) (hUopen : IsOpen U) (hpU : p ∈ U) :
    ∃ K : TopologicalSpace.Compacts M,
      p ∈ interior (K : Set M) ∧ (K : Set M) ⊆ K₀ ∧ (K : Set M) ⊆ U := by
  rcases exists_compact_subset (hU := isOpen_interior.inter hUopen)
      (hx := ⟨hpK, hpU⟩) with ⟨K, hKcompact, hpKint, hKsub⟩
  refine ⟨⟨K, hKcompact⟩, hpKint, ?_, ?_⟩
  · intro y hy
    exact interior_subset (hKsub hy).1
  · intro y hy
    exact (hKsub hy).2

/-- If the interiors of a compact family cover and the target patch is open,
one can choose both the compact-family index and a smaller compact neighborhood
inside the selected family member and the target patch. -/
theorem exists_compact_subset_interior_cover_inter_open
    [LocallyCompactSpace M] {ι : Type*} {Kc : ι → TopologicalSpace.Compacts M}
    {p : M} {U : Set M}
    (hcover_int : (⋃ i, interior (Kc i : Set M)) = Set.univ)
    (hUopen : IsOpen U) (hpU : p ∈ U) :
    ∃ (i : ι) (K : TopologicalSpace.Compacts M),
      p ∈ interior (K : Set M) ∧
        (K : Set M) ⊆ (Kc i : Set M) ∧ (K : Set M) ⊆ U := by
  have hpcover : p ∈ ⋃ i, interior (Kc i : Set M) := by
    rw [hcover_int]
    exact Set.mem_univ p
  rcases Set.mem_iUnion.mp hpcover with ⟨i, hpKc⟩
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      hpKc hUopen hpU with
    ⟨K, hpK, hKsubKc, hKsubU⟩
  exact ⟨i, K, hpK, hKsubKc, hKsubU⟩

/-- An interior-covering compact family is, in particular, an ordinary compact
cover.  This keeps stronger cover data compatible with the existing
finite-cover section-space APIs. -/
theorem iUnion_compacts_eq_univ_of_iUnion_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {ι : Type*} {Kc : ι → TopologicalSpace.Compacts X}
    (hcover_int : (⋃ i, interior (Kc i : Set X)) = Set.univ) :
    (⋃ i, (Kc i : Set X)) = Set.univ := by
  refine eq_univ_of_univ_subset ?_
  intro x _hx
  have hx : x ∈ ⋃ i, interior (Kc i : Set X) := by
    rw [hcover_int]
    exact Set.mem_univ x
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact Set.mem_iUnion.mpr ⟨i, interior_subset hxi⟩

/-- A finite cover of the whole space by compact sets makes the whole space
compact.  Existing finite-cover chart hypotheses therefore carry compactness
as data, even when no `CompactSpace` instance has been installed. -/
theorem isCompact_univ_of_finite_compact_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (Kc : ι → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kc i : Set X)) = Set.univ) :
    IsCompact (Set.univ : Set X) := by
  simpa [hcover] using
    (isCompact_iUnion (f := fun i ↦ (Kc i : Set X)) fun i ↦ (Kc i).isCompact)

/-- Instance-valued version of
`isCompact_univ_of_finite_compact_cover`. -/
theorem compactSpace_of_finite_compact_cover
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    (Kc : ι → TopologicalSpace.Compacts X)
    (hcover : (⋃ i, (Kc i : Set X)) = Set.univ) :
    CompactSpace X :=
  isCompact_univ_iff.1 (isCompact_univ_of_finite_compact_cover Kc hcover)

/-- A finite open cover of a compact set admits compact cores subordinate to
the open patches whose interiors still cover the original compact set.  This
is the cover-level topological input needed to replace plain compact cover
membership by interior compact-cover membership. -/
theorem exists_compacts_interior_cover_of_finite_open_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {ι : Type*} [Finite ι] {s : Set X} {U : ι → Set X}
    (hs : IsCompact s) (hUopen : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ K : ι → TopologicalSpace.Compacts X,
      s ⊆ ⋃ i, interior (K i : Set X) ∧ ∀ i, (K i : Set X) ⊆ U i := by
  have hfinite : ∀ x ∈ s, {i | x ∈ U i}.Finite := by
    intro _x _hx
    exact Set.finite_univ.subset (by intro i _hi; exact Set.mem_univ i)
  rcases exists_subset_iUnion_closure_subset_t2space
      (s := s) (u := U) hs hUopen hfinite hcover with
    ⟨V, hVcover, hVopen, hVclosure, hVcompact⟩
  let K : ι → TopologicalSpace.Compacts X := fun i ↦ ⟨closure (V i), hVcompact i⟩
  refine ⟨K, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp (hVcover hx) with ⟨i, hxi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change x ∈ interior (closure (V i))
    exact mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset ((hVopen i).mem_nhds hxi) subset_closure)
  · intro i
    change closure (V i) ⊆ U i
    exact hVclosure i

/-- Whole-space version of
`exists_compacts_interior_cover_of_finite_open_cover` for compact spaces. -/
theorem exists_compacts_interior_univ_cover_of_finite_open_cover
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [CompactSpace X]
    {ι : Type*} [Finite ι] {U : ι → Set X}
    (hUopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) :
    ∃ K : ι → TopologicalSpace.Compacts X,
      (⋃ i, interior (K i : Set X)) = Set.univ ∧ ∀ i, (K i : Set X) ⊆ U i := by
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i, U i := by
    simpa [hcover]
  rcases exists_compacts_interior_cover_of_finite_open_cover
      (s := (Set.univ : Set X)) (U := U) isCompact_univ hUopen hcover' with
    ⟨K, hKcover, hKsub⟩
  exact ⟨K, eq_univ_of_univ_subset hKcover, hKsub⟩

private noncomputable def compactCurveOfEventuallyMemOnSet
    (K : Set M) (y : ℝ → M) (s : Set ℝ) (t : ℝ) (hy_t : y t ∈ K) : ℝ → K :=
  by
    classical
    exact fun τ ↦
      if hsτ : τ ∈ s then
        if hτ : y τ ∈ K then ⟨y τ, hτ⟩ else ⟨y t, hy_t⟩
      else
        ⟨y t, hy_t⟩

private theorem compactCurveOfEventuallyMemOnSet_eventually_val_eq
    {K : Set M} {y : ℝ → M} {s : Set ℝ} {t : ℝ} {hy_t : y t ∈ K}
    (hmem : ∀ᶠ τ in 𝓝[s] t, y τ ∈ K) :
    (fun τ : ℝ ↦ (compactCurveOfEventuallyMemOnSet K y s t hy_t τ).1)
      =ᶠ[𝓝[s] t] y := by
  filter_upwards [self_mem_nhdsWithin, hmem] with τ hsτ hτ
  simp [compactCurveOfEventuallyMemOnSet, hsτ, hτ]

private theorem compactCurveOfEventuallyMemOnSet_tendsto_Ici
    {K : Set M} {y : ℝ → M} {s : Set ℝ} {t : ℝ} {hy_t : y t ∈ K}
    (hts : t ∈ s)
    (hy : Filter.Tendsto y (𝓝[s] t) (𝓝 (y t)))
    (hmem : ∀ᶠ τ in 𝓝[s] t, y τ ∈ K) :
    Filter.Tendsto (compactCurveOfEventuallyMemOnSet K y s t hy_t)
      (𝓝[Ici t] t) (𝓝 (compactCurveOfEventuallyMemOnSet K y s t hy_t t)) := by
  rw [tendsto_subtype_rng]
  have htarget :
      (compactCurveOfEventuallyMemOnSet K y s t hy_t t).1 = y t := by
    simp [compactCurveOfEventuallyMemOnSet, hts, hy_t]
  rw [htarget]
  intro U hU
  have hytU : y t ∈ U := mem_of_mem_nhds hU
  have hpre : {τ : ℝ | y τ ∈ U} ∈ 𝓝[s] t := hy hU
  have hpre' : ∀ᶠ τ in 𝓝 t, τ ∈ s → y τ ∈ U :=
    mem_nhdsWithin_iff_eventually.mp hpre
  have hmem' : ∀ᶠ τ in 𝓝 t, τ ∈ s → y τ ∈ K :=
    mem_nhdsWithin_iff_eventually.mp hmem
  change
    {τ : ℝ | (compactCurveOfEventuallyMemOnSet K y s t hy_t τ).1 ∈ U} ∈
      𝓝[Ici t] t
  rw [mem_nhdsWithin_iff_eventually]
  filter_upwards [hpre', hmem'] with τ hpreτ hmemτ hτIci
  by_cases hsτ : τ ∈ s
  · have hτU : y τ ∈ U := hpreτ hsτ
    have hτK : y τ ∈ K := hmemτ hsτ
    simp [compactCurveOfEventuallyMemOnSet, hsτ, hτK, hτU]
  · simp [compactCurveOfEventuallyMemOnSet, hsτ, hytU]

section GlobalClosure

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]

/-- On the Picard interval and the genuine Riemannian-metric locus, the density-based
interval-scoped restricted symmetric carrier is the same as the interval chart's built-in
restricted symmetric carrier. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime T)
    (x : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hx : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x =
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x := by
  apply Subtype.ext
  calc
    ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
        chart.A t (x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
      exact chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover t x hx
    _ =
        ((SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
          (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
      exact (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ) t ht x hx).symm

/-- Ambient-coordinate readout of
`TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem`. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_coe_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime T)
    (x : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hx : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
      ((SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ)) t x :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) := by
  exact congrArg Subtype.val
    (chart.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
      (M := M) (F := F) (I := I) rhs hclosure ht x hx)

/-- Transport a state-preserving Banach solution of the interval-scoped density-based carrier to the
chart's built-in restricted symmetric carrier. The terminal-time hypothesis is exactly what restricts
the vector-field equality to the Picard interval, avoiding any false global identification outside
`Icc ivp.initialTime T`. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.toRestrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closure_smooth_spd_on_Icc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (sol : BanachEvolutionLocalSolutionIn
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (fun τ hτ => chart.lipschitzOn_Icc τ hτ))
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp))
    (hsolT : sol.terminalTime ≤ T) :
    BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  curve := sol.curve
  initial_eq := sol.initial_eq
  equation := by
    intro t ht
    have htT : t ∈ Icc ivp.initialTime T := ⟨ht.1, le_trans ht.2 hsolT⟩
    have hEq :=
      chart.restrictedSymmetricA_eq_restrictedSymmetricA_of_closure_smooth_spd_on_Icc_of_mem
        (M := M) (F := F) (I := I) rhs hclosure htT (sol.curve t) (sol.mem_state ht)
    simpa [hEq] using sol.toBanachEvolutionLocalSolution.equation ht
  mem_state := sol.mem_state

/-- The Banach chart right-hand side differentiates the named
`metricBilinearCoordinateField` at the chart center for a smooth intrinsic
DeTurck realization.

This is the centered model-slot form of the finite-cover readout derivative
needed before a raw `C³` gauge-flow argument moves the base point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
      (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
        (M := M) (F := F) (I := I) x0 het ht)
      p uE vE

/-- Tangent-vector-slot version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

This exposes the same Banach chart right-hand side in the scalar shape used by
geometric gauge-pullback calculations. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_chartRHS_of_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) t := by
  exact
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M)
       (realization.hasTimeDerivativeAt_chartRHS_of_mem_Ioo
         (M := M) (F := F) (I := I) x0 het ht)
       p u v

/-- One-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`.

At every time in the closed-left/open-right Banach interval, the centered
metric-coordinate field has the Banach chart right-hand side as its right
derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (uE vE : F) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE)
      (A t (sol.curve t) p
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
        (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE))
      (Ici t) t := by
  have hmetric :=
    realization.metric_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
      (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p) uE vE) =ᶠ[𝓝[Ici t] t]
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M) realization.metric τ p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE)) := by
    filter_upwards with τ
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  have hEq_t :
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) p) uE vE =
        metricTensor (I := I) (M := M) realization.metric t p
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p uE)
          (SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate (I := I) p vE) := by
    rw [SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField_base_apply_eq_tangentVector]
    rfl
  exact hmetric.congr_of_eventuallyEq hEq hEq_t

/-- Tangent-vector-slot one-sided endpoint version of
`metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (p : M) (u v : TangentSpace I p) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) p)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
          (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v))
      (A t (sol.curve t) p u v) (Ici t) t := by
  simpa using
    realization.metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico
      (M := M) (F := F) (I := I) x0 het ht p
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p u)
      (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) p v)

/-- A finite-cover bilinear coordinate readout of a smooth metric section is the
named raw metric-coordinate field centered at the same preferred
trivialization point. -/
theorem metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : MetricFamily (I := I) (M := M)) (τ : ℝ) (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover
      (⟨(g τ).toContinuousRiemannianMetric.toSection,
        (g τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover)).1 i x =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g (x0 i)
        (τ, (extChartAt I (x0 i)) x.1) := by
  ext uE vE
  let TM := (TangentSpace I : M → Type _)
  have hKpref :
      (Kc i : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) (x0 i)).baseSet := by
    simpa [TM, het i] using hKc i
  have hxbase : x.1 ∈ (trivializationAt F TM (x0 i)).baseSet := by
    simpa [TM] using hKpref x.2
  have hsrc_ext : x.1 ∈ (extChartAt I (x0 i)).source := by
    simpa [TM, extChartAt_source] using hxbase
  have hy :
      (extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1) = x.1 := by
    exact PartialEquiv.left_inv _ hsrc_ext
  change
    (et i ⟨x.1, (g τ).inner x.1⟩).2 uE vE =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g (x0 i)
        (τ, (extChartAt I (x0 i)) x.1) uE vE
  rw [het i]
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i) x.1 (x0 i) x.1 ((g τ).inner x.1) uE) vE =
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) g (x0 i)
      (τ, (extChartAt I (x0 i)) x.1) uE vE
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i) x.1 (x0 i) x.1 ((g τ).inner x.1) uE) vE =
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      (x0 i)
      ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))
      (x0 i)
      ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))
      ((g τ).inner ((extChartAt I (x0 i)).symm ((extChartAt I (x0 i)) x.1))) uE) vE
  rw [hy]

/-- Read a finite-cover section on a smaller compact set, then change the
bilinear-form coordinates to the preferred trivialization centered at `p`.

This is the finite-cover readout used when the raw gauge calculation is
centered at an arbitrary moving point rather than at the fixed cover center
`x0 i`. -/
noncomputable def targetBilinearCoordReadoutContinuousLinearMap
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
  (coordChangeContinuousLinearMap
    (𝕜 := ℝ) (F := BilF)
    (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
    (e := et i)
    (e' := trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
    K
    (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)).comp
    ((restrictToCompactContinuousLinearMap
      (𝕜 := ℝ) (F := BilF) (hKL := hK_sub_Kc)).comp
      ((ContinuousLinearMap.proj i).comp
        (((compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL).comp
          (toCompatibleCoordFamilySubmoduleContinuousLinearMap
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))))

/-- The target-centered compact readout is the ordinary coordinate readout of
the reconstructed section in the target trivialization. -/
private theorem targetBilinearCoordReadoutContinuousLinearMap_apply_eq_coordContinuousMap
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)
    (x : K) :
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target s x =
      coordContinuousMap
        (e := trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
        (s := fun y : M ↦ s y)
        K hK_sub_target s.continuous_toFun.continuousOn x := by
  let TM := (TangentSpace I : M → Type _)
  let eTarget :=
    trivializationAt BilF (_root_.Bundle.BilinearFormBundle (V := TM)) p
  have hsource :
      restrictToCompact hK_sub_Kc
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := TM))
            et Kc hKc Ko hKo hKoEq hcover s).1 i) =
        coordContinuousMap
          (e := et i) (s := fun y : M ↦ s y)
          K (fun _ hx ↦ hKc i (hK_sub_Kc hx))
          s.continuous_toFun.continuousOn := by
    ext y
    simp [equivCompatibleCoordFamilySubmodule, toSubtype,
      continuousSectionEquivCompatibleCoordFamilySubmodule,
      continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
      compatibleCoordFamilyOfSection, coordFamilyOfSection, TM]
  calc
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target s x
        =
      coordChangeContinuousMap
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := TM))
        (e := et i) (e' := eTarget) K
        (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
        (restrictToCompact hK_sub_Kc
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := TM))
            et Kc hKc Ko hKo hKoEq hcover s).1 i)) x := by
          rfl
    _ =
      coordChangeContinuousMap
        (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := TM))
        (e := et i) (e' := eTarget) K
        (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
        (coordContinuousMap
          (e := et i) (s := fun y : M ↦ s y)
          K (fun _ hx ↦ hKc i (hK_sub_Kc hx))
          s.continuous_toFun.continuousOn) x := by
          rw [hsource]
    _ =
      coordContinuousMap
        (e := eTarget) (s := fun y : M ↦ s y)
        K hK_sub_target s.continuous_toFun.continuousOn x := by
          exact congrArg (fun f : C(K, BilF) ↦ f x)
            (coordContinuousMap_coordChangeL
              (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := TM))
              (e := et i) (e' := eTarget) (s := fun y : M ↦ s y)
              K (fun _ hx ↦ ⟨hKc i (hK_sub_Kc hx), hK_sub_target hx⟩)
              s.continuous_toFun.continuousOn s.continuous_toFun.continuousOn)

/-- A target-centered compact readout of a smooth metric section is the named
raw metric-coordinate field centered at that target point. -/
theorem metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : MetricFamily (I := I) (M := M)) (τ : ℝ)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    (x : K) :
    targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target
        (⟨(g τ).toContinuousRiemannianMetric.toSection,
          (g τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x =
      SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
        (I := I) (M := M) g p (τ, (extChartAt I p) x.1) := by
  rw [targetBilinearCoordReadoutContinuousLinearMap_apply_eq_coordContinuousMap
    (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    p i K hK_sub_Kc hK_sub_target]
  ext uE vE
  let TM := (TangentSpace I : M → Type _)
  have hxbase :
      x.1 ∈ (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := TM)) p).baseSet :=
    hK_sub_target x.2
  have hsrc_ext : x.1 ∈ (extChartAt I p).source := by
    simpa [TM, extChartAt_source] using hxbase
  have hy : (extChartAt I p).symm ((extChartAt I p) x.1) = x.1 := by
    exact PartialEquiv.left_inv _ hsrc_ext
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p x.1 p x.1 ((g τ).inner x.1) uE) vE =
    SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) g p (τ, (extChartAt I p) x.1) uE vE
  change
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p x.1 p x.1 ((g τ).inner x.1) uE) vE =
    (ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      p
      ((extChartAt I p).symm ((extChartAt I p) x.1))
      p
      ((extChartAt I p).symm ((extChartAt I p) x.1))
      ((g τ).inner ((extChartAt I p).symm ((extChartAt I p) x.1))) uE) vE
  rw [hy]

/-- Interior moving-point time-difference derivative for the raw
metric-coordinate field, obtained from the Banach section norm through the
preferred finite-cover coordinate chart. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) t := by
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) t :=
    coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo_forGaugeRoutes
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ioo_subset_Icc_self ht)]
  have hmetric_coord := hproj.congr_of_eventuallyEq hmetric_curve
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) := by
    filter_upwards with τ
    rw [← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric τ i (x τ),
      ← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric t i (x τ)]
  exact hmetric_coord.congr_of_eventuallyEq hEq

/-- One-sided endpoint version of
`metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (i : κ) {x : ℝ → Kc i}
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1))
      ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (x t)) (Ici t) t := by
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve τ)).1 i (x τ) -
          (equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (sol.curve t)).1 i (x τ))
        ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover
            (A t (sol.curve t))).1 i (x t)) (Ici t) t :=
    coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico_forGaugeRoutes
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) sol i ht hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve τ)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (sol.curve t)).1 i (x τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  have hmetric_coord :=
    hproj.congr_of_eventuallyEq_of_mem hmetric_curve (Set.mem_Ici.mpr le_rfl)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (τ, (extChartAt I (x0 i)) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric (x0 i)
          (t, (extChartAt I (x0 i)) (x τ).1)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
            (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ) -
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
            (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)).1 i (x τ)) := by
    filter_upwards with τ
    rw [← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric τ i (x τ),
      ← metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) het realization.metric t i (x τ)]
  exact hmetric_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- Interior moving-point time-difference derivative for the raw
metric-coordinate field centered at an arbitrary target point.  The Banach
section derivative is read from one finite-cover component after restriction
to a smaller compact set and coordinate change to the target trivialization. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    {x : ℝ → K}
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝 t) (𝓝 (x t))) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1))
      (targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target (A t (sol.curve t)) (x t)) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
    targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      p i K hK_sub_Kc hK_sub_target
  have hcomponent :
      HasDerivAt (fun τ : ℝ ↦ L (sol.curve τ)) (L (A t (sol.curve t))) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivAt_of_mem_Ioo
      (F := A) (stateSet := stateSet) L sol ht
  have hproj :
      HasDerivAt
        (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ))
        (L (A t (sol.curve t)) (x t)) t :=
    continuousMap_moving_eval_sub_const_hasDerivAt hcomponent hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ioo_subset_Icc_self ht)]
  have hmetric_coord := hproj.congr_of_eventuallyEq hmetric_curve
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1)) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) := by
    filter_upwards with τ
    rw [← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric τ p i K
        hK_sub_Kc hK_sub_target (x τ),
      ← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric t p i K
        hK_sub_Kc hK_sub_target (x τ)]
  simpa [L] using hmetric_coord.congr_of_eventuallyEq hEq

/-- One-sided endpoint version of
`metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_target_coord_mem_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    (p : M) (i : κ) (K : TopologicalSpace.Compacts M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet)
    {x : ℝ → K}
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (hx : Filter.Tendsto x (𝓝[Ici t] t) (𝓝 (x t))) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1))
      (targetBilinearCoordReadoutContinuousLinearMap
        (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
        (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
        p i K hK_sub_Kc hK_sub_target (A t (sol.curve t)) (x t)) (Ici t) t := by
  let L :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover →L[ℝ] C(K, BilF) :=
    targetBilinearCoordReadoutContinuousLinearMap
      (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      p i K hK_sub_Kc hK_sub_target
  have hcomponent :
      HasDerivWithinAt (fun τ : ℝ ↦ L (sol.curve τ))
        (L (A t (sol.curve t))) (Ici t) t :=
    BanachEvolutionLocalSolutionIn.continuousLinearMap_hasDerivWithinAt_Ici_of_mem_Ico
      (F := A) (stateSet := stateSet) L sol ht
  have hproj :
      HasDerivWithinAt
        (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ))
        (L (A t (sol.curve t)) (x t)) (Ici t) t :=
    continuousMap_moving_eval_sub_const_hasDerivWithinAt hcomponent hx
  have hmetric_curve :
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦ L (sol.curve τ) (x τ) - L (sol.curve t) (x τ)) := by
    filter_upwards [Icc_mem_nhdsGE_of_mem ht] with τ hτ
    rw [realization.metric_toContinuousSection_eq_curve hτ,
      realization.metric_toContinuousSection_eq_curve (Ico_subset_Icc_self ht)]
  have hmetric_coord :=
    hproj.congr_of_eventuallyEq_of_mem hmetric_curve (Set.mem_Ici.mpr le_rfl)
  have hEq :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (τ, (extChartAt I p) (x τ).1) -
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric p
          (t, (extChartAt I p) (x τ).1)) =ᶠ[𝓝[Ici t] t]
      (fun τ : ℝ ↦
        L (⟨(realization.metric τ).toContinuousRiemannianMetric.toSection,
          (realization.metric τ).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ) -
        L (⟨(realization.metric t).toContinuousRiemannianMetric.toSection,
          (realization.metric t).toContinuousRiemannianMetric.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (x τ)) := by
    filter_upwards with τ
    rw [← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric τ p i K
        hK_sub_Kc hK_sub_target (x τ),
      ← metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField
        (I := I) (M := M) (F := F) (et := et) realization.metric t p i K
        hK_sub_Kc hK_sub_target (x τ)]
  simpa [L] using
    hmetric_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)

/-- Full raw gauge-flow metric-coordinate derivative obtained from the Banach
moving time-difference bridge, once the gauge path has been represented in a
preferred compact coordinate chart centered at the time-`t` image. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_coord_mem_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo
      (M := M) (F := F) (I := I) het i ht hxK
  have htime :
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord.congr_of_eventuallyEq hEq
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G hs realization.metric x htime

/-- Full raw gauge-flow metric-coordinate derivative from the target-centered
Banach readout.  This removes the fixed-cover center equality by reading the
Banach right-hand side through a compact set contained in both a finite-cover
piece and the target trivialization at the time-`t` gauge image. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_target_coord_mem_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    {xK : ℝ → K}
    (hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo
      (M := M) (F := F) (I := I)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target ht hxK
  have htime :
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        (targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hτ]
    exact htime_coord.congr_of_eventuallyEq hEq
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G hs realization.metric x htime

/-- Open-interval target-centered raw gauge derivative from eventual membership
in the selected compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_target_K_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_t : (G.maps3 t) x ∈ (K : Set M))
    (hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (K : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (⟨(G.maps3 t) x, hmem_t⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → K :=
    compactCurveOfEventuallyMem (K : Set M) y t hmem_t
  have hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMem_tendsto
      (K := (K : Set M)) (y := y) (t := t) (hy_t := hmem_t)
      (G.continuousAt_eval hs x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMem_eventually_val_eq
      (K := (K : Set M)) (y := y) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_target_coord_mem_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target
      hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMem, hmem_t] using hmain

/-- Open-interval target-centered raw gauge derivative from interior
membership in the selected compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_int : (G.maps3 t) x ∈ interior (K : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t))
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have hmem_t : (G.maps3 t) x ∈ (K : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (K : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousAt_eval hs x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_target_K_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target
      hmem_t hmem

/-- Open-interval target-centered raw gauge derivative with the compact
overlap piece selected internally.  The only finite-cover hypothesis is that
the time-`t` gauge point lies in the interior of the chosen compact cover
piece; local compactness of the finite-dimensional manifold supplies a smaller
compact neighborhood contained both in that cover piece and in the target
trivialization at the gauge point. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ioo
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    ∃ (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      (by simpa [p] using hmem_int) hUopen hpU with
    ⟨K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo
      (M := M) (F := F) (I := I) G hs ht i K x hK_sub_Kc hK_sub_target hKmem_int'

/-- Open-interval raw gauge-flow metric-coordinate derivative from eventual
membership in one preferred compact cover piece.  This builds the selected
compact chart curve internally from the eventual membership witness. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_t : (G.maps3 t) x ∈ (Kc i : Set M))
    (hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (Kc i : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, hmem_t⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → Kc i :=
    compactCurveOfEventuallyMem (Kc i : Set M) y t hmem_t
  have hxK : Filter.Tendsto xK (𝓝 t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMem_tendsto
      (K := (Kc i : Set M)) (y := y) (t := t) (hy_t := hmem_t)
      (G.continuousAt_eval hs x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝 t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMem_eventually_val_eq
      (K := (Kc i : Set M)) (y := y) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_coord_mem_Ioo
      (M := M) (F := F) (I := I) het G hs ht i x hcenter hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMem, hmem_t] using hmain

/-- Open-interval raw gauge-flow metric-coordinate derivative from membership
of the time-`t` gauge point in the interior of one compact cover piece.  The
interior hypothesis is exactly what turns continuity of the gauge orbit into
the eventual compact-membership witness used by
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_Ioo
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (hs : s ∈ 𝓝 t)
    (ht : t ∈ Ioo ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    HasDerivAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) t := by
  have hmem_t : (G.maps3 t) x ∈ (Kc i : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (Kc i : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousAt_eval hs x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_Kc_Ioo
      (M := M) (F := F) (I := I) het G hs ht i x hcenter hmem_t hmem

/-- Right-sided raw gauge-flow metric-coordinate derivative from the Banach
moving time-difference bridge.  The raw time set is allowed to be any set lying
to the right of `t`, matching the one-sided Banach derivative. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[Ici t] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
      (M := M) (F := F) (I := I) het i ht hxK
  have htime_Ici :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) (Ici t) t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[Ici t] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)
  have htime_s := htime_Ici.mono hs_sub
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided raw gauge-flow metric-coordinate derivative when the selected
compact chart curve agrees with the gauge orbit only relative to the raw time
set.  This form is useful for closed interval gauges: the Banach
time-difference is still taken on `Ici t`, while the final raw derivative is
only within `s`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_timeSet_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    {xK : ℝ → Kc i}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_coord_mem_Ico
      (M := M) (F := F) (I := I) het i ht hxK
  have htime_coord_s := htime_coord.mono hs_sub
  have htime_s :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i (xK t)) s t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[s] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (τ, (extChartAt I (x0 i)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric (x0 i)
            (t, (extChartAt I (x0 i)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hcenter, ← hτ]
    exact htime_coord_s.congr_of_eventuallyEq_of_mem hEq htG
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided target-centered raw gauge-flow metric-coordinate derivative
when the selected compact curve agrees with the gauge orbit only relative to
the raw time set. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_target_coord_mem_timeSet_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    {xK : ℝ → K}
    (hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)))
    (hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have htime_coord :=
    realization.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_target_coord_mem_Ico
      (M := M) (F := F) (I := I)
      ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target ht hxK
  have htime_coord_s := htime_coord.mono hs_sub
  have htime_s :
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        (targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (xK t)) s t := by
    have hEq :
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) =ᶠ[𝓝[s] t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) (xK τ).1) -
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (t, (extChartAt I ((G.maps3 t) x)) (xK τ).1)) := by
      filter_upwards [hxK_eval] with τ hτ
      rw [← hτ]
    exact htime_coord_s.congr_of_eventuallyEq_of_mem hEq htG
  simpa using
    SmoothSelfDiffeomorph3Family.Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivWithinAt_of_timeDifference_along_eval_self
      (I := I) (M := M) G htG realization.metric x htime_s

/-- Right-sided target-centered raw gauge derivative from eventual membership
in the compact overlap piece, relative to the raw time set. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_target_K_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_t : (G.maps3 t) x ∈ (K : Set M))
    (hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (K : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t)) (⟨(G.maps3 t) x, hmem_t⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → K :=
    compactCurveOfEventuallyMemOnSet (K : Set M) y s t hmem_t
  have hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMemOnSet_tendsto_Ici
      (K := (K : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t)
      htG (G.continuousWithinAt_eval htG x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMemOnSet_eventually_val_eq
      (K := (K : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_target_coord_mem_timeSet_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMemOnSet, htG, hmem_t] using hmain

/-- Right-sided target-centered raw gauge derivative from interior membership
in the compact overlap piece. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (K : TopologicalSpace.Compacts M) (x : M)
    (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
    (hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet)
    (hmem_int : (G.maps3 t) x ∈ interior (K : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      ((targetBilinearCoordReadoutContinuousLinearMap
          (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
          ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
          (A t (sol.curve t))
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : K)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have hmem_t : (G.maps3 t) x ∈ (K : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (K : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousWithinAt_eval htG x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_target_K_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hmem_t hmem

/-- Right-sided target-centered raw gauge derivative with the compact overlap
piece selected internally.  This is the endpoint analogue of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ico
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    ∃ (K : TopologicalSpace.Compacts M)
      (hK_sub_Kc : (K : Set M) ⊆ (Kc i : Set M))
      (hK_sub_target : (K : Set M) ⊆
        (trivializationAt BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          ((G.maps3 t) x)).baseSet)
      (hKmem_int : (G.maps3 t) x ∈ interior (K : Set M)),
      HasDerivWithinAt
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
            (I := I) (M := M) realization.metric ((G.maps3 t) x)
            (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
        ((targetBilinearCoordReadoutContinuousLinearMap
            (I := I) (M := M) (F := F) (et := et) (Kc := Kc) (hKc := hKc)
            (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
            ((G.maps3 t) x) i K hK_sub_Kc hK_sub_target
            (A t (sol.curve t))
            (⟨(G.maps3 t) x, interior_subset hKmem_int⟩ : K)) +
          (fderivWithin ℝ
            (fun yE : F ↦
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
            (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
            (X t ((G.maps3 t) x))) s t := by
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (I := I)
  let p : M := (G.maps3 t) x
  let U : Set M :=
    (trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).baseSet
  have hpU : p ∈ U := by
    simpa [U] using
      (mem_baseSet_trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p)
  have hUopen : IsOpen U := by
    simpa [U] using
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) p).open_baseSet
  rcases exists_compact_subset_interior_inter_open
      (M := M) (p := p) (K₀ := (Kc i : Set M)) (U := U)
      (by simpa [p] using hmem_int) hUopen hpU with
    ⟨K, hKmem_int, hK_sub_Kc, hK_sub_U⟩
  have hK_sub_target : (K : Set M) ⊆
      (trivializationAt BilF
        (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        ((G.maps3 t) x)).baseSet := by
    simpa [p, U] using hK_sub_U
  have hKmem_int' : (G.maps3 t) x ∈ interior (K : Set M) := by
    simpa [p] using hKmem_int
  refine ⟨K, hK_sub_Kc, hK_sub_target, hKmem_int', ?_⟩
  simpa using
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico
      (M := M) (F := F) (I := I) G htG hs_sub ht i K x hK_sub_Kc hK_sub_target
      hKmem_int'

/-- Right-sided raw gauge-flow metric-coordinate derivative from eventual
membership in one compact cover piece, relative to the raw time set.  The
selected compact chart curve is built internally and is made constant off the
raw time set, so only within-`s` continuity of the gauge orbit is needed. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_Kc_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_t : (G.maps3 t) x ∈ (Kc i : Set M))
    (hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (Kc i : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, hmem_t⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  let y : ℝ → M := fun τ ↦ (G.maps3 τ) x
  let xK : ℝ → Kc i :=
    compactCurveOfEventuallyMemOnSet (Kc i : Set M) y s t hmem_t
  have hxK : Filter.Tendsto xK (𝓝[Ici t] t) (𝓝 (xK t)) := by
    exact compactCurveOfEventuallyMemOnSet_tendsto_Ici
      (K := (Kc i : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t)
      htG (G.continuousWithinAt_eval htG x) hmem
  have hxK_eval : (fun τ : ℝ ↦ (xK τ).1) =ᶠ[𝓝[s] t]
      fun τ : ℝ ↦ (G.maps3 τ) x := by
    exact compactCurveOfEventuallyMemOnSet_eventually_val_eq
      (K := (Kc i : Set M)) (y := y) (s := s) (t := t) (hy_t := hmem_t) hmem
  have hmain :=
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_coord_mem_timeSet_Ico
      (M := M) (F := F) (I := I) het G htG hs_sub ht i x hcenter hxK hxK_eval
  simpa [xK, y, compactCurveOfEventuallyMemOnSet, htG, hmem_t] using hmain

/-- Right-sided raw gauge-flow metric-coordinate derivative from membership of
the time-`t` gauge point in the interior of one compact cover piece, relative to
the raw time set.  This is the endpoint analogue of
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_Ioo`. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_Kc_Ico
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol)
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {gaugeInitialTime t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s gaugeInitialTime)
    (htG : t ∈ s)
    (hs_sub : s ⊆ Ici t)
    (ht : t ∈ Ico ivp.initialTime sol.terminalTime)
    (i : κ) (x : M)
    (hcenter : x0 i = (G.maps3 t) x)
    (hmem_int : (G.maps3 t) x ∈ interior (Kc i : Set M)) :
    HasDerivWithinAt
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) realization.metric ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)))
      (((equivCompatibleCoordFamilySubmodule
          (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover
          (A t (sol.curve t))).1 i
          (⟨(G.maps3 t) x, interior_subset hmem_int⟩ : Kc i)) +
        (fderivWithin ℝ
          (fun yE : F ↦
            SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) realization.metric ((G.maps3 t) x) (t, yE))
          (Set.range I) ((extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)))
          (X t ((G.maps3 t) x))) s t := by
  have hmem_t : (G.maps3 t) x ∈ (Kc i : Set M) := interior_subset hmem_int
  have hmem : ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (Kc i : Set M) :=
    eventually_mem_of_tendsto_of_mem_interior (G.continuousWithinAt_eval htG x) hmem_int
  exact
    realization.metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_Kc_Ico
      (M := M) (F := F) (I := I) het G htG hs_sub ht i x hcenter hmem_t hmem

/-- The smooth realization supplies the raw identity-gauge scalar derivative
obligation on the open Banach interval, with the Banach chart right-hand side
as the metric velocity. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) realization.metric
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  exact
    SmoothSelfDiffeomorph3Family.id_pullbackMetricInnerDerivativeOn
      (I := I) (M := M)
      (realization.hasTimeDerivativeOn_Ioo_chartRHS
        (M := M) (F := F) (I := I) x0 het)

/-- The tensor time-derivative form of
`id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS`: the identity raw `C^3`
gauge-pullback of a smooth Banach realization is differentiated by the Banach
chart right-hand side on the open interval. -/
theorem BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricFamily_hasTimeDerivativeOn_Ioo_chartRHS
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (x0 : κ → M)
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
        realization.metric)
      (fun τ x u v ↦ A τ (sol.curve τ) x u v)
      (Ioo ivp.initialTime sol.terminalTime) := by
  simpa [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily] using
    (realization.hasTimeDerivativeOn_Ioo_chartRHS
      (M := M) (F := F) (I := I) x0 het)

/-- Global chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Global chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureData.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureData.nonempty_localExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Global chart-closure data exposes the state-preserving Banach solution,
common-interval uniqueness, and symmetric positive-definite persistence before
passing through smooth realization or theorem-package projections. -/
theorem RicciDeTurckChartClosureData.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_symmetricPositiveDefinite
      (M := M) (F := F) (I := I)

/-- Global chart-closure data also exposes the continuous
Riemannian-metric-valued curve represented by the selected Banach solution. -/
theorem RicciDeTurckChartClosureData.exists_unique_with_continuousRiemannianMetricCurve
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_with_continuousRiemannianMetricCurve
      (M := M) (F := F) (I := I)

/-- Single-choice global closure readout carrying the Banach solution,
common-interval uniqueness, symmetric positive-definite persistence, continuous
Riemannian metric curve, smooth realization, and reverse encoding. -/
theorem RicciDeTurckChartClosureData.exists_unique_with_continuousRiemannianMetricCurve_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      (∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationData
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_with_continuousRiemannianMetricCurve
      (M := M) (F := F) (I := I) with
    ⟨sol, huniq, hspd, hcurve⟩
  exact ⟨sol, huniq, hspd, hcurve,
    ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩⟩

/-- Global closure data selects a canonical continuous Riemannian-metric curve whose
values are unique on common Banach existence intervals. -/
theorem RicciDeTurckChartClosureData.exists_unique_continuousRiemannianMetricCurve_on_common_interval
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∃ hspd : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover,
        ∀ (sol' : BanachEvolutionLocalSolutionIn chart.A
            (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toContinuousSectionSpace
              (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp))
          (hspd' : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol'.terminalTime →
            sol'.curve t ∈ symmetricPositiveDefiniteLocus
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
          ⦃t : ℝ⦄,
          t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime) →
          BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol hspd
              ivp.initialMetric.toContinuousRiemannianMetric t =
            BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol' hspd'
              ivp.initialMetric.toContinuousRiemannianMetric t := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, huniq, hspd⟩
  refine ⟨sol, huniq, hspd, ?_⟩
  intro sol' hspd' t ht
  exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_eq_on_common_interval
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol sol' (huniq sol') hspd hspd'
    ivp.initialMetric.toContinuousRiemannianMetric
    ivp.initialMetric.toContinuousRiemannianMetric ht

/-- Proof-level Banach solution existence readout from global chart-closure data. -/
theorem RicciDeTurckChartClosureData.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, _huniq, _hspd⟩
  exact ⟨sol⟩

/-- Proof-level paired global Banach solution, smooth realization, and reverse
encoding for the chosen-background candidate represented by that realization. -/
theorem RicciDeTurckChartClosureData.nonempty_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      Σ realization : RicciDeTurckSmoothRealizationData
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  exact ⟨⟨sol, D.realization sol, D.realizationCandidateEncoding sol⟩⟩

/-- Interval chart closure data yields the intrinsic compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Interval chart closure data yields the ordinary compact point-4 theorem package
through raw identity `C^3` gauge-flow existence and named scalar derivative data. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact
    D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
      |>.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
          (E := F) (H := H) (I := I) (M := M) ivp)
        (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground_pullbackMetricInnerDerivativeData
          (E := F) (H := H) (I := I) (M := M) ivp)

/-- Proof-level version of
`RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness_viaRawIdentityGauge`. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness_viaRawIdentityGauge
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness_viaRawIdentityGauge⟩

/-- Ambient interval chart-closure data exposes the state-preserving Banach
solution and its common-interval uniqueness witness before passing through the
smooth realization or theorem-package projections. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  exact
    exists_unique_in_positiveDefiniteLocus_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT chart.picard
      (by
        simpa [InitialValueProblem.toContinuousSectionSpace] using
          mem_positiveDefiniteLocus_of_continuousRiemannianMetric
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover
            ivp.initialMetric.toContinuousRiemannianMetric)
      chart.lipschitzOn_Icc

/-- Ambient interval chart-closure data exposes the stronger symmetric
positive-definite persistence statement for the selected Banach solution. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_symmetricPositiveDefinite_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_symmetricPositiveDefinite_terminal_le
      (M := M) (F := F) (I := I)

/-- Ambient interval chart-closure data also exposes the continuous
Riemannian-metric-valued curve represented by the selected Banach solution. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      ∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric := by
  simpa [InitialValueProblem.toContinuousSectionSpace] using
    chart.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
      (M := M) (F := F) (I := I)

/-- Single-choice ambient interval closure readout carrying the Banach solution,
terminal control, common-interval uniqueness, symmetric positive-definite
persistence, continuous Riemannian metric curve, smooth realization, and reverse
encoding. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_with_continuousRiemannianMetricCurve_realization_candidateEncoding_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      (∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ∧
      (∃ G : ℝ → _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _),
        (∀ ⦃t : ℝ⦄, (ht : t ∈ Icc ivp.initialTime sol.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            (G t).inner x u v = sol.curve t x u v) ∧
        G ivp.initialTime = ivp.initialMetric.toContinuousRiemannianMetric) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_with_continuousRiemannianMetricCurve_terminal_le
      (M := M) (F := F) (I := I) with
    ⟨sol, hterminal, huniq, hspd, hcurve⟩
  exact ⟨sol, hterminal, huniq, hspd, hcurve,
    ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩⟩

/-- Interval closure data selects a canonical continuous Riemannian-metric curve
whose values are unique on common Banach existence intervals, while retaining the
Picard terminal-time bound. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_continuousRiemannianMetricCurve_on_common_interval_terminal_le
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∃ hspd : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        sol.curve t ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover,
        ∀ (sol' : BanachEvolutionLocalSolutionIn chart.A
            (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toContinuousSectionSpace
              (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp))
          (hspd' : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol'.terminalTime →
            sol'.curve t ∈ symmetricPositiveDefiniteLocus
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover)
          ⦃t : ℝ⦄,
          t ∈ Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime) →
          BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol hspd
              ivp.initialMetric.toContinuousRiemannianMetric t =
            BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              et Kc hKc Ko hKo hKoEq hcover sol' hspd'
              ivp.initialMetric.toContinuousRiemannianMetric t := by
  rcases D.exists_unique_symmetricPositiveDefinite_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hterminal, huniq, hspd⟩
  refine ⟨sol, hterminal, huniq, hspd, ?_⟩
  intro sol' hspd' t ht
  exact BanachEvolutionLocalSolutionIn.toContinuousRiemannianMetricCurve_eq_on_common_interval
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    et Kc hKc Ko hKo hKoEq hcover sol sol' (huniq sol') hspd hspd'
    ivp.initialMetric.toContinuousRiemannianMetric
    ivp.initialMetric.toContinuousRiemannianMetric ht

/-- Proof-level Banach solution existence readout from ambient interval
chart-closure data. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩

/-- Ambient interval chart-closure data pairs the smooth realization of a chosen
state-preserving Banach solution with the reverse encoding of the realized
chosen-background candidate. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart
        (realization.toChosenIntrinsicDeTurckLocalSolution.1)) :=
  ⟨⟨D.realization sol, D.realizationCandidateEncoding sol⟩⟩

/-- Constructive ambient interval closure readout choosing a Banach solution
together with terminal-time control, common-interval uniqueness, smooth
realization, and reverse encoding for the realized chosen-background candidate. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn chart.A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      Nonempty (Σ realization : RicciDeTurckSmoothRealizationDataOnIcc
          x0 et het Kc hKc Ko hKo hKoEq hcover chart sol,
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) chart
          (realization.toChosenIntrinsicDeTurckLocalSolution.1)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with
    ⟨sol, hsolT, huniq⟩
  exact ⟨sol, hsolT, huniq, D.nonempty_realization_candidateEncoding sol⟩

/-- Proof-level symmetric-carrier interval closure data derived from ambient interval closure data
and a Picard proof on the restricted symmetric carrier. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (picard : IsPicardLindelof
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart.hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic) :
    Nonempty (SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :=
  ⟨SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (D := D) picard⟩

/-- Proof-level symmetric-carrier interval closure data after shrinking the ambient interval chart
inside the Riemannian metric cone. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofShrunkRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (hencode_terminal : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      (D.encode candidate).sol.terminalTime ≤ T') :
    Nonempty (SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover
      (chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime)) :=
  ⟨SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (D := D)
    hT' hT'le ha' htime hball hencode_terminal⟩

/-- If the current chart radius already lies in the Riemannian metric cone, the chart-derived
symmetric carrier exposes an actual state-preserving Banach solution and common-interval uniqueness
without first passing through a smaller metric-cone shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_unique_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    ∃ sol : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F)
            (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  have hpicard :=
    chart.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover hball
  exact
    exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT
      hpicard
      (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      (chart.restrictedSymmetricA_lipschitzOn_Icc
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Proof-level Banach solution existence for the chart-derived symmetric carrier when the current
Picard ball is already contained in the Riemannian metric cone. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases chart.exists_unique_restrictedSymmetricA_banachEvolutionLocalSolutionIn_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I) hball with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩

set_option maxHeartbeats 4000000 in
/-- A positive-radius interval chart can be shrunk to an actual state-preserving Banach solution for
the chart-derived symmetric Riemannian-metric carrier, retaining terminal-time control and uniqueness
on common closed intervals. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          ∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F)
                (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
            sol.terminalTime ≤ T' ∧
            ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F)
                  (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
              EqOn sol.curve sol'.curve
                (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  rcases chart.exists_metricCone_shrunk_restrictedSymmetricA_picard
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, hpicard⟩
  have hLip : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate
      ((chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :=
    chart'.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicard
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLip with
    ⟨sol, hsolT, huniq⟩
  exact ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, sol, hsolT, huniq⟩

/-- Proof-level existence readout for the chart-derived symmetric-carrier Banach solution produced
after the standard metric-cone shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty (BanachEvolutionLocalSolutionIn
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases chart.exists_metricCone_shrunk_restrictedSymmetricA_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) ha with
    ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Symmetric-carrier interval closure data exposes the state-preserving Banach solution and its
common-interval uniqueness witness before passing to intrinsic geometric theorem packages. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.exists_unique_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F)
            (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn sol.curve sol'.curve
          (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  exact
    exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance chart.hT
      D.picard
      (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      (chart.restrictedSymmetricA_lipschitzOn_Icc
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Proof-level Banach solution existence readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, _hsolT, _huniq⟩
  exact ⟨sol⟩

/-- Proof-level smooth-realization readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_realization
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
      (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
        (chart.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) := by
  exact ⟨D.realization sol⟩

/-- Proof-level paired Banach solution and smooth-realization readout from
symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_realization
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  exact ⟨⟨sol, D.realization sol⟩⟩

/-- Proof-level reverse-encoding readout from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp) :
    Nonempty (SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      chart.A
      (chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      candidate.1) := by
  exact ⟨D.encode candidate⟩

/-- Proof-level paired Banach solution, smooth realization, and reverse encoding
for the chosen-background candidate represented by that realization. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      Σ realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol),
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.nonempty_banachEvolutionLocalSolutionIn (M := M) (F := F) (I := I) with ⟨sol⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨⟨sol, realization, D.encode candidate⟩⟩

set_option maxHeartbeats 800000 in
/-- Proof-level paired Banach solution, terminal-time control,
common-interval uniqueness, smooth realization, and reverse encoding for the
chosen-background candidate represented by that realization. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_banachEvolutionLocalSolutionIn_unique_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (Σ sol : { sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) //
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      EqOn sol.curve sol'.curve
        (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) },
      Sigma fun realization :
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol.1)) =>
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hT, huniq⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨⟨⟨sol, hT, huniq⟩, realization, D.encode candidate⟩⟩

set_option maxHeartbeats 800000 in
/-- Constructive readout of the strongest symmetric-carrier interval witness:
choose the Banach solution together with terminal-time control, common-interval
uniqueness, smooth realization, and reverse encoding. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.exists_banachEvolutionLocalSolutionIn_unique_realization_candidateEncoding
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ∃ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      sol.terminalTime ≤ T ∧
      (∀ sol' : BanachEvolutionLocalSolutionIn
        (chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      EqOn sol.curve sol'.curve
        (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      Nonempty (Sigma fun realization :
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)) =>
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          (chart.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          chart.A
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
            (M := M) (F := F) (I := I) realization)) := by
  rcases D.exists_unique_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I) with
    ⟨sol, hT, huniq⟩
  let realization := D.realization sol
  let candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp :=
    ⟨BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
      (M := M) (F := F) (I := I) realization, D.usesChosenBackground sol⟩
  exact ⟨sol, hT, huniq, ⟨⟨realization, D.encode candidate⟩⟩⟩

/-- Proof-level chosen-background theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_chosenIntrinsicDeTurckLocalExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩

/-- Proof-level intrinsic theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_intrinsicLocalExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toIntrinsicLocalExistenceUniqueness⟩

/-- Proof-level ordinary theorem package from symmetric-carrier interval closure data. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_localExistenceUniqueness
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toLocalExistenceUniqueness⟩

/-- Ambient interval closure data yields the chosen-background, intrinsic, and
ordinary point-4 theorem packages without any terminal-fit hypothesis when the
original Picard closed ball is already contained in the Riemannian metric cone.
In this case the chart-derived symmetric carrier is built on the original
interval, so arbitrary reverse-encoded candidate intervals only need their
existing chart terminal bound. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_theoremPackages_of_closedBall_subset_riemannianMetricLocus
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (IntrinsicLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (LocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) := by
  let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart :=
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      (chart.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover hball)
  constructor
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  constructor
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- Ambient interval closure data, after the standard metric-cone shrink to the genuine symmetric
carrier, yields the chosen-background, intrinsic, and ordinary point-4 theorem packages as one
proof-level witness.  The only remaining compatibility input is that encoded candidates fit inside
the selected shrunken chart interval. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_theoremPackages_of_metricCone_shrunk_symmetricCarrier
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (hencode_terminal : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      (D.encode candidate).sol.terminalTime ≤ T') :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (IntrinsicLocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) ∧
      Nonempty (LocalExistenceUniqueness
        (E := F) (H := H) (I := I) (M := M) ivp) := by
  rcases
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.nonempty_ofShrunkRicciDeTurckChartClosureDataOnIcc
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha' htime hball hencode_terminal with
    ⟨Dsym⟩
  constructor
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  constructor
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- Proof-level intrinsic theorem family from symmetric-carrier interval closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from symmetric-carrier interval closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level intrinsic theorem family from global chart-closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from global chart-closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level intrinsic theorem family from interval chart-closure data. -/
theorem nonempty_intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

/-- Proof-level ordinary theorem family from interval chart-closure data. -/
theorem nonempty_localExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    Nonempty (LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M)) :=
  ⟨localExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) T a L Kpic Kstate chart D⟩

end GlobalClosure

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow

