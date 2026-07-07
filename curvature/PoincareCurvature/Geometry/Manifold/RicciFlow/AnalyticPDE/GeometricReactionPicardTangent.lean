module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionCoordBounds
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SectionSpacePicard

/-!
# Tangent-bundle DeTurck reaction: section-space Picard coordinate bounds and `IsPicardLindelof`

This module assembles the section-space Picard `hlip`/`hcenter` coordinate obligations for the concrete
**tangent-bundle** DeTurck reaction operator `deTurckReactionSectionMap` (fiber-norm-free, hence
formable at `W := TangentSpace I`), by connecting its model-fibre readout size bounds
(`GeometricReactionCoordBounds`) to the `coord` language of the section-space Picard bridge through a
**fiber-norm-free** coordinate-readout bridge.

The existing coordinate-readout bridge `bilinearFormBundle_coord_eq_trivializationAt_readout` demands
`[∀ x, SeminormedAddCommGroup (W x)]` (the Π-fibre-seminorm) as an explicit binder, which triggers the
derived-module-vs-norm-module diamond at `W := TangentSpace I`.  The bridge
`deTurckReactionSectionMap_coord_eq_readout` below reproves the identity **directly at the tangent
bundle**, where the section-space seminorm `SeminormedAddCommGroup (BilW x)` is supplied per-`x` by the
canonical tangent norm (a global instance) rather than a Π-binder, and the identity itself goes through
the fiber-norm-free `coord_apply` and the `LocalCoordinatePositivity` trivialization lemmas.
-/

@[expose] public noncomputable section

open Bundle RicciFlow
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization

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

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

/-- **Fiber-norm-free coordinate-readout bridge at the tangent bundle (plain sections).**  For any
section `s` of the canonical `BilinearFormBundle` continuous section space at `W := TangentSpace I`,
the compact coordinate `(coord s).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the raw fibre
readout `(trivializationAt BilF BilW (x0 i) ⟨x, s x⟩).2`.  Same identity as
`bilinearFormBundle_coord_eq_trivializationAt_readout`, but obtained at `W := TangentSpace I` — where
the section-space fibre carries the hom-bundle topology `ContinuousLinearMap.topologicalSpace`, not the
norm-metric topology `coord_apply` resolves to — by unfolding the `coord` definition **directly on the
goal** (so the goal's own hom fibre topology is used consistently), sidestepping the
`ContinuousLinearMap.topologicalSpace`-vs-`PseudoMetricSpace…toTopologicalSpace` fibre-topology diamond
that blocks a direct `coord_apply` rewrite. -/
theorem bilinearFormBundle_coord_eq_trivializationAt_readout_tangent
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1 (s.toFun x.1))).2 := by
  have hx : (x : M) ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i x.2
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  simp [equivCompatibleCoordFamilySubmodule, toSubtype,
    continuousSectionEquivCompatibleCoordFamilySubmodule,
    continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
    compatibleCoordFamilyOfSection, coordFamilyOfSection, coordContinuousMap,
    _root_.Bundle.Trivialization.linearMapAt_apply, hx,
    _root_.Bundle.Trivialization.continuousLinearMapAt_apply,
    _root_.Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

/-- **The tangent-bundle DeTurck reaction operator's coordinate readout equals its `trivializationAt`
fibre readout.**  For the concrete operator `deTurckReactionSectionMap … σ` (fiber-norm-free, formable
at `W := TangentSpace I`), the continuous-section-space coordinate
`(coord (deTurckReactionSectionMap … σ)).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the raw
fibre readout `(trivializationAt BilF BilW (x0 i) ⟨x, deTurckReactionSectionMap … σ x⟩).2`.  Proved at
`W := TangentSpace I` without any `[∀ x, SeminormedAddCommGroup (W x)]` Π-binder (which would trigger
the derived-module-vs-norm-module diamond): it combines the fiber-norm-free `coord_apply` with the
on-baseSet trivialization identity `continuousLinearMapAt = (e ⟨x, ·⟩).2` (`coe_linearMapAt_of_mem`),
the bilinear-form trivialization's linearity supplied by the fiber-norm-free
`trivializationAt_bilinearFormBundle_isLinear`.  This turns the operator's model-fibre readout size
bounds (`GeometricReactionCoordBounds`) into section-space Picard coordinate bounds. -/
theorem deTurckReactionSectionMap_coord_eq_readout
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
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP σ)).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1
            (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover hP σ x.1))).2 :=
  bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP σ) i x

/-- **The tangent-bundle DeTurck reaction operator's section-space Picard `hlip` coordinate bound.**
For the concrete operator `deTurckReactionSectionMap … hP` on the tangent-bundle `BilinearFormBundle`
continuous section space, the pointwise coordinate readout is Lipschitz-in-state:
`dist (coord (deTurck s) i x) (coord (deTurck s') i x) ≤ 2·Kp·dist s s'` for any uniform bound
`Kp ≥ ‖inCoordinates E TM E TM (x₀ i) x (x₀ i) x (P x)‖`.  This is EXACTLY the `hlip` hypothesis of the
topological-fibre section-space Picard bridge
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre`
(with `K := 2·Kp`), assembled at `W := TangentSpace I` where the seminormed-fibre coordinate lemmas
diverge.  Proof: rewrite both operator coordinates to their `trivializationAt` readouts
(`deTurckReactionSectionMap_coord_eq_readout`), bound the readout distance by the reaction's
Lipschitz-in-state fibre bound (`deTurckReactionSectionMap_readout_sub_dist_le_inCoordinates`, with the
`BilF`↔`TM` base-set membership supplied by `simpa`), rewrite the plain-section readouts back to
coordinates (`bilinearFormBundle_coord_eq_trivializationAt_readout_tangent`), and close with the
hom-topology-native coordinate contraction `coord_dist_le_dist_topFibre` (`dist (coord s i x)
(coord s' i x) ≤ dist s s'`) and `‖inCoord (P x)‖ ≤ Kp`. -/
theorem deTurckReactionSectionMap_coord_dist_le_inCoordinates
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
    (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) (Kp : ℝ)
    (hKp : ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp) :
    dist
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s)).1 i x)
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s')).1 i x)
      ≤ 2 * Kp * dist s s' := by
  have hxTM : (x : M) ∈ (trivializationAt E TM (x0 i)).baseSet := by simpa using hKc i x.2
  rw [deTurckReactionSectionMap_coord_eq_readout x0 Kc hKc Ko hKo hKoEq hcover hP s i x,
      deTurckReactionSectionMap_coord_eq_readout x0 Kc hKc Ko hKo hKoEq hcover hP s' i x]
  refine (deTurckReactionSectionMap_readout_sub_dist_le_inCoordinates
    (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover hP s s'
    (x0 i) x hxTM).trans ?_
  rw [← bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover s i x,
      ← bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover s' i x]
  have hcd := coord_dist_le_dist_topFibre s s' i x
  have hIC : (0:ℝ) ≤ ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ :=
    norm_nonneg _
  nlinarith [hcd, hKp, hIC,
    dist_nonneg (α := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) (x := s) (y := s'),
    dist_nonneg (α := BilF)
      (x := (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i x)
      (y := (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s').1 i x)]

/-- **`IsPicardLindelof` for the frozen-coefficient geometric DeTurck reaction operator on the
tangent-bundle continuous section space.**  Given a uniform bound `Kp` on the endomorphism coordinate
readout `‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖` over the finite compact cover, the
time-independent (frozen) reaction operator `t ↦ deTurckReactionSectionMap … hP` satisfies
`IsPicardLindelof` about any initial section `σ₀`, with radius `a`, Lipschitz constant `2·Kp`, and an
auto-chosen forward endpoint `T ∈ (t₀, T₀]` and centre size `Mc`.  This is the concrete tangent-bundle
chart operator's `picard` datum (Path B, no seminormed-fibre diamond): its `hlip` field is the just-proved
`deTurckReactionSectionMap_coord_dist_le_inCoordinates` (with `K := 2·Kp`, the uniform bound feeding each
per-point `‖inCoord (P x)‖ ≤ Kp`), and its `hcont` field is `continuousOn_const` (the operator is
constant in time, so its coordinate readouts are trivially time-continuous).  Feeding the affine
`A t s = deTurckReactionSectionMap ∇W s + (-2)•Ric` source and identifying `P := ∇W` yields the chart's
`picard`; the uniform `Kp` is supplied by compactness of the cover and continuity of the frozen
coefficient's coordinate readout. -/
theorem deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a Kp : ℝ≥0) (ha : 0 < (a : ℝ))
    (hKpU : ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ (Kp : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover hP)
    σ0 t₀ T₀ hT₀ a (2 * Kp) ha ?_ ?_
  · intro t _ht s _hs s' _hs' i x
    have h := deTurckReactionSectionMap_coord_dist_le_inCoordinates xc Kc hKc Ko hKo hKoEq hcover hP
      s s' i x (Kp : ℝ) (hKpU i x)
    calc dist _ _ ≤ 2 * (Kp : ℝ) * dist s s' := h
      _ = ((2 * Kp : ℝ≥0) : ℝ) * dist s s' := by push_cast; ring
  · intro s _hs i
    exact continuousOn_const

/-- **`ContinuousOn` of the frozen coefficient's coordinate readout on a compact piece, at `TM`.**
For a continuous tangent-endomorphism section `P` (into the endomorphism bundle `THom = TM →L[ℝ] TM`),
`x ↦ inCoordinates E TM E TM x₀ x x₀ x (P x)` is continuous on the trivializing set
`(trivializationAt (E →L[ℝ] E) THom x₀).baseSet`.  Proved DIRECTLY at `TM` (the seminormed-fibre
`continuousOn_inCoordinates_of_continuous_homSection` fails to synthesize `FiberBundle E TM` when
applied here): the fixed-centre readout equals `(trivₓ₀ ⟨x, P x⟩).2` (`hom_trivializationAt_apply`),
and the hom trivialization is continuous on its source, which the section maps the base set into.  This
is the per-piece ingredient of the uniform inCoordinates bound. -/
theorem contOn_inCoord_tangent
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (x₀ : M) :
    ContinuousOn (fun x => ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (P x))
      (trivializationAt (E →L[ℝ] E) THom x₀).baseSet := by
  set et := trivializationAt (E →L[ℝ] E) THom x₀ with het
  have hEq : (fun x => ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (P x))
      = fun x => (et (TotalSpace.mk' (E →L[ℝ] E) x (P x))).2 := by
    funext x; rw [het, hom_trivializationAt_apply]
  rw [hEq]
  have hsrc : Set.MapsTo (fun x => TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))
      et.baseSet et.source := fun x hx => by rw [Trivialization.mem_source]; exact hx
  exact continuous_snd.comp_continuousOn (et.continuousOn.comp hP.continuousOn hsrc)

/-- **Uniform bound on the frozen coefficient's coordinate readout over a finite compact cover.**  For
a continuous tangent-endomorphism section `P` and a finite family of compact pieces `Kc i`, each inside
the `THom` trivializing set of its centre `xc i`, there is a single `Kp ≥ 0` with
`‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ Kp` for all `i` and `x ∈ Kc i`.  Each per-piece
readout is continuous (`contOn_inCoord_tangent`) hence bounded on the compact `Kc i`
(`IsCompact.exists_bound_of_continuousOn`), and a `Finite κ` supremum of the finitely many bounds gives
the uniform `Kp`.  This discharges the uniform-`Kp` hypothesis of
`deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates`. -/
theorem exists_uniform_inCoord_bound
    {κ : Type*} [Finite κ] (xc : κ → M) (Kc : κ → TopologicalSpace.Compacts M)
    (hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ Kp := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hcont : ∀ i, ContinuousOn
      (fun x => ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x))
      (Kc i) :=
    fun i => (contOn_inCoord_tangent hP (xc i)).mono (hKcTM i)
  choose C hC using fun i => (Kc i).isCompact.exists_bound_of_continuousOn (hcont i)
  obtain ⟨D, hD⟩ := (Set.finite_range C).bddAbove
  refine ⟨max D 0, le_max_right _ _, fun i x => ?_⟩
  exact le_trans (hC i (x : M) x.2) (le_trans (hD (Set.mem_range_self i)) (le_max_left _ _))

/-- **Unconditional `IsPicardLindelof` for the frozen-coefficient geometric DeTurck reaction operator
at `TM`.**  Combining the uniform inCoordinates bound `exists_uniform_inCoord_bound` (which supplies the
uniform Lipschitz constant `Kp` by compactness of the finite cover + continuity of the frozen
coefficient `P`) with the conditional construction
`deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates`, the frozen (time-independent)
reaction operator `t ↦ deTurckReactionSectionMap … hP` satisfies `IsPicardLindelof` about any initial
section `σ₀` — with NO uniform-`Kp` hypothesis, only continuity of `P` and the compact cover.  The
cover's `BilinearFormBundle` trivializing sets coincide with the `THom` trivializing sets (both reduce to
the underlying `TangentSpace` trivializing set), supplied by `simpa`.  This is the frozen reaction's
`picard` datum on the Path-B tangent-bundle section space, fully constructed for a general continuous
frozen coefficient. -/
theorem deTurckReactionSectionMap_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_uniform_inCoord_bound xc Kc hKcTM hP
  have hcast : ((Kp.toNNReal : ℝ≥0) : ℝ) = Kp := Real.coe_toNNReal Kp hKp0
  obtain ⟨T, hT, Mc, hPL⟩ := deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates
    xc Kc hKc Ko hKo hKoEq hcover hP σ0 t₀ T₀ hT₀ a Kp.toNNReal ha
    (fun i x => by rw [hcast]; exact hKpb i x)
  exact ⟨Kp.toNNReal, T, hT, Mc, hPL⟩

/-- **`IsPicardLindelof` for the affine geometric DeTurck operator (frozen reaction + fixed source) on
the tangent-bundle section space, conditional on a uniform inCoordinates bound.**  Given a uniform bound
`Kp` on the endomorphism coordinate readout `‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖` over the
finite compact cover, the affine operator `A t s = deTurckReactionSectionMap … hP s + b` — the frozen
DeTurck reaction plus a FIXED source section `b` (typically the `(-2)•Ric` principal Ricci source frozen
at `g₀`, `b := intrinsicRicciFlowRHSSectionSpace g₀`) — satisfies `IsPicardLindelof` about any initial
section `σ₀`, with radius `a`, Lipschitz constant `2·Kp`, and an auto-chosen forward endpoint
`T ∈ (t₀, T₀]` and centre size `Mc`.  The affine part is DIAGNOSTIC-FREE for the Lipschitz bound: the
fixed source `b` contributes the SAME coordinate summand to `A t s` and `A t s'`, so it cancels in the
coordinate distance (`coord_add_apply_topFibre` then `dist_add_right`), leaving the frozen reaction's
`hlip` bound `deTurckReactionSectionMap_coord_dist_le_inCoordinates` unchanged (constant `2·Kp`).  The
`hcont` field is again `continuousOn_const` (both summands are frozen in time), and the centre size `Mc`
is derived internally by the bridge (absorbing `‖coord b‖`).  This is the affine chart operator's
`picard` datum on the Path-B tangent-bundle section space (no seminormed-fibre diamond). -/
theorem deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a Kp : ℝ≥0) (ha : 0 < (a : ℝ))
    (hKpU : ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ (Kp : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover hP s + b)
    σ0 t₀ T₀ hT₀ a (2 * Kp) ha ?_ ?_
  · intro t _ht s _hs s' _hs' i x
    simp only [coord_add_apply_topFibre, dist_add_right]
    have h := deTurckReactionSectionMap_coord_dist_le_inCoordinates xc Kc hKc Ko hKo hKoEq hcover hP
      s s' i x (Kp : ℝ) (hKpU i x)
    calc dist _ _ ≤ 2 * (Kp : ℝ) * dist s s' := h
      _ = ((2 * Kp : ℝ≥0) : ℝ) * dist s s' := by push_cast; ring
  · intro s _hs i
    exact continuousOn_const

/-- **Unconditional `IsPicardLindelof` for the affine geometric DeTurck operator (frozen reaction +
fixed source) at `TM`.**  Combining the uniform inCoordinates bound `exists_uniform_inCoord_bound`
(which supplies the uniform Lipschitz constant `Kp` by compactness of the finite cover + continuity of
the frozen coefficient `P`) with the conditional affine construction
`deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates`, the affine
operator `A t s = deTurckReactionSectionMap … hP s + b` — frozen reaction plus a FIXED source `b` —
satisfies `IsPicardLindelof` about any initial section `σ₀` with NO uniform-`Kp` hypothesis, only
continuity of `P` and the compact cover.  This is the full frozen chart operator's `picard` datum:
feeding `b := intrinsicRicciFlowRHSSectionSpace g₀` (the `(-2)•Ric` principal Ricci source) and
`P := ∇W` (the frozen DeTurck coefficient) yields the concrete Ricci–DeTurck chart's `picard`, whose
Banach evolution solution decodes to `RicciDeTurckChartClosureData.realization`. -/
theorem deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_uniform_inCoord_bound xc Kc hKcTM hP
  have hcast : ((Kp.toNNReal : ℝ≥0) : ℝ) = Kp := Real.coe_toNNReal Kp hKp0
  obtain ⟨T, hT, Mc, hPL⟩ :=
    deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates
      xc Kc hKc Ko hKo hKoEq hcover hP b σ0 t₀ T₀ hT₀ a Kp.toNNReal ha
      (fun i x => by rw [hcast]; exact hKpb i x)
  exact ⟨Kp.toNNReal, T, hT, Mc, hPL⟩

/-- **`BanachEvolutionLocalSolutionIn` for the affine geometric DeTurck operator (frozen reaction +
fixed source) at `TM`.**  Feeding the unconditional affine `IsPicardLindelof`
`deTurckReactionSectionMap_add_source_exists_isPicardLindelof` to the closed-ball a-posteriori bridge
`IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`, the affine operator
`A t s = deTurckReactionSectionMap … hP s + b` — the frozen DeTurck reaction plus a fixed source `b` —
admits a genuine `BanachEvolutionLocalSolutionIn` in any state locus containing the Picard closed ball
`closedBall σ₀ a`, on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen.  The tangent-bundle
section space is complete (`instCompleteSpace`, since the model fibre `BilF = E →L[ℝ] E →L[ℝ] ℝ` is
complete), so the closed-ball bridge applies.  This is precisely the state-constrained Banach evolution
solution the downstream `realization` decode into a genuine intrinsic De Turck local solution consumes:
taking `b := intrinsicRicciFlowRHSSectionSpace g₀` (the `(-2)•Ric` principal Ricci source), `P := ∇W`
(the frozen DeTurck coefficient), and `locus :=` the positive-definite / Riemannian-metric cone
(containing the ball for suitably small `a`) yields the chart's `realization` input. -/
theorem deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (hsub : Metric.closedBall σ0 (a : ℝ) ⊆ locus) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b) locus t₀ σ0) := by
  obtain ⟨Kp, T, hT, Mc, hPL⟩ := deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover hP b σ0 t₀ T₀ hT₀ a ha
  exact ⟨T, hT,
    IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT hPL hsub⟩

/-- **`BanachEvolutionLocalSolutionIn` for the CONCRETE geometric frozen Ricci–DeTurck operator at
`TM`.**  Specialising `deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn` to
the genuine geometric data: the frozen DeTurck coefficient `P := ∇W = (chosenLeviCivitaFamily g t)
(intrinsicDeTurckVectorField g background t)` (continuous by
`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, which needs only a `C¹` background
slice `hbackground`), and the principal Ricci source `b := intrinsicRicciFlowRHSSectionSpace … g t`
(the `(-2)•Ric` term as a named `ContinuousSectionSpace` value, pointwise identity
`intrinsicRicciFlowRHSSectionSpace_apply`).  The frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` admits a genuine
`BanachEvolutionLocalSolutionIn` in any state locus containing the Picard closed ball `closedBall σ₀ a`,
on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen — unconditionally (the uniform Lipschitz
`Kp` is discharged by compactness of the finite cover + continuity of `∇W`).  At the metric section
`s = (g t).toSection` this operator reproduces the full intrinsic Ricci–DeTurck RHS
(`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`),
so it is the concrete geometric Banach evolution solution the chart-closure `realization` decode into a
genuine intrinsic De Turck local solution consumes. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (hsub : Metric.closedBall σ0 (a : ℝ) ⊆ locus) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        locus t₀ σ0) :=
  deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn
    xc Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    σ0 t₀ T₀ hT₀ a ha locus hsub

/-- **The frozen geometric DeTurck reaction operator is `LipschitzOnWith 2·Kp` on any state locus.**
The section-space chart `lipschitz` field for the bare reaction operator `deTurckReactionSectionMap …`:
from a *uniform* bound `Kp` on the frozen coefficient `P`'s model-fibre readout over the finite compact
cover, the per-coordinate Lipschitz bound `deTurckReactionSectionMap_coord_dist_le_inCoordinates` is
lifted to a genuine `LipschitzOnWith ⟨2·Kp, _⟩` on the section space via
`lipschitzOnWith_of_forall_coord_dist_le` (the finite-cover coordinate-to-global norm handoff).  This
is the substantive Lipschitz content of the chart operator's `lipschitz` field. -/
theorem deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates
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
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)) :
    LipschitzOnWith ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP)
      stateSet := by
  refine lipschitzOnWith_of_forall_coord_dist_le ?_
  intro s _hs s' _hs' i x
  simpa only [NNReal.coe_mk] using
    deTurckReactionSectionMap_coord_dist_le_inCoordinates
      x0 Kc hKc Ko hKo hKoEq hcover hP s s' i x Kp (hKp i x)

/-- **The affine frozen geometric DeTurck chart operator `A τ s = deTurckReactionSectionMap ∇W s + b`
is `LipschitzOnWith 2·Kp` on any state locus — the literal chart `lipschitz` field.**  Adding the fixed
source section `b` contributes the same coordinate summand to `A τ s` and `A τ s'`, which cancels in
every compact coordinate distance (`coord_add_apply_topFibre` then the fibre translation isometry
`dist_add_right`), so the reaction's per-coordinate Lipschitz bound
`deTurckReactionSectionMap_coord_dist_le_inCoordinates` transfers verbatim through
`lipschitzOnWith_of_forall_coord_dist_le`.  This is exactly the
`lipschitz : ∀ t, LipschitzOnWith Kstate (A t) locus` field of the
`TimeDependentGeometricRicciDeTurckBanachChart` for the concrete tangent-bundle frozen operator, with
`Kstate = 2·Kp` (uniform over `t`, the operator being time-independent). -/
theorem deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
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
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)) :
    LipschitzOnWith ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b)
      stateSet := by
  refine lipschitzOnWith_of_forall_coord_dist_le ?_
  intro s _hs s' _hs' i x
  simp only [coord_add_apply_topFibre, dist_add_right, NNReal.coe_mk]
  exact deTurckReactionSectionMap_coord_dist_le_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP s s' i x Kp (hKp i x)

/-- **Global `LipschitzWith 2·Kp` for the bare frozen geometric DeTurck reaction operator.**  The
unconstrained (`LipschitzWith`) strengthening of
`deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates`: from a uniform bound `Kp` on the
frozen coefficient `P`'s model-fibre readout over the finite compact cover, the reaction operator
`deTurckReactionSectionMap …` is globally `LipschitzWith ⟨2·Kp, _⟩` on the whole `ContinuousSectionSpace`
via the global finite-cover coordinate handoff `lipschitzWith_of_forall_coord_dist_le` — the exact
`hlip` shape the Banach-space Picard–Lindelöf foundation consumes, and in particular giving global
continuity of the mild representative (`LipschitzWith.continuous`). -/
theorem deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates
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
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp) :
    LipschitzWith ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP) := by
  rw [← lipschitzOnWith_univ]
  exact deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp Set.univ

/-- **Global `LipschitzWith 2·Kp` for the affine frozen geometric DeTurck chart operator
`A τ s = deTurckReactionSectionMap ∇W s + b`.**  The unconstrained strengthening of
`deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates`: the fixed source `b`
cancels in every coordinate distance (`coord_add_apply_topFibre` + fibre `dist_add_right`), so the affine
chart operator is globally `LipschitzWith ⟨2·Kp, _⟩` on the whole section space — the `hlip` datum of the
Banach-space Picard–Lindelöf foundation for the concrete tangent-bundle chart operator `A`, and giving
its global continuity as a section-space map (`LipschitzWith.continuous`). -/
theorem deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates
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
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    LipschitzWith ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) := by
  rw [← lipschitzOnWith_univ]
  exact deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp b Set.univ

/-- **The affine frozen geometric DeTurck chart operator `A τ s = deTurckReactionSectionMap ∇W s + b`
is continuous as a section-space map.**  Immediate from its global Lipschitz bound
`deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates`
(`LipschitzWith.continuous`); the concrete geometric chart operator `A`, being globally Lipschitz, is in
particular a continuous self-map of the `ContinuousSectionSpace`. -/
theorem deTurckReactionSectionMap_add_source_continuous_of_uniform_inCoordinates
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
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    Continuous
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) :=
  (deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp b).continuous

/-- **`BanachEvolutionLocalSolutionIn` for the concrete geometric frozen Ricci–DeTurck operator, in the
positive-definite locus, at the initial-metric section.**  Specialising
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn` to `locus := positiveDefiniteLocus`
and `σ₀ := g₀.toSection` for a genuine continuous Riemannian metric `g₀`: the geometric a-priori
positivity containment `ContinuousRiemannianMetric.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus`
(openness of the positive-definite locus, from continuity of positive-definiteness on the finite compact
cover) supplies a positive Picard radius `a` whose whole closed ball `closedBall g₀.toSection a` stays
inside the locus, discharging the closed-ball Banach-solution bridge's `hsub` hypothesis.  Hence the
frozen geometric operator `A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`
admits a genuine `BanachEvolutionLocalSolutionIn` **constrained to the positive-definite locus**, at the
metric section of `g₀`, on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen — unconditionally
(the uniform Lipschitz `Kp` is discharged by compactness of the finite cover + continuity of `∇W`).  This
is the precise positive-definite-locus-constrained Banach evolution solution the chart-closure
`realization` field consumes (its `sol : BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …)
ivp.initialTime (ivp initial section)`), assembled here from the two previously independent halves: the
geometric Banach existence and the a-priori positivity containment. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric E TM)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩) := by
  obtain ⟨a, ha, hsub⟩ := g₀.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus
    (M := M) (F := E) (W := TM) xc (fun i => trivializationAt BilF BilW (xc i))
    (fun _ => rfl) Kc hKc Ko hKo hKoEq hcover
  exact deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ⟨g₀.toSection, g₀.continuous_toSection⟩ t₀ T₀ hT₀ a (NNReal.coe_pos.mpr ha) _ hsub

/-- **`BanachEvolutionLocalSolutionIn` for the frozen geometric Ricci–DeTurck operator, in the
positive-definite locus, at the initial section of a Ricci–DeTurck initial value problem.**  The
IVP-vocabulary specialisation of
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus` obtained with
`g₀ := ivp.initialMetric.toContinuousRiemannianMetric` and `t₀ := ivp.initialTime`: since
`InitialValueProblem.toContinuousSectionSpace … ivp` is by definition
`⟨ivp.initialMetric.toContinuousRiemannianMetric.toSection, …⟩`, the produced Banach evolution local
solution is anchored exactly at the IVP's initial section, on the IVP's initial time, constrained to the
positive-definite locus.  This is *precisely* the shape of the `sol` argument the chart-closure
`realization` field consumes
(`BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …) ivp.initialTime
(InitialValueProblem.toContinuousSectionSpace … ivp)`), modulo the identification of the frozen
geometric operator with the chart's `A`. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus_ivp
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (ivp : RicciFlow.InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (T₀ : ℝ) (hT₀ : ivp.initialTime < T₀) :
    ∃ (T : ℝ) (_ : ivp.initialTime < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (RicciFlow.AnalyticPDE.MetricLocusEvolution.InitialValueProblem.toContinuousSectionSpace
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover ivp)) :=
  deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T₀ hT₀

/-- **`IsPicardLindelof` for the concrete geometric frozen Ricci–DeTurck operator at `TM` — the chart
`picard`-field datum.**  Specialising `deTurckReactionSectionMap_add_source_exists_isPicardLindelof` to
the genuine geometric data: the frozen DeTurck coefficient `P := ∇W = (chosenLeviCivitaFamily g t)
(intrinsicDeTurckVectorField g background t)` (continuous by
`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, needing only a `C¹` background slice
`hbackground`) and the principal Ricci source `b := intrinsicRicciFlowRHSSectionSpace … g t` (the
`(-2)•Ric` term as a named `ContinuousSectionSpace` value).  The frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` satisfies
`IsPicardLindelof` about any initial section `σ₀`, on an auto-chosen forward window `[t₀, T]` with
`T ∈ (t₀, T₀]`, with radius `a`, Lipschitz constant `2·Kp` and centre size `Mc + 2·Kp·a` — all produced
internally (the uniform Lipschitz `Kp` discharged by compactness of the finite cover + continuity of
`∇W`, the centre bound derived from continuity of the readout on the compact window).  This is the
literal `picard` datum of the `TimeDependentGeometricRicciDeTurckBanachChart` for the concrete
tangent-bundle geometric operator; the companion
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn` feeds this very datum to the
closed-ball a-posteriori bridge to obtain the chart's Banach evolution solution. -/
theorem deTurckFrozenGeometric_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) :=
  deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    σ0 t₀ T₀ hT₀ a ha

/-- **The tangent-bundle DeTurck reaction operator lands in the pointwise symmetric locus.**  By
`deTurckReactionSectionMap_apply`, `deTurckReactionSectionMap … hP s x u v = s x (P x u) v +
s x (P x v) u` is manifestly symmetric in `(u, v)` (the two summands merely swap), so the reaction
operator maps *every* section `s` — symmetric or not — into the symmetric locus.  This is the
operator-level (set-membership) companion of the pointwise `intrinsicDeTurckCorrectionSectionSpace_symm`
value symmetry: it is exactly the datum certifying that the reaction summand of the affine chart split
`A τ s = reaction s + b` keeps the Banach velocity in `symmetricLocus`. -/
theorem deTurckReactionSectionMap_mem_symmetricLocus
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF
      (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    deTurckReactionSectionMap et Kc hKc Ko hKo hKoEq hcover hP s
      ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover := by
  intro x u v
  simp only [deTurckReactionSectionMap_apply]
  ring

/-- **The affine DeTurck reaction operator preserves the symmetric locus.**  Adding a symmetric
source `b` to the reaction value keeps the result symmetric: `deTurckReactionSectionMap … hP s + b`
lies in the pointwise symmetric locus whenever `b` does.  This is the operator-level statement for the
whole affine chart split `A τ s = reaction s + b`; combined with symmetry of the concrete `(-2)•Ric`
source it certifies the geometric Ricci–DeTurck chart velocity is symmetric. -/
theorem deTurckReactionSectionMap_add_mem_symmetricLocus
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → Trivialization BilF
      (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hb : b ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    (deTurckReactionSectionMap et Kc hKc Ko hKo hKoEq hcover hP s + b)
      ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover := by
  have hr := deTurckReactionSectionMap_mem_symmetricLocus
    et Kc hKc Ko hKo hKoEq hcover hP s
  rw [← mem_symmetricSectionSubmodule_iff x0 et het Kc hKc Ko hKo hKoEq hcover] at hr hb ⊢
  exact add_mem hr hb

/-- **The concrete geometric frozen Ricci–DeTurck chart operator lands in the symmetric locus.**
For every section `s`, the frozen geometric operator value
`A s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` — the operator whose
`IsPicardLindelof` is `deTurckFrozenGeometric_exists_isPicardLindelof` — lies in the pointwise
symmetric locus.  The `∇W` reaction summand is symmetric unconditionally
(`deTurckReactionSectionMap_mem_symmetricLocus`) and the principal `(-2)•Ric` source is symmetric by
`intrinsicRicciFlowRHSSectionSpace_symm`.  This is the direct (frozen-operator) analogue of
`TimeDependentGeometricRicciDeTurckBanachChart.A_mem_symmetricLocus`, established here without routing
through the chart's `geometric` identification field: it certifies that the Banach evolution velocity
of the geometric chart operator is symmetric, so its solution curve stays a symmetric metric family. -/
theorem deTurckFrozenGeometric_A_mem_symmetricLocus
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover) :
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover
        (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          g background t hbackground).continuous s
      + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover g t)
      ∈ symmetricLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover :=
  deTurckReactionSectionMap_add_mem_symmetricLocus
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl) Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    (fun x u v => RicciFlow.intrinsicRicciFlowRHSSectionSpace_symm
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover g t x u v)
    s

/-- **The geometric frozen Ricci–DeTurck chart operator has vanishing coordinatewise symmetry
defect.**  The `coordwiseSymmetryDefectContinuousLinearMap` form of
`deTurckFrozenGeometric_A_mem_symmetricLocus`, obtained through
`coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff`: the transported coordinatewise
antisymmetric-defect readout of the frozen geometric operator value vanishes.  This is the direct
(frozen-operator) analogue of
`TimeDependentGeometricRicciDeTurckBanachChart.A_coordwiseSymmetryDefect_eq_zero` — the defect-zero
datum the symmetric-carrier / interval-defect chart machinery consumes — obtained here without the
chart's `geometric` identification field. -/
theorem deTurckFrozenGeometric_A_coordwiseSymmetryDefect_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover) :
    coordwiseSymmetryDefectContinuousLinearMap (F := E) (V := BilW)
        (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
            Kc hKc Ko hKo hKoEq hcover
            (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace
              (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t) = 0 :=
  (coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    (M := M) (F := E) (W := TM)
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl)
    Kc hKc Ko hKo hKoEq hcover
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover
        (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          g background t hbackground).continuous s
      + RicciFlow.intrinsicRicciFlowRHSSectionSpace
          (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover g t)).2
    (deTurckFrozenGeometric_A_mem_symmetricLocus
      xc Kc hKc Ko hKo hKoEq hcover g background t hbackground s)

/-- **The frozen geometric Ricci–DeTurck operator's Banach evolution solution stays in the symmetric
positive-definite locus.**  Strengthening
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus` with a *symmetric*
conclusion: the concrete frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`, whose
`IsPicardLindelof` datum is `deTurckFrozenGeometric_exists_isPicardLindelof` and whose uniform Lipschitz
control is `deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates`, admits a
Banach evolution local solution — anchored at the metric section `g₀.toSection` of a genuine continuous
Riemannian metric `g₀`, constrained to the positive-definite locus, forward-unique on the overlap of
Picard intervals — whose curve additionally stays in the *symmetric* positive-definite locus at every
time of its interval.  The symmetric containment is obtained WITHOUT the chart's `geometric`
identification field: it is fed purely by the frozen operator's velocity symmetry
`deTurckFrozenGeometric_A_mem_symmetricLocus` (`A τ s ∈ symmetricLocus` for every section `s`) through
the ODE symmetric-carrier invariance
`exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn`
(the coordinatewise antisymmetric defect satisfies the same linear ODE, starts at `0` since `g₀` is
symmetric, hence stays `0`).  This certifies the frozen geometric Banach solution curve is a genuine
symmetric-positive-definite metric family — the realization-side consistency datum a `RicciDeTurckChart`
closure needs for its `sol` to decode into an intrinsic metric evolution — available independently of
the `geometric`/`realization` parabolic reconciliation. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric E TM)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) :
    ∃ sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩,
      (∀ sol' : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
          (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
            Kc hKc Ko hKo hKoEq hcover
            (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background t hbackground).continuous s
            + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
                Kc hKc Ko hKo hKoEq hcover g t)
          (positiveDefiniteLocus (M := M) (F := E) (W := TM)
            (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
          t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩,
        Set.EqOn sol.curve sol'.curve
          (Set.Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ Set.Icc t₀ sol.terminalTime →
        sol.curve τ ∈ symmetricPositiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp', hKp'0, hKp'b⟩ := exists_uniform_inCoord_bound xc Kc hKcTM
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
  obtain ⟨Kp, T, hT, Mc, hPL⟩ := deTurckFrozenGeometric_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ⟨g₀.toSection, g₀.continuous_toSection⟩ t₀ T₀ hT₀ 1 (by norm_num)
  exact RicciFlow.AnalyticPDE.MetricLocusEvolution.exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    (M := M) (F := E) (W := TM)
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl)
    Kc hKc Ko hKo hKoEq hcover inferInstance hT hPL
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover g₀)
    (fun _ => deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
      xc Kc hKc Ko hKo hKoEq hcover
      (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
        g background t hbackground).continuous Kp' hKp'0 hKp'b
      (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover g t)
      (positiveDefiniteLocus (M := M) (F := E) (W := TM)
        (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (fun _ s _ => deTurckFrozenGeometric_A_mem_symmetricLocus
      xc Kc hKc Ko hKo hKoEq hcover g background t hbackground s)

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
