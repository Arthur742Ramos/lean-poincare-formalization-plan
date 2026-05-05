module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Separation.Hausdorff
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Existence interfaces for `C^3` DeTurck gauge flows

This module isolates the remaining raw gauge-flow existence obligation from the
Ricci-flow theorem packages.  A future manifold ODE-flow construction should
produce `Diffeomorph3GaugeFlowOn` witnesses; this file turns those witnesses into
the fixed-IVP and theorem-family geometric gauge-flow bundles consumed by the
endpoint Ricci-flow APIs.
-/

@[expose] public noncomputable section

open Bundle
open Set
open scoped Manifold ContDiff Topology

namespace RicciFlow

section OpenPartialHomeomorphTransport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Glue pointwise equality across an indexed cover of a visible domain. -/
theorem eqOn_of_iUnion_eqOn
    {ι : Type*} {F G : X → Y} {s : Set X} {U : ι → Set X}
    (hcover : s ⊆ ⋃ i, U i)
    (heq : ∀ i, EqOn F G (s ∩ U i)) :
    EqOn F G s := by
  intro x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxU⟩
  exact heq i ⟨hx, hxU⟩

/-- A function is continuous on a domain if every point of the domain has an
open neighborhood on which it agrees with some continuous local readout.  This
is the topological continuity-gluing bridge used after chartwise Picard
time-slices have been identified with a candidate manifold map. -/
theorem continuousOn_of_locally_eqOn_open_continuousOn
    {F : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∃ U : Set X, ∃ G : X → Y,
      IsOpen U ∧ x ∈ U ∧ ContinuousOn G U ∧ EqOn F G (s ∩ U)) :
    ContinuousOn F s := by
  refine continuousOn_of_locally_continuousOn ?_
  intro x hx
  rcases h x hx with ⟨U, G, hUopen, hxU, hG, hEq⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  exact (hG.mono inter_subset_right).congr hEq

/-- Indexed open-cover version of
`continuousOn_of_locally_eqOn_open_continuousOn`.  If local readouts are
continuous on an open cover and agree with a candidate map on the visible
domain, then the candidate is continuous on that domain. -/
theorem continuousOn_of_iUnion_open_eqOn_continuousOn
    {ι : Type*} {F : X → Y} {G : ι → X → Y}
    {s : Set X} {U : ι → Set X}
    (hcover : s ⊆ ⋃ i, U i)
    (hUopen : ∀ i, IsOpen (U i))
    (hcont : ∀ i, ContinuousOn (G i) (U i))
    (heq : ∀ i, EqOn F (G i) (s ∩ U i)) :
    ContinuousOn F s :=
  continuousOn_of_locally_eqOn_open_continuousOn fun x hx ↦ by
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxU⟩
    exact ⟨U i, G i, hUopen i, hxU, hcont i, heq i⟩

/-- Glue left-inverse identities across an indexed cover when the global
forward/backward candidates agree with the local forward/backward readouts on
the relevant visible sets. -/
theorem leftInvOn_of_iUnion_eqOn_leftInvOn
    {ι : Type*} {F : X → Y} {G : Y → X}
    {Fₗ : ι → X → Y} {Gₗ : ι → Y → X}
    {s : Set X} {U : ι → Set X}
    (hcover : s ⊆ ⋃ i, U i)
    (hF : ∀ i, EqOn F (Fₗ i) (s ∩ U i))
    (hG : ∀ i, EqOn G (Gₗ i) (F '' (s ∩ U i)))
    (hinv : ∀ i, LeftInvOn (Gₗ i) (Fₗ i) (s ∩ U i)) :
    LeftInvOn G F s := by
  intro x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxU⟩
  have hxU' : x ∈ s ∩ U i := ⟨hx, hxU⟩
  calc
    G (F x) = Gₗ i (F x) := hG i ⟨x, hxU', rfl⟩
    _ = Gₗ i (Fₗ i x) := by rw [hF i hxU']
    _ = x := hinv i hxU'

/-- Glue right-inverse identities across an indexed cover when the global
forward/backward candidates agree with the local forward/backward readouts on
the relevant visible sets. -/
theorem rightInvOn_of_iUnion_eqOn_rightInvOn
    {ι : Type*} {F : X → Y} {G : Y → X}
    {Fₗ : ι → X → Y} {Gₗ : ι → Y → X}
    {t : Set Y} {V : ι → Set Y}
    (hcover : t ⊆ ⋃ i, V i)
    (hG : ∀ i, EqOn G (Gₗ i) (t ∩ V i))
    (hF : ∀ i, EqOn F (Fₗ i) (G '' (t ∩ V i)))
    (hinv : ∀ i, RightInvOn (Gₗ i) (Fₗ i) (t ∩ V i)) :
    RightInvOn G F t := by
  intro y hy
  rcases Set.mem_iUnion.mp (hcover hy) with ⟨i, hyV⟩
  have hyV' : y ∈ t ∩ V i := ⟨hy, hyV⟩
  calc
    F (G y) = Fₗ i (G y) := hF i ⟨y, hyV', rfl⟩
    _ = Fₗ i (Gₗ i y) := by rw [hG i hyV']
    _ = y := hinv i hyV'

/-- Shrink an `OpenPartialHomeomorph` local inverse patch to prescribed open
source and target constraints, retaining a bijective open patch for the
prescribed forward map. -/
theorem exists_open_nhds_bijOn_subset_of_openPartialHomeomorph
    {g : X → X} {x : X} {φ : OpenPartialHomeomorph X X}
    (hφ : (φ : X → X) = g) (hx : x ∈ φ.source)
    {S T : Set X}
    (hSopen : IsOpen S) (hxS : x ∈ S)
    (hTopen : IsOpen T) (hxT : g x ∈ T) :
    ∃ U W : Set X,
      IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
        IsOpen W ∧ g x ∈ W ∧ W ⊆ T ∧ BijOn g U W := by
  let U : Set X := φ.source ∩ S ∩ φ ⁻¹' T
  let W : Set X := φ '' U
  have hxTφ : φ x ∈ T := by
    simpa [hφ] using hxT
  have hUopen : IsOpen U := by
    have hpre : IsOpen (φ.source ∩ φ ⁻¹' T) := φ.isOpen_inter_preimage hTopen
    simpa [U, inter_assoc, inter_left_comm, inter_comm] using hpre.inter hSopen
  have hxU : x ∈ U := ⟨⟨hx, hxS⟩, hxTφ⟩
  have hUsource : U ⊆ φ.source := fun _ hz ↦ hz.1.1
  have hUS : U ⊆ S := fun _ hz ↦ hz.1.2
  have hWopen : IsOpen W := φ.isOpen_image_of_subset_source hUopen hUsource
  have hxW : g x ∈ W := by
    refine ⟨x, hxU, ?_⟩
    simpa [hφ]
  have hWT : W ⊆ T := by
    rintro _ ⟨z, hzU, rfl⟩
    exact hzU.2
  have hbijφ : BijOn φ U W := (φ.injOn.mono hUsource).bijOn_image
  exact ⟨U, W, hUopen, hxU, hUS, hWopen, hxW, hWT,
    hbijφ.congr (fun _ _ ↦ by simpa [hφ])⟩

/-- Transport a model-space `MapsTo` statement through source and target
partial homeomorphism charts.  The extra source-membership hypothesis records
that the uncharted map lands in the target chart source on the visible patch. -/
theorem mapsTo_symm_image_of_openPartialHomeomorph_model_mapsTo
    (e₀ e₁ : OpenPartialHomeomorph X Y) (F : X → X) {U W : Set Y}
    (hFsource : MapsTo F (e₀.symm '' U) e₁.source)
    (hmaps : MapsTo (fun y : Y ↦ e₁ (F (e₀.symm y))) U W) :
    MapsTo F (e₀.symm '' U) (e₁.symm '' W) := by
  rintro _ ⟨y, hyU, rfl⟩
  exact ⟨e₁ (F (e₀.symm y)), hmaps hyU,
    e₁.left_inv (hFsource ⟨y, hyU, rfl⟩)⟩

/-- Transport model-space injectivity through source and target partial
homeomorphism charts. -/
theorem injOn_symm_image_of_openPartialHomeomorph_model_injOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (F : X → X) {U : Set Y}
    (hinj : InjOn (fun y : Y ↦ e₁ (F (e₀.symm y))) U) :
    InjOn F (e₀.symm '' U) := by
  rintro _ ⟨y, hyU, rfl⟩ _ ⟨z, hzU, rfl⟩ hF
  congr 1
  exact hinj hyU hzU (congrArg e₁ hF)

/-- Transport a model-space bijection through source and target partial
homeomorphism charts. -/
theorem bijOn_symm_image_of_openPartialHomeomorph_model_bijOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (F : X → X) {U W : Set Y}
    (hWt : W ⊆ e₁.target)
    (hFsource : MapsTo F (e₀.symm '' U) e₁.source)
    (hbij : BijOn (fun y : Y ↦ e₁ (F (e₀.symm y))) U W) :
    BijOn F (e₀.symm '' U) (e₁.symm '' W) := by
  refine ⟨
    mapsTo_symm_image_of_openPartialHomeomorph_model_mapsTo
      e₀ e₁ F hFsource hbij.mapsTo,
    injOn_symm_image_of_openPartialHomeomorph_model_injOn
      e₀ e₁ F hbij.injOn,
    ?_⟩
  rintro _ ⟨w, hwW, rfl⟩
  rcases hbij.surjOn hwW with ⟨y, hyU, hyw⟩
  refine ⟨e₀.symm y, ⟨y, hyU, rfl⟩, ?_⟩
  exact (e₁.eq_symm_apply (hFsource ⟨y, hyU, rfl⟩) (hWt hwW)).2 hyw

/-- Convert a chart-conjugated model `MapsTo`/`InjOn` patch into an open local
manifold-side patch.  This is the pointwise transport used after shrinking a
Picard patch to lie in the source and target chart domains. -/
theorem exists_open_nhds_mapsTo_injOn_of_openPartialHomeomorph_model_mapsTo_injOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (F : X → X) {x : X} {U W : Set Y}
    (hxsource : x ∈ e₀.source)
    (hUopen : IsOpen U) (hUt : U ⊆ e₀.target) (hxU : e₀ x ∈ U)
    (hWopen : IsOpen W) (hWt : W ⊆ e₁.target)
    (hFsource : MapsTo F (e₀.symm '' U) e₁.source)
    (hmaps : MapsTo (fun y : Y ↦ e₁ (F (e₀.symm y))) U W)
    (hinj : InjOn (fun y : Y ↦ e₁ (F (e₀.symm y))) U) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧ F x ∈ Wm ∧
        MapsTo F Um Wm ∧ InjOn F Um := by
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hFxWm : F x ∈ Wm := by
    exact ⟨e₁ (F x), by simpa [e₀.left_inv hxsource] using hmaps hxU,
      e₁.left_inv (hFsource hxUm)⟩
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    mapsTo_symm_image_of_openPartialHomeomorph_model_mapsTo
      e₀ e₁ F hFsource hmaps,
    injOn_symm_image_of_openPartialHomeomorph_model_injOn e₀ e₁ F hinj⟩

/-- Convert a chart-conjugated model `BijOn` patch into an open local
manifold-side bijection patch. -/
theorem exists_open_nhds_bijOn_of_openPartialHomeomorph_model_bijOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (F : X → X) {x : X} {U W : Set Y}
    (hxsource : x ∈ e₀.source)
    (hUopen : IsOpen U) (hUt : U ⊆ e₀.target) (hxU : e₀ x ∈ U)
    (hWopen : IsOpen W) (hWt : W ⊆ e₁.target)
    (hFsource : MapsTo F (e₀.symm '' U) e₁.source)
    (hbij : BijOn (fun y : Y ↦ e₁ (F (e₀.symm y))) U W) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧ F x ∈ Wm ∧ BijOn F Um Wm := by
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hFxWm : F x ∈ Wm := by
    exact ⟨e₁ (F x), by simpa [e₀.left_inv hxsource] using hbij.mapsTo hxU,
      e₁.left_inv (hFsource hxUm)⟩
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    bijOn_symm_image_of_openPartialHomeomorph_model_bijOn
      e₀ e₁ F hWt hFsource hbij⟩

/-- If a manifold-side map is defined by pulling a model map back through two
partial homeomorphism charts, model-space `MapsTo` transports directly. -/
theorem mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_mapsTo
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {U W : Set Y}
    (hUt : U ⊆ e₀.target)
    (hmaps : MapsTo G U W) :
    MapsTo (fun x : X ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) (e₁.symm '' W) := by
  rintro _ ⟨y, hyU, rfl⟩
  exact ⟨G y, hmaps hyU, by simpa [e₀.right_inv (hUt hyU)]⟩

/-- If a manifold-side map is defined by pulling a model map back through two
partial homeomorphism charts, model-space injectivity transports directly. -/
theorem injOn_symm_image_of_openPartialHomeomorph_lifted_model_injOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {U W : Set Y}
    (hUt : U ⊆ e₀.target) (hWt : W ⊆ e₁.target)
    (hmaps : MapsTo G U W) (hinj : InjOn G U) :
    InjOn (fun x : X ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) := by
  rintro _ ⟨y, hyU, rfl⟩ _ ⟨z, hzU, rfl⟩ hF
  congr 1
  apply hinj hyU hzU
  have hcong := congrArg e₁ hF
  simpa [e₀.right_inv (hUt hyU), e₀.right_inv (hUt hzU),
    e₁.right_inv (hWt (hmaps hyU)), e₁.right_inv (hWt (hmaps hzU))] using hcong

/-- If a manifold-side map is defined by pulling a model map back through two
partial homeomorphism charts, a model-space bijective patch transports
directly. -/
theorem bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {U W : Set Y}
    (hUt : U ⊆ e₀.target) (hWt : W ⊆ e₁.target)
    (hbij : BijOn G U W) :
    BijOn (fun x : X ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) (e₁.symm '' W) := by
  refine ⟨
    mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_mapsTo
      e₀ e₁ G hUt hbij.mapsTo,
    injOn_symm_image_of_openPartialHomeomorph_lifted_model_injOn
      e₀ e₁ G hUt hWt hbij.mapsTo hbij.injOn,
    ?_⟩
  rintro _ ⟨w, hwW, rfl⟩
  rcases hbij.surjOn hwW with ⟨y, hyU, hyw⟩
  refine ⟨e₀.symm y, ⟨y, hyU, rfl⟩, ?_⟩
  simpa [e₀.right_inv (hUt hyU), hyw]

/-- Open local `MapsTo`/`InjOn` patch for a map obtained by pulling a model map
back through source and target partial homeomorphism charts. -/
theorem exists_open_nhds_mapsTo_injOn_of_openPartialHomeomorph_lifted_model_mapsTo_injOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {x : X} {U W : Set Y}
    (hxsource : x ∈ e₀.source)
    (hUopen : IsOpen U) (hUt : U ⊆ e₀.target) (hxU : e₀ x ∈ U)
    (hWopen : IsOpen W) (hWt : W ⊆ e₁.target)
    (hmaps : MapsTo G U W) (hinj : InjOn G U) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧
        (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧
        MapsTo (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm ∧
          InjOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um := by
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hFxWm : (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm :=
    ⟨G (e₀ x), hmaps hxU, rfl⟩
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_mapsTo
      e₀ e₁ G hUt hmaps,
    injOn_symm_image_of_openPartialHomeomorph_lifted_model_injOn
      e₀ e₁ G hUt hWt hmaps hinj⟩

/-- Open local bijection patch for a map obtained by pulling a model map back
through source and target partial homeomorphism charts. -/
theorem exists_open_nhds_bijOn_of_openPartialHomeomorph_lifted_model_bijOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {x : X} {U W : Set Y}
    (hxsource : x ∈ e₀.source)
    (hUopen : IsOpen U) (hUt : U ⊆ e₀.target) (hxU : e₀ x ∈ U)
    (hWopen : IsOpen W) (hWt : W ⊆ e₁.target)
    (hbij : BijOn G U W) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧
        (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧
          BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm := by
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hFxWm : (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm :=
    ⟨G (e₀ x), hbij.mapsTo hxU, rfl⟩
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
      e₀ e₁ G hUt hWt hbij⟩

/-- Continuity of a model map on a chart patch transports to continuity of the
lifted manifold-side map on the corresponding source-chart patch. -/
theorem continuousOn_symm_image_of_openPartialHomeomorph_lifted_model
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G : Y → Y) {U W : Set Y}
    (hUt : U ⊆ e₀.target) (hWt : W ⊆ e₁.target)
    (hcont : ContinuousOn G U) (hmaps : MapsTo G U W) :
    ContinuousOn (fun x : X ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) := by
  have hsource : e₀.symm '' U ⊆ e₀.source := by
    rintro _ ⟨y, hyU, rfl⟩
    exact e₀.map_target (hUt hyU)
  have hcont_e₀ : ContinuousOn (fun x : X ↦ e₀ x) (e₀.symm '' U) :=
    e₀.continuousOn.mono hsource
  have hmaps_e₀ : MapsTo (fun x : X ↦ e₀ x) (e₀.symm '' U) U := by
    rintro _ ⟨y, hyU, rfl⟩
    simpa [e₀.right_inv (hUt hyU)] using hyU
  have hcont_G :
      ContinuousOn (fun x : X ↦ G (e₀ x)) (e₀.symm '' U) :=
    hcont.comp hcont_e₀ hmaps_e₀
  have hmaps_target : MapsTo (fun x : X ↦ G (e₀ x)) (e₀.symm '' U) e₁.target :=
    fun _ hx ↦ hWt (hmaps (hmaps_e₀ hx))
  exact e₁.continuousOn_symm.comp hcont_G hmaps_target

/-- Shrink a model open-partial-homeomorphism patch inside prescribed source
and target chart domains, then lift it to a manifold-side patch carrying both
continuity and bijectivity for the lifted map. -/
theorem exists_open_nhds_continuousOn_bijOn_of_lifted_openPartialHomeomorph_model
    (e₀ e₁ : OpenPartialHomeomorph X Y) {G : Y → Y}
    {φ : OpenPartialHomeomorph Y Y} (hφ : (φ : Y → Y) = G)
    {x : X} (hxsource : x ∈ e₀.source) (hxφ : e₀ x ∈ φ.source)
    {S T : Set Y}
    (hSopen : IsOpen S) (hS : S ⊆ e₀.target) (hxS : e₀ x ∈ S)
    (hTopen : IsOpen T) (hT : T ⊆ e₁.target) (hxT : G (e₀ x) ∈ T)
    (hcont : ContinuousOn G S) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧
        (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧
          ContinuousOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um ∧
            BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm := by
  rcases exists_open_nhds_bijOn_subset_of_openPartialHomeomorph
      (X := Y) (g := G) (x := e₀ x) (φ := φ) hφ hxφ
      hSopen hxS hTopen hxT with
    ⟨U, W, hUopen, hxU, hUS, hWopen, _hxW, hWT, hbij⟩
  have hUt : U ⊆ e₀.target := fun y hy ↦ hS (hUS hy)
  have hWt : W ⊆ e₁.target := fun y hy ↦ hT (hWT hy)
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hFxWm : (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm :=
    ⟨G (e₀ x), hbij.mapsTo hxU, rfl⟩
  have hcont_lift :
      ContinuousOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um :=
    continuousOn_symm_image_of_openPartialHomeomorph_lifted_model
      e₀ e₁ G hUt hWt (hcont.mono hUS) hbij.mapsTo
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    hcont_lift,
    bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
      e₀ e₁ G hUt hWt hbij⟩

/-- Shrink a lifted model inverse patch inside prescribed model chart domains
and record manifold-side source and target constraints for the resulting local
patch.  This is the overlap-ready form of
`exists_open_nhds_continuousOn_bijOn_of_lifted_openPartialHomeomorph_model`:
after the model source and target have been chosen so their chart pullbacks lie
in prescribed manifold sets, the produced neighborhoods inherit those
constraints together with continuity and bijectivity. -/
theorem exists_open_nhds_continuousOn_bijOn_subset_of_lifted_openPartialHomeomorph_model
    (e₀ e₁ : OpenPartialHomeomorph X Y) {G : Y → Y}
    {φ : OpenPartialHomeomorph Y Y} (hφ : (φ : Y → Y) = G)
    {x : X} (hxsource : x ∈ e₀.source) (hxφ : e₀ x ∈ φ.source)
    {S T : Set Y}
    (hSopen : IsOpen S) (hS : S ⊆ e₀.target) (hxS : e₀ x ∈ S)
    (hTopen : IsOpen T) (hT : T ⊆ e₁.target) (hxT : G (e₀ x) ∈ T)
    (hcont : ContinuousOn G S)
    {Sx Tx : Set X}
    (hSx : e₀.symm '' S ⊆ Sx) (hTx : e₁.symm '' T ⊆ Tx) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ Um ⊆ Sx ∧
        IsOpen Wm ∧
          (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧ Wm ⊆ Tx ∧
            ContinuousOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um ∧
              BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm := by
  rcases exists_open_nhds_bijOn_subset_of_openPartialHomeomorph
      (X := Y) (g := G) (x := e₀ x) (φ := φ) hφ hxφ
      hSopen hxS hTopen hxT with
    ⟨U, W, hUopen, hxU, hUS, hWopen, _hxW, hWT, hbij⟩
  have hUt : U ⊆ e₀.target := fun y hy ↦ hS (hUS hy)
  have hWt : W ⊆ e₁.target := fun y hy ↦ hT (hWT hy)
  let Um : Set X := e₀.symm '' U
  let Wm : Set X := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hUmSx : Um ⊆ Sx := by
    rintro _ ⟨y, hyU, rfl⟩
    exact hSx ⟨y, hUS hyU, rfl⟩
  have hFxWm : (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm :=
    ⟨G (e₀ x), hbij.mapsTo hxU, rfl⟩
  have hWmTx : Wm ⊆ Tx := by
    rintro _ ⟨y, hyW, rfl⟩
    exact hTx ⟨y, hWT hyW, rfl⟩
  have hcont_lift :
      ContinuousOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um :=
    continuousOn_symm_image_of_openPartialHomeomorph_lifted_model
      e₀ e₁ G hUt hWt (hcont.mono hUS) hbij.mapsTo
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    hUmSx,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    hWmTx,
    hcont_lift,
    bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
      e₀ e₁ G hUt hWt hbij⟩

/-- A chart-coordinate equality on a visible patch gives equality of the
underlying manifold maps once both sides land in the chart source.  This is the
topological equality transport used by chart-gluing arguments after model
uniqueness has identified local flows in a common target chart. -/
theorem eqOn_of_openPartialHomeomorph_coord_eqOn
    (e : OpenPartialHomeomorph X Y) {F G : X → X} {S : Set X}
    (hFsource : MapsTo F S e.source) (hGsource : MapsTo G S e.source)
    (hcoord : EqOn (fun x : X ↦ e (F x)) (fun x : X ↦ e (G x)) S) :
    EqOn F G S := by
  intro x hx
  exact e.injOn (hFsource hx) (hGsource hx) (hcoord hx)

/-- If two chart-lifted model maps have equal target coordinates in the same
target chart on a manifold patch, then the lifted manifold maps agree there. -/
theorem eqOn_lifted_models_same_target_of_model_eqOn
    (e₀ f₀ e₁ : OpenPartialHomeomorph X Y) (G₀ G₁ : Y → Y) {S : Set X}
    (hcoord : EqOn (fun x : X ↦ G₀ (e₀ x)) (fun x : X ↦ G₁ (f₀ x)) S) :
    EqOn (fun x : X ↦ e₁.symm (G₀ (e₀ x)))
      (fun x : X ↦ e₁.symm (G₁ (f₀ x))) S := by
  intro x hx
  exact congrArg e₁.symm (hcoord hx)

/-- Model-space equality on a source chart patch transports directly to
manifold-side equality for the two corresponding lifted maps. -/
theorem eqOn_symm_image_of_openPartialHomeomorph_lifted_model_eqOn
    (e₀ e₁ : OpenPartialHomeomorph X Y) (G₀ G₁ : Y → Y) {U : Set Y}
    (hUt : U ⊆ e₀.target) (heq : EqOn G₀ G₁ U) :
    EqOn (fun x : X ↦ e₁.symm (G₀ (e₀ x)))
      (fun x : X ↦ e₁.symm (G₁ (e₀ x))) (e₀.symm '' U) := by
  rintro _ ⟨y, hyU, rfl⟩
  simpa [e₀.right_inv (hUt hyU)] using congrArg e₁.symm (heq hyU)

/-- Chart-lifted model maps through different target charts agree on a
manifold patch once their images lie in a common target chart and their common
target-chart coordinates agree there. -/
theorem eqOn_lifted_models_of_common_target_chart_eqOn
    (e₀ e₁ f₀ f₁ c : OpenPartialHomeomorph X Y) (G₀ G₁ : Y → Y) {S : Set X}
    (h₀source : MapsTo (fun x : X ↦ e₁.symm (G₀ (e₀ x))) S c.source)
    (h₁source : MapsTo (fun x : X ↦ f₁.symm (G₁ (f₀ x))) S c.source)
    (hcoord : EqOn
      (fun x : X ↦ c (e₁.symm (G₀ (e₀ x))))
      (fun x : X ↦ c (f₁.symm (G₁ (f₀ x)))) S) :
    EqOn (fun x : X ↦ e₁.symm (G₀ (e₀ x)))
      (fun x : X ↦ f₁.symm (G₁ (f₀ x))) S :=
  eqOn_of_openPartialHomeomorph_coord_eqOn c h₀source h₁source hcoord

/-- Direct chart lift of a model open-partial-homeomorphism inverse patch:
shrink the model patch to the source and target chart targets, then transport
the resulting bijective patch through the two charts. -/
theorem exists_open_nhds_bijOn_of_lifted_openPartialHomeomorph_model
    (e₀ e₁ : OpenPartialHomeomorph X Y) {G : Y → Y}
    {φ : OpenPartialHomeomorph Y Y} (hφ : (φ : Y → Y) = G)
    {x : X} (hxsource : x ∈ e₀.source) (hxφ : e₀ x ∈ φ.source)
    (hGtarget : G (e₀ x) ∈ e₁.target) :
    ∃ Um Wm : Set X,
      IsOpen Um ∧ x ∈ Um ∧ IsOpen Wm ∧
        (fun z : X ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧
          BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm := by
  rcases exists_open_nhds_bijOn_subset_of_openPartialHomeomorph
      (X := Y) (g := G) (x := e₀ x) (φ := φ) hφ hxφ
      e₀.open_target (e₀.map_source hxsource) e₁.open_target hGtarget with
    ⟨U, W, hUopen, hxU, hUt, hWopen, _hxW, hWt, hbij⟩
  exact exists_open_nhds_bijOn_of_openPartialHomeomorph_lifted_model_bijOn
    e₀ e₁ G hxsource hUopen hUt hxU hWopen hWt hbij

end OpenPartialHomeomorphTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- A manifold self-map is `C^n` on a domain if every point of the domain has
an open neighborhood on which it agrees with a `C^n` local readout.  This is
the regularity-gluing analogue of
`continuousOn_of_locally_eqOn_open_continuousOn`, aimed at the eventual `C³`
time-slice construction. -/
theorem contMDiffOn_of_locally_eqOn_open_contMDiffOn
    {n : WithTop ℕ∞} {F : M → M} {s : Set M}
    (h : ∀ x ∈ s, ∃ U : Set M, ∃ G : M → M,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I I n G U ∧ EqOn F G (s ∩ U)) :
    ContMDiffOn I I n F s := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x hx
  rcases h x hx with ⟨U, G, hUopen, hxU, hG, hEq⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  exact (hG.mono inter_subset_right).congr fun y hy ↦ hEq hy

/-- Indexed open-cover version of
`contMDiffOn_of_locally_eqOn_open_contMDiffOn` for manifold self-maps. -/
theorem contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
    {ι : Type*} {n : WithTop ℕ∞} {F : M → M} {G : ι → M → M}
    {s : Set M} {U : ι → Set M}
    (hcover : s ⊆ ⋃ i, U i)
    (hUopen : ∀ i, IsOpen (U i))
    (hcont : ∀ i, ContMDiffOn I I n (G i) (U i))
    (heq : ∀ i, EqOn F (G i) (s ∩ U i)) :
    ContMDiffOn I I n F s :=
  contMDiffOn_of_locally_eqOn_open_contMDiffOn fun x hx ↦ by
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxU⟩
    exact ⟨U i, G i, hUopen i, hxU, hcont i, heq i⟩

/-- A within-time continuous manifold curve is eventually in any preferred
chart source that contains its value at the base time. -/
theorem preimage_extChartAt_source_mem_nhdsWithin_of_continuousWithinAt
    {s : Set ℝ} {γ : ℝ → M} {t : ℝ} {p : M}
    (hγ : ContinuousWithinAt γ s t)
    (hsrc : γ t ∈ (extChartAt I p).source) :
    γ ⁻¹' (extChartAt I p).source ∈ 𝓝[s] t :=
  hγ.preimage_mem_nhdsWithin ((isOpen_extChartAt_source (I := I) p).mem_nhds hsrc)

/-- A within-time continuous manifold curve is eventually in the preferred
chart source centered at its value at the base time. -/
theorem preimage_extChartAt_source_self_mem_nhdsWithin_of_continuousWithinAt
    {s : Set ℝ} {γ : ℝ → M} {t : ℝ}
    (hγ : ContinuousWithinAt γ s t) :
    γ ⁻¹' (extChartAt I (γ t)).source ∈ 𝓝[s] t :=
  preimage_extChartAt_source_mem_nhdsWithin_of_continuousWithinAt
    (I := I) (M := M) hγ (mem_extChartAt_source (I := I) (γ t))

/-- A concrete `C^3` diffeomorphism flow for a time-dependent vector field on a
time set, anchored at a base time.  This is the raw object expected from the
future manifold ODE-flow existence theorem. -/
structure Diffeomorph3GaugeFlowOn
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps3 t₀
  satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
    maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s

namespace Diffeomorph3GaugeFlowOn

/-- Extract the pointwise manifold derivative statement from a raw `C^3`
gauge-flow witness on its time set. -/
theorem hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  G.satisfies.hasMFDerivWithinAt ht x

/-- Within the raw time set, the pointwise derivative readout can be rewritten
to any vector field that agrees with the original one along the flow in the
relative filter at the time. -/
theorem hasMFDerivWithinAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) := by
  have hXYt_all : ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x) :=
    show t ∈ {τ : ℝ | ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)} from
      mem_of_mem_nhdsWithin ht hXY
  have hXYt : X t (G.maps3 t x) = Y t (G.maps3 t x) :=
    hXYt_all x
  simpa [hXYt] using G.hasMFDerivWithinAt ht x

/-- Raw gauge-flow curves have the expected within-time-set derivative in the
preferred chart centered at their time-`t` value. -/
theorem hasDerivWithinAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) s t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivWithinAt ht x) (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- Raw gauge-flow curves have the expected within-time-set derivative in any
preferred chart whose source contains the time-`t` image.  This is the
fixed-chart form used when passing a manifold flow to chartwise model ODE
hypotheses on a prescribed cover. -/
theorem hasDerivWithinAt_extChartAt_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) s t := by
  have hsrc : (G.maps3 t) x ∈ (chartAt H p).source := by
    simpa [extChartAt_source] using hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivWithinAt ht x) (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- Raw gauge-flow curves have the expected within-time-set derivative in the
preferred chart, with the velocity rewritten by relative-filter agreement of
vector fields along the flow. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) s t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivWithinAt_congr_vectorField ht hXY x)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- Fixed-chart version of
`Diffeomorph3GaugeFlowOn.hasDerivWithinAt_extChartAt_eval_congr_vectorField`. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (p x : M) (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) s t := by
  have hXYt_all : ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x) :=
    show t ∈ {τ : ℝ | ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)} from
      mem_of_mem_nhdsWithin ht hXY
  have hXYt : X t ((G.maps3 t) x) = Y t ((G.maps3 t) x) := hXYt_all x
  simpa [hXYt] using
    G.hasDerivWithinAt_extChartAt_eval_of_mem_source ht p x hsrc_ext

/-- A raw gauge-flow curve has the expected within-time-set derivative in the preferred chart
centered at its time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) s t := by
  have h := G.hasDerivWithinAt_extChartAt_eval ht x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- A raw gauge-flow curve has the centered within-time-set preferred-chart
derivative, with the velocity rewritten by relative-filter agreement of vector
fields along the flow. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) s t := by
  have h := G.hasDerivWithinAt_extChartAt_eval_congr_vectorField ht hXY x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := Y t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- A raw gauge-flow witness is continuous within its time set along every base
point. -/
theorem continuousWithinAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ (G.maps3 τ) x) s t :=
  (G.hasMFDerivWithinAt ht x).continuousWithinAt

/-- A raw gauge-flow witness is continuous on its time set along every base
point. -/
theorem continuousOn_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ (G.maps3 τ) x) s :=
  fun _t ht ↦ G.continuousWithinAt_eval ht x

/-- Raw gauge-flow curves are continuous within the time set in the preferred
chart centered at the base time value. -/
theorem continuousWithinAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) s t :=
  (G.hasDerivWithinAt_extChartAt_eval ht x).continuousWithinAt

/-- Fixed-chart continuity readout for a raw gauge-flow curve, assuming the
time-`t` image lies in that chart source. -/
theorem continuousWithinAt_extChartAt_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x)) s t :=
  (G.hasDerivWithinAt_extChartAt_eval_of_mem_source ht p x hsrc_ext).continuousWithinAt

/-- Within the raw gauge-flow time set, the image of a fixed base point
eventually remains in the preferred tangent-bundle trivialization centered at
its time-`t` image. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝[s] t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousWithinAt_eval ht x).preimage_mem_nhdsWithin
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- Within the raw gauge-flow time set, the image of a fixed base point
eventually remains in the preferred chart source centered at its time-`t` image. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝[s] t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousWithinAt_eval ht x).preimage_mem_nhdsWithin
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

/-- Within the raw gauge-flow time set, the image of a fixed base point
eventually remains in any preferred chart source containing its time-`t` image. -/
theorem eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝[s] t, (G.maps3 τ) x ∈ (extChartAt I p).source :=
  (G.continuousWithinAt_eval ht x).preimage_mem_nhdsWithin
    ((isOpen_extChartAt_source (I := I) p).mem_nhds hsrc_ext)

/-- A raw gauge-flow witness on a closed Picard interval supplies an ordinary
manifold derivative at interior times. -/
theorem hasMFDerivAt_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  (G.satisfies.satisfiesAt (Icc_mem_nhds ht.1 ht.2)).hasMFDerivAt x

/-- Interior raw gauge-flow curves have the expected derivative in the preferred
chart centered at their time-`t` value. -/
theorem hasDerivAt_extChartAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt_of_mem_Ioo ht x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- Interior raw gauge-flow curves have the expected derivative in the preferred chart centered at
the time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval_of_mem_Ioo ht x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- A raw gauge-flow witness on a closed Picard interval is continuous at
interior times along every base point. -/
theorem continuousAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (G.maps3 τ) x) t :=
  (G.hasMFDerivAt_of_mem_Ioo ht x).continuousAt

/-- A closed-interval raw gauge-flow witness is continuous on the open Picard
interior along every base point. -/
theorem continuousOn_eval_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (x : M) :
    ContinuousOn (fun τ : ℝ ↦ (G.maps3 τ) x) (Ioo tmin tmax) :=
  fun _t ht ↦ (G.continuousAt_eval_of_mem_Ioo ht x).continuousWithinAt

/-- Interior raw gauge-flow curves are continuous in the preferred chart centered
at the time-`t` value. -/
theorem continuousAt_extChartAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) t :=
  (G.hasDerivAt_extChartAt_eval_of_mem_Ioo ht x).continuousAt

/-- Interior times of a closed-interval raw gauge flow have the tangent-chart
membership needed for coordinate pullback formulas. -/
theorem eventually_mem_trivializationAt_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousAt_eval_of_mem_Ioo ht x).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- Interior times of a closed-interval raw gauge flow have the preferred-chart
source membership needed for centered chart ODE formulas. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousAt_eval_of_mem_Ioo ht x).preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

/-- A raw gauge-flow witness on a time set gives a local-at-time gauge-flow
statement whenever the time set is a neighborhood of that time. -/
theorem satisfiesAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) :
    SatisfiesGaugeFlowAt (I := I) (M := M)
      G.maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X t :=
  G.satisfies.satisfiesAt hs

/-- Extract the unrestricted manifold derivative statement from a raw gauge-flow
witness on a neighborhood of the time. -/
theorem hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  (G.satisfiesAt hs).hasMFDerivAt x

/-- At a neighborhood time, a raw gauge-flow witness also satisfies any vector field that agrees
with the original one along the flow in a neighborhood of that time. -/
theorem satisfiesAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    SatisfiesGaugeFlowAt (I := I) (M := M)
      G.maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily Y t :=
  (G.satisfiesAt hs).congr_vectorField hXY

/-- At a neighborhood time, the pointwise derivative readout can be rewritten to any vector field
that agrees with the original one along the flow near that time. -/
theorem hasMFDerivAt_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) :=
  (G.satisfiesAt_congr_vectorField hs hXY).hasMFDerivAt x

/-- At a neighborhood time, the preferred-chart derivative readout can be
rewritten to any vector field that agrees with the original one along the flow
near that time. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt_congr_vectorField hs hXY x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- At a neighborhood time, the centered preferred-chart derivative readout can
be rewritten to any vector field that agrees with the original one along the
flow near that time. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval_congr_vectorField hs hXY x
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := Y t ((G.maps3 t) x)) hsrc_ext] at h
  exact h

/-- A closed-interval raw gauge-flow witness gives an ordinary interior derivative for any vector
field that agrees with the original one along the flow near the interior time. -/
theorem hasMFDerivAt_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) :=
  G.hasMFDerivAt_congr_vectorField (Icc_mem_nhds ht.1 ht.2) hXY x

/-- A closed-interval raw gauge-flow witness gives the ordinary interior
preferred-chart derivative for any vector field that agrees with the original
one along the flow near the interior time. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField
    (Icc_mem_nhds ht.1 ht.2) hXY x

/-- A closed-interval raw gauge-flow witness gives the ordinary interior
centered preferred-chart derivative for any vector field that agrees with the
original one along the flow near the interior time. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_mem_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self_congr_vectorField
    (Icc_mem_nhds ht.1 ht.2) hXY x

/-- At any time where the raw time set is a neighborhood, a raw gauge-flow curve
has the expected derivative in the preferred chart centered at its time-`t`
value. -/
theorem hasDerivAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t := by
  have hsrc_ext : (G.maps3 t) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
    mem_extChartAt_source ((G.maps3 t) x)
  have hsrc : (G.maps3 t) x ∈ (chartAt H ((G.maps3 t) x)).source :=
    extChartAt_source I ((G.maps3 t) x) ▸ hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt hs x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- At any time where the raw time set is a neighborhood, a raw gauge-flow
curve has the expected derivative in any preferred chart whose source contains
the time-`t` image. -/
theorem hasDerivAt_extChartAt_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t := by
  have hsrc : (G.maps3 t) x ∈ (chartAt H p).source := by
    simpa [extChartAt_source] using hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt hs x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- Fixed-chart version of
`Diffeomorph3GaugeFlowOn.hasDerivAt_extChartAt_eval_congr_vectorField`. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (p x : M) (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t := by
  have hsrc : (G.maps3 t) x ∈ (chartAt H p).source := by
    simpa [extChartAt_source] using hsrc_ext
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc)
    (G.hasMFDerivAt_congr_vectorField hs hXY x)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- At neighborhood-times, raw gauge-flow curves have the expected derivative in the preferred chart
centered at the time-`t` value, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) t := by
  have h := G.hasDerivAt_extChartAt_eval hs x
  rw [tangentCoordChange_self (I := I)
    (x := (G.maps3 t) x) (z := (G.maps3 t) x)
    (v := X t ((G.maps3 t) x)) (mem_extChartAt_source ((G.maps3 t) x))] at h
  exact h

/-- At neighborhood-times, raw gauge-flow curves are continuous in the preferred
chart centered at the time-`t` value. -/
theorem continuousAt_extChartAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) t :=
  (G.hasDerivAt_extChartAt_eval hs x).continuousAt

/-- Raw gauge-flow curves are continuous at neighborhood-times in any preferred
chart whose source contains the time-`t` image. -/
theorem continuousAt_extChartAt_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x)) t :=
  (G.hasDerivAt_extChartAt_eval_of_mem_source hs p x hsrc_ext).continuousAt

/-- A raw gauge-flow witness is continuous in time along every base point at
times where its time set is a neighborhood. -/
theorem continuousAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (G.maps3 τ) x) t :=
  (G.hasMFDerivAt hs x).continuousAt

/-- Near any time where the raw gauge-flow equation holds on a neighborhood,
the image of a fixed base point remains in the preferred tangent-bundle
trivialization centered at its time-`t` image. -/
theorem eventually_mem_trivializationAt_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  (G.continuousAt_eval hs x).preimage_mem_nhds
    ((trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' ((G.maps3 t) x)))

/-- Near any time where the raw gauge-flow equation holds on a neighborhood, the
image of a fixed base point remains in the preferred chart source centered at
its time-`t` image. -/
theorem eventually_mem_extChartAt_source_eval
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  (G.continuousAt_eval hs x).preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := I) ((G.maps3 t) x))

/-- Near any time where the raw gauge-flow equation holds on a neighborhood,
the image of a fixed base point remains in any preferred chart source
containing its time-`t` image. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (extChartAt I p).source :=
  (G.continuousAt_eval hs x).preimage_mem_nhds
    ((isOpen_extChartAt_source (I := I) p).mem_nhds hsrc_ext)

/-- A raw intrinsic DeTurck gauge-flow witness supplies fixed-chart intrinsic
ODE data on its time set, for any chart-center choice whose sources contain the
corresponding flow images. -/
theorem toIntrinsicFixedChartDerivativeOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀)
    (hmem : ∀ t ∈ s, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) G.maps3 g background chartCenter s := by
  intro t ht x
  exact ⟨hmem t ht x,
    by
      simpa using
        G.eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
          ht (chartCenter t x) x (hmem t ht x),
    by
      simpa using
        G.hasDerivWithinAt_extChartAt_eval_of_mem_source
          ht (chartCenter t x) x (hmem t ht x)⟩

/-- A raw gauge-flow witness for a model vector field supplies fixed-chart
intrinsic DeTurck ODE data once that vector field agrees with the intrinsic
DeTurck field along the flow in the relative time-set filter. -/
theorem toIntrinsicFixedChartDerivativeOn_congr_vectorField_nhdsWithin
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀)
    (hmem : ∀ t ∈ s, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ (G.maps3 τ x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ (G.maps3 τ x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) G.maps3 g background chartCenter s := by
  intro t ht x
  exact ⟨hmem t ht x,
    by
      simpa using
        G.eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
          ht (chartCenter t x) x (hmem t ht x),
    by
      simpa using
        G.hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
          ht (hY t ht) (chartCenter t x) x (hmem t ht x)⟩

/-- A raw intrinsic DeTurck gauge-flow witness supplies ordinary fixed-chart
intrinsic ODE data on any time subset where its raw time set is a neighborhood
of each time. -/
theorem toIntrinsicFixedChartDerivativeAtOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s u : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ u → s ∈ 𝓝 t)
    (hmem : ∀ t ∈ u, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) G.maps3 g background chartCenter u := by
  intro t ht x
  exact ⟨hmem t ht x,
    by
      simpa using
        G.eventually_mem_extChartAt_source_eval_of_mem_source
          (hs ht) (chartCenter t x) x (hmem t ht x),
    by
      simpa using
        G.hasDerivAt_extChartAt_eval_of_mem_source
          (hs ht) (chartCenter t x) x (hmem t ht x)⟩

/-- Ordinary fixed-chart intrinsic ODE data extracted from a raw gauge-flow
whose vector field agrees with the intrinsic DeTurck field along the flow in
the relative raw time-set filters. -/
theorem toIntrinsicFixedChartDerivativeAtOn_congr_vectorField_nhdsWithin
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s u : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ u → s ∈ 𝓝 t)
    (hmem : ∀ t ∈ u, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hY : ∀ t ∈ u, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ (G.maps3 τ x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ (G.maps3 τ x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) G.maps3 g background chartCenter u := by
  intro t ht x
  have hY_nhds : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      Y τ (G.maps3 τ x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ (G.maps3 τ x) := by
    simpa [nhdsWithin_eq_nhds.2 (hs ht)] using hY t ht
  exact ⟨hmem t ht x,
    by
      simpa using
        G.eventually_mem_extChartAt_source_eval_of_mem_source
          (hs ht) (chartCenter t x) x (hmem t ht x),
    by
      simpa using
        G.hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source
          (hs ht) hY_nhds (chartCenter t x) x (hmem t ht x)⟩

/-- Raw open-Picard time sets are neighborhoods of each of their times when the
abstract time set has been identified with `Ioo tmin tmax`. -/
theorem timeSet_mem_nhds_of_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax) :
    ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t := by
  intro t ht
  have ht' : t ∈ Ioo tmin tmax := by
    simpa [htimeSet] using ht
  simpa [htimeSet] using (isOpen_Ioo.mem_nhds ht')

/-- Raw open-Picard local-at-time gauge-flow readout without a separate
neighborhood-of-time hypothesis. -/
theorem satisfiesAt_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax) (ht : t ∈ s) :
    SatisfiesGaugeFlowAt (I := I) (M := M)
      G.maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X t :=
  G.satisfiesAt (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht)

/-- Raw open-Picard pointwise manifold derivative readout without a separate
neighborhood-of-time hypothesis. -/
theorem hasMFDerivAt_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G.maps3 t x))) :=
  G.hasMFDerivAt (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard preferred-chart derivative readout without a separate
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard fixed-chart derivative readout without a separate
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (X t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_of_mem_source
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) p x hsrc_ext

/-- Raw open-Picard pointwise manifold derivative readout rewritten to a
neighborhood-equal vector field, without a separate neighborhood-of-time
hypothesis. -/
theorem hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (G.maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (G.maps3 t x))) :=
  G.hasMFDerivAt_congr_vectorField
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) hXY x

/-- Raw open-Picard preferred-chart derivative readout rewritten to a
neighborhood-equal vector field, without a separate neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) hXY x

/-- Raw open-Picard fixed-chart derivative readout rewritten to a
neighborhood-equal vector field, without a separate neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source_of_timeSet_eq_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (p x : M) (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x))
      (tangentCoordChange I ((G.maps3 t) x) p ((G.maps3 t) x)
        (Y t ((G.maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) hXY p x hsrc_ext

/-- Raw open-Picard centered preferred-chart derivative readout without a
separate neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (X t ((G.maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard centered preferred-chart derivative readout rewritten to a
neighborhood-equal vector field, without a separate neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M, X τ (G.maps3 τ x) = Y τ (G.maps3 τ x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
      (Y t ((G.maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self_congr_vectorField
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) hXY x

/-- Raw open-Picard continuity of gauge-flow curves in preferred chart
coordinates, without a separate neighborhood-of-time hypothesis. -/
theorem continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)) t :=
  G.continuousAt_extChartAt_eval
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard fixed-chart continuity readout without a separate
neighborhood-of-time hypothesis. -/
theorem continuousAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I p) ((G.maps3 τ) x)) t :=
  G.continuousAt_extChartAt_eval_of_mem_source
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) p x hsrc_ext

/-- Raw open-Picard continuity of gauge-flow curves, without a separate
neighborhood-of-time hypothesis. -/
theorem continuousAt_eval_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (G.maps3 τ) x) t :=
  G.continuousAt_eval (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard tangent-trivialization control, without a separate
neighborhood-of-time hypothesis. -/
theorem eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((G.maps3 t) x)).baseSet :=
  G.eventually_mem_trivializationAt_eval
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard chart-source control, without a separate neighborhood-of-time
hypothesis. -/
theorem eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      (G.maps3 τ) x ∈ (extChartAt I ((G.maps3 t) x)).source :=
  G.eventually_mem_extChartAt_source_eval
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) x

/-- Raw open-Picard fixed-chart source control without a separate
neighborhood-of-time hypothesis. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_source_of_timeSet_eq_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (ht : t ∈ s) (p x : M)
    (hsrc_ext : (G.maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝 t, (G.maps3 τ) x ∈ (extChartAt I p).source :=
  G.eventually_mem_extChartAt_source_eval_of_mem_source
    (G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet ht) p x hsrc_ext

/-- Raw open-Picard intrinsic gauge flows supply ordinary fixed-chart ODE data
on any subset of their open time set. -/
theorem toIntrinsicFixedChartDerivativeAtOn_of_timeSet_eq_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s u : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (hu : u ⊆ s)
    (hmem : ∀ t ∈ u, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) G.maps3 g background chartCenter u :=
  G.toIntrinsicFixedChartDerivativeAtOn
    (fun {t} ht ↦ G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet (hu ht))
    hmem

/-- Raw open-Picard model-vector-field gauge flows supply ordinary fixed-chart
intrinsic ODE data on any subset of their open time set once the model field
agrees with the intrinsic DeTurck field along the flow. -/
theorem toIntrinsicFixedChartDerivativeAtOn_congr_vectorField_nhdsWithin_of_timeSet_eq_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s u : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀)
    (tmin tmax : ℝ) (htimeSet : s = Ioo tmin tmax)
    (hu : u ⊆ s)
    (hmem : ∀ t ∈ u, ∀ x : M,
      (G.maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hY : ∀ t ∈ u, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ (G.maps3 τ x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ (G.maps3 τ x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) G.maps3 g background chartCenter u :=
  G.toIntrinsicFixedChartDerivativeAtOn_congr_vectorField_nhdsWithin
    (fun {t} ht ↦ G.timeSet_mem_nhds_of_eq_Ioo tmin tmax htimeSet (hu ht))
    hmem hY

/-- Package a geometric `SatisfiesGaugeFlowOn` statement as a raw `C^3`
diffeomorphism gauge-flow witness. -/
def of_satisfiesGaugeFlowOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
      maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := maps3
  anchored := anchored
  satisfies := satisfies

/-- Package a geometric gauge-flow statement as proof-level raw `C^3`
diffeomorphism gauge-flow existence. -/
theorem nonempty_of_satisfiesGaugeFlowOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (satisfies : SatisfiesGaugeFlowOn (I := I) (M := M)
      maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily X s) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_satisfiesGaugeFlowOn maps3 anchored satisfies⟩

/-- Package autonomous Mathlib integral-curve data for a `C³` diffeomorphism
family as a raw gauge-flow witness for the constant-in-time vector field. -/
def of_autonomousIntegralCurves
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ x : M,
      IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (maps3 t) x) X s) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀ :=
  of_satisfiesGaugeFlowOn maps3 anchored (by
    intro x t ht
    simpa using hcurves x t ht)

/-- Proof-level raw `C³` gauge-flow existence from autonomous Mathlib
integral-curve data for a `C³` diffeomorphism family. -/
theorem nonempty_of_autonomousIntegralCurves
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ x : M,
      IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (maps3 t) x) X s) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀) :=
  ⟨of_autonomousIntegralCurves maps3 anchored hcurves⟩

/-- Package autonomous Mathlib local integral-curve data at every time in `s`
for a `C³` diffeomorphism family as a raw gauge-flow witness for the
constant-in-time vector field. -/
def of_autonomousIntegralCurveAt
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ t ∈ s, ∀ x : M,
      IsMIntegralCurveAt (I := I) (fun τ : ℝ ↦ (maps3 τ) x) X t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀ :=
  of_satisfiesGaugeFlowOn maps3 anchored (by
    intro x t ht
    exact (hcurves t ht x).hasMFDerivAt.hasMFDerivWithinAt)

/-- Proof-level raw `C³` gauge-flow existence from autonomous Mathlib local
integral-curve data at every time in `s`. -/
theorem nonempty_of_autonomousIntegralCurveAt
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcurves : ∀ t ∈ s, ∀ x : M,
      IsMIntegralCurveAt (I := I) (fun τ : ℝ ↦ (maps3 τ) x) X t) :
    Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀) :=
  ⟨of_autonomousIntegralCurveAt maps3 anchored hcurves⟩

/-- Extract Mathlib autonomous integral-curve data from a raw gauge-flow
witness for a constant-in-time vector field. -/
theorem autonomousIntegralCurveOn
    {X : Π x : M, TangentSpace I x}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s t₀)
    (x : M) :
    IsMIntegralCurveOn (I := I) (fun t : ℝ ↦ (G.maps3 t) x) X s := by
  intro t ht
  simpa using G.satisfies x t ht

/-- Two anchored raw `C³` autonomous gauge flows for the same `C¹` vector field
agree on the open interval where both solve the ODE. -/
theorem eqOn_eval_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Ioo tmin tmax) := by
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) (t₀ := t₀) ht₀ hX
    (G₁.autonomousIntegralCurveOn x)
    (G₂.autonomousIntegralCurveOn x) ?_
  have h₁ :
      (G₁.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
  have h₂ :
      (G₂.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
  rw [h₁, h₂]

/-- Pointwise form of autonomous raw gauge-flow uniqueness on an open interval. -/
theorem eval_eq_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Ioo_boundaryless G₂ ht₀ hX x ht

/-- Time-slice diffeomorphism form of autonomous raw gauge-flow uniqueness on
an open interval. -/
theorem eqOn_maps3_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Ioo tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eval_eq_of_autonomous_Ioo_boundaryless G₂ ht₀ hX ht x

/-- Pointwise time-slice diffeomorphism form of autonomous raw gauge-flow
uniqueness on an open interval. -/
theorem maps3_eq_of_autonomous_Ioo_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Ioo tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless G₂ ht₀ hX ht

/-- Two anchored raw `C³` autonomous gauge flows for the same `C¹` vector field
agree on a closed interval once the anchor lies in its interior.  The endpoint
identification is the continuous extension of Mathlib's boundaryless
autonomous uniqueness theorem on the open interval. -/
theorem eqOn_eval_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Icc tmin tmax) := by
  have hIoo :
      EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
        (Ioo tmin tmax) := by
    refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (I := I) (t₀ := t₀) ht₀ hX
      ((G₁.autonomousIntegralCurveOn x).mono (fun _t ht ↦ Ioo_subset_Icc_self ht))
      ((G₂.autonomousIntegralCurveOn x).mono (fun _t ht ↦ Ioo_subset_Icc_self ht)) ?_
    have h₁ :
        (G₁.maps3 t₀) x = x :=
      SmoothSelfDiffeomorph3Family.AnchoredAt.apply
        (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
    have h₂ :
        (G₂.maps3 t₀) x = x :=
      SmoothSelfDiffeomorph3Family.AnchoredAt.apply
        (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
    rw [h₁, h₂]
  have hne : tmin ≠ tmax := ne_of_lt (lt_trans ht₀.1 ht₀.2)
  refine Set.EqOn.of_subset_closure hIoo
    (G₁.continuousOn_eval x) (G₂.continuousOn_eval x)
    (fun _t ht ↦ Ioo_subset_Icc_self ht) ?_
  intro t ht
  rw [closure_Ioo hne]
  exact ht

/-- Pointwise form of autonomous raw gauge-flow uniqueness on a closed interval
with the anchor in the interior. -/
theorem eval_eq_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Icc_boundaryless G₂ ht₀ hX x ht

/-- Time-slice diffeomorphism form of autonomous raw gauge-flow uniqueness on a
closed interval with the anchor in the interior. -/
theorem eqOn_maps3_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Icc tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eval_eq_of_autonomous_Icc_boundaryless G₂ ht₀ hX ht x

/-- Pointwise time-slice diffeomorphism form of autonomous raw gauge-flow
uniqueness on a closed interval with the anchor in the interior. -/
theorem maps3_eq_of_autonomous_Icc_boundaryless
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin tmax t₀ t : ℝ}
    (G₁ G₂ :
      Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) (Icc tmin tmax) t₀)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Icc_boundaryless G₂ ht₀ hX ht

/-- Common-open-subinterval form of autonomous raw gauge-flow uniqueness.  The
two raw flows may live on different ambient time sets, as long as both contain
the visible open Picard interval. -/
theorem eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Ioo tmin tmax) := by
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) (t₀ := t₀) ht₀ hX
    ((G₁.autonomousIntegralCurveOn x).mono h₁)
    ((G₂.autonomousIntegralCurveOn x).mono h₂) ?_
  have hG₁ :
      (G₁.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₁.maps3) G₁.anchored x
  have hG₂ :
      (G₂.maps3 t₀) x = x :=
    SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (I := I) (M := M) (Φ := G₂.maps3) G₂.anchored x
  rw [hG₁, hG₂]

/-- Common-open-subinterval time-slice diffeomorphism form of autonomous raw
gauge-flow uniqueness. -/
theorem eqOn_maps3_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Ioo tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-open-subinterval form of autonomous raw gauge-flow
uniqueness. -/
theorem eval_eq_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-open-subinterval time-slice diffeomorphism form of
autonomous raw gauge-flow uniqueness. -/
theorem maps3_eq_of_autonomous_Ioo_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Ioo tmin tmax ⊆ s₁)
    (h₂ : Ioo tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX ht

/-- Common-closed-subinterval form of autonomous raw gauge-flow uniqueness.  The
endpoint equality is obtained by extending the common open-subinterval equality
using the continuity of both ambient raw flows on the shared closed interval. -/
theorem eqOn_eval_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Icc tmin tmax) := by
  have hIoo :
      EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
        (Ioo tmin tmax) :=
    G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_of_subset G₂
      (fun _t ht ↦ h₁ (Ioo_subset_Icc_self ht))
      (fun _t ht ↦ h₂ (Ioo_subset_Icc_self ht))
      ht₀ hX x
  have hne : tmin ≠ tmax := ne_of_lt (lt_trans ht₀.1 ht₀.2)
  refine Set.EqOn.of_subset_closure hIoo
    ((G₁.continuousOn_eval x).mono h₁)
    ((G₂.continuousOn_eval x).mono h₂)
    (fun _t ht ↦ Ioo_subset_Icc_self ht) ?_
  intro t ht
  rw [closure_Ioo hne]
  exact ht

/-- Common-closed-subinterval time-slice diffeomorphism form of autonomous raw
gauge-flow uniqueness. -/
theorem eqOn_maps3_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Icc tmin tmax) := by
  intro t ht
  apply DFunLike.ext
  intro x
  exact G₁.eqOn_eval_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-closed-subinterval form of autonomous raw gauge-flow
uniqueness. -/
theorem eval_eq_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax)
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX x ht

/-- Pointwise common-closed-subinterval time-slice diffeomorphism form of
autonomous raw gauge-flow uniqueness. -/
theorem maps3_eq_of_autonomous_Icc_boundaryless_of_subset
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {s₁ s₂ : Set ℝ} {tmin tmax t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₁ t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M) (fun _ ↦ X) s₂ t₀)
    (h₁ : Icc tmin tmax ⊆ s₁)
    (h₂ : Icc tmin tmax ⊆ s₂)
    (ht₀ : t₀ ∈ Ioo tmin tmax)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc tmin tmax) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Icc_boundaryless_of_subset G₂
    h₁ h₂ ht₀ hX ht

/-- Open-overlap form of autonomous raw gauge-flow uniqueness for two open
Picard intervals.  The visible overlap is chosen automatically as
`Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂)`. -/
theorem eqOn_maps3_of_autonomous_Ioo_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂)) := by
  refine G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless_of_subset G₂
    ?_ ?_ ht₀ hX
  · intro t ht
    exact
      ⟨lt_of_le_of_lt (le_max_left tmin₁ tmin₂) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left tmax₁ tmax₂)⟩
  · intro t ht
    exact
      ⟨lt_of_le_of_lt (le_max_right tmin₁ tmin₂) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right tmax₁ tmax₂)⟩

/-- Pointwise open-overlap form of autonomous raw gauge-flow uniqueness for two
open Picard intervals. -/
theorem maps3_eq_of_autonomous_Ioo_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂)) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Ioo_boundaryless_overlap G₂ ht₀ hX ht

/-- Pointwise-curve open-overlap form of autonomous raw gauge-flow uniqueness
for two open Picard intervals. -/
theorem eqOn_eval_of_autonomous_Ioo_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂)) := by
  intro t ht
  have hmaps : G₁.maps3 t = G₂.maps3 t :=
    G₁.maps3_eq_of_autonomous_Ioo_boundaryless_overlap G₂ ht₀ hX ht
  simpa [hmaps]

/-- Pointwise open-overlap form of autonomous raw gauge-flow uniqueness for
fixed base points. -/
theorem eval_eq_of_autonomous_Ioo_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Ioo tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Ioo_boundaryless_overlap G₂ ht₀ hX x ht

/-- Closed-overlap form of autonomous raw gauge-flow uniqueness for two closed
Picard intervals.  Endpoint equality is inherited from the common closed
subinterval theorem, with the visible overlap chosen automatically as
`Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂)`. -/
theorem eqOn_maps3_of_autonomous_Icc_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    EqOn G₁.maps3 G₂.maps3 (Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂)) := by
  refine G₁.eqOn_maps3_of_autonomous_Icc_boundaryless_of_subset G₂
    ?_ ?_ ht₀ hX
  · intro t ht
    exact
      ⟨le_trans (le_max_left tmin₁ tmin₂) ht.1,
        le_trans ht.2 (min_le_left tmax₁ tmax₂)⟩
  · intro t ht
    exact
      ⟨le_trans (le_max_right tmin₁ tmin₂) ht.1,
        le_trans ht.2 (min_le_right tmax₁ tmax₂)⟩

/-- Pointwise closed-overlap form of autonomous raw gauge-flow uniqueness for
two closed Picard intervals. -/
theorem maps3_eq_of_autonomous_Icc_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂)) :
    G₁.maps3 t = G₂.maps3 t :=
  G₁.eqOn_maps3_of_autonomous_Icc_boundaryless_overlap G₂ ht₀ hX ht

/-- Pointwise-curve closed-overlap form of autonomous raw gauge-flow uniqueness
for two closed Picard intervals. -/
theorem eqOn_eval_of_autonomous_Icc_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (x : M) :
    EqOn (fun t : ℝ ↦ (G₁.maps3 t) x) (fun t : ℝ ↦ (G₂.maps3 t) x)
      (Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂)) := by
  intro t ht
  have hmaps : G₁.maps3 t = G₂.maps3 t :=
    G₁.maps3_eq_of_autonomous_Icc_boundaryless_overlap G₂ ht₀ hX ht
  simpa [hmaps]

/-- Pointwise closed-overlap form of autonomous raw gauge-flow uniqueness for
fixed base points. -/
theorem eval_eq_of_autonomous_Icc_boundaryless_overlap
    [BoundarylessManifold I M]
    {X : Π x : M, TangentSpace I x}
    {tmin₁ tmax₁ tmin₂ tmax₂ t₀ t : ℝ}
    (G₁ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₁ tmax₁) t₀)
    (G₂ : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (fun _ ↦ X) (Icc tmin₂ tmax₂) t₀)
    (ht₀ : t₀ ∈ Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (hX : ContMDiff I I.tangent 1 (T% X))
    (ht : t ∈ Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂))
    (x : M) :
    (G₁.maps3 t) x = (G₂.maps3 t) x :=
  G₁.eqOn_eval_of_autonomous_Icc_boundaryless_overlap G₂ ht₀ hX x ht

/-- Reinterpret a raw `C³` gauge-flow witness for an equal vector field along the flow image. -/
def congr_vectorField
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := G.satisfies.congr_vectorField hXY

/-- Reinterpret a raw `C³` gauge-flow witness when two vector fields agree
along the flow image in the relative time-set filter at each time. -/
def congr_vectorField_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := SatisfiesGaugeFlowOn.congr_vectorField_nhdsWithin
    (I := I) (M := M) G.satisfies hXY

/-- Reinterpret a raw `C³` gauge-flow witness when two vector fields agree on the time set. -/
def congr_vectorField_of_eqOn
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t x = Y t x) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀ :=
  G.congr_vectorField (fun t ht x ↦ hXY t ht (G.maps3 t x))

@[simp] theorem congr_vectorField_maps3
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).maps3 = G.maps3 := rfl

@[simp] theorem congr_vectorField_nhdsWithin_maps3
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).maps3 = G.maps3 := rfl

@[simp] theorem congr_vectorField_anchored
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).anchored = G.anchored := rfl

@[simp] theorem congr_vectorField_nhdsWithin_anchored
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).anchored = G.anchored := rfl

@[simp] theorem congr_vectorField_satisfies
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ x : M, X t (G.maps3 t x) = Y t (G.maps3 t x)) :
    (G.congr_vectorField hXY).satisfies = G.satisfies.congr_vectorField hXY := rfl

@[simp] theorem congr_vectorField_nhdsWithin_satisfies
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      X τ (G.maps3 τ x) = Y τ (G.maps3 τ x)) :
    (G.congr_vectorField_nhdsWithin hXY).satisfies =
      SatisfiesGaugeFlowOn.congr_vectorField_nhdsWithin
        (I := I) (M := M) G.satisfies hXY := rfl

/-- Transport proof-level raw `C³` gauge-flow existence across vector fields that agree on the
time set. -/
theorem nonempty_congr_vectorField_of_eqOn
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀))
    (hXY : ∀ t ∈ s, ∀ x : M, X t x = Y t x) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.congr_vectorField_of_eqOn hXY⟩

/-- Transport proof-level raw `C³` gauge-flow existence across vector fields
that agree in the relative time-set filter at each time. -/
theorem nonempty_congr_vectorField_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀))
    (hXY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M, X τ x = Y τ x) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) Y s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.congr_vectorField_nhdsWithin
    (fun t ht ↦ (hXY t ht).mono fun τ hτ x ↦ hτ (G.maps3 τ x))⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from the pointwise
manifold derivative form produced by ODE/integral-curve theorems. -/
noncomputable def of_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := maps3
  anchored := anchored
  satisfies := SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (Φ := maps3.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
    (X := X) (s := s) hderiv

/-- Build proof-level raw `C^3` gauge-flow existence from the pointwise
within-time-set manifold derivative form produced by ODE/integral-curve
theorems. -/
theorem nonempty_of_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Build a raw `C^3` gauge-flow witness directly from mutually inverse `C^3`
time-slice maps satisfying the pointwise manifold derivative equation. -/
noncomputable def of_inverse_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  let maps3 := SmoothSelfDiffeomorph3Family.ofInverse
    (I := I) (M := M) F G hleft hright hF hG
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3
    (SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt
      (I := I) (M := M) F G hleft hright hF hG hanchored)
    (fun t ht x ↦ by
      simpa [maps3] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence directly from mutually inverse
`C^3` time-slice maps satisfying the pointwise manifold derivative equation. -/
theorem nonempty_of_inverse_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_inverse_hasMFDerivWithinAt
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from inverse identities and
regularity stated on `Set.univ`.  This is the endpoint shape produced by the
open-cover gluing lemmas above. -/
noncomputable def of_inverseOn_univ_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_inverse_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G
    (fun t x ↦ hleft t (Set.mem_univ x))
    (fun t x ↦ hright t (Set.mem_univ x))
    (fun t ↦ by simpa [contMDiffOn_univ] using hF t)
    (fun t ↦ by simpa [contMDiffOn_univ] using hG t)
    hanchored hderiv

/-- Proof-level raw `C^3` gauge-flow existence from inverse identities and
regularity stated on `Set.univ`. -/
theorem nonempty_of_inverseOn_univ_hasMFDerivWithinAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_inverseOn_univ_hasMFDerivWithinAt
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from the preferred-chart
ODE form of the derivative on the time set.

This is the chart-local adapter expected from Banach/Picard constructions:
instead of asking for a manifold derivative directly, it accepts continuity of
the raw curves and the derivative of the coordinate curve in the chart centered
at the endpoint. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored
    (fun t ht x ↦ by
      rw [HasMFDerivWithinAt]
      refine ⟨hcont t ht x, ?_⟩
      have h := hderiv t ht x
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at h
      simpa [writtenInExtChartAt] using h)

/-- Proof-level raw `C^3` gauge-flow existence from preferred-chart ODE
derivatives on the time set. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from globally glued inverse slices
and centered preferred-chart derivative data for the forward map.  The inverse
and regularity hypotheses are stated on `Set.univ`, matching the output of the
open-cover gluing layer. -/
noncomputable def of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (X t (F t x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ := by
  let hleft' : ∀ t : ℝ, Function.LeftInverse (G t) (F t) :=
    fun t x ↦ hleft t (Set.mem_univ x)
  let hright' : ∀ t : ℝ, Function.RightInverse (G t) (F t) :=
    fun t x ↦ hright t (Set.mem_univ x)
  let hF' : ∀ t : ℝ, ContMDiff I I 3 (F t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hF t
  let hG' : ∀ t : ℝ, ContMDiff I I 3 (G t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hG t
  let maps3 := SmoothSelfDiffeomorph3Family.ofInverse
    (I := I) (M := M) F G hleft' hright' hF' hG'
  exact of_hasDerivWithinAt_extChartAt_eval_self
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3
    (SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt
      (I := I) (M := M) F G hleft' hright' hF' hG' hanchored)
    (fun t ht x ↦ by simpa [maps3] using hcont t ht x)
    (fun t ht x ↦ by simpa [maps3] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from globally glued inverse
slices and centered preferred-chart derivative data. -/
theorem nonempty_of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (X t (F t x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hcont hderiv⟩

/-- A centered preferred-chart derivative gives continuity of the manifold
curve, provided the curve is eventually in the source of the centered chart. -/
theorem continuousWithinAt_eval_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {s : Set ℝ} {t : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)) (x : M)
    (hsource :
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    {v : TangentSpace I ((maps3 t) x)}
    (hderiv : HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x)) v s t) :
    ContinuousWithinAt (fun τ : ℝ ↦ (maps3 τ) x) s t := by
  let e := extChartAt I ((maps3 t) x)
  have hx : (maps3 t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((maps3 t) x)
  have hsymm : ContinuousAt e.symm (e ((maps3 t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((maps3 t) x)
  have hchart : ContinuousWithinAt (fun τ : ℝ ↦ e ((maps3 τ) x)) s t := by
    simpa [e] using hderiv.continuousWithinAt
  have hcomp' : ContinuousWithinAt
      (e.symm ∘ fun τ : ℝ ↦ e ((maps3 τ) x)) s t :=
    ContinuousAt.comp_continuousWithinAt
      (g := e.symm) (f := fun τ : ℝ ↦ e ((maps3 τ) x))
      (s := s) (x := t) hsymm hchart
  have hcomp : ContinuousWithinAt
      (fun τ : ℝ ↦ e.symm (e ((maps3 τ) x))) s t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝[s] t, (maps3 τ) x ∈ e.source := by
    simpa [e] using hsource
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)
    (by simpa [e] using (e.left_inv hx).symm)

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from centered
preferred-chart ODE data, deriving manifold-curve continuity from eventual
membership in the centered chart source. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      continuousWithinAt_eval_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
        (I := I) (M := M) maps3 x (hsource t ht x) (hderiv t ht x))
    hderiv

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart
ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from globally glued inverse slices
and centered preferred-chart derivative data, deriving manifold-curve
continuity from eventual membership in the centered chart source. -/
noncomputable def of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (X t (F t x)) s t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ := by
  let hleft' : ∀ t : ℝ, Function.LeftInverse (G t) (F t) :=
    fun t x ↦ hleft t (Set.mem_univ x)
  let hright' : ∀ t : ℝ, Function.RightInverse (G t) (F t) :=
    fun t x ↦ hright t (Set.mem_univ x)
  let hF' : ∀ t : ℝ, ContMDiff I I 3 (F t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hF t
  let hG' : ∀ t : ℝ, ContMDiff I I 3 (G t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hG t
  let maps3 := SmoothSelfDiffeomorph3Family.ofInverse
    (I := I) (M := M) F G hleft' hright' hF' hG'
  exact of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3
    (SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt
      (I := I) (M := M) F G hleft' hright' hF' hG' hanchored)
    (fun t ht x ↦ by simpa [maps3] using hsource t ht x)
    (fun t ht x ↦ by simpa [maps3] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from globally glued inverse
slices and centered preferred-chart derivative data plus eventual source
membership. -/
theorem nonempty_of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (X t (F t x)) s t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from centered preferred-chart ODE
data for a model vector field, after identifying that model field with the
target field along the candidate flow. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart ODE
data for a model vector field identified with the target field along the
candidate flow. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness from centered preferred-chart ODE
data for a model vector field, after identifying that model field with the
target field along the candidate flow in the relative time-set filter. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  (of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (s := s) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence from centered preferred-chart
ODE data for a model vector field identified with the target field along the
candidate flow in the relative time-set filter. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness from globally glued inverse slices
and centered preferred-chart ODE data for a locally equal readout vector field.
This combines the open-cover gluing endpoint with the relative-filter
vector-field congruence used by finite-cover Banach readouts. -/
noncomputable def of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ := by
  let hleft' : ∀ t : ℝ, Function.LeftInverse (G t) (F t) :=
    fun t x ↦ hleft t (Set.mem_univ x)
  let hright' : ∀ t : ℝ, Function.RightInverse (G t) (F t) :=
    fun t x ↦ hright t (Set.mem_univ x)
  let hF' : ∀ t : ℝ, ContMDiff I I 3 (F t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hF t
  let hG' : ∀ t : ℝ, ContMDiff I I 3 (G t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hG t
  let maps3 := SmoothSelfDiffeomorph3Family.ofInverse
    (I := I) (M := M) F G hleft' hright' hF' hG'
  exact of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y) (s := s) (t₀ := t₀)
    maps3
    (SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt
      (I := I) (M := M) F G hleft' hright' hF' hG' hanchored)
    (fun t ht x ↦ by simpa [maps3] using hsource t ht x)
    (fun t ht x ↦ by simpa [maps3] using hderiv t ht x)
    (fun t ht ↦ by simpa [maps3] using hY t ht)

/-- Proof-level raw `C^3` gauge-flow existence from globally glued inverse
slices and centered preferred-chart ODE data for a locally equal readout vector
field. -/
theorem nonempty_of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hsource hderiv hY⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from
ordinary pointwise manifold derivatives available at each time of `s`.  This
matches local ODE constructions that first promote a closed-interval derivative
to an ordinary derivative on the open time set, without requiring data outside
that time set. -/
noncomputable def of_hasMFDerivAtOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivWithinAt (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t ht x ↦ (hderiv t ht x).hasMFDerivWithinAt)

/-- Build proof-level raw `C^3` gauge-flow existence on `s` from ordinary
pointwise manifold derivatives available at each time of `s`. -/
theorem nonempty_of_hasMFDerivAtOn
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on the open Picard
interior from pointwise manifold derivative data proved within the closed
Picard interval. -/
noncomputable def of_hasMFDerivWithinAt_Icc
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasMFDerivAt[Icc tmin tmax] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasMFDerivAtOn (I := I) (M := M) (X := X)
    (s := Ioo tmin tmax) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      (hderiv t (Ioo_subset_Icc_self ht) x).hasMFDerivAt
        (Icc_mem_nhds ht.1 ht.2))

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
pointwise manifold derivative data proved within the closed Picard interval. -/
theorem nonempty_of_hasMFDerivWithinAt_Icc
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasMFDerivAt[Icc tmin tmax] (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasMFDerivWithinAt_Icc maps3 anchored hderiv⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from named primitive derivative data proved within the closed Picard
interval. -/
noncomputable def of_intrinsicDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_hasMFDerivWithinAt_Icc (I := I) (M := M)
    (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀) maps3 anchored hderiv

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from named primitive derivative data proved within the closed Picard
interval. -/
theorem nonempty_of_intrinsicDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicDerivativeOn_Ioo maps3 anchored hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from ordinary
preferred-chart ODE derivatives available at each time of `s`. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivWithinAt_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦ (hcont t ht x).continuousWithinAt)
    (fun t ht x ↦ (hderiv t ht x).hasDerivWithinAt)

/-- Proof-level raw `C^3` gauge-flow existence on `s` from ordinary
preferred-chart ODE derivatives available at each time of `s`. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hcont : ∀ t ∈ s, ∀ x : M,
      ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- An ordinary centered preferred-chart derivative gives ordinary continuity
of the manifold curve, provided the curve is eventually in the source of the
centered chart. -/
theorem continuousAt_eval_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {t : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M)) (x : M)
    (hsource :
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    {v : TangentSpace I ((maps3 t) x)}
    (hderiv : HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x)) v t) :
    ContinuousAt (fun τ : ℝ ↦ (maps3 τ) x) t := by
  let e := extChartAt I ((maps3 t) x)
  have hx : (maps3 t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((maps3 t) x)
  have hsymm : ContinuousAt e.symm (e ((maps3 t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((maps3 t) x)
  have hchart : ContinuousAt (fun τ : ℝ ↦ e ((maps3 τ) x)) t := by
    simpa [e] using hderiv.continuousAt
  have hcomp' : ContinuousAt
      (e.symm ∘ fun τ : ℝ ↦ e ((maps3 τ) x)) t :=
    ContinuousAt.comp
      (g := e.symm) (f := fun τ : ℝ ↦ e ((maps3 τ) x))
      (x := t) hsymm hchart
  have hcomp : ContinuousAt (fun τ : ℝ ↦ e.symm (e ((maps3 τ) x))) t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝 t, (maps3 τ) x ∈ e.source := by
    simpa [e] using hsource
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from ordinary centered
preferred-chart ODE data, deriving ordinary manifold-curve continuity from
eventual membership in the centered chart source. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self (I := I) (M := M)
    (X := X) (s := s) (t₀ := t₀) maps3 anchored
    (fun t ht x ↦
      continuousAt_eval_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
        (I := I) (M := M) maps3 x (hsource t ht x) (hderiv t ht x))
    hderiv

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness from ordinary centered preferred-chart
ODE data for a model vector field, after identifying that model field with the
target field along the candidate flow. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data for a model vector field identified with the target
field along the candidate flow. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ x : M, Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness from ordinary centered
preferred-chart ODE data for a model vector field, after identifying that model
field with the target field along the candidate flow in the relative time-set
filter. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  (of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (s := s) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence from ordinary centered
preferred-chart ODE data for a model vector field identified with the target
field along the candidate flow in the relative time-set filter. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on the open Picard
interior from centered preferred-chart ODE data proved within the closed Picard
interval. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) (Icc tmin tmax) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := Ioo tmin tmax) (t₀ := t₀)
    maps3 anchored
    (fun t ht x ↦ by
      have htime : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      simpa [nhdsWithin_eq_nhds.2 htime] using
        hsource t (Ioo_subset_Icc_self ht) x)
    (fun t ht x ↦
      (hderiv t (Ioo_subset_Icc_self ht) x).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
centered preferred-chart ODE data proved within the closed Picard interval. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) (Icc tmin tmax) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field,
after identifying that model field with the target field along the candidate
flow on the closed interval. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored hsource
    (fun t ht x ↦ by simpa [hY t ht x] using hderiv t ht x)

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field
identified with the target field along the candidate flow. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) = X t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interior from
closed-interval centered preferred-chart ODE data for a model vector field,
after identifying that model field with the target field along the candidate
flow in the relative open-interval filter. -/
noncomputable def of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  (of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := Y) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored hsource hderiv).congr_vectorField_nhdsWithin hY

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interior
from closed-interval centered preferred-chart ODE data for a model vector field
identified with the target field along the candidate flow in the relative
open-interval filter. -/
theorem nonempty_of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (Y t ((maps3 t) x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) = X τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interval from
globally glued inverse slices and closed-Picard centered preferred-chart ODE
data for a locally equal readout vector field. -/
noncomputable def of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let hleft' : ∀ t : ℝ, Function.LeftInverse (G t) (F t) :=
    fun t x ↦ hleft t (Set.mem_univ x)
  let hright' : ∀ t : ℝ, Function.RightInverse (G t) (F t) :=
    fun t x ↦ hright t (Set.mem_univ x)
  let hF' : ∀ t : ℝ, ContMDiff I I 3 (F t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hF t
  let hG' : ∀ t : ℝ, ContMDiff I I 3 (G t) :=
    fun t ↦ by simpa [contMDiffOn_univ] using hG t
  let maps3 := SmoothSelfDiffeomorph3Family.ofInverse
    (I := I) (M := M) F G hleft' hright' hF' hG'
  exact of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3
    (SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt
      (I := I) (M := M) F G hleft' hright' hF' hG' hanchored)
    (fun t ht x ↦ by simpa [maps3] using hsource t ht x)
    (fun t ht x ↦ by simpa [maps3] using hderiv t ht x)
    (fun t ht ↦ by simpa [maps3] using hY t ht)

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interval from
globally glued inverse slices and closed-Picard centered preferred-chart ODE
data for a locally equal readout vector field. -/
theorem nonempty_of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ F τ x) ⁻¹' (extChartAt I (F t x)).source ∈
        𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G hleft hright hF hG hanchored hsource hderiv hY⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interval from
globally glued inverse slices and closed-Picard centered preferred-chart ODE
data, deriving centered chart-source membership from within-time continuity of
the glued forward slice. -/
noncomputable def of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hcont : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ F τ x) (Icc tmin tmax) t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G hleft hright hF hG hanchored
    (fun t ht x ↦
      preimage_extChartAt_source_self_mem_nhdsWithin_of_continuousWithinAt
        (I := I) (M := M) (s := Icc tmin tmax)
        (γ := fun τ : ℝ ↦ F τ x) (t := t) (hcont t ht x))
    hderiv hY

/-- Proof-level raw `C^3` gauge-flow existence on the open Picard interval from
globally glued inverse slices, closed-Picard centered preferred-chart ODE data,
and within-time continuity of the glued forward slice. -/
theorem nonempty_of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, LeftInvOn (G t) (F t) Set.univ)
    (hright : ∀ t : ℝ, RightInvOn (G t) (F t) Set.univ)
    (hF : ∀ t : ℝ, ContMDiffOn I I 3 (F t) Set.univ)
    (hG : ∀ t : ℝ, ContMDiffOn I I 3 (G t) Set.univ)
    (hanchored : ∀ x : M, F t₀ x = x)
    (hcont : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ F τ x) (Icc tmin tmax) t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (F τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G hleft hright hF hG hanchored hcont hderiv hY⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from named preferred-chart ODE data proved within the closed Picard
interval, by first converting the chart ODE into primitive manifold derivative
data. -/
noncomputable def of_intrinsicChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_intrinsicDerivativeOn_Ioo (I := I) (M := M)
    (g := g) (background := background) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored
    (Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
      (I := I) (M := M) hchart)

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from named preferred-chart ODE data proved within the closed Picard
interval. -/
theorem nonempty_of_intrinsicChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) maps3 g background (Icc tmin tmax)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicChartDerivativeOn_Ioo maps3 anchored hchart⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from fixed-chart ODE data proved within the closed Picard interval.

This is the finite-cover version of `of_intrinsicChartDerivativeOn_Ioo`: the
closed-Picard input may use a chosen chart center for each time and base point,
and the derivative layer transports it to the centered-chart package. -/
noncomputable def of_intrinsicFixedChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) maps3 g background chartCenter (Icc tmin tmax)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_intrinsicChartDerivativeOn_Ioo (I := I) (M := M)
    (g := g) (background := background) (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    maps3 anchored
    (Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.toChartDerivativeOn
      (I := I) (M := M) hfixed)

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from fixed-chart ODE data proved within the closed Picard interval. -/
theorem nonempty_of_intrinsicFixedChartDerivativeOn_Ioo
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) maps3 g background chartCenter (Icc tmin tmax)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicFixedChartDerivativeOn_Ioo maps3 anchored hfixed⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from closed-Picard fixed-chart ODE data for a model vector field, after
identifying that model field with the intrinsic DeTurck gauge field along the
candidate flow. -/
noncomputable def of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hmem : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((maps3 τ) x))
        (tangentCoordChange I ((maps3 t) x) (chartCenter t x) ((maps3 t) x)
          (Y t ((maps3 t) x))) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps3 t) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_intrinsicFixedChartDerivativeOn_Ioo (I := I) (M := M)
    (g := g) (background := background) (chartCenter := chartCenter)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀) maps3 anchored
    (Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq
      (I := I) (M := M) hmem hsource hderiv hY)

/-- Proof-level intrinsic DeTurck raw gauge-flow existence on the open Picard
interior from closed-Picard fixed-chart model-vector-field ODE data. -/
theorem nonempty_of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hmem : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((maps3 τ) x))
        (tangentCoordChange I ((maps3 t) x) (chartCenter t x) ((maps3 t) x)
          (Y t ((maps3 t) x))) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      Y t ((maps3 t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps3 t) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq
    maps3 anchored hmem hsource hderiv hY⟩

/-- Build an intrinsic DeTurck raw gauge-flow witness on the open Picard
interior from closed-Picard fixed-chart ODE data for a model vector field,
identified with the intrinsic DeTurck gauge field in the closed-interval
relative time filter. -/
noncomputable def of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq_nhdsWithin
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hmem : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((maps3 τ) x))
        (tangentCoordChange I ((maps3 t) x) (chartCenter t x) ((maps3 t) x)
          (Y t ((maps3 t) x))) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ᶠ τ in 𝓝[Icc tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((maps3 τ) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀ :=
  of_intrinsicFixedChartDerivativeOn_Ioo (I := I) (M := M)
    (g := g) (background := background) (chartCenter := chartCenter)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀) maps3 anchored
    (Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq_nhdsWithin
      (I := I) (M := M) hmem hsource hderiv hY)

/-- Proof-level intrinsic DeTurck raw gauge-flow existence from fixed-chart
model-vector-field ODE data with a relative-filter intrinsic-field
identification. -/
theorem nonempty_of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq_nhdsWithin
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hmem : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (maps3 t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[Icc tmin tmax] t)
    (hderiv : ∀ t ∈ Icc tmin tmax, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((maps3 τ) x))
        (tangentCoordChange I ((maps3 t) x) (chartCenter t x) ((maps3 t) x)
          (Y t ((maps3 t) x))) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Icc tmin tmax, ∀ᶠ τ in 𝓝[Icc tmin tmax] t, ∀ x : M,
      Y τ ((maps3 τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((maps3 τ) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (Ioo tmin tmax) t₀) :=
  ⟨of_intrinsicFixedChartDerivativeOn_Ioo_of_vectorField_eq_nhdsWithin
    maps3 anchored hmem hsource hderiv hY⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness from unrestricted
ordinary centered preferred-chart ODE data plus eventual membership in the
centered chart source. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t : ℝ, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t _ht x ↦ hsource t x) (fun t _ht x ↦ hderiv t x)

/-- Proof-level raw `C^3` gauge-flow existence from unrestricted ordinary
centered preferred-chart ODE data plus eventual source membership. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hsource : ∀ t : ℝ, ∀ x : M,
      (fun τ : ℝ ↦ (maps3 τ) x) ⁻¹' (extChartAt I ((maps3 t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((maps3 t) x)) ((maps3 τ) x))
        (X t ((maps3 t) x)) t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Build a raw `C^3` diffeomorphism gauge-flow witness on `s` from
unrestricted pointwise manifold derivatives. -/
noncomputable def of_hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  of_hasMFDerivAtOn (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    maps3 anchored (fun t _ht x ↦ hderiv t x)

/-- Build proof-level raw `C^3` gauge-flow existence on `s` from unrestricted
pointwise manifold derivatives. -/
theorem nonempty_of_hasMFDerivAt
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps3 : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      maps3 t₀)
    (hderiv : ∀ t : ℝ, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (maps3 t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

/-- Restrict a raw `C^3` gauge flow to a smaller time set. -/
def mono
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := G.maps3
  anchored := G.anchored
  satisfies := G.satisfies.mono hst

/-- Restrict proof-level raw `C^3` gauge-flow existence to a smaller time set. -/
theorem nonempty_mono
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀))
    (hst : s ⊆ t) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.mono hst⟩

@[simp] theorem mono_maps3
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).maps3 = G.maps3 := rfl

@[simp] theorem mono_anchored
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).anchored = G.anchored := rfl

@[simp] theorem mono_satisfies
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X t t₀)
    (hst : s ⊆ t) :
    (G.mono hst).satisfies = G.satisfies.mono hst := rfl

/-- If the time-dependent vector field vanishes on the time set, the identity `C³`
diffeomorphism family is a raw gauge flow. -/
noncomputable def identity_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ where
  maps3 := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)
  anchored := SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t₀
  satisfies := SmoothSelfDiffeomorph3Family.id_satisfiesGaugeFlowOn_of_eq_zero
    (I := I) (M := M) (X := X) (s := s) hX

/-- If the time-dependent vector field vanishes on the time set, the identity
`C³` diffeomorphism family gives proof-level raw gauge-flow existence. -/
theorem nonempty_identity_of_eq_zero
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hX : ∀ t ∈ s, ∀ x : M, X t x = 0) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_eq_zero X s t₀ hX⟩

/-- If every tangent fiber is a subsingleton, the identity `C³` diffeomorphism
family is a raw gauge flow for any time-dependent vector field. -/
noncomputable def identity_of_subsingleton_tangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun t _ht x ↦ Subsingleton.elim (X t x) 0)

/-- If every tangent fiber is a subsingleton, the identity `C³` diffeomorphism
family gives proof-level raw gauge-flow existence for any vector field. -/
theorem nonempty_identity_of_subsingleton_tangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_subsingleton_tangent X s t₀⟩

/-- Model-space version of `identity_of_subsingleton_tangent`. -/
noncomputable def identity_of_subsingleton_model
    [Subsingleton E]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_subsingleton_tangent (I := I) (M := M) X s t₀

/-- Model-space version of
`nonempty_identity_of_subsingleton_tangent`. -/
theorem nonempty_identity_of_subsingleton_model
    [Subsingleton E]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_subsingleton_model X s t₀⟩

/-- On an empty manifold, the identity `C³` diffeomorphism family is a raw gauge
flow for any time-dependent vector field. -/
noncomputable def identity_of_isEmpty
    [IsEmpty M]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀ :=
  identity_of_eq_zero (I := I) (M := M) X s t₀
    (fun _t _ht x ↦ isEmptyElim x)

/-- On an empty manifold, the identity `C³` diffeomorphism family gives
proof-level raw gauge-flow existence for any vector field. -/
theorem nonempty_identity_of_isEmpty
    [IsEmpty M]
    (X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  ⟨identity_of_isEmpty X s t₀⟩

/-- Specialize a raw flow for the intrinsic DeTurck vector field to the anchored
gauge object used by gauge reduction. -/
def toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M) (g := g) (background := background)
    (s := s) (t₀ := t₀) G.maps3 G.anchored G.satisfies

/-- Proof-level conversion from raw intrinsic DeTurck gauge-flow existence to
the anchored geometric gauge object used by gauge reduction. -/
theorem nonempty_toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hG : Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀)) :
    Nonempty (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      g background s t₀) := by
  rcases hG with ⟨G⟩
  exact ⟨G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn⟩

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).maps = G.maps3 := rfl

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_anchored
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).anchored = G.anchored := rfl

@[simp] theorem toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn_follows
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s t₀) :
    (G.toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) (g := g) (background := background)
      (s := s) (t₀ := t₀)).follows = G.satisfies := rfl

end Diffeomorph3GaugeFlowOn

/-- Raw intrinsic DeTurck `C^3` gauge-flow existence data for every chosen
DeTurck local solution of a fixed initial-value problem. -/
structure IntrinsicDeTurckGaugeFlowExistence
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  flow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistence

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from pointwise
manifold derivative data.  This is the adapter expected when an ODE theorem
directly returns `HasMFDerivAt[s]` integral-curve witnesses. -/
noncomputable def of_hasMFDerivWithinAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from pointwise
within-time-set manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivWithinAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary pointwise manifold derivative data on each local solution's time set.
This is the adapter expected when the manifold ODE construction has already
converted within-interval equations to ordinary derivatives on the open
solution interval. -/
noncomputable def of_hasMFDerivAtOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasMFDerivAtOn
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary
pointwise manifold derivative data on each local solution's time set, kept as
proof-level evidence. -/
theorem nonempty_of_hasMFDerivAtOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from primitive derivative data proved on closed Picard intervals. -/
noncomputable def ofPicardIccDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G := Diffeomorph3GaugeFlowOn.of_intrinsicDerivativeOn_Ioo
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hderiv sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from primitive closed-Picard derivative data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccDerivative maps3 anchored tmin tmax htimeSet hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from preferred-chart ODE data proved on closed Picard intervals, routed
through the primitive derivative handoff. -/
noncomputable def ofPicardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccDerivative (I := I) (M := M) (ivp := ivp)
    maps3 anchored tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
        (I := I) (M := M) (hchart sol))

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from preferred-chart closed-Picard data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative maps3 anchored tmin tmax htimeSet hchart⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from fixed-chart ODE data proved on closed Picard intervals. -/
noncomputable def ofPicardIccFixedChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hfixed : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (chartCenter sol) (Icc (tmin sol) (tmax sol))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccChartDerivative (I := I) (M := M) (ivp := ivp)
    maps3 anchored tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.toChartDerivativeOn
        (I := I) (M := M) (hfixed sol))

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from fixed-chart closed-Picard data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hfixed : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (chartCenter sol) (Icc (tmin sol) (tmax sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccFixedChartDerivative
    maps3 anchored chartCenter tmin tmax htimeSet hfixed⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard fixed-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows. -/
noncomputable def ofPicardIccFixedChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccFixedChartDerivative (I := I) (M := M) (ivp := ivp)
    maps3 anchored chartCenter tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq
        (I := I) (M := M) (hmem sol) (hsource sol) (hderiv sol) (hY sol))

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard fixed-chart model-vector-field ODE data, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccFixedChartDerivative_of_vectorField_eq
    maps3 anchored chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard fixed-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields in the
closed-interval relative time filters. -/
noncomputable def ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccFixedChartDerivative (I := I) (M := M) (ivp := ivp)
    maps3 anchored chartCenter tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq_nhdsWithin
        (I := I) (M := M) (hmem sol) (hsource sol) (hderiv sol) (hY sol))

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from fixed-chart
model-vector-field ODE data with a closed-interval relative-filter
intrinsic-field identification, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard preferred-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G :=
      Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard model-vector-field chart ODE data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard preferred-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have G :=
      Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using G

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from closed-Picard model-vector-field chart ODE data and relative-filter
field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from globally glued inverse slices and closed-Picard preferred-chart ODE
data for model vector fields, after identifying those fields with the
intrinsic DeTurck gauge fields in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (hleft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, LeftInvOn (G sol t) (F sol t) Set.univ)
    (hright : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, RightInvOn (G sol t) (F sol t) Set.univ)
    (hF : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ContMDiffOn I I 3 (F sol t) Set.univ)
    (hG : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ContMDiffOn I I 3 (G sol t) Set.univ)
    (hanchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ x : M, F sol ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ F sol τ x) ⁻¹' (extChartAt I (F sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (F sol τ x))
          ((Y sol) t (F sol t x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ (F sol τ x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ (F sol τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (F sol) (G sol) (hleft sol) (hright sol) (hF sol) (hG sol)
        (hanchored sol) (hsource sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from globally glued
inverse slices, closed-Picard chart ODE data, and relative-filter field
equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (hleft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, LeftInvOn (G sol t) (F sol t) Set.univ)
    (hright : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, RightInvOn (G sol t) (F sol t) Set.univ)
    (hF : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ContMDiffOn I I 3 (F sol t) Set.univ)
    (hG : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ContMDiffOn I I 3 (G sol t) Set.univ)
    (hanchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ x : M, F sol ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ F sol τ x) ⁻¹' (extChartAt I (F sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (F sol τ x))
          ((Y sol) t (F sol t x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ (F sol τ x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ (F sol τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    F G hleft hright hF hG hanchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ (maps3 sol τ) x)
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hcont sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ (maps3 sol τ) x)
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousAt (fun τ : ℝ ↦ (maps3 sol τ) x) t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hcont sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        ContinuousAt (fun τ : ℝ ↦ (maps3 sol τ) x) t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (Y := Y sol)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from same-time-set
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (Y := Y sol)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (maps3 sol) (anchored sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from ordinary
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          ((Y sol) t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored (fun sol t _ht x ↦ hsource sol t x) (fun sol t _ht x ↦ hderiv sol t x)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership,
kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data. -/
noncomputable def of_hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivAtOn (I := I) (M := M) (ivp := ivp)
    maps3 anchored (fun sol t _ht x ↦ hderiv sol t x)

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

/-- If the intrinsic DeTurck gauge field vanishes on every local solution's time
set, the identity diffeomorphism family supplies the raw `C³` gauge-flow
existence data for a fixed IVP. -/
noncomputable def identityOfGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (hzero sol)

/-- Fixed-IVP zero-gauge-field identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfGaugeFieldEqZero hzero⟩

/-- Package fixed-IVP named derivative data as raw gauge-flow existence data. -/
noncomputable def ofDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivWithinAt (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Package fixed-IVP named derivative data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofDerivative maps3 anchored hflowDeriv⟩

/-- Package fixed-IVP within-time-set preferred-chart ODE data as raw gauge-flow
existence data. This is the named chart-data analogue of
`of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored
    (fun sol t ht x ↦ (hchart sol t ht x).1)
    (fun sol t ht x ↦ (hchart sol t ht x).2)

/-- Package fixed-IVP within-time-set preferred-chart ODE data as proof-level raw
gauge-flow existence data. -/
theorem nonempty_ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofChartDerivative maps3 anchored hchart⟩

/-- Fixed-IVP within-time-set preferred-chart ODE data also supplies the existing
within-time-set derivative view directly. -/
theorem derivativeData_ofChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivative_of_chartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3) hchart

/-- Package fixed-IVP ordinary-at-time named derivative data as raw gauge-flow
existence data. -/
noncomputable def ofDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivAtOn (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Package fixed-IVP ordinary-at-time named derivative data as proof-level raw
gauge-flow existence data. -/
theorem nonempty_ofDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofDerivativeAt maps3 anchored hflowDeriv⟩

/-- Package fixed-IVP preferred-chart ODE data as raw gauge-flow existence data.
This is the named chart-data analogue of
`of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M) (ivp := ivp)
    maps3 anchored
    (fun sol t ht x ↦ (hchart sol t ht x).1)
    (fun sol t ht x ↦ (hchart sol t ht x).2)

/-- Package fixed-IVP preferred-chart ODE data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofChartDerivativeAt maps3 anchored hchart⟩

/-- Fixed-IVP ordinary preferred-chart ODE data also supplies the existing
within-time-set derivative view directly. -/
theorem derivativeData_ofChartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivative_of_derivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3) hchart)

/-- Chosen-background intrinsic DeTurck solutions have zero intrinsic DeTurck gauge field, so the
identity diffeomorphism family supplies the raw `C³` gauge-flow existence data for a fixed IVP. -/
noncomputable def identityOfChosenBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_eq_zero
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
      (fun t _ht x ↦ by
        have hLC :
            CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
              (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background :=
          usesChosenBackground_isLeviCivita
            (I := I) (M := M) sol.1 sol.2
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background hLC
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- Chosen-background fixed-IVP identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfChosenBackground
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfChosenBackground ivp⟩

/-- When every tangent fiber is a subsingleton, the intrinsic DeTurck vector field vanishes
identically, so the identity `C³` diffeomorphism family supplies the raw gauge-flow existence
data for any chosen DeTurck local solution of a fixed initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_subsingleton_tangent
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

/-- Fixed-IVP subsingleton-tangent identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfSubsingletonTangent ivp⟩

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, every tangent fiber is automatically subsingleton, so the identity `C³` family
supplies raw gauge-flow existence data. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  identityOfSubsingletonTangent (I := I) (M := M) ivp

/-- Fixed-IVP subsingleton-model identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonModel
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfSubsingletonModel ivp⟩

/-- On an empty manifold, the gauge-flow obligation is vacuous, so the identity `C³` diffeomorphism
family supplies the raw gauge-flow existence data for any chosen DeTurck local solution of a fixed
initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.identity_of_isEmpty
      (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

/-- Fixed-IVP empty-manifold identity raw-flow existence, kept as proof-level
evidence. -/
theorem nonempty_identityOfIsEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨identityOfIsEmpty ivp⟩

def toDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := fun sol ↦ (G.flow sol).maps3
  anchored := fun sol ↦ (G.flow sol).anchored
  satisfies := fun sol ↦ (G.flow sol).satisfies

/-- For a fixed-IVP package whose intrinsic DeTurck gauge field vanishes on each
solution's time set, the identity raw gauge flow supplies the required pullback
metric time derivative. -/
theorem identityOfGaugeFieldEqZero_hpullDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0)
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
          hzero).toDiffeomorph3GaugeFlow).maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
          hzero).toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (hzero sol)
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  intro t ht x u v
  have hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t
  have hu : (gauge3.maps t).pushforwardTangent x u = u := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x u = u
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
  have hv : (gauge3.maps t).pushforwardTangent x v = v := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x v = v
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
  have hvec :
      sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t = 0 := by
    rw [sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField]
    have hsource :
        intrinsicDeTurckVectorField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t = 0 := by
      funext y
      simpa [intrinsicDeTurckGaugeField] using hzero sol t ht y
    rw [hsource]
    funext y
    rw [SmoothSelfDiffeomorph2.pullbackVectorField_apply]
    exact ContinuousLinearMap.map_zero ((gauge3.maps t).pullbackTangent y)
  let pulledConnection :=
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t
  have hcov :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) = 0 := by
    rw [hvec]
    exact CovariantDerivative.zero (cov := pulledConnection)
  have hcovu :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u = 0 := by
    exact congrArg (fun A => A u) (congrFun hcov x)
  have hcovv :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v = 0 := by
    exact congrArg (fun A => A v) (congrFun hcov x)
  have hleft :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    rw [hcovu]
    exact congrArg (fun L : (TangentSpace I : M → Type _) x →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.map_zero
        (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x))
  have hright :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    rw [hcovv]
    exact ContinuousLinearMap.map_zero
      (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u)
  have hleftExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    simpa [pulledConnection] using hleft
  have hrightExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    simpa [pulledConnection] using hright
  have hpoint :
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    change sol.1.toIntrinsicDeTurckSolution.metricVelocity t
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x) u v =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v
    rw [SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x]
  have hvelocity :
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
    rw [hu, hv, hleftExact, hrightExact, zero_add, sub_zero]
    exact hpoint
  rw [hvelocity]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution ht x u v

/-- Package a fixed-IVP geometric intrinsic DeTurck gauge-flow bundle as raw
gauge-flow existence data. -/
def ofDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦
    Diffeomorph3GaugeFlowOn.of_satisfiesGaugeFlowOn
      (I := I) (M := M)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (G.maps3 sol) (G.anchored sol) (G.satisfies sol)

/-- Package a fixed-IVP geometric intrinsic DeTurck gauge-flow bundle as
proof-level raw gauge-flow existence data. -/
theorem nonempty_ofDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofDiffeomorph3GaugeFlow G⟩

/-- Proof-level conversion from fixed-IVP raw gauge-flow existence data to the
geometric gauge-flow bundle consumed by endpoint routes. -/
theorem nonempty_toDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hG : Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)) :
    Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases hG with ⟨G⟩
  exact ⟨G.toDiffeomorph3GaugeFlow⟩

/-- Package fixed-IVP named derivative data as raw gauge-flow existence data. -/
noncomputable def ofDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  of_hasMFDerivWithinAt (I := I) (M := M) (ivp := ivp)
    maps3 anchored hflowDeriv

/-- Derivative-family data extracted directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem derivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
      (G.flow sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht x
  exact (G.flow sol).hasMFDerivWithinAt ht x

/-- Fixed-chart derivative data extracted directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence, for any chart-center choice whose sources contain
the flow images on the solution time set. -/
theorem fixedChartDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (chartCenter : ℝ → M → M)
    (hmem : ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
      ((G.flow sol).maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
      (G.flow sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      chartCenter sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.flow sol).toIntrinsicFixedChartDerivativeOn hmem

/-- Ordinary fixed-chart derivative data extracted from fixed-IVP raw intrinsic
DeTurck gauge-flow existence on any time subset where the solution time set is a
neighborhood of each time. -/
theorem fixedChartDerivativeAtData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (chartCenter : ℝ → M → M) {u : Set ℝ}
    (hs : ∀ ⦃t : ℝ⦄, t ∈ u → sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmem : ∀ t ∈ u, ∀ x : M,
      ((G.flow sol).maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn (I := I) (M := M)
      (G.flow sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      chartCenter u :=
  (G.flow sol).toIntrinsicFixedChartDerivativeAtOn hs hmem

/-- Pointwise manifold derivative read out directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem hasMFDerivWithinAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivWithinAt ht x

/-- Preferred-chart derivative read out directly from fixed-IVP raw intrinsic
DeTurck gauge-flow existence. -/
theorem hasDerivWithinAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow derivatives in any preferred chart
whose source contains the time-`t` image. -/
theorem hasDerivWithinAt_extChartAt_eval_of_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) p (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_of_mem_source ht p x hsrc_ext

/-- Preferred-chart derivative read out directly from fixed-IVP raw intrinsic DeTurck gauge-flow
existence, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_self ht x

/-- Fixed-IVP raw intrinsic gauge-flow derivatives can be rewritten to a
relative-neighborhood-equal vector field. -/
theorem hasMFDerivWithinAt_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivWithinAt_congr_vectorField ht hXY x

/-- Fixed-IVP raw intrinsic gauge-flow preferred-chart derivatives can be
rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_congr_vectorField ht hXY x

/-- Fixed-chart version of
`IntrinsicDeTurckGaugeFlowExistence.hasDerivWithinAt_extChartAt_eval_congr_vectorField`. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (p x : M) (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) p (((G.flow sol).maps3 t) x)
        (Y t (((G.flow sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
    ht hXY p x hsrc_ext

/-- Fixed-IVP raw intrinsic gauge-flow centered preferred-chart derivatives can
be rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).hasDerivWithinAt_extChartAt_eval_self_congr_vectorField ht hXY x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous within the solution
time set in preferred chart coordinates. -/
theorem continuousWithinAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).continuousWithinAt_extChartAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous within the
solution time set in any preferred chart whose source contains the time-`t`
image. -/
theorem continuousWithinAt_extChartAt_eval_of_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).continuousWithinAt_extChartAt_eval_of_mem_source ht p x hsrc_ext

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous within the solution
time set. -/
theorem continuousWithinAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.flow sol).continuousWithinAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves are continuous on the solution time
set. -/
theorem continuousOn_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.flow sol).continuousOn_eval x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
tangent-bundle trivialization within the solution time set. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  (G.flow sol).eventuallyWithin_mem_trivializationAt_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the
preferred chart source within the solution time set. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  (G.flow sol).eventuallyWithin_mem_extChartAt_source_eval ht x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in any preferred
chart source containing the time-`t` image. -/
theorem eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow sol).maps3 τ) x ∈ (extChartAt I p).source :=
  (G.flow sol).eventuallyWithin_mem_extChartAt_source_eval_of_mem_source ht p x hsrc_ext

/-- Fixed-IVP open-Picard solution time sets are neighborhoods of each of their
times when the chosen solution time set has been identified with `Ioo tmin tmax`. -/
theorem timeSet_mem_nhds_of_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol)) :
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t := by
  intro sol t ht
  have ht' : t ∈ Ioo (tmin sol) (tmax sol) := by
    simpa [htimeSet sol] using ht
  simpa [htimeSet sol] using (isOpen_Ioo.mem_nhds ht')

/-- Fixed-IVP open-Picard ordinary fixed-chart derivative data on any subset of
the chosen solution's open time set. -/
theorem fixedChartDerivativeAtData_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (chartCenter : ℝ → M → M) {u : Set ℝ}
    (hu : u ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hmem : ∀ t ∈ u, ∀ x : M,
      ((G.flow sol).maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn (I := I) (M := M)
      (G.flow sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      chartCenter u :=
  G.fixedChartDerivativeAtData sol chartCenter
    (fun {t} ht ↦
      (G.timeSet_mem_nhds_of_eq_Ioo
        (I := I) (M := M) tmin tmax htimeSet) sol (hu ht))
    hmem

/-- Ordinary pointwise manifold derivative read out directly from fixed-IVP raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivAt hs x

/-- Ordinary preferred-chart derivative read out directly from fixed-IVP raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasDerivAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval hs x

/-- Ordinary preferred-chart derivative read out directly from fixed-IVP raw intrinsic DeTurck
gauge-flow existence at neighborhood-times, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x)) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_self hs x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow derivatives can be rewritten to
a neighborhood-equal vector field. -/
theorem hasMFDerivAt_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  (G.flow sol).hasMFDerivAt_congr_vectorField hs hXY x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow preferred-chart derivatives can
be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_congr_vectorField hs hXY x

/-- Ordinary fixed-IVP raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x)) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_self_congr_vectorField hs hXY x

/-- Fixed-IVP raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times in preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x)) t :=
  (G.flow sol).continuousAt_extChartAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times. -/
theorem continuousAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t :=
  (G.flow sol).continuousAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
tangent-bundle trivialization at neighborhood-times. -/
theorem eventually_mem_trivializationAt_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  (G.flow sol).eventually_mem_trivializationAt_eval hs x

/-- Fixed-IVP raw intrinsic gauge-flow curves eventually remain in the preferred
chart source at neighborhood-times. -/
theorem eventually_mem_extChartAt_source_eval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  (G.flow sol).eventually_mem_extChartAt_source_eval hs x

/-- Fixed-IVP open-Picard pointwise manifold derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasMFDerivAt_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) :=
  G.hasMFDerivAt sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard preferred-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard fixed-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) p
        (((G.flow sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_of_mem_source
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    p x hsrc_ext

/-- Fixed-IVP open-Picard pointwise manifold derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow sol).maps3 t) x))) :=
  G.hasMFDerivAt_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard preferred-chart derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) (((G.flow sol).maps3 t) x)
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x))) t :=
  G.hasDerivAt_extChartAt_eval_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard fixed-chart derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (p x : M)
    (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow sol).maps3 t) x) p
        (((G.flow sol).maps3 t) x) (Y t (((G.flow sol).maps3 t) x))) t :=
  (G.flow sol).hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY p x hsrc_ext

/-- Fixed-IVP open-Picard preferred-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow sol).maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard centered preferred-chart derivative readout rewritten
to a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow sol).maps3 τ) x) =
        Y τ (((G.flow sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x))
      (Y t (((G.flow sol).maps3 t) x)) t :=
  G.hasDerivAt_extChartAt_eval_self_congr_vectorField sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    hXY x

/-- Fixed-IVP open-Picard continuity of raw intrinsic gauge-flow curves in
preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow sol).maps3 t) x))
        (((G.flow sol).maps3 τ) x)) t :=
  G.continuousAt_extChartAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard fixed-chart continuity readout without an extra
neighborhood-of-time hypothesis. -/
theorem continuousAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow sol).maps3 τ) x)) t :=
  (G.flow sol).continuousAt_extChartAt_eval_of_mem_source
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    p x hsrc_ext

/-- Fixed-IVP open-Picard continuity of raw intrinsic gauge-flow curves. -/
theorem continuousAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow sol).maps3 τ) x) t :=
  G.continuousAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard tangent-trivialization control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow sol).maps3 t) x)).baseSet :=
  G.eventually_mem_trivializationAt_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard chart-source control of raw intrinsic gauge-flow
curves. -/
theorem eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow sol).maps3 τ) x ∈
        (extChartAt I (((G.flow sol).maps3 t) x)).source :=
  G.eventually_mem_extChartAt_source_eval sol
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht) x

/-- Fixed-IVP open-Picard fixed-chart source control of raw intrinsic gauge-flow
curves. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_source_of_timeSet_eq_Ioo
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow sol).maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝 t, ((G.flow sol).maps3 τ) x ∈ (extChartAt I p).source :=
  (G.flow sol).eventually_mem_extChartAt_source_eval_of_mem_source
    ((G.timeSet_mem_nhds_of_eq_Ioo (I := I) (M := M) tmin tmax htimeSet) sol ht)
    p x hsrc_ext

@[simp] theorem toDiffeomorph3GaugeFlow_maps3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.maps3 sol) = (G.flow sol).maps3 := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.anchored sol) = (G.flow sol).anchored := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_satisfies
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.satisfies sol) = (G.flow sol).satisfies := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlow.gauge sol) =
      (G.flow sol).toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn := rfl

end IntrinsicDeTurckGaugeFlowExistence

/-- The theorem-family version of raw intrinsic DeTurck `C^3` gauge-flow
existence data. -/
structure IntrinsicDeTurckGaugeFlowExistenceFamily where
  flow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime

namespace IntrinsicDeTurckGaugeFlowExistenceFamily

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from pointwise
manifold derivative data.  This is the family-level adapter expected from a
future compact-manifold ODE-flow construction. -/
noncomputable def of_hasMFDerivWithinAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasMFDerivWithinAt
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from pointwise
within-time-set manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivWithinAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivWithinAt maps3 anchored hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary pointwise manifold derivative data on each local solution's time set. -/
noncomputable def of_hasMFDerivAtOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasMFDerivAtOn
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
pointwise manifold derivative data on each local solution's time set, kept as
proof-level evidence. -/
theorem nonempty_of_hasMFDerivAtOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivAtOn maps3 anchored hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from primitive derivative data proved on closed Picard intervals. -/
noncomputable def ofPicardIccDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from primitive closed-Picard derivative data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccDerivative maps3 anchored tmin tmax htimeSet hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from preferred-chart ODE data proved on closed Picard intervals. -/
noncomputable def ofPicardIccChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hchart ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from preferred-chart closed-Picard data, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative maps3 anchored tmin tmax htimeSet hchart⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from fixed-chart ODE data proved on closed Picard intervals. -/
noncomputable def ofPicardIccFixedChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hfixed : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (chartCenter ivp sol) (Icc (tmin ivp sol) (tmax ivp sol))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccFixedChartDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (chartCenter ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hfixed ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from fixed-chart closed-Picard data, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hfixed : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (chartCenter ivp sol) (Icc (tmin ivp sol) (tmax ivp sol))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccFixedChartDerivative
    maps3 anchored chartCenter tmin tmax htimeSet hfixed⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard fixed-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields along the
candidate flows. -/
noncomputable def ofPicardIccFixedChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccFixedChartDerivative_of_vectorField_eq
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (chartCenter ivp) (Y ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hmem ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard fixed-chart model-vector-field ODE data, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccFixedChartDerivative_of_vectorField_eq
    maps3 anchored chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard fixed-chart ODE data for model vector fields, after
identifying those model fields with the intrinsic DeTurck gauge fields in the
closed-interval relative time filters. -/
noncomputable def ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (chartCenter ivp) (Y ivp)
      (tmin ivp) (tmax ivp) (htimeSet ivp) (hmem ivp) (hsource ivp)
      (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from fixed-chart
model-vector-field ODE data with a closed-interval relative-filter
intrinsic-field identification, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard preferred-chart ODE data for model vector fields,
after identifying those model fields with the intrinsic DeTurck gauge fields
along the candidate flows. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_vectorField_eq
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (Y ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard model-vector-field chart ODE data, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard preferred-chart ODE data for model vector fields,
after identifying those model fields with the intrinsic DeTurck gauge fields
along the candidate flows in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (Y ivp) (tmin ivp) (tmax ivp)
      (htimeSet ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from closed-Picard model-vector-field chart ODE data and
relative-filter field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_vectorField_eq_nhdsWithin
    maps3 anchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from globally glued inverse slices and closed-Picard preferred-chart
ODE data for model vector fields, after identifying those fields with the
intrinsic DeTurck gauge fields in the relative open-interval filters. -/
noncomputable def ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (hleft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, LeftInvOn (G ivp sol t) (F ivp sol t) Set.univ)
    (hright : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, RightInvOn (G ivp sol t) (F ivp sol t) Set.univ)
    (hF : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ContMDiffOn I I 3 (F ivp sol t) Set.univ)
    (hG : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ContMDiffOn I I 3 (G ivp sol t) Set.univ)
    (hanchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ x : M, F ivp sol ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ F ivp sol τ x) ⁻¹'
              (extChartAt I (F ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (F ivp sol τ x))
            ((Y ivp sol) t (F ivp sol t x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ (F ivp sol τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (F ivp sol τ x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (F ivp) (G ivp) (hleft ivp) (hright ivp) (hF ivp) (hG ivp)
        (hanchored ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from globally
glued inverse slices, closed-Picard chart ODE data, and relative-filter field
equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (hleft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, LeftInvOn (G ivp sol t) (F ivp sol t) Set.univ)
    (hright : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, RightInvOn (G ivp sol t) (F ivp sol t) Set.univ)
    (hF : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ContMDiffOn I I 3 (F ivp sol t) Set.univ)
    (hG : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ContMDiffOn I I 3 (G ivp sol t) Set.univ)
    (hanchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ x : M, F ivp sol ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ F ivp sol τ x) ⁻¹'
              (extChartAt I (F ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (F ivp sol τ x))
            ((Y ivp sol) t (F ivp sol t x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ (F ivp sol τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (F ivp sol τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin
    F G hleft hright hF hG hanchored Y tmin tmax htimeSet hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x)
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hcont ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x)
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data on each local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (maps3 ivp) (anchored ivp) (hcont ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data, kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          ContinuousAt (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self maps3 anchored hcont hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership on each local
solution's time set. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (hsource ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from centered
preferred-chart ODE data for model vector fields, after identifying those model
fields with the intrinsic DeTurck gauge fields along the candidate flows in the
relative solution-time filters. -/
noncomputable def of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from same-time-set
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x))
            sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data plus eventual chart-source membership on each
local solution's time set. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (hsource ivp) (hderiv ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data plus eventual chart-source membership, kept as
proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
centered preferred-chart ODE data for model vector fields, after identifying
those model fields with the intrinsic DeTurck gauge fields along the candidate
flows in the relative solution-time filters. -/
noncomputable def of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (maps3 ivp) (anchored ivp) (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from ordinary
model-vector-field chart ODE data and relative-filter RHS identification, kept
as proof-level evidence. -/
theorem nonempty_of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            ((Y ivp sol) t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
          ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAtOn_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    maps3 anchored Y hsource hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership. -/
noncomputable def of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t _ht x ↦ hsource ivp sol t x)
    (fun ivp sol t _ht x ↦ hderiv ivp sol t x)

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
ordinary centered preferred-chart ODE data plus eventual chart-source membership,
kept as proof-level evidence. -/
theorem nonempty_of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasDerivAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) t) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasDerivAt_extChartAt_eval_self_of_eventually_mem_source
    maps3 anchored hsource hderiv⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data. -/
noncomputable def of_hasMFDerivAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivAtOn (I := I) (M := M)
    maps3 anchored (fun ivp sol t _ht x ↦ hderiv ivp sol t x)

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from unrestricted
pointwise manifold derivative data, kept as proof-level evidence. -/
theorem nonempty_of_hasMFDerivAt
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ x : M,
          HasMFDerivAt 𝓘(ℝ) I
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t
                  ((maps3 ivp sol t) x)))) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨of_hasMFDerivAt maps3 anchored hderiv⟩

/-- If the intrinsic DeTurck gauge field vanishes on every theorem-family local
solution time set, the identity diffeomorphism family supplies raw `C³`
gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfGaugeFieldEqZero
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
      (hzero ivp)).flow sol

/-- Theorem-family zero-gauge-field identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfGaugeFieldEqZero
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfGaugeFieldEqZero hzero⟩

/-- Chosen-background intrinsic DeTurck solutions have the identity raw `C³` gauge flow for every
initial-value problem. -/
noncomputable def identityOfChosenBackground :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Chosen-background theorem-family identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfChosenBackground :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfChosenBackground⟩

/-- When every tangent fiber is a subsingleton, the identity `C³` diffeomorphism family supplies
the raw gauge-flow existence data for every initial-value problem. -/
noncomputable def identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Theorem-family subsingleton-tangent identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonTangent
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfSubsingletonTangent⟩

/-- Model-space version of `identityOfSubsingletonTangent`: when the model vector space `E` is a
subsingleton, the identity `C³` diffeomorphism family supplies raw gauge-flow existence data for
every initial-value problem. -/
noncomputable def identityOfSubsingletonModel
    [Subsingleton E] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  identityOfSubsingletonTangent (I := I) (M := M)

/-- Theorem-family subsingleton-model identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfSubsingletonModel
    [Subsingleton E] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfSubsingletonModel⟩

/-- On an empty manifold, the identity `C³` diffeomorphism family supplies the raw gauge-flow
existence data vacuously for every initial-value problem. -/
noncomputable def identityOfIsEmpty
    [IsEmpty M] :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M) ivp).flow sol

/-- Theorem-family empty-manifold identity raw-flow existence, kept as
proof-level evidence. -/
theorem nonempty_identityOfIsEmpty
    [IsEmpty M] :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨identityOfIsEmpty⟩

/-- Restrict theorem-family raw gauge-flow existence data to one initial-value
problem. -/
def forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := G.flow ivp

@[simp] theorem forInitialValueProblem_flow
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).flow sol) = G.flow ivp sol := rfl

/-- Restrict proof-level theorem-family raw gauge-flow existence to one
initial-value problem. -/
theorem nonempty_forInitialValueProblem
    (hG : Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases hG with ⟨G⟩
  exact ⟨G.forInitialValueProblem ivp⟩

/-- Turn theorem-family raw intrinsic gauge-flow existence data into the
geometric gauge-flow family consumed by endpoint routes. -/
def toDiffeomorph3GaugeFlowFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M) where
  maps3 := fun ivp sol ↦ (G.flow ivp sol).maps3
  anchored := fun ivp sol ↦ (G.flow ivp sol).anchored
  satisfies := fun ivp sol ↦ (G.flow ivp sol).satisfies

@[simp] theorem toDiffeomorph3GaugeFlowFamily_maps3
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.maps3 ivp sol) = (G.flow ivp sol).maps3 := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_anchored
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.anchored ivp sol) =
      (G.flow ivp sol).anchored := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_satisfies
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.satisfies ivp sol) =
      (G.flow ivp sol).satisfies := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_gauge
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.toDiffeomorph3GaugeFlowFamily.gauge ivp sol) =
      (G.flow ivp sol).toAnchoredIntrinsicDeTurckDiffeomorph3GaugeOn := rfl

/-- Package a theorem-family geometric intrinsic DeTurck gauge-flow bundle as raw
gauge-flow existence data. -/
def ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M)
      (G.forInitialValueProblem ivp)).flow sol

/-- Package a theorem-family geometric intrinsic DeTurck gauge-flow bundle as
proof-level raw gauge-flow existence data. -/
theorem nonempty_ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDiffeomorph3GaugeFlowFamily G⟩

/-- Proof-level conversion from theorem-family raw gauge-flow existence data to
the geometric gauge-flow family consumed by endpoint routes. -/
theorem nonempty_toDiffeomorph3GaugeFlowFamily
    (hG : Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))) :
    Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) := by
  rcases hG with ⟨G⟩
  exact ⟨G.toDiffeomorph3GaugeFlowFamily⟩

/-- Package theorem-family named derivative data as raw gauge-flow existence
data. -/
noncomputable def ofDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivWithinAt (I := I) (M := M)
    maps3 anchored hflowDeriv

/-- Package theorem-family named derivative data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDerivativeFamily maps3 anchored hflowDeriv⟩

/-- Package theorem-family within-time-set preferred-chart ODE data as raw
gauge-flow existence data. This is the named chart-data analogue of
theorem-family `of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivWithinAt_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).1)
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).2)

/-- Package theorem-family within-time-set preferred-chart ODE data as
proof-level raw gauge-flow existence data. -/
theorem nonempty_ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofChartDerivativeFamily maps3 anchored hchart⟩

/-- Theorem-family within-time-set preferred-chart ODE data also supplies the
existing within-time-set derivative-family view directly. -/
theorem derivativeFamily_ofChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_chartDerivativeFamily
    (I := I) (M := M) (maps3 := maps3) hchart

/-- Package theorem-family ordinary-at-time named derivative data as raw
gauge-flow existence data.  This is the named derivative-family analogue of
`of_hasMFDerivAtOn`. -/
noncomputable def ofDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasMFDerivAtOn (I := I) (M := M)
    maps3 anchored hflowDeriv

/-- Package theorem-family ordinary-at-time named derivative data as proof-level
raw gauge-flow existence data. -/
theorem nonempty_ofDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofDerivativeAtFamily maps3 anchored hflowDeriv⟩

/-- Package theorem-family preferred-chart ODE data as raw gauge-flow existence
data.  This is the named chart-data analogue of theorem-family
`of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source`. -/
noncomputable def ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) :=
  of_hasDerivAtOn_extChartAt_eval_self_of_eventually_mem_source
    (I := I) (M := M)
    maps3 anchored
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).1)
    (fun ivp sol t ht x ↦ (hchart ivp sol t ht x).2)

/-- Package theorem-family preferred-chart ODE data as proof-level raw gauge-flow
existence data. -/
theorem nonempty_ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofChartDerivativeAtFamily maps3 anchored hchart⟩

/-- Theorem-family ordinary preferred-chart ODE data also supplies the existing
within-time-set derivative-family view directly. -/
theorem derivativeFamily_ofChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_derivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
      (I := I) (M := M) (maps3 := maps3) hchart)

/-- Derivative-family data extracted directly from theorem-family raw intrinsic
DeTurck gauge-flow existence. -/
theorem derivativeFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M)
      (fun ivp sol ↦ (G.flow ivp sol).maps3) := by
  intro ivp sol
  exact (G.forInitialValueProblem ivp).derivativeData sol

/-- Pointwise manifold derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence. -/
theorem hasMFDerivWithinAt
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivWithinAt sol ht x

/-- Preferred-chart derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence. -/
theorem hasDerivWithinAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow derivatives in any preferred chart
whose source contains the time-`t` image. -/
theorem hasDerivWithinAt_extChartAt_eval_of_mem_source
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x) p
        (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_of_mem_source
    sol ht p x hsrc_ext

/-- Preferred-chart derivative read out directly from theorem-family raw intrinsic DeTurck
gauge-flow existence, simplified with the centered tangent-coordinate change. -/
theorem hasDerivWithinAt_extChartAt_eval_self
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_self sol ht x

/-- Theorem-family raw intrinsic gauge-flow derivatives can be rewritten to a
relative-neighborhood-equal vector field. -/
theorem hasMFDerivWithinAt_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivWithinAt_congr_vectorField sol ht hXY x

/-- Theorem-family raw intrinsic gauge-flow preferred-chart derivatives can be
rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_congr_vectorField
    sol ht hXY x

/-- Fixed-chart theorem-family version of
`IntrinsicDeTurckGaugeFlowExistenceFamily.hasDerivWithinAt_extChartAt_eval_congr_vectorField`. -/
theorem hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (p x : M) (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x) p
        (((G.flow ivp sol).maps3 t) x) (Y t (((G.flow ivp sol).maps3 t) x)))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_congr_vectorField_of_mem_source
    sol ht hXY p x hsrc_ext

/-- Theorem-family raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a relative-neighborhood-equal vector field. -/
theorem hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).hasDerivWithinAt_extChartAt_eval_self_congr_vectorField
    sol ht hXY x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous within the
solution time set in preferred chart coordinates. -/
theorem continuousWithinAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).continuousWithinAt_extChartAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous within the
solution time set in any preferred chart whose source contains the time-`t`
image. -/
theorem continuousWithinAt_extChartAt_eval_of_mem_source
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x))
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).continuousWithinAt_extChartAt_eval_of_mem_source
    sol ht p x hsrc_ext

/-- Theorem-family raw intrinsic gauge-flow curves are continuous within the
solution time set. -/
theorem continuousWithinAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet t :=
  (G.forInitialValueProblem ivp).continuousWithinAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves are continuous on the solution
time set. -/
theorem continuousOn_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) (x : M) :
    ContinuousOn (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x)
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).continuousOn_eval sol x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred tangent-bundle trivialization within the solution time set. -/
theorem eventuallyWithin_mem_trivializationAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventuallyWithin_mem_trivializationAt_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred chart source within the solution time set. -/
theorem eventuallyWithin_mem_extChartAt_source_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventuallyWithin_mem_extChartAt_source_eval sol ht x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in any
preferred chart source containing the time-`t` image. -/
theorem eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M) (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t,
      ((G.flow ivp sol).maps3 τ) x ∈ (extChartAt I p).source :=
  (G.forInitialValueProblem ivp).eventuallyWithin_mem_extChartAt_source_eval_of_mem_source
    sol ht p x hsrc_ext

/-- Theorem-family open-Picard solution time sets are neighborhoods of each of
their times when each solution time set has been identified with `Ioo tmin tmax`. -/
theorem timeSet_mem_nhds_of_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t := by
  intro ivp sol t ht
  exact (G.forInitialValueProblem ivp).timeSet_mem_nhds_of_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht

/-- Theorem-family open-Picard ordinary fixed-chart derivative data on any
subset of the chosen solution's open time set. -/
theorem fixedChartDerivativeAtData_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (chartCenter : ℝ → M → M) {u : Set ℝ}
    (hu : u ⊆ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hmem : ∀ t ∈ u, ∀ x : M,
      ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I (chartCenter t x)).source) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn (I := I) (M := M)
      (G.flow ivp sol).maps3
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      chartCenter u :=
  (G.forInitialValueProblem ivp).fixedChartDerivativeAtData_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp)
    sol chartCenter hu hmem

/-- Ordinary pointwise manifold derivative read out directly from theorem-family
raw intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasMFDerivAt
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt sol hs x

/-- Ordinary preferred-chart derivative read out directly from theorem-family raw
intrinsic DeTurck gauge-flow existence at neighborhood-times. -/
theorem hasDerivAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval sol hs x

/-- Ordinary preferred-chart derivative read out directly from theorem-family raw intrinsic DeTurck
gauge-flow existence at neighborhood-times, simplified with the centered tangent-coordinate change. -/
theorem hasDerivAt_extChartAt_eval_self
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self sol hs x

/-- Ordinary theorem-family raw intrinsic gauge-flow derivatives can be
rewritten to a neighborhood-equal vector field. -/
theorem hasMFDerivAt_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_congr_vectorField sol hs hXY x

/-- Ordinary theorem-family raw intrinsic gauge-flow preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_congr_vectorField
    sol hs hXY x

/-- Ordinary theorem-family raw intrinsic gauge-flow centered preferred-chart
derivatives can be rewritten to a neighborhood-equal vector field. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_congr_vectorField
    sol hs hXY x

/-- Theorem-family raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times in preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x)) t :=
  (G.forInitialValueProblem ivp).continuousAt_extChartAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves are ordinarily continuous at
neighborhood-times. -/
theorem continuousAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t :=
  (G.forInitialValueProblem ivp).continuousAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred tangent-bundle trivialization at neighborhood-times. -/
theorem eventually_mem_trivializationAt_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventually_mem_trivializationAt_eval sol hs x

/-- Theorem-family raw intrinsic gauge-flow curves eventually remain in the
preferred chart source at neighborhood-times. -/
theorem eventually_mem_extChartAt_source_eval
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (hs : sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventually_mem_extChartAt_source_eval sol hs x

/-- Theorem-family open-Picard pointwise manifold derivative readout without
an extra neighborhood-of-time hypothesis. -/
theorem hasMFDerivAt_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard preferred-chart derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard fixed-chart derivative readout without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x) p
        (((G.flow ivp sol).maps3 t) x)
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t
            (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp)
    sol ht p x hsrc_ext

/-- Theorem-family open-Picard pointwise manifold derivative readout rewritten
to a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (((G.flow ivp sol).maps3 t) x))) :=
  (G.forInitialValueProblem ivp).hasMFDerivAt_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard preferred-chart derivative readout rewritten to
a neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x)
        (((G.flow ivp sol).maps3 t) x) (((G.flow ivp sol).maps3 t) x)
        (Y t (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard fixed-chart derivative readout rewritten to a
neighborhood-equal vector field, without an extra neighborhood-of-time
hypothesis. -/
theorem hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (p x : M)
    (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x))
      (tangentCoordChange I (((G.flow ivp sol).maps3 t) x) p
        (((G.flow ivp sol).maps3 t) x) (Y t (((G.flow ivp sol).maps3 t) x))) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp)
    sol ht hXY p x hsrc_ext

/-- Theorem-family open-Picard preferred-chart derivative readout without an
extra neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background t
          (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard centered preferred-chart derivative readout
rewritten to a neighborhood-equal vector field, without an extra
neighborhood-of-time hypothesis. -/
theorem hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hXY : ∀ᶠ τ in 𝓝 t, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background τ
          (((G.flow ivp sol).maps3 τ) x) =
        Y τ (((G.flow ivp sol).maps3 τ) x))
    (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x))
      (Y t (((G.flow ivp sol).maps3 t) x)) t :=
  (G.forInitialValueProblem ivp).hasDerivAt_extChartAt_eval_self_congr_vectorField_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht hXY x

/-- Theorem-family open-Picard continuity of raw intrinsic gauge-flow curves in
preferred chart coordinates. -/
theorem continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I (((G.flow ivp sol).maps3 t) x))
        (((G.flow ivp sol).maps3 τ) x)) t :=
  (G.forInitialValueProblem ivp).continuousAt_extChartAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard fixed-chart continuity readout without an extra
neighborhood-of-time hypothesis. -/
theorem continuousAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    ContinuousAt
      (fun τ : ℝ ↦ (extChartAt I p) (((G.flow ivp sol).maps3 τ) x)) t :=
  (G.forInitialValueProblem ivp).continuousAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp)
    sol ht p x hsrc_ext

/-- Theorem-family open-Picard continuity of raw intrinsic gauge-flow curves. -/
theorem continuousAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ ((G.flow ivp sol).maps3 τ) x) t :=
  (G.forInitialValueProblem ivp).continuousAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard tangent-trivialization control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _)
          (((G.flow ivp sol).maps3 t) x)).baseSet :=
  (G.forInitialValueProblem ivp).eventually_mem_trivializationAt_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard chart-source control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet) (x : M) :
    ∀ᶠ τ in 𝓝 t,
      ((G.flow ivp sol).maps3 τ) x ∈
        (extChartAt I (((G.flow ivp sol).maps3 t) x)).source :=
  (G.forInitialValueProblem ivp).eventually_mem_extChartAt_source_eval_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp) sol ht x

/-- Theorem-family open-Picard fixed-chart source control of raw intrinsic
gauge-flow curves. -/
theorem eventually_mem_extChartAt_source_eval_of_mem_source_of_timeSet_eq_Ioo
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (p x : M)
    (hsrc_ext : ((G.flow ivp sol).maps3 t) x ∈ (extChartAt I p).source) :
    ∀ᶠ τ in 𝓝 t, ((G.flow ivp sol).maps3 τ) x ∈ (extChartAt I p).source :=
  (G.forInitialValueProblem ivp).eventually_mem_extChartAt_source_eval_of_mem_source_of_timeSet_eq_Ioo
    (I := I) (M := M) (tmin ivp) (tmax ivp) (htimeSet ivp)
    sol ht p x hsrc_ext

/-- The family-level chosen-background raw flow induces the same anchored gauge as the existing
identity `C³` gauge attached to a chosen-background solution. -/
theorem identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((identityOfChosenBackground
        (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol =
      sol.1.identityDiffeomorph3GaugeOn
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2) := by
  unfold ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.gauge
  unfold toDiffeomorph3GaugeFlowFamily identityOfChosenBackground
  unfold IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
  unfold IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn
  unfold identityDiffeomorph3GaugeOn_of_isLeviCivita
  unfold AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
  congr

/-- For the chosen-background identity raw gauge-flow family, the gauge-corrected pullback metric
has the original intrinsic DeTurck metric velocity. -/
theorem identityOfChosenBackground_hpullDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfChosenBackground
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let hbackground :=
    usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
  rw [identityOfChosenBackground_gauge_eq_identityDiffeomorph3GaugeOn
    (E := E) (H := H) (I := I) (M := M) ivp sol,
    sol.1.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity hbackground]
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    sol.1.toIntrinsicDeTurckSolution.metricVelocity
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution

/-- For any theorem-family whose intrinsic DeTurck gauge field vanishes on each
solution's time set, the identity raw gauge-flow family supplies the required
pullback metric time derivative. -/
theorem identityOfGaugeFieldEqZero_hpullDerivative
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) hzero).toDiffeomorph3GaugeFlowFamily).maps3
            ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfGaugeFieldEqZero
          (E := E) (H := H) (I := I) (M := M) hzero).toDiffeomorph3GaugeFlowFamily).gauge
            ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  let gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
      (I := I) (M := M)
      (g := sol.1.toIntrinsicDeTurckSolution.metric)
      (background := sol.1.toIntrinsicDeTurckSolution.background)
      (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
      (t₀ := ivp.initialTime)
      (hzero ivp sol)
  change HasTimeDerivativeOn (I := I) (M := M)
    ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric)
    (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    sol.1.toIntrinsicDeTurckSolution.timeSet
  rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily]
  intro t ht x u v
  have hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t
  have hx : (gauge3.maps t) x = x := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x = x
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x
  have hu : (gauge3.maps t).pushforwardTangent x u = u := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x u = u
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
  have hv : (gauge3.maps t).pushforwardTangent x v = v := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x v = v
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
  have hvec :
      sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t = 0 := by
    rw [sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField]
    have hsource :
        intrinsicDeTurckVectorField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t = 0 := by
      funext y
      simpa [intrinsicDeTurckGaugeField] using hzero ivp sol t ht y
    rw [hsource]
    funext y
    rw [SmoothSelfDiffeomorph2.pullbackVectorField_apply]
    exact ContinuousLinearMap.map_zero ((gauge3.maps t).pullbackTangent y)
  let pulledConnection :=
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric) t
  have hcov :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) = 0 := by
    rw [hvec]
    exact CovariantDerivative.zero (cov := pulledConnection)
  have hcovu :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u = 0 := by
    exact congrArg (fun A => A u) (congrFun hcov x)
  have hcovv :
      pulledConnection (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v = 0 := by
    exact congrArg (fun A => A v) (congrFun hcov x)
  have hleft :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    rw [hcovu]
    exact congrArg (fun L : (TangentSpace I : M → Type _) x →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.map_zero
        (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x))
  have hright :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          (pulledConnection
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    rw [hcovv]
    exact ContinuousLinearMap.map_zero
      (((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u)
  have hleftExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    simpa [pulledConnection] using hleft
  have hrightExact :
      ((gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric) t)
            (sol.1.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    simpa [pulledConnection] using hright
  have hpoint :
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    change sol.1.toIntrinsicDeTurckSolution.metricVelocity t
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x) u v =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v
    rw [SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x]
  have hvelocity :
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        sol.1.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
    rw [hu, hv, hleftExact, hrightExact, zero_add, sub_zero]
    exact hpoint
  rw [hvelocity]
  exact intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution ht x u v

@[simp] theorem toDiffeomorph3GaugeFlowFamily_forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (G.toDiffeomorph3GaugeFlowFamily.forInitialValueProblem ivp) =
      (G.forInitialValueProblem ivp).toDiffeomorph3GaugeFlow := rfl

/-- For the subsingleton-tangent identity raw gauge-flow family, the gauge-corrected pullback
metric has the original intrinsic DeTurck metric velocity. The proof routes through the
chosen-background `_hpullDerivative` because both constructors produce the same identity flow. -/
theorem identityOfSubsingletonTangent_hpullDerivative
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfSubsingletonTangent
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfSubsingletonTangent
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  identityOfChosenBackground_hpullDerivative
    (E := E) (H := H) (I := I) (M := M) ivp sol

/-- Model-space variant of `identityOfSubsingletonTangent_hpullDerivative`. -/
theorem identityOfSubsingletonModel_hpullDerivative
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfSubsingletonModel
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfSubsingletonModel
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  identityOfChosenBackground_hpullDerivative
    (E := E) (H := H) (I := I) (M := M) ivp sol

/-- For the empty-manifold identity raw gauge-flow family, the gauge-corrected pullback metric
has the original intrinsic DeTurck metric velocity vacuously. -/
theorem identityOfIsEmpty_hpullDerivative
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.pullbackMetricFamily
        (I := I) (M := M)
        (((identityOfIsEmpty
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (((identityOfIsEmpty
          (E := E) (H := H) (I := I) (M := M)).toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro t _ht x
  exact isEmptyElim x

end IntrinsicDeTurckGaugeFlowExistenceFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible directly from raw
intrinsic `C^3` gauge-flow existence data and a pulled-back metric time-derivative proof. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G.toDiffeomorph3GaugeFlowFamily hpullDerivative

/-- Intrinsic Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistenceTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toOrdinary

/-- Gauge-reducible theorem-family projection when the intrinsic DeTurck gauge
field vanishes on each solution's time set.

This uses the identity raw `C³` gauge-flow family and the bundled zero-field
pullback time-derivative theorem, so callers only provide the pointwise gauge
field vanishing hypothesis. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) hzero)
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfGaugeFieldEqZero_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) hzero)

/-- Intrinsic Ricci-flow theorem-family projection from a chosen DeTurck package
whose intrinsic DeTurck gauge field vanishes on each solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFieldEqZero hzero).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a chosen DeTurck package
whose intrinsic DeTurck gauge field vanishes on each solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFieldEqZero
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (hzero : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFieldEqZero hzero).toOrdinary

/-- A chosen-background DeTurck theorem family becomes gauge-reducible directly from raw
intrinsic `C^3` gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G.toDiffeomorph3GaugeFlowFamily hderiv

/-- Intrinsic Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistenceInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ) x)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x u)
                  ((((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol) τ).pushforwardTangent
                    x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toOrdinary

/-- A fixed-IVP chosen-background DeTurck theorem package becomes gauge-reducible directly from
raw intrinsic `C^3` gauge-flow existence data and a pulled-back metric time-derivative proof. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G.toDiffeomorph3GaugeFlow hpullDerivative

/-- Fixed-IVP intrinsic Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and pulled-back metric time-derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistenceTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistenceTimeDerivative
    G hpullDerivative).toOrdinary

/-- Fixed-IVP gauge-reducible projection when the intrinsic DeTurck gauge field
vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaGaugeFlowExistenceTimeDerivative
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp) hzero)
    (IntrinsicDeTurckGaugeFlowExistence.identityOfGaugeFieldEqZero_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) (ivp := ivp) hzero)

/-- Fixed-IVP intrinsic Ricci-flow projection when the intrinsic DeTurck gauge
field vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFieldEqZero hzero).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow projection when the intrinsic DeTurck gauge
field vanishes on each chosen solution's time set. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFieldEqZero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background t x = 0) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFieldEqZero hzero).toOrdinary

/-- A fixed-IVP chosen-background DeTurck theorem package becomes gauge-reducible directly from
raw intrinsic `C^3` gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G.toDiffeomorph3GaugeFlow hderiv

/-- Fixed-IVP intrinsic Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toIntrinsic

/-- Fixed-IVP ordinary Ricci-flow theorem-package projection directly from raw intrinsic `C^3`
gauge-flow existence data and scalar inner-product derivative proofs. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistenceInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ) x)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x u)
                ((((G.toDiffeomorph3GaugeFlow).maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlow).gauge sol) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistenceInnerDerivative
    G hderiv).toOrdinary

end RicciFlow
