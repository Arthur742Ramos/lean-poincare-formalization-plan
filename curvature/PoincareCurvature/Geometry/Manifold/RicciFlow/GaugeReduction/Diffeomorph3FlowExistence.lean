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

/-- A canonical global map obtained by choosing one local readout on an indexed
cover.  Outside the covered locus it falls back to `default`; on covered
domains, compatibility on overlaps makes the choice independent. -/
noncomputable def gluedMapOf_iUnion {ι : Type*}
    (default : X → Y) (U : ι → Set X) (Fₗ : ι → X → Y) : X → Y :=
  fun x ↦ by
    classical
    exact if hx : ∃ i, x ∈ U i then Fₗ (Classical.choose hx) x else default x

/-- The canonical glued map agrees with each local readout on that readout's
visible set, provided the local readouts agree on pairwise overlaps. -/
theorem gluedMapOf_iUnion_eqOn
    {ι : Type*} {default : X → Y} {U : ι → Set X} {Fₗ : ι → X → Y}
    (hcompat : ∀ i j, EqOn (Fₗ i) (Fₗ j) (U i ∩ U j)) :
    ∀ i, EqOn (gluedMapOf_iUnion default U Fₗ) (Fₗ i) (U i) := by
  classical
  intro i x hxU
  have hxcover : ∃ j, x ∈ U j := ⟨i, hxU⟩
  rw [gluedMapOf_iUnion, dif_pos hxcover]
  exact hcompat (Classical.choose hxcover) i ⟨Classical.choose_spec hxcover, hxU⟩

/-- Pointwise source persistence lets a time-dependent canonical glued map
agree eventually with the local readout that contains the base point. -/
theorem gluedMapOf_iUnion_eventually_eq_of_pointwiseSource
    {ι : Type*} {default : ℝ → X → Y} {U : ℝ → ι → Set X}
    {Fₗ : ι → ℝ → X → Y} {s : Set ℝ}
    (hcompat : ∀ τ : ℝ, ∀ i j, EqOn (Fₗ i τ) (Fₗ j τ) (U τ i ∩ U τ j))
    (hsource : ∀ t ∈ s, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[s] t, x ∈ U τ i) :
    ∀ t ∈ s, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[s] t,
        gluedMapOf_iUnion (default τ) (U τ) (fun j ↦ Fₗ j τ) x = Fₗ i τ x := by
  intro t ht i x hx
  have hEq : ∀ τ : ℝ, ∀ i,
      EqOn (gluedMapOf_iUnion (default τ) (U τ) (fun j ↦ Fₗ j τ))
        (Fₗ i τ) (U τ i) := by
    intro τ
    exact gluedMapOf_iUnion_eqOn
      (default := default τ) (U := U τ) (Fₗ := fun j ↦ Fₗ j τ)
      (hcompat τ)
  exact (hsource t ht i x hx).mono fun τ hτ ↦ hEq τ i hτ

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

/-- Pointwise time-continuity glues from a local readout covering the base
point, provided the glued time slices agree with that readout in the relative
time filter and agree at the base time.  This is the temporal analogue of the
open-cover continuity gluing used for fixed time slices. -/
theorem continuousWithinAt_eval_of_iUnion_eventuallyEqOn_continuousWithinAt
    {ι : Type*} {F : ℝ → X → Y} {G : ι → ℝ → X → Y}
    {s : Set ℝ} {t : ℝ} {U : ι → Set X} {x : X}
    (hcover : x ∈ ⋃ i, U i)
    (hcont : ∀ i, ContinuousWithinAt (fun τ : ℝ ↦ G i τ x) s t)
    (heq : ∀ i, ∀ᶠ τ in 𝓝[s] t, EqOn (F τ) (G i τ) (U i))
    (heq_t : ∀ i, EqOn (F t) (G i t) (U i)) :
    ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t := by
  rcases Set.mem_iUnion.mp hcover with ⟨i, hxU⟩
  exact (hcont i).congr_of_eventuallyEq
    ((heq i).mono fun τ hτ ↦ hτ hxU)
    (heq_t i hxU)

/-- Pointwise time-continuity glues from local readouts when the glued time
slices agree with the readouts on the chosen cover for all times. -/
theorem continuousWithinAt_eval_of_iUnion_eqOn_continuousWithinAt
    {ι : Type*} {F : ℝ → X → Y} {G : ι → ℝ → X → Y}
    {s : Set ℝ} {t : ℝ} {U : ι → Set X} {x : X}
    (hcover : x ∈ ⋃ i, U i)
    (hcont : ∀ i, ContinuousWithinAt (fun τ : ℝ ↦ G i τ x) s t)
    (heq : ∀ i, ∀ τ : ℝ, EqOn (F τ) (G i τ) (U i)) :
    ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t :=
  continuousWithinAt_eval_of_iUnion_eventuallyEqOn_continuousWithinAt
    hcover hcont
    (fun i ↦ Filter.Eventually.of_forall fun τ ↦ heq i τ)
    (fun i ↦ heq i t)

/-- Pointwise time-continuity glues across a time-dependent indexed cover when
the selected base-time patch persists for the base point in the relative time
filter. -/
theorem continuousWithinAt_eval_of_timeDependent_iUnion_pointwiseSource_continuousWithinAt
    {ι : Type*} {F : ℝ → X → Y} {G : ι → ℝ → X → Y}
    {s : Set ℝ} {t : ℝ} {U : ℝ → ι → Set X} {x : X}
    (hcover : x ∈ ⋃ i, U t i)
    (hcont : ∀ i, x ∈ U t i → ContinuousWithinAt (fun τ : ℝ ↦ G i τ x) s t)
    (heq : ∀ τ : ℝ, ∀ i, EqOn (F τ) (G i τ) (U τ i))
    (hsource : ∀ i, x ∈ U t i → ∀ᶠ τ in 𝓝[s] t, x ∈ U τ i) :
    ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t := by
  rcases Set.mem_iUnion.mp hcover with ⟨i, hxU⟩
  exact (hcont i hxU).congr_of_eventuallyEq
    ((hsource i hxU).mono fun τ hτ ↦ heq τ i hτ)
    (heq t i hxU)

/-- If time-dependent source patches are preimages of fixed open target patches
along pointwise time-continuous trajectories, membership in a base-time patch
persists in the relative time filter.  This supplies the pointwise
source-persistence hypothesis used by compatible glued-slice constructors. -/
theorem timeDependent_iUnion_pointwiseSource_of_open_preimage_continuousWithinAt
    {ι : Type*} {F : ℝ → X → Y} {s : Set ℝ}
    {U : ℝ → ι → Set X} {V : ι → Set Y}
    (hU : ∀ τ i x, x ∈ U τ i ↔ F τ x ∈ V i)
    (hVopen : ∀ i, IsOpen (V i))
    (hcont : ∀ t ∈ s, ∀ i, ∀ x ∈ U t i,
      ContinuousWithinAt (fun τ : ℝ ↦ F τ x) s t) :
    ∀ t ∈ s, ∀ i, ∀ x ∈ U t i, ∀ᶠ τ in 𝓝[s] t, x ∈ U τ i := by
  intro t ht i x hx
  have hFx : F t x ∈ V i := (hU t i x).1 hx
  filter_upwards
    [(hcont t ht i x hx).preimage_mem_nhdsWithin ((hVopen i).mem_nhds hFx)]
    with τ hτ
  exact (hU τ i x).2 hτ

/-- Indexed-readout version of
`timeDependent_iUnion_pointwiseSource_of_open_preimage_continuousWithinAt`.
This is the form used when each cover patch has its own local time-dependent
map. -/
theorem timeDependent_iUnion_pointwiseSource_of_indexed_open_preimage_continuousWithinAt
    {ι : Type*} {F : ι → ℝ → X → Y} {s : Set ℝ}
    {U : ℝ → ι → Set X} {V : ι → Set Y}
    (hU : ∀ τ i x, x ∈ U τ i ↔ F i τ x ∈ V i)
    (hVopen : ∀ i, IsOpen (V i))
    (hcont : ∀ t ∈ s, ∀ i, ∀ x ∈ U t i,
      ContinuousWithinAt (fun τ : ℝ ↦ F i τ x) s t) :
    ∀ t ∈ s, ∀ i, ∀ x ∈ U t i, ∀ᶠ τ in 𝓝[s] t, x ∈ U τ i := by
  intro t ht i x hx
  have hFx : F i t x ∈ V i := (hU t i x).1 hx
  filter_upwards
    [(hcont t ht i x hx).preimage_mem_nhdsWithin ((hVopen i).mem_nhds hFx)]
    with τ hτ
  exact (hU τ i x).2 hτ

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

/-- Canonically glued compatible local forward/backward readouts are left
inverse on a covered source domain when each local forward readout maps its
source patch into the corresponding backward patch. -/
theorem leftInvOn_gluedMapOf_iUnion
    {ι : Type*} {defaultF : X → Y} {defaultG : Y → X}
    {Fₗ : ι → X → Y} {Gₗ : ι → Y → X}
    {s : Set X} {U : ι → Set X} {V : ι → Set Y}
    (hcover : s ⊆ ⋃ i, U i)
    (hFcompat : ∀ i j, EqOn (Fₗ i) (Fₗ j) (U i ∩ U j))
    (hGcompat : ∀ i j, EqOn (Gₗ i) (Gₗ j) (V i ∩ V j))
    (hmaps : ∀ i, MapsTo (Fₗ i) (s ∩ U i) (V i))
    (hleft : ∀ i, LeftInvOn (Gₗ i) (Fₗ i) (s ∩ U i)) :
    LeftInvOn (gluedMapOf_iUnion defaultG V Gₗ)
      (gluedMapOf_iUnion defaultF U Fₗ) s := by
  let F := gluedMapOf_iUnion defaultF U Fₗ
  let G := gluedMapOf_iUnion defaultG V Gₗ
  have hFEq : ∀ i, EqOn F (Fₗ i) (U i) := by
    simpa [F] using
      (gluedMapOf_iUnion_eqOn (default := defaultF) (U := U) (Fₗ := Fₗ) hFcompat)
  have hGEq : ∀ i, EqOn G (Gₗ i) (V i) := by
    simpa [G] using
      (gluedMapOf_iUnion_eqOn (default := defaultG) (U := V) (Fₗ := Gₗ) hGcompat)
  exact leftInvOn_of_iUnion_eqOn_leftInvOn
    (F := F) (G := G) (Fₗ := Fₗ) (Gₗ := Gₗ)
    (s := s) (U := U) hcover
    (fun i x hx ↦ hFEq i hx.2)
    (fun i y hy ↦ by
      rcases hy with ⟨x, hx, rfl⟩
      have hFx : F x = Fₗ i x := hFEq i hx.2
      have hV : F x ∈ V i := by
        rw [hFx]
        exact hmaps i hx
      exact hGEq i hV)
    hleft

/-- Canonically glued compatible local forward/backward readouts are right
inverse on a covered target domain when each local backward readout maps its
target patch into the corresponding forward patch. -/
theorem rightInvOn_gluedMapOf_iUnion
    {ι : Type*} {defaultF : X → Y} {defaultG : Y → X}
    {Fₗ : ι → X → Y} {Gₗ : ι → Y → X}
    {t : Set Y} {U : ι → Set X} {V : ι → Set Y}
    (hcover : t ⊆ ⋃ i, V i)
    (hFcompat : ∀ i j, EqOn (Fₗ i) (Fₗ j) (U i ∩ U j))
    (hGcompat : ∀ i j, EqOn (Gₗ i) (Gₗ j) (V i ∩ V j))
    (hmaps : ∀ i, MapsTo (Gₗ i) (t ∩ V i) (U i))
    (hright : ∀ i, RightInvOn (Gₗ i) (Fₗ i) (t ∩ V i)) :
    RightInvOn (gluedMapOf_iUnion defaultG V Gₗ)
      (gluedMapOf_iUnion defaultF U Fₗ) t := by
  let F := gluedMapOf_iUnion defaultF U Fₗ
  let G := gluedMapOf_iUnion defaultG V Gₗ
  have hFEq : ∀ i, EqOn F (Fₗ i) (U i) := by
    simpa [F] using
      (gluedMapOf_iUnion_eqOn (default := defaultF) (U := U) (Fₗ := Fₗ) hFcompat)
  have hGEq : ∀ i, EqOn G (Gₗ i) (V i) := by
    simpa [G] using
      (gluedMapOf_iUnion_eqOn (default := defaultG) (U := V) (Fₗ := Gₗ) hGcompat)
  exact rightInvOn_of_iUnion_eqOn_rightInvOn
    (F := F) (G := G) (Fₗ := Fₗ) (Gₗ := Gₗ)
    (t := t) (V := V) hcover
    (fun i y hy ↦ hGEq i hy.2)
    (fun i x hx ↦ by
      rcases hx with ⟨y, hy, rfl⟩
      have hGy : G y = Gₗ i y := hGEq i hy.2
      have hU : G y ∈ U i := by
        rw [hGy]
        exact hmaps i hy
      exact hFEq i hU)
    hright

/-- If two local forward maps agree on the overlap of their source patches,
then their local inverse readouts agree on the image of that overlap under the
first forward map. -/
theorem eqOn_localInverses_on_left_image_inter_of_eqOn_forward
    {F₀ F₁ : X → Y} {G₀ G₁ : Y → X} {U₀ U₁ : Set X}
    (hF : EqOn F₀ F₁ (U₀ ∩ U₁))
    (hleft₀ : LeftInvOn G₀ F₀ U₀)
    (hleft₁ : LeftInvOn G₁ F₁ U₁) :
    EqOn G₀ G₁ (F₀ '' (U₀ ∩ U₁)) := by
  rintro _ ⟨x, hx, rfl⟩
  calc
    G₀ (F₀ x) = x := hleft₀ hx.1
    _ = G₁ (F₁ x) := (hleft₁ hx.2).symm
    _ = G₁ (F₀ x) := by rw [hF hx]

/-- If two local forward maps agree on the overlap of their source patches,
then their local inverse readouts agree on the image of that overlap under the
second forward map. -/
theorem eqOn_localInverses_on_right_image_inter_of_eqOn_forward
    {F₀ F₁ : X → Y} {G₀ G₁ : Y → X} {U₀ U₁ : Set X}
    (hF : EqOn F₀ F₁ (U₀ ∩ U₁))
    (hleft₀ : LeftInvOn G₀ F₀ U₀)
    (hleft₁ : LeftInvOn G₁ F₁ U₁) :
    EqOn G₀ G₁ (F₁ '' (U₀ ∩ U₁)) := by
  rintro _ ⟨x, hx, rfl⟩
  calc
    G₀ (F₁ x) = G₀ (F₀ x) := by rw [hF hx]
    _ = x := hleft₀ hx.1
    _ = G₁ (F₁ x) := (hleft₁ hx.2).symm

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

/-- The inverse of a model open partial homeomorphism, lifted through source
and target charts, maps the lifted target image back to the lifted source
image.  This is the local backward `MapsTo` fact used by compatible
forward/backward gluing. -/
theorem mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_inverse_mapsTo
    (e₀ e₁ : OpenPartialHomeomorph X Y) {φ : OpenPartialHomeomorph Y Y}
    {U W : Set Y}
    (hUsource : U ⊆ φ.source) (hW : W = φ '' U) (hWt : W ⊆ e₁.target) :
    MapsTo (fun x : X ↦ e₀.symm (φ.symm (e₁ x))) (e₁.symm '' W) (e₀.symm '' U) := by
  rintro _ ⟨y, hyW, rfl⟩
  have hyφ : y ∈ φ '' U := by simpa [hW] using hyW
  rcases hyφ with ⟨u, huU, rfl⟩
  have hφuW : φ u ∈ W := by
    rw [hW]
    exact ⟨u, huU, rfl⟩
  refine ⟨u, huU, ?_⟩
  calc
    e₀.symm u = e₀.symm (φ.symm (φ u)) := by
      rw [φ.left_inv (hUsource huU)]
    _ = e₀.symm (φ.symm (e₁ (e₁.symm (φ u)))) := by
      rw [e₁.right_inv (hWt hφuW)]

/-- Left-inverse identity for a chart-lifted model open partial homeomorphism
and its lifted inverse on an explicit source patch. -/
theorem leftInvOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
    (e₀ e₁ : OpenPartialHomeomorph X Y) {G : Y → Y}
    {φ : OpenPartialHomeomorph Y Y} (hφ : (φ : Y → Y) = G)
    {U W : Set Y}
    (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hW : W = φ '' U) (hWt : W ⊆ e₁.target) :
    LeftInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
      (fun z : X ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) := by
  rintro _ ⟨y, hyU, rfl⟩
  have hytarget : y ∈ e₀.target := hUt hyU
  have hGyW : G y ∈ W := by
    rw [← hφ, hW]
    exact ⟨y, hyU, rfl⟩
  have hGytarget : G y ∈ e₁.target := hWt hGyW
  calc
    (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
        ((fun z : X ↦ e₁.symm (G (e₀ z))) (e₀.symm y))
        = e₀.symm (φ.symm (G y)) := by
          simp [e₀.right_inv hytarget, e₁.right_inv hGytarget]
    _ = e₀.symm (φ.symm (φ y)) := by
          simpa [hφ]
    _ = e₀.symm y := by
          rw [φ.left_inv (hUsource hyU)]

/-- Right-inverse identity for a chart-lifted model open partial homeomorphism
and its lifted inverse on an explicit target patch. -/
theorem rightInvOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
    (e₀ e₁ : OpenPartialHomeomorph X Y) {G : Y → Y}
    {φ : OpenPartialHomeomorph Y Y} (hφ : (φ : Y → Y) = G)
    {U W : Set Y}
    (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hW : W = φ '' U) (hWt : W ⊆ e₁.target) :
    RightInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
      (fun z : X ↦ e₁.symm (G (e₀ z))) (e₁.symm '' W) := by
  rintro _ ⟨y, hyW, rfl⟩
  have hyφ : y ∈ φ '' U := by simpa [hW] using hyW
  rcases hyφ with ⟨u, huU, rfl⟩
  have hutarget : u ∈ e₀.target := hUt huU
  have hφutarget : φ u ∈ e₁.target := hWt (by
    rw [hW]
    exact ⟨u, huU, rfl⟩)
  calc
    (fun z : X ↦ e₁.symm (G (e₀ z)))
        ((fun z : X ↦ e₀.symm (φ.symm (e₁ z))) (e₁.symm (φ u)))
        = e₁.symm (G (e₀ (e₀.symm (φ.symm (φ u))))) := by
          simp [e₁.right_inv hφutarget]
    _ = e₁.symm (G (e₀ (e₀.symm u))) := by
          rw [φ.left_inv (hUsource huU)]
    _ = e₁.symm (G u) := by
          rw [e₀.right_inv hutarget]
    _ = e₁.symm (φ u) := by
          simpa [hφ]

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

/-- Shrink a lifted model inverse patch inside prescribed model chart domains,
retaining the lifted inverse readout and its local left/right inverse
identities.  This is the inverse-identity companion to
`exists_open_nhds_continuousOn_bijOn_subset_of_lifted_openPartialHomeomorph_model`:
the returned backward map is the chart lift of `φ.symm`, where `φ` is the
model-space open partial homeomorphism whose forward map is `G`. -/
theorem exists_open_nhds_continuousOn_bijOn_inverseOn_subset_of_lifted_openPartialHomeomorph_model
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
              BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm ∧
                LeftInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
                  (fun z : X ↦ e₁.symm (G (e₀ z))) Um ∧
                  RightInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
                    (fun z : X ↦ e₁.symm (G (e₀ z))) Wm := by
  let U : Set Y := φ.source ∩ S ∩ φ ⁻¹' T
  let W : Set Y := φ '' U
  have hxTφ : φ (e₀ x) ∈ T := by
    simpa [hφ] using hxT
  have hUopen : IsOpen U := by
    have hpre : IsOpen (φ.source ∩ φ ⁻¹' T) := φ.isOpen_inter_preimage hTopen
    simpa [U, inter_assoc, inter_left_comm, inter_comm] using hpre.inter hSopen
  have hxU : e₀ x ∈ U := ⟨⟨hxφ, hxS⟩, hxTφ⟩
  have hUsource : U ⊆ φ.source := fun _ hz ↦ hz.1.1
  have hUS : U ⊆ S := fun _ hz ↦ hz.1.2
  have hWopen : IsOpen W := φ.isOpen_image_of_subset_source hUopen hUsource
  have hWT : W ⊆ T := by
    rintro _ ⟨z, hzU, rfl⟩
    exact hzU.2
  have hUt : U ⊆ e₀.target := fun y hy ↦ hS (hUS hy)
  have hWt : W ⊆ e₁.target := fun y hy ↦ hT (hWT hy)
  have hbijφ : BijOn φ U W := (φ.injOn.mono hUsource).bijOn_image
  have hbij : BijOn G U W :=
    hbijφ.congr (fun _ _ ↦ by simpa [hφ])
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
  have hbij_lift :
      BijOn (fun z : X ↦ e₁.symm (G (e₀ z))) Um Wm :=
    bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
      e₀ e₁ G hUt hWt hbij
  have hleft : LeftInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
      (fun z : X ↦ e₁.symm (G (e₀ z))) Um := by
    rintro _ ⟨y, hyU, rfl⟩
    have hytarget : y ∈ e₀.target := hUt hyU
    have hGyW : G y ∈ W := hbij.mapsTo hyU
    have hGytarget : G y ∈ e₁.target := hWt hGyW
    calc
      (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
          ((fun z : X ↦ e₁.symm (G (e₀ z))) (e₀.symm y))
          = e₀.symm (φ.symm (G y)) := by
            simp [e₀.right_inv hytarget, e₁.right_inv hGytarget]
      _ = e₀.symm (φ.symm (φ y)) := by
            simpa [hφ]
      _ = e₀.symm y := by
            rw [φ.left_inv (hUsource hyU)]
  have hright : RightInvOn (fun z : X ↦ e₀.symm (φ.symm (e₁ z)))
      (fun z : X ↦ e₁.symm (G (e₀ z))) Wm := by
    rintro _ ⟨y, hyW, rfl⟩
    rcases hyW with ⟨u, huU, rfl⟩
    have hutarget : u ∈ e₀.target := hUt huU
    have hφutarget : φ u ∈ e₁.target := hWt ⟨u, huU, rfl⟩
    calc
      (fun z : X ↦ e₁.symm (G (e₀ z)))
          ((fun z : X ↦ e₀.symm (φ.symm (e₁ z))) (e₁.symm (φ u)))
          = e₁.symm (G (e₀ (e₀.symm (φ.symm (φ u))))) := by
            simp [e₁.right_inv hφutarget]
      _ = e₁.symm (G (e₀ (e₀.symm u))) := by
            rw [φ.left_inv (hUsource huU)]
      _ = e₁.symm (G u) := by
            rw [e₀.right_inv hutarget]
      _ = e₁.symm (φ u) := by
            simpa [hφ]
  exact ⟨Um, Wm,
    e₀.isOpen_image_symm_of_subset_target hUopen hUt,
    hxUm,
    hUmSx,
    e₁.isOpen_image_symm_of_subset_target hWopen hWt,
    hFxWm,
    hWmTx,
    hcont_lift,
    hbij_lift,
    hleft,
    hright⟩

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

/-- Local manifold gluing data for one forward/backward time slice.

This packages the open source/target patches, forward/backward `MapsTo`
statements, `C^n` regularity of both lifted slices, and local inverse
identities produced by chartwise inverse-function arguments. -/
structure LocalGluingData
    (n : WithTop ℕ∞) (F G : M → M) (U V : Set M) : Prop where
  source_open : IsOpen U
  target_open : IsOpen V
  forward_mapsTo : MapsTo F (Set.univ ∩ U) V
  backward_mapsTo : MapsTo G (Set.univ ∩ V) U
  forward_contMDiffOn : ContMDiffOn I I n F U
  backward_contMDiffOn : ContMDiffOn I I n G V
  left_invOn : LeftInvOn G F (Set.univ ∩ U)
  right_invOn : RightInvOn G F (Set.univ ∩ V)

/-- Smoothness of a model map transports through source and target chart
partials once the chart maps are smooth on the visible patches.  This is the
`ContMDiffOn` counterpart of the lifted-model continuity bridge above, aimed
at producing local `C^3` slices for the glued manifold flow. -/
theorem contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model
    {n : WithTop ℕ∞} (e₀ e₁ : OpenPartialHomeomorph M H) (G : H → H)
    {U W : Set H}
    (hUt : U ⊆ e₀.target) (hWt : W ⊆ e₁.target)
    (he₀ : ContMDiffOn I I n (fun x : M ↦ e₀ x) (e₀.symm '' U))
    (hG : ContMDiffOn I I n G U)
    (he₁symm : ContMDiffOn I I n (fun y : H ↦ e₁.symm y) W)
    (hmaps : MapsTo G U W) :
    ContMDiffOn I I n (fun x : M ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) := by
  have he₀maps : MapsTo (fun x : M ↦ e₀ x) (e₀.symm '' U) U := by
    rintro _ ⟨y, hyU, rfl⟩
    simpa [e₀.right_inv (hUt hyU)] using hyU
  have hG_comp : ContMDiffOn I I n (fun x : M ↦ G (e₀ x)) (e₀.symm '' U) :=
    hG.comp he₀ he₀maps
  have hGmaps : MapsTo (fun x : M ↦ G (e₀ x)) (e₀.symm '' U) W := by
    intro x hx
    exact hmaps (he₀maps hx)
  exact he₁symm.comp hG_comp hGmaps

/-- Atlas-member specialization of
`contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model`.  Smooth source
and target chart readouts are supplied by membership in the `C^∞` maximal
atlas, leaving only the model-map regularity and model `MapsTo` data as inputs. -/
theorem contMDiffOn_symm_image_of_maximalAtlas_lifted_model
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) (G : H → H)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {U W : Set H}
    (hUt : U ⊆ e₀.target) (hWt : W ⊆ e₁.target)
    (hG : ContMDiffOn I I n G U) (hmaps : MapsTo G U W) :
    ContMDiffOn I I n (fun x : M ↦ e₁.symm (G (e₀ x))) (e₀.symm '' U) := by
  have he₀source : e₀.symm '' U ⊆ e₀.source := by
    rintro _ ⟨y, hyU, rfl⟩
    exact e₀.map_target (hUt hyU)
  have he₀smooth : ContMDiffOn I I n (fun x : M ↦ e₀ x) (e₀.symm '' U) :=
    ((contMDiffOn_of_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) he₀).of_le
      hn.out).mono he₀source
  have he₁smooth : ContMDiffOn I I n (fun y : H ↦ e₁.symm y) W :=
    ((contMDiffOn_symm_of_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) he₁).of_le
      hn.out).mono hWt
  exact contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model
    (I := I) e₀ e₁ G hUt hWt he₀smooth hG he₁smooth hmaps

/-- Smoothness of the lifted inverse readout associated to a model open partial
homeomorphism.  If `W = φ '' U`, then the backward chart lift
`e₀.symm ∘ φ.symm ∘ e₁` is `C^n` on the lifted target patch. -/
theorem contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
    {n : WithTop ℕ∞} (e₀ e₁ : OpenPartialHomeomorph M H)
    {φ : OpenPartialHomeomorph H H} {U W : Set H}
    (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hWt : W ⊆ e₁.target) (hW : W = φ '' U)
    (he₁ : ContMDiffOn I I n (fun x : M ↦ e₁ x) (e₁.symm '' W))
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) W)
    (he₀symm : ContMDiffOn I I n (fun y : H ↦ e₀.symm y) U) :
    ContMDiffOn I I n (fun x : M ↦ e₀.symm (φ.symm (e₁ x))) (e₁.symm '' W) := by
  have hmaps : MapsTo (fun y : H ↦ φ.symm y) W U := by
    intro y hyW
    have hyφ : y ∈ φ '' U := by simpa [hW] using hyW
    rcases hyφ with ⟨u, huU, rfl⟩
    simpa [φ.left_inv (hUsource huU)] using huU
  exact contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model
    (I := I) e₁ e₀ (fun y : H ↦ φ.symm y) hWt hUt he₁ hφsymm he₀symm hmaps

/-- Atlas-member specialization of
`contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse`. -/
theorem contMDiffOn_symm_image_of_maximalAtlas_lifted_model_inverse
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) {φ : OpenPartialHomeomorph H H}
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {U W : Set H}
    (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hWt : W ⊆ e₁.target) (hW : W = φ '' U)
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) W) :
    ContMDiffOn I I n (fun x : M ↦ e₀.symm (φ.symm (e₁ x))) (e₁.symm '' W) := by
  have he₁source : e₁.symm '' W ⊆ e₁.source := by
    rintro _ ⟨y, hyW, rfl⟩
    exact e₁.map_target (hWt hyW)
  have he₁smooth : ContMDiffOn I I n (fun x : M ↦ e₁ x) (e₁.symm '' W) :=
    ((contMDiffOn_of_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) he₁).of_le
      hn.out).mono he₁source
  have he₀symm : ContMDiffOn I I n (fun y : H ↦ e₀.symm y) U :=
    ((contMDiffOn_symm_of_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) he₀).of_le
      hn.out).mono hUt
  exact contMDiffOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
    (I := I) e₀ e₁ hUsource hUt hWt hW he₁smooth hφsymm he₀symm

/-- A model open-partial-homeomorphism patch lifted through atlas charts supplies
the local forward/backward data needed by compatible manifold gluing: open
source and target patches, forward and backward `MapsTo`, bijectivity,
`C^n` regularity of both lifted slices, and local inverse identities. -/
theorem lifted_model_local_gluing_data_of_openPartialHomeomorph
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) {G : H → H}
    {φ : OpenPartialHomeomorph H H} (hφ : (φ : H → H) = G)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {U W : Set H}
    (hUopen : IsOpen U) (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hW : W = φ '' U) (hWt : W ⊆ e₁.target)
    (hG : ContMDiffOn I I n G U)
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) W) :
    IsOpen (e₀.symm '' U) ∧
      IsOpen (e₁.symm '' W) ∧
        MapsTo (fun z : M ↦ e₁.symm (G (e₀ z))) (Set.univ ∩ e₀.symm '' U)
          (e₁.symm '' W) ∧
          MapsTo (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) (Set.univ ∩ e₁.symm '' W)
            (e₀.symm '' U) ∧
            BijOn (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) (e₁.symm '' W) ∧
              ContMDiffOn I I n (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) ∧
                ContMDiffOn I I n (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
                  (e₁.symm '' W) ∧
                  LeftInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
                    (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) ∧
                    RightInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
                      (fun z : M ↦ e₁.symm (G (e₀ z))) (e₁.symm '' W) := by
  have hWopen : IsOpen W := by
    simpa [hW] using φ.isOpen_image_of_subset_source hUopen hUsource
  have hUmopen : IsOpen (e₀.symm '' U) :=
    e₀.isOpen_image_symm_of_subset_target hUopen hUt
  have hWmopen : IsOpen (e₁.symm '' W) :=
    e₁.isOpen_image_symm_of_subset_target hWopen hWt
  have hmapsModel : MapsTo G U W := by
    intro y hyU
    rw [← hφ, hW]
    exact ⟨y, hyU, rfl⟩
  have hbijφ : BijOn (fun y : H ↦ φ y) U W := by
    simpa [hW] using (φ.injOn.mono hUsource).bijOn_image
  have hbijModel : BijOn G U W :=
    hbijφ.congr (fun _ _ ↦ by simpa [hφ])
  have hFmaps :
      MapsTo (fun z : M ↦ e₁.symm (G (e₀ z))) (Set.univ ∩ e₀.symm '' U)
        (e₁.symm '' W) := by
    intro z hz
    exact mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_mapsTo
      e₀ e₁ G hUt hmapsModel hz.2
  have hGmaps :
      MapsTo (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) (Set.univ ∩ e₁.symm '' W)
        (e₀.symm '' U) := by
    intro z hz
    exact mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_inverse_mapsTo
      e₀ e₁ hUsource hW hWt hz.2
  have hbijLift :
      BijOn (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) (e₁.symm '' W) :=
    bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn
      e₀ e₁ G hUt hWt hbijModel
  have hFsmooth :
      ContMDiffOn I I n (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) :=
    contMDiffOn_symm_image_of_maximalAtlas_lifted_model
      (I := I) e₀ e₁ G he₀ he₁ hUt hWt hG hmapsModel
  have hGsmooth :
      ContMDiffOn I I n (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) (e₁.symm '' W) :=
    contMDiffOn_symm_image_of_maximalAtlas_lifted_model_inverse
      (I := I) e₀ e₁ he₀ he₁ hUsource hUt hWt hW hφsymm
  have hleft :
      LeftInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
        (fun z : M ↦ e₁.symm (G (e₀ z))) (e₀.symm '' U) :=
    leftInvOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
      e₀ e₁ hφ hUsource hUt hW hWt
  have hright :
      RightInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
        (fun z : M ↦ e₁.symm (G (e₀ z))) (e₁.symm '' W) :=
    rightInvOn_symm_image_of_openPartialHomeomorph_lifted_model_inverse
      e₀ e₁ hφ hUsource hUt hW hWt
  exact ⟨hUmopen, hWmopen, hFmaps, hGmaps, hbijLift, hFsmooth, hGsmooth, hleft, hright⟩

/-- A model open-partial-homeomorphism patch lifted through atlas charts,
packaged as `LocalGluingData`. -/
theorem lifted_model_localGluingData_of_openPartialHomeomorph
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) {G : H → H}
    {φ : OpenPartialHomeomorph H H} (hφ : (φ : H → H) = G)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {U W : Set H}
    (hUopen : IsOpen U) (hUsource : U ⊆ φ.source) (hUt : U ⊆ e₀.target)
    (hW : W = φ '' U) (hWt : W ⊆ e₁.target)
    (hG : ContMDiffOn I I n G U)
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) W) :
    LocalGluingData (I := I) (M := M) n
      (fun z : M ↦ e₁.symm (G (e₀ z)))
      (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
      (e₀.symm '' U) (e₁.symm '' W) := by
  rcases lifted_model_local_gluing_data_of_openPartialHomeomorph
      (I := I) e₀ e₁ hφ he₀ he₁ hUopen hUsource hUt hW hWt hG hφsymm with
    ⟨hUmopen, hWmopen, hFmaps, hGmaps, _hbij, hFsmooth, hGsmooth, hleft, hright⟩
  exact
    { source_open := hUmopen
      target_open := hWmopen
      forward_mapsTo := hFmaps
      backward_mapsTo := hGmaps
      forward_contMDiffOn := hFsmooth
      backward_contMDiffOn := hGsmooth
      left_invOn := by
        intro z hz
        exact hleft hz.2
      right_invOn := by
        intro z hz
        exact hright hz.2 }

/-- Standard selected-shrink form of
`lifted_model_local_gluing_data_of_openPartialHomeomorph`.  The model source is
shrunk to the open set `φ.source ∩ S ∩ φ ⁻¹' T`, so the lifted source and target
patches lie inside prescribed manifold neighborhoods while retaining the local
gluing data needed by the compatible glued-slice constructors. -/
theorem exists_open_nhds_local_gluing_data_subset_of_lifted_openPartialHomeomorph_model
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) {G : H → H}
    {φ : OpenPartialHomeomorph H H} (hφ : (φ : H → H) = G)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {x : M} (hxsource : x ∈ e₀.source) (hxφ : e₀ x ∈ φ.source)
    {S T : Set H}
    (hSopen : IsOpen S) (hS : S ⊆ e₀.target) (hxS : e₀ x ∈ S)
    (hTopen : IsOpen T) (hT : T ⊆ e₁.target) (hxT : G (e₀ x) ∈ T)
    (hG : ContMDiffOn I I n G S)
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) T)
    {Sx Tx : Set M}
    (hSx : e₀.symm '' S ⊆ Sx) (hTx : e₁.symm '' T ⊆ Tx) :
    ∃ Um Wm : Set M,
      IsOpen Um ∧ x ∈ Um ∧ Um ⊆ Sx ∧
        IsOpen Wm ∧
          (fun z : M ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧ Wm ⊆ Tx ∧
            MapsTo (fun z : M ↦ e₁.symm (G (e₀ z))) (Set.univ ∩ Um) Wm ∧
              MapsTo (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) (Set.univ ∩ Wm) Um ∧
                BijOn (fun z : M ↦ e₁.symm (G (e₀ z))) Um Wm ∧
                  ContMDiffOn I I n (fun z : M ↦ e₁.symm (G (e₀ z))) Um ∧
                    ContMDiffOn I I n (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) Wm ∧
                      LeftInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
                        (fun z : M ↦ e₁.symm (G (e₀ z))) Um ∧
                        RightInvOn (fun z : M ↦ e₀.symm (φ.symm (e₁ z)))
                          (fun z : M ↦ e₁.symm (G (e₀ z))) Wm := by
  let U : Set H := φ.source ∩ S ∩ φ ⁻¹' T
  let W : Set H := φ '' U
  have hxTφ : φ (e₀ x) ∈ T := by
    simpa [hφ] using hxT
  have hUopen : IsOpen U := by
    have hpre : IsOpen (φ.source ∩ φ ⁻¹' T) := φ.isOpen_inter_preimage hTopen
    simpa [U, inter_assoc, inter_left_comm, inter_comm] using hpre.inter hSopen
  have hxU : e₀ x ∈ U := ⟨⟨hxφ, hxS⟩, hxTφ⟩
  have hUsource : U ⊆ φ.source := fun _ hz ↦ hz.1.1
  have hUS : U ⊆ S := fun _ hz ↦ hz.1.2
  have hWT : W ⊆ T := by
    rintro _ ⟨z, hzU, rfl⟩
    exact hzU.2
  have hUt : U ⊆ e₀.target := fun y hy ↦ hS (hUS hy)
  have hWt : W ⊆ e₁.target := fun y hy ↦ hT (hWT hy)
  rcases lifted_model_local_gluing_data_of_openPartialHomeomorph
      (I := I) e₀ e₁ hφ he₀ he₁ hUopen hUsource hUt rfl hWt
      (hG.mono hUS) (hφsymm.mono hWT) with
    ⟨hUmopen, hWmopen, hFmaps, hGmaps, hbij, hFsmooth, hGsmooth, hleft, hright⟩
  let Um : Set M := e₀.symm '' U
  let Wm : Set M := e₁.symm '' W
  have hxUm : x ∈ Um := ⟨e₀ x, hxU, e₀.left_inv hxsource⟩
  have hUmSx : Um ⊆ Sx := by
    rintro _ ⟨y, hyU, rfl⟩
    exact hSx ⟨y, hUS hyU, rfl⟩
  have hFxWm : (fun z : M ↦ e₁.symm (G (e₀ z))) x ∈ Wm :=
    hFmaps ⟨Set.mem_univ x, hxUm⟩
  have hWmTx : Wm ⊆ Tx := by
    rintro _ ⟨y, hyW, rfl⟩
    exact hTx ⟨y, hWT hyW, rfl⟩
  exact ⟨Um, Wm, hUmopen, hxUm, hUmSx, hWmopen, hFxWm, hWmTx,
    hFmaps, hGmaps, hbij, hFsmooth, hGsmooth, hleft, hright⟩

/-- Standard selected-shrink form of
`lifted_model_localGluingData_of_openPartialHomeomorph`.  This keeps the
membership and containment facts needed for cover selection while packaging the
slice inverse-function output as `LocalGluingData`. -/
theorem exists_open_nhds_localGluingData_subset_of_lifted_openPartialHomeomorph_model
    {n : WithTop ℕ∞} [hn : ENat.LEInfty n]
    (e₀ e₁ : OpenPartialHomeomorph M H) {G : H → H}
    {φ : OpenPartialHomeomorph H H} (hφ : (φ : H → H) = G)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M)
    {x : M} (hxsource : x ∈ e₀.source) (hxφ : e₀ x ∈ φ.source)
    {S T : Set H}
    (hSopen : IsOpen S) (hS : S ⊆ e₀.target) (hxS : e₀ x ∈ S)
    (hTopen : IsOpen T) (hT : T ⊆ e₁.target) (hxT : G (e₀ x) ∈ T)
    (hG : ContMDiffOn I I n G S)
    (hφsymm : ContMDiffOn I I n (fun y : H ↦ φ.symm y) T)
    {Sx Tx : Set M}
    (hSx : e₀.symm '' S ⊆ Sx) (hTx : e₁.symm '' T ⊆ Tx) :
    ∃ Um Wm : Set M,
      x ∈ Um ∧ Um ⊆ Sx ∧
        (fun z : M ↦ e₁.symm (G (e₀ z))) x ∈ Wm ∧ Wm ⊆ Tx ∧
          LocalGluingData (I := I) (M := M) n
            (fun z : M ↦ e₁.symm (G (e₀ z)))
            (fun z : M ↦ e₀.symm (φ.symm (e₁ z))) Um Wm := by
  rcases exists_open_nhds_local_gluing_data_subset_of_lifted_openPartialHomeomorph_model
      (I := I) e₀ e₁ hφ he₀ he₁ hxsource hxφ hSopen hS hxS hTopen hT hxT
      hG hφsymm hSx hTx with
    ⟨Um, Wm, hUmopen, hxUm, hUmSx, hWmopen, hFxWm, hWmTx,
      hFmaps, hGmaps, _hbij, hFsmooth, hGsmooth, hleft, hright⟩
  refine ⟨Um, Wm, hxUm, hUmSx, hFxWm, hWmTx, ?_⟩
  exact
    { source_open := hUmopen
      target_open := hWmopen
      forward_mapsTo := hFmaps
      backward_mapsTo := hGmaps
      forward_contMDiffOn := hFsmooth
      backward_contMDiffOn := hGsmooth
      left_invOn := by
        intro z hz
        exact hleft hz.2
      right_invOn := by
        intro z hz
        exact hright hz.2 }

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

/-- Time-slice version of `contMDiffOn_of_iUnion_open_eqOn_contMDiffOn` on
`Set.univ`.  If every local readout is `C^n` on its open patch for every time
and the glued time-slice agrees with those readouts on the cover, then every
glued time-slice is globally `C^n` on `Set.univ`. -/
theorem contMDiffOn_univ_timeSlice_of_iUnion_open_eqOn_contMDiffOn
    {ι : Type*} {n : WithTop ℕ∞} {F : ℝ → M → M}
    {G : ι → ℝ → M → M} {U : ι → Set M}
    (hcover : Set.univ ⊆ ⋃ i, U i)
    (hUopen : ∀ i, IsOpen (U i))
    (hcont : ∀ t : ℝ, ∀ i, ContMDiffOn I I n (G i t) (U i))
    (heq : ∀ t : ℝ, ∀ i, EqOn (F t) (G i t) (U i)) :
    ∀ t : ℝ, ContMDiffOn I I n (F t) Set.univ := fun t ↦
  contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
    (I := I) (M := M) (s := Set.univ) (U := U) hcover hUopen
    (fun i ↦ hcont t i)
    (fun i x hx ↦ heq t i hx.2)

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

/-- Transfer a preferred-chart time derivative from a local readout to a glued
map that agrees with it in the relative time filter at the base point. -/
theorem hasDerivWithinAt_extChartAt_eval_of_eventuallyEq
    {s : Set ℝ} {F G : ℝ → M → M} {t : ℝ} {x p : M} {v : E}
    (hderiv : HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (G τ x)) v s t)
    (heq : ∀ᶠ τ in 𝓝[s] t, F τ x = G τ x)
    (heq_t : F t x = G t x) :
    HasDerivWithinAt (fun τ : ℝ ↦ (extChartAt I p) (F τ x)) v s t :=
  hderiv.congr_of_eventuallyEq
    (heq.mono fun τ hτ ↦ congrArg (fun y : M ↦ (extChartAt I p) y) hτ)
    (congrArg (fun y : M ↦ (extChartAt I p) y) heq_t)

/-- Transfer a preferred-chart time derivative from whichever local readout in
an indexed cover contains the base point. -/
theorem hasDerivWithinAt_extChartAt_eval_of_iUnion_eventuallyEqOn
    {ι : Type*} {F : ℝ → M → M} {G : ι → ℝ → M → M}
    {s : Set ℝ} {t : ℝ} {U : ι → Set M} {x p : M} {v : E}
    (hcover : x ∈ ⋃ i, U i)
    (hderiv : ∀ i, HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (G i τ x)) v s t)
    (heq : ∀ i, ∀ᶠ τ in 𝓝[s] t, EqOn (F τ) (G i τ) (U i))
    (heq_t : ∀ i, EqOn (F t) (G i t) (U i)) :
    HasDerivWithinAt (fun τ : ℝ ↦ (extChartAt I p) (F τ x)) v s t := by
  rcases Set.mem_iUnion.mp hcover with ⟨i, hxU⟩
  exact hasDerivWithinAt_extChartAt_eval_of_eventuallyEq
    (I := I) (M := M) (hderiv i)
    ((heq i).mono fun τ hτ ↦ hτ hxU)
    (heq_t i hxU)

/-- Transfer a preferred-chart time derivative from local readouts when the
glued time slices agree with the readouts on the chosen cover for all times. -/
theorem hasDerivWithinAt_extChartAt_eval_of_iUnion_eqOn
    {ι : Type*} {F : ℝ → M → M} {G : ι → ℝ → M → M}
    {s : Set ℝ} {t : ℝ} {U : ι → Set M} {x p : M} {v : E}
    (hcover : x ∈ ⋃ i, U i)
    (hderiv : ∀ i, HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (G i τ x)) v s t)
    (heq : ∀ i, ∀ τ : ℝ, EqOn (F τ) (G i τ) (U i)) :
    HasDerivWithinAt (fun τ : ℝ ↦ (extChartAt I p) (F τ x)) v s t :=
  hasDerivWithinAt_extChartAt_eval_of_iUnion_eventuallyEqOn
    (I := I) (M := M) hcover hderiv
    (fun i ↦ Filter.Eventually.of_forall fun τ ↦ heq i τ)
    (fun i ↦ heq i t)

/-- Transfer a preferred-chart time derivative across a time-dependent indexed
cover when the selected base-time patch persists for the base point in the
relative time filter. -/
theorem hasDerivWithinAt_extChartAt_eval_of_timeDependent_iUnion_pointwiseSource
    {ι : Type*} {F : ℝ → M → M} {G : ι → ℝ → M → M}
    {s : Set ℝ} {t : ℝ} {U : ℝ → ι → Set M} {x p : M} {v : E}
    (hcover : x ∈ ⋃ i, U t i)
    (hderiv : ∀ i, x ∈ U t i →
      HasDerivWithinAt (fun τ : ℝ ↦ (extChartAt I p) (G i τ x)) v s t)
    (heq : ∀ τ : ℝ, ∀ i, EqOn (F τ) (G i τ) (U τ i))
    (hsource : ∀ i, x ∈ U t i → ∀ᶠ τ in 𝓝[s] t, x ∈ U τ i) :
    HasDerivWithinAt (fun τ : ℝ ↦ (extChartAt I p) (F τ x)) v s t := by
  rcases Set.mem_iUnion.mp hcover with ⟨i, hxU⟩
  exact hasDerivWithinAt_extChartAt_eval_of_eventuallyEq
    (I := I) (M := M) (hderiv i hxU)
    ((hsource i hxU).mono fun τ hτ ↦ heq τ i hτ)
    (heq t i hxU)

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

/-- Build a raw `C^3` gauge-flow witness on the open Picard interval from
global glued forward/backward slices and local readouts on indexed open covers.

The local readouts supply inverse identities, `C^3` slice regularity,
within-time continuity, and closed-Picard centered chart ODE data.  The cover
compatibility hypotheses identify the local readouts with the global glued
slices on the domains needed for inverse, regularity, continuity, and
derivative gluing. -/
noncomputable def of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (Fₗ i τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G
    (fun t ↦
      leftInvOn_of_iUnion_eqOn_leftInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (s := Set.univ) (U := U) hUcover
        (fun i x hx ↦ hFEq t i hx.2)
        (fun i ↦ hGEqLeft t i)
        (fun i ↦ hleftLocal t i))
    (fun t ↦
      rightInvOn_of_iUnion_eqOn_rightInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (t := Set.univ) (V := V) hVcover
        (fun i x hx ↦ hGEq t i hx.2)
        (fun i ↦ hFEqRight t i)
        (fun i ↦ hrightLocal t i))
    (contMDiffOn_univ_timeSlice_of_iUnion_open_eqOn_contMDiffOn
      (I := I) (M := M) (F := F) (G := Fₗ) (U := U)
      hUcover hUopen hFLocal hFEq)
    (contMDiffOn_univ_timeSlice_of_iUnion_open_eqOn_contMDiffOn
      (I := I) (M := M) (F := G) (G := Gₗ) (U := V)
      hVcover hVopen hGLocal hGEq)
    (fun x ↦ by
      rcases Set.mem_iUnion.mp (hUcover (Set.mem_univ x)) with ⟨i, hxU⟩
      calc
        F t₀ x = Fₗ i t₀ x := hFEq t₀ i hxU
        _ = x := hanchoredLocal i x hxU)
    (fun t ht x ↦
      continuousWithinAt_eval_of_iUnion_eqOn_continuousWithinAt
        (F := F) (G := Fₗ) (U := U) (s := Icc tmin tmax) (t := t) (x := x)
        (hUcover (Set.mem_univ x)) (fun i ↦ hcontLocal i t ht x)
        (fun i τ ↦ hFEq τ i))
    (fun t ht x ↦ by
      rcases Set.mem_iUnion.mp (hUcover (Set.mem_univ x)) with ⟨i, hxU⟩
      exact hasDerivWithinAt_extChartAt_eval_of_eventuallyEq
        (I := I) (M := M) (F := F) (G := Fₗ i)
        (s := Icc tmin tmax) (t := t) (x := x) (p := F t x)
        (hderivLocal i t ht x hxU)
        (Filter.Eventually.of_forall fun τ ↦ hFEq τ i hxU)
        (hFEq t i hxU))
    hY

/-- Proof-level raw `C^3` gauge-flow existence from local readouts on indexed
open covers and global glued forward/backward slices. -/
theorem nonempty_of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (Fₗ i τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    hcontLocal hderivLocal hY⟩

/-- Build a raw `C^3` gauge-flow witness on the open Picard interval from
global glued forward/backward slices and local readouts on open covers that may
depend on the time slice.

This is the time-dependent-cover companion to
`of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`.
Slice-level inverse and `C^3` regularity are glued using the cover at that
slice.  Time continuity and the centered chart ODE are transferred from a local
readout on the cover chosen at the base time, using relative-filter equality
between that readout and the global glued slices. -/
noncomputable def of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i))
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (Fₗ i τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G
    (fun t ↦
      leftInvOn_of_iUnion_eqOn_leftInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (s := Set.univ) (U := U t) (hUcover t)
        (fun i x hx ↦ hFEq t i hx.2)
        (fun i ↦ hGEqLeft t i)
        (fun i ↦ hleftLocal t i))
    (fun t ↦
      rightInvOn_of_iUnion_eqOn_rightInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (t := Set.univ) (V := V t) (hVcover t)
        (fun i x hx ↦ hGEq t i hx.2)
        (fun i ↦ hFEqRight t i)
        (fun i ↦ hrightLocal t i))
    (fun t ↦
      contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
        (I := I) (M := M) (s := Set.univ) (U := U t)
        (hUcover t) (hUopen t) (fun i ↦ hFLocal t i)
        (fun i x hx ↦ hFEq t i hx.2))
    (fun t ↦
      contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
        (I := I) (M := M) (s := Set.univ) (U := V t)
        (hVcover t) (hVopen t) (fun i ↦ hGLocal t i)
        (fun i x hx ↦ hGEq t i hx.2))
    (fun x ↦ by
      rcases Set.mem_iUnion.mp (hUcover t₀ (Set.mem_univ x)) with ⟨i, hxU⟩
      calc
        F t₀ x = Fₗ i t₀ x := hFEq t₀ i hxU
        _ = x := hanchoredLocal i x hxU)
    (fun t ht x ↦ by
      rcases Set.mem_iUnion.mp (hUcover t (Set.mem_univ x)) with ⟨i, hxU⟩
      exact (hcontLocal i t ht x hxU).congr_of_eventuallyEq
        ((hFEqWithin t ht i).mono fun τ hτ ↦ hτ hxU)
        (hFEq t i hxU))
    (fun t ht x ↦ by
      rcases Set.mem_iUnion.mp (hUcover t (Set.mem_univ x)) with ⟨i, hxU⟩
      exact hasDerivWithinAt_extChartAt_eval_of_eventuallyEq
        (I := I) (M := M) (F := F) (G := Fₗ i)
        (s := Icc tmin tmax) (t := t) (x := x) (p := F t x)
        (hderivLocal i t ht x hxU)
        ((hFEqWithin t ht i).mono fun τ hτ ↦ hτ hxU)
        (hFEq t i hxU))
    hY

/-- Proof-level raw `C^3` gauge-flow existence from local readouts on
time-dependent open covers and global glued forward/backward slices. -/
theorem nonempty_of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i))
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (F t x)) (Fₗ i τ x))
        (Y t (F t x)) (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ (F τ x) = X τ (F τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    hFEqWithin hcontLocal hderivLocal hY⟩

/-- Finite-cover helper for the uniform relative-filter equality required by
the local-readout time-dependent-cover constructor.  Per-index equality in the
closed-interval relative filter implies simultaneous equality for all indices
in the open-interval relative filter. -/
theorem timeDependent_iUnion_hFEqWithinAll_of_finite
    {ι : Type*} [Finite ι] {tmin tmax : ℝ}
    {F : ℝ → M → M} {Fₗ : ι → ℝ → M → M} {U : ℝ → ι → Set M}
    (hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i)) :
    ∀ t ∈ Ioo tmin tmax,
      ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ i, EqOn (F τ) (Fₗ i τ) (U t i) := by
  intro t ht
  exact Filter.eventually_all.2 fun i ↦
    (hFEqWithin t (Ioo_subset_Icc_self ht) i).filter_mono
      (nhdsWithin_mono t Ioo_subset_Icc_self)

/-- Build a raw `C^3` gauge-flow witness from global glued forward/backward
slices and local readouts on time-dependent open covers when the
preferred-chart derivative and vector-field-identification hypotheses are
stated against the local forward readouts.

The derivative transport uses equality with the global glued slice at the base
time and relative-filter equality near the base time.  The field-identification
transport needs the strengthened uniform relative-filter equality
`hFEqWithinAll`, because the target gauge-flow statement is uniform in the base
point `x`. -/
noncomputable def of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i))
    (hFEqWithinAll : ∀ t ∈ Ioo tmin tmax,
      ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ i, EqOn (F τ) (Fₗ i τ) (U t i))
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal hFEqWithin
    hcontLocal
    (fun i t ht x hxU ↦ by
      have hFx : F t x = Fₗ i t x := hFEq t i hxU
      rw [hFx]
      exact hderivLocal i t ht x hxU)
    (fun t ht ↦ by
      filter_upwards [hYLocal t ht, hFEqWithinAll t ht] with τ hYτ hEqτ
      intro x
      rcases Set.mem_iUnion.mp (hUcover t (Set.mem_univ x)) with ⟨i, hxU⟩
      have hFx : F τ x = Fₗ i τ x := hEqτ i hxU
      rw [hFx]
      exact hYτ i x hxU)

/-- Proof-level raw `C^3` gauge-flow existence from local readouts on
time-dependent open covers, with derivative and vector-field-identification
hypotheses stated against the local forward readouts. -/
theorem nonempty_of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (F G : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i))
    (hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)))
    (hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i))
    (hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i))
    (hFEqWithinAll : ∀ t ∈ Ioo tmin tmax,
      ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ i, EqOn (F τ) (Fₗ i τ) (U t i))
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal hFEqWithin
    hFEqWithinAll hcontLocal hderivLocal hYLocal⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on
time-dependent open covers, constructing the global forward/backward slices
canonically via `gluedMapOf_iUnion`.

The additional `hUwithin` hypothesis is the temporal source-persistence bridge:
the source patch chosen at the base time remains inside the corresponding patch
for nearby times in the closed Picard relative filter.  This turns slice-wise
canonical gluing into the relative-filter equality required by the lower-level
time-dependent-cover endpoint. -/
noncomputable def of_timeDependent_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let F : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultF t) (U t) (fun i ↦ Fₗ i t)
  let G : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultG t) (V t) (fun i ↦ Gₗ i t)
  have hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i) := by
    intro t
    simpa [F] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultF t) (U := U t) (Fₗ := fun i ↦ Fₗ i t) (hFcompat t))
  have hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i) := by
    intro t
    simpa [G] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultG t) (U := V t) (Fₗ := fun i ↦ Gₗ i t) (hGcompat t))
  have hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)) := by
    intro t i y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hFx : F t x = Fₗ i t x := hFEq t i hx.2
    have hV : F t x ∈ V t i := by
      rw [hFx]
      exact hFmaps t i hx
    exact hGEq t i hV
  have hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)) := by
    intro t i x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hGy : G t y = Gₗ i t y := hGEq t i hy.2
    have hU : G t y ∈ U t i := by
      rw [hGy]
      exact hGmaps t i hy
    exact hFEq t i hU
  have hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i) := by
    intro t ht i
    filter_upwards [hUwithin t ht i] with τ hτ x hx
    exact hFEq τ i (hτ hx)
  exact of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    hFEqWithin hcontLocal
    (fun i t ht x hxU ↦ by
      simpa [F] using hderivLocal i t ht x hxU)
    (fun t ht ↦ by
      simpa [F] using hY t ht)

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on time-dependent open covers, with canonical glued slices. -/
theorem nonempty_of_timeDependent_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hUwithin hleftLocal hrightLocal hFLocal
    hGLocal hanchoredLocal hcontLocal hderivLocal hY⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on
time-dependent open covers when source persistence is only pointwise.

This variant targets the common situation where a chosen local patch around the
base point persists for that base point in the closed Picard relative filter,
without requiring a uniform eventual inclusion of the whole patch.  The
vector-field identification is still stated for the canonically glued global
slice, so no uniform local-field handoff is needed here. -/
noncomputable def of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithinPoint : ∀ t ∈ Icc tmin tmax, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, x ∈ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let F : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultF t) (U t) (fun i ↦ Fₗ i t)
  let G : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultG t) (V t) (fun i ↦ Gₗ i t)
  have hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i) := by
    intro t
    simpa [F] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultF t) (U := U t) (Fₗ := fun i ↦ Fₗ i t) (hFcompat t))
  have hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i) := by
    intro t
    simpa [G] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultG t) (U := V t) (Fₗ := fun i ↦ Gₗ i t) (hGcompat t))
  have hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)) := by
    intro t i y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hFx : F t x = Fₗ i t x := hFEq t i hx.2
    have hV : F t x ∈ V t i := by
      rw [hFx]
      exact hFmaps t i hx
    exact hGEq t i hV
  have hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)) := by
    intro t i x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hGy : G t y = Gₗ i t y := hGEq t i hy.2
    have hU : G t y ∈ U t i := by
      rw [hGy]
      exact hGmaps t i hy
    exact hFEq t i hU
  exact of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G
    (fun t ↦
      leftInvOn_of_iUnion_eqOn_leftInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (s := Set.univ) (U := U t) (hUcover t)
        (fun i x hx ↦ hFEq t i hx.2)
        (fun i y hy ↦ hGEqLeft t i hy)
        (fun i ↦ hleftLocal t i))
    (fun t ↦
      rightInvOn_of_iUnion_eqOn_rightInvOn
        (F := F t) (G := G t) (Fₗ := fun i ↦ Fₗ i t) (Gₗ := fun i ↦ Gₗ i t)
        (t := Set.univ) (V := V t) (hVcover t)
        (fun i x hx ↦ hGEq t i hx.2)
        (fun i y hy ↦ hFEqRight t i hy)
        (fun i ↦ hrightLocal t i))
    (fun t ↦
      contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
        (I := I) (M := M) (s := Set.univ) (U := U t)
        (hUcover t) (hUopen t) (fun i ↦ hFLocal t i)
        (fun i x hx ↦ hFEq t i hx.2))
    (fun t ↦
      contMDiffOn_of_iUnion_open_eqOn_contMDiffOn
        (I := I) (M := M) (s := Set.univ) (U := V t)
        (hVcover t) (hVopen t) (fun i ↦ hGLocal t i)
        (fun i x hx ↦ hGEq t i hx.2))
    (fun x ↦ by
      rcases Set.mem_iUnion.mp (hUcover t₀ (Set.mem_univ x)) with ⟨i, hxU⟩
      calc
        F t₀ x = Fₗ i t₀ x := hFEq t₀ i hxU
        _ = x := hanchoredLocal i x hxU)
    (fun t ht x ↦
      continuousWithinAt_eval_of_timeDependent_iUnion_pointwiseSource_continuousWithinAt
        (F := F) (G := Fₗ) (s := Icc tmin tmax) (t := t) (U := U) (x := x)
        (hUcover t (Set.mem_univ x))
        (fun i hxU ↦ hcontLocal i t ht x hxU)
        hFEq
        (fun i hxU ↦ hUwithinPoint t ht i x hxU))
    (fun t ht x ↦
      hasDerivWithinAt_extChartAt_eval_of_timeDependent_iUnion_pointwiseSource
        (I := I) (M := M) (F := F) (G := Fₗ)
        (s := Icc tmin tmax) (t := t) (U := U) (x := x) (p := F t x)
        (hUcover t (Set.mem_univ x))
        (fun i hxU ↦ by simpa [F] using hderivLocal i t ht x hxU)
        hFEq
        (fun i hxU ↦ hUwithinPoint t ht i x hxU))
    (fun t ht ↦ by
      simpa [F] using hY t ht)

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on time-dependent open covers with pointwise source persistence. -/
theorem nonempty_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithinPoint : ∀ t ∈ Icc tmin tmax, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, x ∈ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hUwithinPoint hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal hcontLocal hderivLocal hY⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on
time-dependent open covers when the global-vector-field route's source
persistence is supplied by fixed open target patches along the local forward
readouts. -/
noncomputable def of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M) (W : ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUpreimage : ∀ τ : ℝ, ∀ i, ∀ x : M, x ∈ U τ i ↔ Fₗ i τ x ∈ W i)
    (hWopen : ∀ i, IsOpen (W i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps
    (timeDependent_iUnion_pointwiseSource_of_indexed_open_preimage_continuousWithinAt
      (F := Fₗ) (s := Icc tmin tmax) (U := U) (V := W)
      hUpreimage hWopen
      (fun t ht i x hx ↦ hcontLocal i t ht x hx))
    hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal hcontLocal
    hderivLocal hY

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on time-dependent open covers, with global vector-field identification and
source persistence derived from fixed open target patches. -/
theorem nonempty_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M) (W : ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUpreimage : ∀ τ : ℝ, ∀ i, ∀ x : M, x ∈ U τ i ↔ Fₗ i τ x ∈ W i)
    (hWopen : ∀ i, IsOpen (W i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I
            ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ)) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V W hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hUpreimage hWopen hleftLocal hrightLocal hFLocal
    hGLocal hanchoredLocal hcontLocal hderivLocal hY⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on
time-dependent open covers with pointwise source persistence, when the
preferred-chart derivative and vector-field-identification hypotheses are
stated against local forward readouts.  Unlike the finite-cover local-readout
route below, the vector-field handoff is stated on the actual time-slice patch
`U τ i`, so it does not require a uniform simultaneous equality over the
base-time cover. -/
noncomputable def of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithinPoint : ∀ t ∈ Icc tmin tmax, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, x ∈ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U τ i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let F : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultF t) (U t) (fun i ↦ Fₗ i t)
  have hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i) := by
    intro t
    simpa [F] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultF t) (U := U t) (Fₗ := fun i ↦ Fₗ i t) (hFcompat t))
  exact
    of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (X := X) (Y := Y)
      (tmin := tmin) (tmax := tmax) (t₀ := t₀)
      defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
      hGcompat hFmaps hGmaps hUwithinPoint hleftLocal hrightLocal hFLocal
      hGLocal hanchoredLocal hcontLocal
      (fun i t ht x hxU ↦ by
        have hFx :
            gluedMapOf_iUnion (defaultF t) (U t) (fun j ↦ Fₗ j t) x = Fₗ i t x := by
          simpa [F] using hFEq t i hxU
        rw [hFx]
        exact hderivLocal i t ht x hxU)
      (fun t ht ↦ by
        filter_upwards [hYLocal t ht] with τ hYτ x
        rcases Set.mem_iUnion.mp (hUcover τ (Set.mem_univ x)) with ⟨i, hxU⟩
        have hFx :
            gluedMapOf_iUnion (defaultF τ) (U τ) (fun i ↦ Fₗ i τ) x = Fₗ i τ x := by
          simpa [F] using hFEq τ i hxU
        rw [hFx]
        exact hYτ i x hxU)

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on time-dependent open covers with pointwise source persistence and local
vector-field readouts on the actual time-slice patches. -/
theorem nonempty_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithinPoint : ∀ t ∈ Icc tmin tmax, ∀ i, ∀ x ∈ U t i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, x ∈ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U τ i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hUwithinPoint hleftLocal hrightLocal hFLocal
    hGLocal hanchoredLocal hcontLocal hderivLocal hYLocal⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on
time-dependent open covers when the pointwise source persistence is supplied by
open-preimage patches along the local forward readouts.  This matches Picard
outputs where the active source patch is defined by requiring the local flow
value to stay in a fixed open target patch. -/
noncomputable def of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M) (W : ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUpreimage : ∀ τ : ℝ, ∀ i, ∀ x : M, x ∈ U τ i ↔ Fₗ i τ x ∈ W i)
    (hWopen : ∀ i, IsOpen (W i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U τ i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps
    (timeDependent_iUnion_pointwiseSource_of_indexed_open_preimage_continuousWithinAt
      (F := Fₗ) (s := Icc tmin tmax) (U := U) (V := W)
      hUpreimage hWopen
      (fun t ht i x hx ↦ hcontLocal i t ht x hx))
    hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal hcontLocal
    hderivLocal hYLocal

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on time-dependent open covers whose source persistence comes from fixed open
target patches along the local forward readouts. -/
theorem nonempty_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M) (W : ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUpreimage : ∀ τ : ℝ, ∀ i, ∀ x : M, x ∈ U τ i ↔ Fₗ i τ x ∈ W i)
    (hWopen : ∀ i, IsOpen (W i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U τ i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V W hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hUpreimage hWopen hleftLocal hrightLocal hFLocal
    hGLocal hanchoredLocal hcontLocal hderivLocal hYLocal⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on a
finite time-dependent open cover, with derivative and vector-field
identification hypotheses stated against the local forward readouts.

The finite index type promotes per-patch relative-filter equality to the
uniform equality needed to identify the vector field along the canonically glued
global slice for all base points. -/
noncomputable def of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let F : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultF t) (U t) (fun i ↦ Fₗ i t)
  let G : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultG t) (V t) (fun i ↦ Gₗ i t)
  have hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U t i) := by
    intro t
    simpa [F] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultF t) (U := U t) (Fₗ := fun i ↦ Fₗ i t) (hFcompat t))
  have hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V t i) := by
    intro t
    simpa [G] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultG t) (U := V t) (Fₗ := fun i ↦ Gₗ i t) (hGcompat t))
  have hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U t i)) := by
    intro t i y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hFx : F t x = Fₗ i t x := hFEq t i hx.2
    have hV : F t x ∈ V t i := by
      rw [hFx]
      exact hFmaps t i hx
    exact hGEq t i hV
  have hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V t i)) := by
    intro t i x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hGy : G t y = Gₗ i t y := hGEq t i hy.2
    have hU : G t y ∈ U t i := by
      rw [hGy]
      exact hGmaps t i hy
    exact hFEq t i hU
  have hFEqWithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, EqOn (F τ) (Fₗ i τ) (U t i) := by
    intro t ht i
    filter_upwards [hUwithin t ht i] with τ hτ x hx
    exact hFEq τ i (hτ hx)
  exact of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    hFEqWithin
    (timeDependent_iUnion_hFEqWithinAll_of_finite
      (F := F) (Fₗ := Fₗ) (U := U) hFEqWithin)
    hcontLocal hderivLocal hYLocal

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
on a finite time-dependent open cover, with local derivative and
vector-field-identification hypotheses. -/
theorem nonempty_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hUopen : ∀ t : ℝ, ∀ i, IsOpen (U t i))
    (hVopen : ∀ t : ℝ, ∀ i, IsOpen (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U t i) (V t i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V t i) (U t i))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U t i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V t i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U t i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V t i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hUwithin hleftLocal hrightLocal hFLocal
    hGLocal hanchoredLocal hcontLocal hderivLocal hYLocal⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts on a
finite time-dependent open cover when each local time-slice is supplied as a
named `LocalGluingData` patch.  This is the finite-cover assembly form matching
the lifted local inverse-function outputs. -/
noncomputable def of_finite_timeDependent_iUnion_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hlocal : ∀ t : ℝ, ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover
    (fun t i ↦ (hlocal t i).source_open)
    (fun t i ↦ (hlocal t i).target_open)
    hFcompat hGcompat
    (fun t i ↦ (hlocal t i).forward_mapsTo)
    (fun t i ↦ (hlocal t i).backward_mapsTo)
    hUwithin
    (fun t i ↦ (hlocal t i).left_invOn)
    (fun t i ↦ (hlocal t i).right_invOn)
    (fun t i ↦ (hlocal t i).forward_contMDiffOn)
    (fun t i ↦ (hlocal t i).backward_contMDiffOn)
    hanchoredLocal hcontLocal hderivLocal hYLocal

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts on
a finite time-dependent open cover supplied by named `LocalGluingData` patches. -/
theorem nonempty_of_finite_timeDependent_iUnion_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ℝ → ι → Set M)
    (hUcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, U t i)
    (hVcover : ∀ t : ℝ, Set.univ ⊆ ⋃ i, V t i)
    (hlocal : ∀ t : ℝ, ∀ i,
      LocalGluingData (I := I) (M := M) 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U t i ∩ U t j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V t i ∩ V t j))
    (hUwithin : ∀ t ∈ Icc tmin tmax, ∀ i,
      ∀ᶠ τ in 𝓝[Icc tmin tmax] t, U t i ⊆ U τ i)
    (hanchoredLocal : ∀ i, ∀ x ∈ U t₀ i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U t i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U t i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_finite_timeDependent_iUnion_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hlocal hFcompat hGcompat
    hUwithin hanchoredLocal hcontLocal hderivLocal hYLocal⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts by
constructing the global forward/backward slices canonically via
`gluedMapOf_iUnion`.  The local maps only need to agree on overlaps and map
each source patch into the matching target patch; the global equality data
required by the lower-level glued-slice endpoint is derived here. -/
noncomputable def of_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U i ∩ U j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V i ∩ V j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U i) (V i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V i) (U i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I ((gluedMapOf_iUnion (defaultF t) U (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) U (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) U (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) U (fun i ↦ Fₗ i τ)) x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ := by
  let F : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultF t) U (fun i ↦ Fₗ i t)
  let G : ℝ → M → M := fun t ↦ gluedMapOf_iUnion (defaultG t) V (fun i ↦ Gₗ i t)
  have hFEq : ∀ t : ℝ, ∀ i, EqOn (F t) (Fₗ i t) (U i) := by
    intro t
    simpa [F] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultF t) (U := U) (Fₗ := fun i ↦ Fₗ i t) (hFcompat t))
  have hGEq : ∀ t : ℝ, ∀ i, EqOn (G t) (Gₗ i t) (V i) := by
    intro t
    simpa [G] using
      (gluedMapOf_iUnion_eqOn
        (default := defaultG t) (U := V) (Fₗ := fun i ↦ Gₗ i t) (hGcompat t))
  have hGEqLeft : ∀ t : ℝ, ∀ i,
      EqOn (G t) (Gₗ i t) ((F t) '' (Set.univ ∩ U i)) := by
    intro t i y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hFx : F t x = Fₗ i t x := hFEq t i hx.2
    have hV : F t x ∈ V i := by
      rw [hFx]
      exact hFmaps t i hx
    exact hGEq t i hV
  have hFEqRight : ∀ t : ℝ, ∀ i,
      EqOn (F t) (Fₗ i t) ((G t) '' (Set.univ ∩ V i)) := by
    intro t i x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hGy : G t y = Gₗ i t y := hGEq t i hy.2
    have hU : G t y ∈ U i := by
      rw [hGy]
      exact hGmaps t i hy
    exact hFEq t i hU
  exact of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    hcontLocal
    (fun i t ht x hxU ↦ by
      simpa [F] using hderivLocal i t ht x hxU)
    (fun t ht ↦ by
      simpa [F] using hY t ht)

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts,
with global forward/backward slices constructed canonically by
`gluedMapOf_iUnion`. -/
theorem nonempty_of_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U i ∩ U j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V i ∩ V j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U i) (V i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V i) (U i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦
          (extChartAt I ((gluedMapOf_iUnion (defaultF t) U (fun j ↦ Fₗ j t)) x))
            (Fₗ i τ x))
        (Y t ((gluedMapOf_iUnion (defaultF t) U (fun j ↦ Fₗ j t)) x))
        (Icc tmin tmax) t)
    (hY : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t, ∀ x : M,
      Y τ ((gluedMapOf_iUnion (defaultF τ) U (fun i ↦ Fₗ i τ)) x) =
        X τ ((gluedMapOf_iUnion (defaultF τ) U (fun i ↦ Fₗ i τ)) x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal
    hanchoredLocal hcontLocal hderivLocal hY⟩

/-- Build a raw `C^3` gauge-flow witness from compatible local readouts when
the preferred-chart derivative and vector-field-identification hypotheses are
stated against the local forward readouts.  The canonical glued map agrees with
each local readout on its source patch, so this repackages the local hypotheses
into the glued-slice endpoint. -/
noncomputable def of_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U i ∩ U j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V i ∩ V j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U i) (V i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V i) (U i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀ :=
  of_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal
    hanchoredLocal hcontLocal
    (fun i t ht x hxU ↦ by
      have hFx :
          (gluedMapOf_iUnion (defaultF t) U (fun j ↦ Fₗ j t)) x = Fₗ i t x :=
        (gluedMapOf_iUnion_eqOn
          (default := defaultF t) (U := U) (Fₗ := fun j ↦ Fₗ j t)
          (hFcompat t)) i (x := x) hxU
      rw [hFx]
      exact hderivLocal i t ht x hxU)
    (fun t ht ↦ by
      filter_upwards [hYLocal t ht] with τ hτ
      intro x
      have hxcover : x ∈ ⋃ i, U i := hUcover (by simp)
      rcases Set.mem_iUnion.mp hxcover with ⟨i, hxU⟩
      have hFx :
          (gluedMapOf_iUnion (defaultF τ) U (fun j ↦ Fₗ j τ)) x = Fₗ i τ x :=
        (gluedMapOf_iUnion_eqOn
          (default := defaultF τ) (U := U) (Fₗ := fun j ↦ Fₗ j τ)
          (hFcompat τ)) i (x := x) hxU
      rw [hFx]
      exact hτ i x hxU)

/-- Proof-level raw `C^3` gauge-flow existence from compatible local readouts
whose derivative and vector-field-identification hypotheses are stated against
the local forward readouts. -/
theorem nonempty_of_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    {ι : Type*}
    {X Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (defaultF defaultG : ℝ → M → M) (Fₗ Gₗ : ι → ℝ → M → M)
    (U V : ι → Set M)
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hVcover : Set.univ ⊆ ⋃ i, V i)
    (hUopen : ∀ i, IsOpen (U i))
    (hVopen : ∀ i, IsOpen (V i))
    (hFcompat : ∀ t : ℝ, ∀ i j, EqOn (Fₗ i t) (Fₗ j t) (U i ∩ U j))
    (hGcompat : ∀ t : ℝ, ∀ i j, EqOn (Gₗ i t) (Gₗ j t) (V i ∩ V j))
    (hFmaps : ∀ t : ℝ, ∀ i, MapsTo (Fₗ i t) (Set.univ ∩ U i) (V i))
    (hGmaps : ∀ t : ℝ, ∀ i, MapsTo (Gₗ i t) (Set.univ ∩ V i) (U i))
    (hleftLocal : ∀ t : ℝ, ∀ i,
      LeftInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ U i))
    (hrightLocal : ∀ t : ℝ, ∀ i,
      RightInvOn (Gₗ i t) (Fₗ i t) (Set.univ ∩ V i))
    (hFLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ i t) (U i))
    (hGLocal : ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ i t) (V i))
    (hanchoredLocal : ∀ i, ∀ x ∈ U i, Fₗ i t₀ x = x)
    (hcontLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M,
      ContinuousWithinAt (fun τ : ℝ ↦ Fₗ i τ x) (Icc tmin tmax) t)
    (hderivLocal : ∀ i, ∀ t ∈ Icc tmin tmax, ∀ x : M, x ∈ U i →
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (Fₗ i t x)) (Fₗ i τ x))
        (Y t (Fₗ i t x)) (Icc tmin tmax) t)
    (hYLocal : ∀ t ∈ Ioo tmin tmax, ∀ᶠ τ in 𝓝[Ioo tmin tmax] t,
      ∀ i, ∀ x : M, x ∈ U i → Y τ (Fₗ i τ x) = X τ (Fₗ i τ x)) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Ioo tmin tmax) t₀) :=
  ⟨of_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (X := X) (Y := Y)
    (tmin := tmin) (tmax := tmax) (t₀ := t₀)
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen
    hFcompat hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal
    hanchoredLocal hcontLocal hderivLocal hYLocal⟩

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

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence on open solution time
sets from globally glued inverse slices, within-time continuity, and
closed-Picard preferred-chart ODE data for model vector fields. -/
noncomputable def ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
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
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ F sol τ x)
          (Icc (tmin sol) (tmax sol)) t)
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
      Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol)
        (tmin := tmin sol) (tmax := tmax sol) (t₀ := ivp.initialTime)
        (F sol) (G sol) (hleft sol) (hright sol) (hF sol) (hG sol)
        (hanchored sol) (hcont sol) (hderiv sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from globally glued
inverse slices, within-time continuity, closed-Picard chart ODE data, and
relative-filter field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
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
    (hcont : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ F sol τ x)
          (Icc (tmin sol) (tmax sol)) t)
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
  ⟨ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
    F G hleft hright hF hG hanchored Y tmin tmax htimeSet hcont hderiv hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from global glued
forward/backward slices and local readouts on indexed open covers.  This is
the fixed-IVP form of
`Diffeomorph3GaugeFlowOn.of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (Fₗ sol i τ x))
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
      Diffeomorph3GaugeFlowOn.of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (F sol) (G sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFEq sol) (hGEqLeft sol) (hGEq sol) (hFEqRight sol)
        (hleftLocal sol) (hrightLocal sol) (hFLocal sol) (hGLocal sol)
        (hanchoredLocal sol) (hcontLocal sol) (hderivLocal sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from local readouts on
indexed open covers and global glued forward/backward slices, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (Fₗ sol i τ x))
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
  ⟨ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hcontLocal hderivLocal hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from global glued
forward/backward slices and local readouts on open covers that may depend on
the time slice.  This is the fixed-IVP form of
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol t i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol t i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol t i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol t i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hFEqWithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (Fₗ sol i τ x))
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
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (F sol) (G sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFEq sol) (hGEqLeft sol) (hGEq sol) (hFEqRight sol)
        (hleftLocal sol) (hrightLocal sol) (hFLocal sol) (hGLocal sol)
        (hanchoredLocal sol) (hFEqWithin sol) (hcontLocal sol)
        (hderivLocal sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from local readouts on
time-dependent open covers and global glued forward/backward slices, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol t i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol t i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol t i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol t i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hFEqWithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (F sol t x)) (Fₗ sol i τ x))
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
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hFEqWithin hcontLocal hderivLocal hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from local readouts on
time-dependent open covers, with derivative and vector-field-identification
hypotheses stated against the local forward readouts. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol t i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol t i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol t i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol t i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hFEqWithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hFEqWithinAll : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ i,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (F sol) (G sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFEq sol) (hGEqLeft sol) (hGEq sol) (hFEqRight sol)
        (hleftLocal sol) (hrightLocal sol) (hFLocal sol) (hGLocal sol)
        (hanchoredLocal sol) (hFEqWithin sol) (hFEqWithinAll sol)
        (hcontLocal sol) (hderivLocal sol) (hYLocal sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from local readouts on
time-dependent open covers, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (F G : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (F sol t) (Fₗ sol i t) (U sol t i))
    (hGEqLeft : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (G sol t) (Gₗ sol i t) ((F sol t) '' (Set.univ ∩ U sol t i)))
    (hGEq : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, EqOn (G sol t) (Gₗ sol i t) (V sol t i))
    (hFEqRight : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        EqOn (F sol t) (Fₗ sol i t) ((G sol t) '' (Set.univ ∩ V sol t i)))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hFEqWithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hFEqWithinAll : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ i,
          EqOn (F sol τ) (Fₗ sol i τ) (U sol t i))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hFEqWithin hFEqWithinAll hcontLocal hderivLocal
    hYLocal⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on time-dependent covers, with canonical glued slices and pointwise
source persistence.  This is the fixed-IVP form of
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithinPoint : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i, ∀ x ∈ U sol t i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, x ∈ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
                (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
              (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hUwithinPoint sol) (hleftLocal sol) (hrightLocal sol)
        (hFLocal sol) (hGLocal sol) (hanchoredLocal sol) (hcontLocal sol)
        (hderivLocal sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible
time-dependent local readouts with pointwise source persistence, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithinPoint : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i, ∀ x ∈ U sol t i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, x ∈ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
                (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
              (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUwithinPoint hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal hderivLocal hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on time-dependent covers whose global-field source persistence is
derived from fixed open target patches along the local forward readouts. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (W : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUpreimage : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ τ : ℝ, ∀ i, ∀ x : M,
        x ∈ U sol τ i ↔ Fₗ sol i τ x ∈ W sol i)
    (hWopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (W sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
                (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
              (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol) (W sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hUpreimage sol) (hWopen sol) (hleftLocal sol) (hrightLocal sol)
        (hFLocal sol) (hGLocal sol) (hanchoredLocal sol)
        (hcontLocal sol) (hderivLocal sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts with global vector-field identification and source persistence derived
from fixed open target patches, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (W : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUpreimage : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ τ : ℝ, ∀ i, ∀ x : M,
        x ∈ U sol τ i ↔ Fₗ sol i τ x ∈ W sol i)
    (hWopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (W sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
                (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol t)
              (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol τ)
                (fun i ↦ Fₗ sol i τ)) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V W hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUpreimage hWopen hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal hderivLocal hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on time-dependent covers with pointwise source persistence, where the
derivative and vector-field-identification inputs are stated against local
forward readouts on the actual time-slice patches. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithinPoint : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i, ∀ x ∈ U sol t i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, x ∈ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol τ i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hUwithinPoint sol) (hleftLocal sol) (hrightLocal sol)
        (hFLocal sol) (hGLocal sol) (hanchoredLocal sol)
        (hcontLocal sol) (hderivLocal sol) (hYLocal sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible
time-dependent local readouts with pointwise source persistence and local
vector-field readouts on actual time-slice patches, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithinPoint : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i, ∀ x ∈ U sol t i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, x ∈ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol τ i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUwithinPoint hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal hderivLocal
    hYLocal⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on time-dependent covers whose source persistence is derived from
fixed open target patches along the local forward readouts. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (W : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUpreimage : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ τ : ℝ, ∀ i, ∀ x : M,
        x ∈ U sol τ i ↔ Fₗ sol i τ x ∈ W sol i)
    (hWopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (W sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol τ i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol) (W sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hUpreimage sol) (hWopen sol) (hleftLocal sol) (hrightLocal sol)
        (hFLocal sol) (hGLocal sol) (hanchoredLocal sol)
        (hcontLocal sol) (hderivLocal sol) (hYLocal sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts whose source persistence comes from fixed open target patches along
the local forward readouts, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (W : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUpreimage : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ τ : ℝ, ∀ i, ∀ x : M,
        x ∈ U sol τ i ↔ Fₗ sol i τ x ∈ W sol i)
    (hWopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (W sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol τ i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V W hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUpreimage hWopen hleftLocal
    hrightLocal hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal
    hderivLocal hYLocal⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on a finite time-dependent open cover.

This packages the finite raw gluing constructor at the intrinsic fixed-IVP
boundary: source persistence is supplied directly as monotone patch inclusion
on the closed Picard interval, and the finite index type promotes local
vector-field identifications to the uniform glued-slice handoff internally. -/
noncomputable def ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, U sol t i ⊆ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hUwithin sol) (hleftLocal sol) (hrightLocal sol) (hFLocal sol)
        (hGLocal sol) (hanchoredLocal sol) (hcontLocal sol) (hderivLocal sol)
        (hYLocal sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP finite compatible-cover local-readout gauge-flow existence, kept
as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (U sol t i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, IsOpen (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol t i) (V sol t i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol t i) (U sol t i))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, U sol t i ⊆ U sol τ i)
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol t i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol t i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol t i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol t i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUwithin hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal hderivLocal
    hYLocal⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on a finite time-dependent open cover supplied by named
`LocalGluingData` patches. -/
noncomputable def ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hlocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        LocalGluingData (I := I) (M := M) 3
          (Fₗ sol i t) (Gₗ sol i t) (U sol t i) (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, U sol t i ⊆ U sol τ i)
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover
    (fun sol t i ↦ (hlocal sol t i).source_open)
    (fun sol t i ↦ (hlocal sol t i).target_open)
    hFcompat hGcompat
    (fun sol t i ↦ (hlocal sol t i).forward_mapsTo)
    (fun sol t i ↦ (hlocal sol t i).backward_mapsTo)
    tmin tmax hUwithin
    (fun sol t i ↦ (hlocal sol t i).left_invOn)
    (fun sol t i ↦ (hlocal sol t i).right_invOn)
    (fun sol t i ↦ (hlocal sol t i).forward_contMDiffOn)
    (fun sol t i ↦ (hlocal sol t i).backward_contMDiffOn)
    hanchoredLocal Y htimeSet hcontLocal hderivLocal hYLocal

/-- Fixed-IVP finite local-gluing-data gauge-flow existence, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, U sol t i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, Set.univ ⊆ ⋃ i, V sol t i)
    (hlocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i,
        LocalGluingData (I := I) (M := M) 3
          (Fₗ sol i t) (Gₗ sol i t) (U sol t i) (V sol t i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t)
        (U sol t i ∩ U sol t j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t)
        (V sol t i ∩ V sol t j))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ i,
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, U sol t i ⊆ U sol τ i)
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol ivp.initialTime i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol t i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t,
          ∀ i, ∀ x : M, x ∈ U sol t i →
            (Y sol) τ (Fₗ sol i τ x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hlocal hFcompat hGcompat
    tmin tmax hUwithin hanchoredLocal Y htimeSet hcontLocal hderivLocal
    hYLocal⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on indexed open covers, with global forward/backward slices
constructed canonically by `gluedMapOf_iUnion`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t) (U sol i ∩ U sol j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t) (V sol i ∩ V sol j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol i) (V sol i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol i) (U sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol) (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol) (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol) (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol) (fun i ↦ Fₗ sol i τ)) x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hleftLocal sol) (hrightLocal sol) (hFLocal sol) (hGLocal sol)
        (hanchoredLocal sol) (hcontLocal sol) (hderivLocal sol) (hY sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts on indexed open covers, with canonical glued slices, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t) (U sol i ∩ U sol j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t) (V sol i ∩ V sol j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol i) (V sol i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol i) (U sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦
            (extChartAt I
              ((gluedMapOf_iUnion (defaultF sol t) (U sol) (fun j ↦ Fₗ sol j t)) x))
              (Fₗ sol i τ x))
          ((Y sol) t
            ((gluedMapOf_iUnion (defaultF sol t) (U sol) (fun j ↦ Fₗ sol j t)) x))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol) (fun i ↦ Fₗ sol i τ)) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ
              ((gluedMapOf_iUnion (defaultF sol τ) (U sol) (fun i ↦ Fₗ sol i τ)) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    Y tmin tmax htimeSet hcontLocal hderivLocal hY⟩

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts whose derivative and vector-field-identification hypotheses are stated
against the local forward readouts.  The global slices are constructed
canonically by `gluedMapOf_iUnion`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t) (U sol i ∩ U sol j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t) (V sol i ∩ V sol j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol i) (V sol i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol i) (U sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ i, ∀ x : M, x ∈ U sol i →
          (Y sol) τ (Fₗ sol i τ x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp where
  flow := fun sol ↦ by
    have raw :=
      Diffeomorph3GaugeFlowOn.of_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin
        (I := I) (M := M)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (Y := Y sol) (tmin := tmin sol) (tmax := tmax sol)
        (t₀ := ivp.initialTime)
        (defaultF sol) (defaultG sol) (Fₗ sol) (Gₗ sol) (U sol) (V sol)
        (hUcover sol) (hVcover sol) (hUopen sol) (hVopen sol)
        (hFcompat sol) (hGcompat sol) (hFmaps sol) (hGmaps sol)
        (hleftLocal sol) (hrightLocal sol) (hFLocal sol) (hGLocal sol)
        (hanchoredLocal sol) (hcontLocal sol) (hderivLocal sol) (hYLocal sol)
    simpa [htimeSet sol] using raw

/-- Fixed-IVP raw intrinsic DeTurck gauge-flow existence from compatible local
readouts with local derivative and vector-field-identification hypotheses, kept
as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (defaultF defaultG : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ℝ → M → M)
    (Fₗ Gₗ : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → ℝ → M → M)
    (U V : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ι → Set M)
    (hUcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, U sol i)
    (hVcover : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Set.univ ⊆ ⋃ i, V sol i)
    (hUopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (U sol i))
    (hVopen : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, IsOpen (V sol i))
    (hFcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Fₗ sol i t) (Fₗ sol j t) (U sol i ∩ U sol j))
    (hGcompat : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i j, EqOn (Gₗ sol i t) (Gₗ sol j t) (V sol i ∩ V sol j))
    (hFmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Fₗ sol i t) (Set.univ ∩ U sol i) (V sol i))
    (hGmaps : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, MapsTo (Gₗ sol i t) (Set.univ ∩ V sol i) (U sol i))
    (hleftLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, LeftInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ U sol i))
    (hrightLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, RightInvOn (Gₗ sol i t) (Fₗ sol i t) (Set.univ ∩ V sol i))
    (hFLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ sol i t) (U sol i))
    (hGLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ sol i t) (V sol i))
    (hanchoredLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ x ∈ U sol i, Fₗ sol i ivp.initialTime x = x)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hcontLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        ContinuousWithinAt (fun τ : ℝ ↦ Fₗ sol i τ x)
          (Icc (tmin sol) (tmax sol)) t)
    (hderivLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ i, ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M, x ∈ U sol i →
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (Fₗ sol i t x)) (Fₗ sol i τ x))
          ((Y sol) t (Fₗ sol i t x)) (Icc (tmin sol) (tmax sol)) t)
    (hYLocal : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ i, ∀ x : M, x ∈ U sol i →
          (Y sol) τ (Fₗ sol i τ x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    Y tmin tmax htimeSet hcontLocal hderivLocal hYLocal⟩

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

@[simp] theorem ofDiffeomorph3GaugeFlow_flow_maps3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlow (I := I) (M := M) G).flow sol).maps3 =
      G.maps3 sol := rfl

@[simp] theorem ofDiffeomorph3GaugeFlow_flow_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlow (I := I) (M := M) G).flow sol).anchored =
      G.anchored sol := rfl

@[simp] theorem ofDiffeomorph3GaugeFlow_flow_satisfies
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlow (I := I) (M := M) G).flow sol).satisfies =
      G.satisfies sol := rfl

@[simp] theorem toDiffeomorph3GaugeFlow_ofDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (ofDiffeomorph3GaugeFlow (I := I) (M := M) G).toDiffeomorph3GaugeFlow =
      G := rfl

@[simp] theorem ofDiffeomorph3GaugeFlow_toDiffeomorph3GaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ofDiffeomorph3GaugeFlow (I := I) (M := M) G.toDiffeomorph3GaugeFlow =
      G := rfl

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

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence on open solution
time sets from globally glued inverse slices, within-time continuity, and
closed-Picard preferred-chart ODE data for model vector fields. -/
noncomputable def ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
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
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ F ivp sol τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
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
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (F ivp) (G ivp) (hleft ivp) (hright ivp) (hF ivp) (hG ivp)
        (hanchored ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hcont ivp) (hderiv ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from globally
glued inverse slices, within-time continuity, closed-Picard chart ODE data, and
relative-filter field equality, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
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
    (hcont : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ F ivp sol τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
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
  ⟨ofPicardIccChartDerivative_of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin
    F G hleft hright hF hG hanchored Y tmin tmax htimeSet hcont hderiv hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from global glued
forward/backward slices and local readouts on indexed open covers.  This is the
family-level form of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (Fₗ ivp sol i τ x))
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
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (F ivp) (G ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFEq ivp) (hGEqLeft ivp) (hGEq ivp) (hFEqRight ivp)
        (hleftLocal ivp) (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp)
        (hanchoredLocal ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hcontLocal ivp) (hderivLocal ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from local
readouts on indexed open covers and global glued forward/backward slices, kept
as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (Fₗ ivp sol i τ x))
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
  ⟨ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hcontLocal hderivLocal hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from global
glued forward/backward slices and local readouts on open covers that may depend
on the time slice.  This is the family-level form of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol t i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol t i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol t i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol t i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
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
    (hFEqWithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (Fₗ ivp sol i τ x))
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
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (F ivp) (G ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFEq ivp) (hGEqLeft ivp) (hGEq ivp) (hFEqRight ivp)
        (hleftLocal ivp) (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp)
        (hanchoredLocal ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hFEqWithin ivp) (hcontLocal ivp) (hderivLocal ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from local
readouts on time-dependent open covers and global glued forward/backward
slices, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol t i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol t i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol t i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol t i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
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
    (hFEqWithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (F ivp sol t x)) (Fₗ ivp sol i τ x))
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
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hFEqWithin hcontLocal hderivLocal hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from local
readouts on time-dependent open covers, with derivative and
vector-field-identification hypotheses stated against the local forward
readouts.  This is the family-level form of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol t i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol t i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol t i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol t i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
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
    (hFEqWithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hFEqWithinAll : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ i,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (F ivp) (G ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFEq ivp) (hGEqLeft ivp) (hGEq ivp) (hFEqRight ivp)
        (hleftLocal ivp) (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp)
        (hanchoredLocal ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hFEqWithin ivp) (hFEqWithinAll ivp) (hcontLocal ivp)
        (hderivLocal ivp) (hYLocal ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from local
readouts on time-dependent open covers, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    (F G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (F ivp sol t) (Fₗ ivp sol i t) (U ivp sol t i))
    (hGEqLeft : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (G ivp sol t) (Gₗ ivp sol i t)
            ((F ivp sol t) '' (Set.univ ∩ U ivp sol t i)))
    (hGEq : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, EqOn (G ivp sol t) (Gₗ ivp sol i t) (V ivp sol t i))
    (hFEqRight : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          EqOn (F ivp sol t) (Fₗ ivp sol i t)
            ((G ivp sol t) '' (Set.univ ∩ V ivp sol t i)))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
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
    (hFEqWithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hFEqWithinAll : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ i,
            EqOn (F ivp sol τ) (Fₗ ivp sol i τ) (U ivp sol t i))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    F G Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFEq hGEqLeft hGEq
    hFEqRight hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal Y
    tmin tmax htimeSet hFEqWithin hFEqWithinAll hcontLocal hderivLocal
    hYLocal⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts on finite time-dependent open covers, with global
forward/backward slices constructed canonically by `gluedMapOf_iUnion`.  This
is the family-level form of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol t i ∩ U ivp sol t j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol t i ∩ V ivp sol t j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i)
          (V ivp sol t i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol t i)
          (U ivp sol t i))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            U ivp sol t i ⊆ U ivp sol τ i)
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (defaultF ivp) (defaultG ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFcompat ivp) (hGcompat ivp) (hFmaps ivp) (hGmaps ivp)
        (tmin ivp) (tmax ivp) (hUwithin ivp) (hleftLocal ivp)
        (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp) (hanchoredLocal ivp)
        (Y ivp) (htimeSet ivp) (hcontLocal ivp) (hderivLocal ivp)
        (hYLocal ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts on finite time-dependent open covers, kept as proof-level
evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (U ivp sol t i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, IsOpen (V ivp sol t i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol t i ∩ U ivp sol t j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol t i ∩ V ivp sol t j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i)
          (V ivp sol t i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol t i)
          (U ivp sol t i))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            U ivp sol t i ⊆ U ivp sol τ i)
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol t i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol t i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol t i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol t i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps tmin tmax hUwithin hleftLocal hrightLocal
    hFLocal hGLocal hanchoredLocal Y htimeSet hcontLocal hderivLocal
    hYLocal⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts on finite time-dependent open covers supplied by named
`LocalGluingData` patches.  This is the family-level form of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hlocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LocalGluingData (I := I) (M := M) 3
            (Fₗ ivp sol i t) (Gₗ ivp sol i t)
            (U ivp sol t i) (V ivp sol t i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol t i ∩ U ivp sol t j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol t i ∩ V ivp sol t j))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            U ivp sol t i ⊆ U ivp sol τ i)
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (defaultF ivp) (defaultG ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hlocal ivp) (hFcompat ivp)
        (hGcompat ivp) (tmin ivp) (tmax ivp) (hUwithin ivp)
        (hanchoredLocal ivp) (Y ivp) (htimeSet ivp) (hcontLocal ivp)
        (hderivLocal ivp) (hYLocal ivp)).flow sol

/-- Theorem-family finite local-gluing-data gauge-flow existence, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*} [Finite ι]
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ℝ → ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, U ivp sol t i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, Set.univ ⊆ ⋃ i, V ivp sol t i)
    (hlocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LocalGluingData (I := I) (M := M) 3
            (Fₗ ivp sol i t) (Gₗ ivp sol i t)
            (U ivp sol t i) (V ivp sol t i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol t i ∩ U ivp sol t j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol t i ∩ V ivp sol t j))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (hUwithin : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ i,
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t,
            U ivp sol t i ⊆ U ivp sol τ i)
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol ivp.initialTime i,
          Fₗ ivp sol i ivp.initialTime x = x)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol t i →
            HasDerivWithinAt
              (fun τ : ℝ ↦ (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol t i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hlocal hFcompat hGcompat
    tmin tmax hUwithin hanchoredLocal Y htimeSet hcontLocal hderivLocal
    hYLocal⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts on indexed open covers, with global forward/backward slices
constructed canonically by `gluedMapOf_iUnion`.  This is the family-level form
of
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol i ∩ U ivp sol j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol i ∩ V ivp sol j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i)
          (V ivp sol i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol i)
          (U ivp sol i))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦
                (extChartAt I
                  ((gluedMapOf_iUnion (defaultF ivp sol t) (U ivp sol)
                    (fun j ↦ Fₗ ivp sol j t)) x))
                  (Fₗ ivp sol i τ x))
              ((Y ivp sol) t
                ((gluedMapOf_iUnion (defaultF ivp sol t) (U ivp sol)
                  (fun j ↦ Fₗ ivp sol j t)) x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ
                ((gluedMapOf_iUnion (defaultF ivp sol τ) (U ivp sol)
                  (fun i ↦ Fₗ ivp sol i τ)) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((gluedMapOf_iUnion (defaultF ivp sol τ) (U ivp sol)
                  (fun i ↦ Fₗ ivp sol i τ)) x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (defaultF ivp) (defaultG ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFcompat ivp) (hGcompat ivp) (hFmaps ivp) (hGmaps ivp)
        (hleftLocal ivp) (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp)
        (hanchoredLocal ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hcontLocal ivp) (hderivLocal ivp) (hY ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts on indexed open covers, with canonical glued slices, kept as
proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    {ι : Type*}
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol i ∩ U ivp sol j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol i ∩ V ivp sol j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i)
          (V ivp sol i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol i)
          (U ivp sol i))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦
                (extChartAt I
                  ((gluedMapOf_iUnion (defaultF ivp sol t) (U ivp sol)
                    (fun j ↦ Fₗ ivp sol j t)) x))
                  (Fₗ ivp sol i τ x))
              ((Y ivp sol) t
                ((gluedMapOf_iUnion (defaultF ivp sol t) (U ivp sol)
                  (fun j ↦ Fₗ ivp sol j t)) x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ
                ((gluedMapOf_iUnion (defaultF ivp sol τ) (U ivp sol)
                  (fun i ↦ Fₗ ivp sol i τ)) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((gluedMapOf_iUnion (defaultF ivp sol τ) (U ivp sol)
                  (fun i ↦ Fₗ ivp sol i τ)) x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    Y tmin tmax htimeSet hcontLocal hderivLocal hY⟩

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts whose derivative and vector-field-identification hypotheses are
stated against the local forward readouts.  The global slices are constructed
canonically by `gluedMapOf_iUnion`. -/
noncomputable def ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol i ∩ U ivp sol j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol i ∩ V ivp sol j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i)
          (V ivp sol i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol i)
          (U ivp sol i))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦
                (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦
    (IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
        (E := E) (H := H) (I := I) (M := M) (ivp := ivp)
        (defaultF ivp) (defaultG ivp) (Fₗ ivp) (Gₗ ivp) (U ivp) (V ivp)
        (hUcover ivp) (hVcover ivp) (hUopen ivp) (hVopen ivp)
        (hFcompat ivp) (hGcompat ivp) (hFmaps ivp) (hGmaps ivp)
        (hleftLocal ivp) (hrightLocal ivp) (hFLocal ivp) (hGLocal ivp)
        (hanchoredLocal ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
        (hcontLocal ivp) (hderivLocal ivp) (hYLocal ivp)).flow sol

/-- Theorem-family raw intrinsic DeTurck gauge-flow existence from compatible
local readouts with local derivative and vector-field-identification
hypotheses, kept as proof-level evidence. -/
theorem nonempty_ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    {ι : Type*}
    (defaultF defaultG :
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          ℝ → M → M)
    (Fₗ Gₗ : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → ℝ → M → M)
    (U V : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ι → Set M)
    (hUcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, U ivp sol i)
    (hVcover : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Set.univ ⊆ ⋃ i, V ivp sol i)
    (hUopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (U ivp sol i))
    (hVopen : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, IsOpen (V ivp sol i))
    (hFcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Fₗ ivp sol i t) (Fₗ ivp sol j t)
          (U ivp sol i ∩ U ivp sol j))
    (hGcompat : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i j, EqOn (Gₗ ivp sol i t) (Gₗ ivp sol j t)
          (V ivp sol i ∩ V ivp sol j))
    (hFmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i)
          (V ivp sol i))
    (hGmaps : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, MapsTo (Gₗ ivp sol i t) (Set.univ ∩ V ivp sol i)
          (U ivp sol i))
    (hleftLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          LeftInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ U ivp sol i))
    (hrightLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i,
          RightInvOn (Gₗ ivp sol i t) (Fₗ ivp sol i t) (Set.univ ∩ V ivp sol i))
    (hFLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Fₗ ivp sol i t) (U ivp sol i))
    (hGLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t : ℝ, ∀ i, ContMDiffOn I I 3 (Gₗ ivp sol i t) (V ivp sol i))
    (hanchoredLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ x ∈ U ivp sol i, Fₗ ivp sol i ivp.initialTime x = x)
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
    (hcontLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          ContinuousWithinAt (fun τ : ℝ ↦ Fₗ ivp sol i τ x)
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hderivLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ i, ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          x ∈ U ivp sol i →
            HasDerivWithinAt
              (fun τ : ℝ ↦
                (extChartAt I (Fₗ ivp sol i t x)) (Fₗ ivp sol i τ x))
              ((Y ivp sol) t (Fₗ ivp sol i t x))
              (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hYLocal : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t,
            ∀ i, ∀ x : M, x ∈ U ivp sol i →
              (Y ivp sol) τ (Fₗ ivp sol i τ x) =
                intrinsicDeTurckGaugeField (I := I) (M := M)
                  sol.1.toIntrinsicDeTurckSolution.metric
                  sol.1.toIntrinsicDeTurckSolution.background τ (Fₗ ivp sol i τ x)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :=
  ⟨ofPicardIccChartDerivative_of_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin
    defaultF defaultG Fₗ Gₗ U V hUcover hVcover hUopen hVopen hFcompat
    hGcompat hFmaps hGmaps hleftLocal hrightLocal hFLocal hGLocal hanchoredLocal
    Y tmin tmax htimeSet hcontLocal hderivLocal hYLocal⟩

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

/-- Assemble theorem-family raw gauge-flow existence from fixed-IVP raw
gauge-flow existence data for every initial-value problem.  This lets
fixed-IVP handoffs feed the theorem-family layer without duplicating each long
constructor signature. -/
noncomputable def of_forInitialValueProblem
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicDeTurckGaugeFlowExistence
        (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M) where
  flow := fun ivp sol ↦ (G ivp).flow sol

@[simp] theorem of_forInitialValueProblem_flow
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicDeTurckGaugeFlowExistence
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((of_forInitialValueProblem (I := I) (M := M) G).flow ivp sol) =
      (G ivp).flow sol := rfl

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

@[simp] theorem forInitialValueProblem_of_forInitialValueProblem
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicDeTurckGaugeFlowExistence
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (of_forInitialValueProblem (I := I) (M := M) G).forInitialValueProblem ivp =
      G ivp := rfl

@[simp] theorem of_forInitialValueProblem_forInitialValueProblem
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    of_forInitialValueProblem (I := I) (M := M)
      (fun ivp ↦ G.forInitialValueProblem ivp) = G := rfl

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

/-- Assemble proof-level theorem-family raw gauge-flow existence from
proof-level fixed-IVP raw gauge-flow existence for every initial-value problem. -/
theorem nonempty_of_forInitialValueProblem
    (hG : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (IntrinsicDeTurckGaugeFlowExistence
        (E := E) (H := H) (I := I) (M := M) ivp)) :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) := by
  classical
  exact ⟨of_forInitialValueProblem (I := I) (M := M)
    (fun ivp ↦ Classical.choice (hG ivp))⟩

/-- Theorem-family raw gauge-flow existence is equivalent to fixed-IVP raw
gauge-flow existence for every initial-value problem. -/
theorem nonempty_iff_forall_nonempty_forInitialValueProblem :
    Nonempty (IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) ↔
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (IntrinsicDeTurckGaugeFlowExistence
        (E := E) (H := H) (I := I) (M := M) ivp) := by
  constructor
  · intro hG ivp
    exact nonempty_forInitialValueProblem (I := I) (M := M) hG ivp
  · exact nonempty_of_forInitialValueProblem (I := I) (M := M)

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

@[simp] theorem ofDiffeomorph3GaugeFlowFamily_flow_maps3
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G).flow ivp sol).maps3 =
      G.maps3 ivp sol := rfl

@[simp] theorem ofDiffeomorph3GaugeFlowFamily_flow_anchored
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G).flow ivp sol).anchored =
      G.anchored ivp sol := rfl

@[simp] theorem ofDiffeomorph3GaugeFlowFamily_flow_satisfies
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ((ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G).flow ivp sol).satisfies =
      G.satisfies ivp sol := rfl

@[simp] theorem forInitialValueProblem_ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G).forInitialValueProblem ivp =
      IntrinsicDeTurckGaugeFlowExistence.ofDiffeomorph3GaugeFlow
        (I := I) (M := M) (G.forInitialValueProblem ivp) := rfl

@[simp] theorem toDiffeomorph3GaugeFlowFamily_ofDiffeomorph3GaugeFlowFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    (ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G).toDiffeomorph3GaugeFlowFamily =
      G := rfl

@[simp] theorem ofDiffeomorph3GaugeFlowFamily_toDiffeomorph3GaugeFlowFamily
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ofDiffeomorph3GaugeFlowFamily (I := I) (M := M) G.toDiffeomorph3GaugeFlowFamily =
      G := rfl

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
