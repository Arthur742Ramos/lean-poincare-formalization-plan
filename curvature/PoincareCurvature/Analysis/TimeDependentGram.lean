/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.ParametrizedInner
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Joint `(t, x)` smoothness of the local-frame Gram matrix of a time-dependent metric

The joint space-time smoothness of the Ricci–DeTurck gauge field reduces, via the raised-covector
coefficient formula, to inverting the local-frame Gram matrix of the *time-dependent* metric jointly
in `(t, x)`.  The field-independent matrix calculus that inverts and contracts such a jointly-smooth
matrix already exists (`PoincareCurvature.MatrixSmoothness`).  The missing input is the joint
`(t, x)` smoothness of the Gram *readout* itself,
`G(t, x)ᵢⱼ = (g t).inner x (frameᵢ x) (frameⱼ x)`.

Given a time-dependent metric `g : ℝ → ContMDiffRiemannianMetric` whose fibrewise bilinear form is
**jointly** `(t, x)`-smooth (the honest "time-dependent Riemannian raising" datum), this file proves
that readout is `ContMDiffOn` over `ℝ × B`, valued in `ι → ι → ℝ` — exactly the matrix family the
`contMDiffOn_matrixInv_mulVec` / `contMDiffOn_bilinForm` core consumes.

The proof feeds the joint metric section and the (time-independent) local frame vectors into the
parameter-dependent bilinear-form apply lemma `contMDiffOn_paramBilin_apply₂` from
`PoincareCurvature.Analysis.ParametrizedInner`, with parameter manifold `ℝ × B` and base map
`Prod.snd`.
-/

open Manifold Bundle
open scoped Manifold Topology

namespace PoincareCurvature.ParametrizedInner

section Gram

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]

/-- **Joint `(t, x)` smoothness of a time-independent local frame section, over the space-time base.**
Composing the spatial `contMDiffOn_localFrame_baseSet` with `Prod.snd : ℝ × B → B`.  This is the
common `v`/`w` input to both the Gram readout and the one-form pairing readout. -/
theorem contMDiffOn_frameSection_prodSnd
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet) (k : ι) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ (TotalSpace.mk' F p.2 (e.localFrame bas k p.2))) (Set.univ ×ˢ u) := by
  have hspatial : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun x : B ↦ TotalSpace.mk' F x (e.localFrame bas k x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := IB) (e := e)
      (n := n) (b := bas) k).mono hu'
  exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp ↦ hp.2)

/-- **Joint `(t, x)` smoothness of a fixed pair of frame vectors paired by a time-dependent metric.**
If the fibrewise bilinear form `(g t).inner` of a time-dependent metric is jointly `(t, x)`-smooth
over `ℝ ×ˢ u`, and `i j` index a local frame of a trivialization `e` with `u ⊆ e.baseSet`, then the
scalar `(t, x) ↦ (g t).inner x (frameᵢ x) (frameⱼ x)` is `ContMDiffOn` over `Set.univ ×ˢ u`. -/
theorem contMDiffOn_timeDependentInner_localFrame
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (i j : ι) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ) n
      (fun p : ℝ × B ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2))
      (Set.univ ×ˢ u) := by
  have hframe : ∀ k : ι, ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ (TotalSpace.mk' F p.2 (e.localFrame bas k p.2))) (Set.univ ×ˢ u) := by
    intro k
    have hspatial : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
        (fun x : B ↦ TotalSpace.mk' F x (e.localFrame bas k x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := IB) (e := e)
        (n := n) (b := bas) k).mono hu'
    exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp ↦ hp.2)
  exact contMDiffOn_paramBilin_apply₂ (b := Prod.snd) (v := fun p ↦ e.localFrame bas i p.2)
    (w := fun p ↦ e.localFrame bas j p.2) (ψ := fun p ↦ (g p.1).inner p.2) hg (hframe i) (hframe j)

/-- **Joint `(t, x)` smoothness of the time-dependent local-frame Gram readout.**  Packaging the
previous lemma over all index pairs, the matrix-valued readout
`(t, x) ↦ fun i j ↦ (g t).inner x (frameᵢ x) (frameⱼ x)` is `ContMDiffOn` over `Set.univ ×ˢ u`,
valued in `ι → ι → ℝ`.  This is exactly the shape of the matrix family fed to
`PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec` and `contMDiffOn_bilinForm`. -/
theorem contMDiffOn_timeDependentGramReadout
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ι → ℝ) n
      (fun p : ℝ × B ↦
        (fun i j ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2) : ι → ι → ℝ))
      (Set.univ ×ˢ u) := by
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro j
  exact contMDiffOn_timeDependentInner_localFrame g e bas hu' hg i j

/-- **Joint `(t, x)` smoothness of a time-dependent one-form pairing readout.**  Given a
time-dependent field of covectors `ω t : Π y, V y →L[ℝ] ℝ` whose section `(t, x) ↦ ω t x` is jointly
`(t, x)`-smooth over `ℝ ×ˢ u`, the pairing readout `(t, x) ↦ fun j ↦ ω t x (frameⱼ x)` is
`ContMDiffOn` over `Set.univ ×ˢ u`, valued in `ι → ℝ`.  This is the vector family `b(t, x)ⱼ` fed
(alongside the inverse Gram matrix) to `PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec`
to obtain the joint `(t, x)` raised-covector coefficients. -/
theorem contMDiffOn_timeDependentOneFormPairing
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hω : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n
      (fun p : ℝ × B ↦ (fun j ↦ ω p.1 p.2 (e.localFrame bas j p.2) : ι → ℝ)) (Set.univ ×ˢ u) := by
  rw [contMDiffOn_pi_space]
  intro j
  exact contMDiffOn_paramLinear_apply (b := Prod.snd) (v := fun p ↦ e.localFrame bas j p.2)
    (φ := fun p ↦ ω p.1 p.2) hω (contMDiffOn_frameSection_prodSnd e bas hu' j)

end Gram

end PoincareCurvature.ParametrizedInner
