/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.ParametrizedInner
import PoincareCurvature.Analysis.MatrixSmoothness
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

omit [ContMDiffVectorBundle n F V IB] in
/-- **Positive-definiteness of the local-frame Gram form of a Riemannian metric.**  For `c ≠ 0`,
`∑ᵢⱼ cᵢ cⱼ · g.inner x (frameᵢ) (frameⱼ) > 0`, since it equals `g.inner x w w` for the nonzero
combination `w = ∑ᵢ cᵢ • frameᵢ` and the metric is positive-definite. -/
theorem timeDependentGram_pos
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) {c : ι → ℝ} (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := by
  classical
  let w : V x := ∑ i, c i • e.localFrame bas i x
  have hw : w ≠ 0 := by
    intro hw0
    apply hc
    calc
      c = (e.basisAt bas hx).repr w := by
        simpa [w, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := bas) hx]
          using ((e.basisAt bas hx).repr_sum_self c).symm
      _ = 0 := by simp [hw0]
  have hsum :
      g.inner x w w =
        ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := by
    show (g.inner x) (∑ i, c i • e.localFrame bas i x) (∑ j, c j • e.localFrame bas j x) = _
    rw [_root_.map_sum (g.inner x), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      _root_.map_sum (g.inner x (e.localFrame bas i x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  calc
    0 < g.inner x w w := g.pos x w hw
    _ = ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := hsum

omit [ContMDiffVectorBundle n F V IB] in
/-- **The local-frame Gram matrix of a Riemannian metric is nonsingular.**  Its determinant is
nonzero at every base point of the trivialization, since positive-definiteness rules out a nontrivial
kernel vector.  This discharges the nonsingularity hypothesis of
`PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec` for the time-dependent Gram
readout. -/
theorem timeDependentGram_det_ne_zero
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) :
    (show Matrix ι ι ℝ from
        (fun i j ↦ g.inner x (e.localFrame bas i x) (e.localFrame bas j x))).det ≠ 0 := by
  classical
  let A : Matrix ι ι ℝ := fun i j ↦ g.inner x (e.localFrame bas i x) (e.localFrame bas j x)
  intro hA
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  have hAcA : A.mulVec c = 0 := by simpa [A] using hAc
  have hAc' : ∀ i, ∑ j, A i j * c j = 0 := by
    intro i
    have hi := congrFun hAcA i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hsum :
      ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) = 0 := by
    calc
      ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x)
          = ∑ i, c i * (∑ j, A i j * c j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [A]
            ring
      _ = ∑ i, c i * 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hAc' i]
      _ = 0 := by simp
  have hpos := timeDependentGram_pos g e bas hx hc
  rw [hsum] at hpos
  exact lt_irrefl 0 hpos

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

/-- **Joint `(t, x)` smoothness of the raised-covector coefficients.**  Combining the joint Gram
readout, the joint one-form pairing, and Gram nonsingularity through the Cramer-solve smoothness
`contMDiffOn_matrixInv_mulVec`, the raised-covector coefficient family
`cᵢ(t, x) = (G(t, x)⁻¹ *ᵥ b(t, x))ᵢ` — where `Gᵢⱼ = (g t).inner x (frameᵢ) (frameⱼ)` and
`bⱼ = ω t x (frameⱼ)` — is `ContMDiffOn` over `Set.univ ×ˢ u`, valued in `ι → ℝ`.  This is the joint
`(t, x)` version of the raised-coefficient formula `cᵢ = ∑ⱼ (Gram⁻¹)ᵢⱼ · ω(frameⱼ)`, the coefficients
of the space-time raised section. -/
theorem contMDiffOn_timeDependentRaisedCoeff
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (hω : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n
      (fun p : ℝ × B ↦ (show ι → ℝ from
        ((show Matrix ι ι ℝ from
            (fun i j ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2)))⁻¹
          : Matrix ι ι ℝ).mulVec (fun j ↦ ω p.1 p.2 (e.localFrame bas j p.2)))) (Set.univ ×ˢ u) :=
  PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec
    (contMDiffOn_timeDependentGramReadout g e bas hu' hg)
    (contMDiffOn_timeDependentOneFormPairing ω e bas hu' hω)
    (fun p hp ↦ timeDependentGram_det_ne_zero (g p.1) e bas (hu' hp.2))

/-- **Joint `(t, x)` smoothness of a raised section assembled from smooth coefficients.**  Given a
jointly `(t, x)`-smooth family of coefficients `c(t, x) : ι → ℝ`, the raised section
`(t, x) ↦ ∑ᵢ c(t, x)ᵢ • frameᵢ(x)` — a section of the bundle `V` along `Prod.snd : ℝ × B → B` — is
`ContMDiffOn` over `Set.univ ×ˢ u`.  Combined with `contMDiffOn_timeDependentRaisedCoeff` (whose output
is exactly such a `c`), this produces the joint `(t, x)` smoothness of the raised gauge field on a
single chart patch — the per-patch `hXfield`.  The proof composes the smooth inverse trivialization
`e.symm` with the smooth coordinate map `(t, x) ↦ (x, ∑ᵢ c(t, x)ᵢ • basᵢ)`. -/
theorem contMDiffOn_raisedSection_of_coeff
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    {c : ℝ × B → ι → ℝ}
    (hc : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n c (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' F p.2 (∑ i, c p i • e.localFrame bas i p.2))
      (Set.univ ×ˢ u) := by
  have hcoord : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n
      (fun p : ℝ × B ↦ ∑ i, c p i • bas i) (Set.univ ×ˢ u) := by
    classical
    have hs : ∀ t : Finset ι, ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n
        (fun p : ℝ × B ↦ ∑ i ∈ t, c p i • bas i) (Set.univ ×ˢ u) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using (contMDiffOn_const (c := (0 : F)))
      | insert i t hi ih =>
        simp only [Finset.sum_insert hi]
        exact (((contMDiffOn_pi_space.mp hc) i).smul contMDiffOn_const).add ih
    exact hs Finset.univ
  have hh : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ ((p.2, ∑ i, c p i • bas i) : B × F)) (Set.univ ×ˢ u) :=
    (contMDiff_snd.contMDiffOn).prodMk hcoord
  have hmaps : Set.MapsTo (fun p : ℝ × B ↦ ((p.2, ∑ i, c p i • bas i) : B × F))
      (Set.univ ×ˢ u) e.target := fun p hp ↦ e.mem_target.mpr (hu' hp.2)
  have hcomp := (Bundle.Trivialization.contMDiffOn_symm e (n := n)).comp hh hmaps
  refine hcomp.congr fun p hp ↦ ?_
  have hp2 : p.2 ∈ e.baseSet := hu' hp.2
  have hframe : ∀ i : ι, e.localFrame bas i p.2 = e.symm p.2 (bas i) := by
    intro i
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet e bas hp2]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
  have hlin : e.symm p.2 (∑ i, c p i • bas i) = ∑ i, c p i • e.symm p.2 (bas i) := by
    have h := map_sum (e.symmL ℝ p.2) (fun i => c p i • bas i) Finset.univ
    simp only [map_smul, Bundle.Trivialization.symmL_apply] at h
    exact h
  show TotalSpace.mk' F p.2 (∑ i, c p i • e.localFrame bas i p.2)
      = e.toOpenPartialHomeomorph.symm ((p.2, ∑ i, c p i • bas i))
  rw [← Bundle.Trivialization.mk_symm e hp2, hlin]
  refine congrArg (TotalSpace.mk' F p.2) ?_
  exact (Finset.sum_congr rfl fun i _ => by rw [hframe i]).symm

end Gram

end PoincareCurvature.ParametrizedInner
