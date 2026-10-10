/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.TimeDependentGram

/-!
# Joint regularity of an inverse-metric bilinear contraction

Unlike raising a traced one-form, the conventional DeTurck field contracts both
input slots of a vector-valued bilinear tensor. This file proves the joint
regularity of that local-frame expression from the actual metric and tensor
sections. Nonsingularity of the Gram matrix follows from positive definiteness;
no inverse-matrix regularity or contracted-field regularity is assumed.
-/

open Bundle Manifold
open scoped Manifold Topology BigOperators

namespace PoincareCurvature.ParametrizedInner

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]

/-- Contract the two covariant slots with the actual inverse Gram matrix.
The resulting vector section is jointly `C^n` on the frame patch. -/
theorem contMDiffOn_timeDependentMetricContraction
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (C : ℝ → ∀ x : B, V x →L[ℝ] V x →L[ℝ] V x)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB)
      (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x : B => V x →L[ℝ] V x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (hC : ContMDiffOn (𝓘(ℝ).prod IB)
      (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] F)) n
      (fun p : ℝ × B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] F)
        (E := fun x : B => V x →L[ℝ] V x →L[ℝ] V x) p.2
        (C p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B => TotalSpace.mk' F p.2
        (∑ i, ∑ j,
          ((Matrix.of (fun a b => (g p.1).inner p.2
            (e.localFrame bas a p.2) (e.localFrame bas b p.2)))⁻¹) i j •
          C p.1 p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2)))
      (Set.univ ×ˢ u) := by
  classical
  let S : Set (ℝ × B) := Set.univ ×ˢ u
  let A : ℝ × B → ι → ι → ℝ := fun p a b =>
    (g p.1).inner p.2 (e.localFrame bas a p.2) (e.localFrame bas b p.2)
  let c : ℝ × B → ι → ι → F := fun p i j =>
    (e (TotalSpace.mk' F p.2
      (C p.1 p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2)))).2
  have hA : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ι → ℝ) n
      (fun p => (show ι → ι → ℝ from ((Matrix.of (A p))⁻¹ : Matrix ι ι ℝ))) S := by
    convert MatrixSmoothness.contMDiffOn_matrixInv
      (contMDiffOn_timeDependentGramReadout g e bas hu hg)
      (fun p hp => timeDependentGram_det_ne_zero (g p.1) e bas (hu hp.2)) using 1 <;> rfl
  have hframe (i : ι) : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B => TotalSpace.mk' F p.2 (e.localFrame bas i p.2)) S :=
    contMDiffOn_frameSection_prodSnd e bas hu i
  have hCC (i j : ι) : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B => TotalSpace.mk' F p.2
        (C p.1 p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2))) S :=
    hC.clm_bundle_apply₂ (F₁ := F) (F₂ := F) (hframe i) (hframe j)
  have hc (i j : ι) : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n
      (fun p => c p i j) S := by
    have htriv := e.contMDiffOn.comp (hCC i j)
      (fun p hp => e.mem_source.mpr (hu hp.2))
    exact contMDiff_snd.comp_contMDiffOn htriv
  let coord : ℝ × B → F := fun p => ∑ i, ∑ j, (Matrix.of (A p))⁻¹ i j • c p i j
  have hcoord : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n coord S := by
    intro p hp
    apply ContMDiffWithinAt.sum
    intro i _
    apply ContMDiffWithinAt.sum
    intro j _
    convert ((MatrixSmoothness.contMDiffOn_matrixEntry hA i j) p hp).smul
      (hc i j p hp) using 1 <;> rfl
  have hpair : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B => (p.2, coord p)) S :=
    contMDiff_snd.contMDiffOn.prodMk hcoord
  have hresult := e.contMDiffOn_symm.comp hpair
    (fun p hp => e.mem_target.mpr (hu hp.2))
  refine hresult.congr ?_
  intro p hp
  have hbase := hu hp.2
  change TotalSpace.mk' F p.2 _ =
    e.toOpenPartialHomeomorph.symm (p.2, coord p)
  rw [← e.mk_symm hbase]
  apply congrArg (TotalSpace.mk' F p.2)
  change (∑ i, ∑ j, (Matrix.of (A p))⁻¹ i j •
      C p.1 p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2)) =
    e.symm p.2 (coord p)
  symm
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hbase]
  simp only [coord, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [Bundle.Trivialization.symmL_apply e hbase]
  exact e.symm_apply_apply_mk hbase _

/-- Negation preserves joint regularity of a vector section along an arbitrary
base map. This avoids treating a time-dependent section as an ordinary section
of the spatial bundle. -/
theorem contMDiff_paramSection_neg
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HM N]
    {b : N → B} {v : ∀ p : N, V (b p)}
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun p => TotalSpace.mk' F (b p) (v p))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun p => TotalSpace.mk' F (b p) (-v p)) := by
  intro p₀
  have h := Bundle.contMDiffAt_totalSpace.mp (hv p₀)
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨h.1, ?_⟩
  let e : Trivialization F (π F V) := trivializationAt F V (b p₀)
  have hbase : ∀ᶠ p in 𝓝 p₀, b p ∈ e.baseSet :=
    h.1.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V (b p₀)))
  refine h.2.neg.congr_of_eventuallyEq ?_
  filter_upwards [hbase] with p hp
  change (e (TotalSpace.mk' F (b p) (-v p))).2 =
    -(e (TotalSpace.mk' F (b p) (v p))).2
  have hneg := map_neg (e.linearMapAt ℝ (b p)) (v p)
  simpa only [Bundle.Trivialization.linearMapAt_apply, hp, if_pos] using hneg

end PoincareCurvature.ParametrizedInner
