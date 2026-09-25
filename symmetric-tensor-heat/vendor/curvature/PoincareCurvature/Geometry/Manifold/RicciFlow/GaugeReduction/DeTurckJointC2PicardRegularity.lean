import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointC2CoordinateBridge

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Product `C²` regularity and the spatial Picard derivatives

This file isolates the analytic passage from a jointly `C²` product-domain
field to the two spatial derivative-continuity statements used by the
coordinate Picard estimates.  The spatial derivative is obtained by composing
the total derivative with the fixed product inclusion `y ↦ (t, y)`; the
second spatial derivative is obtained by repeating that argument for the
first spatial derivative.  No geometric assumptions are hidden in this
lemma.
-/

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- A jointly `C²` field has jointly continuous value, spatial derivative, and
second spatial derivative on an open product domain. -/
theorem continuousOn_spatial_picard_data_of_contDiffOn_prod_two
    {f : ℝ → E → E} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (2 : ℕ∞) (Function.uncurry f) (Set.univ ×ˢ s)) :
    ContinuousOn
        (fun p : ℝ × E =>
          (f p.1 p.2, fderiv ℝ (f p.1) p.2))
        (Set.univ ×ˢ s) ∧
      ContinuousOn
        (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
        (Set.univ ×ˢ s) := by
  let U : Set (ℝ × E) := Set.univ ×ˢ s
  let inr : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let D : (ℝ × E) → (ℝ × E →L[ℝ] E) := fderiv ℝ (Function.uncurry f)
  let G : (ℝ × E) → (E →L[ℝ] E) := fun p => (D p).comp inr
  have hU : IsOpen U := isOpen_univ.prod hs
  have hf_cont : ContinuousOn (Function.uncurry f) U := by
    simpa [U] using hf.continuousOn
  have hD : ContDiffOn ℝ (1 : ℕ∞) D U := by
    simpa [D] using hf.fderiv_of_isOpen hU (by norm_num)
  have hG : ContDiffOn ℝ (1 : ℕ∞) G U := by
    have hinr : ContDiffOn ℝ (1 : ℕ∞) (fun _ : ℝ × E => inr) U :=
      contDiff_const.contDiffOn
    simpa [G] using hD.clm_comp hinr
  have hG_cont : ContinuousOn G U := hG.continuousOn
  have hpartial (p : ℝ × E) (hp : p ∈ U) :
      fderiv ℝ (f p.1) p.2 = G p := by
    have hFdiff : DifferentiableAt ℝ (Function.uncurry f) p := by
      exact (hf p hp).contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by norm_num)
    have hslice : DifferentiableAt ℝ (fun y : E => (p.1, y)) p.2 :=
      (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
    have hcomp :=
      fderiv_comp (f := fun y : E => (p.1, y)) (g := Function.uncurry f)
        p.2 hFdiff hslice
    have hinr' : fderiv ℝ (fun y : E => (p.1, y)) p.2 = inr :=
      (hasFDerivAt_prodMk_right p.1 p.2).fderiv
    calc
      fderiv ℝ (f p.1) p.2 =
          fderiv ℝ (Function.uncurry f ∘ fun y : E => (p.1, y)) p.2 := by
            rfl
      _ = (D p).comp (fderiv ℝ (fun y : E => (p.1, y)) p.2) := by
            simpa [D] using hcomp
      _ = G p := by rw [hinr']
  have hpair : ContinuousOn
      (fun p : ℝ × E => (Function.uncurry f p, G p)) U :=
    hf_cont.prodMk hG_cont
  have hfirst : ContinuousOn
      (fun p : ℝ × E => (f p.1 p.2, fderiv ℝ (f p.1) p.2)) U := by
    refine hpair.congr (fun p hp => ?_)
    rw [hpartial p hp]
    rfl
  have hDG : ContDiffOn ℝ (0 : ℕ∞) (fderiv ℝ G) U :=
    hG.fderiv_of_isOpen hU (by norm_num)
  have hDG_cont : ContinuousOn (fderiv ℝ G) U := hDG.continuousOn
  let H : (ℝ × E) → (E →L[ℝ] (E →L[ℝ] E)) :=
    fun p => (fderiv ℝ G p).comp inr
  have hH_cont : ContinuousOn H U := by
    have hinr : ContinuousOn (fun _ : ℝ × E => inr) U := continuousOn_const
    simpa [H] using hDG_cont.clm_comp hinr
  have hsecond (p : ℝ × E) (hp : p ∈ U) :
      fderiv ℝ (fderiv ℝ (f p.1)) p.2 = H p := by
    have hGdiff : DifferentiableAt ℝ G p := by
      exact (hG p hp).contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by norm_num)
    have hslice : DifferentiableAt ℝ (fun y : E => (p.1, y)) p.2 :=
      (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
    have hinr' : fderiv ℝ (fun y : E => (p.1, y)) p.2 = inr :=
      (hasFDerivAt_prodMk_right p.1 p.2).fderiv
    have heq : (fun y : E => G (p.1, y)) =ᶠ[𝓝 p.2]
        (fun y : E => fderiv ℝ (f p.1) y) := by
      filter_upwards [hs.mem_nhds (show p.2 ∈ s from hp.2)] with y hy
      exact (hpartial (p.1, y) ⟨mem_univ _, hy⟩).symm
    have hcomp : HasFDerivAt (G ∘ fun y : E => (p.1, y))
        ((fderiv ℝ G p).comp (fderiv ℝ (fun y : E => (p.1, y)) p.2)) p.2 :=
      hGdiff.hasFDerivAt.comp p.2 hslice.hasFDerivAt
    have hcomp' : HasFDerivAt (fun y : E => fderiv ℝ (f p.1) y)
        ((fderiv ℝ G p).comp (fderiv ℝ (fun y : E => (p.1, y)) p.2)) p.2 := by
      apply hcomp.congr_of_eventuallyEq
      simpa [Function.comp_def] using heq.symm
    have hcomp'' := hcomp'.fderiv
    calc
      fderiv ℝ (fderiv ℝ (f p.1)) p.2 =
          (fderiv ℝ G p).comp (fderiv ℝ (fun y : E => (p.1, y)) p.2) := hcomp''
      _ = H p := by rw [hinr']
  have hsecond' : ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2) U := by
    exact hH_cont.congr (fun p hp => hsecond p hp)
  simpa [U] using And.intro hfirst hsecond'

/-! **The exact Picard regularity package.** -/

/-- A jointly intrinsic `C²` DeTurck section supplies the exact three regularity
premises consumed by `deTurckGaugeCoordinatePicardEstimates`, after an explicit
chart-containment buffer is provided.  The theorem does not infer the joint
intrinsic premise from the current slicewise metric and connection families. -/
theorem deTurckGaugeCoordinateField_picardRegularityPackage_of_joint_intrinsic_contMDiffOn_two
    [I.Boundaryless]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) {t₀ : ℝ} {y₀ : E} {a : ℝ≥0}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun r : ℝ × M =>
        (⟨r.2, intrinsicDeTurckGaugeField (I := I) (M := M) g background r.1 r.2⟩ :
          TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p₀).source))
    (hball : Metric.closedBall y₀ ((a : ℝ) + 1) ⊆ (extChartAt I p₀).target) :
    (∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ (2 : ℕ∞)
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
        (Metric.ball y₀ ((a : ℝ) + 1))) ∧
      ContinuousOn
        (fun p : ℝ × E =>
          (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1 p.2,
            fderiv ℝ
              (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1) p.2))
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall y₀ (a : ℝ)) ∧
      ContinuousOn
        (fun p : ℝ × E =>
          fderiv ℝ
            (fderiv ℝ
              (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1)) p.2)
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall y₀ (a : ℝ)) := by
  let f : ℝ → E → E :=
    deTurckGaugeCoordinateField (I := I) (M := M) g background p₀
  have hprod :=
    deTurckGaugeCoordinateField_contDiffOn_prod_of_intrinsic_contMDiffOn_two
      (I := I) (M := M) g background p₀ hX
  have hprod' : ContDiffOn ℝ (2 : ℕ∞) (Function.uncurry f)
      (Set.univ ×ˢ (extChartAt I p₀).target) := by
    change ContDiffOn ℝ (2 : ℕ∞)
      (fun r : ℝ × E => f r.1 r.2)
      (Set.univ ×ˢ (extChartAt I p₀).target)
    simpa [f] using hprod
  have hball_open_sub : Metric.ball y₀ ((a : ℝ) + 1) ⊆ (extChartAt I p₀).target :=
    Metric.ball_subset_closedBall.trans hball
  have hclosed_sub : Metric.closedBall y₀ (a : ℝ) ⊆
      Metric.ball y₀ ((a : ℝ) + 1) := by
    exact Metric.closedBall_subset_ball
      (by linarith [show (0 : ℝ) ≤ a from a.coe_nonneg])
  have hclosed_target : Metric.closedBall y₀ (a : ℝ) ⊆ (extChartAt I p₀).target :=
    hclosed_sub.trans hball_open_sub
  have hslice (t : ℝ) :
      ContDiffOn ℝ (2 : ℕ∞) (fun y : E => (t, y))
        (Metric.ball y₀ ((a : ℝ) + 1)) := by
    exact (contDiff_const.prodMk contDiff_id).contDiffOn
  have hreg : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ (2 : ℕ∞) (f t)
        (Metric.ball y₀ ((a : ℝ) + 1)) := by
    intro t ht
    have hmaps : MapsTo (fun y : E => (t, y))
        (Metric.ball y₀ ((a : ℝ) + 1))
        (Set.univ ×ˢ (extChartAt I p₀).target) := by
      intro y hy
      exact ⟨mem_univ _, hball_open_sub hy⟩
    have hcomp := hprod.comp (hslice t) hmaps
    simpa [f, Function.comp_def] using hcomp
  have hdata :=
    continuousOn_spatial_picard_data_of_contDiffOn_prod_two
      (s := (extChartAt I p₀).target)
      (isOpen_extChartAt_target (I := I) p₀) hprod'
  have hsubset : Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall y₀ (a : ℝ) ⊆
      Set.univ ×ˢ (extChartAt I p₀).target := by
    intro p hp
    exact ⟨mem_univ _, hclosed_target hp.2⟩
  refine ⟨hreg, ?_, ?_⟩
  · simpa [f] using hdata.1.mono hsubset
  · simpa [f] using hdata.2.mono hsubset

end RicciFlow
