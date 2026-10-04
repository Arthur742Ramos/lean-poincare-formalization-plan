/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.TimeDependentMetricContraction
import PoincareCurvature.Geometry.Manifold.RicciFlow.MetricContractedDeTurckField
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointCorrectionTensorRegularity
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointFieldCompactGaugeFlow

/-!
# Joint regularity of the conventional metric-contracted DeTurck field

This is the two-input-slot contraction of the actual chosen/background
connection difference. It is not the legacy raised trace one-form. The joint
metric and explicit correction tensor give joint regularity through the actual
inverse-Gram formula. The correction-functional corollary further lowers the
analytic inputs using the existing geometric Riesz/Gram reconstruction.

All time--space regularity inputs are explicit. Slicewise metric/connection
families alone do not supply them, and no parabolic solution is constructed.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance metricContractionTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance metricContractionTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

/-- The conventional field is the inverse Gram contraction of the actual
explicit correction tensor, using any smooth metric representative agreeing
with the defining `C²` metric. The agreement is about metric values only. -/
theorem metricContractedDeTurckVectorField_eq_sum_inverseGram_correction
    (g : MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : ConnectionFamily (I := I) (M := M))
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (t : ℝ)
    (e : Trivialization E (π E TM)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) :
    metricContractedDeTurckVectorField (I := I) (M := M) g background t x =
      ∑ i, ∑ j,
        ((show Matrix ι ι ℝ from fun a b => (gSmooth t).inner x
          (e.localFrame bas a x) (e.localFrame bas b x))⁻¹) i j •
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame bas i x) (e.localFrame bas j x) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let basis := e.basisAt bas hx
  have hframe (i : ι) : basis i = e.localFrame bas i x := by
    simp [basis, Bundle.Trivialization.basisAt,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := bas) hx]
  have hGram : Matrix.gram ℝ basis =
      (show Matrix ι ι ℝ from fun a b => (gSmooth t).inner x
        (e.localFrame bas a x) (e.localFrame bas b x)) := by
    ext i j
    simp only [Matrix.gram_apply, hframe]
    exact hinner t x _ _
  change CovariantDerivative.metricConnectionDifferenceVector
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x = _
  rw [CovariantDerivative.metricConnectionDifferenceVector_eq_sum_inverseGram
    _ _ x basis, hGram]
  simp_rw [hframe, intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection]

set_option maxHeartbeats 2000000 in
/-- The genuine conventional vector section is jointly smooth if the actual
metric and explicit correction tensor are jointly smooth. Neither the inverse
Gram matrix nor the contracted field is assumed smooth. -/
theorem contMDiff_metricContractedDeTurckVectorField_of_joint_correction
    (g : MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((gSmooth p.1).inner p.2)))
    (hcorrection : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
        (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2))) :
    ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2,
        metricContractedDeTurckVectorField (I := I) (M := M) g background p.1 p.2⟩ :
        TangentBundle I M)) := by
  letI : FiberBundle E (TangentSpace I : M → Type _) :=
    metricContractionTangentFiberBundle (I := I) (M := M)
  letI : VectorBundle ℝ E (TangentSpace I : M → Type _) :=
    metricContractionTangentVectorBundle (I := I) (M := M)
  intro p₀
  let e : Trivialization E (π E TM) := trivializationAt E TM p₀.2
  letI hAtlas : MemTrivializationAtlas e := by infer_instance
  let S : Set (ℝ × M) := Set.univ ×ˢ e.baseSet
  have hp₀ : p₀ ∈ S :=
    ⟨Set.mem_univ _, FiberBundle.mem_baseSet_trivializationAt E TM p₀.2⟩
  have hSopen : IsOpen S := isOpen_univ.prod e.open_baseSet
  have hmetricOn : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((gSmooth p.1).inner p.2)) S := hmetric.contMDiffOn
  have hcorrectionOn : ContMDiffOn (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
        (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2)) S :=
    hcorrection.contMDiffOn
  have hlocal : ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2
        (∑ i, ∑ j,
          ((Matrix.of (fun a b => (gSmooth p.1).inner p.2
            (e.localFrame bas a p.2) (e.localFrame bas b p.2)))⁻¹) i j •
          explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2
            (e.localFrame bas i p.2) (e.localFrame bas j p.2))) S := by
    -- Use the flat model norm explicitly: its algebra and topology are the
    -- canonical tangent structures, rather than independently inferred fibre norms.
    exact @PoincareCurvature.ParametrizedInner.contMDiffOn_timeDependentMetricContraction
      E ‹NormedAddCommGroup E› ‹NormedSpace ℝ E› H ‹TopologicalSpace H› I ∞
      M ‹TopologicalSpace M› ‹ChartedSpace H M›
      E ‹NormedAddCommGroup E› ‹NormedSpace ℝ E› (TangentSpace I : M → Type _)
      instTopologicalSpaceTangentBundle
      (PoincareCurvature.instNormedAddCommGroupTangentSpace (M := M) I)
      (PoincareCurvature.instNormedSpaceTangentSpace (M := M) I)
      (by
        change FiberBundle E TM
        exact metricContractionTangentFiberBundle (I := I) (M := M))
      (by
        change VectorBundle ℝ E TM
        exact metricContractionTangentVectorBundle (I := I) (M := M))
      ‹ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I›
      gSmooth (explicitLeviCivitaCorrection (I := I) (M := M) g background)
      e hAtlas ι (by infer_instance) (by infer_instance)
      bas e.baseSet subset_rfl hmetricOn hcorrectionOn
  have hactual : ContMDiffOn (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2,
        metricContractedDeTurckVectorField (I := I) (M := M) g background p.1 p.2⟩ :
        TangentBundle I M)) S := by
    refine hlocal.congr ?_
    intro p hp
    exact congrArg (TotalSpace.mk' E p.2)
      (metricContractedDeTurckVectorField_eq_sum_inverseGram_correction
        g gSmooth background hinner p.1 e bas hp.2)
  exact hactual.contMDiffAt (hSopen.mem_nhds hp₀)

/-- The recovery gauge is the negative of the conventional field, so the
same geometric data supply its joint smoothness. -/
theorem contMDiff_metricContractedDeTurckGaugeField_of_joint_correction
    (g : MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((gSmooth p.1).inner p.2)))
    (hcorrection : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
        (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2))) :
    ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2,
        metricContractedDeTurckGaugeField (I := I) (M := M) g background p.1 p.2⟩ :
        TangentBundle I M)) := by
  letI : FiberBundle E (TangentSpace I : M → Type _) :=
    metricContractionTangentFiberBundle (I := I) (M := M)
  letI : VectorBundle ℝ E (TangentSpace I : M → Type _) :=
    metricContractionTangentVectorBundle (I := I) (M := M)
  have hvector := contMDiff_metricContractedDeTurckVectorField_of_joint_correction
    g gSmooth background bas hinner hmetric hcorrection
  simpa only [metricContractedDeTurckGaugeField, Pi.neg_apply] using
    (@PoincareCurvature.ParametrizedInner.contMDiff_paramSection_neg
      E ‹NormedAddCommGroup E› ‹NormedSpace ℝ E› H ‹TopologicalSpace H› I ∞
      M ‹TopologicalSpace M› ‹ChartedSpace H M›
      E ‹NormedAddCommGroup E› ‹NormedSpace ℝ E› (TangentSpace I : M → Type _)
      instTopologicalSpaceTangentBundle
      (PoincareCurvature.instNormedAddCommGroupTangentSpace (M := M) I)
      (PoincareCurvature.instNormedSpaceTangentSpace (M := M) I)
      (by
        change FiberBundle E TM
        exact metricContractionTangentFiberBundle (I := I) (M := M))
      (by
        change VectorBundle ℝ E TM
        exact metricContractionTangentVectorBundle (I := I) (M := M))
      ‹ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I›
      (ℝ × E) _ _ (ModelProd ℝ H) _ (𝓘(ℝ).prod I)
      (ℝ × M) _ (prodChartedSpace ℝ ℝ H M)
      (Prod.snd : ℝ × M → M)
      (fun p : ℝ × M =>
        metricContractedDeTurckVectorField (I := I) (M := M) g background p.1 p.2)
      hvector)

/-- Conditional compact gauge-flow construction for this same conventional
field. This migrates the field-level input only: it constructs no Ricci--DeTurck
PDE solution and does not identify the legacy trace field with this field. -/
theorem exists_pos_metricContractedDiffeomorph3GaugeFlowOn_of_joint_correction
    [I.Boundaryless] [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    (g : MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((gSmooth p.1).inner p.2)))
    (hcorrection : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x) p.2
        (explicitLeviCivitaCorrection (I := I) (M := M) g background p.1 p.2))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (metricContractedDeTurckGaugeField (I := I) (M := M) g background)
        (Set.Ioo (-ε) ε) 0) := by
  apply PoincareCurvature.GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_joint_coherent_field
  simpa only [PoincareCurvature.GaugeFlowAssembly.coherentCoordinateField] using
    contMDiff_metricContractedDeTurckGaugeField_of_joint_correction
      g gSmooth background bas hinner hmetric hcorrection

/-- Lower the correction-section premise to local covector sections of the
actual correction functional. The existing Gram/Riesz theorem reconstructs
that tensor, and the preceding theorem contracts its two covariant slots. -/
theorem contMDiff_metricContractedDeTurckVectorField_of_joint_correctionFunctional
    (g : MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E TM)
    (background : ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TM x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ) p.2
        ((gSmooth p.1).inner p.2)))
    (hfunctional : ∀ (x₀ : M) (i j : ι),
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) p.2
            ((CovariantDerivative.correctionFunctional (background p.1) p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2)))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) :
    ContMDiff (𝓘(ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2,
        metricContractedDeTurckVectorField (I := I) (M := M) g background p.1 p.2⟩ :
        TangentBundle I M)) := by
  exact contMDiff_metricContractedDeTurckVectorField_of_joint_correction
    g gSmooth background bas hinner hmetric
    (PoincareCurvature.GaugeFlowAssembly.contMDiff_joint_explicitLeviCivitaCorrection_of_joint_correctionFunctional
        g gSmooth background bas hinner hmetric hfunctional)

end RicciFlow
