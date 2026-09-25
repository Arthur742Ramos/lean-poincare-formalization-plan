import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointCorrectionTensorRegularity

set_option linter.unusedSectionVars false
set_option linter.all false

noncomputable section

open scoped Manifold Topology ContDiff
open Bundle

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance sliceCorrectionTangentFiberBundle : FiberBundle E TM := TangentSpace.fiberBundle
local instance sliceCorrectionTangentVectorBundle : VectorBundle ℝ E TM := TangentSpace.vectorBundle

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Slicewise regularity of the actual correction functional.**

For a fixed time, the `C²` metric family supplies the Riemannian-bundle
regularity required by the static Levi--Civita API.  A `C¹` background slice
then makes the covector-valued `correctionFunctional` `C¹` after application to
each pair of local-frame sections.  This is the spatial part of the joint
correction-functional premise consumed by
`contMDiff_joint_explicitLeviCivitaCorrection_of_joint_correctionFunctional`.
The theorem deliberately says nothing about differentiability in the time
parameter: `MetricFamily` and `ConnectionFamily` are only slicewise families.
-/
theorem contMDiffOn_slice_correctionFunctional_localFrame
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x₀ : M)
    {ι : Type*} (bas : Module.Basis ι ℝ E) (i j : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x : M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TM y →L[ℝ] ℝ) x
          ((CovariantDerivative.correctionFunctional (background t) x)
            ((trivializationAt E TM x₀).localFrame bas i x)
            ((trivializationAt E TM x₀).localFrame bas j x)))
      (trivializationAt E TM x₀).baseSet := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  letI : MemTrivializationAtlas e := by infer_instance
  have hcov :
      ContMDiffCovariantDerivativeOn E 1
        (background t).toFun e.baseSet := by
    letI : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1 :=
      hbackground
    exact
      CovariantDerivative.contMDiffCovariantDerivativeOn_of_contMDiffCovariantDerivative
        (I := I) (E := E) (u := e.baseSet) e.open_baseSet
  have hframe (k : ι) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y : M => TotalSpace.mk' E y (e.localFrame bas k y)) e.baseSet :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
      (I := I) (e := e) (n := (2 : WithTop ℕ∞)) (b := bas) k).mono
      (Set.Subset.rfl)
  simpa [e] using
    (CovariantDerivative.contMDiffOn_correctionFunctional_section
      (I := I) (E := E) e bas e.open_baseSet (Set.Subset.rfl) hcov
      (σ := fun y : M => e.localFrame bas i y)
      (τ := fun y : M => e.localFrame bas j y)
      (hframe i) (hframe j))

end PoincareCurvature.GaugeFlowAssembly
