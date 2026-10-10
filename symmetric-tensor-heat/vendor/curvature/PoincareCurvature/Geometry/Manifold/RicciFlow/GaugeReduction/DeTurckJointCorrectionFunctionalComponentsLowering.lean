import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointCorrectionFunctionalComponents

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

local instance jointCorrectionLoweringTangentFiberBundle : FiberBundle E TM :=
  TangentSpace.fiberBundle
local instance jointCorrectionLoweringTangentVectorBundle : VectorBundle ℝ E TM :=
  TangentSpace.vectorBundle

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- **Joint correction functional from metric-defect and torsion components.**

This is the scalar geometric lowering after the coordinate reconstruction in
`DeTurckJointCorrectionFunctionalComponents`.  It expands the actual
`correctionFunctional` on each local-frame triple using its metric-defect and
torsion formula, then closes the finite scalar expression under `ContMDiffOn`.
The hypotheses are deliberately stated at the joint scalar level; no
time--space regularity is inferred from the slicewise family abbreviations.
-/
theorem contMDiffOn_joint_correctionFunctional_of_joint_metricDefect_torsion_components
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hmetric : ∀ (x₀ : M) (a b c : ι),
      ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          (background p.1).metricDefect p.2
            ((trivializationAt E TM x₀).localFrame bas a p.2)
            ((trivializationAt E TM x₀).localFrame bas b p.2)
            ((trivializationAt E TM x₀).localFrame bas c p.2))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet))
    (htorsion : ∀ (x₀ : M) (a b c : ι),
      ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          Inner.inner ℝ
            ((background p.1).torsion p.2
              ((trivializationAt E TM x₀).localFrame bas a p.2)
              ((trivializationAt E TM x₀).localFrame bas b p.2))
            ((trivializationAt E TM x₀).localFrame bas c p.2))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet)) :
    ∀ (x₀ : M) (i j : ι),
      ContMDiffOn (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M =>
          letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          TotalSpace.mk' (E →L[ℝ] ℝ)
            (E := fun x : M => TM x →L[ℝ] ℝ) p.2
            ((CovariantDerivative.correctionFunctional (background p.1) p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2)))
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet) := by
  apply contMDiffOn_joint_correctionFunctional_of_joint_localFrame_evaluations
    (g := g) (background := background) bas
  intro x₀ i j k
  have hmetric_ikj := hmetric x₀ i k j
  have hmetric_jki := hmetric x₀ j k i
  have hmetric_jik := hmetric x₀ j i k
  have htorsion_jik := htorsion x₀ j i k
  have htorsion_ikj := htorsion x₀ i k j
  have htorsion_kji := htorsion x₀ k j i
  have hsum' :=
    ((((hmetric_ikj.add hmetric_jki).sub hmetric_jik).sub htorsion_jik).add
      htorsion_ikj).sub htorsion_kji
  have hsum : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        (letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
        (background p.1).metricDefect p.2
            ((trivializationAt E TM x₀).localFrame bas i p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2)
            ((trivializationAt E TM x₀).localFrame bas j p.2) +
          (background p.1).metricDefect p.2
            ((trivializationAt E TM x₀).localFrame bas j p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2)
            ((trivializationAt E TM x₀).localFrame bas i p.2) -
          (background p.1).metricDefect p.2
            ((trivializationAt E TM x₀).localFrame bas j p.2)
            ((trivializationAt E TM x₀).localFrame bas i p.2)
            ((trivializationAt E TM x₀).localFrame bas k p.2) -
          Inner.inner ℝ
            ((background p.1).torsion p.2
              ((trivializationAt E TM x₀).localFrame bas j p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2))
            ((trivializationAt E TM x₀).localFrame bas k p.2) +
          Inner.inner ℝ
            ((background p.1).torsion p.2
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas k p.2))
            ((trivializationAt E TM x₀).localFrame bas j p.2) -
          Inner.inner ℝ
            ((background p.1).torsion p.2
              ((trivializationAt E TM x₀).localFrame bas k p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2))
            ((trivializationAt E TM x₀).localFrame bas i p.2)))
      (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using hsum'
  have hscaled : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        (2 : ℝ)⁻¹ *
          (letI : Bundle.RiemannianBundle TM := ⟨(g p.1).toRiemannianMetric⟩
          (background p.1).metricDefect p.2
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas k p.2)
              ((trivializationAt E TM x₀).localFrame bas j p.2) +
            (background p.1).metricDefect p.2
              ((trivializationAt E TM x₀).localFrame bas j p.2)
              ((trivializationAt E TM x₀).localFrame bas k p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2) -
            (background p.1).metricDefect p.2
              ((trivializationAt E TM x₀).localFrame bas j p.2)
              ((trivializationAt E TM x₀).localFrame bas i p.2)
              ((trivializationAt E TM x₀).localFrame bas k p.2) -
            Inner.inner ℝ
              ((background p.1).torsion p.2
                ((trivializationAt E TM x₀).localFrame bas j p.2)
                ((trivializationAt E TM x₀).localFrame bas i p.2))
              ((trivializationAt E TM x₀).localFrame bas k p.2) +
            Inner.inner ℝ
              ((background p.1).torsion p.2
                ((trivializationAt E TM x₀).localFrame bas i p.2)
                ((trivializationAt E TM x₀).localFrame bas k p.2))
              ((trivializationAt E TM x₀).localFrame bas j p.2) -
            Inner.inner ℝ
              ((background p.1).torsion p.2
                ((trivializationAt E TM x₀).localFrame bas k p.2)
                ((trivializationAt E TM x₀).localFrame bas j p.2))
              ((trivializationAt E TM x₀).localFrame bas i p.2)))
      (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet) := by
    have hconst : ContMDiffOn (𝓘(ℝ).prod I) 𝓘(ℝ) ∞
        (fun _ : ℝ × M => (2 : ℝ)⁻¹)
        (Set.univ ×ˢ (trivializationAt E TM x₀).baseSet) := contMDiffOn_const
    convert hconst.smul hsum using 1 <;> ext p <;>
      simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  simpa [CovariantDerivative.correctionFunctional_apply, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hscaled

end PoincareCurvature.GaugeFlowAssembly
