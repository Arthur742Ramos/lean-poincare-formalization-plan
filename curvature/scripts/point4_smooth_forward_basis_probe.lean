module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardBasis

open Bundle
open scoped Manifold ContDiff

set_option pp.universes true
set_option pp.explicit true
set_option format.width 160

#check @RicciFlow.SmoothForward.chartGramComponent_eq_sum_basis
#check @RicciFlow.SmoothForward.jointlySmoothOn_iff_basis
#print axioms RicciFlow.SmoothForward.chartGramComponent_eq_sum_basis
#print axioms RicciFlow.SmoothForward.jointlySmoothOn_iff_basis

universe uE uH uM uι

section ExactType
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type uι} [Fintype ι]

example : ∀ (b : Module.Basis ι ℝ E)
    (g : RicciFlow.SmoothForward.MetricFamily (I := I) (M := M)) (a terminal : ℝ),
    RicciFlow.SmoothForward.JointlySmoothOn g a terminal ↔
      ∀ (x₀ : M) (i j : ι),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M => RicciFlow.SmoothForward.chartGramComponent (g p.1) x₀ (b i) (b j) p.2)
          (Set.Ico a terminal ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
  RicciFlow.SmoothForward.jointlySmoothOn_iff_basis

/-- A basis with no indices imposes no nonempty-model requirement. -/
example (b : Module.Basis (Fin 0) ℝ E)
    (g : RicciFlow.SmoothForward.MetricFamily (I := I) (M := M)) (a terminal : ℝ) :
    RicciFlow.SmoothForward.JointlySmoothOn g a terminal :=
  (RicciFlow.SmoothForward.jointlySmoothOn_iff_basis b g a terminal).2
    (fun _ i _ => Fin.elim0 i)

example [IsEmpty M] (b : Module.Basis ι ℝ E)
    (g : RicciFlow.SmoothForward.MetricFamily (I := I) (M := M)) (a terminal : ℝ) :
    RicciFlow.SmoothForward.JointlySmoothOn g a terminal :=
  (RicciFlow.SmoothForward.jointlySmoothOn_iff_basis b g a terminal).2
    (fun x₀ _ _ => isEmptyElim x₀)

end ExactType
