module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardTimeTranslate

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff
open RicciFlow.SmoothForward

set_option pp.universes true
set_option pp.fullNames true
set_option format.width 240

#check @time_add_preimage_Ici
#check @time_add_preimage_Ico
#check @ForwardEquation.timeTranslate
#check @JointlySmoothOn.timeTranslate
#check @StrongSolution.timeTranslate
#print axioms time_add_preimage_Ici
#print axioms time_add_preimage_Ico
#print axioms ForwardEquation.timeTranslate
#print axioms JointlySmoothOn.timeTranslate
#print axioms StrongSolution.timeTranslate

namespace TimeTranslateVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

theorem zero_shift_equation {g : MetricFamily (I := I) (M := M)} {a b : ℝ}
    (hg : ForwardEquation g a b) : ForwardEquation g a b := by
  simpa only [sub_zero, add_zero] using hg.timeTranslate 0

theorem zero_shift_joint {g : MetricFamily (I := I) (M := M)} {a b : ℝ}
    (hg : JointlySmoothOn g a b) : JointlySmoothOn g a b := by
  simpa only [sub_zero, add_zero] using hg.timeTranslate 0

def zero_shift_solution {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) : StrongSolution a g₀ := by
  simpa only [sub_zero] using sol.timeTranslate 0

theorem zero_shift_terminal {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) : (sol.timeTranslate 0).terminalTime = sol.terminalTime := by
  exact sub_zero sol.terminalTime

theorem zero_shift_metric {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) (t : ℝ) :
    (sol.timeTranslate 0).metric t = sol.metric t := by
  change sol.metric (t + 0) = sol.metric t
  rw [add_zero]

theorem translated_initial_metric {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) (c : ℝ) :
    (sol.timeTranslate c).metric (a - c) = g₀ :=
  (sol.timeTranslate c).initial_eq

end TimeTranslateVerification

#check @TimeTranslateVerification.zero_shift_equation
#check @TimeTranslateVerification.zero_shift_joint
#check @TimeTranslateVerification.zero_shift_solution
#check @TimeTranslateVerification.zero_shift_terminal
#check @TimeTranslateVerification.zero_shift_metric
#check @TimeTranslateVerification.translated_initial_metric
#print axioms TimeTranslateVerification.zero_shift_equation
#print axioms TimeTranslateVerification.zero_shift_joint
#print axioms TimeTranslateVerification.zero_shift_solution
#print axioms TimeTranslateVerification.zero_shift_terminal
#print axioms TimeTranslateVerification.zero_shift_metric
#print axioms TimeTranslateVerification.translated_initial_metric

run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    Lean.logInfo s!"IMPORT_MODULE {name}"
