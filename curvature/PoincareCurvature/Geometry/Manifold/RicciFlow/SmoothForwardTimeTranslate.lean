module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardContract
public import PoincareCurvature.Geometry.Manifold.RicciFlow.IntrinsicRicciReindex
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
Time translation preserves the smooth forward solution class, its initial
metric, and its half-open time interval. The one-sided derivative domain moves
with the initial time.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow.SmoothForward

/-- Exact translation of the right-sided derivative domain. -/
theorem time_add_preimage_Ici (a c : ℝ) :
    (fun t : ℝ ↦ t + c) ⁻¹' Set.Ici a = Set.Ici (a - c) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Ici, sub_le_iff_le_add]

/-- Exact translation of the half-open solution interval. -/
theorem time_add_preimage_Ico (a b c : ℝ) :
    (fun t : ℝ ↦ t + c) ⁻¹' Set.Ico a b = Set.Ico (a - c) (b - c) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Ico, sub_le_iff_le_add, lt_sub_iff_add_lt]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Translation transports the equation and its one-sided derivative domain. -/
theorem ForwardEquation.timeTranslate {g : MetricFamily (I := I) (M := M)}
    {a b : ℝ} (hg : ForwardEquation g a b) (c : ℝ) :
    ForwardEquation (fun t ↦ g (t + c)) (a - c) (b - c) := by
  intro t ht x u v
  have ht' : t + c ∈ Set.Ico a b := by
    change t ∈ (fun s : ℝ ↦ s + c) ⁻¹' Set.Ico a b
    rw [time_add_preimage_Ico]
    exact ht
  have hmaps : Set.MapsTo (fun s : ℝ ↦ s + c) (Set.Ici (a - c)) (Set.Ici a) := by
    intro s hs
    change s ∈ (fun q : ℝ ↦ q + c) ⁻¹' Set.Ici a
    rw [time_add_preimage_Ici]
    exact hs
  have hshift : HasDerivWithinAt (fun s : ℝ ↦ s + c) 1 (Set.Ici (a - c)) t := by
    simpa only [id_eq] using ((hasDerivAt_id t).add_const c).hasDerivWithinAt
  have hcomp := (hg (t + c) ht' x u v).comp t hshift hmaps
  have hRicci :
      RicciFlow.intrinsicRicciTensor (c2Family (fun s ↦ g (s + c))) t x u v =
        RicciFlow.intrinsicRicciTensor (c2Family g) (t + c) x u v :=
    RicciFlow.intrinsicRicciTensor_time_add (c2Family g) c t x u v
  rw [hRicci]
  simpa only [Function.comp_def, mul_one] using hcomp

omit [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M] in
/-- Joint chart regularity transports along the smooth map `(t,x) ↦ (t+c,x)`. -/
theorem JointlySmoothOn.timeTranslate {g : MetricFamily (I := I) (M := M)}
    {a b : ℝ} (hg : JointlySmoothOn g a b) (c : ℝ) :
    JointlySmoothOn (fun t ↦ g (t + c)) (a - c) (b - c) := by
  intro x₀ u v
  have htime : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ t + c) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M ↦ (p.1 + c, p.2)) :=
    (htime.comp contMDiff_fst).prodMk contMDiff_snd
  apply (hg x₀ u v).comp hshift.contMDiffOn
  rintro p ⟨ht, hx⟩
  refine ⟨?_, hx⟩
  change p.1 ∈ (fun t : ℝ ↦ t + c) ⁻¹' Set.Ico a b
  rw [time_add_preimage_Ico]
  exact ht

/-- Translate a strong solution while preserving its initial metric. -/
def StrongSolution.timeTranslate {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) (c : ℝ) : StrongSolution (a - c) g₀ where
  terminalTime := sol.terminalTime - c
  terminal_gt := sub_lt_sub_right sol.terminal_gt c
  metric := fun t ↦ sol.metric (t + c)
  initial_eq := by simpa only [sub_add_cancel] using sol.initial_eq
  joint_smooth := sol.joint_smooth.timeTranslate c
  equation := sol.equation.timeTranslate c

end RicciFlow.SmoothForward
