module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Endpoint closure for Banach evolution uniqueness

This leaf module closes the restricted-terminal Banach uniqueness bridge at the
common endpoint.  The core analytic layer already supplies equality on every
shorter closed interval and therefore on the open common interval; the lemmas
below add the endpoint using within-interval continuity of the ODE curves.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Endpoint closure for functions that agree on the left-open interval and
are continuous within the corresponding closed interval at the endpoint. -/
theorem eq_of_continuousWithinAt_Icc_of_eqOn_Ico {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ℝ → Y} {a b : ℝ} (hab : a < b)
    (hf : ContinuousWithinAt f (Icc a b) b)
    (hg : ContinuousWithinAt g (Icc a b) b)
    (hEq : EqOn f g (Ico a b)) : f b = g b := by
  have hleft_le : 𝓝[<] b ≤ 𝓝[Icc a b] b := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact nhdsWithin_mono b (by
      intro t ht
      exact ⟨ht.1, le_of_lt ht.2⟩)
  have hfg : f =ᶠ[𝓝[<] b] g := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hab]
    exact eventuallyEq_nhdsWithin_of_eqOn hEq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left hleft_le) (hg.mono_left hleft_le) hfg

namespace BanachEvolutionLocalSolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {t₀ : ℝ} {u₀ : X}

/-- Closed-interval continuation bridge: if equality is available on every
prescribed shorter common terminal, continuity of the Banach ODE curves closes
the equality at the common terminal. -/
theorem eqOn_Icc_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolution F t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  let Tcommon := min sol₁.terminalTime sol₂.terminalTime
  intro t ht
  by_cases htlt : t < Tcommon
  · exact eqOn_Ico_of_eqOn_Icc_of_le_terminal sol₁ sol₂ hEq ⟨ht.1, htlt⟩
  · have ht_eq : t = Tcommon :=
      le_antisymm (by simpa [Tcommon] using ht.2) (le_of_not_gt htlt)
    subst t
    have hT₀ : t₀ < Tcommon := by
      exact lt_min sol₁.initial_lt_terminal sol₂.initial_lt_terminal
    have hcont₁ : ContinuousWithinAt sol₁.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₁.continuousOn_Icc_of_le_terminal (min_le_left _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    have hcont₂ : ContinuousWithinAt sol₂.curve (Icc t₀ Tcommon) Tcommon := by
      exact (sol₂.continuousOn_Icc_of_le_terminal (min_le_right _ _)).continuousWithinAt
        ⟨le_of_lt hT₀, le_rfl⟩
    exact eq_of_continuousWithinAt_Icc_of_eqOn_Ico hT₀ hcont₁ hcont₂
      (eqOn_Ico_of_eqOn_Icc_of_le_terminal sol₁ sol₂ hEq)

end BanachEvolutionLocalSolution

namespace BanachEvolutionLocalSolutionIn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : ℝ → X → X} {stateSet : Set X} {t₀ : ℝ} {u₀ : X}

/-- Closed-interval continuation bridge for state-preserving solutions. -/
theorem eqOn_Icc_of_eqOn_Icc_of_le_terminal
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hEq : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      EqOn sol₁.curve sol₂.curve (Icc t₀ T)) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact BanachEvolutionLocalSolution.eqOn_Icc_of_eqOn_Icc_of_le_terminal
    sol₁.toBanachEvolutionLocalSolution sol₂.toBanachEvolutionLocalSolution hEq

/-- State-set uniqueness on the closed common interval when the Lipschitz bound
is available on every prescribed shorter common terminal interval. -/
theorem eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal_common
    {K : ℝ≥0}
    (sol₁ sol₂ : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀)
    (hF : ∀ {T : ℝ}, t₀ < T → T ≤ sol₁.terminalTime → T ≤ sol₂.terminalTime →
      ∀ t ∈ Icc t₀ T, LipschitzOnWith K (F t) stateSet) :
    EqOn sol₁.curve sol₂.curve (Icc t₀ (min sol₁.terminalTime sol₂.terminalTime)) := by
  exact eqOn_Icc_of_eqOn_Icc_of_le_terminal sol₁ sol₂ (fun hT₀ hT₁ hT₂ ↦
    eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal (F := F) (stateSet := stateSet)
      (t₀ := t₀) (u₀ := u₀) (K := K) sol₁ sol₂ hT₀ hT₁ hT₂
      (hF hT₀ hT₁ hT₂))

end BanachEvolutionLocalSolutionIn

/-- Picard-Lindelof plus an open state set and Lipschitz bounds on every
prescribed shorter terminal gives local existence and closed-common-interval
uniqueness.  This is the endpoint-closed form of
`IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc`. -/
theorem IsPicardLindelof.exists_unique_banachEvolutionLocalSolutionIn_of_mem_isOpen_restricted_Icc_closed
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {F : ℝ → X → X} {stateSet : Set X} {t₀ T : ℝ} (hT : t₀ < T) {u₀ : X}
    {a L K Kstate : ℝ≥0}
    (hF : IsPicardLindelof F (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ u₀ a 0 L K)
    (hstate_open : IsOpen stateSet) (hu₀ : u₀ ∈ stateSet)
    (hLip : ∀ {S : ℝ}, t₀ < S → S ≤ T →
      ∀ t ∈ Icc t₀ S, LipschitzOnWith Kstate (F t) stateSet) :
    ∃ sol : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
      sol.terminalTime ≤ T ∧
      ∀ sol' : BanachEvolutionLocalSolutionIn F stateSet t₀ u₀,
        EqOn sol.curve sol'.curve (Icc t₀ (min sol.terminalTime sol'.terminalTime)) := by
  rcases hF.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨u, hu_init, hu_eq⟩
  let baseSol : BanachEvolutionLocalSolution F t₀ u₀ :=
    { terminalTime := T
      initial_lt_terminal := hT
      curve := u
      initial_eq := hu_init
      equation := by
        intro t ht
        exact hu_eq t ht }
  rcases baseSol.exists_restrict_in_isOpen hstate_open hu₀ with ⟨sol, hsolT, _hcurve⟩
  refine ⟨sol, hsolT, fun sol' ↦ ?_⟩
  exact BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal_common
    (F := F) (stateSet := stateSet) (t₀ := t₀) (u₀ := u₀) (K := Kstate) sol sol'
    (fun hS₀ hS₁ _hS₂ t ht ↦ hLip hS₀ (le_trans hS₁ hsolT) t ht)

end AnalyticPDE
end RicciFlow
