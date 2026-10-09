import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Unconditional scalar identities for a proposed C² Ricci-flow obstruction.
These lemmas do not construct a torus or a Ricci-flow counterexample.
The variable L is the positive logarithmic radius log(1/r).
-/

namespace RicciFlow.C2Resonance

noncomputable def profile (ε L : ℝ) : ℝ :=
  -(3 * ε / 2) * Real.log L + ε / (4 * L)

noncomputable def profileSlope (ε L : ℝ) : ℝ :=
  -(3 * ε / 2) / L - ε / (4 * L ^ 2)

noncomputable def profileSecond (ε L : ℝ) : ℝ :=
  (3 * ε / 2) / L ^ 2 + ε / (2 * L ^ 3)

/-- First derivative of the explicit logarithmic resonant profile. -/
theorem hasDerivAt_profile (ε L : ℝ) (hL : L ≠ 0) :
    HasDerivAt (profile ε) (profileSlope ε L) L := by
  have hlog := (Real.hasDerivAt_log hL).const_mul (-(3 * ε / 2))
  have hinv := (hasDerivAt_id L).const_mul 4
  have hquot := (hasDerivAt_const L ε).div hinv (by simpa using hL)
  have h := hlog.add hquot
  change HasDerivAt (profile ε)
    (-(3 * ε / 2) * L⁻¹ + (0 * (4 * L) - ε * (4 * 1)) / (4 * L) ^ 2) L at h
  have heq : -(3 * ε / 2) * L⁻¹ + (0 * (4 * L) - ε * (4 * 1)) / (4 * L) ^ 2 =
      profileSlope ε L := by
    dsimp [profileSlope]
    field_simp [hL]
    ring
  rw [heq] at h
  exact h

/-- Second derivative, stated as the derivative of the proved slope. -/
theorem hasDerivAt_profileSlope (ε L : ℝ) (hL : L ≠ 0) :
    HasDerivAt (profileSlope ε) (profileSecond ε L) L := by
  have hfirst := (hasDerivAt_const L (-(3 * ε / 2))).div (hasDerivAt_id L) hL
  have hden := ((hasDerivAt_id L).pow 2).const_mul 4
  have hsecond := (hasDerivAt_const L ε).div hden (by simp [hL])
  have h := hfirst.sub hsecond
  change HasDerivAt (profileSlope ε)
    ((0 * L - -(3 * ε / 2) * 1) / L ^ 2 -
      (0 * (4 * L ^ 2) - ε * (4 * (2 * L ^ 1 * 1))) / (4 * L ^ 2) ^ 2) L at h
  have heq : (0 * L - -(3 * ε / 2) * 1) / L ^ 2 -
      (0 * (4 * L ^ 2) - ε * (4 * (2 * L ^ 1 * 1))) / (4 * L ^ 2) ^ 2 =
      profileSecond ε L := by
    dsimp [profileSecond]
    field_simp [hL]
    ring
  rw [heq] at h
  exact h

/-- In logarithmic radius, the order-two resonant Euler operator is b'' - 4 b'. -/
theorem resonant_profile_identity (ε L : ℝ) (hL : L ≠ 0) :
    profileSecond ε L - 4 * profileSlope ε L =
      ε * (6 / L + 5 / (2 * L ^ 2) + 1 / (2 * L ^ 3)) := by
  dsimp [profileSlope, profileSecond]
  field_simp
  ring

/-- The resonant profile diverges for every fixed positive perturbation. -/
theorem tendsto_profile_atBot (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (profile ε) Filter.atTop Filter.atBot := by
  rw [Filter.tendsto_atBot]
  intro B
  have hlog := (Filter.tendsto_atTop.1 Real.tendsto_log_atTop)
    ((ε / 4 - B) / (3 * ε / 2))
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℝ)] with L hlog hL
  have hpositive : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hcorrection : ε / (4 * L) ≤ ε / 4 := by
    apply div_le_div_of_nonneg_left (le_of_lt hε) (by norm_num : (0 : ℝ) < 4)
    nlinarith
  have hmain : ε / 4 - B ≤ (3 * ε / 2) * Real.log L := by
    nlinarith [(div_le_iff₀ (by positivity : 0 < 3 * ε / 2)).1 hlog]
  dsimp [profile]
  nlinarith

#print axioms hasDerivAt_profile
#print axioms hasDerivAt_profileSlope
#print axioms resonant_profile_identity
#print axioms tendsto_profile_atBot

end RicciFlow.C2Resonance
