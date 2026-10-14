import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatCoercivity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quantitative inverse-coefficient control for the actual initial heat path

Source candidate, not yet compiled. The coercivity reserve is constructed from
the literal initial C2 metric. The error below is the finite sum of actual
Gaussian heat errors in the bounded-function norm. Its limit follows from the
already proved initial heat trace and the bounded first derivatives of the data.

This supplies initial principal-coefficient control. It does not construct a
nonlinear interval solution or assert an interval Ricci equation.
-/

noncomputable section

open Bundle Set Filter Matrix
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

private theorem quadraticMatrix_eq_dotProduct {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    ofMatrix (fun i j => A i j) v v = dotProduct v (A.mulVec v) := by
  rw [ofMatrix_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Uniform coercivity forces the actual coordinate matrix to be invertible.
No symmetry hypothesis or positive-rank hypothesis is required. -/
theorem isUnit_matrix_of_coercive {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) : IsUnit A := by
  classical
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  by_contra hne
  have hkernel : A.mulVec (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hnorm : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hzero : c * ‖u - v‖ ^ 2 ≤ 0 := by
    have hq := hcoer (u - v)
    rw [quadraticMatrix_eq_dotProduct A (u - v), hkernel] at hq
    simpa only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hq
  exact (not_lt_of_ge hzero) (mul_pos hc (sq_pos_of_pos hnorm))

/-- Every inverse entry is bounded by the same coercivity reserve. The finite
coordinate norm here is the sup norm used by the existing bilinear adapter. -/
theorem abs_matrix_inv_entry_le_of_coercive {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v) (i j : Fin d) :
    |A⁻¹ i j| ≤ 1 / c := by
  classical
  have hunit : IsUnit A := isUnit_matrix_of_coercive A hc hcoer
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  let w : Fin d → ℝ := (A⁻¹).mulVec (Pi.single j 1)
  have hAw : A.mulVec w = Pi.single j 1 := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hquadratic : c * ‖w‖ ^ 2 ≤ w j := by
    simpa only [quadraticMatrix_eq_dotProduct, hAw, dotProduct_single_one] using hcoer w
  have hcomponent : |w j| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  have hmul : c * ‖w‖ ^ 2 ≤ ‖w‖ :=
    hquadratic.trans ((le_abs_self _).trans hcomponent)
  have hnorm : ‖w‖ ≤ 1 / c := by
    by_cases hw : ‖w‖ = 0
    · rw [hw]
      positivity
    · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
      apply (le_div_iff₀ hc).mpr
      have hcancel : (c * ‖w‖) * ‖w‖ ≤ 1 * ‖w‖ := by
        nlinarith only [hmul]
      have hcr : c * ‖w‖ ≤ 1 := le_of_mul_le_mul_right hcancel hwpos
      simpa only [mul_comm] using hcr
  have hwi : w i = A⁻¹ i j := by
    dsimp only [w]
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← hwi]
  calc
    |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
    _ ≤ 1 / c := hnorm

/-- The resolvent identity turns entrywise metric error into entrywise inverse
error, with a concrete dimension-squared and inverse-reserve-squared factor. -/
theorem abs_matrix_inv_sub_inv_entry_le_of_coercive {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) {c ε : ℝ} (hc : 0 < c)
    (hA : ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => A i j) v v)
    (hB : ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => B i j) v v)
    (hε : 0 ≤ ε) (hAB : ∀ p q, |A p q - B p q| ≤ ε) (i j : Fin d) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (d : ℝ) ^ 2 * (1 / c) ^ 2 * ε := by
  classical
  have huA : IsUnit A := isUnit_matrix_of_coercive A hc hA
  have huB : IsUnit B := isUnit_matrix_of_coercive B hc hB
  have hres : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ :=
    Matrix.inv_sub_inv ⟨fun _ => huB, fun _ => huA⟩
  have hentry := congrArg (fun C : Matrix (Fin d) (Fin d) ℝ => C i j) hres
  change A⁻¹ i j - B⁻¹ i j = _ at hentry
  rw [hentry]
  simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
  calc
    |∑ q : Fin d, ∑ p : Fin d, (A⁻¹ i p * (B p q - A p q)) * B⁻¹ q j| ≤
        ∑ q : Fin d, ∑ p : Fin d, |(A⁻¹ i p * (B p q - A p q)) * B⁻¹ q j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun q _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ q : Fin d, ∑ p : Fin d, ((1 / c) * ε) * (1 / c) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_mul]
      have hBA : |B p q - A p q| ≤ ε := by
        rw [abs_sub_comm]
        exact hAB p q
      exact mul_le_mul
        (mul_le_mul (abs_matrix_inv_entry_le_of_coercive A hc hA i p)
          hBA (abs_nonneg _) (by positivity))
        (abs_matrix_inv_entry_le_of_coercive B hc hB q j)
        (abs_nonneg _) (mul_nonneg (by positivity) hε)
    _ = (d : ℝ) ^ 2 * (1 / c) ^ 2 * ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A concrete global heat-value error. The nonpositive extension only defines
the zero-time value; for positive time every entry is the actual Gaussian heat. -/
def matrixInitialHeatValueError {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) (t : ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ‖heatFlowPathBcf (D i j).value t - (D i j).value‖

private theorem matrixInitialHeatValueError_nonneg {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) (t : ℝ) :
    0 ≤ matrixInitialHeatValueError D t :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- The error tends to zero for the actual bounded C2 data; no separate uniform
continuity hypothesis is needed for the metric values. -/
theorem tendsto_matrixInitialHeatValueError_zero {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) :
    Tendsto (matrixInitialHeatValueError D) (𝓝 0) (𝓝 0) := by
  classical
  have hentry (i j : Fin d) :
      Tendsto (fun t : ℝ => ‖heatFlowPathBcf (D i j).value t - (D i j).value‖)
        (𝓝 0) (𝓝 0) := by
    have h := continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
      (D i j).value (D i j).uniformContinuous_value
    have hzero : heatFlowPathBcf (D i j).value 0 = (D i j).value :=
      dif_neg (lt_irrefl 0)
    have hconst : ContinuousAt (fun _ : ℝ => (D i j).value) 0 := continuousAt_const
    have hnorm : ContinuousAt
        (fun t : ℝ => ‖heatFlowPathBcf (D i j).value t - (D i j).value‖) 0 :=
      (h.sub hconst).norm
    simpa only [hzero, sub_self, norm_zero] using hnorm.tendsto
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => hentry i j))
  change Tendsto
    (fun t : ℝ => ∑ i : Fin d, ∑ j : Fin d,
      ‖heatFlowPathBcf (D i j).value t - (D i j).value‖) (𝓝 0) (𝓝 0)
  simpa only [Finset.sum_const_zero] using hsum

/-- The inverse of the actual Gaussian heat matrix is uniformly close to the
inverse of its initial matrix, at every spatial point. -/
theorem abs_matrixInitialHeat_inv_sub_initial_inv_le {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ) (i j : Fin d) :
    |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
      (Matrix.of (fun a b => (D a b).value z))⁻¹ i j| ≤
      (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of
    (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z)
  let B : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun a b => (D a b).value z)
  change |A⁻¹ i j - B⁻¹ i j| ≤
    (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t
  apply abs_matrix_inv_sub_inv_entry_le_of_coercive A B hc
  · intro v
    change c * ‖v‖ ^ 2 ≤ ofMatrix
      (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z) v v
    exact matrixHeatSemigroupND_preserves_coercivity
      (fun a b => (D a b).value) c hcoer ht z v
  · intro v
    change c * ‖v‖ ^ 2 ≤ ofMatrix (fun a b => (D a b).value z) v v
    exact hcoer z v
  · exact matrixInitialHeatValueError_nonneg D t
  · intro a b
    have hterm : ‖heatFlowPathBcf (D a b).value t - (D a b).value‖ ≤
        matrixInitialHeatValueError D t := by
      have hrow : ‖heatFlowPathBcf (D a b).value t - (D a b).value‖ ≤
          ∑ q : Fin d, ‖heatFlowPathBcf (D a q).value t - (D a q).value‖ :=
        Finset.single_le_sum
          (f := fun q : Fin d => ‖heatFlowPathBcf (D a q).value t - (D a q).value‖)
          (fun q _ => norm_nonneg _) (Finset.mem_univ b)
      have htotal : (∑ q : Fin d, ‖heatFlowPathBcf (D a q).value t - (D a q).value‖) ≤
          ∑ p : Fin d, ∑ q : Fin d, ‖heatFlowPathBcf (D p q).value t - (D p q).value‖ :=
        Finset.single_le_sum
          (f := fun p : Fin d => ∑ q : Fin d,
            ‖heatFlowPathBcf (D p q).value t - (D p q).value‖)
          (fun p _ => Finset.sum_nonneg (fun q _ => norm_nonneg _)) (Finset.mem_univ a)
      change ‖heatFlowPathBcf (D a b).value t - (D a b).value‖ ≤
        ∑ p : Fin d, ∑ q : Fin d, ‖heatFlowPathBcf (D p q).value t - (D p q).value‖
      exact hrow.trans htotal
    have hb := (heatFlowPathBcf (D a b).value t - (D a b).value).norm_coe_le_norm z
    calc
      |A a b - B a b| ≤ ‖heatFlowPathBcf (D a b).value t - (D a b).value‖ := by
        change |heatSemigroupND t (fun y => (D a b).value y) z - (D a b).value z| ≤
          ‖heatFlowPathBcf (D a b).value t - (D a b).value‖
        simpa only [heatFlowPathBcf_of_pos (D a b).value ht,
          BoundedContinuousFunction.sub_apply, heatSemigroupNDbcf_apply,
          Real.norm_eq_abs] using hb
      _ ≤ matrixInitialHeatValueError D t := hterm

section LiteralInitialMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A literal C2 initial metric produces a positive reserve and actual Gaussian
heat data whose inverse principal coefficients have a global error tending to
zero. The reserve, data, value continuity and inverse control are constructed. -/
theorem exists_initialMetricLocalizedHeatData_with_inverse_control
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (p : M) :
    ∃ c > 0, ∃ D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        EuclideanBoundedC2Data (Module.finrank ℝ E),
      (∀ᶠ z in 𝓝 (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)),
        ∀ i j, (D i j).value z = initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j) ∧
      (∀ z i j, (D i j).value z = (D j i).value z) ∧
      (∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v) ∧
      (∀ t : ℝ, 0 < t → ∀ z v, c * ‖v‖ ^ 2 ≤
        ofMatrix (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y a b => (D a b).value y) z) v v) ∧
      (∀ i j a b, UniformContinuous ((D i j).second a b :
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ)) ∧
      (∀ t : ℝ, 0 < t → ∀ z i j,
        |(Matrix.of (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
          t (fun y a b => (D a b).value y) z))⁻¹ i j -
          (Matrix.of (fun a b => (D a b).value z))⁻¹ i j| ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t) ∧
      Tendsto (fun t : ℝ =>
        (Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t)
        (𝓝 0) (𝓝 0) := by
  classical
  obtain ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond⟩ :=
    exists_initialMetricLocalizedHeatData_with_coercive_heat g₀ p
  refine ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, ?_, ?_⟩
  · intro t ht z i j
    exact abs_matrixInitialHeat_inv_sub_initial_inv_le D hc hcoer ht z i j
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_matrixInitialHeatValueError_zero D) :
        Tendsto (fun t : ℝ =>
          (Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t)
          (𝓝 0) (𝓝 ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / c) ^ 2 * 0)))

end LiteralInitialMetric

end RicciFlow.AnalyticPDE
