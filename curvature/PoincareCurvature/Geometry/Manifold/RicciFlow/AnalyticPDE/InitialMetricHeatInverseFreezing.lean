import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InitialMetricHeatInverseControl

/-!
# Initial-face freezing of actual Gaussian inverse coefficients

Source candidate, not yet compiled. Its inverse-control dependency is also a
Source dependency until the parent's separate native qualification succeeds.
The spatial modulus is computed from the actual bounded C2 data. The time
modulus is the actual bounded-function heat error from inverse control.

The geometric theorem constructs its positive time and neighborhood from the
literal C2 initial metric. It supplies coefficient closeness for this initial
Gaussian heat path, without constructing a nonlinear interval solution.
-/

noncomputable section

open Bundle Set Filter
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

/-- The concrete spatial value modulus relative to a fixed point. -/
def matrixInitialSpatialValueError {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n)
    (z z₀ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ‖(D i j).value z - (D i j).value z₀‖

private theorem matrixInitialSpatialValueError_nonneg {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) (z z₀ : Fin n → ℝ) :
    0 ≤ matrixInitialSpatialValueError D z z₀ :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem abs_initialMatrixEntry_sub_basepoint_le {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n)
    (z z₀ : Fin n → ℝ) (i j : Fin d) :
    |(D i j).value z - (D i j).value z₀| ≤ matrixInitialSpatialValueError D z z₀ := by
  classical
  rw [← Real.norm_eq_abs]
  have hrow : ‖(D i j).value z - (D i j).value z₀‖ ≤
      ∑ q : Fin d, ‖(D i q).value z - (D i q).value z₀‖ :=
    Finset.single_le_sum
      (f := fun q : Fin d => ‖(D i q).value z - (D i q).value z₀‖)
      (fun q _ => norm_nonneg _) (Finset.mem_univ j)
  have htotal : (∑ q : Fin d, ‖(D i q).value z - (D i q).value z₀‖) ≤
      ∑ p : Fin d, ∑ q : Fin d, ‖(D p q).value z - (D p q).value z₀‖ :=
    Finset.single_le_sum
      (f := fun p : Fin d => ∑ q : Fin d, ‖(D p q).value z - (D p q).value z₀‖)
      (fun p _ => Finset.sum_nonneg (fun q _ => norm_nonneg _)) (Finset.mem_univ i)
  change ‖(D i j).value z - (D i j).value z₀‖ ≤
    ∑ p : Fin d, ∑ q : Fin d, ‖(D p q).value z - (D p q).value z₀‖
  exact hrow.trans htotal

private theorem tendsto_matrixInitialSpatialValueError_zero {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) (z₀ : Fin n → ℝ) :
    Tendsto (fun z => matrixInitialSpatialValueError D z z₀) (𝓝 z₀) (𝓝 0) := by
  classical
  have hentry (i j : Fin d) :
      Tendsto (fun z : Fin n → ℝ => ‖(D i j).value z - (D i j).value z₀‖)
        (𝓝 z₀) (𝓝 0) := by
    have hvalue : ContinuousAt ((D i j).value : (Fin n → ℝ) → ℝ) z₀ :=
      (D i j).value.continuous.continuousAt
    have hconst : ContinuousAt (fun _ : Fin n → ℝ => (D i j).value z₀) z₀ :=
      continuousAt_const
    have h : ContinuousAt
        (fun z : Fin n → ℝ => ‖(D i j).value z - (D i j).value z₀‖) z₀ :=
      (hvalue.sub hconst).norm
    simpa only [sub_self, norm_zero] using h.tendsto
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => hentry i j))
  change Tendsto
    (fun z : Fin n → ℝ => ∑ i : Fin d, ∑ j : Fin d,
      ‖(D i j).value z - (D i j).value z₀‖) (𝓝 z₀) (𝓝 0)
  simpa only [Finset.sum_const_zero] using hsum

/-- The actual heat inverse is compared with one fixed initial matrix, with
separate concrete temporal and spatial errors and the same coercivity reserve. -/
theorem abs_matrixInitialHeat_inv_sub_basepoint_inv_le {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    {t : ℝ} (ht : 0 < t) (z z₀ : Fin n → ℝ) (i j : Fin d) :
    |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
      (Matrix.of (fun a b => (D a b).value z₀))⁻¹ i j| ≤
      (d : ℝ) ^ 2 * (1 / c) ^ 2 *
        (matrixInitialHeatValueError D t + matrixInitialSpatialValueError D z z₀) := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun a b => (D a b).value z)
  let B : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun a b => (D a b).value z₀)
  have hspace : |A⁻¹ i j - B⁻¹ i j| ≤
      (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialSpatialValueError D z z₀ := by
    apply abs_matrix_inv_sub_inv_entry_le_of_coercive A B hc
    · intro v
      change c * ‖v‖ ^ 2 ≤ ofMatrix (fun a b => (D a b).value z) v v
      exact hcoer z v
    · intro v
      change c * ‖v‖ ^ 2 ≤ ofMatrix (fun a b => (D a b).value z₀) v v
      exact hcoer z₀ v
    · exact matrixInitialSpatialValueError_nonneg D z z₀
    · intro a b
      change |(D a b).value z - (D a b).value z₀| ≤ _
      exact abs_initialMatrixEntry_sub_basepoint_le D z z₀ a b
  let H : Matrix (Fin d) (Fin d) ℝ := Matrix.of
    (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z)
  have htime : |H⁻¹ i j - A⁻¹ i j| ≤
      (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t :=
    abs_matrixInitialHeat_inv_sub_initial_inv_le D hc hcoer ht z i j
  change |H⁻¹ i j - B⁻¹ i j| ≤ _
  calc
    |H⁻¹ i j - B⁻¹ i j| = |(H⁻¹ i j - A⁻¹ i j) + (A⁻¹ i j - B⁻¹ i j)| := by
      congr 1
      ring
    _ ≤ |H⁻¹ i j - A⁻¹ i j| + |A⁻¹ i j - B⁻¹ i j| := abs_add_le _ _
    _ ≤ (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialHeatValueError D t +
        (d : ℝ) ^ 2 * (1 / c) ^ 2 * matrixInitialSpatialValueError D z z₀ :=
      add_le_add htime hspace
    _ = (d : ℝ) ^ 2 * (1 / c) ^ 2 *
        (matrixInitialHeatValueError D t + matrixInitialSpatialValueError D z z₀) := by ring

/-- For any prescribed coefficient tolerance, construct a positive time window
and a neighborhood of the fixed initial point. The continuity and vanishing
heat error used here are derived from D, rather than supplied as hypotheses. -/
theorem matrixInitialHeat_inverse_coefficients_freeze {n d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data n) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    (z₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ U : Set (Fin n → ℝ), U ∈ 𝓝 z₀ ∧
      ∀ t : ℝ, 0 < t → t < T → ∀ z ∈ U, ∀ i j : Fin d,
        |(Matrix.of (matrixHeatSemigroupND n d t (fun y a b => (D a b).value y) z))⁻¹ i j -
          (Matrix.of (fun a b => (D a b).value z₀))⁻¹ i j| < ε := by
  classical
  let K : ℝ := (d : ℝ) ^ 2 * (1 / c) ^ 2
  have htime : Tendsto (fun t : ℝ => K * matrixInitialHeatValueError D t)
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) (𝓝 0) (𝓝 K)).mul
        (tendsto_matrixInitialHeatValueError_zero D)
  have hspace : Tendsto (fun z : Fin n → ℝ => K * matrixInitialSpatialValueError D z z₀)
      (𝓝 z₀) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Fin n → ℝ => K) (𝓝 z₀) (𝓝 K)).mul
        (tendsto_matrixInitialSpatialValueError_zero D z₀)
  have htimeSmall : ∀ᶠ t : ℝ in 𝓝 0, K * matrixInitialHeatValueError D t < ε / 2 :=
    htime.eventually (Iio_mem_nhds (half_pos hε))
  obtain ⟨T, hT, htimeBall⟩ := Metric.eventually_nhds_iff.mp htimeSmall
  let U : Set (Fin n → ℝ) := {z | K * matrixInitialSpatialValueError D z z₀ < ε / 2}
  have hU : U ∈ 𝓝 z₀ := hspace.eventually (Iio_mem_nhds (half_pos hε))
  refine ⟨T, hT, U, hU, ?_⟩
  intro t ht htT z hz i j
  have htError : K * matrixInitialHeatValueError D t < ε / 2 :=
    htimeBall (by simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos ht] using htT)
  have hzError : K * matrixInitialSpatialValueError D z z₀ < ε / 2 := hz
  have hbound := abs_matrixInitialHeat_inv_sub_basepoint_inv_le D hc hcoer ht z z₀ i j
  have hsmall : K * (matrixInitialHeatValueError D t +
      matrixInitialSpatialValueError D z z₀) < ε := by
    rw [mul_add]
    linarith
  exact hbound.trans_lt hsmall

section LiteralInitialMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Literal C2 initial data construct actual Gaussian inverse coefficients
uniformly close to the fixed intrinsic initial-coordinate matrix. The returned
spatial neighborhood also retains exact agreement with the original metric. -/
theorem exists_initialMetricLocalizedHeatData_with_frozen_inverse_coefficients
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
      (∀ ε : ℝ, 0 < ε → ∃ T > 0,
        ∃ U : Set (Fin (Module.finrank ℝ E) → ℝ),
          U ∈ 𝓝 (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) ∧
          (∀ z ∈ U, ∀ i j, (D i j).value z =
            initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j) ∧
          ∀ t : ℝ, 0 < t → t < T → ∀ z ∈ U, ∀ i j,
            |(Matrix.of (matrixHeatSemigroupND (Module.finrank ℝ E) (Module.finrank ℝ E)
              t (fun y a b => (D a b).value y) z))⁻¹ i j -
              (Matrix.of (fun a b => initialMetricCoordinates g₀ p (Module.finBasis ℝ E)
                (initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)) a b))⁻¹ i j| < ε) := by
  classical
  obtain ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, hinv, hinvlim⟩ :=
    exists_initialMetricLocalizedHeatData_with_inverse_control g₀ p
  refine ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, ?_⟩
  intro ε hε
  let z₀ := initialMetricCoordinatePoint (I := I) p (Module.finBasis ℝ E)
  obtain ⟨T, hT, U, hU, hfrozen⟩ :=
    matrixInitialHeat_inverse_coefficients_freeze D hc hcoer z₀ hε
  let V : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    U ∩ {z | ∀ i j, (D i j).value z = initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z i j}
  have hV : V ∈ 𝓝 z₀ := inter_mem hU hnear
  have hbase : Matrix.of (fun a b => (D a b).value z₀) =
      Matrix.of (fun a b => initialMetricCoordinates g₀ p (Module.finBasis ℝ E) z₀ a b) := by
    ext a b
    exact hnear.self_of_nhds a b
  refine ⟨T, hT, V, hV, ?_, ?_⟩
  · intro z hz i j
    exact hz.2 i j
  · intro t ht htT z hz i j
    simpa only [hbase] using hfrozen t ht htT z hz.1 i j

end LiteralInitialMetric

end RicciFlow.AnalyticPDE
