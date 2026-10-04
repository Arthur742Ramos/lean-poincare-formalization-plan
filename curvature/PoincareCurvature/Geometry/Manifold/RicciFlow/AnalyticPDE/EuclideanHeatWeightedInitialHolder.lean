import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckHolderSmoothing

/-!
# Vanishing weighted Hessian Hölder constants at the initial heat face

For genuine bounded C² data whose initial Hessian entries are uniformly
continuous, the actual compatible positive-time Gaussian heat data admit an
explicit Hessian Hölder certificate K(t) with t^(α/2) K(t) → 0, for 0 < α ≤ 1.
The scale is √t and the error is the actual sup-norm heat-approximation error;
no positive-exponent Hölder modulus of the initial Hessian is assumed.

The proof splits f into f - S_{√t} f and S_{√t} f. Actual Gaussian linearity
and the semigroup law identify the latter evolution with S_{t+√t} f.
This is flat initial-face analysis, not a nonlinear parabolic solver,
compact-manifold localization, or an ordinary endpoint derivative theorem.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The linearized scalar form of the already proved Gaussian Hölder gain. -/
theorem abs_heatSemigroupNDbcf_spatial_holder_le
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {t α : ℝ} (ht : 0 < t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : Fin n → ℝ) :
    |heatSemigroupNDbcf ht f x - heatSemigroupNDbcf ht f y| ≤
      (2 * (π * t) ^ (-(α / 2)) * ‖f‖) *
        (∑ i : Fin n, |(x - y) i|) ^ α := by
  have h := heatSemigroupND_spatial_holder_seminorm_bound ht
    f.continuous.aestronglyMeasurable (fun z => f.norm_coe_le_norm z) hα0 hα1 x y
  have hconst := rpow_holder_smoothing_const_le (norm_nonneg f) ht hα0 hα1
  simpa only [heatSemigroupNDbcf_apply, Pi.sub_apply] using
    h.trans (mul_le_mul_of_nonneg_right hconst
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _))

/-- The actual semigroup decomposition into a small initial error and a
positive-time smoothed piece. -/
theorem heatSemigroupNDbcf_split_initial_error
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    heatSemigroupNDbcf ht f =
      heatSemigroupNDbcf ht (f - heatSemigroupNDbcf hδ f) +
        heatSemigroupNDbcf (add_pos ht hδ) f := by
  have hlin : heatSemigroupNDbcf ht (f - heatSemigroupNDbcf hδ f) =
      heatSemigroupNDbcf ht f -
        heatSemigroupNDbcf ht (heatSemigroupNDbcf hδ f) :=
    (heatSemigroupNDclm ht).map_sub _ _
  rw [hlin, heatSemigroupNDbcf_comp t δ ht hδ]
  abel

/-- Explicit scalar certificate using the genuine heat error at scale √t.
The total zero/negative-time extension is only used to state a limit. -/
def initialHeatHolderConstant {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (α t : ℝ) : ℝ :=
  2 * (π * t) ^ (-(α / 2)) * ‖f - heatFlowPathBcf f (Real.sqrt t)‖ +
    2 * (π * Real.sqrt t) ^ (-(α / 2)) * ‖f‖

theorem initialHeatHolderConstant_nonneg {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (α t : ℝ) :
    0 ≤ initialHeatHolderConstant f α t := by
  unfold initialHeatHolderConstant
  positivity

/-- Actual scalar Gaussian Hölder certificate, with no initial Hölder premise. -/
theorem abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {t α : ℝ} (ht : 0 < t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : Fin n → ℝ) :
    |heatSemigroupNDbcf ht f x - heatSemigroupNDbcf ht f y| ≤
      initialHeatHolderConstant f α t *
        (∑ i : Fin n, |(x - y) i|) ^ α := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let g := f - heatSemigroupNDbcf hs f
  have herr := abs_heatSemigroupNDbcf_spatial_holder_le g ht hα0 hα1 x y
  have hsmooth := abs_heatSemigroupNDbcf_spatial_holder_le f
    (add_pos ht hs) hα0 hα1 x y
  have hscale : (π * (t + Real.sqrt t)) ^ (-(α / 2)) ≤
      (π * Real.sqrt t) ^ (-(α / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le) (by linarith)
  have hspatial : 0 ≤ (∑ i : Fin n, |(x - y) i|) ^ α :=
    Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _
  have hsmooth' := hsmooth.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by norm_num))
      (norm_nonneg f)) hspatial)
  have hsplit := heatSemigroupNDbcf_split_initial_error f ht hs
  have hxy : heatSemigroupNDbcf ht f x - heatSemigroupNDbcf ht f y =
      (heatSemigroupNDbcf ht g x - heatSemigroupNDbcf ht g y) +
        (heatSemigroupNDbcf (add_pos ht hs) f x -
          heatSemigroupNDbcf (add_pos ht hs) f y) := by
    rw [hsplit]
    simp only [BoundedContinuousFunction.add_apply]
    dsimp [g]
    ring
  rw [hxy]
  calc
    _ ≤ |heatSemigroupNDbcf ht g x - heatSemigroupNDbcf ht g y| +
        |heatSemigroupNDbcf (add_pos ht hs) f x -
          heatSemigroupNDbcf (add_pos ht hs) f y| := abs_add _ _
    _ ≤ _ := add_le_add herr hsmooth'
    _ = _ := by
      rw [initialHeatHolderConstant, heatFlowPathBcf_of_pos f hs]
      dsimp [g]
      ring

/-- Exact weight accounting: the small-error coefficient is constant after
weighting, and the smoothed-piece coefficient gains t^(α/4). -/
theorem initialHeatHolderConstant_weight_identity {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {α t : ℝ} (ht : 0 < t) :
    t ^ (α / 2) * initialHeatHolderConstant f α t =
      2 * π ^ (-(α / 2)) * ‖f - heatFlowPathBcf f (Real.sqrt t)‖ +
        2 * π ^ (-(α / 2)) * t ^ (α / 4) * ‖f‖ := by
  have hcancel : t ^ (α / 2) * t ^ (-(α / 2)) = 1 := by
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hsqrt : (Real.sqrt t) ^ (-(α / 2)) = t ^ (-(α / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hgain : t ^ (α / 2) * t ^ (-(α / 4)) = t ^ (α / 4) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [initialHeatHolderConstant, Real.mul_rpow Real.pi_pos.le ht.le,
    Real.mul_rpow Real.pi_pos.le (Real.sqrt_nonneg t), hsqrt]
  calc
    _ = 2 * π ^ (-(α / 2)) *
        (t ^ (α / 2) * t ^ (-(α / 2))) *
          ‖f - heatFlowPathBcf f (Real.sqrt t)‖ +
        2 * π ^ (-(α / 2)) *
          (t ^ (α / 2) * t ^ (-(α / 4))) * ‖f‖ := by ring
    _ = _ := by rw [hcancel, hgain, mul_one]

/-- Uniform continuity, rather than an initial positive-exponent Hölder
modulus, makes the explicit weighted scalar certificate vanish. -/
theorem tendsto_weighted_initialHeatHolderConstant_zero
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ))
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => t ^ (α / 2) * initialHeatHolderConstant f α t)
      (𝓝[>] 0) (𝓝 0) := by
  have hpath : ContinuousAt (fun t : ℝ => heatFlowPathBcf f (Real.sqrt t)) 0 := by
    simpa only [Real.sqrt_zero] using
      (continuousAt_heatFlowPathBcf_zero_of_uniformContinuous f hf).comp
        Real.continuous_sqrt.continuousAt
  have herr : Tendsto (fun t : ℝ => ‖f - heatFlowPathBcf f (Real.sqrt t)‖)
      (𝓝 0) (𝓝 0) := by
    simpa [heatFlowPathBcf] using (continuousAt_const.sub hpath).norm.tendsto
  have hpow : Tendsto (fun t : ℝ => t ^ (α / 4)) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (show α / 4 ≠ 0 by positivity)] using
      (Real.continuous_rpow_const (show 0 ≤ α / 4 by positivity)).tendsto (0 : ℝ)
  have hlim : Tendsto (fun t : ℝ =>
      2 * π ^ (-(α / 2)) * ‖f - heatFlowPathBcf f (Real.sqrt t)‖ +
        2 * π ^ (-(α / 2)) * t ^ (α / 4) * ‖f‖) (𝓝[>] 0) (𝓝 0) := by
    have h := (herr.const_mul (2 * π ^ (-(α / 2)))).add
      ((hpow.const_mul (2 * π ^ (-(α / 2)))).mul_const ‖f‖)
    simpa only [mul_zero, zero_mul, zero_add] using
      h.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (initialHeatHolderConstant_weight_identity f ht).symm

/-- Sum of the explicit actual-error certificates for every initial Hessian
entry. The definition does not choose a modulus or assume a weighted bound. -/
def EuclideanBoundedC2Data.initialHessianHolderConstant {n : ℕ}
    (D : EuclideanBoundedC2Data n) (α t : ℝ) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n, initialHeatHolderConstant (D.second j k) α t

/-- Actual positive-time compatible C²,α Gaussian data with a vanishing
weighted Hessian certificate whenever the initial Hessian is uniformly continuous. -/
def heatEvolvedWeightedC2AlphaData {n : ℕ} (D : EuclideanBoundedC2Data n)
    {t α : ℝ} (ht : 0 < t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    EuclideanBoundedC2AlphaData n α where
  base := heatEvolvedBoundedC2Data D ht
  hessianHolderConstant := D.initialHessianHolderConstant α t
  hessianHolderConstant_nonneg := Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => initialHeatHolderConstant_nonneg (D.second j k) α t
  hessianHolder := by
    intro j k x y
    have hmain := abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant
      (D.second j k) ht hα0 hα1 x y
    have hterm : initialHeatHolderConstant (D.second j k) α t ≤
        D.initialHessianHolderConstant α t := by
      refine le_trans (Finset.single_le_sum
        (fun k' _ => initialHeatHolderConstant_nonneg (D.second j k') α t)
        (Finset.mem_univ k)) ?_
      exact Finset.single_le_sum
        (fun j' _ => Finset.sum_nonneg fun k' _ =>
          initialHeatHolderConstant_nonneg (D.second j' k') α t) (Finset.mem_univ j)
    exact hmain.trans (mul_le_mul_of_nonneg_right hterm
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _))

@[simp] theorem heatEvolvedWeightedC2AlphaData_base_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (heatEvolvedWeightedC2AlphaData D ht hα0 hα1).base =
      heatEvolvedBoundedC2Data D ht := rfl

@[simp] theorem heatEvolvedWeightedC2AlphaData_holderConstant_eq {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t α : ℝ} (ht : 0 < t)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (heatEvolvedWeightedC2AlphaData D ht hα0 hα1).hessianHolderConstant =
      D.initialHessianHolderConstant α t := rfl

/-- The explicit certificate of the actual compatible heat datum vanishes
after multiplication by t^(α/2). No initial Hölder hypothesis is present. -/
theorem EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => t ^ (α / 2) * D.initialHessianHolderConstant α t)
      (𝓝[>] 0) (𝓝 0) := by
  have hentry := fun j k =>
    tendsto_weighted_initialHeatHolderConstant_zero (D.second j k) (hsecond j k) hα
  have hsum : Tendsto (fun t : ℝ =>
      ∑ j : Fin n, ∑ k : Fin n,
        t ^ (α / 2) * initialHeatHolderConstant (D.second j k) α t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ =>
      tendsto_finsetSum Finset.univ (fun k _ => hentry j k))
  simpa only [EuclideanBoundedC2Data.initialHessianHolderConstant, Finset.mul_sum]
    using hsum

/-- Headline initial-face limit for the Hölder constant of the constructed
actual compatible C²,α Gaussian datum itself. Only Hessian uniform continuity
is added to genuine bounded C² initial data. -/
theorem EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Tendsto (fun t : ℝ => t ^ (α / 2) *
      (if ht : 0 < t then
        (heatEvolvedWeightedC2AlphaData D ht hα.le hα1).hessianHolderConstant
      else 0)) (𝓝[>] 0) (𝓝 0) := by
  apply (D.tendsto_weighted_initialHessianHolderConstant_zero hsecond hα).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [dif_pos ht, heatEvolvedWeightedC2AlphaData_holderConstant_eq]

end AnalyticPDE
end RicciFlow
