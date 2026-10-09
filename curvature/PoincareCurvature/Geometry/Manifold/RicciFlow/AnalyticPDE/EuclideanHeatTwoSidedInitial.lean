import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatHessianSemigroup
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A two-sided initial derivative for genuine bounded C² heat data

This is a supporting linear Euclidean construction. At nonnegative time it
is exactly the existing closed heat path. At negative time it is
`f + t • heat(-t)(Δf)`, where `Δf` is the trace of the actual stored Hessian.
Only positive heat times are used, including in the negative-time branch.

The initial ordinary time derivative is proved by joining the already proved
right generator with the Gaussian approximate identity on the left. No
spatial derivative of `Δf`, C³ initial regularity, or positive initial Hölder
exponent is assumed. Every fixed slice has bounded continuous actual first
and second coordinate derivatives, including at rank zero.

This construction is not a backward heat solution, a nonlinear Ricci--DeTurck
solution, a manifold localization, or a gauge completion. In particular it
does not change any canonical Point-4 contract.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The exponent-zero oscillation bound needed by the existing smoothing
package is derived from boundedness. It imposes no initial Hölder regularity.
For rank zero the two spatial points are equal, so the empty sum is valid. -/
theorem boundedContinuous_zero_coordHolder
    {n : ℕ} (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x y : Fin n → ℝ) :
    |f y - f x| ≤ (2 * ‖f‖) * ∑ ell : Fin n, |(x - y) ell| ^ (0 : ℝ) := by
  classical
  cases n with
  | zero =>
      have hxy : x = y := Subsingleton.elim _ _
      simp [hxy]
  | succ n =>
      have hosc : |f y - f x| ≤ 2 * ‖f‖ := by
        calc
          |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
          _ ≤ ‖f‖ + ‖f‖ := by
            exact add_le_add
              (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y)
              (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
          _ = 2 * ‖f‖ := by ring
      simp only [Real.rpow_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact hosc.trans (le_mul_of_one_le_right (by positivity)
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))

/-- Positive heat smoothing of arbitrary bounded continuous data, with
actual bounded first and second coordinate derivatives. The exponent-zero
bound passed to the inherited constructor is the theorem above. -/
def heatSmoothedBoundedC2Data
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) : EuclideanBoundedC2Data n :=
  heatSmoothedC2Data hs (le_refl (0 : ℝ)) f
    (by positivity : 0 ≤ 2 * ‖f‖) (boundedContinuous_zero_coordHolder f)

@[simp] theorem heatSmoothedBoundedC2Data_value_apply
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (x : Fin n → ℝ) :
    (heatSmoothedBoundedC2Data hs f).value x = heatSemigroupND s f x := rfl

namespace EuclideanBoundedC2Data

/-- The actual initial Laplacian as a bounded continuous function. This is
only the finite diagonal trace of the stored actual Hessian witnesses. -/
def initialLaplacianBcf {n : ℕ} (D : EuclideanBoundedC2Data n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∑ k : Fin n, D.second k k

@[simp] theorem initialLaplacianBcf_apply
    {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    D.initialLaplacianBcf x = ∑ k : Fin n, D.second k k x := by
  classical
  simp [initialLaplacianBcf]

/-- Uniform continuity of actual Hessian entries implies uniform continuity
of the generator. It is not a differentiability hypothesis on the generator. -/
theorem uniformContinuous_initialLaplacianBcf
    {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)) :
    UniformContinuous (D.initialLaplacianBcf : (Fin n → ℝ) → ℝ) := by
  classical
  have hsum : ∀ s : Finset (Fin n),
      UniformContinuous (fun x : Fin n → ℝ => ∑ k ∈ s, D.second k k x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (uniformContinuous_const :
        UniformContinuous (fun _ : Fin n → ℝ => (0 : ℝ)))
    | @insert k s hks ih =>
        simpa only [Finset.sum_insert hks] using (hsecond k k).add ih
  have hfun : (D.initialLaplacianBcf : (Fin n → ℝ) → ℝ) =
      fun x => ∑ k : Fin n, D.second k k x := by
    funext x
    exact D.initialLaplacianBcf_apply x
  rw [hfun]
  exact hsum Finset.univ

/-- The positive and zero branch is exactly the inherited heat path. The
negative branch smooths the bounded actual generator at positive time `-t`.
There is no backward heat solve and no target PDE premise. -/
def twoSidedHeatPathBcf {n : ℕ} (D : EuclideanBoundedC2Data n)
    (t : ℝ) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  if 0 ≤ t then heatFlowPathBcf D.value t
  else D.value + t • heatFlowPathBcf D.initialLaplacianBcf (-t)

theorem twoSidedHeatPathBcf_of_nonneg
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 ≤ t) :
    D.twoSidedHeatPathBcf t = heatFlowPathBcf D.value t := if_pos ht

@[simp] theorem twoSidedHeatPathBcf_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) :
    D.twoSidedHeatPathBcf 0 = D.value := by
  rw [D.twoSidedHeatPathBcf_of_nonneg (le_refl 0)]
  exact dif_neg (lt_irrefl 0)

theorem twoSidedHeatPathBcf_of_neg
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : t < 0) :
    D.twoSidedHeatPathBcf t =
      D.value + t • heatSemigroupNDbcf (neg_pos.mpr ht) D.initialLaplacianBcf := by
  rw [twoSidedHeatPathBcf, if_neg (not_le.mpr ht),
    heatFlowPathBcf_of_pos D.initialLaplacianBcf (neg_pos.mpr ht)]

theorem twoSidedHeatPathBcf_of_pos_apply
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) :
    D.twoSidedHeatPathBcf t x = heatSemigroupND t D.value x := by
  rw [D.twoSidedHeatPathBcf_of_nonneg ht.le, heatFlowPathBcf_of_pos D.value ht]
  exact heatSemigroupNDbcf_apply ht D.value x

/-- A direct sup-norm bound on the negative-time perturbation. This can
support a later near-zero positivity argument; no global positivity or
cutoff has been imposed on this supporting linear path. -/
theorem norm_twoSidedHeatPathBcf_sub_value_of_neg
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : t < 0) :
    ‖D.twoSidedHeatPathBcf t - D.value‖ ≤ |t| * ‖D.initialLaplacianBcf‖ := by
  rw [D.twoSidedHeatPathBcf_of_neg ht, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_heatSemigroupNDbcf_le (neg_pos.mpr ht) D.initialLaplacianBcf) (abs_nonneg t)

/-- Both branches meet the literal datum in the value sup norm. Continuity
of the negative-time generator in the sup norm is not needed for this
particular estimate: its heat evolution is uniformly norm bounded. -/
theorem continuousAt_twoSidedHeatPathBcf_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) :
    ContinuousAt D.twoSidedHeatPathBcf 0 := by
  show Tendsto D.twoSidedHeatPathBcf (𝓝 0) (𝓝 (D.twoSidedHeatPathBcf 0))
  rw [D.twoSidedHeatPathBcf_zero]
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hheat : Tendsto (heatFlowPathBcf D.value) (𝓝 0) (𝓝 D.value) := by
    have hzero : heatFlowPathBcf D.value 0 = D.value := dif_neg (lt_irrefl 0)
    simpa only [hzero] using
      (continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
        D.value D.uniformContinuous_value).tendsto
  have hnear := Metric.tendsto_nhds.mp hheat ε hε
  have hlinear : ∀ᶠ t : ℝ in 𝓝 0, |t| * ‖D.initialLaplacianBcf‖ < ε := by
    have hlim : Tendsto (fun t : ℝ => |t| * ‖D.initialLaplacianBcf‖)
        (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => |t| * ‖D.initialLaplacianBcf‖) :=
        continuous_abs.mul continuous_const
      simpa only [abs_zero, zero_mul] using hcont.tendsto (0 : ℝ)
    exact hlim.eventually (Iio_mem_nhds hε)
  filter_upwards [hnear, hlinear] with t htnear htlinear
  by_cases ht : 0 ≤ t
  · rw [D.twoSidedHeatPathBcf_of_nonneg ht]
    exact htnear
  · rw [dist_eq_norm]
    exact (D.norm_twoSidedHeatPathBcf_sub_value_of_neg (not_le.mp ht)).trans_lt htlinear

/-- Every negative-time fixed slice is genuinely bounded C²: its stored
derivatives are the actual derivatives of the original datum plus the
corresponding derivatives of the positively smoothed bounded generator. -/
def negativeHeatC2Data
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : t < 0) :
    EuclideanBoundedC2Data n where
  value := D.value + t • (heatSmoothedBoundedC2Data (neg_pos.mpr ht)
    D.initialLaplacianBcf).value
  first := fun k => D.first k + t • (heatSmoothedBoundedC2Data (neg_pos.mpr ht)
    D.initialLaplacianBcf).first k
  second := fun j k => D.second j k + t •
    (heatSmoothedBoundedC2Data (neg_pos.mpr ht) D.initialLaplacianBcf).second j k
  hasDeriv_value := by
    intro k x
    simp only [BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply]
    apply HasDerivAt.fun_add
    · exact D.hasDeriv_value k x
    · exact ((heatSmoothedBoundedC2Data (neg_pos.mpr ht)
        D.initialLaplacianBcf).hasDeriv_value k x).fun_const_smul t
  hasDeriv_first := by
    intro j k x
    simp only [BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply]
    apply HasDerivAt.fun_add
    · exact D.hasDeriv_first j k x
    · exact ((heatSmoothedBoundedC2Data (neg_pos.mpr ht)
        D.initialLaplacianBcf).hasDeriv_first j k x).fun_const_smul t

theorem negativeHeatC2Data_value_eq
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : t < 0) :
    (D.negativeHeatC2Data ht).value = D.twoSidedHeatPathBcf t := by
  rw [D.twoSidedHeatPathBcf_of_neg ht]
  rfl

/-- A bounded C² witness for every fixed slice, including the literal datum
at zero. No spatial rank is excluded. -/
def twoSidedHeatC2Data {n : ℕ} (D : EuclideanBoundedC2Data n) (t : ℝ) :
    EuclideanBoundedC2Data n :=
  if ht : 0 < t then heatSmoothedBoundedC2Data ht D.value
  else if htneg : t < 0 then D.negativeHeatC2Data htneg else D

theorem twoSidedHeatC2Data_value_eq
    {n : ℕ} (D : EuclideanBoundedC2Data n) (t : ℝ) :
    (D.twoSidedHeatC2Data t).value = D.twoSidedHeatPathBcf t := by
  by_cases ht : 0 < t
  · rw [twoSidedHeatC2Data, dif_pos ht,
      D.twoSidedHeatPathBcf_of_nonneg ht.le, heatFlowPathBcf_of_pos D.value ht]
    rfl
  · by_cases htneg : t < 0
    · rw [twoSidedHeatC2Data, dif_neg ht, dif_pos htneg]
      exact D.negativeHeatC2Data_value_eq htneg
    · have htzero : t = 0 := le_antisymm (not_lt.mp ht) (not_lt.mp htneg)
      subst t
      simp [twoSidedHeatC2Data]

/-- The ordinary initial derivative joins the already proved right heat
generator to the left Gaussian approximate identity for the actual bounded
continuous generator. This pointwise statement even holds without global
uniform continuity of the Hessian; only a compact singleton trace is used. -/
theorem hasDerivAt_twoSidedHeatPathBcf_apply_zero
    {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    HasDerivAt (fun t => D.twoSidedHeatPathBcf t x)
      (∑ k : Fin n, D.second k k x) 0 := by
  have hright : HasDerivWithinAt (fun t => D.twoSidedHeatPathBcf t x)
      (∑ k : Fin n, D.second k k x) (Ici 0) 0 :=
    (D.hasDerivWithinAt_heatFlowPathBcf_apply_zero x).congr
      (fun t ht => by rw [D.twoSidedHeatPathBcf_of_nonneg ht])
      (by rw [D.twoSidedHeatPathBcf_of_nonneg (le_refl 0)])
  have htrace : Tendsto
      (fun s => heatSemigroupND s D.initialLaplacianBcf x)
      (𝓝[>] 0) (𝓝 (∑ k : Fin n, D.second k k x)) := by
    simpa only [initialLaplacianBcf_apply] using
      (tendstoUniformlyOn_heatSemigroupND_zero D.initialLaplacianBcf
        (K := {x}) isCompact_singleton).tendsto_at (mem_singleton x)
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [neg_zero] using
        ((show Continuous (fun t : ℝ => -t) from continuous_neg).tendsto 0).mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact neg_pos.mpr (mem_Iio.mp ht)
  have hslope : Tendsto (slope (fun t => D.twoSidedHeatPathBcf t x) 0)
      (𝓝[<] 0) (𝓝 (∑ k : Fin n, D.second k k x)) := by
    apply (htrace.comp hneg).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htneg : t < 0 := mem_Iio.mp ht
    rw [slope_def_field, D.twoSidedHeatPathBcf_of_neg htneg,
      D.twoSidedHeatPathBcf_zero, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, heatSemigroupNDbcf_apply]
    simp only [Function.comp_apply, smul_eq_mul, sub_zero, add_sub_cancel_left]
    rw [mul_div_cancel_left₀ _ (ne_of_lt htneg)]
  have hleft : HasDerivWithinAt (fun t => D.twoSidedHeatPathBcf t x)
      (∑ k : Fin n, D.second k k x) (Iic 0) 0 :=
    ((hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Iio 0)).mpr
      hslope).Iic_of_Iio
  have hboth := hleft.union hright
  have hcover : Iic (0 : ℝ) ∪ Ici 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total t 0
  rw [hcover] at hboth
  exact hasDerivWithinAt_univ.mp hboth

/-- At strictly positive time the same actual heat equation is retained. -/
theorem hasDerivAt_twoSidedHeatPathBcf_apply_of_pos
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s => D.twoSidedHeatPathBcf s x)
      (heatSemigroupLaplacianND t D.value x) t := by
  apply (hasDerivAt_heatSemigroupND_time_eq_laplacian ht D.value x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact D.twoSidedHeatPathBcf_of_pos_apply hs x

end EuclideanBoundedC2Data
end AnalyticPDE
end RicciFlow
