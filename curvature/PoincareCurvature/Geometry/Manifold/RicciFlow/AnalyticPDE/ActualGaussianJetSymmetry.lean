import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ActualGaussianJetPrincipalError

/-!
# Actual Gaussian jet symmetries and the algebraic principal split

Source candidate, uncompiled. ActualGaussianJetPrincipalError is a Source
dependency until its separate native qualification succeeds. Initial metric
symmetry propagates through the actual coordinate derivative witnesses; mixed
spatial Hessian symmetry follows from the actual Gaussian kernel formula.

The final split uses freely chosen background arrays as algebraic parameters.
It does not identify them with a manifold connection or construct an intrinsic
Ricci-DeTurck equation, a Cauchy generator, or a nonlinear interval solution.
-/

noncomputable section

open Bundle Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff Topology Matrix
open PoincareCurvature.FiniteCoordinateBilinear

namespace RicciFlow.AnalyticPDE

private theorem heatHessianKernelEntryND_swap_indices {n : ℕ} (t : ℝ)
    (z : Fin n → ℝ) (j k : Fin n) :
    heatHessianKernelEntryND t z j k = heatHessianKernelEntryND t z k j := by
  classical
  by_cases hjk : j = k
  · subst k
    rfl
  · unfold heatHessianKernelEntryND
    rw [if_neg hjk, if_neg (Ne.symm hjk)]
    ring

/-- The actual Gaussian Hessian convolution is symmetric in its two spatial
indices. This is a pointwise kernel identity, with no regularity oracle. -/
theorem heatHessianEntryConvolutionND_swap_indices {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (j k : Fin n) (z : Fin n → ℝ) :
    heatHessianEntryConvolutionND t f j k z = heatHessianEntryConvolutionND t f k j z := by
  unfold heatHessianEntryConvolutionND
  apply integral_congr_ae
  filter_upwards with y
  rw [heatHessianKernelEntryND_swap_indices t (z - y) j k]

/-- Initial metric-index symmetry survives in the value of the actual Gaussian
jet. The first and second initial slots need not be supplied as symmetric. -/
theorem actualGaussianMetricJet_val_metric_symm {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d)
    (hsymm : ∀ z i j, (D i j).value z = (D j i).value z)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i j : Fin d) :
    (actualGaussianMetricJet D ht z).val i j = (actualGaussianMetricJet D ht z).val j i := by
  change heatSemigroupND t (fun y => (D i j).value y) z =
    heatSemigroupND t (fun y => (D j i).value y) z
  have hfun : (fun y => (D i j).value y) = (fun y => (D j i).value y) := by
    funext y
    exact hsymm y i j
  rw [hfun]

/-- Actual first derivative witnesses propagate metric-index symmetry into the
first slot, by uniqueness of derivatives of equal coordinate functions. -/
theorem actualGaussianMetricJet_deriv1_metric_symm {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d)
    (hsymm : ∀ z i j, (D i j).value z = (D j i).value z)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k i j : Fin d) :
    (actualGaussianMetricJet D ht z).deriv1 k i j =
      (actualGaussianMetricJet D ht z).deriv1 k j i := by
  have hleft := actualGaussianMetricJet_hasDeriv_value D ht z k i j
  have hright := actualGaussianMetricJet_hasDeriv_value D ht z k j i
  have hfun :
      (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).val i j) =
      (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).val j i) := by
    funext r
    exact actualGaussianMetricJet_val_metric_symm D hsymm ht (Function.update z k r) i j
  rw [hfun] at hleft
  exact hleft.unique hright

/-- Actual second derivative witnesses propagate metric-index symmetry into
the second slot. This is exactly the hS34 premise of the existing split. -/
theorem actualGaussianMetricJet_deriv2_metric_symm {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d)
    (hsymm : ∀ z i j, (D i j).value z = (D j i).value z)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k l i j : Fin d) :
    (actualGaussianMetricJet D ht z).deriv2 k l i j =
      (actualGaussianMetricJet D ht z).deriv2 k l j i := by
  have hleft := actualGaussianMetricJet_hasDeriv_first D ht z k l i j
  have hright := actualGaussianMetricJet_hasDeriv_first D ht z k l j i
  have hfun :
      (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).deriv1 l i j) =
      (fun r => (actualGaussianMetricJet D ht (Function.update z k r)).deriv1 l j i) := by
    funext r
    exact actualGaussianMetricJet_deriv1_metric_symm D hsymm ht
      (Function.update z k r) l i j
  rw [hfun] at hleft
  exact hleft.unique hright

/-- The actual heat second slot is symmetric in the two spatial indices by
the Gaussian Hessian convolution formula. This is the existing hS12 premise. -/
theorem actualGaussianMetricJet_deriv2_spatial_symm {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (k l i j : Fin d) :
    (actualGaussianMetricJet D ht z).deriv2 k l i j =
      (actualGaussianMetricJet D ht z).deriv2 l k i j := by
  change heatSemigroupND t ((D i j).second k l) z =
    heatSemigroupND t ((D i j).second l k) z
  rw [← (D i j).heatHessianEntryConvolutionND_eq ht k l z,
    ← (D i j).heatHessianEntryConvolutionND_eq ht l k z]
  exact heatHessianEntryConvolutionND_swap_indices t (D i j).value k l z

/-- Retained coercivity also supplies the nonzero determinant premise of the
actual Gaussian jet principal split. It imposes no positive-rank hypothesis. -/
theorem actualGaussianMetricJet_det_ne_zero {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) :
    (actualGaussianMetricJet D ht z).val.det ≠ 0 := by
  have hheat : ∀ v : Fin d → ℝ,
      c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (actualGaussianMetricJet D ht z).val i j) v v := by
    intro v
    change c * ‖v‖ ^ 2 ≤ ofMatrix
      (matrixHeatSemigroupND d d t (fun y i j => (D i j).value y) z) v v
    exact matrixHeatSemigroupND_preserves_coercivity
      (fun i j => (D i j).value) c hcoer ht z v
  have hunit := isUnit_matrix_of_coercive (actualGaussianMetricJet D ht z).val hc hheat
  exact ((Matrix.isUnit_iff_isUnit_det (actualGaussianMetricJet D ht z).val).mp hunit).ne_zero

/-- The exact existing algebraic principal/remainder split applies to the
actual Gaussian jet. All determinant and symmetry premises are derived.
The background arrays remain freely chosen algebraic parameters. -/
theorem actualGaussianMetricJet_principal_split {d : ℕ}
    (D : Fin d → Fin d → EuclideanBoundedC2Data d) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i j => (D i j).value z) v v)
    (hsymm : ∀ z i j, (D i j).value z = (D j i).value z)
    (A : Fin d → Fin d → ℝ)
    (Γbg : Fin d → Fin d → Fin d → ℝ)
    (Γbg1 : Fin d → Fin d → Fin d → Fin d → ℝ)
    {t : ℝ} (ht : 0 < t) (z : Fin d → ℝ) (i k : Fin d) :
    GenuinePhiRD.phiRDWithBackgroundJetOfJet Γbg Γbg1 (actualGaussianMetricJet D ht z) i k =
      GenuinePhiRD.jetPrincipalContraction A (actualGaussianMetricJet D ht z) i k +
      GenuinePhiRD.frozenCoefficientRemainderOfJet A Γbg Γbg1 (actualGaussianMetricJet D ht z) i k :=
  GenuinePhiRD.phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder
    A Γbg Γbg1 (actualGaussianMetricJet D ht z)
    (actualGaussianMetricJet_det_ne_zero D hc hcoer ht z)
    (fun a b => actualGaussianMetricJet_val_metric_symm D hsymm ht z a b)
    (fun a b j l => actualGaussianMetricJet_deriv2_spatial_symm D ht z a b j l)
    (fun a b j l => actualGaussianMetricJet_deriv2_metric_symm D hsymm ht z a b j l) i k

section LiteralInitialMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Literal C2 initial metric data construct actual Gaussian jets with all
three split symmetry premises and the actual determinant premise, together
with the algebraic split for arbitrary background arrays. No supplied jet,
symmetry, coefficient-closeness, background witness or solver is assumed. -/
theorem exists_initialMetricActualGaussianJet_symmetricPrincipalSplit
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
      (∀ t : ℝ, ∀ ht : 0 < t, ∀ z,
        (∀ i j, (actualGaussianMetricJet D ht z).val i j =
          (actualGaussianMetricJet D ht z).val j i) ∧
        (∀ k i j, (actualGaussianMetricJet D ht z).deriv1 k i j =
          (actualGaussianMetricJet D ht z).deriv1 k j i) ∧
        (∀ k l i j, (actualGaussianMetricJet D ht z).deriv2 k l i j =
          (actualGaussianMetricJet D ht z).deriv2 l k i j) ∧
        (∀ k l i j, (actualGaussianMetricJet D ht z).deriv2 k l i j =
          (actualGaussianMetricJet D ht z).deriv2 k l j i) ∧
        (actualGaussianMetricJet D ht z).val.det ≠ 0 ∧
        ∀ A Γbg Γbg1 i k,
          GenuinePhiRD.phiRDWithBackgroundJetOfJet Γbg Γbg1 (actualGaussianMetricJet D ht z) i k =
            GenuinePhiRD.jetPrincipalContraction A (actualGaussianMetricJet D ht z) i k +
            GenuinePhiRD.frozenCoefficientRemainderOfJet A Γbg Γbg1 (actualGaussianMetricJet D ht z) i k) := by
  obtain ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond⟩ :=
    exists_initialMetricLocalizedHeatData_with_coercive_heat g₀ p
  refine ⟨c, hc, D, hnear, hsymm, hcoer, hheat, hsecond, ?_⟩
  intro t ht z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j => actualGaussianMetricJet_val_metric_symm D hsymm ht z i j
  · exact fun k i j => actualGaussianMetricJet_deriv1_metric_symm D hsymm ht z k i j
  · exact fun k l i j => actualGaussianMetricJet_deriv2_spatial_symm D ht z k l i j
  · exact fun k l i j => actualGaussianMetricJet_deriv2_metric_symm D hsymm ht z k l i j
  · exact actualGaussianMetricJet_det_ne_zero D hc hcoer ht z
  · exact fun A Γbg Γbg1 i k => actualGaussianMetricJet_principal_split
      D hc hcoer hsymm A Γbg Γbg1 ht z i k

end LiteralInitialMetric

end RicciFlow.AnalyticPDE
