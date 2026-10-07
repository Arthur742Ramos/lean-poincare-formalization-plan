/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2Localization
import PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
import PoincareCurvature.Analysis.FiniteCoordinateBilinear

/-!
# Positive frozen-exterior C² bilinear fields

The positive coercivity constant, the small neighborhood and the cutoff are
constructed from an actual local C² field and pointwise positivity. The
rank-zero case is handled internally. The lower bound holds on the whole
Euclidean space, including the frozen exterior.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace RicciFlow.AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative stability of coercivity for genuine bilinear operator norms. -/
theorem bilinear_coercivity_of_norm_sub_le
    {B C : E →L[ℝ] E →L[ℝ] ℝ} {c ε : ℝ}
    (hB : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) (hε : ‖C - B‖ ≤ ε) :
    ∀ v, (c - ε) * ‖v‖ ^ 2 ≤ C v v := by
  intro v
  have hb : ‖(C - B) v v‖ ≤ ε * ‖v‖ ^ 2 := by
    calc
      ‖(C - B) v v‖ ≤ ‖(C - B) v‖ * ‖v‖ := ((C - B) v).le_opNorm v
      _ ≤ (‖C - B‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((C - B).le_opNorm v) (norm_nonneg v)
      _ ≤ (ε * ‖v‖) * ‖v‖ := by gcongr
      _ = ε * ‖v‖ ^ 2 := by ring
  have hl : -(ε * ‖v‖ ^ 2) ≤ (C - B) v v :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)).1
  have he : (C - B) v v = C v v - B v v := rfl
  have h := hB v
  rw [he] at hl
  nlinarith

/-- A finite-dimensional positive form has a coercivity constant in every rank. -/
theorem exists_bilinear_coercivity_of_pos [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ B v v := by
  by_cases hsub : Subsingleton E
  · letI := hsub
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    exact Bundle.ContinuousLinearMap.exists_pos_mul_sq_le_of_pos B hB

/-- Construct a globally C², uniformly coercive localization which agrees with
the actual local form near the selected point and freezes to its value outside
a compact set. No global positive-rank or higher-regularity premise is added. -/
theorem exists_positiveFrozenC2Bilinear
    {n : ℕ} [FiniteDimensional ℝ E]
    {F : (Fin n → ℝ) → E →L[ℝ] E →L[ℝ] ℝ}
    {U : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hF : ContDiffOn ℝ 2 F U)
    (hpos : ∀ v, v ≠ 0 → 0 < F x₀ v v) :
    ∃ χ : (Fin n → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      ContDiff ℝ 2 (fun x => F x₀ + χ x • (F x - F x₀)) ∧
      (∀ᶠ x in 𝓝 x₀, F x₀ + χ x • (F x - F x₀) = F x) ∧
      (∀ x ∉ tsupport χ, F x₀ + χ x • (F x - F x₀) = F x₀) ∧
      (∀ x v, c * ‖v‖ ^ 2 ≤ (F x₀ + χ x • (F x - F x₀)) v v) := by
  obtain ⟨c, hc, hcoer⟩ := exists_bilinear_coercivity_of_pos (F x₀) hpos
  let V : Set (Fin n → ℝ) := U ∩ F ⁻¹' ball (F x₀) (c / 2)
  have hVo : IsOpen V := hF.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hxV : x₀ ∈ V := ⟨hx₀, by simp [half_pos hc]⟩
  obtain ⟨χ, hχ, hχc, hχV, hχone, hχIcc⟩ :=
    SmoothDependenceCk.exists_contDiff_cutoff_one_nhdsSet_of_isCompact
      (n := (2 : ℕ∞)) isCompact_singleton hVo (singleton_subset_iff.mpr hxV)
  have hχU : tsupport χ ⊆ U := fun x hx => (hχV hx).1
  have hP := SmoothDependenceCk.contDiff_and_hasCompactSupport_cutoff_smul
    (w := fun x => F x - F x₀)
    hU (hF.sub (contDiffOn_const (c := F x₀))) hχ hχc hχU
  refine ⟨χ, c / 2, half_pos hc, hχ, hχc, hχU, hχIcc,
    contDiff_const.add hP.1, ?_, ?_, ?_⟩
  · have hχone' : ∀ᶠ x in 𝓝 x₀, χ x = 1 := by
      simpa only [nhdsSet_singleton] using hχone
    filter_upwards [hχone'] with x hx
    ext u w
    change F x₀ u w + χ x * (F x u w - F x₀ u w) = F x u w
    rw [hx]
    ring
  · intro x hx
    ext u w
    change F x₀ u w + χ x * (F x u w - F x₀ u w) = F x₀ u w
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  · intro x v
    have hclose : ‖(F x₀ + χ x • (F x - F x₀)) - F x₀‖ ≤ c / 2 := by
      by_cases hx : x ∈ tsupport χ
      · have hball : F x ∈ ball (F x₀) (c / 2) := (hχV hx).2
        have hnorm : ‖F x - F x₀‖ < c / 2 := by
          letI : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
          have hdist : dist (F x) (F x₀) = ‖F x - F x₀‖ :=
            @dist_eq_norm (E →L[ℝ] E →L[ℝ] ℝ)
              (ContinuousLinearMap.toSeminormedAddCommGroup
                (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ)
                (σ₁₂ := RingHom.id ℝ))
              (F x) (F x₀)
          exact hdist ▸ (mem_ball.mp hball)
        letI : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
        letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
        letI : NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
          NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
        have hcancel : (F x₀ + χ x • (F x - F x₀)) - F x₀ =
            χ x • (F x - F x₀) := by
          ext u w
          change F x₀ u w + χ x * (F x u w - F x₀ u w) - F x₀ u w =
            χ x * (F x u w - F x₀ u w)
          ring
        rw [hcancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχIcc x).1]
        calc
          χ x * ‖F x - F x₀‖ ≤ 1 * ‖F x - F x₀‖ :=
            mul_le_mul_of_nonneg_right (hχIcc x).2
              (ContinuousLinearMap.opNorm_nonneg (F x - F x₀))
          _ ≤ c / 2 := by simpa using hnorm.le
      · have hzero : (F x₀ + χ x • (F x - F x₀)) - F x₀ = 0 := by
          ext u w
          change F x₀ u w + χ x * (F x u w - F x₀ u w) - F x₀ u w = 0
          rw [image_eq_zero_of_notMem_tsupport hx]
          ring
        rw [hzero, ContinuousLinearMap.opNorm_zero]
        exact (half_pos hc).le
    have h := bilinear_coercivity_of_norm_sub_le hcoer hclose v
    convert h using 1 <;> ring

open PoincareCurvature.FiniteCoordinateBilinear

/-- Local C² positive matrix data produce genuinely bounded heat input whose
entire Euclidean extension is uniformly positive and whose Hessian entries are
uniformly continuous. Positivity is needed only at the localization point. -/
theorem exists_positiveFrozenC2MatrixHeatData
    {n d : ℕ} {G : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    {U : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hG : ContDiffOn ℝ 2 G U)
    (hpos : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < ofMatrix (G x₀) v v)
    (hsymm : ∀ x ∈ U, ∀ i k, G x i k = G x k i) :
    ∃ χ : (Fin n → ℝ) → ℝ, ∃ c > 0,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data n,
        (∀ i k x, (D i k).value x = G x₀ i k + χ x * (G x i k - G x₀ i k)) ∧
        (∀ᶠ x in 𝓝 x₀, ∀ i k, (D i k).value x = G x i k) ∧
        (∀ x ∉ tsupport χ, ∀ i k, (D i k).value x = G x₀ i k) ∧
        (∀ x i k, (D i k).value x = (D k i).value x) ∧
        (∀ x v, c * ‖v‖ ^ 2 ≤ ofMatrix (fun i k => (D i k).value x) v v) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin n → ℝ) → ℝ)) := by
  let F : (Fin n → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
    fun x => ofMatrix (G x)
  have hF : ContDiffOn ℝ 2 F U := contDiff_ofMatrix.comp_contDiffOn hG
  obtain ⟨χ, c, hc, hχ, hχc, hχU, _hχIcc, _hFext, hFeq, hFout, hcoer⟩ :=
    exists_positiveFrozenC2Bilinear hU hx₀ hF hpos
  let P : (Fin n → ℝ) → (Fin d → Fin d → ℝ) := fun x => χ x • (G x - G x₀)
  have hP : ContDiff ℝ 2 P ∧ HasCompactSupport P :=
    SmoothDependenceCk.contDiff_and_hasCompactSupport_cutoff_smul
      hU (hG.sub contDiffOn_const) hχ hχc hχU
  have hPe : ∀ i k, ContDiff ℝ 2 (fun x => P x i k) := fun i k =>
    contDiff_pi.mp (contDiff_pi.mp hP.1 i) k
  have hPec : ∀ i k, HasCompactSupport (fun x => P x i k) := fun i k =>
    hP.2.comp_left (g := fun A : Fin d → Fin d → ℝ => A i k) rfl
  let D : Fin d → Fin d → EuclideanBoundedC2Data n := fun i k =>
    (EuclideanBoundedC2Data.ofCompactSupport (hPe i k) (hPec i k)).addConst (G x₀ i k)
  have hmatrix : ∀ x,
      ofMatrix (fun i k => (D i k).value x) = F x₀ + χ x • (F x - F x₀) := by
    intro x
    change ofMatrix (G x₀ + χ x • (G x - G x₀)) = _
    rw [ofMatrix_add, ofMatrix_smul, ofMatrix_sub]
  refine ⟨χ, c, hc, hχ, hχc, hχU, D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k x
    rfl
  · filter_upwards [hFeq] with x hx i k
    have h := congrArg (fun B => B (Pi.single i 1) (Pi.single k 1))
      ((hmatrix x).trans hx)
    simpa only [F, ofMatrix_coordinateVector] using h
  · intro x hx i k
    change G x₀ i k + χ x * (G x i k - G x₀ i k) = G x₀ i k
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, add_zero]
  · intro x i k
    change G x₀ i k + χ x * (G x i k - G x₀ i k) =
      G x₀ k i + χ x * (G x k i - G x₀ k i)
    by_cases hx : x ∈ tsupport χ
    · rw [hsymm x₀ hx₀ i k, hsymm x (hχU hx) i k]
    · simp [image_eq_zero_of_notMem_tsupport hx, hsymm x₀ hx₀ i k]
  · intro x v
    rw [hmatrix]
    exact hcoer x v
  · intro i k a b
    exact EuclideanBoundedC2Data.uniformContinuous_second_ofCompactSupport
      (hPe i k) (hPec i k) a b

end RicciFlow.AnalyticPDE
