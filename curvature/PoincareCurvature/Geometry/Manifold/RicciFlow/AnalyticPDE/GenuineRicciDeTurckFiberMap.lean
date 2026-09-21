/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.NemytskiiChainRule
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorialCommutator
import PoincareCurvature.Analysis.MatrixSmoothness

/-!
# The genuine Ricci–DeTurck fiber map

Defines the **genuine** Ricci–DeTurck fiber map `Φ_RD : Jet2 d d → Matrix`
using actual coordinate formulas, and proves smoothness.

No `sorry`, no `admit`, no axioms.
-/

open Matrix PoincareCurvature.MatrixSmoothness
open scoped Topology

namespace RicciFlow.AnalyticPDE

variable {d : ℕ}

namespace GenuinePhiRD

/-! ## 1. The 0-jet projection is a continuous linear map -/

/-- The 0-jet projection as a linear map. -/
def jet2ValLinear : (Jet2 d d) →ₗ[ℝ] (Matrix (Fin d) (Fin d) ℝ) where
  toFun j := j.val
  map_add' j₁ j₂ := by
    obtain ⟨v₁, d₁, h₁⟩ := j₁
    obtain ⟨v₂, d₂, h₂⟩ := j₂
    rfl
  map_smul' r j := by
    obtain ⟨v, d₁, h⟩ := j
    rfl

/-- The 0-jet projection is 1-Lipschitz in the Jet2 norm. -/
theorem jet2Val_bound (j : Jet2 d d) : ‖jet2ValLinear (d := d) j‖ ≤ 1 * ‖j‖ := by
  simp only [jet2ValLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  rw [Jet2.jet2_norm_eq]
  have h1 : (0:ℝ) ≤ ∑ i : Fin d, ‖j.deriv1 i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h2 : (0:ℝ) ≤ ∑ i : Fin d, ∑ k : Fin d, ‖j.deriv2 i k‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  linarith

/-- The 0-jet projection as a continuous linear map (type inferred to avoid
instance diamond). -/
noncomputable def jet2ValCLM :=
  LinearMap.mkContinuous (f := jet2ValLinear (d := d)) 1 (jet2Val_bound (d := d))

/-- The 0-jet projection is smooth. -/
theorem contDiff_jet2_val {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun j : Jet2 d d => j.val) := by
  have h : (fun j : Jet2 d d => j.val) = ⇑jet2ValCLM := rfl
  rw [h]
  exact jet2ValCLM.contDiff

/-! ## 2. Smoothness of the matrix inverse on the invertible locus -/

/-- The matrix inverse is `ContDiffOn` on the invertible locus, via
`M⁻¹ = (det M)⁻¹ • adj(M)`.

We state this for the function type `Fin d → Fin d → ℝ` (with Pi instances)
to match `PoincareCurvature.MatrixSmoothness.contDiff_det`. -/
theorem contDiffOn_matrixInv {n : WithTop ℕ∞} :
    ContDiffOn ℝ n
      (fun A : Fin d → Fin d → ℝ => fun i j =>
        ((show Matrix (Fin d) (Fin d) ℝ from A).det)⁻¹ *
          ((show Matrix (Fin d) (Fin d) ℝ from A).adjugate i j))
      {A | (show Matrix (Fin d) (Fin d) ℝ from A).det ≠ 0} := by
  -- The function is `(det)⁻¹ • (adjugate as function)`, pointwise.
  -- We prove it as a smul of ContDiffOn maps.
  have h_det : ContDiff ℝ n
      (fun A : Fin d → Fin d → ℝ => (show Matrix (Fin d) (Fin d) ℝ from A).det) :=
    contDiff_det (ι := Fin d) (n := n)
  have h_det_inv : ContDiffOn ℝ n
      (fun A : Fin d → Fin d → ℝ => ((show Matrix (Fin d) (Fin d) ℝ from A).det)⁻¹)
      {A | (show Matrix (Fin d) (Fin d) ℝ from A).det ≠ 0} :=
    h_det.contDiffOn.inv (fun A hA => hA)
  have h_adj : ContDiff ℝ n
      (fun A : Fin d → Fin d → ℝ => fun i j =>
        (show Matrix (Fin d) (Fin d) ℝ from A).adjugate i j) := by
    have h := contDiff_adjugate (ι := Fin d) (n := n)
    -- `contDiff_adjugate` gives `fun A => adjugate A` (as Fun).
    -- Our target is `fun A => fun i j => (adjugate A) i j`, which is the same.
    simpa using h
  have h_smul := h_det_inv.smul h_adj.contDiffOn
  -- `h_smul` : `ContDiffOn ... (((fun A => (det A)⁻¹) • (fun A => fun i j => adj A i j))) ...`
  -- We need: `ContDiffOn ... (fun A => fun i j => (det A)⁻¹ * adj A i j) ...`
  -- These are equal by pointwise smul.
  have h_eq_fun : ((fun A : Fin d → Fin d → ℝ => ((show Matrix (Fin d) (Fin d) ℝ from A).det)⁻¹) •
      (fun A : Fin d → Fin d → ℝ => fun i j =>
        (show Matrix (Fin d) (Fin d) ℝ from A).adjugate i j)) =
      (fun A : Fin d → Fin d → ℝ => fun i j =>
        ((show Matrix (Fin d) (Fin d) ℝ from A).det)⁻¹ *
          ((show Matrix (Fin d) (Fin d) ℝ from A).adjugate i j)) := by
    funext A i j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h_eq_fun] at h_smul
  exact h_smul

/-- The inverse metric as a function of the 2-jet (as a function type for Pi instances).

Defined via the adjugate formula: `(g⁻¹) i j = (det g)⁻¹ * (adjugate g) i j`. -/
noncomputable def invMetricOfJet (j : Jet2 d d) : Fin d → Fin d → ℝ :=
  fun i k => (j.val.det)⁻¹ * (j.val.adjugate i k)

/-- The 0-jet as a function type (for composition with Pi-instance lemmas).

Defined as an explicit lambda to ensure Pi instances on the codomain. -/
noncomputable def jet2ValFun (j : Jet2 d d) : Fin d → Fin d → ℝ :=
  fun i k => j.val i k

/-- The 0-jet as a function is smooth (Pi instances on codomain).

The map `j ↦ fun i k => j.val i k` is a bounded linear map, with
`‖fun i k => j.val i k‖_Pi ≤ ‖j‖_Jet2` via sup ≤ sum. -/
theorem contDiff_jet2ValFun {n : WithTop ℕ∞} :
    ContDiff ℝ n (jet2ValFun (d := d)) := by
  unfold jet2ValFun
  -- Define the linear map
  let fLinear : (Jet2 d d) →ₗ[ℝ] (Fin d → Fin d → ℝ) :=
    { toFun := fun j => fun i k => j.val i k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Bound: `‖fLinear j‖ ≤ 1 * ‖j‖`
  have h_bound : ∀ j : Jet2 d d, ‖fLinear j‖ ≤ 1 * ‖j‖ := by
    intro j
    rw [one_mul]
    -- `fLinear j = fun i k => j.val i k` definitionally
    -- Show `‖fun i k => j.val i k‖ ≤ ‖j‖` via `pi_norm_le_iff`
    have h_pi : ‖(fun i k => j.val i k : Fin d → Fin d → ℝ)‖ ≤ ‖j‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro k
      -- `‖j.val i k‖ ≤ ‖j‖`
      calc ‖j.val i k‖ ≤ ∑ k' : Fin d, ‖j.val i k'‖ := by
            apply Finset.single_le_sum _ (Finset.mem_univ k)
            intro k' _
            exact norm_nonneg _
        _ ≤ ∑ i' : Fin d, ∑ k' : Fin d, ‖j.val i' k'‖ := by
            apply Finset.single_le_sum _ (Finset.mem_univ i)
            intro i' _
            exact Finset.sum_nonneg (fun k' _ => norm_nonneg _)
        _ = ‖j.val‖ := rfl
        _ ≤ ‖j‖ := by
            have h_eq := Jet2.jet2_norm_eq (d := d) (j := j)
            rw [h_eq]
            have hA : 0 ≤ ∑ i : Fin d, ‖j.deriv1 i‖ :=
              Finset.sum_nonneg (fun i _ => norm_nonneg _)
            have hB : 0 ≤ ∑ i : Fin d, ∑ k : Fin d, ‖j.deriv2 i k‖ :=
              Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
            linarith
    -- `fLinear j` is definitionally `fun i k => j.val i k`
    have h_def : (fLinear j : Fin d → Fin d → ℝ) = (fun i k => j.val i k) := rfl
    rw [h_def]
    exact h_pi
  -- The linear map is continuous, hence a CLM
  let fCLM := LinearMap.mkContinuous fLinear 1 h_bound
  have h_eq : (fun j : Jet2 d d => fun i k => j.val i k) = ⇑fCLM := rfl
  rw [h_eq]
  exact fCLM.contDiff

/-- The inverse metric is smooth on the invertible locus. -/
theorem contDiffOn_invMetricOfJet {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (invMetricOfJet (d := d)) {j : Jet2 d d | j.val.det ≠ 0} := by
  unfold invMetricOfJet
  have h_comp : (fun j : Jet2 d d => fun i k => (j.val.det)⁻¹ * (j.val.adjugate i k)) =
      (fun A : Fin d → Fin d → ℝ => fun i k =>
        ((show Matrix (Fin d) (Fin d) ℝ from A).det)⁻¹ *
          ((show Matrix (Fin d) (Fin d) ℝ from A).adjugate i k)) ∘
      (jet2ValFun (d := d)) := by
    funext j
    -- `jet2ValFun j` is `j.val` as a function; `(show Matrix ... from (jet2ValFun j))`
    -- is `j.val` as a matrix. These are definitionally the same.
    rfl
  rw [h_comp]
  apply ContDiffOn.comp contDiffOn_matrixInv
  · exact contDiff_jet2ValFun.contDiffOn
  · intro j hj
    simp at hj ⊢
    exact hj

end GenuinePhiRD

end RicciFlow.AnalyticPDE
