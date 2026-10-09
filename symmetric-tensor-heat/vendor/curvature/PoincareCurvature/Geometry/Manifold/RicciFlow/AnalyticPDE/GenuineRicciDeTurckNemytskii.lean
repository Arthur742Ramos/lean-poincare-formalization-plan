/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckFiberMap

/-!
# Nemytskii packaging of the genuine Ricci–DeTurck fiber map

Packages the smooth coordinate fiber map `phiRDOfJet`
(from `GenuineRicciDeTurckFiberMap`) as `NemytskiiData` for the Hölder
Nemytskii machine (`NemytskiiChainRule`).

Main results:
- `FiniteDimensional ℝ (Jet2 n d)`: the 2-jet fiber is finite-dimensional,
  hence proper; closed balls are compact.
- `isOpen_jetInvertibleLocus`: the locus `{j | j.val.det ≠ 0}` is open.
- `contDiffOn_phiRDMatrix`: the matrix-valued fiber map is smooth there.
- `phiRDNemytskiiData`: the packaged `NemytskiiData`. The bounds `B`
  (uniform bound on `‖Φ'‖`) and `L` (Lipschitz constant of `Φ'`) are
  *proved* from compactness of a closed ball around the Euclidean jet,
  not assumed.
- `genuineNRD`: the Nemytskii operator `u ↦ Φ_RD ∘ u`, with Hölder bound.

No `sorry`, no `admit`, no axioms.
-/

open Matrix PoincareCurvature.MatrixSmoothness
open scoped Topology

namespace RicciFlow.AnalyticPDE

variable {d : ℕ}
variable (Γbg : Fin d → Fin d → Fin d → ℝ)

namespace GenuinePhiRD

/-! ## 1. The 2-jet fiber is finite-dimensional -/

/-- `Jet2 n d` unfolded as a product of matrix spaces. -/
def jet2ProdEquiv (n d : ℕ) : (Jet2 n d) ≃ₗ[ℝ]
    (Matrix (Fin d) (Fin d) ℝ × (Fin n → Matrix (Fin d) (Fin d) ℝ) ×
      (Fin n → Fin n → Matrix (Fin d) (Fin d) ℝ)) where
  toFun j := (j.val, j.deriv1, j.deriv2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {n : ℕ}

/-- The 2-jet fiber is finite-dimensional, hence proper. -/
instance : FiniteDimensional ℝ (Jet2 n d) :=
  LinearEquiv.finiteDimensional (jet2ProdEquiv n d).symm

/-! ## 2. The invertible locus is open -/

/-- The locus of 2-jets whose metric value is invertible. -/
def jetInvertibleLocus : Set (Jet2 d d) := {j : Jet2 d d | j.val.det ≠ 0}

/-- A matrix entry is bounded by the matrix norm. -/
theorem abs_entry_le_matrix_norm (M : Matrix (Fin d) (Fin d) ℝ) (i k : Fin d) :
    |M i k| ≤ ‖M‖ := by
  rw [matrix_norm_eq]
  have h1 : |M i k| ≤ ∑ k' : Fin d, |M i k'| := by
    have h := Finset.single_le_sum (s := Finset.univ (α := Fin d))
      (f := fun k' : Fin d => |M i k'|)
      (fun k' _ => abs_nonneg _)
      (Finset.mem_univ k)
    simpa using h
  have h2 : (∑ k' : Fin d, |M i k'|) ≤ ∑ i' : Fin d, ∑ k' : Fin d, |M i' k'| := by
    have h := Finset.single_le_sum (s := Finset.univ (α := Fin d))
      (f := fun i' : Fin d => ∑ k' : Fin d, |M i' k'|)
      (fun i' _ => Finset.sum_nonneg (fun k' _ => abs_nonneg _))
      (Finset.mem_univ i)
    simpa using h
  exact le_trans h1 h2

/-- The matrix norm is bounded by the 2-jet norm. -/
theorem matrix_norm_le_jet2_norm (j : Jet2 d d) : ‖j.val‖ ≤ ‖j‖ := by
  rw [Jet2.jet2_norm_eq]
  have h1 : 0 ≤ ∑ i : Fin d, ‖j.deriv1 i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h2 : 0 ≤ ∑ i : Fin d, ∑ k : Fin d, ‖j.deriv2 i k‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  linarith

/-- Coordinate evaluation on 2-jets, as a linear map. -/
def jet2CoordLinear (i k : Fin d) : (Jet2 d d) →ₗ[ℝ] ℝ where
  toFun j := j.val i k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate evaluation is bounded by the jet norm. -/
theorem norm_jet2CoordLinear_le (i k : Fin d) (j : Jet2 d d) :
    ‖jet2CoordLinear (d := d) i k j‖ ≤ 1 * ‖j‖ := by
  rw [one_mul, Real.norm_eq_abs]
  show |j.val i k| ≤ ‖j‖
  exact le_trans (abs_entry_le_matrix_norm _ _ _) (matrix_norm_le_jet2_norm _)

/-- Coordinate evaluation on 2-jets, as a continuous linear map. -/
noncomputable def jet2CoordCLM (i k : Fin d) : (Jet2 d d) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (jet2CoordLinear (d := d) i k) 1
    (norm_jet2CoordLinear_le (d := d) i k)

/-- Each 2-jet coordinate is continuous. -/
theorem continuous_jet2_coord (i k : Fin d) :
    Continuous (fun j : Jet2 d d => j.val i k) :=
  (jet2CoordCLM (d := d) i k).continuous

/-- The 0-jet projection is continuous into the Pi topology. -/
theorem continuous_jet2_val_pi :
    Continuous (fun j : Jet2 d d => fun i : Fin d => fun k : Fin d => j.val i k) := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro k
  exact continuous_jet2_coord (d := d) i k

/-- The determinant is continuous in the 2-jet. -/
theorem continuous_jet2_det :
    Continuous (fun j : Jet2 d d => j.val.det) := by
  have h2 : Continuous
      (fun A : Fin d → Fin d → ℝ => (show Matrix (Fin d) (Fin d) ℝ from A).det) :=
    (contDiff_det (ι := Fin d) (n := (⊤ : WithTop ℕ∞))).continuous
  have heq : (fun j : Jet2 d d => j.val.det) =
      (fun A : Fin d → Fin d → ℝ => (show Matrix (Fin d) (Fin d) ℝ from A).det) ∘
        (fun j : Jet2 d d => fun i : Fin d => fun k : Fin d => j.val i k) := rfl
  rw [heq]
  exact h2.comp (continuous_jet2_val_pi (d := d))

/-- The invertible locus is open. -/
theorem isOpen_jetInvertibleLocus : IsOpen (jetInvertibleLocus (d := d)) := by
  have heq : jetInvertibleLocus (d := d)
      = (fun j : Jet2 d d => j.val.det) ⁻¹' {0}ᶜ := rfl
  rw [heq]
  exact (continuous_jet2_det (d := d)).isOpen_preimage _ isOpen_compl_singleton

/-! ## 3. The matrix-valued fiber map is smooth -/

/-- The Ricci–DeTurck fiber map, matrix-valued. -/
noncomputable def phiRDMatrix (j : Jet2 d d) : Fin d → Fin d → ℝ :=
  fun i k => phiRDOfJet (d := d) Γbg j i k

/-- The matrix-valued fiber map is smooth on the invertible locus.

We use the Pi type `Fin d → Fin d → ℝ` (definitionally `Matrix`) to avoid
the custom norm instance diamond on `Matrix`. -/
theorem contDiffOn_phiRDMatrix :
    ContDiffOn ℝ ⊤ (phiRDMatrix (d := d) Γbg) (jetInvertibleLocus (d := d)) := by
  have h : ∀ i : Fin d, ∀ k : Fin d,
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun j : Jet2 d d => phiRDOfJet (d := d) Γbg j i k)
        (jetInvertibleLocus (d := d)) :=
    fun i k => contDiffOn_phiRDOfJet (d := d) Γbg (n := ⊤) i k
  have heq : phiRDMatrix (d := d) Γbg =
      fun j : Jet2 d d => fun i : Fin d => fun k : Fin d =>
        phiRDOfJet (d := d) Γbg j i k := rfl
  rw [heq]
  exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun k => h i k))

/-! ## 4. Bounds of continuous functions on compacts -/

/-- A continuous function on a compact set has bounded norm (existence version).

We use `continuous_norm.comp_continuousOn` which works for CLM-valued
functions because `ContinuousLinearMap.topologicalSpace` is definitionally
the norm topology. -/
theorem exists_norm_bound_of_continuousOn {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖f x‖ ≤ B := by
  have hnorm : ContinuousOn (fun x => ‖f x‖) K :=
    continuous_norm.comp_continuousOn hf
  have himg : IsCompact ((fun x => ‖f x‖) '' K) :=
    hK.image_of_continuousOn hnorm
  obtain ⟨B, hB⟩ := himg.bddAbove
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have hmem : ‖f x‖ ∈ (fun x => ‖f x‖) '' K := ⟨x, hx, rfl⟩
  exact le_trans (hB hmem) (le_max_left _ _)

/-- The Subtype version, for use in data construction. -/
noncomputable def norm_bound_of_continuousOn {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    { B : ℝ // 0 ≤ B ∧ ∀ x ∈ K, ‖f x‖ ≤ B } :=
  ⟨Classical.choose (exists_norm_bound_of_continuousOn hK hf),
   Classical.choose_spec (exists_norm_bound_of_continuousOn hK hf)⟩

/-! ## 5. A C² map has Lipschitz derivative on compacts -/

/-- A `C^∞` (hence `C²`) map has Lipschitz `fderivWithin` on a compact
convex set. The Lipschitz constant is *proved* via the mean value theorem
applied to the derivative, whose second derivative is bounded on the
compact by continuity. -/
noncomputable def lipschitzOnWith_fderivWithin_of_contDiffOn_top
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E → F} {S K : Set E}
    (hS : IsOpen S) (hK : IsCompact K) (hKs : K ⊆ S) (hconv : Convex ℝ K)
    (hΦ : ContDiffOn ℝ ⊤ Φ S) :
    { C : NNReal // LipschitzOnWith C (fun x => fderivWithin ℝ Φ S x) K } := by
  have hU : UniqueDiffOn ℝ S := hS.uniqueDiffOn
  have h2 : ContDiffOn ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) Φ S := hΦ.of_le le_top
  have hg1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fderivWithin ℝ Φ S) S :=
    h2.fderivWithin hU le_rfl
  have hdiff : DifferentiableOn ℝ (fderivWithin ℝ Φ S) S :=
    hg1.differentiableOn (by simp)
  have hcont2 : ContinuousOn (fderivWithin ℝ (fderivWithin ℝ Φ S) S) S :=
    hg1.continuousOn_fderivWithin hU (by simp)
  -- Bound the second derivative on K via compactness (inlined to avoid
  -- instance unification issues with the general lemma).
  have hex : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ K, ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖ ≤ B := by
    have h1 : Continuous (fun L : E →L[ℝ] (E →L[ℝ] F) => ‖L‖) := by
      show Continuous
        (fun L : E →L[ℝ] (E →L[ℝ] F) => @norm _ SeminormedAddGroup.toNorm L)
      exact continuous_norm
    have hnorm : ContinuousOn
        (fun x => ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖) K :=
      h1.comp_continuousOn (hcont2.mono hKs)
    have himg : IsCompact
        ((fun x => ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖) '' K) :=
      hK.image_of_continuousOn hnorm
    obtain ⟨B, hB⟩ := himg.bddAbove
    refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
    have hmem : ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖ ∈
        (fun x => ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖) '' K :=
      ⟨x, hx, rfl⟩
    exact le_trans (hB hmem) (le_max_left _ _)
  let B := Classical.choose hex
  have hB0 : 0 ≤ B := (Classical.choose_spec hex).1
  have hB : ∀ x ∈ K, ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖ ≤ B :=
    (Classical.choose_spec hex).2
  refine ⟨⟨B, hB0⟩, hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := fun x => fderivWithin ℝ (fderivWithin ℝ Φ S) S x) ?_ ?_⟩
  · intro x hx
    exact ((hdiff x (hKs hx)).hasFDerivWithinAt).mono hKs
  · intro x hx
    have hle : ‖fderivWithin ℝ (fderivWithin ℝ Φ S) S x‖ ≤ B := hB x hx
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    exact hle

/-! ## 6. A compact convex set of jets around the Euclidean jet -/

/-- The Euclidean 2-jet: identity metric, vanishing derivatives. -/
noncomputable def euclideanJet2 : Jet2 d d := ⟨1, 0, 0⟩

/-- The Euclidean jet lies in the invertible locus. -/
theorem euclideanJet2_mem_locus :
    euclideanJet2 (d := d) ∈ jetInvertibleLocus (d := d) := by
  show Matrix.det (1 : Matrix (Fin d) (Fin d) ℝ) ≠ 0
  rw [Matrix.det_one]
  exact one_ne_zero

/-- Some ball around the Euclidean jet stays in the locus. -/
theorem exists_ball_subset_locus :
    ∃ r > 0, Metric.ball (euclideanJet2 (d := d)) r ⊆ jetInvertibleLocus (d := d) :=
  Metric.isOpen_iff.mp (isOpen_jetInvertibleLocus (d := d)) _
    euclideanJet2_mem_locus

/-- Radius of a ball around the Euclidean jet inside the locus. -/
noncomputable def phiRDRadius : ℝ :=
  Classical.choose (exists_ball_subset_locus (d := d))

theorem phiRDRadius_pos : 0 < phiRDRadius (d := d) :=
  (Classical.choose_spec (exists_ball_subset_locus (d := d))).1

theorem phiRDBall_subset :
    Metric.ball (euclideanJet2 (d := d)) (phiRDRadius (d := d))
      ⊆ jetInvertibleLocus (d := d) :=
  (Classical.choose_spec (exists_ball_subset_locus (d := d))).2

/-- Compact convex set of jets: closed ball of half the radius. -/
noncomputable def phiRDK : Set (Jet2 d d) :=
  Metric.closedBall (euclideanJet2 (d := d)) (phiRDRadius (d := d) / 2)

theorem phiRDK_subset_locus : phiRDK (d := d) ⊆ jetInvertibleLocus (d := d) := by
  intro x hx
  have hx' : x ∈ Metric.closedBall (euclideanJet2 (d := d)) (phiRDRadius (d := d) / 2) := hx
  have hlt : phiRDRadius (d := d) / 2 < phiRDRadius (d := d) := by
    have hpos := phiRDRadius_pos (d := d)
    linarith
  exact phiRDBall_subset (d := d) (Metric.closedBall_subset_ball hlt hx')

theorem convex_phiRDK : Convex ℝ (phiRDK (d := d)) :=
  convex_closedBall _ _

theorem isCompact_phiRDK : IsCompact (phiRDK (d := d)) :=
  isCompact_closedBall _ _

/-! ## 7. The Nemytskii data -/

/-- The derivative of the fiber map (as `fderivWithin` on the locus). -/
noncomputable def phiRDMatrixDeriv (x : Jet2 d d) :
    (Jet2 d d) →L[ℝ] (Fin d → Fin d → ℝ) :=
  fderivWithin ℝ (phiRDMatrix (d := d) Γbg) (jetInvertibleLocus (d := d)) x

/-- The Nemytskii data for the genuine Ricci–DeTurck fiber map.

The bounds `B` and `L` are proved from compactness, not assumed. -/
noncomputable def phiRDNemytskiiData :
    NemytskiiData (Jet2 d d) (Fin d → Fin d → ℝ) := by
  let ⟨L, hL⟩ := lipschitzOnWith_fderivWithin_of_contDiffOn_top
    (isOpen_jetInvertibleLocus (d := d)) (isCompact_phiRDK (d := d))
    (phiRDK_subset_locus (d := d)) (convex_phiRDK (d := d))
    (contDiffOn_phiRDMatrix (d := d) Γbg)
  have hcont1 : ContinuousOn (phiRDMatrixDeriv (d := d) Γbg)
      (jetInvertibleLocus (d := d)) :=
    (contDiffOn_phiRDMatrix (d := d) Γbg).continuousOn_fderivWithin
      (isOpen_jetInvertibleLocus (d := d)).uniqueDiffOn le_top
  -- Bound the derivative on K via compactness (inlined).
  have hexB : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ phiRDK (d := d), ‖phiRDMatrixDeriv (d := d) Γbg x‖ ≤ B := by
    have h1 : Continuous
        (fun L : (Jet2 d d) →L[ℝ] (Fin d → Fin d → ℝ) => ‖L‖) := by
      show Continuous (fun L : (Jet2 d d) →L[ℝ] (Fin d → Fin d → ℝ) =>
        @norm _ SeminormedAddGroup.toNorm L)
      exact continuous_norm
    have hnorm : ContinuousOn
        (fun x => ‖phiRDMatrixDeriv (d := d) Γbg x‖) (phiRDK (d := d)) :=
      h1.comp_continuousOn (hcont1.mono (phiRDK_subset_locus (d := d)))
    have himg : IsCompact
        ((fun x => ‖phiRDMatrixDeriv (d := d) Γbg x‖) '' phiRDK (d := d)) :=
      (isCompact_phiRDK (d := d)).image_of_continuousOn hnorm
    obtain ⟨B, hB⟩ := himg.bddAbove
    refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
    have hmem : ‖phiRDMatrixDeriv (d := d) Γbg x‖ ∈
        (fun x => ‖phiRDMatrixDeriv (d := d) Γbg x‖) '' phiRDK (d := d) :=
      ⟨x, hx, rfl⟩
    exact le_trans (hB hmem) (le_max_left _ _)
  let B := Classical.choose hexB
  have hB0 : 0 ≤ B := (Classical.choose_spec hexB).1
  have hBb : ∀ x ∈ phiRDK (d := d), ‖phiRDMatrixDeriv (d := d) Γbg x‖ ≤ B :=
    (Classical.choose_spec hexB).2
  have h2 : ContDiffOn ℝ (((1 : ℕ) : WithTop ℕ∞) + 1)
      (phiRDMatrix (d := d) Γbg) (jetInvertibleLocus (d := d)) :=
    (contDiffOn_phiRDMatrix (d := d) Γbg).of_le le_top
  have hdiff : DifferentiableOn ℝ (phiRDMatrix (d := d) Γbg)
      (jetInvertibleLocus (d := d)) :=
    h2.differentiableOn (by simp)
  refine ⟨phiRDMatrix (d := d) Γbg, phiRDMatrixDeriv (d := d) Γbg,
    phiRDK (d := d), convex_phiRDK (d := d), ?_,
    B, hB0, ?_, L, ?_⟩
  · intro x hx
    have hxS := phiRDK_subset_locus (d := d) hx
    exact ((hdiff x hxS).hasFDerivWithinAt).mono (phiRDK_subset_locus (d := d))
  · intro x hx
    exact hBb x hx
  · exact hL

/-! ## 8. The genuine Nemytskii operator -/

/-- The genuine Ricci–DeTurck Nemytskii operator: `u ↦ Φ_RD ∘ u`.

Returns the Pi type `Fin d → Fin d → ℝ` (definitionally `Matrix`);
use as `Matrix` via definitional unfolding. -/
noncomputable def genuineNRD {m : ℕ} (u : (Fin m → ℝ) → Jet2 d d) :
    (Fin m → ℝ) → (Fin d → Fin d → ℝ) :=
  (phiRDNemytskiiData (d := d) Γbg).nemytskii u

/-- The genuine operator preserves Hölder regularity, with constant `B * H`. -/
theorem isHolderNorm_genuineNRD {m : ℕ} {α H : ℝ} {u : (Fin m → ℝ) → Jet2 d d}
    (hu : IsHolderNorm α u H)
    (hrange : ∀ x, u x ∈ (phiRDNemytskiiData (d := d) Γbg).K) :
    IsHolderNorm α (genuineNRD (d := d) Γbg u)
      ((phiRDNemytskiiData (d := d) Γbg).B * H) :=
  (phiRDNemytskiiData (d := d) Γbg).isHolderNorm_nemytskii hu hrange

end GenuinePhiRD

end AnalyticPDE
end RicciFlow
