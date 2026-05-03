module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option linter.unusedSectionVars false

/-!
# Matrix-valued parabolic `C^{0,α}` closure

This module contains finite-dimensional algebraic closure facts for the
parabolic `C^{0,α}` predicates.  It is kept separate from `ParabolicHolder`
so determinant imports do not enlarge the base parabolic Holder module.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- A continuous nonvanishing function on a compact time-space set has norm uniformly bounded away
from zero. -/
theorem exists_pos_norm_lower_bound_of_isCompact_of_continuousOn_ne_zero {E : Type*}
    [NormedAddCommGroup E] {K : Set (ℝ × X)} {f : ℝ × X → E}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hne : ∀ ⦃z : ℝ × X⦄, z ∈ K → f z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖f z‖ := by
  by_cases hKnonempty : K.Nonempty
  · have hnorm : ContinuousOn (fun z => ‖f z‖) K := hf.norm
    rcases hK.exists_isMinOn hKnonempty hnorm with ⟨z₀, hz₀, hmin⟩
    refine ⟨‖f z₀‖, norm_pos_iff.mpr (hne hz₀), ?_⟩
    intro z hz
    exact (isMinOn_iff.mp hmin) z hz
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact False.elim (hKnonempty ⟨z, hz⟩)

/-- The sup constant for a single Leibniz-term in the determinant estimate. -/
def matrixDetTermBoundConst {n A : Type*} [Fintype n] [NormedRing A]
    (B : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  max ‖(1 : A)‖ 1 * ∏ i : n, max (B (σ i) i) 1

/-- The Holder constant for a single Leibniz-term in the determinant estimate. -/
def matrixDetTermHolderConst {n A : Type*} [Fintype n] [NormedRing A]
    (B H : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  (∑ i : n, H (σ i) i) * matrixDetTermBoundConst (A := A) B σ

/-- The sup constant used by the quantitative finite determinant estimate. -/
def matrixDetBoundConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermBoundConst (A := A) B σ

/-- The Holder constant used by the quantitative finite determinant estimate. -/
def matrixDetHolderConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B H : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermHolderConst (A := A) B H σ

theorem matrixDetTermBoundConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    (B : n → n → ℝ) (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermBoundConst (A := A) B σ := by
  exact mul_nonneg (zero_le_one.trans (le_max_right _ _))
    (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (B (σ i) i) 1))

theorem matrixDetTermHolderConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermHolderConst (A := A) B H σ := by
  exact mul_nonneg
    (Finset.sum_nonneg fun i _hi => hH (σ i) i)
    (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetBoundConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) :
    0 ≤ matrixDetBoundConst (A := A) B := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _) (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetHolderConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixDetHolderConst (A := A) B H := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _) (matrixDetTermHolderConst_nonneg (A := A) hH σ)

/-- The determinant of a finite matrix whose entries have explicit parabolic `C^{0,α}` bounds
has an explicit bounded parabolic `C^{0,α}` estimate.  This is the quantitative version used
before passing to the existential `ParabolicC0AlphaOn` closure theorem. -/
theorem matrix_det_with {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {B H : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (matrixDetBoundConst (A := A) B) (matrixDetHolderConst (A := A) B H)
      α (fun z => (M z).det) s := by
  classical
  let term : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaWith
        (‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) B σ)
        (‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermHolderConst (A := A) B H σ)
        α (term σ) s := by
    intro σ _hσ
    have hprod :
        ParabolicC0AlphaWith
          (matrixDetTermBoundConst (A := A) B σ)
          (matrixDetTermHolderConst (A := A) B H σ)
          α (fun z => ∏ i : n, M z (σ i) i) s := by
      simpa [matrixDetTermBoundConst, matrixDetTermHolderConst] using
        (ParabolicC0AlphaWith.finset_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (B := fun i => B (σ i) i)
          (H := fun i => H (σ i) i)
          (u := fun i z => M z (σ i) i)
          (fun i _hi => hH (σ i) i)
          (fun i _hi => hM (σ i) i))
    dsimp [term]
    simpa [zsmul_eq_mul] using hprod.zsmul (Equiv.Perm.sign σ)
  have hsum :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := A) B) (matrixDetHolderConst (A := A) B H)
        α (fun z => ∑ σ : Equiv.Perm n, term σ z) s := by
    simpa [matrixDetBoundConst, matrixDetHolderConst] using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset (Equiv.Perm n)))
        (B := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermBoundConst (A := A) B σ)
        (H := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermHolderConst (A := A) B H σ)
        (u := term) hterm)
  convert hsum using 1
  funext z
  dsimp [term]
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [← zsmul_eq_mul]
  rfl

/-- Determinants are pointwise Lipschitz on entrywise bounded finite matrices.  This is the
finite-dimensional algebra estimate behind local Lipschitz control of determinant terms in chart
coordinates. -/
theorem matrix_det_norm_sub_le {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) (hN : ∀ i j, ‖N i j‖ ≤ C i j) :
    ‖M.det - N.det‖ ≤
      ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) := by
  classical
  let termM : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M (σ i) i
  let termN : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, N (σ i) i
  have hdetM : M.det = ∑ σ : Equiv.Perm n, termM σ := by
    dsimp [termM]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hdetN : N.det = ∑ σ : Equiv.Perm n, termN σ := by
    dsimp [termN]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ‖termM σ - termN σ‖ ≤
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) := by
    intro σ _hσ
    have hprod :
        ‖(∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i‖ ≤
          (∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1) := by
      simpa using
        (norm_finset_prod_sub_prod_le_sum_norm_sub_mul_unit_prod_max
          (A := A) (S := (Finset.univ : Finset n))
          (C := fun i => C (σ i) i)
          (a := fun i => M (σ i) i)
          (b := fun i => N (σ i) i)
          (fun i _hi => hM (σ i) i)
          (fun i _hi => hN (σ i) i))
    have hsub :
        termM σ - termN σ =
          (Equiv.Perm.sign σ : ℤ) • ((∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i) := by
      dsimp [termM, termN]
      rw [← zsmul_eq_mul, ← zsmul_eq_mul, zsmul_sub]
    calc
      ‖termM σ - termN σ‖ =
          ‖(Equiv.Perm.sign σ : ℤ) • ((∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i)‖ := by
        rw [hsub]
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ *
            ‖(∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i‖ :=
        norm_zsmul_le _ _
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  calc
    ‖M.det - N.det‖ =
        ‖(∑ σ : Equiv.Perm n, termM σ) - ∑ σ : Equiv.Perm n, termN σ‖ := by
      rw [hdetM, hdetN]
    _ = ‖∑ σ : Equiv.Perm n, (termM σ - termN σ)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ σ : Equiv.Perm n, ‖termM σ - termN σ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) :=
      Finset.sum_le_sum hterm

/-- The determinant of a finite matrix whose entries are parabolic `C^{0,α}` functions is
again parabolic `C^{0,α}`. -/
theorem matrix_det {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).det) s := by
  classical
  let term : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaOn α (term σ) s := by
    intro σ _hσ
    have hprod : ParabolicC0AlphaOn α (fun z => ∏ i : n, M z (σ i) i) s := by
      simpa using
        (ParabolicC0AlphaOn.finset_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (u := fun i z => M z (σ i) i)
          (fun i _hi => hM (σ i) i))
    dsimp [term]
    simpa [zsmul_eq_mul] using hprod.zsmul (Equiv.Perm.sign σ : ℤ)
  have hsum :
      ParabolicC0AlphaOn α
        (fun z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)), term σ z) s :=
    ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset (Equiv.Perm n))) hterm
  convert hsum using 1
  funext z
  dsimp [term]
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [← zsmul_eq_mul]
  rfl

/-- On a compact time-space set, a finite matrix with parabolic `C^{0,α}` entries and nonvanishing
determinant has determinant norm uniformly bounded away from zero. -/
theorem matrix_det_exists_pos_norm_lower_bound_of_isCompact {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M z).det‖ :=
  exists_pos_norm_lower_bound_of_isCompact_of_continuousOn_ne_zero hK
    ((matrix_det (M := M) hM).continuousOn hα) hdet_ne

/-- Entrywise parabolic `C^{0,α}` control packages a finite vector-valued coefficient family. -/
theorem vector_of_entries {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {v : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s) :
    ParabolicC0AlphaOn α v s :=
  ParabolicC0AlphaOn.pi hv

/-- Entrywise parabolic `C^{0,α}` control packages a finite matrix-valued coefficient family. -/
theorem matrix_of_entries {m n A : Type*} [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {M : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α M s :=
  ParabolicC0AlphaOn.pi fun i => ParabolicC0AlphaOn.pi fun j => hM i j

/-- Transposes of finite matrix-valued parabolic `C^{0,α}` functions are parabolic `C^{0,α}`
from entrywise control. -/
theorem matrix_transpose {m n A : Type*} [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {M : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).transpose) s :=
  matrix_of_entries fun i j => hM j i

/-- Finite matrix symmetrization preserves parabolic `C^{0,α}` control from entrywise control. -/
theorem matrix_symmetrize {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (2 : 𝕜)⁻¹ • (M z + (M z).transpose)) s :=
  ((matrix_of_entries hM).add (matrix_transpose hM)).smul ((2 : 𝕜)⁻¹)

/-- The finite matrix symmetrization is pointwise symmetric. -/
theorem matrix_symmetrize_isSymm {n 𝕜 : Type*} [NormedField 𝕜] (M : Matrix n n 𝕜) :
    ((2 : 𝕜)⁻¹ • (M + M.transpose)).IsSymm :=
  (Matrix.isSymm_add_transpose_self M).smul ((2 : 𝕜)⁻¹)

/-- Entrywise sup constants for replacing row `j` by the `i`th coordinate vector. -/
def matrixUpdateRowBoundConst {n A : Type*} [DecidableEq n] [NormedRing A]
    (B : n → n → ℝ) (i j : n) : n → n → ℝ :=
  fun r c => if r = j then ‖((Pi.single i (1 : A)) : n → A) c‖ else B r c

/-- Entrywise Holder constants for replacing row `j` by the constant `i`th coordinate vector. -/
def matrixUpdateRowHolderConst {n : Type*} [DecidableEq n]
    (H : n → n → ℝ) (j : n) : n → n → ℝ :=
  fun r c => if r = j then 0 else H r c

theorem matrixUpdateRowHolderConst_nonneg {n : Type*} [DecidableEq n]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (j : n) :
    ∀ r c, 0 ≤ matrixUpdateRowHolderConst H j r c := by
  intro r c
  by_cases hr : r = j
  · simp [matrixUpdateRowHolderConst, hr]
  · simpa [matrixUpdateRowHolderConst, hr] using hH r c

/-- The quantitative sup constant used for an adjugate entry. -/
def matrixAdjugateEntryBoundConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetBoundConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)

/-- The quantitative Holder constant used for an adjugate entry. -/
def matrixAdjugateEntryHolderConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B H : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetHolderConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)
    (matrixUpdateRowHolderConst H j)

theorem matrixAdjugateEntryBoundConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) (i j : n) :
    0 ≤ matrixAdjugateEntryBoundConst (A := A) B i j :=
  matrixDetBoundConst_nonneg (A := A) (matrixUpdateRowBoundConst (A := A) B i j)

theorem matrixAdjugateEntryHolderConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (i j : n) :
    0 ≤ matrixAdjugateEntryHolderConst (A := A) B H i j :=
  matrixDetHolderConst_nonneg (A := A)
    (matrixUpdateRowHolderConst_nonneg hH j)

/-- Each adjugate entry has an explicit bounded parabolic `C^{0,α}` estimate when the matrix
entries do. -/
theorem matrix_adjugate_entry_with {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {B H : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixAdjugateEntryBoundConst (A := A) B i j)
      (matrixAdjugateEntryHolderConst (A := A) B H i j)
      α (fun z => (M z).adjugate i j) s := by
  have hHupd : ∀ r c, 0 ≤ matrixUpdateRowHolderConst H j r c := by
    intro r c
    by_cases hr : r = j
    · simp [matrixUpdateRowHolderConst, hr]
    · simpa [matrixUpdateRowHolderConst, hr] using hH r c
  have hMupd : ∀ r c,
      ParabolicC0AlphaWith
        (matrixUpdateRowBoundConst (A := A) B i j r c)
        (matrixUpdateRowHolderConst H j r c)
        α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow] using
        (ParabolicC0AlphaWith.const (s := s) (α := α)
          (((Pi.single i (1 : A)) : n → A) c) le_rfl le_rfl)
    · simpa [matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow,
        Function.update_of_ne hr, hr] using hM r c
  have hdet :
      ParabolicC0AlphaWith
        (matrixAdjugateEntryBoundConst (A := A) B i j)
        (matrixAdjugateEntryHolderConst (A := A) B H i j)
        α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)).det) s := by
    simpa [matrixAdjugateEntryBoundConst, matrixAdjugateEntryHolderConst] using
      (matrix_det_with
        (M := fun z => (M z).updateRow j ((Pi.single i (1 : A)) : n → A))
        (B := matrixUpdateRowBoundConst (A := A) B i j)
        (H := matrixUpdateRowHolderConst H j)
        hHupd hMupd)
  convert hdet using 1
  funext z
  rw [Matrix.adjugate_apply]

/-- Each adjugate entry of a finite matrix is parabolic `C^{0,α}` when the matrix entries are. -/
theorem matrix_adjugate_entry {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z).adjugate i j) s := by
  have hdet :
      ParabolicC0AlphaOn α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)).det) s := by
    exact matrix_det (M := fun z => (M z).updateRow j ((Pi.single i (1 : A)) : n → A))
      (fun r c => by
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (ParabolicC0AlphaOn.const (α := α) (s := s)
              (((Pi.single i (1 : A)) : n → A) c))
        · simpa [Matrix.updateRow, Function.update_of_ne hr] using hM r c)
  convert hdet using 1
  funext z
  rw [Matrix.adjugate_apply]

/-- Each inverse-matrix entry is parabolic `C^{0,α}` when the matrix entries are and the
determinant is uniformly bounded away from zero on the domain. -/
theorem matrix_inv_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ i j) s := by
  have hdet_inv : ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹) s :=
    (matrix_det (M := M) hM).inv hδpos hdet
  have hadj : ParabolicC0AlphaOn α (fun z => (M z).adjugate i j) s :=
    matrix_adjugate_entry (M := M) hM i j
  have hprod := hdet_inv.mul hadj
  convert hprod using 1
  funext z
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- The quantitative sup constant used for an inverse-matrix entry. -/
def matrixInvEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryBoundConst (A := 𝕜) B i j

/-- The quantitative Holder constant used for an inverse-matrix entry. -/
def matrixInvEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B H : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryHolderConst (A := 𝕜) B H i j +
    matrixAdjugateEntryBoundConst (A := 𝕜) B i j *
      (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)

theorem matrixInvEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (B : n → n → ℝ) (i j : n) :
    0 ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j := by
  exact mul_nonneg (inv_nonneg.mpr hδpos.le)
    (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j)

theorem matrixInvEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ) (i j : n) :
    0 ≤ matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j := by
  exact add_nonneg
    (mul_nonneg (inv_nonneg.mpr hδpos.le)
      (matrixAdjugateEntryHolderConst_nonneg (A := 𝕜) hH i j))
    (mul_nonneg (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j)
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδpos.le) (matrixDetHolderConst_nonneg (A := 𝕜) hH))
        (inv_nonneg.mpr hδpos.le)))

/-- Each inverse-matrix entry has an explicit bounded parabolic `C^{0,α}` estimate when the matrix
entries do and the determinant is uniformly bounded away from zero on the domain. -/
theorem matrix_inv_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {B H : n → n → ℝ} {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j)
      (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j)
      α (fun z => (M z)⁻¹ i j) s := by
  have hdet_with :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := 𝕜) B) (matrixDetHolderConst (A := 𝕜) B H)
        α (fun z => (M z).det) s :=
    matrix_det_with (M := M) hH hM
  have hdet_inv :
      ParabolicC0AlphaWith δ⁻¹
        (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)
        α (fun z => ((M z).det)⁻¹) s :=
    hdet_with.inv hδpos hdet
  have hadj :
    ParabolicC0AlphaWith
      (matrixAdjugateEntryBoundConst (A := 𝕜) B i j)
      (matrixAdjugateEntryHolderConst (A := 𝕜) B H i j)
      α (fun z => (M z).adjugate i j) s :=
    matrix_adjugate_entry_with (M := M) hH hM i j
  have hprod := hdet_inv.mul hadj (inv_nonneg.mpr hδpos.le)
  convert hprod using 1
  funext z
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- A finite inverse-matrix-valued function has an explicit bounded parabolic `C^{0,α}` estimate
when the matrix entries do and the determinant is uniformly bounded away from zero. -/
theorem matrix_inv_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {B H : n → n → ℝ} {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j)
      (∑ i : n, ∑ j : n, matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j)
      α (fun z => (M z)⁻¹) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i j
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i j
    · intro j
      exact matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j
    · intro j
      exact matrix_inv_entry_with (M := M) hH hM hδpos hdet i j

/-- On a compact time-space set, inverse-matrix entries preserve parabolic `C^{0,α}` control from
entrywise control and pointwise nonvanishing determinant. -/
theorem matrix_inv_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ i j) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_entry (M := M) hM hδpos hdet i j

/-- A finite inverse-matrix-valued function is parabolic `C^{0,α}` when the matrix entries are and
the determinant is uniformly bounded away from zero. -/
theorem matrix_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹) s :=
  matrix_of_entries fun i j => matrix_inv_entry (M := M) hM hδpos hdet i j

/-- Compact-domain inverse-matrix-valued closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹) K :=
  matrix_of_entries fun i j =>
    matrix_inv_entry_of_isCompact_det_ne_zero hK hα hM hdet_ne i j

/-- Entries of a product of two matrix-valued parabolic `C^{0,α}` functions are
parabolic `C^{0,α}` when all input entries are. -/
theorem matrix_mul_entry {l m n A : Type*} [Fintype m] [NormedRing A]
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s) (i : l) (j : n) :
    ParabolicC0AlphaOn α (fun z => (M z * N z) i j) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ k : m, M z i k * N z k j) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset m))
        (u := fun k z => M z i k * N z k j)
        (fun k _hk => (hM i k).mul (hN k j)))
  simpa [Matrix.mul_apply] using hsum

/-- Products of finite matrix-valued parabolic `C^{0,α}` functions are parabolic `C^{0,α}` from
entrywise control. -/
theorem matrix_mul {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s) :
    ParabolicC0AlphaOn α (fun z => M z * N z) s :=
  matrix_of_entries fun i j => matrix_mul_entry hM hN i j

/-- Entries of a matrix-vector product are parabolic `C^{0,α}` when the matrix entries and
vector components are. -/
theorem matrix_mulVec_entry {m n A : Type*} [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s) (i : m) :
    ParabolicC0AlphaOn α (fun z => (M z).mulVec (v z) i) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ j : n, M z i j * v z j) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun j z => M z i j * v z j)
        (fun j _hj => (hM i j).mul (hv j)))
  simpa [Matrix.mulVec] using hsum

/-- Matrix-vector products preserve parabolic `C^{0,α}` control from entrywise matrix control and
componentwise vector control. -/
theorem matrix_mulVec {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).mulVec (v z)) s :=
  vector_of_entries fun i => matrix_mulVec_entry hM hv i

/-- Entries of a vector-matrix product are parabolic `C^{0,α}` when the vector components and
matrix entries are. -/
theorem matrix_vecMul_entry {m n A : Type*} [Fintype m] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z) j) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ i : m, v z i * M z i j) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset m))
        (u := fun i z => v z i * M z i j)
        (fun i _hi => (hv i).mul (hM i j)))
  simpa [Matrix.vecMul] using hsum

/-- Vector-matrix products preserve parabolic `C^{0,α}` control from componentwise vector control
and entrywise matrix control. -/
theorem matrix_vecMul {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)) s :=
  vector_of_entries fun j => matrix_vecMul_entry hv hM j

/-- Entries of an inverse-matrix-vector product are parabolic `C^{0,α}` when the matrix entries
and vector components are, and the determinant is uniformly bounded away from zero. -/
theorem matrix_inv_mulVec_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : n) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z) i) s :=
  matrix_mulVec_entry
    (M := fun z => (M z)⁻¹) (v := v)
    (fun r c => matrix_inv_entry (M := M) hM hδpos hdet r c) hv i

/-- Inverse-matrix-vector products preserve parabolic `C^{0,α}` control when the determinant is
uniformly bounded away from zero. -/
theorem matrix_inv_mulVec {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z)) s :=
  vector_of_entries fun i => matrix_inv_mulVec_entry hM hv hδpos hdet i

/-- Compact-domain inverse-matrix-vector entry closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_mulVec_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i : n) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z) i) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_mulVec_entry hM hv hδpos hdet i

/-- Compact-domain inverse-matrix-vector closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_mulVec_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_mulVec hM hv hδpos hdet

/-- Entries of a vector-inverse-matrix product are parabolic `C^{0,α}` when the matrix entries
and vector components are, and the determinant is uniformly bounded away from zero. -/
theorem matrix_vecMul_inv_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹ j) s :=
  matrix_vecMul_entry
    (v := v) (M := fun z => (M z)⁻¹)
    hv (fun r c => matrix_inv_entry (M := M) hM hδpos hdet r c) j

/-- Vector-inverse-matrix products preserve parabolic `C^{0,α}` control when the determinant is
uniformly bounded away from zero. -/
theorem matrix_vecMul_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹) s :=
  vector_of_entries fun j => matrix_vecMul_inv_entry hv hM hδpos hdet j

/-- Compact-domain vector-inverse-matrix entry closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_vecMul_inv_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹ j) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_vecMul_inv_entry hv hM hδpos hdet j

/-- Compact-domain vector-inverse-matrix closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_vecMul_inv_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_vecMul_inv hv hM hδpos hdet

/-- Finite dot products of vector-valued parabolic `C^{0,α}` functions are parabolic
`C^{0,α}`. -/
theorem vector_dot_entry {n A : Type*} [Fintype n] [NormedRing A]
    {v w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hw : ∀ i, ParabolicC0AlphaOn α (fun z => w z i) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * w z i) s := by
  simpa using
    (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun i z => v z i * w z i)
      (fun i _hi => (hv i).mul (hw i)))

/-- Finite bilinear matrix contractions `v · (M w)` preserve parabolic `C^{0,α}` control from
entrywise control. -/
theorem matrix_bilinear_entry {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A} {w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i : m, v z i * (M z).mulVec (w z) i) s :=
  vector_dot_entry hv (fun i => matrix_mulVec_entry hM hw i)

/-- Finite bilinear contractions through an inverse matrix `v · (M⁻¹ w)` preserve parabolic
`C^{0,α}` control when the matrix determinant is uniformly bounded away from zero. -/
theorem matrix_inv_bilinear_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) s :=
  vector_dot_entry hv (fun i => matrix_inv_mulVec_entry hM hw hδpos hdet i)

/-- Compact-domain bilinear contraction through an inverse matrix, from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_inv_bilinear_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_bilinear_entry hv hM hw hδpos hdet

/-- Christoffel-symbol type inverse-metric contractions preserve parabolic `C^{0,α}` control:
if `M` and the three-index derivative array `D` are controlled entrywise and `det M` is bounded
away from zero, then each finite contraction
`(1 / 2) * M⁻¹ᵢˡ (Dⱼₖₗ + Dₖⱼₗ - Dₗⱼₖ)` is controlled. -/
theorem matrix_inv_christoffel_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j k : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  have hvec : ∀ l : n,
      ParabolicC0AlphaOn α (fun z => D z j k l + D z k j l - D z l j k) s := by
    intro l
    exact ((hD j k l).add (hD k j l)).sub (hD l j k)
  have hcontraction :
      ParabolicC0AlphaOn α
        (fun z =>
          ((M z)⁻¹).mulVec (fun l : n => D z j k l + D z k j l - D z l j k) i) s :=
    matrix_inv_mulVec_entry hM hvec hδpos hdet i
  have hhalf :
      ParabolicC0AlphaOn α
        (fun z =>
          (2 : 𝕜)⁻¹ *
            ((M z)⁻¹).mulVec (fun l : n => D z j k l + D z k j l - D z l j k) i) s :=
    (ParabolicC0AlphaOn.const (α := α) (s := s) ((2 : 𝕜)⁻¹)).mul hcontraction
  simpa [Matrix.mulVec] using hhalf

/-- The full finite Christoffel-symbol type array preserves parabolic `C^{0,α}` control from
entrywise metric and derivative control, under a determinant lower bound. -/
theorem matrix_inv_christoffel {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  refine ParabolicC0AlphaOn.pi ?_
  intro i
  refine ParabolicC0AlphaOn.pi ?_
  intro j
  refine ParabolicC0AlphaOn.pi ?_
  intro k
  exact matrix_inv_christoffel_entry (M := M) (D := D) hM hD hδpos hdet i j k

/-- Compact-domain Christoffel-symbol type array closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_christoffel_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_christoffel (M := M) (D := D) hM hD hδpos hdet

/-- Finite inverse-matrix contractions against a four-index coefficient array preserve parabolic
`C^{0,α}` control. This is the coordinate-algebra pattern for terms such as
`g^{ab} H_{abij}` in a local Ricci-DeTurck principal part. -/
theorem matrix_inv_two_index_contract_entry {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {T : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : p) (j : q) :
    ParabolicC0AlphaOn α
      (fun z => ∑ a : n, ∑ b : n,
        ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) s := by
  have hinner : ∀ a : n,
      ParabolicC0AlphaOn α
        (fun z => ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j)
        (fun b _hb => (matrix_inv_entry (M := M) hM hδpos hdet a b).mul (hT a b i j)))
  simpa using
    (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun a z => ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j)
      (fun a _ha => hinner a))

/-- Finite inverse-matrix contractions against a four-index coefficient array package as a
matrix-valued parabolic `C^{0,α}` function. -/
theorem matrix_inv_two_index_contract {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [Fintype q] [NormedField 𝕜] {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {T : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) s :=
  matrix_of_entries fun i j => matrix_inv_two_index_contract_entry hM hT hδpos hdet i j

/-- Compact-domain matrix-valued inverse principal-contraction closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_inv_two_index_contract_of_isCompact_det_ne_zero {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {T : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_two_index_contract (M := M) (T := T) hM hT hδpos hdet

/-- Ricci-coordinate quadratic Christoffel contractions preserve parabolic `C^{0,α}` control
from entrywise control of the Christoffel array. -/
theorem christoffel_quadratic_ricci_entry {n A : Type*} [Fintype n] [NormedRing A]
    {Γ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s) (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
          (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s := by
  have hleftInner : ∀ a : n,
      ParabolicC0AlphaOn α (fun z => ∑ b : n, Γ z a i j * Γ z b a b) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => Γ z a i j * Γ z b a b)
        (fun b _hb => (hΓ a i j).mul (hΓ b a b)))
  have hleft :
      ParabolicC0AlphaOn α (fun z => ∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun a z => ∑ b : n, Γ z a i j * Γ z b a b)
        (fun a _ha => hleftInner a))
  have hrightInner : ∀ a : n,
      ParabolicC0AlphaOn α (fun z => ∑ b : n, Γ z a i b * Γ z b a j) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => Γ z a i b * Γ z b a j)
        (fun b _hb => (hΓ a i b).mul (hΓ b a j)))
  have hright :
      ParabolicC0AlphaOn α (fun z => ∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun a z => ∑ b : n, Γ z a i b * Γ z b a j)
        (fun a _ha => hrightInner a))
  exact hleft.sub hright

/-- The full finite Ricci-coordinate quadratic Christoffel contraction packages as a
matrix-valued parabolic `C^{0,α}` function. -/
theorem christoffel_quadratic_ricci {n A : Type*} [Fintype n] [NormedRing A]
    {Γ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) :
            Matrix n n A)) s :=
  matrix_of_entries fun i j => christoffel_quadratic_ricci_entry hΓ i j

/-- Schematic local Ricci-DeTurck coordinate right-hand sides preserve parabolic `C^{0,α}`
control from entrywise control of metric coefficients, first derivative coefficients, and second
derivative coefficients, assuming the metric determinant is bounded away from zero.  The formula
packages the principal contraction `g^{ab} H_{abij}` together with the standard quadratic
Christoffel contraction. -/
theorem ricciDeTurck_schematic_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
              (D z b c l + D z c b l - D z l b c)
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) s := by
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  have hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s := by
    intro a b c
    exact matrix_inv_christoffel_entry (M := M) (D := D) hM hD hδpos hdet a b c
  have hprincipal :
      ParabolicC0AlphaOn α
        (fun z => ∑ a : n, ∑ b : n,
          ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) s :=
    matrix_inv_two_index_contract_entry hM hH hδpos hdet i j
  have hquadratic :
      ParabolicC0AlphaOn α
        (fun z =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s :=
    christoffel_quadratic_ricci_entry hΓ i j
  simpa [Γ] using hprincipal.add hquadratic

/-- Schematic local Ricci-DeTurck coordinate right-hand sides package as a matrix-valued
parabolic `C^{0,α}` function from entrywise control, under a determinant lower bound. -/
theorem ricciDeTurck_schematic {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) s :=
  matrix_of_entries fun i j =>
    ricciDeTurck_schematic_entry (M := M) (D := D) (H := H)
      hM hD hH hδpos hdet i j

/-- Compact-domain version of `ricciDeTurck_schematic_entry`: pointwise nonvanishing of the
metric determinant supplies the determinant lower bound. -/
theorem ricciDeTurck_schematic_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
              (D z b c l + D z c b l - D z l b c)
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ricciDeTurck_schematic_entry (M := M) (D := D) (H := H)
    hM hD hH hδpos hdet i j

/-- Compact-domain matrix-valued schematic Ricci-DeTurck RHS closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem ricciDeTurck_schematic_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ricciDeTurck_schematic (M := M) (D := D) (H := H)
    hM hD hH hδpos hdet

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
