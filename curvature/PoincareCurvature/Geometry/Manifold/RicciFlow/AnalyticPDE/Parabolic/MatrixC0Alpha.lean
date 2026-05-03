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

/-- Elementwise matrix-norm Lipschitz constant for the determinant on an entrywise bounded set. -/
def matrixDetLipschitzConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    (C : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n,
    ‖(Equiv.Perm.sign σ : ℤ)‖ *
      ((Fintype.card n : ℝ) *
        (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1))

theorem matrixDetLipschitzConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) :
    0 ≤ matrixDetLipschitzConst (A := A) C := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (zero_le_one.trans (le_max_right _ _))
          (Finset.prod_nonneg fun i _hi =>
            zero_le_one.trans (le_max_right (C (σ i) i) 1))))

/-- Determinants are Lipschitz in the elementwise matrix norm on entrywise bounded finite
matrices. -/
theorem matrix_det_norm_sub_le_const_mul {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) (hN : ∀ i j, ‖N i j‖ ≤ C i j) :
    ‖M.det - N.det‖ ≤ matrixDetLipschitzConst (A := A) C * ‖M - N‖ := by
  classical
  have hbase := matrix_det_norm_sub_le (C := C) M N hM hN
  have hsum : ∀ σ : Equiv.Perm n,
      (∑ i : n, ‖M (σ i) i - N (σ i) i‖) ≤
        (Fintype.card n : ℝ) * ‖M - N‖ := by
    intro σ
    calc
      (∑ i : n, ‖M (σ i) i - N (σ i) i‖) ≤ ∑ _i : n, ‖M - N‖ := by
        exact Finset.sum_le_sum fun i _hi => by
          simpa using Matrix.norm_entry_le_entrywise_sup_norm (M - N) (i := σ i) (j := i)
      _ = (Fintype.card n : ℝ) * ‖M - N‖ := by
        simp
  refine hbase.trans ?_
  calc
    (∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)))
        ≤
      ∑ σ : Equiv.Perm n,
        (‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((Fintype.card n : ℝ) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1))) * ‖M - N‖ := by
      refine Finset.sum_le_sum fun σ _hσ => ?_
      let Lσ : ℝ := max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1
      have hLσ_nonneg : 0 ≤ Lσ := by
        exact mul_nonneg (zero_le_one.trans (le_max_right _ _))
          (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (C (σ i) i) 1))
      calc
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
            ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) * Lσ) ≤
          ‖(Equiv.Perm.sign σ : ℤ)‖ *
            (((Fintype.card n : ℝ) * ‖M - N‖) * Lσ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hsum σ) hLσ_nonneg) (norm_nonneg _)
        _ =
          (‖(Equiv.Perm.sign σ : ℤ)‖ *
            ((Fintype.card n : ℝ) * Lσ)) * ‖M - N‖ := by
          ring
    _ = matrixDetLipschitzConst (A := A) C * ‖M - N‖ := by
      simp [matrixDetLipschitzConst, Finset.sum_mul, mul_assoc]

/-- Determinants are pointwise bounded by the quantitative finite product constant. -/
theorem matrix_det_norm_le {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {C : n → n → ℝ} (M : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) :
    ‖M.det‖ ≤ matrixDetBoundConst (A := A) C := by
  classical
  let term : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M (σ i) i
  have hdet : M.det = ∑ σ : Equiv.Perm n, term σ := by
    dsimp [term]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ‖term σ‖ ≤
        ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ := by
    intro σ _hσ
    have hprod :
        ‖∏ i : n, M (σ i) i‖ ≤ matrixDetTermBoundConst (A := A) C σ := by
      simpa [matrixDetTermBoundConst] using
        (norm_finset_prod_le_unit_mul_prod_max
          (A := A) (S := (Finset.univ : Finset n))
          (C := fun i => C (σ i) i)
          (a := fun i => M (σ i) i)
          (fun i _hi => hM (σ i) i))
    have hterm_zsmul :
        term σ = (Equiv.Perm.sign σ : ℤ) • (∏ i : n, M (σ i) i) := by
      dsimp [term]
      rw [← zsmul_eq_mul]
    calc
      ‖term σ‖ = ‖(Equiv.Perm.sign σ : ℤ) • (∏ i : n, M (σ i) i)‖ := by
        rw [hterm_zsmul]
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ * ‖∏ i : n, M (σ i) i‖ :=
        norm_zsmul_le _ _
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  calc
    ‖M.det‖ = ‖∑ σ : Equiv.Perm n, term σ‖ := by rw [hdet]
    _ ≤ ∑ σ : Equiv.Perm n, ‖term σ‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ :=
      Finset.sum_le_sum hterm
    _ = matrixDetBoundConst (A := A) C := by
      rfl

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

/-- Adjugate entries are pointwise Lipschitz on entrywise bounded finite matrices.  The estimate
is obtained by applying the determinant Lipschitz bound to the row-replacement matrices defining
the adjugate entry. -/
theorem matrix_adjugate_entry_norm_sub_le {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (i j : n) :
    ‖M.adjugate i j - N.adjugate i j‖ ≤
      ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ r : n,
              ‖(M.updateRow j ((Pi.single i (1 : A)) : n → A)) (σ r) r -
                (N.updateRow j ((Pi.single i (1 : A)) : n → A)) (σ r) r‖) *
            (max ‖(1 : A)‖ 1 *
              ∏ r : n, max (matrixUpdateRowBoundConst (A := A) C i j (σ r) r) 1)) := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow, Function.update_of_ne hr, hr]
        using hM r c
  have hNupd : ∀ r c, ‖(N.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow, Function.update_of_ne hr, hr]
        using hN r c
  simpa [e, Matrix.adjugate_apply] using
    (matrix_det_norm_sub_le
      (C := matrixUpdateRowBoundConst (A := A) C i j)
      (M.updateRow j e) (N.updateRow j e) hMupd hNupd)

/-- Elementwise matrix-norm Lipschitz constant for one adjugate entry on an entrywise bounded
set. -/
def matrixAdjugateEntryLipschitzConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetLipschitzConst (A := A) (matrixUpdateRowBoundConst (A := A) C i j)

theorem matrixAdjugateEntryLipschitzConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) (i j : n) :
    0 ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j :=
  matrixDetLipschitzConst_nonneg (A := A) (matrixUpdateRowBoundConst (A := A) C i j)

/-- Adjugate entries are Lipschitz in the elementwise matrix norm on entrywise bounded finite
matrices. -/
theorem matrix_adjugate_entry_norm_sub_le_const_mul {n A : Type*} [Fintype n]
    [DecidableEq n] [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (i j : n) :
    ‖M.adjugate i j - N.adjugate i j‖ ≤
      matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M - N‖ := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow, Function.update_of_ne hr, hr]
        using hM r c
  have hNupd : ∀ r c, ‖(N.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow, Function.update_of_ne hr, hr]
        using hN r c
  have hupd_norm :
      ‖M.updateRow j e - N.updateRow j e‖ ≤ ‖M - N‖ := by
    refine (Matrix.norm_le_iff (norm_nonneg _)).2 ?_
    intro r c
    by_cases hr : r = j
    · subst r
      simp [Matrix.updateRow]
    · simpa [Matrix.updateRow, Function.update_of_ne hr] using
        Matrix.norm_entry_le_entrywise_sup_norm (M - N) (i := r) (j := c)
  have hdet :
      ‖(M.updateRow j e).det - (N.updateRow j e).det‖ ≤
        matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M.updateRow j e - N.updateRow j e‖ := by
    simpa [matrixAdjugateEntryLipschitzConst] using
      matrix_det_norm_sub_le_const_mul
        (C := matrixUpdateRowBoundConst (A := A) C i j)
        (M.updateRow j e) (N.updateRow j e) hMupd hNupd
  calc
    ‖M.adjugate i j - N.adjugate i j‖ =
        ‖(M.updateRow j e).det - (N.updateRow j e).det‖ := by
      simp [e, Matrix.adjugate_apply]
    _ ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j *
        ‖M.updateRow j e - N.updateRow j e‖ := hdet
    _ ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M - N‖ :=
      mul_le_mul_of_nonneg_left hupd_norm
        (matrixAdjugateEntryLipschitzConst_nonneg (A := A) C i j)

/-- Adjugate entries are pointwise bounded by the quantitative adjugate-entry constant. -/
theorem matrix_adjugate_entry_norm_le {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (i j : n) :
    ‖M.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := A) C i j := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow, Function.update_of_ne hr, hr]
        using hM r c
  simpa [e, Matrix.adjugate_apply, matrixAdjugateEntryBoundConst] using
    (matrix_det_norm_le
      (C := matrixUpdateRowBoundConst (A := A) C i j)
      (M.updateRow j e) hMupd)

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

/-- Pointwise finite-dimensional Lipschitz bound for one inverse-matrix entry.  It depends on
the two matrices through the determinant and row-replacement adjugate differences. -/
def matrixInvEntryLipschitzBound {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (M N : Matrix n n 𝕜)
    (i j : n) : ℝ :=
  δ⁻¹ *
    (∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n,
            ‖(M.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r -
              (N.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 *
            ∏ r : n, max (matrixUpdateRowBoundConst (A := 𝕜) C i j (σ r) r) 1))) +
    ((δ⁻¹ * δ⁻¹) *
      (∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ r : n, ‖M (σ r) r - N (σ r) r‖) *
            (max ‖(1 : 𝕜)‖ 1 * ∏ r : n, max (C (σ r) r) 1)))) *
      matrixAdjugateEntryBoundConst (A := 𝕜) C i j

/-- Inverse-matrix entries are pointwise Lipschitz on entrywise bounded matrices whose
determinants have a common positive lower bound.  The estimate separates the adjugate variation
from the reciprocal determinant variation. -/
theorem matrix_inv_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖M⁻¹ i j - N⁻¹ i j‖ ≤
      matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
  classical
  let adjRhs : ℝ :=
    ∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n,
            ‖(M.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r -
              (N.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 *
            ∏ r : n, max (matrixUpdateRowBoundConst (A := 𝕜) C i j (σ r) r) 1))
  let detRhs : ℝ :=
    ∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n, ‖M (σ r) r - N (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 * ∏ r : n, max (C (σ r) r) 1))
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hdet_lip : ‖M.det - N.det‖ ≤ detRhs := by
    simpa [detRhs] using matrix_det_norm_sub_le (C := C) M N hM hN
  have hadj_lip : ‖M.adjugate i j - N.adjugate i j‖ ≤ adjRhs := by
    simpa [adjRhs] using matrix_adjugate_entry_norm_sub_le (C := C) M N hM hN i j
  have hdetRhs_nonneg : 0 ≤ detRhs := (norm_nonneg _).trans hdet_lip
  have hadjRhs_nonneg : 0 ≤ adjRhs := (norm_nonneg _).trans hadj_lip
  have hadj_boundN :
      ‖N.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) N hN i j
  have hinv_detM : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdetM
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdetM
  have hdet_inv_lip :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * ‖M.det - N.det‖ := by
    have hdist := (lipschitzOnWith_inv_of_norm_ge (𝕜 := 𝕜) hδpos).dist_le_mul
      M.det (show M.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetM)
      N.det (show N.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetN)
    simpa [dist_eq_norm, mul_assoc] using hdist
  have hdet_inv_Rhs :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * detRhs :=
    hdet_inv_lip.trans
      (mul_le_mul_of_nonneg_left hdet_lip (mul_nonneg hinvδ_nonneg hinvδ_nonneg))
  have hfirst :
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤ δ⁻¹ * adjRhs :=
    mul_le_mul hinv_detM hadj_lip (norm_nonneg _) hinvδ_nonneg
  have hsecond :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
        ((δ⁻¹ * δ⁻¹) * detRhs) *
          matrixAdjugateEntryBoundConst (A := 𝕜) C i j := by
    exact mul_le_mul hdet_inv_Rhs hadj_boundN (norm_nonneg _)
      (mul_nonneg (mul_nonneg hinvδ_nonneg hinvδ_nonneg) hdetRhs_nonneg)
  have hentry :
      M⁻¹ i j - N⁻¹ i j =
        (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j := by
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    rfl
  have hsplit :
      (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j =
        (M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j := by
    ring
  calc
    ‖M⁻¹ i j - N⁻¹ i j‖ =
        ‖(M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j‖ := by
      rw [hentry]
    _ =
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ := by
      rw [hsplit]
    _ ≤
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j)‖ +
          ‖((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ :=
      norm_add_le _ _
    _ ≤
        ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ +
          (‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤
        δ⁻¹ * adjRhs +
          ((δ⁻¹ * δ⁻¹) * detRhs) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
      add_le_add hfirst hsecond
    _ = matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
      simp [adjRhs, detRhs, matrixInvEntryLipschitzBound]

theorem matrixInvEntryLipschitzBound_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    0 ≤ matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j :=
  (norm_nonneg _).trans (matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i j)

/-- Elementwise matrix-norm Lipschitz constant for one inverse-matrix entry on an entrywise
bounded set with a determinant lower bound. -/
def matrixInvEntryMatrixNormLipschitzConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j +
    ((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
      matrixAdjugateEntryBoundConst (A := 𝕜) C i j

theorem matrixInvEntryMatrixNormLipschitzConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ)
    (C : n → n → ℝ) (i j : n) :
    0 ≤ matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j := by
  exact add_nonneg
    (mul_nonneg (inv_nonneg.mpr hδpos.le)
      (matrixAdjugateEntryLipschitzConst_nonneg (A := 𝕜) C i j))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδpos.le) (inv_nonneg.mpr hδpos.le))
        (matrixDetLipschitzConst_nonneg (A := 𝕜) C))
      (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) C i j))

/-- Inverse-matrix entries are Lipschitz in the elementwise matrix norm on entrywise bounded
matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_entry_norm_sub_le_const_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖M⁻¹ i j - N⁻¹ i j‖ ≤
      matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j * ‖M - N‖ := by
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hadj_lip :
      ‖M.adjugate i j - N.adjugate i j‖ ≤
        matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j * ‖M - N‖ :=
    matrix_adjugate_entry_norm_sub_le_const_mul M N hM hN i j
  have hdet_lip :
      ‖M.det - N.det‖ ≤ matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖ :=
    matrix_det_norm_sub_le_const_mul M N hM hN
  have hadj_boundN :
      ‖N.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) N hN i j
  have hinv_detM : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdetM
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdetM
  have hdet_inv_lip :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * ‖M.det - N.det‖ := by
    have hdist := (lipschitzOnWith_inv_of_norm_ge (𝕜 := 𝕜) hδpos).dist_le_mul
      M.det (show M.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetM)
      N.det (show N.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetN)
    simpa [dist_eq_norm, mul_assoc] using hdist
  have hdet_inv_const :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤
        (δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖) :=
    hdet_inv_lip.trans
      (mul_le_mul_of_nonneg_left hdet_lip (mul_nonneg hinvδ_nonneg hinvδ_nonneg))
  have hfirst :
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤
        (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ := by
    calc
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤
          δ⁻¹ * (matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j * ‖M - N‖) :=
        mul_le_mul hinv_detM hadj_lip (norm_nonneg _) hinvδ_nonneg
      _ = (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ := by
        ring
  have hsecond :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
        (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
          matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ := by
    have hdet_rhs_nonneg :
        0 ≤ (δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖) := by
      exact mul_nonneg (mul_nonneg hinvδ_nonneg hinvδ_nonneg)
        (mul_nonneg (matrixDetLipschitzConst_nonneg (A := 𝕜) C) (norm_nonneg _))
    calc
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
          ((δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖)) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
        mul_le_mul hdet_inv_const hadj_boundN (norm_nonneg _) hdet_rhs_nonneg
      _ =
          (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ := by
        ring
  have hentry :
      M⁻¹ i j - N⁻¹ i j =
        (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j := by
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    rfl
  have hsplit :
      (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j =
        (M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j := by
    ring
  calc
    ‖M⁻¹ i j - N⁻¹ i j‖ =
        ‖(M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j‖ := by
      rw [hentry]
    _ =
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ := by
      rw [hsplit]
    _ ≤
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j)‖ +
          ‖((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ :=
      norm_add_le _ _
    _ ≤
        ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ +
          (‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤
        (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ +
          (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ :=
      add_le_add hfirst hsecond
    _ =
        matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j * ‖M - N‖ := by
      simp [matrixInvEntryMatrixNormLipschitzConst]
      ring

/-- Elementwise matrix-norm Lipschitz constant for finite matrix inversion on an entrywise bounded
set with a determinant lower bound. -/
def matrixInvMatrixNormLipschitzConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j

theorem matrixInvMatrixNormLipschitzConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (C : n → n → ℝ) :
    0 ≤ matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C i j

/-- Finite matrix inversion is Lipschitz in the elementwise matrix norm on entrywise bounded
matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_norm_sub_le_const_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖M⁻¹ - N⁻¹‖ ≤ matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * ‖M - N‖ := by
  classical
  let entryConst : n → n → ℝ :=
    fun i j => matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j
  let entryBound : n → n → ℝ := fun i j => entryConst i j * ‖M - N‖
  have hentry : ∀ i j, ‖M⁻¹ i j - N⁻¹ i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound, entryConst] using
      matrix_inv_entry_norm_sub_le_const_mul M N hM hN hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact mul_nonneg
      (matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C i j)
      (norm_nonneg _)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm : ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M⁻¹ - N⁻¹) i j‖ = ‖M⁻¹ i j - N⁻¹ i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  calc
    ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := hnorm
    _ = matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * ‖M - N‖ := by
      simp [entryBound, entryConst, matrixInvMatrixNormLipschitzConst, Finset.sum_mul]

/-- Finite matrix inversion is pointwise Lipschitz in the elementwise matrix norm on entrywise
bounded matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖M⁻¹ - N⁻¹‖ ≤
      ∑ i : n, ∑ j : n, matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
  classical
  let entryBound : n → n → ℝ :=
    fun i j => matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j
  have hentry : ∀ i j, ‖M⁻¹ i j - N⁻¹ i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M⁻¹ - N⁻¹) i j‖ = ‖M⁻¹ i j - N⁻¹ i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- Inverse-matrix entries are pointwise bounded by the quantitative inverse-entry constant. -/
theorem matrix_inv_entry_norm_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j : n) :
    ‖M⁻¹ i j‖ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i j := by
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hadj_bound :
      ‖M.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) M hM i j
  have hinv_det : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdet
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdet
  have hentry :
      M⁻¹ i j = (M.det)⁻¹ * M.adjugate i j := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  calc
    ‖M⁻¹ i j‖ = ‖(M.det)⁻¹ * M.adjugate i j‖ := by rw [hentry]
    _ ≤ ‖(M.det)⁻¹‖ * ‖M.adjugate i j‖ := norm_mul_le _ _
    _ ≤ δ⁻¹ * matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
      mul_le_mul hinv_det hadj_bound (norm_nonneg _) hinvδ_nonneg
    _ = matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i j := by
      rfl

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

/-- Entries of finite matrix products are pointwise Lipschitz on bounded left/right factors. -/
theorem matrix_mul_entry_norm_sub_le {l m n A : Type*} [Fintype m] [NormedRing A]
    {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j)
    (i : l) (j : n) :
    ‖(M * N) i j - (M' * N') i j‖ ≤
      ∑ k : m, (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖) := by
  simpa [Matrix.mul_apply] using
    (norm_finset_sum_mul_sub_sum_mul_le
      (S := (Finset.univ : Finset m))
      (B := fun k => BM i k)
      (D := fun k => BN k j)
      (a := fun k => M i k)
      (b := fun k => N k j)
      (c := fun k => M' i k)
      (d := fun k => N' k j)
      (fun k _hk => hM i k)
      (fun k _hk => hN' k j))

/-- Finite matrix multiplication is pointwise Lipschitz in the elementwise matrix norm on bounded
left/right factors. -/
theorem matrix_mul_norm_sub_le {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j) :
    ‖M * N - M' * N'‖ ≤
      ∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖) := by
  classical
  let entryBound : l → n → ℝ :=
    fun i j => ∑ k : m,
      (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖)
  have hentry : ∀ i j, ‖(M * N) i j - (M' * N') i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using matrix_mul_entry_norm_sub_le M M' N N' hM hN' i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : l, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm : ‖M * N - M' * N'‖ ≤ ∑ i : l, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M * N - M' * N') i j‖ = ‖(M * N) i j - (M' * N') i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : l, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- Matrix-norm Lipschitz constant for varying the right factor of a matrix product, with the
left factor bounded entrywise by `BM`. -/
def matrixMulRightFactorLipschitzConst {l m n : Type*} [Fintype l] [Fintype m]
    [Fintype n] (BM : l → m → ℝ) : ℝ :=
  ∑ i : l, ∑ _j : n, ∑ k : m, BM i k

/-- Matrix-norm Lipschitz constant for varying the left factor of a matrix product, with the
right factor bounded entrywise by `BN`. -/
def matrixMulLeftFactorLipschitzConst {l m n : Type*} [Fintype l] [Fintype m]
    [Fintype n] (BN : m → n → ℝ) : ℝ :=
  ∑ _i : l, ∑ j : n, ∑ k : m, BN k j

theorem matrixMulRightFactorLipschitzConst_nonneg {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] {BM : l → m → ℝ} (hBM : ∀ i k, 0 ≤ BM i k) :
    0 ≤ matrixMulRightFactorLipschitzConst (n := n) BM := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun _j _hj =>
      Finset.sum_nonneg fun k _hk => hBM i k

theorem matrixMulLeftFactorLipschitzConst_nonneg {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] {BN : m → n → ℝ} (hBN : ∀ k j, 0 ≤ BN k j) :
    0 ≤ matrixMulLeftFactorLipschitzConst (l := l) BN := by
  exact Finset.sum_nonneg fun _i _hi =>
    Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk => hBN k j

/-- Finite matrix multiplication is Lipschitz in the elementwise matrix norm on bounded
left/right factors, with separate constants for the two factor differences. -/
theorem matrix_mul_norm_sub_le_const {l m n A : Type*} [Fintype l] [Fintype m]
    [Fintype n] [NormedRing A] {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j) :
    ‖M * N - M' * N'‖ ≤
      matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ +
        matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
  have hBM_nonneg : ∀ i k, 0 ≤ BM i k := by
    intro i k
    exact (norm_nonneg _).trans (hM i k)
  have hBN_nonneg : ∀ k j, 0 ≤ BN k j := by
    intro k j
    exact (norm_nonneg _).trans (hN' k j)
  have hbase := matrix_mul_norm_sub_le M M' N N' hM hN'
  refine hbase.trans ?_
  calc
    (∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖))
        ≤
      ∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N - N'‖ + BN k j * ‖M - M'‖) := by
      refine Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj =>
          Finset.sum_le_sum fun k _hk => ?_
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (by simpa using Matrix.norm_entry_le_entrywise_sup_norm (N - N') (i := k) (j := j))
          (hBM_nonneg i k))
        (mul_le_mul_of_nonneg_left
          (by simpa using Matrix.norm_entry_le_entrywise_sup_norm (M - M') (i := i) (j := k))
          (hBN_nonneg k j))
    _ =
      (∑ i : l, ∑ j : n, ∑ k : m, BM i k * ‖N - N'‖) +
        (∑ i : l, ∑ j : n, ∑ k : m, BN k j * ‖M - M'‖) := by
      simp [Finset.sum_add_distrib]
    _ =
      matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ +
        matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
      have hright :
          (∑ i : l, ∑ j : n, ∑ k : m, BM i k * ‖N - N'‖) =
            matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ := by
        simp_rw [matrixMulRightFactorLipschitzConst, Finset.sum_mul]
      have hleft :
          (∑ i : l, ∑ j : n, ∑ k : m, BN k j * ‖M - M'‖) =
            matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
        simp_rw [matrixMulLeftFactorLipschitzConst, Finset.sum_mul]
      rw [hright, hleft]

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

/-- The Christoffel derivative combination is Lipschitz in its three displayed derivative
entries. -/
theorem christoffelDerivativeCombo_norm_sub_le {n A : Type*} [NormedAddCommGroup A]
    (D E : n → n → n → A) (j k l : n) :
    ‖(D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k)‖ ≤
      ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖ := by
  have hsplit :
      (D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k) =
        (D j k l - E j k l) + (D k j l - E k j l) - (D l j k - E l j k) := by
    abel
  calc
    ‖(D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k)‖ =
        ‖(D j k l - E j k l) + (D k j l - E k j l) -
          (D l j k - E l j k)‖ := by
      rw [hsplit]
    _ ≤ ‖(D j k l - E j k l) + (D k j l - E k j l)‖ +
        ‖D l j k - E l j k‖ :=
      norm_sub_le _ _
    _ ≤ (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖) +
        ‖D l j k - E l j k‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ = ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
        ‖D l j k - E l j k‖ := by
      ring

/-- A bounded derivative array bounds the Christoffel derivative combination. -/
theorem christoffelDerivativeCombo_norm_le {n A : Type*} [NormedAddCommGroup A]
    {B : n → n → n → ℝ} (D : n → n → n → A)
    (hD : ∀ a b c, ‖D a b c‖ ≤ B a b c) (j k l : n) :
    ‖D j k l + D k j l - D l j k‖ ≤ B j k l + B k j l + B l j k := by
  calc
    ‖D j k l + D k j l - D l j k‖ ≤ ‖D j k l + D k j l‖ + ‖D l j k‖ :=
      norm_sub_le _ _
    _ ≤ (‖D j k l‖ + ‖D k j l‖) + ‖D l j k‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ (B j k l + B k j l) + B l j k :=
      add_le_add (add_le_add (hD j k l) (hD k j l)) (hD l j k)
    _ = B j k l + B k j l + B l j k := by
      ring

/-- Christoffel-symbol type inverse-metric contractions are pointwise Lipschitz on bounded
derivative arrays and entrywise bounded matrices with a common determinant lower bound. -/
theorem matrix_inv_christoffel_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M N : Matrix n n 𝕜)
    (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
              (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
                ‖D l j k - E l j k‖) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l) := by
  classical
  let comboD : n → 𝕜 := fun l => D j k l + D k j l - D l j k
  let comboE : n → 𝕜 := fun l => E j k l + E k j l - E l j k
  let comboDiffBound : n → ℝ := fun l =>
    ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖
  let comboBound : n → ℝ := fun l => DB j k l + DB k j l + DB l j k
  let innerBound : ℝ :=
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboDiffBound l +
        comboBound l * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l)
  have hinner :
      ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤ innerBound := by
    have hsum :
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤
          ∑ l : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
                ‖comboD l - comboE l‖ +
              comboBound l * ‖(M⁻¹ : Matrix n n 𝕜) i l -
                (N⁻¹ : Matrix n n 𝕜) i l‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun l => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l)
          (D := comboBound)
          (a := fun l => (M⁻¹ : Matrix n n 𝕜) i l)
          (b := comboD)
          (c := fun l => (N⁻¹ : Matrix n n 𝕜) i l)
          (d := comboE)
          (fun l _hl => matrix_inv_entry_norm_le M hM hδpos hdetM i l)
          (fun l _hl => by
            simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun l _hl => by
      have hcombo_bound :
          ‖comboE l‖ ≤ comboBound l := by
        simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l
      have hcombo_bound_nonneg : 0 ≤ comboBound l :=
        (norm_nonneg _).trans hcombo_bound
      have hcombo_diff :
          ‖comboD l - comboE l‖ ≤ comboDiffBound l := by
        simpa [comboD, comboE, comboDiffBound] using
          christoffelDerivativeCombo_norm_sub_le D E j k l
      have hlip :
          ‖(M⁻¹ : Matrix n n 𝕜) i l - (N⁻¹ : Matrix n n 𝕜) i l‖ ≤
            matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l :=
        matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i l
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcombo_diff
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l))
        (mul_le_mul_of_nonneg_left hlip hcombo_bound_nonneg)
  have hsplit :
      ((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
        ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)) =
          (2 : 𝕜)⁻¹ *
            ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l) := by
    ring
  calc
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ =
        ‖((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
          ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l))‖ := by
      simp [comboD, comboE]
    _ = ‖(2 : 𝕜)⁻¹ *
          ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)‖ := by
      rw [hsplit]
    _ ≤ ‖(2 : 𝕜)⁻¹‖ *
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ :=
      norm_mul_le _ _
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * innerBound :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
              (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
                ‖D l j k - E l j k‖) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l) := by
      simp [innerBound, comboDiffBound, comboBound]

/-- Christoffel-symbol type inverse-metric contractions are pointwise bounded by the quantitative
inverse-entry constants and derivative-array bounds. -/
theorem matrix_inv_christoffel_entry_norm_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    (M : Matrix n n 𝕜) (D : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j k : n) :
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ ≤
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (DB j k l + DB k j l + DB l j k) := by
  classical
  let comboD : n → 𝕜 := fun l => D j k l + D k j l - D l j k
  let comboBound : n → ℝ := fun l => DB j k l + DB k j l + DB l j k
  let innerBound : ℝ := ∑ l : n,
    matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l
  have hterm : ∀ l ∈ (Finset.univ : Finset n),
      ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
        matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l := by
    intro l _hl
    have hinv :
        ‖(M⁻¹ : Matrix n n 𝕜) i l‖ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l :=
      matrix_inv_entry_norm_le M hM hδpos hdet i l
    have hcombo : ‖comboD l‖ ≤ comboBound l := by
      simpa [comboD, comboBound] using christoffelDerivativeCombo_norm_le D hD j k l
    calc
      ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
          ‖(M⁻¹ : Matrix n n 𝕜) i l‖ * ‖comboD l‖ :=
        norm_mul_le _ _
      _ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l :=
        mul_le_mul hinv hcombo (norm_nonneg _)
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l)
  have hinner :
      ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤ innerBound := by
    calc
      ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
          ∑ l : n, ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l :=
        Finset.sum_le_sum hterm
      _ = innerBound := by
        rfl
  calc
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ =
        ‖(2 : 𝕜)⁻¹ * ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ := by
      simp [comboD]
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ :=
      norm_mul_le _ _
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * innerBound :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (DB j k l + DB k j l + DB l j k) := by
      simp [innerBound, comboBound]

/-- Quantitative pointwise bound for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
        (DB j k l + DB k j l + DB l j k)

/-- Quantitative pointwise Lipschitz bound for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntryLipschitzBound {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜) (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
          (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
            ‖D l j k - E l j k‖) +
        (DB j k l + DB k j l + DB l j k) *
          matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l)

theorem matrix_inv_christoffel_entry_norm_le_bound {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M : Matrix n n 𝕜) (D : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j k : n) :
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ ≤
      matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB i j k := by
  simpa [matrixInvChristoffelEntryBoundConst] using
    matrix_inv_christoffel_entry_norm_le M D hM hD hδpos hdet i j k

theorem matrix_inv_christoffel_entry_norm_sub_le_bound {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E i j k := by
  simpa [matrixInvChristoffelEntryLipschitzBound] using
    matrix_inv_christoffel_entry_norm_sub_le M N D E hM hN hE hδpos hdetM hdetN i j k

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

/-- Finite inverse-matrix contractions against a four-index coefficient array are pointwise
Lipschitz on bounded coefficient arrays and entrywise bounded matrices with a common determinant
lower bound. -/
theorem matrix_inv_two_index_contract_entry_norm_sub_le {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i : p) (j : q) :
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
      ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
  classical
  let innerBound : n → ℝ := fun a =>
    ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
        TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  have hinner : ∀ a : n,
      ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤ innerBound a := by
    intro a
    have hsum :
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
          ∑ b : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b *
                ‖T a b i j - U a b i j‖ +
              TB a b i j * ‖(M⁻¹ : Matrix n n 𝕜) a b -
                (N⁻¹ : Matrix n n 𝕜) a b‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b)
          (D := fun b => TB a b i j)
          (a := fun b => (M⁻¹ : Matrix n n 𝕜) a b)
          (b := fun b => T a b i j)
          (c := fun b => (N⁻¹ : Matrix n n 𝕜) a b)
          (d := fun b => U a b i j)
          (fun b _hb => matrix_inv_entry_norm_le M hM hδpos hdetM a b)
          (fun b _hb => hU a b i j))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun b _hb => by
      have hTB_nonneg : 0 ≤ TB a b i j := (norm_nonneg _).trans (hU a b i j)
      have hlip :
          ‖(M⁻¹ : Matrix n n 𝕜) a b - (N⁻¹ : Matrix n n 𝕜) a b‖ ≤
            matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b :=
        matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN a b
      exact add_le_add_right (mul_le_mul_of_nonneg_left hlip hTB_nonneg)
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖)
  calc
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ =
        ‖∑ a : n,
          ((∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a : n,
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : n, innerBound a :=
      Finset.sum_le_sum fun a _ha => hinner a
    _ =
      ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
      rfl

/-- Matrix-norm Lipschitz constant for varying the coefficient array in one entry of the
finite contraction `M⁻¹ᵃᵇ T_abij`, with the inverse matrix bounded by the determinant lower
bound and entrywise metric bounds. -/
def matrixInvTwoIndexContractCoeffDiffConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) : ℝ :=
  ∑ a : n, ∑ b : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b

/-- Matrix-norm Lipschitz constant for varying the metric in one entry of the finite contraction
`M⁻¹ᵃᵇ T_abij`, with the coefficient array bounded by `TB`. -/
def matrixInvTwoIndexContractMetricDiffConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ)
    (TB : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    TB a b i j * matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b

theorem matrixInvTwoIndexContractCoeffDiffConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (C : n → n → ℝ) :
    0 ≤ matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C a b

theorem matrixInvTwoIndexContractMetricDiffConst_nonneg {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (hTB : ∀ a b i j, 0 ≤ TB a b i j) (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      mul_nonneg (hTB a b i j)
        (matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C a b)

/-- One entry of the finite inverse contraction is Lipschitz in the coefficient-array matrix norm
and the metric matrix norm, on bounded coefficient arrays and entrywise bounded matrices with a
common determinant lower bound. -/
theorem matrix_inv_two_index_contract_entry_norm_sub_le_const {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i : p) (j : q) :
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
            ((fun a b => U a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
  classical
  let coeffDiffNorm : ℝ :=
    ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
      ((fun a b => U a b i j) : Matrix n n 𝕜)‖
  let innerBound : n → ℝ := fun a =>
    ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm +
        TB a b i j *
          (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖))
  have hinner : ∀ a : n,
      ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤ innerBound a := by
    intro a
    have hsum :
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
          ∑ b : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b *
                ‖T a b i j - U a b i j‖ +
              TB a b i j * ‖(M⁻¹ : Matrix n n 𝕜) a b -
                (N⁻¹ : Matrix n n 𝕜) a b‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b)
          (D := fun b => TB a b i j)
          (a := fun b => (M⁻¹ : Matrix n n 𝕜) a b)
          (b := fun b => T a b i j)
          (c := fun b => (N⁻¹ : Matrix n n 𝕜) a b)
          (d := fun b => U a b i j)
          (fun b _hb => matrix_inv_entry_norm_le M hM hδpos hdetM a b)
          (fun b _hb => hU a b i j))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun b _hb => by
      have hTB_nonneg : 0 ≤ TB a b i j := (norm_nonneg _).trans (hU a b i j)
      have hcoeff_diff :
          ‖T a b i j - U a b i j‖ ≤ coeffDiffNorm := by
        simpa [coeffDiffNorm] using
          Matrix.norm_entry_le_entrywise_sup_norm
            (((fun a b => T a b i j) : Matrix n n 𝕜) -
              ((fun a b => U a b i j) : Matrix n n 𝕜)) (i := a) (j := b)
      have hinv_diff :
          ‖(M⁻¹ : Matrix n n 𝕜) a b - (N⁻¹ : Matrix n n 𝕜) a b‖ ≤
            matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖ :=
        matrix_inv_entry_norm_sub_le_const_mul M N hM hN hδpos hdetM hdetN a b
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoeff_diff
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C a b))
        (mul_le_mul_of_nonneg_left hinv_diff hTB_nonneg)
  have hnorm :
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        ∑ a : n, innerBound a := by
    calc
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ =
          ‖∑ a : n,
            ((∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
              ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, innerBound a :=
        Finset.sum_le_sum fun a _ha => hinner a
  calc
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        ∑ a : n, innerBound a := hnorm
    _ =
        (∑ a : n, ∑ b : n,
            matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm) +
          (∑ a : n, ∑ b : n,
            TB a b i j *
              (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) := by
      simp [innerBound, Finset.sum_add_distrib]
    _ =
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * coeffDiffNorm +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
      have hcoeff :
          (∑ a : n, ∑ b : n,
              matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm) =
            matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * coeffDiffNorm := by
        simp_rw [matrixInvTwoIndexContractCoeffDiffConst, Finset.sum_mul]
      have hmetric :
          (∑ a : n, ∑ b : n,
              TB a b i j *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) =
            matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
        calc
          (∑ a : n, ∑ b : n,
              TB a b i j *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) =
              ∑ a : n, ∑ b : n,
                (TB a b i j *
                  matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b) * ‖M - N‖ := by
            refine Finset.sum_congr rfl fun a _ha =>
              Finset.sum_congr rfl fun b _hb => ?_
            ring
          _ =
            matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
            simp_rw [matrixInvTwoIndexContractMetricDiffConst, Finset.sum_mul]
      rw [hcoeff, hmetric]
    _ =
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
            ((fun a b => U a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
      rfl

/-- Matrix-valued finite inverse contractions against four-index coefficient arrays are
pointwise Lipschitz in the elementwise matrix norm. -/
theorem matrix_inv_two_index_contract_norm_sub_le {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜] {δ : ℝ}
    {C : n → n → ℝ} {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
        Matrix p q 𝕜) -
      ((fun i j =>
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
        Matrix p q 𝕜)‖ ≤
      ∑ i : p, ∑ j : q, ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
  classical
  let entryBound : p → q → ℝ := fun i j =>
    ∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
        TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  have hentry : ∀ i j,
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        entryBound i j := by
    intro i j
    simpa [entryBound] using
      matrix_inv_two_index_contract_entry_norm_sub_le M N T U hM hN hU hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : q, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : p, ∑ j : q, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
          Matrix p q 𝕜) -
        ((fun i j =>
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
          Matrix p q 𝕜)‖ ≤
        ∑ i : p, ∑ j : q, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
          Matrix p q 𝕜) -
        ((fun i j =>
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
          Matrix p q 𝕜)) i j‖ =
          ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : p, ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

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

/-- Ricci-coordinate quadratic Christoffel contractions are pointwise Lipschitz on bounded
Christoffel arrays. -/
theorem christoffel_quadratic_ricci_entry_norm_sub_le {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ : n → n → n → ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c) (i j : n) :
    ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
      ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
        (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤
      (∑ a : n, ∑ b : n,
        (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
          BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
          BΓ b a j * ‖Γ a i b - Λ a i b‖)) := by
  classical
  let leftΓ : A := ∑ a : n, ∑ b : n, Γ a i j * Γ b a b
  let leftΛ : A := ∑ a : n, ∑ b : n, Λ a i j * Λ b a b
  let rightΓ : A := ∑ a : n, ∑ b : n, Γ a i b * Γ b a j
  let rightΛ : A := ∑ a : n, ∑ b : n, Λ a i b * Λ b a j
  let leftBound : ℝ := ∑ a : n, ∑ b : n,
    (BΓ a i j * ‖Γ b a b - Λ b a b‖ + BΓ b a b * ‖Γ a i j - Λ a i j‖)
  let rightBound : ℝ := ∑ a : n, ∑ b : n,
    (BΓ a i b * ‖Γ b a j - Λ b a j‖ + BΓ b a j * ‖Γ a i b - Λ a i b‖)
  have hleftInner : ∀ a : n,
      ‖(∑ b : n, Γ a i j * Γ b a b) - ∑ b : n, Λ a i j * Λ b a b‖ ≤
        ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖) := by
    intro a
    simpa using
      (norm_finset_sum_mul_sub_sum_mul_le
        (S := (Finset.univ : Finset n))
        (B := fun _b => BΓ a i j)
        (D := fun b => BΓ b a b)
        (a := fun _b => Γ a i j)
        (b := fun b => Γ b a b)
        (c := fun _b => Λ a i j)
        (d := fun b => Λ b a b)
        (fun _b _hb => hΓ a i j)
        (fun b _hb => hΛ b a b))
  have hleft : ‖leftΓ - leftΛ‖ ≤ leftBound := by
    calc
      ‖leftΓ - leftΛ‖ =
          ‖(∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            ∑ a : n, ∑ b : n, Λ a i j * Λ b a b‖ := by
        rfl
      _ = ‖∑ a : n,
          ((∑ b : n, Γ a i j * Γ b a b) -
            ∑ b : n, Λ a i j * Λ b a b)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, Γ a i j * Γ b a b) -
            ∑ b : n, Λ a i j * Λ b a b‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖) :=
        Finset.sum_le_sum fun a _ha => hleftInner a
      _ = leftBound := by
        rfl
  have hrightInner : ∀ a : n,
      ‖(∑ b : n, Γ a i b * Γ b a j) - ∑ b : n, Λ a i b * Λ b a j‖ ≤
        ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖) := by
    intro a
    simpa using
      (norm_finset_sum_mul_sub_sum_mul_le
        (S := (Finset.univ : Finset n))
        (B := fun b => BΓ a i b)
        (D := fun b => BΓ b a j)
        (a := fun b => Γ a i b)
        (b := fun b => Γ b a j)
        (c := fun b => Λ a i b)
        (d := fun b => Λ b a j)
        (fun b _hb => hΓ a i b)
        (fun b _hb => hΛ b a j))
  have hright : ‖rightΓ - rightΛ‖ ≤ rightBound := by
    calc
      ‖rightΓ - rightΛ‖ =
          ‖(∑ a : n, ∑ b : n, Γ a i b * Γ b a j) -
            ∑ a : n, ∑ b : n, Λ a i b * Λ b a j‖ := by
        rfl
      _ = ‖∑ a : n,
          ((∑ b : n, Γ a i b * Γ b a j) -
            ∑ b : n, Λ a i b * Λ b a j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, Γ a i b * Γ b a j) -
            ∑ b : n, Λ a i b * Λ b a j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖) :=
        Finset.sum_le_sum fun a _ha => hrightInner a
      _ = rightBound := by
        rfl
  have hsplit :
      (leftΓ - rightΓ) - (leftΛ - rightΛ) = (leftΓ - leftΛ) - (rightΓ - rightΛ) := by
    abel
  calc
    ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
      ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
        (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ =
        ‖(leftΓ - rightΓ) - (leftΛ - rightΛ)‖ := by
      rfl
    _ = ‖(leftΓ - leftΛ) - (rightΓ - rightΛ)‖ := by
      rw [hsplit]
    _ ≤ ‖leftΓ - leftΛ‖ + ‖rightΓ - rightΛ‖ :=
      norm_sub_le _ _
    _ ≤ leftBound + rightBound :=
      add_le_add hleft hright
    _ =
      (∑ a : n, ∑ b : n,
        (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
          BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
          BΓ b a j * ‖Γ a i b - Λ a i b‖)) := by
      simp [leftBound, rightBound]

/-- The full finite Ricci-coordinate quadratic Christoffel contraction is pointwise Lipschitz in
the elementwise matrix norm on bounded Christoffel arrays. -/
theorem christoffel_quadratic_ricci_norm_sub_le {n A : Type*} [Fintype n] [NormedRing A]
    {BΓ : n → n → n → ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
        (∑ a : n, ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
        BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
        BΓ b a j * ‖Γ a i b - Λ a i b‖))
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using christoffel_quadratic_ricci_entry_norm_sub_le Γ Λ hΓ hΛ i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)) i j‖ =
          ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- The schematic Ricci-DeTurck coordinate entry built from an inverse principal contraction and
a supplied Christoffel array is pointwise Lipschitz on bounded inputs.  This is the algebraic
combination step before substituting the inverse-metric Christoffel formula. -/
theorem ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖))) := by
  classical
  let principalM : 𝕜 := ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j
  let principalN : 𝕜 := ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j
  let quadraticΓ : 𝕜 :=
    (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
      (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)
  let quadraticΛ : 𝕜 :=
    (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
      (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)
  let principalBound : ℝ := ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
      HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  let quadraticBound : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖))
  have hprincipal : ‖principalM - principalN‖ ≤ principalBound := by
    simpa [principalM, principalN, principalBound] using
      matrix_inv_two_index_contract_entry_norm_sub_le M N H K hM hN hK hδpos hdetM hdetN i j
  have hquadratic : ‖quadraticΓ - quadraticΛ‖ ≤ quadraticBound := by
    simpa [quadraticΓ, quadraticΛ, quadraticBound] using
      christoffel_quadratic_ricci_entry_norm_sub_le Γ Λ hΓ hΛ i j
  have hsplit :
      (principalM + quadraticΓ) - (principalN + quadraticΛ) =
        (principalM - principalN) + (quadraticΓ - quadraticΛ) := by
    abel
  calc
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ =
        ‖(principalM + quadraticΓ) - (principalN + quadraticΛ)‖ := by
      rfl
    _ = ‖(principalM - principalN) + (quadraticΓ - quadraticΛ)‖ := by
      rw [hsplit]
    _ ≤ ‖principalM - principalN‖ + ‖quadraticΓ - quadraticΛ‖ :=
      norm_add_le _ _
    _ ≤ principalBound + quadraticBound :=
      add_le_add hprincipal hquadratic
    _ =
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖))) := by
      simp [principalBound, quadraticBound]

/-- The matrix-valued schematic Ricci-DeTurck expression built from inverse principal contractions
and supplied Christoffel arrays is pointwise Lipschitz in the elementwise matrix norm. -/
theorem ricciDeTurck_schematic_from_christoffel_norm_sub_le {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
            HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
        ((∑ a : n, ∑ b : n,
          (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
            ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
        (∑ a : n, ∑ b : n,
          (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
            ΓB b a j * ‖Γ a i b - Λ a i b‖)))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
        HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
    ((∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖)))
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le
        M N H K Γ Λ hM hN hK hΓ hΛ hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)) i j‖ =
          ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
              ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
            ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
              ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
                (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- The schematic Ricci-DeTurck coordinate entry is pointwise Lipschitz in the primitive metric,
first-derivative, and second-derivative arrays, on entrywise bounded matrices with a common
determinant lower bound. -/
theorem ricciDeTurck_schematic_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      (let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
      (∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b))) := by
  classical
  let Γ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l * (D b c l + D c b l - D l b c)
  let Λ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l * (E b c l + E c b l - E l b c)
  let ΓB : n → n → n → ℝ :=
    fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c
  let ΓL : n → n → n → ℝ :=
    fun a b c => matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a b c
  let principalBound : ℝ := ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
      HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  let quadraticActual : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖))
  let quadraticBound : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ΓL b a b + ΓB b a b * ΓL a i j)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ΓL b a j + ΓB b a j * ΓL a i b))
  have hΓbound : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Γ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound M D hM hD hδpos hdetM a b c
  have hΛbound : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Λ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound N E hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ΓL a b c := by
    intro a b c
    simpa [Γ, Λ, ΓL] using
      matrix_inv_christoffel_entry_norm_sub_le_bound M N D E hM hN hE hδpos hdetM hdetN a b c
  have hbase :
      ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
        principalBound + quadraticActual := by
    simpa [principalBound, quadraticActual, ΓB] using
      ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le
        M N H K Γ Λ hM hN hK hΓbound hΛbound hδpos hdetM hdetN i j
  have hquad : quadraticActual ≤ quadraticBound := by
    have hleft : (∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) ≤
        ∑ a : n, ∑ b : n,
          (ΓB a i j * ΓL b a b + ΓB b a b * ΓL a i j) := by
      exact Finset.sum_le_sum fun a _ha =>
        Finset.sum_le_sum fun b _hb => by
          have hΓB_aij_nonneg : 0 ≤ ΓB a i j := (norm_nonneg _).trans (hΓbound a i j)
          have hΓB_bab_nonneg : 0 ≤ ΓB b a b := (norm_nonneg _).trans (hΓbound b a b)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hΓdiff b a b) hΓB_aij_nonneg)
            (mul_le_mul_of_nonneg_left (hΓdiff a i j) hΓB_bab_nonneg)
    have hright : (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖)) ≤
        ∑ a : n, ∑ b : n,
          (ΓB a i b * ΓL b a j + ΓB b a j * ΓL a i b) := by
      exact Finset.sum_le_sum fun a _ha =>
        Finset.sum_le_sum fun b _hb => by
          have hΓB_aib_nonneg : 0 ≤ ΓB a i b := (norm_nonneg _).trans (hΓbound a i b)
          have hΓB_baj_nonneg : 0 ≤ ΓB b a j := (norm_nonneg _).trans (hΓbound b a j)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hΓdiff b a j) hΓB_aib_nonneg)
            (mul_le_mul_of_nonneg_left (hΓdiff a i b) hΓB_baj_nonneg)
    exact add_le_add hleft hright
  calc
    ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      (let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ =
        ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := by
      simp [Γ, Λ]
    _ ≤ principalBound + quadraticActual := hbase
    _ ≤ principalBound + quadraticBound :=
      add_le_add (le_refl principalBound) hquad
    _ =
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
      (∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b))) := by
      simp [principalBound, quadraticBound, ΓB, ΓL]

/-- The matrix-valued schematic Ricci-DeTurck coordinate RHS is pointwise Lipschitz in the
elementwise matrix norm for the primitive metric, first-derivative, and second-derivative arrays. -/
theorem ricciDeTurck_schematic_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
            HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
        ((∑ a : n, ∑ b : n,
          (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
            matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
        (∑ a : n, ∑ b : n,
          (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
            matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b)))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
        HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
    ((∑ a : n, ∑ b : n,
      (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
        matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
    (∑ a : n, ∑ b : n,
      (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
        matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b)))
  have hentry : ∀ i j,
      ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        (let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      ricciDeTurck_schematic_entry_norm_sub_le M N D E H K
        hM hN hD hE hK hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)) i j‖ =
          ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                    (D b c l + D c b l - D l b c);
              (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
            (let Λ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                    (E b c l + E c b l - E l b c);
              (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
                ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
                  (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

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
