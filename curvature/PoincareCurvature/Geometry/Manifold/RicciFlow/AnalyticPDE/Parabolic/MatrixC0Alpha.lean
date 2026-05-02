module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.unusedSectionVars false

/-!
# Matrix-valued parabolic `C^{0,α}` closure

This module contains finite-dimensional algebraic closure facts for the
parabolic `C^{0,α}` predicates.  It is kept separate from `ParabolicHolder`
so determinant imports do not enlarge the base parabolic Holder module.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

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

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
