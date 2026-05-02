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

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
