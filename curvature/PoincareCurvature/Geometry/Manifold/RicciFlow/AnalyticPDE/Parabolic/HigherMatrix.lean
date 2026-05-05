module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.MatrixC0Alpha

set_option linter.unusedSectionVars false

/-!
# Higher parabolic Holder matrix handoffs

This module connects the coordinate `C^{2+α,1+α/2}` norm-ball layer to the
matrix-valued `C^{0,α}` closure estimates used by the Ricci-DeTurck schematic
RHS.  It proves no Schauder estimate; it only records that higher entry controls
are strong enough to supply the primitive `C^{0,α}` hypotheses.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE

namespace ParabolicC2AlphaNormLe

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise higher parabolic control packages as matrix-valued value-level `C^{0,α}`
control, with the matrix radius the sum of the entry radii. -/
theorem matrix_c0AlphaNormLe_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaNormLe (N i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaNormLe (∑ i, ∑ j, N i j) α M s :=
  ParabolicC0AlphaNormLe.matrix_of_entries
    (X := X) (α := α) (s := s) fun i j => (h i j).value_c0AlphaNormLe_self

/-- A matrix-valued higher parabolic norm ball projects to each entry as a value-level
`C^{0,α}` norm ball with the same radius. -/
theorem matrix_apply {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : ℝ} {M : ℝ × X → Matrix m n A}
    (h : ParabolicC2AlphaNormLe N α M s) (i : m) (j : n) :
    ParabolicC0AlphaNormLe N α (fun z => M z i j) s :=
  h.value_c0AlphaNormLe_self.matrix_apply i j

/-- Finite Pi-valued value-level `C^{0,α}` control from entrywise higher parabolic
single-radius controls. -/
theorem pi_c0AlphaNormLe_of_entries {ι A : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {N : ι → ℝ} {u : ℝ × X → ι → A}
    (h : ∀ i, ParabolicC2AlphaNormLe (N i) α (fun z => u z i) s) :
    ParabolicC0AlphaNormLe (∑ i, N i) α u s :=
  ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := N) (u := u) fun i => (h i).value_c0AlphaNormLe_self

/-- Higher parabolic entry controls supply the primitive entrywise hypotheses for the
single-radius schematic Ricci-DeTurck RHS difference estimate. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_entries {n : Type*}
    [Fintype n] [DecidableEq n]
    {R Rd : n → n → ℝ} {RD RDd : n → n → n → ℝ}
    {RH RHd : n → n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n ℝ}
    {D E : ℝ × X → n → n → n → ℝ}
    {H K : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC2AlphaNormLe (Rd a b) α
      (fun z => M z a b - N z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c, ParabolicC2AlphaNormLe (RDd a b c) α
      (fun z => D z a b c - E z a b c) s)
    (hK : ∀ a b i j, ParabolicC2AlphaNormLe (RH a b i j) α
      (fun z => K z a b i j) s)
    (hHdiff : ∀ a b i j, ParabolicC2AlphaNormLe (RHd a b i j) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ R Rd RD RDd RH RHd +
        ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ R R Rd Rd RD RD RDd RDd RH RH RHd RHd)
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  exact ParabolicC0AlphaNormLe.ricciDeTurckSchematicMatrix_sub_entrywise_of_entries
    (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
    (R := R) (Rd := Rd) (RD := RD) (RDd := RDd) (RH := RH) (RHd := RHd)
    (fun a b => (hM a b).value_c0AlphaNormLe_self)
    (fun a b => (hN a b).value_c0AlphaNormLe_self)
    (fun a b => (hMdiff a b).value_c0AlphaNormLe_self)
    (fun a b c => (hD a b c).value_c0AlphaNormLe_self)
    (fun a b c => (hE a b c).value_c0AlphaNormLe_self)
    (fun a b c => (hDdiff a b c).value_c0AlphaNormLe_self)
    (fun a b i j => (hK a b i j).value_c0AlphaNormLe_self)
    (fun a b i j => (hHdiff a b i j).value_c0AlphaNormLe_self)
    hδpos hdetM hdetN

end ParabolicC2AlphaNormLe

end AnalyticPDE
end RicciFlow
