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

/-- The exported single-radius `C^{0,α}` constant for the primitive-input schematic
Ricci-DeTurck matrix estimate after higher entry controls are projected to value-level controls. -/
def ricciDeTurckSchematicMatrixBoundConst {n : Type*} [Fintype n] [DecidableEq n]
    (δ : ℝ) (R : n → n → ℝ) (RD : n → n → n → ℝ)
    (RH : n → n → n → n → ℝ) : ℝ :=
  ((∑ i : n, ∑ j : n,
      (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst
          (𝕜 := ℝ) δ R RH i j +
        ParabolicC0AlphaOn.christoffelQuadraticRicciEntryBoundConst
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
              (𝕜 := ℝ) δ R RD a b c)
          i j)) +
    (∑ i : n, ∑ j : n,
      (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst
          (𝕜 := ℝ) δ R R RH RH i j +
        ParabolicC0AlphaOn.christoffelQuadraticRicciEntryHolderConst
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
              (𝕜 := ℝ) δ R RD a b c)
          (fun a b c =>
            ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst
              (𝕜 := ℝ) δ R R RD RD a b c)
          i j)))

/-- Entrywise higher primitive metric, first-derivative, and second-derivative controls feed
the existing quantitative schematic Ricci-DeTurck RHS `C^{0,α}` estimate. -/
theorem ricciDeTurckSchematicMatrix_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {R : n → n → ℝ} {RD : n → n → n → ℝ}
    {RH : n → n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n ℝ}
    {D : ℝ × X → n → n → n → ℝ}
    {H : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC2AlphaNormLe (RH a b i j) α
      (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      (ricciDeTurckSchematicMatrixBoundConst (n := n) δ R RD RH)
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z)) s := by
  exact ParabolicC0AlphaNormLe.ricciDeTurck_schematic_of_entries
    (M := M) (D := D) (H := H) (R := R) (RD := RD) (RH := RH) (δ := δ)
    (fun a b => (hM a b).value_c0AlphaNormLe_self)
    (fun a b c => (hD a b c).value_c0AlphaNormLe_self)
    (fun a b i j => (hH a b i j).value_c0AlphaNormLe_self)
    hδpos hdet

/-- Finite-family direct schematic Ricci-DeTurck RHS `C^{0,α}` estimates from entrywise higher
primitive controls. -/
theorem ricciDeTurckSchematicMatrix_family_of_entries {κ n : Type*}
    [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {RD : κ → n → n → n → ℝ}
    {RH : κ → n → n → n → n → ℝ} {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaNormLe (R r a b) α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaNormLe (RD r a b c) α
      (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaNormLe (RH r a b i j) α
      (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaNormLe
      (ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s := by
  intro r
  exact ricciDeTurckSchematicMatrix_of_entries
    (X := X) (α := α) (s := s) (δ := δ)
    (R := R r) (RD := RD r) (RH := RH r)
    (M := M r) (D := D r) (H := H r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Pi-valued finite-family direct schematic Ricci-DeTurck RHS `C^{0,α}` estimate from entrywise
higher primitive controls. -/
theorem ricciDeTurckSchematicMatrix_pi_family_of_entries {κ n : Type*}
    [Fintype κ] [Fintype n] [DecidableEq n]
    {R : κ → n → n → ℝ} {RD : κ → n → n → n → ℝ}
    {RH : κ → n → n → n → n → ℝ} {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaNormLe (R r a b) α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaNormLe (RD r a b c) α
      (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaNormLe (RH r a b i j) α
      (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaNormLe
      (∑ r, ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
      α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s :=
  ParabolicC0AlphaNormLe.pi (X := X) (α := α) (s := s)
    (N := fun r =>
      ricciDeTurckSchematicMatrixBoundConst (n := n) δ (R r) (RD r) (RH r))
    (u := fun z : ℝ × X => fun r : κ =>
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z))
    (ricciDeTurckSchematicMatrix_family_of_entries
      (X := X) (α := α) (s := s) (δ := δ)
      (R := R) (RD := RD) (RH := RH) (M := M) (D := D) (H := H)
      hM hD hH hδpos hdet)

/-- Entrywise higher parabolic difference controls with radii linear in a shared scalar give a
pointwise matrix-norm difference bound with the summed entry radius. -/
theorem matrix_norm_sub_le_sum_mul_of_entries {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {R : ℝ} {K : m → n → ℝ} {M N : ℝ × X → Matrix m n ℝ}
    (hK : ∀ i j, 0 ≤ K i j) (hR : 0 ≤ R)
    (h : ∀ i j, ParabolicC2AlphaNormLe (K i j * R) α
      (fun z => M z i j - N z i j) s)
    ⦃z : ℝ × X⦄ (hz : z ∈ s) :
    ‖M z - N z‖ ≤ (∑ i, ∑ j, K i j) * R := by
  have hsum_nonneg : 0 ≤ ∑ i, ∑ j, K i j :=
    Finset.sum_nonneg fun i _hi => Finset.sum_nonneg fun j _hj => hK i j
  have htarget_nonneg : 0 ≤ (∑ i, ∑ j, K i j) * R :=
    mul_nonneg hsum_nonneg hR
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun j => ?_
  have hentry : ‖M z i j - N z i j‖ ≤ K i j * R := by
    simpa [dist_eq_norm] using (h i j).dist_le_of_sub hz
  have hentry_le_sum : K i j ≤ ∑ i, ∑ j, K i j := by
    have hentry_le_row : K i j ≤ ∑ j, K i j :=
      Finset.single_le_sum (fun j' _hj' => hK i j') (Finset.mem_univ j)
    have hrow_le_sum : (∑ j, K i j) ≤ ∑ i, ∑ j, K i j :=
      Finset.single_le_sum
        (fun i' _hi' => Finset.sum_nonneg fun j' _hj' => hK i' j')
        (Finset.mem_univ i)
    exact hentry_le_row.trans hrow_le_sum
  exact hentry.trans (mul_le_mul_of_nonneg_right hentry_le_sum hR)

private theorem entry_le_triple_sum {n : Type*} [Fintype n] [DecidableEq n]
    {K : n → n → n → ℝ} (hK : ∀ a b c, 0 ≤ K a b c) (a b c : n) :
    K a b c ≤ ∑ a, ∑ b, ∑ c, K a b c := by
  have hentry_le_c : K a b c ≤ ∑ c, K a b c :=
    Finset.single_le_sum (fun c' _hc' => hK a b c') (Finset.mem_univ c)
  have hc_le_b : (∑ c, K a b c) ≤ ∑ b, ∑ c, K a b c :=
    Finset.single_le_sum
      (fun b' _hb' => Finset.sum_nonneg fun c' _hc' => hK a b' c')
      (Finset.mem_univ b)
  have hb_le_a : (∑ b, ∑ c, K a b c) ≤ ∑ a, ∑ b, ∑ c, K a b c :=
    Finset.single_le_sum
      (fun a' _ha' =>
        Finset.sum_nonneg fun b' _hb' =>
          Finset.sum_nonneg fun c' _hc' => hK a' b' c')
      (Finset.mem_univ a)
  exact hentry_le_c.trans (hc_le_b.trans hb_le_a)

/-- Linear-radius bounded schematic Ricci-DeTurck RHS difference estimate from higher parabolic
primitive controls.  This is the `C⁰` readout form of the higher matrix Lipschitz estimate: the
entrywise higher difference balls are summed into matrix/array primitive difference constants
before the existing pointwise schematic RHS bound is applied. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe
    {n : Type*} [Fintype n] [DecidableEq n]
    {δ R : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n ℝ}
    {D E : ℝ × X → n → n → n → ℝ}
    {H K : ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j) (hR : 0 ≤ R)
    (hM : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC2AlphaNormLe (C a b) α (fun z => N z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC2AlphaNormLe (DB a b c) α (fun z => E z a b c) s)
    (hK : ∀ a b i j, ParabolicC2AlphaNormLe (HB a b i j) α
      (fun z => K z a b i j) s)
    (hMdiff : ∀ a b, ParabolicC2AlphaNormLe (KM a b * R) α
      (fun z => M z a b - N z a b) s)
    (hDdiff : ∀ a b c, ParabolicC2AlphaNormLe (KD a b c * R) α
      (fun z => D z a b c - E z a b c) s)
    (hHdiff : ∀ a b i j, ParabolicC2AlphaNormLe (KH a b i j * R) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB
          (∑ a, ∑ b, KM a b)
          (∑ a, ∑ b, ∑ c, KD a b c)
          (fun i j => ∑ a, ∑ b, KH a b i j) * R)
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hKMsum : 0 ≤ ∑ a, ∑ b, KM a b :=
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b
  have hKDsum : 0 ≤ ∑ a, ∑ b, ∑ c, KD a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb => Finset.sum_nonneg fun c _hc => hKD a b c
  have hKHsum : ∀ i j, 0 ≤ ∑ a, ∑ b, KH a b i j := fun i j =>
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKH a b i j
  have hMbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b := by
    intro z hz a b
    exact (hM a b).norm_le hz
  have hNbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b := by
    intro z hz a b
    exact (hN a b).norm_le hz
  have hDbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c := by
    intro z hz a b c
    exact (hD a b c).norm_le hz
  have hEbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c := by
    intro z hz a b c
    exact (hE a b c).norm_le hz
  have hKbound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j := by
    intro z hz a b i j
    exact (hK a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s →
      ‖M z - N z‖ ≤ (∑ a, ∑ b, KM a b) * R := by
    intro z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM) (M := M) (N := N)
      hKM hR hMdiff hz
  have hDdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ (∑ a, ∑ b, ∑ c, KD a b c) * R := by
    intro z hz a b c
    have hentry : ‖D z a b c - E z a b c‖ ≤ KD a b c * R := by
      simpa [dist_eq_norm] using (hDdiff a b c).dist_le_of_sub hz
    exact hentry.trans (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD a b c) hR)
  have hHdiff_bound : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n ℝ) -
          ((fun a b => K z a b i j) : Matrix n n ℝ)‖ ≤
        (∑ a, ∑ b, KH a b i j) * R := by
    intro z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH a b i j)
      (M := fun z : ℝ × X => (fun a b => H z a b i j))
      (N := fun z : ℝ × X => (fun a b => K z a b i j))
      (fun a b => hKH a b i j) hR (fun a b => hHdiff a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
    (X := X) (s := s) (δ := δ) (R := R)
    (KM := ∑ a, ∑ b, KM a b)
    (KD := ∑ a, ∑ b, ∑ c, KD a b c)
    (KH := fun i j => ∑ a, ∑ b, KH a b i j)
    (C := C) (DB := DB) (HB := HB)
    (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
    hDB hHB hMbound hNbound hDbound hEbound hKbound hKDsum hR
    hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdetM hdetN

/-- Compact-coordinate readout Lipschitz bridge for a state-space vector field that agrees with
the schematic Ricci-DeTurck RHS on the state set.  The analytic input remains the higher primitive
entry control; the output is the finite compact-family readout used by parabolic chart estimates. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_toCompactCoordFamily_of_higher_primitive_normLe
    {ι Y n : Type*} [Fintype ι] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    (Kdom : ι → TopologicalSpace.Compacts (ℝ × X))
    (hKdom : ∀ i, (Kdom i : Set (ℝ × X)) ⊆ s) (hα : 0 < α)
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {A : Y → parabolicC0AlphaSubmodule X (Matrix n n ℝ) α s}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖)
    (hAeq : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ z : ℝ × X,
      A u z = ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (M u z) (D u z) (H u z)) :
    LipschitzOnWith
      ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
          (𝕜 := ℝ) δ C DB HB
          (∑ a, ∑ b, KM a b)
          (∑ a, ∑ b, ∑ c, KD a b c)
          (fun i j => ∑ a, ∑ b, KH a b i j),
        ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
          (𝕜 := ℝ) hδpos hDB hHB
          (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
          (Finset.sum_nonneg fun a _ha =>
            Finset.sum_nonneg fun b _hb =>
              Finset.sum_nonneg fun c _hc => hKD a b c)
          (fun i j =>
            Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
      (fun u : Y =>
        parabolicC0AlphaSubmodule.toCompactCoordFamily
          (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
          Kdom hKdom hα (A u))
      stateSet := by
  refine parabolicC0AlphaSubmodule.lipschitzOnWith_toCompactCoordFamily_of_bounded_sub
    (X := X) (E := Matrix n n ℝ) (α := α) (s := s)
    Kdom hKdom hα ?_
  intro u hu v hv
  have hraw :
      ParabolicBoundedWith
        (ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j) * dist u v)
        (fun z : ℝ × X =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M u z) (D u z) (H u z) -
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (M v z) (D v z) (H v z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) (δ := δ) (R := dist u v)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (M := M u) (N := M v) (D := D u) (E := D v) (H := H u) (K := H v)
      hDB hHB hKM hKD hKH dist_nonneg
      (hM hu) (hM hv) (hD hu) (hD hv) (hH hv)
      (hMdiff hu hv) (hDdiff hu hv) (hHdiff hu hv)
      hδpos (hdet hu) (hdet hv)
  intro z hz
  simpa [hAeq hu z, hAeq hv z] using hraw hz

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

/-- State-space Lipschitz bridge for the schematic Ricci-DeTurck RHS from higher parabolic
primitive controls.  Uniform higher norm balls give the pointwise primitive bounds, while
pairwise higher norm balls with radii linear in `dist u v` give the primitive difference
estimates consumed by the existing matrix `C^{0,α}` Lipschitz theorem. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : n → n → ℝ} {KD : n → n → n → ℝ}
    {KH : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : ∀ a b, 0 ≤ KM a b) (hKD : ∀ a b c, 0 ≤ KD a b c)
    (hKH : ∀ a b i j, 0 ≤ KH a b i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB
            (∑ a, ∑ b, KM a b)
            (∑ a, ∑ b, ∑ c, KD a b c)
            (fun i j => ∑ a, ∑ b, KH a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB
            (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                Finset.sum_nonneg fun c _hc => hKD a b c)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKH a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z) (D u z) (H u z))
        stateSet := by
  have hKMsum : 0 ≤ ∑ a, ∑ b, KM a b :=
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM a b
  have hKDsum : 0 ≤ ∑ a, ∑ b, ∑ c, KD a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb => Finset.sum_nonneg fun c _hc => hKD a b c
  have hKHsum : ∀ i j, 0 ≤ ∑ a, ∑ b, KH a b i j := fun i j =>
    Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKH a b i j
  have hMbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b := by
    intro u hu z hz a b
    exact (hM hu a b).norm_le hz
  have hDbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c := by
    intro u hu z hz a b c
    exact (hD hu a b c).norm_le hz
  have hHbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j := by
    intro u hu z hz a b i j
    exact (hH hu a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s →
        ‖M u z - M v z‖ ≤ (∑ a, ∑ b, KM a b) * dist u v := by
    intro u hu v hv z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM) (M := M u) (N := M v)
      hKM dist_nonneg (hMdiff hu hv) hz
  have hDdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤
          (∑ a, ∑ b, ∑ c, KD a b c) * dist u v := by
    intro u hu v hv z hz a b c
    have hentry : ‖D u z a b c - D v z a b c‖ ≤ KD a b c * dist u v := by
      simpa [dist_eq_norm] using (hDdiff hu hv a b c).dist_le_of_sub hz
    exact hentry.trans
      (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD a b c) dist_nonneg)
  have hHdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n ℝ) -
          ((fun a b => H v z a b i j) : Matrix n n ℝ)‖ ≤
            (∑ a, ∑ b, KH a b i j) * dist u v := by
    intro u hu v hv z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH a b i j)
      (M := fun z : ℝ × X => (fun a b => H u z a b i j))
      (N := fun z : ℝ × X => (fun a b => H v z a b i j))
      (fun a b => hKH a b i j) dist_nonneg (fun a b => hHdiff hu hv a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le
    (X := X) (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (KM := ∑ a, ∑ b, KM a b)
    (KD := ∑ a, ∑ b, ∑ c, KD a b c)
    (KH := fun i j => ∑ a, ∑ b, KH a b i j)
    (stateSet := stateSet) (M := M) (D := D) (H := H)
    hDB hHB hKMsum hKDsum hKHsum
    hMbound hDbound hHbound hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdet

/-- State-space Lipschitz bridge from higher parabolic primitive controls with coarser exported
constants.  Entrywise higher difference controls may be proved with sharper constants; the
resulting schematic RHS Lipschitz constant is formed from any larger primitive constants accepted
by the existing matrix `C^{0,α}` theorem. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe_of_le
    {Y n : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ KM KD : ℝ} {KH : n → n → ℝ}
    {KM0 : n → n → ℝ} {KD0 : n → n → n → ℝ}
    {KH0 : n → n → n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n ℝ}
    {D : Y → ℝ × X → n → n → n → ℝ}
    {H : Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM0_nonneg : ∀ a b, 0 ≤ KM0 a b)
    (hKD0_nonneg : ∀ a b c, 0 ≤ KD0 a b c)
    (hKH0_nonneg : ∀ a b i j, 0 ≤ KH0 a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD)
    (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM_le : (∑ a, ∑ b, KM0 a b) ≤ KM)
    (hKD_le : (∑ a, ∑ b, ∑ c, KD0 a b c) ≤ KD)
    (hKH_le : ∀ i j, (∑ a, ∑ b, KH0 a b i j) ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C a b) α (fun z => M u z a b) s)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB a b c) α (fun z => D u z a b c) s)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB a b i j) α (fun z => H u z a b i j) s)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 a b * dist u v) α
        (fun z => M u z a b - M v z a b) s)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 a b c * dist u v) α
        (fun z => D u z a b c - D v z a b c) s)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 a b i j * dist u v) α
        (fun z => H u z a b i j - H v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ C DB HB KM KD KH,
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M u z) (D u z) (H u z))
        stateSet := by
  have hKD0sum : 0 ≤ ∑ a, ∑ b, ∑ c, KD0 a b c :=
    Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        Finset.sum_nonneg fun c _hc => hKD0_nonneg a b c
  have hMbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b := by
    intro u hu z hz a b
    exact (hM hu a b).norm_le hz
  have hDbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c := by
    intro u hu z hz a b c
    exact (hD hu a b c).norm_le hz
  have hHbound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j := by
    intro u hu z hz a b i j
    exact (hH hu a b i j).norm_le hz
  have hMdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s →
        ‖M u z - M v z‖ ≤ (∑ a, ∑ b, KM0 a b) * dist u v := by
    intro u hu v hv z hz
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := KM0) (M := M u) (N := M v)
      hKM0_nonneg dist_nonneg (hMdiff hu hv) hz
  have hDdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤
          (∑ a, ∑ b, ∑ c, KD0 a b c) * dist u v := by
    intro u hu v hv z hz a b c
    have hentry : ‖D u z a b c - D v z a b c‖ ≤ KD0 a b c * dist u v := by
      simpa [dist_eq_norm] using (hDdiff hu hv a b c).dist_le_of_sub hz
    exact hentry.trans
      (mul_le_mul_of_nonneg_right (entry_le_triple_sum hKD0_nonneg a b c) dist_nonneg)
  have hHdiff_bound : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n ℝ) -
          ((fun a b => H v z a b i j) : Matrix n n ℝ)‖ ≤
            (∑ a, ∑ b, KH0 a b i j) * dist u v := by
    intro u hu v hv z hz i j
    exact matrix_norm_sub_le_sum_mul_of_entries
      (X := X) (α := α) (s := s) (K := fun a b => KH0 a b i j)
      (M := fun z : ℝ × X => (fun a b => H u z a b i j))
      (N := fun z : ℝ × X => (fun a b => H v z a b i j))
      (fun a b => hKH0_nonneg a b i j) dist_nonneg
      (fun a b => hHdiff hu hv a b i j) hz
  exact ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le_of_le
    (X := X) (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (KM0 := ∑ a, ∑ b, KM0 a b)
    (KD0 := ∑ a, ∑ b, ∑ c, KD0 a b c)
    (KH0 := fun i j => ∑ a, ∑ b, KH0 a b i j)
    (KM := KM) (KD := KD) (KH := KH)
    (stateSet := stateSet) (M := M) (D := D) (H := H)
    hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le hKD0sum
    hMbound hDbound hHbound hMdiff_bound hDdiff_bound hHdiff_bound hδpos hdet

/-- Finite-family state-space Lipschitz bridge from higher parabolic primitive controls to the
schematic Ricci-DeTurck RHS coordinates. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b) (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos (hDB r) (hHB r)
            (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM r a b)
            (Finset.sum_nonneg fun a _ha =>
              Finset.sum_nonneg fun b _hb =>
                Finset.sum_nonneg fun c _hc => hKD r a b c)
            (fun i j =>
              Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKH r a b i j)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe
    (X := X) (α := α) (s := s) (δ := δ)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) hz

/-- Pi-valued finite-family state-space Lipschitz bridge from higher parabolic primitive
controls.  The Lipschitz constant is the finite sum of the coordinate schematic constants, so the
whole family can be consumed as one finite-product coordinate readout. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_higher_primitive_normLe
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM : κ → n → n → ℝ} {KD : κ → n → n → n → ℝ}
    {KH : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r a b, 0 ≤ KM r a b) (hKD : ∀ r a b c, 0 ≤ KD r a b c)
    (hKH : ∀ r a b i j, 0 ≤ KH r a b i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r)
            (∑ a, ∑ b, KM r a b)
            (∑ a, ∑ b, ∑ c, KD r a b c)
            (fun i j => ∑ a, ∑ b, KH r a b i j),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos (hDB r) (hHB r)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb => hKM r a b)
              (Finset.sum_nonneg fun a _ha =>
                Finset.sum_nonneg fun b _hb =>
                  Finset.sum_nonneg fun c _hc => hKD r a b c)
              (fun i j =>
                Finset.sum_nonneg fun a _ha =>
                  Finset.sum_nonneg fun b _hb => hKH r a b i j)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro z hz
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r)
      (∑ a, ∑ b, KM r a b)
      (∑ a, ∑ b, ∑ c, KD r a b c)
      (fun i j => ∑ a, ∑ b, KH r a b i j)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hKM r a b)
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          Finset.sum_nonneg fun c _hc => hKD r a b c)
      (fun i j =>
        Finset.sum_nonneg fun a _ha =>
          Finset.sum_nonneg fun b _hb => hKH r a b i j)
  have hcoord : ∀ r,
      LipschitzOnWith
        ⟨Kcoord r, hKcoord_nonneg r⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
    intro r
    exact ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe
      (X := X) (α := α) (s := s) (δ := δ)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (M := M) (D := D) (H := H)
      hDB hHB hKM hKD hKH hM hD hH hMdiff hDdiff hHdiff hδpos hdet r hz
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hsum_nonneg : 0 ≤ ∑ r, Kcoord r :=
    Finset.sum_nonneg fun r _hr => hKcoord_nonneg r
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum_nonneg dist_nonneg)).2 fun r => ?_
  have hr := (hcoord r).dist_le_mul u hu v hv
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  have hentry :
      ‖ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z) -
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r v z) (D r v z) (H r v z)‖ ≤ Kcoord r * dist u v := by
    simpa [dist_eq_norm] using hr
  exact hentry.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

/-- Finite-family state-space Lipschitz bridge from higher primitive controls with coarser
exported constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe_of_le
    {κ Y n : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := ℝ) hδpos (hDB r) (hHB r)
            (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_higher_primitive_normLe_of_le
    (X := X) (α := α) (s := s) (δ := δ)
    (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (C := C r) (DB := DB r) (HB := HB r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM0_nonneg r) (hKD0_nonneg r) (hKH0_nonneg r)
    (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
    (hKM_le r) (hKD_le r) (hKH_le r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r)
    hδpos (hdet r) hz

/-- Pi-valued finite-family state-space Lipschitz bridge from higher primitive controls with
coarser exported constants. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_pi_family_of_higher_primitive_normLe_of_le
    {κ Y n : Type*} [Fintype κ] [DecidableEq κ] [PseudoMetricSpace Y]
    [Fintype n] [DecidableEq n]
    {δ : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {KM0 : κ → n → n → ℝ} {KD0 : κ → n → n → n → ℝ}
    {KH0 : κ → n → n → n → n → ℝ} {C : κ → n → n → ℝ}
    {DB : κ → n → n → n → ℝ} {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n ℝ}
    {D : κ → Y → ℝ × X → n → n → n → ℝ}
    {H : κ → Y → ℝ × X → n → n → n → n → ℝ}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM0_nonneg : ∀ r a b, 0 ≤ KM0 r a b)
    (hKD0_nonneg : ∀ r a b c, 0 ≤ KD0 r a b c)
    (hKH0_nonneg : ∀ r a b i j, 0 ≤ KH0 r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM_le : ∀ r, (∑ a, ∑ b, KM0 r a b) ≤ KM r)
    (hKD_le : ∀ r, (∑ a, ∑ b, ∑ c, KD0 r a b c) ≤ KD r)
    (hKH_le : ∀ r i j, (∑ a, ∑ b, KH0 r a b i j) ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (C r a b) α (fun z => M r u z a b) s)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (DB r a b c) α (fun z => D r u z a b c) s)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (HB r a b i j) α (fun z => H r u z a b i j) s)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b,
      ParabolicC2AlphaNormLe (KM0 r a b * dist u v) α
        (fun z => M r u z a b - M r v z a b) s)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b c,
      ParabolicC2AlphaNormLe (KD0 r a b c * dist u v) α
        (fun z => D r u z a b c - D r v z a b c) s)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet → ∀ a b i j,
      ParabolicC2AlphaNormLe (KH0 r a b i j * dist u v) α
        (fun z => H r u z a b i j - H r v z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨∑ r, ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
            (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          Finset.sum_nonneg fun r _hr =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
              (𝕜 := ℝ) hδpos (hDB r) (hHB r)
              (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)⟩
        (fun u : Y => fun r =>
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
            (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro z hz
  let Kcoord : κ → ℝ := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst
      (𝕜 := ℝ) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r)
  have hKcoord_nonneg : ∀ r, 0 ≤ Kcoord r := fun r =>
    ParabolicC0AlphaOn.ricciDeTurckSchematicDiffBoundConst_nonneg
      (𝕜 := ℝ) hδpos (hDB r) (hHB r)
      (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
  have hcoord : ∀ r,
      LipschitzOnWith
        ⟨Kcoord r, hKcoord_nonneg r⟩
        (fun u : Y => ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z))
        stateSet := by
    intro r
    exact ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_higher_primitive_normLe_of_le
      (X := X) (α := α) (s := s) (δ := δ)
      (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH) (C := C) (DB := DB) (HB := HB)
      (stateSet := stateSet) (M := M) (D := D) (H := H)
      hDB hHB hKM0_nonneg hKD0_nonneg hKH0_nonneg
      hKM_nonneg hKD_nonneg hKH_nonneg hKM_le hKD_le hKH_le
      hM hD hH hMdiff hDdiff hHdiff hδpos hdet r hz
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hsum_nonneg : 0 ≤ ∑ r, Kcoord r :=
    Finset.sum_nonneg fun r _hr => hKcoord_nonneg r
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hsum_nonneg dist_nonneg)).2 fun r => ?_
  have hr := (hcoord r).dist_le_mul u hu v hv
  have hr_le_sum : Kcoord r ≤ ∑ r, Kcoord r :=
    Finset.single_le_sum (fun r' _hr' => hKcoord_nonneg r') (Finset.mem_univ r)
  have hentry :
      ‖ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r u z) (D r u z) (H r u z) -
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
          (M r v z) (D r v z) (H r v z)‖ ≤ Kcoord r * dist u v := by
    simpa [dist_eq_norm] using hr
  exact hentry.trans (mul_le_mul_of_nonneg_right hr_le_sum dist_nonneg)

end ParabolicC2AlphaNormLe

namespace ParabolicC2AlphaOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise higher parabolic membership packages as matrix-valued `C^{0,α}` membership. -/
theorem matrix_c0AlphaOn_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC2AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α M s :=
  ParabolicC0AlphaOn.matrix_of_entries fun i j => (h i j).c0AlphaOn

/-- Finite Pi-valued value-level `C^{0,α}` membership from coordinatewise higher parabolic
membership. -/
theorem pi_c0AlphaOn_of_entries {ι A : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {u : ℝ × X → ι → A}
    (h : ∀ i, ParabolicC2AlphaOn α (fun z => u z i) s) :
    ParabolicC0AlphaOn α u s :=
  ParabolicC0AlphaOn.pi fun i => (h i).c0AlphaOn

/-- Direct higher-regularity handoff for the schematic Ricci-DeTurck coordinate RHS.  Higher
primitive controls provide the value-level `C^{0,α}` hypotheses of the matrix closure theorem. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries {n : Type*}
    [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : ℝ × X → Matrix n n ℝ}
    {D : ℝ × X → n → n → n → ℝ}
    {H : ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ a b, ParabolicC2AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC2AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC2AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z)) s := by
  simpa [ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix] using
    (ParabolicC0AlphaOn.ricciDeTurck_schematic
      (M := M) (D := D) (H := H)
      (fun a b => (hM a b).c0AlphaOn)
      (fun a b c => (hD a b c).c0AlphaOn)
      (fun a b i j => (hH a b i j).c0AlphaOn)
      hδpos hdet)

/-- Finite-family direct higher-regularity handoff for schematic Ricci-DeTurck RHS coordinates. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_entries {κ n : Type*}
    [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaOn α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaOn α (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaOn α (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ∀ r, ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s := by
  intro r
  exact ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries
    (M := M r) (D := D r) (H := H r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Pi-valued finite-family direct higher-regularity handoff for schematic Ricci-DeTurck RHS
coordinates. -/
theorem ricciDeTurckSchematicMatrix_c0AlphaOn_pi_family_of_entries {κ n : Type*}
    [Fintype κ] [Fintype n] [DecidableEq n] {δ : ℝ}
    {M : κ → ℝ × X → Matrix n n ℝ}
    {D : κ → ℝ × X → n → n → n → ℝ}
    {H : κ → ℝ × X → n → n → n → n → ℝ}
    (hM : ∀ r a b, ParabolicC2AlphaOn α (fun z => M r z a b) s)
    (hD : ∀ r a b c, ParabolicC2AlphaOn α (fun z => D r z a b c) s)
    (hH : ∀ r a b i j, ParabolicC2AlphaOn α (fun z => H r z a b i j) s)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M r z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X => fun r : κ =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M r z) (D r z) (H r z)) s :=
  ParabolicC0AlphaOn.pi fun r =>
    ricciDeTurckSchematicMatrix_c0AlphaOn_family_of_entries
      (M := M) (D := D) (H := H) hM hD hH hδpos hdet r

end ParabolicC2AlphaOn

end AnalyticPDE
end RicciFlow
