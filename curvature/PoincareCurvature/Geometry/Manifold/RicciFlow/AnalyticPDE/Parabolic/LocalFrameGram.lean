module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.MatrixC0Alpha
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

set_option linter.unusedSectionVars false

/-!
# Parabolic local-frame Gram matrix bridges

This module connects the geometric local-frame Gram determinant facts to the
finite matrix-valued parabolic `C^{0,α}` closure API.  It stays on the analytic
PDE side of the import graph so the core Levi-Civita geometry layer does not
depend on parabolic estimates.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set
open scoped Bundle Manifold ContDiff Topology NNReal Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC0AlphaOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- If the local-frame Gram entries have parabolic `C^{0,α}` control on a compact time-space
set contained in a trivialization base, then the inverse Gram matrix is parabolic `C^{0,α}` there.
-/
theorem localFrameGramMatrix_inv_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv (s := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    hG hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries lift to
parabolic `C^{0,α}` control of the inverse Gram matrix on compact time-space sets contained in a
trivialization base. -/
theorem localFrameGramMatrix_inv_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B Hc : ι → ι → ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ Hc i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        Hc i j * (dist x y) ^ α) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hB_nonneg i j) (hH_nonneg i j) hα (hB i j) (hholder i j)

/-- If the local-frame Gram entries and a three-index derivative array have parabolic
`C^{0,α}` control on a compact time-space set contained in a trivialization base, then the
associated inverse-Gram Christoffel-type contraction has parabolic `C^{0,α}` control there. -/
theorem localFrameGramMatrix_inv_christoffel_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z : ℝ × M => D z i j k) K) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : ℝ)⁻¹ *
          ∑ l : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) i l *
              (D z j k l + D z k j l - D z l j k)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_christoffel
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (D := D) hG hD hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
parabolic control of a three-index derivative array, lift to parabolic `C^{0,α}` control of the
associated inverse-Gram Christoffel-type contraction on compact time-space sets contained in a
trivialization base. -/
theorem localFrameGramMatrix_inv_christoffel_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B Hc : ι → ι → ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ Hc i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        Hc i j * (dist x y) ^ α)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z : ℝ × M => D z i j k) K) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : ℝ)⁻¹ *
          ∑ l : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) i l *
              (D z j k l + D z k j l - D z l j k)) K := by
  refine localFrameGramMatrix_inv_christoffel_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hD
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hB_nonneg i j) (hH_nonneg i j) hα (hB i j) (hholder i j)

/-- If the local-frame Gram entries and the first- and second-derivative coefficient arrays have
parabolic `C^{0,α}` control on a compact time-space set contained in a trivialization base, then
the schematic local Ricci-DeTurck coordinate right-hand side has parabolic `C^{0,α}` control
there.  The Gram determinant lower bound is supplied by the geometric local-frame theorem. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z : ℝ × M => D z i j k) K)
    (hHc : ∀ a b i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a b i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          let Γ : ι → ι → ι → ℝ := fun a c d =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) a l *
                  (D z c d l + D z d c l - D z l c d)
          (∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) +
            ((∑ a : ι, ∑ c : ι, Γ a i j * Γ c a c) -
              (∑ a : ι, ∑ c : ι, Γ a i c * Γ c a j)) :
          Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact ricciDeTurck_schematic
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (D := D) (H := Hc) hG hD hHc hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
parabolic control of the first- and second-derivative coefficient arrays, lift to parabolic
`C^{0,α}` control of the schematic local Ricci-DeTurck coordinate right-hand side on compact
time-space sets contained in a trivialization base. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B Hgram : ι → ι → ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hHgram_nonneg : ∀ i j, 0 ≤ Hgram i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        Hgram i j * (dist x y) ^ α)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z : ℝ × M => D z i j k) K)
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          let Γ : ι → ι → ι → ℝ := fun a c d =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) a l *
                  (D z c d l + D z d c l - D z l c d)
          (∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) +
            ((∑ a : ι, ∑ c : ι, Γ a i j * Γ c a c) -
              (∑ a : ι, ∑ c : ι, Γ a i c * Γ c a j)) :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hD hHc
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hB_nonneg i j) (hHgram_nonneg i j) hα (hB i j) (hholder i j)

/-- Quantitative compact local-frame bridge for the schematic local Ricci-DeTurck coordinate
right-hand side.  The geometric Gram determinant theorem supplies a positive determinant lower
bound `δ`, and the finite-dimensional parabolic estimate exposes the corresponding explicit
bounded `C^{0,α}` constants. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    {HB HH : ι → ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          (matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j +
            christoffelQuadraticRicciEntryBoundConst
              (fun a c d =>
                matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB a c d)
              i j))
        (∑ i : ι, ∑ j : ι,
          (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB GH HB HH i j +
            christoffelQuadraticRicciEntryHolderConst
              (fun a c d =>
                matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB a c d)
              (fun a c d =>
                matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB GH DB DH a c d)
              i j))
        α
        (fun z : ℝ × M =>
          (fun i j =>
            let Γ : ι → ι → ι → ℝ := fun a c d =>
              (2 : ℝ)⁻¹ *
                ∑ l : ι,
                  ((show Matrix ι ι ℝ from
                      CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                      Matrix ι ι ℝ) a l *
                    (D z c d l + D z d c l - D z l c d)
            (∑ a : ι, ∑ c : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) a c * Hc z a c i j) +
              ((∑ a : ι, ∑ c : ι, Γ a i j * Γ c a c) -
                (∑ a : ι, ∑ c : ι, Γ a i c * Γ c a j)) :
            Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact ricciDeTurck_schematic_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (D := D) (H := Hc) hGH hDB hDH hHB hHH hG hDctrl hHc hδpos hdet

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
