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

/-- A finite family of local-frame Gram determinants admits one compact time-space lower bound.
This is the determinant handoff needed when a finite cover uses several trivializations at once. -/
theorem localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ (e r).baseSet) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ r ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖ := by
  classical
  have hcommon :
      ∀ S : Finset ρ, ∃ δ : ℝ, 0 < δ ∧
        ∀ r, r ∈ S → ∀ ⦃z : ℝ × M⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨1, by norm_num, ?_⟩
        intro r hr
        exact False.elim (by
          simp at hr)
    | insert r S hrS ih =>
        rcases ih with ⟨δS, hδS, hS⟩
        rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
            (I := I) (E := E) (e r) (b r) hK (hKbase r) with
          ⟨δr, hδr, hr⟩
        refine ⟨min δr δS, lt_min hδr hδS, ?_⟩
        intro q hq z hz
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact (min_le_left δr δS).trans (hr hz)
        · exact (min_le_right δr δS).trans (hS q hq hz)
  rcases hcommon (Finset.univ : Finset ρ) with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro r z hz
  exact hδ r (Finset.mem_univ r) hz

/-- A finite family of inverse local-frame Gram matrices has explicit bounded parabolic
`C^{0,α}` estimates with one compact Gram determinant lower bound shared by the family. -/
theorem localFrameGramMatrix_inv_family_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    {GB GH : ρ → ι → ι → ℝ}
    (hGH : ∀ r i j, 0 ≤ GH r i j)
    (hG : ∀ r i j,
      ParabolicC0AlphaWith (GB r i j) (GH r i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2 i j)
        K) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ (GB r) i j)
          (∑ i : ι, ∑ j : ι, matrixInvEntryHolderConst (𝕜 := ℝ) δ (GB r) (GH r) i j)
          α
          (fun z : ℝ × M =>
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  rcases localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact matrix_inv_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2))
    (B := GB r) (H := GH r) (δ := δ)
    (hGH r) (hG r) hδpos (hdet r)

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

/-- On a unit parabolic-diameter compact time-space set, spatial Lipschitz estimates for
local-frame Gram entries lower to parabolic `C^{0,α}` estimates for every `0 ≤ α ≤ 1`,
and hence give parabolic control of the inverse Gram matrix. -/
theorem localFrameGramMatrix_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_
  intro i j
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := B i j) (K := L i j)
    hα_nonneg hα_le_one (hB_nonneg i j) (hB i j) (hL i j) hdiam

/-- On a compact time-space subset of a closed parabolic ball of diameter at most one, spatial
Lipschitz Gram-entry estimates lower to inverse-Gram parabolic `C^{0,α}` control for every
`0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_
  intro i j
  exact
    (of_snd_lipschitzOnWith (s := K) (B := B i j) (K := L i j)
      (hB_nonneg i j) (hB i j) (hL i j)).mono_exponent_of_subset_closedBall
        hα_nonneg hα_le_one hs hR

/-- On a compact time-space subset of a closed parabolic cylinder of diameter at most one,
spatial Lipschitz Gram-entry estimates lower to inverse-Gram parabolic `C^{0,α}` control for
every `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_
  intro i j
  exact
    (of_snd_lipschitzOnWith (s := K) (B := B i j) (K := L i j)
      (hB_nonneg i j) (hB i j) (hL i j)).mono_exponent_of_subset_closedCylinder
        hα_nonneg hα_le_one hs hdiam

/-- Quantitative compact local-frame bridge for the inverse Gram matrix.  The geometric Gram
determinant theorem supplies a positive determinant lower bound `δ`, and the finite-dimensional
matrix inverse estimate exposes explicit bounded `C^{0,α}` constants. -/
theorem localFrameGramMatrix_inv_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ GB i j)
        (∑ i : ι, ∑ j : ι, matrixInvEntryHolderConst (𝕜 := ℝ) δ GB GH i j)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_inv_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    hGH hG hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries yield the
quantitative compact local-frame inverse Gram estimate. -/
theorem localFrameGramMatrix_inv_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ GB i j)
        (∑ i : ι, ∑ j : ι, matrixInvEntryHolderConst (𝕜 := ℝ) δ GB GH i j)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH ?_
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hB i j) (hGH i j) hα (hholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for inverse Gram matrices.
The Lipschitz constants become the explicit parabolic Holder constants after lowering to any
`0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ GB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) i j)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase (fun i j => NNReal.coe_nonneg (Lgram i j)) ?_
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hB i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse Gram
matrices.  The Lipschitz constants become the explicit parabolic Holder constants after lowering
to any `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ GB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) i j)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase (fun i j => NNReal.coe_nonneg (Lgram i j)) ?_
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hB i j) (hL i j)).mono_exponent_of_subset_closedBall
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hs hR

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse Gram
matrices.  The Lipschitz constants become the explicit parabolic Holder constants after lowering
to any `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, matrixInvEntryBoundConst (𝕜 := ℝ) δ GB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) i j)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase (fun i j => NNReal.coe_nonneg (Lgram i j)) ?_
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hB i j) (hL i j)).mono_exponent_of_subset_closedCylinder
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hs hdiam

/-- Compact local-frame bridge for the function-level bounded difference of inverse Gram
matrices, comparing the geometric local-frame Gram matrix with an arbitrary comparison matrix
input. -/
theorem localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hGctrl : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c,
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 a c‖ ≤ C a c)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := ℝ) δ C * ηG)
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_bounded_sub_le_const_mul_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) hK hα hGctrl hNctrl hdetG_ne hdetN_ne hGbound hNbound hGdiff

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {ηG : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := ℝ) δ C * ηG)
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase ?_ hNctrl hdetN_ne ?_
    hNbound hGdiff
  · intro i j
    exact of_snd_holder (s := K) (α := α)
      (hC_nonneg i j) (hGH i j) hα.le (hGbound i j) (hGholder i j)
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Unit-diameter spatial-Lipschitz local-frame bridge for the function-level bounded difference
of inverse Gram matrices. -/
theorem localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := ℝ) δ C * ηG)
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase ?_ hNctrl hdetN_ne ?_
    hNbound hGdiff
  · intro i j
    exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
      (s := K) (α := α) (B := C i j) (K := Lgram i j)
      hα_pos.le hα_le_one (hC_nonneg i j) (hGbound i j) (hL i j) hdiam
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse Gram matrices. -/
theorem localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := ℝ) δ C * ηG)
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hNbound hGdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse Gram matrices. -/
theorem localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := ℝ) δ C * ηG)
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_bounded_sub_le_const_mul_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hNbound hGdiff

/-- Compact local-frame bridge for parabolic `C^{0,α}` control of inverse Gram differences,
comparing the geometric local-frame Gram matrix with an arbitrary comparison matrix input. -/
theorem localFrameGramMatrix_inv_sub_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {ηG : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := ℝ) δ C ηG)
        (matrixInvSubHolderConst (𝕜 := ℝ) δ C GH)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_sub_with_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) hK hα hC_nonneg hGH hG hN hdetG_ne hdetN_ne hGdiff

/-- Entrywise-difference compact local-frame bridge for inverse Gram matrices. -/
theorem localFrameGramMatrix_inv_sub_with_entrywise_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd)
        (matrixInvEntrywiseSubHolderConst (𝕜 := ℝ) δ C GH Gd GHd)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_sub_with_entrywise_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) hK hα hC_nonneg hGH hGd hGHd hG hN hGdiff hdetG_ne hdetN_ne

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_sub_with_entrywise_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd)
        (matrixInvEntrywiseSubHolderConst (𝕜 := ℝ) δ C GH Gd GHd)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hGd hGHd ?_ hN hGdiff
    hdetN_ne
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_sub_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_sub_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {ηG : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := ℝ) δ C ηG)
        (matrixInvSubHolderConst (𝕜 := ℝ) δ C GH)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH ?_ hN hdetN_ne hGdiff
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Unit-diameter spatial-Lipschitz local-frame bridge for entrywise inverse Gram matrix
differences. -/
theorem localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd)
        (matrixInvEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hGd hGHd ?_ hN hGdiff hdetN_ne
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for entrywise inverse Gram matrix
differences. -/
theorem localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd)
        (matrixInvEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hGdiff hdetN_ne

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for entrywise inverse Gram
matrix differences. -/
theorem localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd)
        (matrixInvEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hGdiff hdetN_ne

/-- Unit-diameter spatial-Lipschitz local-frame bridge for inverse Gram matrix differences. -/
theorem localFrameGramMatrix_inv_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := ℝ) δ C ηG)
        (matrixInvSubHolderConst (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)))
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  refine localFrameGramMatrix_inv_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) ?_ hN hdetN_ne hGdiff
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse Gram matrix
differences. -/
theorem localFrameGramMatrix_inv_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := ℝ) δ C ηG)
        (matrixInvSubHolderConst (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)))
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hdetN_ne hGdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse Gram matrix
differences. -/
theorem localFrameGramMatrix_inv_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {ηG : ℝ} {Lgram : ι → ι → ℝ≥0}
    {N : ℝ × M → Matrix ι ι ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := ℝ) δ C ηG)
        (matrixInvSubHolderConst (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)))
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ) - (N z)⁻¹) K := by
  exact
    localFrameGramMatrix_inv_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hdetN_ne hGdiff

/-- If the local-frame Gram entries and a vector have parabolic `C^{0,α}` control on a compact
time-space set contained in a trivialization base, then the inverse-Gram vector product has
parabolic `C^{0,α}` control there. -/
theorem localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {v : ℝ × M → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => v z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ).mulVec (v z)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_mulVec
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (v := v) hG hv hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_mulVec_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hGB : ∀ i j, 0 ≤ GB i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => v z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ).mulVec (v z)) K := by
  refine localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hv
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hGB i j) (hGH i j) hα (hGbound i j) (hGholder i j)

/-- Unit-diameter spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_mulVec_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => v z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ).mulVec (v z)) K := by
  refine localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hv
  intro i j
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := GB i j) (K := Lgram i j)
    hα_nonneg hα_le_one (hGB_nonneg i j) (hGbound i j) (hL i j) hdiam

/-- Closed-parabolic-ball spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_mulVec_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => v z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ).mulVec (v z)) K := by
  exact
    localFrameGramMatrix_inv_mulVec_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hv

/-- Closed-parabolic-cylinder spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_mulVec_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_mulVec_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => v z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ((show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
          Matrix ι ι ℝ).mulVec (v z)) K := by
  exact
    localFrameGramMatrix_inv_mulVec_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hv

/-- Quantitative compact local-frame bridge for inverse-Gram vector products. -/
theorem localFrameGramMatrix_inv_mulVec_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {Bv Hv : ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j) (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z : ℝ × M => v z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, matrixInvMulVecEntryBoundConst (𝕜 := ℝ) δ GB Bv i)
        (∑ i : ι, matrixInvMulVecEntryHolderConst (𝕜 := ℝ) δ GB GH Bv Hv i)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (v z)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_inv_mulVec_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (v := v) hGH hBv hHv hG hv hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_mulVec_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_mulVec_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {Bv Hv : ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j) (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z : ℝ × M => v z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, matrixInvMulVecEntryBoundConst (𝕜 := ℝ) δ GB Bv i)
        (∑ i : ι, matrixInvMulVecEntryHolderConst (𝕜 := ℝ) δ GB GH Bv Hv i)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (v z)) K := by
  refine localFrameGramMatrix_inv_mulVec_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH hBv hHv ?_ hv
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα (hGholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for inverse-Gram vector
products. -/
theorem localFrameGramMatrix_inv_mulVec_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bv Hv : ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z : ℝ × M => v z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, matrixInvMulVecEntryBoundConst (𝕜 := ℝ) δ GB Bv i)
        (∑ i : ι,
          matrixInvMulVecEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) Bv Hv i)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (v z)) K := by
  refine localFrameGramMatrix_inv_mulVec_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hBv hHv ?_ hv
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-Gram
vector products. -/
theorem localFrameGramMatrix_inv_mulVec_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bv Hv : ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z : ℝ × M => v z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, matrixInvMulVecEntryBoundConst (𝕜 := ℝ) δ GB Bv i)
        (∑ i : ι,
          matrixInvMulVecEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) Bv Hv i)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (v z)) K := by
  exact
    localFrameGramMatrix_inv_mulVec_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hHv hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hv

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-Gram
vector products. -/
theorem localFrameGramMatrix_inv_mulVec_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bv Hv : ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z : ℝ × M => v z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, matrixInvMulVecEntryBoundConst (𝕜 := ℝ) δ GB Bv i)
        (∑ i : ι,
          matrixInvMulVecEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) Bv Hv i)
        α
        (fun z : ℝ × M =>
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (v z)) K := by
  exact
    localFrameGramMatrix_inv_mulVec_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hHv hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hv

/-- If the local-frame Gram entries and a row vector have parabolic `C^{0,α}` control on a
compact time-space set contained in a trivialization base, then the vector-inverse-Gram product
has parabolic `C^{0,α}` control there. -/
theorem localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {v : ℝ × M → ι → ℝ}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        Matrix.vecMul (v z)
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_vecMul_inv
    (v := v)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    hv hG hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_vecMul_inv_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hGB : ∀ i j, 0 ≤ GB i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        Matrix.vecMul (v z)
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hv ?_
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hGB i j) (hGH i j) hα (hGbound i j) (hGholder i j)

/-- Unit-diameter spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_vecMul_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        Matrix.vecMul (v z)
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hv ?_
  intro i j
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := GB i j) (K := Lgram i j)
    hα_nonneg hα_le_one (hGB_nonneg i j) (hGbound i j) (hL i j) hdiam

/-- Closed-parabolic-ball spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_vecMul_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        Matrix.vecMul (v z)
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_vecMul_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hv hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)

/-- Closed-parabolic-cylinder spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_vecMul_inv_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_vecMul_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        Matrix.vecMul (v z)
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_vecMul_inv_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hv hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)

/-- Quantitative compact local-frame bridge for vector-inverse-Gram products. -/
theorem localFrameGramMatrix_vecMul_inv_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB GH : ι → ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ j : ι, matrixVecMulInvEntryBoundConst (𝕜 := ℝ) δ Bv GB j)
        (∑ j : ι, matrixVecMulInvEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB GH j)
        α
        (fun z : ℝ × M =>
          Matrix.vecMul (v z)
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_vecMul_inv_with
    (v := v)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    hBv hHv hGH hv hG hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_vecMul_inv_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_vecMul_inv_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB GH : ι → ι → ℝ} {v : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ j : ι, matrixVecMulInvEntryBoundConst (𝕜 := ℝ) δ Bv GB j)
        (∑ j : ι, matrixVecMulInvEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB GH j)
        α
        (fun z : ℝ × M =>
          Matrix.vecMul (v z)
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_vecMul_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hBv hHv hGH hv ?_
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα (hGholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for vector-inverse-Gram
products. -/
theorem localFrameGramMatrix_vecMul_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {v : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ j : ι, matrixVecMulInvEntryBoundConst (𝕜 := ℝ) δ Bv GB j)
        (∑ j : ι,
          matrixVecMulInvEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
            (fun i j => (Lgram i j : ℝ)) j)
        α
        (fun z : ℝ × M =>
          Matrix.vecMul (v z)
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_vecMul_inv_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hBv hHv
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hv ?_
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for
vector-inverse-Gram products. -/
theorem localFrameGramMatrix_vecMul_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {v : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ j : ι, matrixVecMulInvEntryBoundConst (𝕜 := ℝ) δ Bv GB j)
        (∑ j : ι,
          matrixVecMulInvEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
            (fun i j => (Lgram i j : ℝ)) j)
        α
        (fun z : ℝ × M =>
          Matrix.vecMul (v z)
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_vecMul_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hHv hv hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for
vector-inverse-Gram products. -/
theorem localFrameGramMatrix_vecMul_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {v : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ j : ι, matrixVecMulInvEntryBoundConst (𝕜 := ℝ) δ Bv GB j)
        (∑ j : ι,
          matrixVecMulInvEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
            (fun i j => (Lgram i j : ℝ)) j)
        α
        (fun z : ℝ × M =>
          Matrix.vecMul (v z)
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_vecMul_inv_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hHv hv hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)

/-- If the local-frame Gram entries and two vectors have parabolic `C^{0,α}` control on a compact
time-space set contained in a trivialization base, then the inverse-Gram bilinear contraction has
parabolic `C^{0,α}` control there. -/
theorem localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {v w : ℝ × M → ι → ℝ}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => w z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ∑ i : ι, v z i *
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (w z) i) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_bilinear_entry
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (v := v) (w := w) hv hG hw hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bilinear_entry_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {v w : ℝ × M → ι → ℝ}
    (hGB : ∀ i j, 0 ≤ GB i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => w z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ∑ i : ι, v z i *
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (w z) i) K := by
  refine localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hv ?_ hw
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hGB i j) (hGH i j) hα (hGbound i j) (hGholder i j)

/-- Unit-diameter spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bilinear_entry_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v w : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => w z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ∑ i : ι, v z i *
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (w z) i) K := by
  refine localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hv ?_ hw
  intro i j
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := GB i j) (K := Lgram i j)
    hα_nonneg hα_le_one (hGB_nonneg i j) (hGbound i j) (hL i j) hdiam

/-- Closed-parabolic-ball spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bilinear_entry_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v w : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => w z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ∑ i : ι, v z i *
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (w z) i) K := by
  exact
    localFrameGramMatrix_inv_bilinear_entry_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hv hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hw

/-- Closed-parabolic-cylinder spatial-Lipschitz Gram-entry variant of
`localFrameGramMatrix_inv_bilinear_entry_of_entries_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bilinear_entry_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {v w : ℝ × M → ι → ℝ}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z : ℝ × M => w z j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        ∑ i : ι, v z i *
          ((show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
            Matrix ι ι ℝ).mulVec (w z) i) K := by
  exact
    localFrameGramMatrix_inv_bilinear_entry_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hv hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hw

/-- Quantitative compact local-frame bridge for inverse-Gram bilinear contractions. -/
theorem localFrameGramMatrix_inv_bilinear_entry_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB GH : ι → ι → ℝ} {Bw Hw : ι → ℝ}
    {v w : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z : ℝ × M => w z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := ℝ) δ Bv GB Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB GH Bw Hw)
        α
        (fun z : ℝ × M =>
          ∑ i : ι, v z i *
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ).mulVec (w z) i) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_inv_bilinear_entry_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (v := v) (w := w) hBv hGH hv hG hw hδpos hdet

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_bilinear_entry_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB GH : ι → ι → ℝ} {Bw Hw : ι → ℝ}
    {v w : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hGH : ∀ i j, 0 ≤ GH i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z : ℝ × M => w z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := ℝ) δ Bv GB Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB GH Bw Hw)
        α
        (fun z : ℝ × M =>
          ∑ i : ι, v z i *
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ).mulVec (w z) i) K := by
  refine localFrameGramMatrix_inv_bilinear_entry_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hBv hGH hv ?_ hw
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα (hGholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for inverse-Gram bilinear
contractions. -/
theorem localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bw Hw : ι → ℝ} {v w : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z : ℝ × M => w z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := ℝ) δ Bv GB Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
          (fun i j => (Lgram i j : ℝ)) Bw Hw)
        α
        (fun z : ℝ × M =>
          ∑ i : ι, v z i *
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ).mulVec (w z) i) K := by
  refine localFrameGramMatrix_inv_bilinear_entry_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hBv
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hv ?_ hw
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-Gram
bilinear contractions. -/
theorem localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bw Hw : ι → ℝ} {v w : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z : ℝ × M => w z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := ℝ) δ Bv GB Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
          (fun i j => (Lgram i j : ℝ)) Bw Hw)
        α
        (fun z : ℝ × M =>
          ∑ i : ι, v z i *
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ).mulVec (w z) i) K := by
  exact
    localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hv hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hw

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-Gram
bilinear contractions. -/
theorem localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Bv Hv : ι → ℝ} {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {Bw Hw : ι → ℝ} {v w : ℝ × M → ι → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z : ℝ × M => v z i) K)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z : ℝ × M => w z j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := ℝ) δ Bv GB Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := ℝ) δ Bv Hv GB
          (fun i j => (Lgram i j : ℝ)) Bw Hw)
        α
        (fun z : ℝ × M =>
          ∑ i : ι, v z i *
            ((show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
              Matrix ι ι ℝ).mulVec (w z) i) K := by
  exact
    localFrameGramMatrix_inv_bilinear_entry_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hBv hv hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hw

/-- If the local-frame Gram entries and a four-index coefficient array have parabolic
`C^{0,α}` control on a compact time-space set contained in a trivialization base, then the
inverse-principal contraction against the Gram matrix has parabolic `C^{0,α}` control there. -/
theorem localFrameGramMatrix_inv_two_index_contract_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          ∑ a : ι, ∑ c : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) a c * Hc z a c i j :
          Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_two_index_contract
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (T := Hc) hG hHc hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
parabolic control of a four-index coefficient array, lift to parabolic `C^{0,α}` control of the
inverse-principal contraction on compact time-space sets contained in a trivialization base. -/
theorem localFrameGramMatrix_inv_two_index_contract_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B Hgram : ι → ι → ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ Hgram i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        Hgram i j * (dist x y) ^ α)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          ∑ a : ι, ∑ c : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) a c * Hc z a c i j :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hHc
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hB_nonneg i j) (hH_nonneg i j) hα (hB i j) (hholder i j)

/-- Unit-diameter spatial-Lipschitz local-frame bridge for the inverse-principal contraction
`g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          ∑ a : ι, ∑ c : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) a c * Hc z a c i j :
          Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_of_entries_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase ?_ hHc
  intro i j
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := GB i j) (K := Lgram i j)
    hα_nonneg hα_le_one (hGB_nonneg i j) (hGbound i j) (hL i j) hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for the inverse-principal
contraction `g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          ∑ a : ι, ∑ c : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) a c * Hc z a c i j :
          Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hHc

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the inverse-principal
contraction `g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j, ParabolicC0AlphaOn α (fun z : ℝ × M => Hc z a c i j) K) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × M =>
        (fun i j =>
          ∑ a : ι, ∑ c : ι,
            ((show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                Matrix ι ι ℝ) a c * Hc z a c i j :
          Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hHc

/-- Quantitative compact local-frame bridge for the inverse-principal contraction
`g^{ab}H_abij`.  The geometric Gram determinant theorem supplies a positive determinant lower
bound `δ`, and the finite-dimensional inverse-contraction estimate exposes explicit bounded
`C^{0,α}` constants. -/
theorem localFrameGramMatrix_inv_two_index_contract_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB GH HB HH i j)
        α
        (fun z : ℝ × M =>
          (fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j :
            Matrix ι ι ℝ)) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_inv_two_index_contract_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (T := Hc) hGH hHB hHH hG hHc hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
explicit parabolic controls for a four-index coefficient array, yield the quantitative compact
local-frame inverse-principal contraction estimate. -/
theorem localFrameGramMatrix_inv_two_index_contract_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB GH HB HH i j)
        α
        (fun z : ℝ × M =>
          (fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH hHB hHH ?_ hHc
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hB i j) (hGH i j) hα (hholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for the inverse-principal
contraction `g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ}
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) HB HH i j)
        α
        (fun z : ℝ × M =>
          (fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hHB hHH ?_ hHc
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for the
inverse-principal contraction `g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ}
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) HB HH i j)
        α
        (fun z : ℝ × M =>
          (fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hHc

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the
inverse-principal contraction `g^{ab}H_abij`. -/
theorem localFrameGramMatrix_inv_two_index_contract_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ}
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ GB HB i j)
        (∑ i : ι, ∑ j : ι,
          matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) HB HH i j)
        α
        (fun z : ℝ × M =>
          (fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hHc

/-- Compact local-frame bridge for the function-level bounded difference of inverse-principal
contractions, comparing the geometric local-frame Gram matrix with an arbitrary comparison
primitive input. -/
theorem localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {HB : ι → ι → ι → ι → ℝ}
    {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hGctrl : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c,
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 a c‖ ≤ C a c)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_two_index_contract_bounded_sub_le_const_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (T := Hc) (U := Kc)
    hK hα hGctrl hNctrl hdetG_ne hdetN_ne hHB hGbound hNbound hKc hGdiff hHdiff

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {HB : ι → ι → ι → ι → ℝ}
    {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase ?_ hNctrl hdetN_ne hHB ?_
    hNbound hKc hGdiff hHdiff
  · intro i j
    exact of_snd_holder (s := K) (α := α)
      (hC_nonneg i j) (hGH i j) hα.le (hGbound i j) (hGholder i j)
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Unit-diameter spatial-Lipschitz local-frame bridge for the function-level bounded difference
of inverse-principal contractions. -/
theorem localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase ?_ hNctrl hdetN_ne hHB ?_
    hNbound hKc hGdiff hHdiff
  · intro i j
    exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
      (s := K) (α := α) (B := C i j) (K := Lgram i j)
      hα_pos.le hα_le_one (hC_nonneg i j) (hGbound i j) (hL i j) hdiam
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse-principal contractions. -/
theorem localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hHB hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hNbound hKc hGdiff hHdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse-principal contractions. -/
theorem localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hHB hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hNbound hKc hGdiff hHdiff

/-- Compact local-frame bridge for parabolic `C^{0,α}` control of inverse-principal contraction
differences, comparing the geometric local-frame Gram matrix with an arbitrary comparison
primitive input. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (matrixInvTwoIndexContractDiffHolderConst (𝕜 := ℝ) δ C GH HB HH)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_two_index_contract_sub_with_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (T := Hc) (U := Kc)
    hK hα hC_nonneg hGH hHB hHH hG hN hHc hKc hdetG_ne hdetN_ne hGdiff hHdiff

/-- Entrywise-difference compact local-frame bridge for inverse-principal contractions against a
four-index coefficient array. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd HB HBd)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_two_index_contract_sub_with_entrywise_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (T := Hc) (U := Kc)
    hK hα hC_nonneg hGH hGd hGHd hHB hHH hHBd hHHd
    hG hN hGdiff hKc hHdiff hdetG_ne hdetN_ne

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd HB HBd)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hGd hGHd hHB hHH hHBd
    hHHd ?_ hN hGdiff hKc hHdiff hdetN_ne
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_two_index_contract_sub_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (matrixInvTwoIndexContractDiffHolderConst (𝕜 := ℝ) δ C GH HB HH)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hHB hHH ?_
    hN hHc hKc hdetN_ne hGdiff hHdiff
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Unit-diameter spatial-Lipschitz local-frame bridge for entrywise inverse-principal
contraction differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd HB HBd)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hGd hGHd hHB hHH hHBd hHHd ?_
    hN hGdiff hKc hHdiff hdetN_ne
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for entrywise inverse-principal
contraction differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd HB HBd)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hHB hHH hHBd hHHd hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hGdiff hKc hHdiff hdetN_ne

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for entrywise
inverse-principal contraction differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd HB HBd)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hHB hHH hHBd hHHd hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hGdiff hKc hHdiff hdetN_ne

/-- Unit-diameter spatial-Lipschitz local-frame bridge for inverse-principal contraction
differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (matrixInvTwoIndexContractDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) HB HH)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_inv_two_index_contract_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hHB hHH ?_
    hN hHc hKc hdetN_ne hGdiff hHdiff
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-principal
contraction differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (matrixInvTwoIndexContractDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) HB HH)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hHc hKc hdetN_ne hGdiff hHdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-principal
contraction differences. -/
theorem localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {HB HH : ι → ι → ι → ι → ℝ} {ηG : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := ℝ) δ C HB ηG ηH)
        (matrixInvTwoIndexContractDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) HB HH)
        α
        (fun z : ℝ × M =>
          ((fun i j =>
            ∑ a : ι, ∑ c : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) a c * Hc z a c i j) :
            Matrix ι ι ℝ) -
          ((fun i j =>
            ∑ a : ι, ∑ c : ι, ((N z)⁻¹ : Matrix ι ι ℝ) a c *
              Kc z a c i j) :
            Matrix ι ι ℝ)) K := by
  exact
    localFrameGramMatrix_inv_two_index_contract_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hHc hKc hdetN_ne hGdiff hHdiff

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

/-- Unit-diameter spatial-Lipschitz local-frame bridge for inverse-Gram Christoffel-type
contractions. -/
theorem localFrameGramMatrix_inv_christoffel_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
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
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := GB i j) (K := Lgram i j)
    hα_nonneg hα_le_one (hGB_nonneg i j) (hGbound i j) (hL i j) hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type contractions. -/
theorem localFrameGramMatrix_inv_christoffel_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
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
  exact
    localFrameGramMatrix_inv_christoffel_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hD

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type contractions. -/
theorem localFrameGramMatrix_inv_christoffel_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    (hGB_nonneg : ∀ i j, 0 ≤ GB i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
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
  exact
    localFrameGramMatrix_inv_christoffel_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hGB_nonneg hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hD

/-- Quantitative compact local-frame bridge for the inverse-Gram Christoffel-type contraction.
The geometric Gram determinant theorem supplies a positive determinant lower bound `δ`, and the
finite-dimensional inverse-Christoffel estimate exposes explicit bounded `C^{0,α}` constants. -/
theorem localFrameGramMatrix_inv_christoffel_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hG : ∀ i j,
      ParabolicC0AlphaWith (GB i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB i j k)
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB GH DB DH i j k)
        α
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
  refine ⟨δ, hδpos, hdet, ?_⟩
  exact matrix_inv_christoffel_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (D := D) hGH hDB hDH hG hDctrl hδpos hdet

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
explicit parabolic controls for a three-index derivative array, yield the quantitative compact
local-frame inverse-Gram Christoffel estimate. -/
theorem localFrameGramMatrix_inv_christoffel_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB i j k)
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB GH DB DH i j k)
        α
        (fun z i j k =>
          (2 : ℝ)⁻¹ *
            ∑ l : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) i l *
                (D z j k l + D z k j l - D z l j k)) K := by
  refine localFrameGramMatrix_inv_christoffel_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH hDB hDH ?_ hDctrl
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hB i j) (hGH i j) hα (hholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type contractions. -/
theorem localFrameGramMatrix_inv_christoffel_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB i j k)
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) DB DH i j k)
        α
        (fun z i j k =>
          (2 : ℝ)⁻¹ *
            ∑ l : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) i l *
                (D z j k l + D z k j l - D z l j k)) K := by
  refine localFrameGramMatrix_inv_christoffel_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hDB hDH ?_ hDctrl
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type contractions. -/
theorem localFrameGramMatrix_inv_christoffel_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB i j k)
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) DB DH i j k)
        α
        (fun z i j k =>
          (2 : ℝ)⁻¹ *
            ∑ l : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) i l *
                (D z j k l + D z k j l - D z l j k)) K := by
  exact
    localFrameGramMatrix_inv_christoffel_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hDB hDH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hDctrl

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type contractions. -/
theorem localFrameGramMatrix_inv_christoffel_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    (hDctrl : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α (fun z : ℝ × M => D z i j k) K) :
    ∃ δ > 0,
      (∀ ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
      ParabolicC0AlphaWith
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB i j k)
        (∑ i : ι, ∑ j : ι, ∑ k : ι,
          matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
            (fun i j => (Lgram i j : ℝ)) DB DH i j k)
        α
        (fun z i j k =>
          (2 : ℝ)⁻¹ *
            ∑ l : ι,
              ((show Matrix ι ι ℝ from
                  CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                  Matrix ι ι ℝ) i l *
                (D z j k l + D z k j l - D z l j k)) K := by
  exact
    localFrameGramMatrix_inv_christoffel_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hDB hDH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hDctrl

/-- Compact local-frame bridge for the function-level bounded difference of inverse-Gram
Christoffel-type arrays, comparing the geometric local-frame Gram matrix with an arbitrary
comparison primitive input. -/
theorem localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {DB : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hGctrl : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c,
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 a c‖ ≤ C a c)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_christoffel_bounded_sub_le_const_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr)
    hK hα hGctrl hNctrl hdetG_ne hdetN_ne hGbound hNbound hE hηD hGdiff hDdiff

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase ?_ hNctrl hdetN_ne ?_
    hNbound hE hηD hGdiff hDdiff
  · intro i j
    exact of_snd_holder (s := K) (α := α)
      (hC_nonneg i j) (hGH i j) hα.le (hGbound i j) (hGholder i j)
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Unit-diameter spatial-Lipschitz local-frame bridge for the function-level bounded difference
of inverse-Gram Christoffel-type arrays. -/
theorem localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase ?_ hNctrl hdetN_ne ?_
    hNbound hE hηD hGdiff hDdiff
  · intro i j
    exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
      (s := K) (α := α) (B := C i j) (K := Lgram i j)
      hα_pos.le hα_le_one (hC_nonneg i j) (hGbound i j) (hL i j) hdiam
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse-Gram Christoffel-type arrays. -/
theorem localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hNbound hE hηD hGdiff hDdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the function-level bounded
difference of inverse-Gram Christoffel-type arrays. -/
theorem localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hNbound hE hηD hGdiff hDdiff

/-- Compact local-frame bridge for parabolic `C^{0,α}` control of inverse-Gram Christoffel-type
array differences, comparing the geometric local-frame Gram matrix with an arbitrary comparison
primitive input. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => D z i j k) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (matrixInvChristoffelDiffHolderConst (𝕜 := ℝ) δ C GH DB DH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_christoffel_sub_with_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr)
    hK hα hC_nonneg hGH hDB hDH hG hN hD hEarr hdetG_ne hdetN_ne
    hηD hGdiff hDdiff

/-- Entrywise-difference compact local-frame bridge for inverse-Christoffel arrays. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {DB DH DDB DDH : ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hDDB : ∀ i j k, 0 ≤ DDB i j k) (hDDH : ∀ i j k, 0 ≤ DDH i j k)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hDdiff : ∀ i j k,
      ParabolicC0AlphaWith (DDB i j k) (DDH i j k) α
        (fun z : ℝ × M => D z i j k - Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd DB DH DDB DDH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact matrix_inv_christoffel_sub_with_entrywise_of_isCompact_det_ne_zero
    (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr)
    hK hα hC_nonneg hGH hGd hGHd hDB hDH hDDB hDDH
    hG hN hGdiff hEarr hDdiff hdetG_ne hdetN_ne

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {DB DH DDB DDH : ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hDDB : ∀ i j k, 0 ≤ DDB i j k) (hDDH : ∀ i j k, 0 ≤ DDH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hDdiff : ∀ i j k,
      ParabolicC0AlphaWith (DDB i j k) (DDH i j k) α
        (fun z : ℝ × M => D z i j k - Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd DB DH DDB DDH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hGd hGHd hDB hDH hDDB
    hDDH ?_ hN hGdiff hEarr hDdiff hdetN_ne
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_inv_christoffel_sub_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => D z i j k) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (matrixInvChristoffelDiffHolderConst (𝕜 := ℝ) δ C GH DB DH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hDB hDH ?_
    hN hD hEarr hdetN_ne hηD hGdiff hDdiff
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Unit-diameter spatial-Lipschitz local-frame bridge for entrywise inverse-Christoffel array
differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hDDB : ∀ i j k, 0 ≤ DDB i j k) (hDDH : ∀ i j k, 0 ≤ DDH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hDdiff : ∀ i j k,
      ParabolicC0AlphaWith (DDB i j k) (DDH i j k) α
        (fun z : ℝ × M => D z i j k - Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd DB DH DDB DDH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hGd hGHd hDB hDH hDDB hDDH ?_
    hN hGdiff hEarr hDdiff hdetN_ne
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for entrywise inverse-Christoffel
array differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hDDB : ∀ i j k, 0 ≤ DDB i j k) (hDDH : ∀ i j k, 0 ≤ DDH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hDdiff : ∀ i j k,
      ParabolicC0AlphaWith (DDB i j k) (DDH i j k) α
        (fun z : ℝ × M => D z i j k - Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd DB DH DDB DDH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hDB hDH hDDB hDDH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hGdiff hEarr hDdiff hdetN_ne

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for entrywise
inverse-Christoffel array differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C Gd GHd : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hDDB : ∀ i j k, 0 ≤ DDB i j k) (hDDH : ∀ i j k, 0 ≤ DDH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hDdiff : ∀ i j k,
      ParabolicC0AlphaWith (DDB i j k) (DDH i j k) α
        (fun z : ℝ × M => D z i j k - Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := ℝ) δ C Gd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd DB DH DDB DDH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hDB hDH hDDB hDDH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hGdiff hEarr hDdiff hdetN_ne

/-- Unit-diameter spatial-Lipschitz local-frame bridge for inverse-Gram Christoffel-type array
differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => D z i j k) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (matrixInvChristoffelDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  refine localFrameGramMatrix_inv_christoffel_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hDB hDH ?_
    hN hD hEarr hdetN_ne hηD hGdiff hDdiff
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for inverse-Gram Christoffel-type
array differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => D z i j k) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (matrixInvChristoffelDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hDB hDH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hD hEarr hdetN_ne hηD hGdiff hDdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for inverse-Gram
Christoffel-type array differences. -/
theorem localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M}
    (hK : IsCompact K) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {ηG ηD : ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => D z i j k) K)
    (hEarr : ∀ i j k,
      ParabolicC0AlphaWith (DB i j k) (DH i j k) α
        (fun z : ℝ × M => Earr z i j k) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := ℝ) δ C DB ηD ηG)
        (matrixInvChristoffelDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH)
        α
        (fun z : ℝ × M =>
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι,
                ((show Matrix ι ι ℝ from
                    CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)⁻¹ :
                    Matrix ι ι ℝ) i l *
                  (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : ℝ)⁻¹ *
              ∑ l : ι, ((N z)⁻¹ : Matrix ι ι ℝ) i l *
                (Earr z j k l + Earr z k j l - Earr z l j k))) K := by
  exact
    localFrameGramMatrix_inv_christoffel_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hDB hDH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hD hEarr hdetN_ne hηD hGdiff hDdiff

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

/-- On a unit parabolic-diameter compact time-space set, spatial Lipschitz Gram-entry estimates,
together with parabolic control of the first- and second-derivative coefficient arrays, give
parabolic `C^{0,α}` control of the schematic local Ricci-DeTurck RHS for every `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
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
  exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one
    (s := K) (α := α) (B := B i j) (K := L i j)
    hα_nonneg hα_le_one (hB_nonneg i j) (hB i j) (hL i j) hdiam

/-- On a compact time-space subset of a closed parabolic ball of diameter at most one, spatial
Lipschitz Gram-entry estimates and parabolic control of the derivative coefficient arrays give
parabolic `C^{0,α}` control of the schematic local Ricci-DeTurck RHS for every `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
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
  exact
    (of_snd_lipschitzOnWith (s := K) (B := B i j) (K := L i j)
      (hB_nonneg i j) (hB i j) (hL i j)).mono_exponent_of_subset_closedBall
        hα_nonneg hα_le_one hs hR

/-- On a compact time-space subset of a closed parabolic cylinder of diameter at most one,
spatial Lipschitz Gram-entry estimates and parabolic control of the derivative coefficient arrays
give parabolic `C^{0,α}` control of the schematic local Ricci-DeTurck RHS for every
`0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {B : ι → ι → ℝ} {L : ι → ι → ℝ≥0}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ B i j)
    (hL : ∀ i j,
      LipschitzOnWith (L i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
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
  exact
    (of_snd_lipschitzOnWith (s := K) (B := B i j) (K := L i j)
      (hB_nonneg i j) (hB i j) (hL i j)).mono_exponent_of_subset_closedCylinder
        hα_nonneg hα_le_one hs hdiam

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

/-- Quantitative finite-family compact local-frame bridge for the schematic local Ricci-DeTurck
coordinate right-hand side.  One Gram determinant lower bound is shared across the whole finite
family of trivializations. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_family_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hKbase : ∀ r ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    {GB GH : ρ → ι → ι → ℝ}
    {DB DH : ρ → ι → ι → ι → ℝ}
    {HB HH : ρ → ι → ι → ι → ι → ℝ}
    (hGH : ∀ r i j, 0 ≤ GH r i j)
    (hDB : ∀ r i j k, 0 ≤ DB r i j k) (hDH : ∀ r i j k, 0 ≤ DH r i j k)
    (hHB : ∀ r a c i j, 0 ≤ HB r a c i j)
    (hHH : ∀ r a c i j, 0 ≤ HH r a c i j)
    {D : ρ → ℝ × M → ι → ι → ι → ℝ}
    {Hc : ρ → ℝ × M → ι → ι → ι → ι → ℝ}
    (hG : ∀ r i j,
      ParabolicC0AlphaWith (GB r i j) (GH r i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2 i j)
        K)
    (hDctrl : ∀ r i j k,
      ParabolicC0AlphaWith (DB r i j k) (DH r i j k) α
        (fun z : ℝ × M => D r z i j k) K)
    (hHc : ∀ r a c i j,
      ParabolicC0AlphaWith (HB r a c i j) (HH r a c i j) α
        (fun z : ℝ × M => Hc r z a c i j) K) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : ι, ∑ j : ι,
            (matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ (GB r) (HB r) i j +
              christoffelQuadraticRicciEntryBoundConst
                (fun a c d =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ (GB r) (DB r) a c d)
                i j))
          (∑ i : ι, ∑ j : ι,
            (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ (GB r) (GH r)
                (HB r) (HH r) i j +
              christoffelQuadraticRicciEntryHolderConst
                (fun a c d =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ (GB r) (DB r) a c d)
                (fun a c d =>
                  matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ (GB r) (GH r)
                    (DB r) (DH r) a c d)
                i j))
          α
          (fun z : ℝ × M =>
            (fun i j =>
              let Γ : ι → ι → ι → ℝ := fun a c d =>
                (2 : ℝ)⁻¹ *
                  ∑ l : ι,
                    ((show Matrix ι ι ℝ from
                        CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)⁻¹ :
                        Matrix ι ι ℝ) a l *
                      (D r z c d l + D r z d c l - D r z l c d)
              (∑ a : ι, ∑ c : ι,
                  ((show Matrix ι ι ℝ from
                      CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)⁻¹ :
                      Matrix ι ι ℝ) a c * Hc r z a c i j) +
                ((∑ a : ι, ∑ c : ι, Γ a i j * Γ c a c) -
                  (∑ a : ι, ∑ c : ι, Γ a i c * Γ c a j)) :
              Matrix ι ι ℝ)) K := by
  rcases localFrameGramMatrix_det_family_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact ricciDeTurck_schematic_with
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2))
    (D := D r) (H := Hc r)
    (hGH r) (hDB r) (hDH r) (hHB r) (hHH r)
    (hG r) (hDctrl r) (hHc r) hδpos (hdet r)

/-- Finite-family spatial-Hölder local-frame bridge for the quantitative schematic
Ricci-DeTurck RHS.  The spatial Gram-entry bounds are packaged into the family
`C^{0,α}` hypotheses before selecting the shared Gram determinant lower bound. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_family_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    {ρ : Type*} [Fintype ρ]
    (e : ρ → Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [∀ r, MemTrivializationAtlas (e r)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ρ → Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ r ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ (e r).baseSet)
    {GB GH : ρ → ι → ι → ℝ}
    {DB DH : ρ → ι → ι → ι → ℝ}
    {HB HH : ρ → ι → ι → ι → ι → ℝ}
    (hGH : ∀ r i j, 0 ≤ GH r i j)
    (hDB : ∀ r i j k, 0 ≤ DB r i j k) (hDH : ∀ r i j k, 0 ≤ DH r i j k)
    (hHB : ∀ r a c i j, 0 ≤ HB r a c i j)
    (hHH : ∀ r a c i j, 0 ≤ HH r a c i j)
    (hB : ∀ r i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) x i j‖ ≤ GB r i j)
    (hholder : ∀ r i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) y i j‖ ≤
        GH r i j * (dist x y) ^ α)
    {D : ρ → ℝ × M → ι → ι → ι → ℝ}
    {Hc : ρ → ℝ × M → ι → ι → ι → ι → ℝ}
    (hDctrl : ∀ r i j k,
      ParabolicC0AlphaWith (DB r i j k) (DH r i j k) α
        (fun z : ℝ × M => D r z i j k) K)
    (hHc : ∀ r a c i j,
      ParabolicC0AlphaWith (HB r a c i j) (HH r a c i j) α
        (fun z : ℝ × M => Hc r z a c i j) K) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × M⦄, z ∈ K →
        δ ≤ ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : ι, ∑ j : ι,
            (matrixInvTwoIndexContractEntryBoundConst (𝕜 := ℝ) δ (GB r) (HB r) i j +
              christoffelQuadraticRicciEntryBoundConst
                (fun a c d =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ (GB r) (DB r) a c d)
                i j))
          (∑ i : ι, ∑ j : ι,
            (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ (GB r) (GH r)
                (HB r) (HH r) i j +
              christoffelQuadraticRicciEntryHolderConst
                (fun a c d =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ (GB r) (DB r) a c d)
                (fun a c d =>
                  matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ (GB r) (GH r)
                    (DB r) (DH r) a c d)
                i j))
          α
          (fun z : ℝ × M =>
            (fun i j =>
              let Γ : ι → ι → ι → ℝ := fun a c d =>
                (2 : ℝ)⁻¹ *
                  ∑ l : ι,
                    ((show Matrix ι ι ℝ from
                        CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)⁻¹ :
                        Matrix ι ι ℝ) a l *
                      (D r z c d l + D r z d c l - D r z l c d)
              (∑ a : ι, ∑ c : ι,
                  ((show Matrix ι ι ℝ from
                      CovariantDerivative.localFrameGramMatrix (I := I) (e r) (b r) z.2)⁻¹ :
                      Matrix ι ι ℝ) a c * Hc r z a c i j) +
                ((∑ a : ι, ∑ c : ι, Γ a i j * Γ c a c) -
                  (∑ a : ι, ∑ c : ι, Γ a i c * Γ c a j)) :
              Matrix ι ι ℝ)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_family_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH hDB hDH hHB hHH ?_ hDctrl hHc
  intro r i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hB r i j) (hGH r i j) hα (hholder r i j)

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries, together with
explicit parabolic controls for the first- and second-derivative coefficient arrays, yield the
quantitative compact local-frame schematic Ricci-DeTurck estimate. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 ≤ α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    {HB HH : ι → ι → ι → ι → ℝ}
    (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄, y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
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
  refine localFrameGramMatrix_ricciDeTurck_schematic_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase hGH hDB hDH hHB hHH ?_ hDctrl hHc
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hB i j) (hGH i j) hα (hholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for the schematic
Ricci-DeTurck RHS.  The Gram-entry Lipschitz constants serve as the explicit parabolic Holder
constants after lowering to any exponent `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
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
          (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
              (fun i j => (Lgram i j : ℝ)) HB HH i j +
            christoffelQuadraticRicciEntryHolderConst
              (fun a c d =>
                matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB a c d)
              (fun a c d =>
                matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
                  (fun i j => (Lgram i j : ℝ)) DB DH a c d)
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
  refine localFrameGramMatrix_ricciDeTurck_schematic_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hKbase
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hDB hDH hHB hHH ?_ hDctrl hHc
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := GB i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hB i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_nonneg hα_le_one hdiam

/-- Quantitative closed-parabolic-ball spatial-Lipschitz local-frame bridge for the schematic
Ricci-DeTurck RHS.  The Gram-entry Lipschitz constants serve as the explicit parabolic Holder
constants after lowering to any exponent `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
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
          (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
              (fun i j => (Lgram i j : ℝ)) HB HH i j +
            christoffelQuadraticRicciEntryHolderConst
              (fun a c d =>
                matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB a c d)
              (fun a c d =>
                matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
                  (fun i j => (Lgram i j : ℝ)) DB DH a c d)
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
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hDB hDH hHB hHH hB hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hDctrl hHc

/-- Quantitative closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the schematic
Ricci-DeTurck RHS.  The Gram-entry Lipschitz constants serve as the explicit parabolic Holder
constants after lowering to any exponent `0 ≤ α ≤ 1`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {GB : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    (hDB : ∀ i j k, 0 ≤ DB i j k) (hDH : ∀ i j k, 0 ≤ DH i j k)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hB : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ GB i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    {D : ℝ × M → ι → ι → ι → ℝ}
    {Hc : ℝ × M → ι → ι → ι → ι → ℝ}
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
          (matrixInvTwoIndexContractEntryHolderConst (𝕜 := ℝ) δ GB
              (fun i j => (Lgram i j : ℝ)) HB HH i j +
            christoffelQuadraticRicciEntryHolderConst
              (fun a c d =>
                matrixInvChristoffelEntryBoundConst (𝕜 := ℝ) δ GB DB a c d)
              (fun a c d =>
                matrixInvChristoffelEntryHolderConst (𝕜 := ℝ) δ GB
                  (fun i j => (Lgram i j : ℝ)) DB DH a c d)
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
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_nonneg hα_le_one hKbase
      hDB hDH hHB hHH hB hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hDctrl hHc

/-- Compact local-frame bridge for the function-level bounded difference of two schematic
Ricci-DeTurck coordinate right-hand sides, one built from the geometric local-frame Gram matrix
and one from an arbitrary comparison primitive input.  The local-frame Gram determinant supplies
the first nonvanishing determinant hypothesis; the comparison determinant is supplied explicitly.
-/
theorem localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {DB : ι → ι → ι → ℝ}
    {HB : ι → ι → ι → ι → ℝ} {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hGctrl : ∀ i j,
      ParabolicC0AlphaOn α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hDB : ∀ a c d, 0 ≤ DB a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c,
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 a c‖ ≤ C a c)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hD : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖D z a c d‖ ≤ DB a c d)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero
    (Kdom := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr) (Hc := Hc) (Kc := Kc)
    hK hα hGctrl hNctrl hdetG_ne hdetN_ne hDB hHB hGbound hNbound
    hD hE hKc hηD hGdiff hDdiff hHdiff

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB : ι → ι → ι → ℝ}
    {HB : ι → ι → ι → ι → ℝ} {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hDB : ∀ a c d, 0 ≤ DB a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hD : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖D z a c d‖ ≤ DB a c d)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase ?_ hNctrl hdetN_ne hDB hHB ?_
    hNbound hD hE hKc hηD hGdiff hDdiff hHdiff
  · intro i j
    exact of_snd_holder (s := K) (α := α)
      (hC_nonneg i j) (hGH i j) hα.le (hGbound i j) (hGholder i j)
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Unit-diameter spatial-Lipschitz local-frame bridge for the function-level bounded difference
of schematic Ricci-DeTurck coordinate right-hand sides. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {HB : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hDB : ∀ a c d, 0 ≤ DB a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hD : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖D z a c d‖ ≤ DB a c d)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase ?_ hNctrl hdetN_ne
    hDB hHB ?_ hNbound hD hE hKc hηD hGdiff hDdiff hHdiff
  · intro i j
    exact of_snd_lipschitzOnWith_of_parabolicDistance_le_one (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      hα_pos.le hα_le_one (hC_nonneg i j) (hGbound i j) (hL i j) hdiam
  · intro z hz a c
    exact hGbound a c ⟨z, hz, rfl⟩

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for the function-level bounded
difference of schematic Ricci-DeTurck coordinate right-hand sides. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {HB : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hDB : ∀ a c d, 0 ≤ DB a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hD : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖D z a c d‖ ≤ DB a c d)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hDB hHB hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hNbound hD hE hKc hηD hGdiff hDdiff hHdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for the function-level bounded
difference of schematic Ricci-DeTurck coordinate right-hand sides. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB : ι → ι → ι → ℝ} {HB : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z : ℝ × M => N z i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hDB : ∀ a c d, 0 ≤ DB a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hNbound : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c, ‖N z a c‖ ≤ C a c)
    (hD : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖D z a c d‖ ≤ DB a c d)
    (hE : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d, ‖Earr z a c d‖ ≤ DB a c d)
    (hKc : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c i j, ‖Kc z a c i j‖ ≤ HB a c i j)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_bounded_sub_le_const_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hNctrl hdetN_ne hDB hHB hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hNbound hD hE hKc hηD hGdiff hDdiff hHdiff

/-- Compact local-frame bridge for parabolic `C^{0,α}` control of schematic Ricci-DeTurck RHS
differences, comparing the geometric local-frame Gram matrix with an arbitrary comparison
primitive input. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    {HB HH : ι → ι → ι → ι → ℝ} {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := ℝ) δ C GH DB DH HB HH)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact ricciDeTurckSchematicMatrix_sub_with_of_isCompact_det_ne_zero
    (Kdom := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr) (Hc := Hc) (Kc := Kc)
    hK hα hC_nonneg hGH hDB hDH hHB hHH hG hN hD hEarr hHc hKc
    hdetG_ne hdetN_ne hηD hGdiff hDdiff hHdiff

/-- Entrywise-difference compact local-frame bridge for parabolic `C^{0,α}` control of schematic
Ricci-DeTurck RHS differences, comparing the geometric local-frame Gram matrix with an arbitrary
comparison primitive input. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {DB DH DDB DDH : ι → ι → ι → ℝ}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hDDB : ∀ a c d, 0 ≤ DDB a c d) (hDDH : ∀ a c d, 0 ≤ DDH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hG : ∀ i j,
      ParabolicC0AlphaWith (C i j) (GH i j) α
        (fun z : ℝ × M => CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j)
        K)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hDdiff : ∀ a c d,
      ParabolicC0AlphaWith (DDB a c d) (DDH a c d) α
        (fun z : ℝ × M => D z a c d - Earr z a c d) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ C Gd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  have hdetG_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det ≠ 0 := by
    intro z hz
    exact CovariantDerivative.localFrameGramMatrix_det_ne_zero
      (I := I) (E := E) e b (hKbase hz)
  exact ricciDeTurckSchematicMatrix_sub_with_entrywise_of_isCompact_det_ne_zero
    (Kdom := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    (N := N) (D := D) (E := Earr) (Hc := Hc) (Kc := Kc)
    hK hα hC_nonneg hGH hGd hGHd hDB hDH hDDB hDDH hHB hHH hHBd hHHd
    hG hN hGdiff hD hEarr hDdiff hKc hHdiff hdetG_ne hdetN_ne

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH Gd GHd : ι → ι → ℝ} {DB DH DDB DDH : ι → ι → ι → ℝ}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hDDB : ∀ a c d, 0 ≤ DDB a c d) (hDDH : ∀ a c d, 0 ≤ DDH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hDdiff : ∀ a c d,
      ParabolicC0AlphaWith (DDB a c d) (DDH a c d) α
        (fun z : ℝ × M => D z a c d - Earr z a c d) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ C Gd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C GH Gd GHd DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hGd hGHd
    hDB hDH hDDB hDDH hHB hHH hHBd hHHd ?_ hN hGdiff
    hD hEarr hDdiff hKc hHdiff hdetN_ne
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Spatial-Hölder Gram-entry variant of
`localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_timeSpace_isCompact`. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C GH : ι → ι → ℝ} {DB DH : ι → ι → ι → ℝ}
    {HB HH : ι → ι → ι → ι → ℝ} {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j) (hGH : ∀ i j, 0 ≤ GH i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hGholder : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K → ∀ ⦃y : M⦄,
      y ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j -
          CovariantDerivative.localFrameGramMatrix (I := I) e b y i j‖ ≤
        GH i j * (dist x y) ^ α)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (GH i j) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := ℝ) δ C GH DB DH HB HH)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα hKbase hC_nonneg hGH hDB hDH hHB hHH ?_
    hN hD hEarr hHc hKc hdetN_ne hηD hGdiff hDdiff hHdiff
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := K) (α := α)
    (hGbound i j) (hGH i j) hα.le (hGholder i j)

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for schematic
Ricci-DeTurck RHS differences.  The Gram-entry Lipschitz constants become the parabolic Holder
constants after lowering to any exponent `0 < α ≤ 1`, matching compact comparison estimates on
small Picard patches. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH HB HH)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hDB hDH hHB hHH ?_
    hN hD hEarr hHc hKc hdetN_ne hηD hGdiff hDdiff hHdiff
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for schematic Ricci-DeTurck RHS
differences. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH HB HH)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hDB hDH hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hD hEarr hHc hKc hdetN_ne hηD hGdiff hDdiff hHdiff

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for schematic Ricci-DeTurck RHS
differences. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0}
    {DB DH : ι → ι → ι → ℝ} {HB HH : ι → ι → ι → ι → ℝ}
    {ηG ηD : ℝ} {ηH : ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hHc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Hc z a c i j) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hGdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K →
      ‖(show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) - N z‖ ≤ ηG)
    (hDdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ a c d,
      ‖D z a c d - Earr z a c d‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × M⦄, z ∈ K → ∀ i j,
      ‖((fun a c => Hc z a c i j) : Matrix ι ι ℝ) -
          ((fun a c => Kc z a c i j) : Matrix ι ι ℝ)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := ℝ) δ C DB HB ηG ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) DB DH HB HH)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_sub_with_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hDB hDH hHB hHH hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hD hEarr hHc hKc hdetN_ne hηD hGdiff hDdiff hHdiff

/-- Quantitative unit-diameter spatial-Lipschitz local-frame bridge for entrywise schematic
Ricci-DeTurck RHS differences. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {Gd GHd : ι → ι → ℝ}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hDDB : ∀ a c d, 0 ≤ DDB a c d) (hDDH : ∀ a c d, 0 ≤ DDH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hdiam : ∀ ⦃p : ℝ × M⦄, p ∈ K → ∀ ⦃q : ℝ × M⦄, q ∈ K →
      parabolicDistance p q ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hDdiff : ∀ a c d,
      ParabolicC0AlphaWith (DDB a c d) (DDH a c d) α
        (fun z : ℝ × M => D z a c d - Earr z a c d) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ C Gd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd
          DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  refine localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_timeSpace_isCompact
    (I := I) (E := E) e b hK hα_pos hKbase hC_nonneg
    (fun i j => NNReal.coe_nonneg (Lgram i j)) hGd hGHd
    hDB hDH hDDB hDDH hHB hHH hHBd hHHd ?_
    hN hGdiff hD hEarr hDdiff hKc hHdiff hdetN_ne
  intro i j
  exact
    (ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := K) (B := C i j)
      (K := Lgram i j)
      (f := fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
      (hGbound i j) (hL i j)).mono_exponent_of_parabolicDistance_le_one
        (NNReal.coe_nonneg (Lgram i j)) hα_pos.le hα_le_one hdiam

/-- Closed-parabolic-ball spatial-Lipschitz local-frame bridge for entrywise schematic
Ricci-DeTurck RHS differences. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedBall
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α R : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {Gd GHd : ι → ι → ℝ}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hDDB : ∀ a c d, 0 ≤ DDB a c d) (hDDH : ∀ a c d, 0 ≤ DDH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hDdiff : ∀ a c d,
      ParabolicC0AlphaWith (DDB a c d) (DDH a c d) α
        (fun z : ℝ × M => D z a c d - Earr z a c d) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ C Gd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd
          DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hDB hDH hDDB hDDH hHB hHH hHBd hHHd
      hGbound hL
      (by
        intro p hp q hq
        exact parabolicClosedBall.pair_parabolicDistance_le_one (hs hp) (hs hq) hR)
      hN hGdiff hD hEarr hDdiff hKc hHdiff hdetN_ne

/-- Closed-parabolic-cylinder spatial-Lipschitz local-frame bridge for entrywise schematic
Ricci-DeTurck RHS differences. -/
theorem localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_subset_closedCylinder
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α timeRadius spaceRadius : ℝ} {c : ℝ × M} (hK : IsCompact K)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hKbase : ∀ ⦃z : ℝ × M⦄, z ∈ K → z.2 ∈ e.baseSet)
    {C : ι → ι → ℝ} {Lgram : ι → ι → ℝ≥0} {Gd GHd : ι → ι → ℝ}
    {DB DH DDB DDH : ι → ι → ι → ℝ}
    {HB HH HBd HHd : ι → ι → ι → ι → ℝ}
    {N : ℝ × M → Matrix ι ι ℝ}
    {D Earr : ℝ × M → ι → ι → ι → ℝ}
    {Hc Kc : ℝ × M → ι → ι → ι → ι → ℝ}
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hGd : ∀ i j, 0 ≤ Gd i j) (hGHd : ∀ i j, 0 ≤ GHd i j)
    (hDB : ∀ a c d, 0 ≤ DB a c d) (hDH : ∀ a c d, 0 ≤ DH a c d)
    (hDDB : ∀ a c d, 0 ≤ DDB a c d) (hDDH : ∀ a c d, 0 ≤ DDH a c d)
    (hHB : ∀ a c i j, 0 ≤ HB a c i j) (hHH : ∀ a c i j, 0 ≤ HH a c i j)
    (hHBd : ∀ a c i j, 0 ≤ HBd a c i j)
    (hHHd : ∀ a c i j, 0 ≤ HHd a c i j)
    (hGbound : ∀ i j ⦃x : M⦄, x ∈ Prod.snd '' K →
      ‖CovariantDerivative.localFrameGramMatrix (I := I) e b x i j‖ ≤ C i j)
    (hL : ∀ i j,
      LipschitzOnWith (Lgram i j)
        (fun x : M => CovariantDerivative.localFrameGramMatrix (I := I) e b x i j)
        (Prod.snd '' K))
    (hs : K ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1)
    (hN : ∀ i j, ParabolicC0AlphaWith (C i j) (Lgram i j : ℝ) α
      (fun z : ℝ × M => N z i j) K)
    (hGdiff : ∀ i j,
      ParabolicC0AlphaWith (Gd i j) (GHd i j) α
        (fun z : ℝ × M =>
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2 i j - N z i j) K)
    (hD : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => D z a c d) K)
    (hEarr : ∀ a c d,
      ParabolicC0AlphaWith (DB a c d) (DH a c d) α
        (fun z : ℝ × M => Earr z a c d) K)
    (hDdiff : ∀ a c d,
      ParabolicC0AlphaWith (DDB a c d) (DDH a c d) α
        (fun z : ℝ × M => D z a c d - Earr z a c d) K)
    (hKc : ∀ a c i j,
      ParabolicC0AlphaWith (HB a c i j) (HH a c i j) α
        (fun z : ℝ × M => Kc z a c i j) K)
    (hHdiff : ∀ a c i j,
      ParabolicC0AlphaWith (HBd a c i j) (HHd a c i j) α
        (fun z : ℝ × M => Hc z a c i j - Kc z a c i j) K)
    (hdetN_ne : ∀ ⦃z : ℝ × M⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := ℝ) δ C Gd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := ℝ) δ C (fun i j => (Lgram i j : ℝ)) Gd GHd
          DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × M =>
          ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (Earr z) (Kc z)) K := by
  exact
    localFrameGramMatrix_ricciDeTurck_schematic_sub_with_entrywise_of_spatial_lipschitzOnWith_of_timeSpace_isCompact_of_parabolicDistance_le_one
      (I := I) (E := E) e b hK hα_pos hα_le_one hKbase
      hC_nonneg hGd hGHd hDB hDH hDDB hDDH hHB hHH hHBd hHHd
      hGbound hL
      (by
        intro p hp q hq
        exact (parabolicClosedCylinder.pair_parabolicDistance_le (hs hp) (hs hq)).trans hdiam)
      hN hGdiff hD hEarr hDdiff hKc hHdiff hdetN_ne

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
