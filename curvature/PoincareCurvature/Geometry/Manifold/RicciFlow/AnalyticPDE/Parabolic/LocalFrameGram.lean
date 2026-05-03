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
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
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
  exact matrix_inv_of_isCompact_det_ne_zero (K := K)
    (M := fun z : ℝ × M =>
      (show Matrix ι ι ℝ from CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
    hK hα hG
    (fun z hz =>
      CovariantDerivative.localFrameGramMatrix_det_ne_zero (I := I) (E := E) e b (hKbase hz))

/-- Spatial boundedness and spatial Holder estimates for local-frame Gram entries lift to
parabolic `C^{0,α}` control of the inverse Gram matrix on compact time-space sets contained in a
trivialization base. -/
theorem localFrameGramMatrix_inv_of_spatial_holder_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 2 E TM I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × M)} {α : ℝ} (hK : IsCompact K) (hα : 0 < α)
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
    (I := I) (E := E) e b hK hα hKbase ?_
  intro i j
  exact of_snd_holder (s := K) (α := α)
    (hB_nonneg i j) (hH_nonneg i j) hα.le (hB i j) (hholder i j)

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
