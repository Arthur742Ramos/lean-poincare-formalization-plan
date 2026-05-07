module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherMatrix
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalFrameGram

set_option linter.unusedSectionVars false

/-!
# Higher parabolic local-frame Gram bridges

This module specializes the higher parabolic matrix second-jet readout layer to local-frame
Gram matrices.  It keeps the higher dependency out of `LocalFrameGram.lean`, while exposing a
proof interface where the first- and second-derivative primitive arrays are chosen from second
jets of the Gram entries.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set
open scoped Bundle Manifold ContDiff Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC2AlphaNormLe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [ChartedSpace H E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [IsManifold I 2 E]
variable [RiemannianBundle (TangentSpace I : E → Type _)]
variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : E → Type _)]

local notation "TE" => (TangentSpace I : E → Type _)

set_option maxHeartbeats 1000000 in
/-- Compact local-frame Gram bridge with second-jet primitive arrays.  On a normed-vector
chart model, entrywise `C^{2+α,1+α/2}` control of the Gram matrix supplies chosen second jets.
Reading those jets along the local-frame basis vectors gives the first- and second-derivative
arrays used by the schematic Ricci-DeTurck RHS estimate.  The compact local-frame determinant
lower bound is chosen internally. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ} {R : ι → ι → ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaNormLe (R i j) α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K) :
    ∃ J : ∀ i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K,
      ∃ δ > 0,
        (∀ ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
        ParabolicC0AlphaNormLe
          (ricciDeTurckSchematicMatrixBoundConst (n := ι) δ R
            (firstDerivativeVectorRadius (X := E) (fun a : ι => b a) R)
            (secondDerivativeVectorRadius (X := E) (fun a : ι => b a) R))
          α
          (fun z : ℝ × E =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (fun a i j => (J i j).spaceDeriv z (b a))
              (fun a c i j => (J i j).spaceSecondDeriv z (b a) (b c))) K := by
  rcases CovariantDerivative.localFrameGramMatrix_det_exists_pos_norm_lower_bound_of_timeSpace_isCompact
      (I := I) (E := E) e b hK hKbase with
    ⟨δ, hδpos, hdet⟩
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_ricciDeTurckSchematicMatrix_of_metric_entries_directions
      (X := E) (α := α) (v := fun a : ι => b a) (R := R) (δ := δ) (s := K)
      (M := fun z : ℝ × E =>
        (show Matrix ι ι ℝ from
          CovariantDerivative.localFrameGramMatrix (I := I) e b z.2))
      hG hδpos hdet with
    ⟨J, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ⟩

end ParabolicC2AlphaNormLe

namespace ParabolicC2AlphaOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [ChartedSpace H E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [IsManifold I 2 E]
variable [RiemannianBundle (TangentSpace I : E → Type _)]
variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : E → Type _)]

local notation "TE" => (TangentSpace I : E → Type _)

set_option maxHeartbeats 1000000 in
/-- Qualitative compact local-frame Gram bridge with second-jet primitive arrays.  This is the
membership-only version of
`ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact`. -/
theorem exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_c0AlphaOn_of_entries_of_timeSpace_isCompact
    [IsContMDiffRiemannianBundle I 2 E TE]
    [ContMDiffVectorBundle 2 E TE I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TE → E)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {K : Set (ℝ × E)} {α : ℝ}
    (hK : IsCompact K)
    (hKbase : ∀ ⦃z : ℝ × E⦄, z ∈ K → z.2 ∈ e.baseSet)
    (hG : ∀ i j,
      ParabolicC2AlphaOn α
        (fun z : ℝ × E =>
          (show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K) :
    ∃ J : ∀ i j,
        ParabolicSecondJet
          (fun z : ℝ × E =>
            (show Matrix ι ι ℝ from
              CovariantDerivative.localFrameGramMatrix (I := I) e b z.2) i j) K,
      ∃ δ > 0,
        (∀ ⦃z : ℝ × E⦄, z ∈ K →
          δ ≤ ‖(show Matrix ι ι ℝ from
            CovariantDerivative.localFrameGramMatrix (I := I) e b z.2).det‖) ∧
        ParabolicC0AlphaOn α
          (fun z : ℝ × E =>
            ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
              (show Matrix ι ι ℝ from
                CovariantDerivative.localFrameGramMatrix (I := I) e b z.2)
              (fun a i j => (J i j).spaceDeriv z (b a))
              (fun a c i j => (J i j).spaceSecondDeriv z (b a) (b c))) K := by
  classical
  choose R _hR_nonneg hR using hG
  rcases
    ParabolicC2AlphaNormLe.exists_secondJet_localFrameGramMatrix_ricciDeTurckSchematicMatrix_of_entries_of_timeSpace_isCompact
      (I := I) e b (K := K) (α := α) (R := R) hK hKbase hR with
    ⟨J, δ, hδpos, hdet, hJ⟩
  exact ⟨J, δ, hδpos, hdet, hJ.c0AlphaOn⟩

end ParabolicC2AlphaOn
end AnalyticPDE
end RicciFlow
