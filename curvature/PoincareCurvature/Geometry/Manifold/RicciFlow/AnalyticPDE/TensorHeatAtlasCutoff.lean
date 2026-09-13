import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteAtlasEquation

/-!
# Buffered cutoffs for the finite tensor-heat atlas

Each member of the subordinate partition has compact topological support
strictly inside its radius-adapted chart patch.  This file chooses a second
smooth cutoff which is identically one on a neighborhood of that compact
piece and remains supported in the patch.  Multiplying the uncut local
solution by the buffered cutoff gives a globally `C²` tensor field without
changing the actual partition-of-unity summand.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative
open PoincareCurvature.Bundle.Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- A smooth buffer which is one near one compact partition piece and whose
support stays inside the corresponding tensor-heat chart patch. -/
structure BufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) where
  cutoff : M → ℝ
  contMDiff_three : ContMDiff I 𝓘(ℝ) 3 cutoff
  compactSupport : HasCompactSupport cutoff
  support_subset : tsupport cutoff ⊆
    actualLocalTensorHeatPatch (I := I) (i : M) (A.radius (i : M))
  one_nhds : ∀ᶠ x in nhdsSet (A.cover.pieces i : Set M), cutoff x = 1

/-- Every atlas piece admits a buffered cutoff. -/
theorem nonempty_bufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : Nonempty (BufferedCutoff cov A i) := by
  let K : Set M := (A.cover.pieces i : Set M)
  let U : Set M := actualLocalTensorHeatPatch (I := I)
    (i : M) (A.radius (i : M))
  have hK : IsCompact K := (A.cover.pieces i).isCompact
  have hU : IsOpen U := isOpen_actualLocalTensorHeatPatch
    (I := I) (i : M) (A.radius (i : M))
  have hKU : K ⊆ U := A.cover.pieces_subset_domain i
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hfOne, hfZero, _hfIcc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior I hK.isClosed hKL
      (n := (3 : ℕ∞))
  have hsupp : Function.support (f : M → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hfZero x hxL)
  have hcompact : HasCompactSupport (f : M → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hLc hsupp
  have htsupp : tsupport (f : M → ℝ) ⊆ U := by
    calc
      tsupport (f : M → ℝ) = closure (Function.support (f : M → ℝ)) := rfl
      _ ⊆ closure L := closure_mono hsupp
      _ = L := hLc.isClosed.closure_eq
      _ ⊆ U := hLU
  exact ⟨⟨(f : M → ℝ), f.contMDiff, hcompact, htsupp, hfOne⟩⟩

/-- A fixed buffered cutoff for each selected atlas piece. -/
def bufferedCutoff
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) : BufferedCutoff cov A i :=
  Classical.choice (nonempty_bufferedCutoff cov A i)

theorem bufferedCutoff_eq_one_of_mem_piece
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) {x : M} (hx : x ∈ (A.cover.pieces i : Set M)) :
    (A.bufferedCutoff cov i).cutoff x = 1 :=
  (A.bufferedCutoff cov i).one_nhds.self_of_nhdsSet x hx

/-- The normalized local solution, extended to a globally `C²` tensor by
the buffered cutoff. -/
def bufferedLocalSolutionSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M))
      (A.normalizedLocalSolution cov i q) s)

/-- Every positive-time buffered slice is globally `C²`. -/
theorem contMDiff_bufferedLocalSolutionSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    {s : ℝ} (hs : s ∈ Ioc t₀ T) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (A.bufferedLocalSolutionSlice cov i q s x)) := by
  apply contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
    (I := I) (i : M) (trivializationAt E TM (i : M)) b
    (A.bufferedCutoff cov i).cutoff
    (normalizedTensorHeatCoefficientSlice (I := I)
      (i : M) (A.radius (i : M))
      (A.normalizedLocalSolution cov i q) s)
    (isOpen_actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)))
    (A.patch_subset_trivialization (i : M))
  · exact (A.bufferedCutoff cov i).contMDiff_three.of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  · exact (A.bufferedCutoff cov i).support_subset
  · exact contMDiffOn_normalizedTensorHeatCoefficientSlice
      (I := I) (i : M) (A.radius (i : M))
        (A.normalizedLocalSolution cov i q) A.alpha_pos hs

/-- The original partition-cutoff summand is exactly the partition function
times its globally regular buffered local solution. -/
theorem cutoffLocalSummand_eq_partition_smul_buffered
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) :
    cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (normalizedTensorHeatCoefficientSlice (I := I)
          (i : M) (A.radius (i : M))
          (A.normalizedLocalSolution cov i q) s) =
      (fun x => A.cover.partition i x •
        A.bufferedLocalSolutionSlice cov i q s x) := by
  funext x
  by_cases hψ : A.cover.partition i x = 0
  · simp only [cutoffLocalTensorOfMatrix]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [_root_.smul_apply, smul_eq_mul]
    simp [hψ]
  · have hxSupport : x ∈ Function.support (A.cover.partition i) := by
      simpa [Function.mem_support] using hψ
    have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure hxSupport
    have hχ := A.bufferedCutoff_eq_one_of_mem_piece cov i hxPiece
    simp [cutoffLocalTensorOfMatrix, bufferedLocalSolutionSlice, hχ]

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
