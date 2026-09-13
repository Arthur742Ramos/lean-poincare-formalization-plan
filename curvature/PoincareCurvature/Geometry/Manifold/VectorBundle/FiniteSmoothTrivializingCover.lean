module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import PoincareCurvature.Geometry.Manifold.VectorBundle.FiniteTrivializingCover

/-!
# Finite smooth partitions subordinate to preferred bundle trivializations

For a vector bundle over a compact finite-dimensional manifold, this file
extracts a finite preferred trivializing cover and equips it with a smooth
partition of unity.  The topological supports of the partition functions are
compact, lie in their corresponding trivialization domains, and cover the
whole manifold.  These are the geometric data needed for an honest
local-to-global parabolic parametrix.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace PoincareCurvature
namespace Bundle.Trivialization

variable
  {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  [NormedAddCommGroup F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)]
  [FiberBundle F V]

/-- A finite smooth partition of unity subordinate to preferred bundle
trivializations. -/
structure FiniteSmoothPreferredTrivializingCover where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers I M Set.univ
  subordinate : partition.IsSubordinate
    (fun i : centers => (trivializationAt F V (i : M)).baseSet)

namespace FiniteSmoothPreferredTrivializingCover

variable {I}

/-- The finite type indexing the cover. -/
abbrev Index
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) :=
  C.centers

/-- Preferred bundle trivialization at a cover center. -/
def trivialization
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    Trivialization F (TotalSpace.proj : TotalSpace F V → M) :=
  trivializationAt F V (i : M)

instance memTrivializationAtlas_trivialization
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : MemTrivializationAtlas (C.trivialization i) := by
  unfold trivialization
  infer_instance

/-- Compact support piece belonging to one partition function. -/
def pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) : TopologicalSpace.Compacts M :=
  ⟨tsupport (C.partition i), isClosed_closure.isCompact⟩

@[simp]
theorem coe_pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) = tsupport (C.partition i) :=
  rfl

theorem pieces_subset_baseSet
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i : C.Index) :
    (C.pieces i : Set M) ⊆ (C.trivialization i).baseSet := by
  change tsupport (C.partition i) ⊆
    (trivializationAt F V (i : M)).baseSet
  exact C.subordinate i

/-- The compact supports of the finite partition cover the manifold. -/
theorem iUnion_pieces
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) :
    (⋃ i : C.Index, (C.pieces i : Set M)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := C.partition.exists_pos_of_mem (Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨i, subset_closure (Function.mem_support.2 (ne_of_gt hi))⟩

/-- Canonical compact pairwise overlaps. -/
def overlaps
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) : TopologicalSpace.Compacts M :=
  compactOverlap C.pieces i j

theorem overlaps_subset
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) ⊆
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  compactOverlap_subset C.pieces i j

@[simp]
theorem coe_overlaps
    (C : FiniteSmoothPreferredTrivializingCover I (F := F) (V := V))
    (i j : C.Index) :
    (C.overlaps i j : Set M) =
      (C.pieces i : Set M) ∩ (C.pieces j : Set M) :=
  coe_compactOverlap C.pieces i j

/-- Construct a finite smooth preferred trivializing cover from compactness
and the smooth-partition-of-unity theorem for manifolds. -/
theorem exists_finiteSmoothPreferredTrivializingCover :
    Nonempty (FiniteSmoothPreferredTrivializingCover I (F := F) (V := V)) := by
  classical
  let U₀ : M → Set M := fun x => (trivializationAt F V x).baseSet
  have hU₀open : ∀ x : M, IsOpen (U₀ x) := fun x =>
    (trivializationAt F V x).open_baseSet
  have hU₀cover : Set.univ ⊆ ⋃ x : M, U₀ x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F V x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U₀ hU₀open hU₀cover
  let U : s → Set M := fun i => U₀ (i : M)
  have hUopen : ∀ i : s, IsOpen (U i) := fun i => hU₀open (i : M)
  have hUcover : Set.univ ⊆ ⋃ i : s, U i := by
    intro x hx
    have hx' : x ∈ ⋃ i ∈ s, U₀ i := hs hx
    simpa [U] using hx'
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    I isClosed_univ U hUopen hUcover
  exact ⟨{ centers := s, partition := ρ, subordinate := hρ }⟩

/-- A canonical noncomputable choice of finite smooth preferred cover. -/
noncomputable def chosen :
    FiniteSmoothPreferredTrivializingCover I (F := F) (V := V) :=
  Classical.choice
    (exists_finiteSmoothPreferredTrivializingCover (I := I) (F := F) (V := V))

end FiniteSmoothPreferredTrivializingCover
end Bundle.Trivialization
end PoincareCurvature
