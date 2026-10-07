module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
Intrinsic Ricci curvature is slicewise and respects arbitrary time reindexing.
The old chosen connection family is transported and connection-independence
identifies its Ricci tensor with the reindexed intrinsic tensor. No equality
between independently chosen background connections is assumed.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Intrinsic Ricci curvature respects every map of the time parameter. -/
theorem intrinsicRicciTensor_reindex
    (g : MetricFamily (I := I) (M := M)) (φ : ℝ → ℝ)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) (fun s ↦ g (φ s)) t x u v =
      intrinsicRicciTensor (I := I) (M := M) g (φ t) x u v := by
  let cov : ConnectionFamily (I := I) (M := M) := fun s ↦
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g (φ s)
  have hcov : ∀ s : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov s) 1 :=
    fun s ↦ CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g (φ s)
  have hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) (fun s ↦ g (φ s)) cov := by
    intro s
    letI : Bundle.RiemannianBundle TM := ⟨(g (φ s)).toRiemannianMetric⟩
    exact CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) (g := g) (φ s)
  rw [intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
    (I := I) (M := M) (fun s ↦ g (φ s)) hcov hLevi]
  -- Both sides now use the same original chosen connection at φ t and
  -- the same metric g (φ t); only regularity proofs can differ.
  rfl

/-- Translation of time is a specialization of arbitrary reindexing. -/
theorem intrinsicRicciTensor_time_add
    (g : MetricFamily (I := I) (M := M)) (c t : ℝ)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) (fun s ↦ g (s + c)) t x u v =
      intrinsicRicciTensor (I := I) (M := M) g (t + c) x u v :=
  intrinsicRicciTensor_reindex (I := I) (M := M) g (fun s ↦ s + c) t x u v

end RicciFlow
