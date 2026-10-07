module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.IntrinsicRicciReindex

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

set_option pp.universes true
set_option pp.fullNames true
set_option format.width 240

#check @RicciFlow.intrinsicRicciTensor_reindex
#check @RicciFlow.intrinsicRicciTensor_time_add
#print axioms RicciFlow.intrinsicRicciTensor_reindex
#print axioms RicciFlow.intrinsicRicciTensor_time_add

namespace IntrinsicRicciReindexVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

theorem zero_shift (g : RicciFlow.MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    RicciFlow.intrinsicRicciTensor (I := I) (M := M) (fun s ↦ g (s + 0)) t x u v =
      RicciFlow.intrinsicRicciTensor (I := I) (M := M) g t x u v := by
  simpa only [add_zero] using
    RicciFlow.intrinsicRicciTensor_time_add (I := I) (M := M) g 0 t x u v

theorem rank_zero_reindex (g : RicciFlow.MetricFamily (I := I) (M := M))
    (hE : Module.finrank ℝ E = 0) (φ : ℝ → ℝ)
    (t : ℝ) (x : M) (u v : TM x) :
    RicciFlow.intrinsicRicciTensor (I := I) (M := M) (fun s ↦ g (φ s)) t x u v = 0 := by
  let _ : Fact (Module.finrank ℝ E ≤ 1) := ⟨by rw [hE]; exact Nat.zero_le 1⟩
  rw [RicciFlow.intrinsicRicciTensor_reindex (I := I) (M := M) g φ t x u v]
  exact RicciFlow.intrinsicRicciTensor_eq_zero_of_finrank_model_le_one g (φ t) x u v

-- Applying the same theorem in the empty case requires no positive-rank,
-- nonempty, curvature, boundary, or time-regularity assumption.
theorem empty_reindex [IsEmpty M]
    (g : RicciFlow.MetricFamily (I := I) (M := M)) (φ : ℝ → ℝ) :
    (fun (t : ℝ) (x : M) (u v : TM x) ↦
      RicciFlow.intrinsicRicciTensor (I := I) (M := M) (fun s ↦ g (φ s)) t x u v) =
    (fun (t : ℝ) (x : M) (u v : TM x) ↦
      RicciFlow.intrinsicRicciTensor (I := I) (M := M) g (φ t) x u v) := by
  funext t x u v
  exact RicciFlow.intrinsicRicciTensor_reindex (I := I) (M := M) g φ t x u v

end IntrinsicRicciReindexVerification

#check @IntrinsicRicciReindexVerification.zero_shift
#check @IntrinsicRicciReindexVerification.rank_zero_reindex
#check @IntrinsicRicciReindexVerification.empty_reindex
#print axioms IntrinsicRicciReindexVerification.zero_shift
#print axioms IntrinsicRicciReindexVerification.rank_zero_reindex
#print axioms IntrinsicRicciReindexVerification.empty_reindex
