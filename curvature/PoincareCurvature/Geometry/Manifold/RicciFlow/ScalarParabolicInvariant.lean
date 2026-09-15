module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicBarrier

/-!
# Compact scalar parabolic invariant regions

This file isolates the maximum-principle mechanism used by the
Hamilton--Ivey estimate.  A scalar quantity on a compact boundaryless
manifold cannot cross from nonnegative to negative when its parabolic
evolution has a reaction term which is strictly positive throughout the
negative region.

The statement uses the intrinsic Laplace--Beltrami operator of the evolving
metric.  No coordinate minimum principle or finite coefficient surrogate is
used.
-/

@[expose] public noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- A compact-manifold scalar invariant-region principle.  If

`Delta f + reaction <= partial_t f`

and the reaction is strictly positive at every negative value of `f`, then
nonnegative initial data remain nonnegative. -/
theorem parabolicNonnegativeInvariant
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f ft reaction : ℝ → M → ℝ) {T : ℝ}
    (hcont : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => f s x) (ft t x) t)
    (hfNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (f t) y)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I) (f t) y)) x)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov f t x + reaction t x ≤ ft t x)
    (hreaction : ∀ t ∈ Icc 0 T, ∀ x : M,
      f t x < 0 → 0 < reaction t x)
    (hinitial : ∀ x : M, 0 ≤ f 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  intro b hb x
  by_contra hnonneg
  have hfbx : f b x < 0 := lt_of_not_ge hnonneg
  let slab : Set (ℝ × M) := Icc 0 b ×ˢ (Set.univ : Set M)
  have hslabCompact : IsCompact slab :=
    isCompact_Icc.prod isCompact_univ
  have hslabNonempty : slab.Nonempty :=
    ⟨(0, Classical.choice inferInstance), ⟨⟨le_rfl, hb.1⟩, Set.mem_univ _⟩⟩
  have hslabSub : slab ⊆ Icc 0 T ×ˢ (Set.univ : Set M) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hb.2⟩, Set.mem_univ _⟩
  obtain ⟨p, hp, hpmin⟩ :=
    hslabCompact.exists_isMinOn hslabNonempty (hcont.mono hslabSub)
  have hpcomp : f p.1 p.2 ≤ f b x :=
    hpmin (show (b, x) ∈ slab from ⟨⟨hb.1, le_rfl⟩, Set.mem_univ x⟩)
  have hpneg : f p.1 p.2 < 0 := hpcomp.trans_lt hfbx
  have hptimePos : 0 < p.1 := by
    have hptimeNonneg : 0 ≤ p.1 := hp.1.1
    have hne : p.1 ≠ 0 := by
      intro hpeq
      have hinit := hinitial p.2
      rw [hpeq] at hpneg
      linarith
    exact lt_of_le_of_ne hptimeNonneg (Ne.symm hne)
  have hspatialMinOn : IsMinOn (f p.1) Set.univ p.2 := by
    intro y hy
    exact hpmin (show (p.1, y) ∈ slab from ⟨hp.1, Set.mem_univ y⟩)
  have hlap : 0 ≤ g.scalarLaplacian cov f p.1 p.2 :=
    g.scalarLaplacian_nonneg_of_isLocalMin cov f p.1
      (hspatialMinOn.isLocalMin univ_mem)
      (hfNear p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2)
      (hdf p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2)
  let z : ℝ → ℝ := fun t => f t p.2
  have hzderiv : HasDerivAt z (ft p.1 p.2) p.1 := by
    simpa [z] using htime p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2
  have htimeMin : IsLocalMinOn z (Icc 0 b) p.1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpmin (show (t, p.2) ∈ slab from ⟨ht, Set.mem_univ p.2⟩)
  have hzeroMem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
  have htangent : (0 : ℝ) - p.1 ∈ posTangentConeAt (Icc 0 b) p.1 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) b).segment_subset hp.1 hzeroMem)
  have hderivNonneg := htimeMin.hasFDerivWithinAt_nonneg
    hzderiv.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hderivNonneg
  have htimeNonpos : ft p.1 p.2 ≤ 0 := by
    nlinarith
  have hpde' := hpde p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2
  have hreaction' := hreaction p.1
    ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2 hpneg
  nlinarith

end CovariantDerivative.TimeDependentRiemannianMetric
