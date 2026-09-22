module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicInvariant

/-!
# Scalar maximum principle with an open initial-time equation

The parabolic equation for a classical Cauchy solution is normally asserted
only at positive times. This variant keeps the initial condition as a
continuous trace and never asks for a time derivative at the initial face.
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

/-- A strict supersolution cannot acquire a negative value after a
nonnegative continuous initial trace. The differential assumptions hold only
on the open time interval. -/
theorem parabolicNonnegativeInvariant_openInitial
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f ft : ℝ → M → ℝ) {t₀ T : ℝ}
    (hcont : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (Icc t₀ T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      HasDerivAt (fun s => f s x) (ft t x) t)
    (hfNear : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (f t) y)
    (hdf : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I) (f t) y)) x)
    (hpde : ∀ t ∈ Ioo t₀ T, ∀ x : M,
      f t x < 0 → g.scalarLaplacian cov f t x < ft t x)
    (hinitial : ∀ x : M, 0 ≤ f t₀ x) :
    ∀ t ∈ Ioo t₀ T, ∀ x : M, 0 ≤ f t x := by
  intro b hb x
  by_contra hnonneg
  have hfbx : f b x < 0 := lt_of_not_ge hnonneg
  let slab : Set (ℝ × M) := Icc t₀ b ×ˢ (Set.univ : Set M)
  have hslabCompact : IsCompact slab :=
    isCompact_Icc.prod isCompact_univ
  have hslabNonempty : slab.Nonempty :=
    ⟨(t₀, Classical.choice inferInstance), ⟨⟨le_rfl, hb.1.le⟩, Set.mem_univ _⟩⟩
  have hslabSub : slab ⊆ Icc t₀ T ×ˢ (Set.univ : Set M) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hb.2.le⟩, Set.mem_univ _⟩
  obtain ⟨p, hp, hpmin⟩ :=
    hslabCompact.exists_isMinOn hslabNonempty (hcont.mono hslabSub)
  have hpcomp : f p.1 p.2 ≤ f b x :=
    hpmin (show (b, x) ∈ slab from ⟨⟨hb.1.le, le_rfl⟩, Set.mem_univ x⟩)
  have hpneg : f p.1 p.2 < 0 := hpcomp.trans_lt hfbx
  have hptimePos : t₀ < p.1 := by
    have hptimeNonneg : t₀ ≤ p.1 := hp.1.1
    have hne : p.1 ≠ t₀ := by
      intro hpeq
      have hinit := hinitial p.2
      rw [hpeq] at hpneg
      linarith
    exact lt_of_le_of_ne hptimeNonneg (Ne.symm hne)
  have hpInterior : p.1 ∈ Ioo t₀ T :=
    ⟨hptimePos, hp.1.2.trans_lt hb.2⟩
  have hspatialMinOn : IsMinOn (f p.1) Set.univ p.2 := by
    intro y hy
    exact hpmin (show (p.1, y) ∈ slab from ⟨hp.1, Set.mem_univ y⟩)
  have hlap : 0 ≤ g.scalarLaplacian cov f p.1 p.2 :=
    g.scalarLaplacian_nonneg_of_isLocalMin cov f p.1
      (hspatialMinOn.isLocalMin univ_mem)
      (hfNear p.1 hpInterior p.2)
      (hdf p.1 hpInterior p.2)
  let z : ℝ → ℝ := fun t => f t p.2
  have hzderiv : HasDerivAt z (ft p.1 p.2) p.1 := by
    simpa [z] using htime p.1 hpInterior p.2
  have htimeMin : IsLocalMinOn z (Icc t₀ b) p.1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpmin (show (t, p.2) ∈ slab from ⟨ht, Set.mem_univ p.2⟩)
  have hzeroMem : t₀ ∈ Icc t₀ b := ⟨le_rfl, hb.1.le⟩
  have htangent : t₀ - p.1 ∈ posTangentConeAt (Icc t₀ b) p.1 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc t₀ b).segment_subset hp.1 hzeroMem)
  have hderivNonneg := htimeMin.hasFDerivWithinAt_nonneg
    hzderiv.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hderivNonneg
  have htimeNonpos : ft p.1 p.2 ≤ 0 := by
    nlinarith
  have hpde' := hpde p.1 hpInterior p.2 hpneg
  linarith

end CovariantDerivative.TimeDependentRiemannianMetric

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Spatially constant affine negation reverses the scalar differential. -/
theorem scalarDifferential_const_sub
    (c : ℝ) {f : M → ℝ} (hf : ∀ y, MDiffAt f y) :
    scalarDifferential (I := I) (fun y => c - f y) =
      -scalarDifferential (I := I) f := by
  have heq : (fun y : M => c - f y) =
      (fun _ : M => c) + (-1 : ℝ) • f := by
    funext y
    simp [Pi.add_apply, sub_eq_add_neg]
  have hneg : ∀ y, MDiffAt ((-1 : ℝ) • f) y := by
    intro y
    exact (mdifferentiableAt_const : MDiffAt (fun _ : M => (-1 : ℝ)) y).smul (hf y)
  rw [heq, scalarDifferential_add (fun y => mdifferentiableAt_const) hneg]
  rw [scalarDifferential_smul_const (-1) hf]
  have hc : scalarDifferential (I := I) (fun _ : M => c) = 0 := by
    funext y
    ext v
    simp only [scalarDifferential_apply, Pi.zero_apply]
    rw [mvfderiv_const]
  rw [hc]
  simpa only [zero_add] using
    (neg_one_smul ℝ (scalarDifferential (I := I) f))

/-- Spatial constants disappear and negation reverses the intrinsic scalar
Laplacian. This affine form is used for time-dependent maximum-principle
barriers, whose spatial offset is constant on each time slice. -/
theorem scalarLaplacian_const_sub
    (cov : CovariantDerivative I E TM) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    scalarLaplacian cov (fun y => c - f y) x =
      -scalarLaplacian cov f x := by
  have hdc : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (fun _ : M => c) y)) x := by
    have hz :
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (scalarDifferential (I := I) (fun _ : M => c) y)) =
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y 0) := by
      funext y
      congr 1
      ext v
      simp only [scalarDifferential_apply]
      rw [mvfderiv_const]
    rw [hz]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (F := E →L[ℝ] ℝ) (E := T₁) (x := x)
  have heq : (fun y : M => c - f y) =
      (fun _ : M => c) + (-1 : ℝ) • f := by
    funext y
    simp [Pi.add_apply, sub_eq_add_neg]
  rw [heq, scalarLaplacian_add_smul_const cov (-1)
    (fun y => mdifferentiableAt_const) hf hdc hdf]
  rw [scalarLaplacian_const]
  ring

end CovariantDerivative
