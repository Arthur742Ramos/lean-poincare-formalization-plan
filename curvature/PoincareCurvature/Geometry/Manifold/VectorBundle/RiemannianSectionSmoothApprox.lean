module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
public import PoincareCurvature.Geometry.Manifold.VectorBundle.SmoothApprox

/-!
# Smooth approximation for bilinear-form section carriers

This file keeps the analytic-density bridge out of the large Ricci-flow modules.  It combines the
fiberwise smooth-approximant interface with the preferred bilinear-form finite-cover norm control
from `RiemannianSection`.
-/

@[expose] public noncomputable section

open scoped Bundle Manifold ContDiff Topology

namespace PoincareCurvature
namespace Bundle.Trivialization
namespace ContinuousSectionSpace

section PreferredBilinearSmoothApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance smoothApproxBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))
local instance smoothApproxBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
local instance smoothApproxBilWNormedAddCommGroup (x : M) : NormedAddCommGroup (BilW x) :=
  inferInstance
local instance smoothApproxBilWNormedSpace (x : M) : NormedSpace ℝ (BilW x) :=
  inferInstance
local instance smoothApproxBilWTopologicalSpace :
    TopologicalSpace (_root_.Bundle.TotalSpace BilF BilW) :=
  _root_.Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance smoothApproxBilWFiberBundle : FiberBundle BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance smoothApproxBilWVectorBundle : VectorBundle ℝ BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- The inverse preferred bilinear-form trivialization pulls both arguments forward through the
underlying vector-bundle trivialization. -/
lemma trivializationAt_bilinearFormBundle_symm_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilF) (u v : W x) :
    ((trivializationAt BilF BilW x0).symm x B) u v =
      B ((trivializationAt F W x0).continuousLinearMapAt ℝ x u)
        ((trivializationAt F W x0).continuousLinearMapAt ℝ x v) := by
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  let tb := trivializationAt BilF BilW x0
  have hxBil : x ∈ tb.baseSet := by
    simpa [tb] using hx
  have happly : (tb ⟨x, tb.symm x B⟩).2 = B := by
    exact congrArg Prod.snd (tb.apply_mk_symm hxBil B)
  have hleft :
      (tb ⟨x, tb.symm x B⟩).2 (e u) (e v) = tb.symm x B u v := by
    rw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (F := F) (W := W) x0 x hx (tb.symm x B) (e u) (e v)]
    simpa [e] using
      congrArg₂ (fun a b : W x => tb.symm x B a b)
        (e.symm_apply_apply u) (e.symm_apply_apply v)
  have hright := congrArg (fun C : BilF => C (e u) (e v)) happly
  simpa [tb, e, Bundle.Trivialization.linearMapAt_apply, hx] using hleft.symm.trans hright

/-- The inverse preferred bilinear-form trivialization is bounded by the square of the underlying
vector-bundle trivialization bound. -/
theorem preferredBilinear_symmL_opNorm_le_of_linearMapAt_opNorm_le
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ‖(trivializationAt F W x0).continuousLinearMapAt ℝ x‖ ≤ C) :
    ‖(trivializationAt BilF BilW x0).symmL ℝ x‖ ≤ C * C := by
  let S : W x →L[ℝ] F := (trivializationAt F W x0).continuousLinearMapAt ℝ x
  let A : BilF →L[ℝ] BilW x := (trivializationAt BilF BilW x0).symmL ℝ x
  have hA : ‖A‖ ≤ C * C := by
    refine ContinuousLinearMap.opNorm_le_bound A (mul_nonneg hC0 hC0) ?_
    intro B
    have hCB : 0 ≤ (C * C) * ‖B‖ := mul_nonneg (mul_nonneg hC0 hC0) (norm_nonneg B)
    refine ContinuousLinearMap.opNorm_le_bound (A B) hCB ?_
    intro u
    have hCBu : 0 ≤ ((C * C) * ‖B‖) * ‖u‖ := mul_nonneg hCB (norm_nonneg u)
    refine ContinuousLinearMap.opNorm_le_bound ((A B) u) hCBu ?_
    intro v
    have hSu : ‖S u‖ ≤ C * ‖u‖ := by
      exact (ContinuousLinearMap.le_opNorm S u).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg u))
    have hSv : ‖S v‖ ≤ C * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm S v).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg v))
    have hAuv : (A B) u v = B (S u) (S v) := by
      dsimp [A, S]
      simpa using trivializationAt_bilinearFormBundle_symm_apply_eq
        (F := F) (W := W) x0 x hx B u v
    calc
      ‖(A B) u v‖ = ‖B (S u) (S v)‖ := by rw [hAuv]
      _ ≤ ‖B‖ * ‖S u‖ * ‖S v‖ :=
        ContinuousLinearMap.le_opNorm₂ B (S u) (S v)
      _ ≤ ‖B‖ * (C * ‖u‖) * (C * ‖v‖) := by
        gcongr
      _ = (((C * C) * ‖B‖) * ‖u‖) * ‖v‖ := by ring
  simpa [A] using hA

/-- A local bound for the underlying vector-bundle trivialization gives the local inverse-bound
needed to smooth bilinear-form sections. -/
theorem eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
    (hbound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C) :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C := by
  intro x
  obtain ⟨C, hCpos, hCevent⟩ := hbound x
  refine ⟨C * C + 1, by nlinarith [hCpos], ?_⟩
  have hxbase : x ∈ (trivializationAt F W x).baseSet := mem_baseSet_trivializationAt F W x
  filter_upwards [hCevent, (trivializationAt F W x).open_baseSet.mem_nhds hxbase] with y hy hybase
  have hle :
      ‖(trivializationAt BilF BilW x).symmL ℝ y‖ ≤ C * C :=
    preferredBilinear_symmL_opNorm_le_of_linearMapAt_opNorm_le
      (F := F) (W := W) x y hybase hCpos.le hy.le
  exact lt_of_le_of_lt hle (by nlinarith [hCpos])

/-- Continuous preferred bilinear-form sections have smooth fiberwise approximants once the
underlying vector-bundle trivializations are locally bounded. -/
theorem exists_smooth_fiberwise_approx_preferredBilinear_of_eventually_norm_trivializationAt_lt
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    (hbound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C)
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η := by
  intro η hη
  have hBilBound :
      ∀ x : M, ∃ C > 0,
        ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C :=
    eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
      (F := F) (W := W) hbound
  obtain ⟨g, hg⟩ :=
    Continuous.exists_contMDiffSection_approx_of_eventually_norm_symmL_lt
      (I := I) (F := BilF) (V := BilW) (n := (2 : ℕ∞))
      hBilBound (s := (s : ∀ x : M, BilW x)) s.continuous continuous_const (fun _ => hη)
  exact ⟨g, fun x => by simpa [dist_comm] using hg x⟩

/-- Smooth fiberwise approximation of bilinear-form bundle sections upgrades to approximation in the
transported finite-cover Banach norm for preferred bilinear-form trivializations, provided the
underlying inverse vector-bundle trivializations are uniformly bounded on the cover.

This is the concrete density bridge needed downstream: it replaces an abstract Banach-norm
approximation hypothesis by a fiberwise smooth-approximant theorem plus a finite-cover coordinate
Lipschitz estimate. -/
theorem exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hsmoothApprox : ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε := by
  refine exists_dist_lt_of_forall_fiber_dist_lt_preferredBilinear_of_symmL_opNorm_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (s := s)
    (P := fun u ↦ ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)))
    hCpos hC ?_
  intro η hη
  obtain ⟨g, hg⟩ := hsmoothApprox η hη
  let u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
    ⟨fun x ↦ g x, g.contMDiff.continuous⟩
  refine ⟨u, ?_, ?_⟩
  · simpa [u] using g.contMDiff
  · intro x
    have hdist_comm : dist (s x) (g x) = dist (g x) (s x) := dist_comm _ _
    simpa [u, hdist_comm] using hg x

end PreferredBilinearSmoothApprox

section PreferredBilinearRiemannianSmoothApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance riemannianSmoothApproxBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))
local instance riemannianSmoothApproxBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
local instance riemannianSmoothApproxBilWNormedAddCommGroup (x : M) :
    NormedAddCommGroup (BilW x) :=
  inferInstance
local instance riemannianSmoothApproxBilWNormedSpace (x : M) : NormedSpace ℝ (BilW x) :=
  inferInstance
local instance riemannianSmoothApproxBilWTopologicalSpace :
    TopologicalSpace (_root_.Bundle.TotalSpace BilF BilW) :=
  _root_.Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance riemannianSmoothApproxBilWFiberBundle : FiberBundle BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance riemannianSmoothApproxBilWVectorBundle : VectorBundle ℝ BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- A continuous Riemannian vector-bundle structure gives the local coordinate-map bounds used by
the preferred bilinear-form smooth-approximation theorem. -/
theorem eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W] :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C := by
  intro x
  exact eventually_norm_trivializationAt_lt (F := F) (E := W) x

/-- A continuous Riemannian vector-bundle structure supplies the local inverse bounds for the
bilinear-form bundle induced by preferred trivializations. -/
theorem eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_isContinuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W] :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C :=
  eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
    (F := F) (W := W)
    (eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle (F := F) (W := W))

/-- Continuous preferred bilinear-form sections have smooth fiberwise approximants in a continuous
Riemannian vector bundle.  This discharges the local trivialization-boundedness hypothesis from the
Riemannian vector-bundle estimate. -/
theorem exists_smooth_fiberwise_approx_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η :=
  exists_smooth_fiberwise_approx_preferredBilinear_of_eventually_norm_trivializationAt_lt
    (F := F) (W := W)
    (eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle (F := F) (W := W))
    x0 s

/-- Smooth approximation in the transported finite-cover Banach norm for preferred bilinear-form
trivializations in a continuous Riemannian vector bundle.  The local coordinate-map boundedness
hypothesis is discharged internally by the Riemannian vector-bundle estimate; only the finite-cover
inverse bound remains as explicit input. -/
theorem exists_dist_lt_preferredBilinear_of_continuousRiemannianBundle_and_symmL_opNorm_le
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε :=
  exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
    (F := F) (W := W) x0 s hCpos hC
    (exists_smooth_fiberwise_approx_preferredBilinear_of_continuousRiemannianBundle
      (F := F) (W := W) x0 s)

end PreferredBilinearRiemannianSmoothApprox

end ContinuousSectionSpace
end Bundle.Trivialization
end PoincareCurvature

