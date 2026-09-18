import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicVariation
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianIntrinsic
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ThreeDimensionalDecomposition

/-!
# Geometric Hamilton--Ivey curvature evolution

This module is the first non-conditional bridge from a Ricci-flow metric
variation to the curvature-operator equation used by the Hamilton--Ivey
argument.  The finite-dimensional contraction is kept as a named theorem so
that the signs and numerical coefficients are independently auditable.

The mixed space--time regularity needed to construct a connection variation
is not implied by the slicewise Ricci-flow predicate.  The geometric
interface below therefore asks for that regularity explicitly, while the
curvature evolution itself is derived from the connection variation and the
curvature contractions.
-/

noncomputable section

open Bundle
open Filter Set Topology
open scoped BigOperators Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)

/-! The component contraction used after tracing the connection-variation
formula.  K is the actual three-dimensional curvature tensor, Ric the
actual Ricci tensor, and H the actual second covariant derivative of Ricci.
The six-term left side is the trace of the curvature velocity. -/

theorem trace_curvatureVariation_components_eq_laplacian_add_reaction
    (K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Ric : Fin 3 → Fin 3 → ℝ) (Scal : ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (S : Fin 3 → Fin 3 → ℝ)
    (hK : ∀ a b c d,
      K a b c d =
        Ric a d * (if b = c then 1 else 0) -
          Ric a c * (if b = d then 1 else 0) -
          Ric b d * (if a = c then 1 else 0) +
          Ric b c * (if a = d then 1 else 0) -
          Scal / 2 *
            ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
              (if a = c then 1 else 0) * (if b = d then 1 else 0)))
    (hRicSymm : ∀ a b, Ric a b = Ric b a)
    (hScal : Scal = ∑ i, Ric i i)
    (hHlast : ∀ a b c d, H a b c d = H a b d c)
    (hHcomm : ∀ a b c d,
      H a b c d - H b a c d =
        -∑ l, (K a b c l * Ric l d + K a b d l * Ric c l))
    (hDiv : ∀ a b, ∑ i, H a i b i = (1 / 2 : ℝ) * S a b)
    (hTrace : ∀ a b, ∑ i, H a b i i = S a b)
    (hSsymm : ∀ a b, S a b = S b a)
    (a b : Fin 3) :
    ∑ i, (-H i a b i - H i b a i + H i i a b +
          H a i b i + H a b i i - H a i i b) =
      ∑ i, H i i a b +
        ((2 * (∑ i, ∑ j, (Ric i j) ^ 2) - Scal ^ 2) *
            (if a = b then 1 else 0) +
          3 * Scal * Ric a b -
          6 * ∑ l, Ric a l * Ric l b) := by
  classical
  have hrewrite :
      (∑ i, (-H i a b i - H i b a i +
          H i i a b + H a i b i + H a b i i - H a i i b)) =
        ∑ i, (-H i a b i - H i b i a + H i i a b +
          H a b i i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hHlast i b a i, hHlast a i i b]
    ring
  rw [hrewrite]
  have hcomm₁ (i : Fin 3) :
      -H i a b i =
        -H a i b i +
          ∑ l, (K i a b l * Ric l i + K i a i l * Ric b l) := by
    have h := hHcomm i a b i
    rw [← Finset.sum_neg_distrib] at h
    rw [Finset.sum_neg_distrib] at h
    linarith
  have hcomm₂ (i : Fin 3) :
      -H i b i a =
        -H b i i a +
          ∑ l, (K i b i l * Ric l a + K i b a l * Ric i l) := by
    have h := hHcomm i b i a
    rw [← Finset.sum_neg_distrib] at h
    rw [Finset.sum_neg_distrib] at h
    linarith
  simp_rw [sub_eq_add_neg]
  simp_rw [hcomm₁, hcomm₂]
  have hlast_rw (i : Fin 3) : H b i i a = H b i a i :=
    hHlast b i i a
  simp_rw [hlast_rw]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hDiv a b, hDiv b a, hTrace a b]
  have hSab : S b a = S a b := hSsymm b a
  rw [hSab]
  have hres :
      (∑ x, ∑ l, (K x a b l * Ric l x + K x a x l * Ric b l)) +
          ∑ x, ∑ l, (K x b x l * Ric l a + K x b a l * Ric x l) =
        (2 * (∑ i, ∑ j, (Ric i j) ^ 2) - Scal ^ 2) *
            (if a = b then 1 else 0) +
           3 * Scal * Ric a b -
           6 * ∑ l, Ric a l * Ric l b := by
    have hR01 : Ric (0 : Fin 3) 1 = Ric 1 0 := hRicSymm 0 1
    have hR02 : Ric (0 : Fin 3) 2 = Ric 2 0 := hRicSymm 0 2
    have hR12 : Ric (1 : Fin 3) 2 = Ric 2 1 := hRicSymm 1 2
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.sum_univ_three] at ⊢ <;>
      simp [hK, hR01, hR02, hR12, hScal, Fin.ext_iff] at ⊢ <;>
      simp only [Fin.sum_univ_three] at ⊢ <;>
      ring_nf at ⊢ <;>
      nlinarith [hR01, hR02, hR12]
  have hres' := hres
  simp only [Finset.sum_add_distrib] at hres'
  simp only [Finset.sum_add_distrib] at ⊢
  linarith [hres']

/-! The following two small algebraic interfaces let the component calculation
be transported back to the actual bilinear tensors.  They are kept here,
rather than hidden in a coordinate representation, because the selected
orthonormal basis is only an evaluation device. -/

theorem bilinear_eq_of_basis_fin3
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 3) ℝ V)
    (F G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (h : ∀ i j, F (b i) (b j) = G (b i) (b j)) :
    ∀ u v, F u v = G u v := by
  intro u v
  have hFG : F = G := by
    apply b.ext
    intro i
    apply LinearMap.ext
    intro w
    rw [← b.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [h]
  exact congrArg (fun Q => Q u v) hFG

theorem trace_curvatureVariation_components_eq_bilinear_fin3
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 3) ℝ V)
    (F G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Ric : Fin 3 → Fin 3 → ℝ) (Scal : ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (S : Fin 3 → Fin 3 → ℝ)
    (reaction : Fin 3 → Fin 3 → ℝ)
    (hK : ∀ a b c d,
      K a b c d =
        Ric a d * (if b = c then 1 else 0) -
          Ric a c * (if b = d then 1 else 0) -
          Ric b d * (if a = c then 1 else 0) +
          Ric b c * (if a = d then 1 else 0) -
          Scal / 2 *
            ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
              (if a = c then 1 else 0) * (if b = d then 1 else 0)))
    (hRicSymm : ∀ a b, Ric a b = Ric b a)
    (hScal : Scal = ∑ i, Ric i i)
    (hHlast : ∀ a b c d, H a b c d = H a b d c)
    (hHcomm : ∀ a b c d,
      H a b c d - H b a c d =
        -∑ l, (K a b c l * Ric l d + K a b d l * Ric c l))
    (hDiv : ∀ a b, ∑ i, H a i b i = (1 / 2 : ℝ) * S a b)
    (hTrace : ∀ a b, ∑ i, H a b i i = S a b)
    (hSsymm : ∀ a b, S a b = S b a)
    (hReaction : ∀ i j, reaction i j =
      (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
            (if i = j then 1 else 0) +
        3 * Scal * Ric i j -
        6 * ∑ l, Ric i l * Ric l j)
    (hRaw : ∀ i j,
      F (b i) (b j) =
        ∑ k, (-H k i j k - H k j i k + H k k i j +
          H i k j k + H i j k k - H i k k j))
    (hCoordinate : ∀ i j,
      reaction i j = G (b i) (b j) - ∑ k, H k k i j) :
    ∀ u v, F u v = G u v := by
  have hBasis : ∀ i j, F (b i) (b j) = G (b i) (b j) := by
    intro i j
    calc
      F (b i) (b j) =
          ∑ k, (-H k i j k - H k j i k + H k k i j +
            H i k j k + H i j k k - H i k k j) := hRaw i j
      _ = ∑ k, H k k i j + reaction i j :=
        by
          simpa only [hReaction i j] using
            (trace_curvatureVariation_components_eq_laplacian_add_reaction
              K Ric Scal H S hK hRicSymm hScal hHlast hHcomm hDiv hTrace hSsymm i j)
      _ = ∑ k, H k k i j +
          (G (b i) (b j) - ∑ k, H k k i j) := by
            rw [hCoordinate i j]
      _ = G (b i) (b j) := by ring
  exact bilinear_eq_of_basis_fin3 b F G hBasis

set_option maxHeartbeats 10000000 in
def curvatureOperatorReactionLinearMap
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    { toFun := fun u =>
        { toFun := fun v =>
            curvatureOperatorReaction g cov hcov hLevi hdim t x u v
          map_add' := by
            intro v w
            rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
              g cov hcov hLevi hdim t x u (v + w),
              curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
                g cov hcov hLevi hdim t x u v,
              curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
                g cov hcov hLevi hdim t x u w]
            simp [curvatureEndomorphismApply, map_add, inner_add_right]
            ring
          map_smul' := by
            intro c v
            rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
              g cov hcov hLevi hdim t x u (c • v),
              curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
                g cov hcov hLevi hdim t x u v]
            simp [curvatureEndomorphismApply, map_smul, inner_smul_right]
            ring }
      map_add' := by
        intro u v
        ext w
        change curvatureOperatorReaction g cov hcov hLevi hdim t x (u + v) w =
          curvatureOperatorReaction g cov hcov hLevi hdim t x u w +
            curvatureOperatorReaction g cov hcov hLevi hdim t x v w
        rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
          g cov hcov hLevi hdim t x (u + v) w,
          curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
            g cov hcov hLevi hdim t x u w,
          curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
            g cov hcov hLevi hdim t x v w]
        simp [curvatureEndomorphismApply, map_add, inner_add_left]
        ring
      map_smul' := by
        intro c u
        ext v
        change curvatureOperatorReaction g cov hcov hLevi hdim t x (c • u) v =
          c * curvatureOperatorReaction g cov hcov hLevi hdim t x u v
        rw [curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
          g cov hcov hLevi hdim t x (c • u) v,
          curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
            g cov hcov hLevi hdim t x u v]
        simp [curvatureEndomorphismApply, map_smul, inner_smul_left]
        ring
      }

@[simp] theorem curvatureOperatorReactionLinearMap_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    [RiemannianBundle TM]
    (t : ℝ) (x : M) (u v : TM x) :
    curvatureOperatorReactionLinearMap g cov hcov hLevi hdim t x u v =
      curvatureOperatorReaction g cov hcov hLevi hdim t x u v := by
  rfl

def bilinearContinuousToLinear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  { toFun := fun u => (B u).toLinearMap
    map_add' := by
      intro u v
      ext w
      simp
    map_smul' := by
      intro c u
      ext v
      simp }

@[simp] theorem bilinearContinuousToLinear_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u v : V) :
    bilinearContinuousToLinear B u v = B u v := rfl

def hamiltonIveyRicciTraceRHS
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (u v : TM x) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    connectionLaplacian (cov t)
        (fun y => CovariantDerivative.ricciCovariantTwoTensor
          (cov t) y) x u v +
      (2 * g.ricciNormSq cov hcov t x * (g t).inner x u v -
        2 * g.scalarCurvature cov hcov t x *
          g.ricciCurvature cov hcov t x u v -
        curvatureOperatorReaction g cov hcov hLevi hdim t x u v) / 2

theorem hamiltonIveyRicciTraceRHS_eq_expanded
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (u v : TM x) :
    hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x u v =
      (by
        letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
        letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
        exact
          connectionLaplacian (cov t)
              (fun y => CovariantDerivative.ricciCovariantTwoTensor
                (cov t) y) x u v +
            (2 * g.ricciNormSq cov hcov t x * (g t).inner x u v -
              2 * g.scalarCurvature cov hcov t x *
                g.ricciCurvature cov hcov t x u v -
              curvatureOperatorReaction g cov hcov hLevi hdim t x u v) / 2) := by
  rfl


def hamiltonIveyRicciTraceEvolutionLinearMapImpl
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    bilinearContinuousToLinear
        (connectionLaplacian (cov t)
          (fun y => CovariantDerivative.ricciCovariantTwoTensor
            (cov t) y) x) +
      g.ricciNormSq cov hcov t x •
        bilinearContinuousToLinear ((g t).inner x) -
      g.scalarCurvature cov hcov t x •
        (CovariantDerivative.ricciCurvature (cov := cov t) x) -
      (1 / 2 : ℝ) •
        curvatureOperatorReactionLinearMap g cov hcov hLevi hdim t x

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem hamiltonIveyRicciTraceEvolutionLinearMapImpl_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (u v : TM x) :
    hamiltonIveyRicciTraceEvolutionLinearMapImpl
        g cov hcov hLevi hdim t x u v =
      hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x u v := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  simp only [hamiltonIveyRicciTraceRHS,
    hamiltonIveyRicciTraceEvolutionLinearMapImpl,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    bilinearContinuousToLinear_apply,
    curvatureOperatorReactionLinearMap_apply,
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature]
  generalize hLap :
    connectionLaplacian (cov t)
      (fun y => CovariantDerivative.ricciCovariantTwoTensor (cov t) y) x u v = L
  generalize hNorm : g.ricciNormSq cov hcov t x = N
  generalize hInner : (g t).inner x u v = G
  generalize hScalar : g.scalarCurvature cov hcov t x = R
  generalize hRicci :
      (CovariantDerivative.ricciCurvature (cov := cov t) x) u v = P
  generalize hReaction :
      curvatureOperatorReaction g cov hcov hLevi hdim t x u v = Q
  ring

structure HamiltonIveyRicciTraceMapData
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) where
  map : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ
  map_apply : ∀ u v, map u v =
    hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x u v

opaque hamiltonIveyRicciTraceMapData
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    HamiltonIveyRicciTraceMapData g cov hcov hLevi hdim t x := by
  exact
    { map := hamiltonIveyRicciTraceEvolutionLinearMapImpl
        g cov hcov hLevi hdim t x
      map_apply := by
        intro u v
        exact hamiltonIveyRicciTraceEvolutionLinearMapImpl_apply
          g cov hcov hLevi hdim t x u v }

irreducible_def hamiltonIveyRicciTraceEvolutionLinearMap
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
  (hamiltonIveyRicciTraceMapData g cov hcov hLevi hdim t x).map

theorem hamiltonIveyRicciTraceEvolutionLinearMap_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) (u v : TM x) :
    hamiltonIveyRicciTraceEvolutionLinearMap g cov hcov hLevi hdim t x u v =
      hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x u v := by
  simpa only [hamiltonIveyRicciTraceEvolutionLinearMap] using
    (hamiltonIveyRicciTraceMapData g cov hcov hLevi hdim t x).map_apply u v

def HamiltonIveyRicciTraceEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (curvatureVelocity :
      ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    ∀ u v : TM x,
      curvatureTensorVelocityRicci curvatureVelocity x u v =
        connectionLaplacian (cov t)
            (fun y => CovariantDerivative.ricciCovariantTwoTensor
              (cov t) y) x u v +
          ((2 * g.ricciNormSq cov hcov t x * (g t).inner x u v -
              2 * g.scalarCurvature cov hcov t x *
                g.ricciCurvature cov hcov t x u v -
              curvatureOperatorReaction g cov hcov hLevi hdim t x u v) / 2)



/-! This is the dynamic bridge itself.  Its inputs are the actual trace of
the connection-induced curvature velocity and the static covariant-Hessian
contractions.  The conclusion is the Ricci evolution identity; no
connection-Laplacian-plus-reaction equation is assumed. -/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
theorem HamiltonIveyRicciTraceEvolution.of_geometricContractions
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    [RiemannianBundle TM]
    {t : ℝ} (x : M)
    (curvatureVelocity :
      ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (b : Module.Basis (Fin 3) ℝ (TM x))
    (K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Ric : Fin 3 → Fin 3 → ℝ) (Scal : ℝ)
    (H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (S : Fin 3 → Fin 3 → ℝ)
    (hK : ∀ a b c d,
      K a b c d =
        Ric a d * (if b = c then 1 else 0) -
          Ric a c * (if b = d then 1 else 0) -
          Ric b d * (if a = c then 1 else 0) +
          Ric b c * (if a = d then 1 else 0) -
          Scal / 2 *
            ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
              (if a = c then 1 else 0) * (if b = d then 1 else 0)))
    (hRicSymm : ∀ a b, Ric a b = Ric b a)
    (hScal : Scal = ∑ i, Ric i i)
    (hHlast : ∀ a b c d, H a b c d = H a b d c)
    (hHcomm : ∀ a b c d,
      H a b c d - H b a c d =
        -∑ l, (K a b c l * Ric l d + K a b d l * Ric c l))
    (hDiv : ∀ a b, ∑ i, H a i b i = (1 / 2 : ℝ) * S a b)
    (hTrace : ∀ a b, ∑ i, H a b i i = S a b)
    (hSsymm : ∀ a b, S a b = S b a)
    (hRaw : ∀ i j,
      curvatureTensorVelocityRicci curvatureVelocity x (b i) (b j) =
        ∑ k, (-H k i j k - H k j i k + H k k i j +
          H i k j k + H i j k k - H i k k j))
    (hLaplacian : ∀ i j,
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      ∑ k, H k k i j =
        connectionLaplacian (cov t)
          (fun y => CovariantDerivative.ricciCovariantTwoTensor
            (cov t) y) x (b i) (b j))
    (hReaction : ∀ i j,
      (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
            (if i = j then 1 else 0) +
        3 * Scal * Ric i j -
        6 * ∑ l, Ric i l * Ric l j =
      (2 * g.ricciNormSq cov hcov t x * (g t).inner x (b i) (b j) -
        2 * g.scalarCurvature cov hcov t x *
          g.ricciCurvature cov hcov t x (b i) (b j) -
        curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b j)) / 2) :
    HamiltonIveyRicciTraceEvolution g cov hcov hLevi hdim
      curvatureVelocity t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let reaction : Fin 3 → Fin 3 → ℝ := fun i j =>
    (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
          (if i = j then 1 else 0) +
      3 * Scal * Ric i j -
      6 * ∑ l, Ric i l * Ric l j
  have hReactionPoly : ∀ i j, reaction i j =
      (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
            (if i = j then 1 else 0) +
        3 * Scal * Ric i j -
        6 * ∑ l, Ric i l * Ric l j := by
    intro i j
    rfl
  have hCoordinate : ∀ i j,
      reaction i j =
        hamiltonIveyRicciTraceEvolutionLinearMapImpl
            g cov hcov hLevi hdim t x (b i) (b j) -
          ∑ k, H k k i j := by
    intro i j
    dsimp [reaction]
    have hMap := hamiltonIveyRicciTraceEvolutionLinearMapImpl_apply
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (hdim := hdim) t x (b i) (b j)
    have hRhs :
        hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x (b i) (b j) =
          (((cov t).connectionLaplacian
              (fun y => CovariantDerivative.ricciCovariantTwoTensor
                (cov t) y) x) (b i)) (b j) +
            (2 * g.ricciNormSq cov hcov t x * (g t).inner x (b i) (b j) -
              2 * g.scalarCurvature cov hcov t x *
                g.ricciCurvature cov hcov t x (b i) (b j) -
              curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b j)) / 2 := by
      rfl
    have hG := hMap.trans hRhs
    rw [← hReaction (i := i) (j := j)] at hG
    have hL := hLaplacian (i := i) (j := j)
    rw [← hL] at hG
    set P : ℝ :=
      hamiltonIveyRicciTraceEvolutionLinearMapImpl
        g cov hcov hLevi hdim t x (b i) (b j) with hP
    have hGP :
        P = (∑ k, H k k i j) + reaction i j := by
      calc
        P = hamiltonIveyRicciTraceEvolutionLinearMapImpl
              g cov hcov hLevi hdim t x (b i) (b j) := hP
        _ = (∑ k, H k k i j) + reaction i j := by
          exact hG
    have hCoordinateP :
        reaction i j = P - ∑ k, H k k i j := by
      linarith [hGP]
    calc
      reaction i j = P - ∑ k, H k k i j := hCoordinateP
      _ = hamiltonIveyRicciTraceEvolutionLinearMapImpl
            g cov hcov hLevi hdim t x (b i) (b j) - ∑ k, H k k i j := by
        exact congrArg₂ (fun a b : ℝ => a - b) hP rfl
  let G : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    hamiltonIveyRicciTraceEvolutionLinearMapImpl
      g cov hcov hLevi hdim t x
  have hGmap :
      G = hamiltonIveyRicciTraceEvolutionLinearMapImpl
        g cov hcov hLevi hdim t x := by
    rfl
  have hCoordinateG : ∀ i j,
      reaction i j = G (b i) (b j) - ∑ k, H k k i j := by
    intro i j
    exact (hCoordinate i j).trans
      (congrArg₂ (fun a b : ℝ => a - b)
        (congrArg (fun Q => Q (b i) (b j)) hGmap.symm) rfl)
  have hFGG :
      ∀ u v,
        curvatureTensorVelocityRicci curvatureVelocity x u v =
          G u v := by
    exact
      trace_curvatureVariation_components_eq_bilinear_fin3
        b (curvatureTensorVelocityRicci curvatureVelocity x) G
        K Ric Scal H S reaction
        hK hRicSymm hScal hHlast hHcomm hDiv hTrace hSsymm
        hReactionPoly hRaw
        hCoordinateG
  have hFG :
      ∀ u v,
        curvatureTensorVelocityRicci curvatureVelocity x u v =
          hamiltonIveyRicciTraceEvolutionLinearMap
            g cov hcov hLevi hdim t x u v := by
    intro u v
    exact (hFGG u v).trans
      ((hamiltonIveyRicciTraceEvolutionLinearMapImpl_apply
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (hdim := hdim) t x u v).trans
        (hamiltonIveyRicciTraceEvolutionLinearMap_apply
          (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
          (hdim := hdim) t x u v).symm)
  unfold HamiltonIveyRicciTraceEvolution
  dsimp only
  intro u v
  calc
    curvatureTensorVelocityRicci curvatureVelocity x u v =
        hamiltonIveyRicciTraceEvolutionLinearMap
          g cov hcov hLevi hdim t x u v := hFG u v
    _ = hamiltonIveyRicciTraceRHS g cov hcov hLevi hdim t x u v :=
      hamiltonIveyRicciTraceEvolutionLinearMap_apply
        g cov hcov hLevi hdim t x u v
    _ = _ := hamiltonIveyRicciTraceRHS_eq_expanded
      g cov hcov hLevi hdim t x u v

def HamiltonIveyMetricTraceEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (curvatureVelocity :
      ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (t : ℝ) (x : M) : Prop :=
  RicciFlow.metricTraceAt (I := I) (M := M) g t x
      (curvatureTensorVelocityRicci curvatureVelocity x) =
    g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x

def HamiltonIveyCurvatureOperatorLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Prop := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact
    ∀ u v : TM x,
      connectionLaplacian (cov t)
          (g.curvatureNuShiftedContactTwoTensor
            cov hcov hLevi hdim t x) x u v =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x *
            (g t).inner x u v -
          2 * connectionLaplacian (cov t)
            (fun y => CovariantDerivative.ricciCovariantTwoTensor
              (cov t) y) x u v

/-! The following package contains only the static three-dimensional
contractions used by the Ricci-trace bridge.  In particular, it does not
contain either a Ricci evolution equation or an operator evolution equation. -/

structure HamiltonIveyRicciTraceContractions
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (t : ℝ) (x : M) where
  b : Module.Basis (Fin 3) ℝ (TM x)
  K : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ
  Ric : Fin 3 → Fin 3 → ℝ
  Scal : ℝ
  H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ
  S : Fin 3 → Fin 3 → ℝ
  hK : ∀ a b c d,
    K a b c d =
      Ric a d * (if b = c then 1 else 0) -
        Ric a c * (if b = d then 1 else 0) -
        Ric b d * (if a = c then 1 else 0) +
        Ric b c * (if a = d then 1 else 0) -
        Scal / 2 *
          ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
            (if a = c then 1 else 0) * (if b = d then 1 else 0))
  hRicSymm : ∀ a b, Ric a b = Ric b a
  hScal : Scal = ∑ i, Ric i i
  hHlast : ∀ a b c d, H a b c d = H a b d c
  hHcomm : ∀ a b c d,
    H a b c d - H b a c d =
      -∑ l, (K a b c l * Ric l d + K a b d l * Ric c l)
  hDiv : ∀ a b, ∑ i, H a i b i = (1 / 2 : ℝ) * S a b
  hTrace : ∀ a b, ∑ i, H a b i i = S a b
  hSsymm : ∀ a b, S a b = S b a
  hRaw : ∀ i j,
    curvatureTensorVelocityRicci curvatureVelocity x (b i) (b j) =
      ∑ k, (-H k i j k - H k j i k + H k k i j +
        H i k j k + H i j k k - H i k k j)
  hLaplacian : letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ i j,
      ∑ k, H k k i j =
        connectionLaplacian (cov t)
          (fun y => CovariantDerivative.ricciCovariantTwoTensor
            (cov t) y) x (b i) (b j)
  hReaction : ∀ i j,
    (2 * (∑ p, ∑ q, (Ric p q) ^ 2) - Scal ^ 2) *
          (if i = j then 1 else 0) +
      3 * Scal * Ric i j -
      6 * ∑ l, Ric i l * Ric l j =
    (2 * g.ricciNormSq cov hcov t x * (g t).inner x (b i) (b j) -
      2 * g.scalarCurvature cov hcov t x *
        g.ricciCurvature cov hcov t x (b i) (b j) -
      curvatureOperatorReaction g cov hcov hLevi hdim t x (b i) (b j)) / 2

/-! The nontrivial time-dependent bridge.  Its only time-regularity inputs
are the connection variation and the regularity needed to differentiate its
actual curvature commutator. -/

set_option maxHeartbeats 2000000 in
theorem hasDerivAt_curvatureOperatorTwoTensor_of_connectionVariation_traceEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (curvatureVelocity :
      ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hRicci :
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g
        (curvatureTensorVelocityRicci curvatureVelocity) t)
    (hRicciEvolution :
      HamiltonIveyRicciTraceEvolution g cov hcov hLevi hdim
        curvatureVelocity t x)
    (hTrace :
      HamiltonIveyMetricTraceEvolution g cov hcov curvatureVelocity t x)
    (hLaplacian :
      HamiltonIveyCurvatureOperatorLaplacian g cov hcov hLevi hdim t x) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
      ContinuousLinearMap.toNormedSpace
    letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
      ContinuousLinearMap.toNormedAddCommGroup
    letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
      inferInstance
    ∀ u v : TM x,
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x u v)
        (connectionLaplacian (cov t)
            (g.curvatureNuShiftedContactTwoTensor
              cov hcov hLevi hdim t x) x u v +
          curvatureOperatorReaction g cov hcov hLevi hdim t x u v) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ∀ y : M, NormedAddCommGroup (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₁ y) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ y : M, NormedAddCommGroup (T₂ y) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ y : M, NormedSpace ℝ (T₂ y) := fun _ =>
    inferInstance
  intro u v
  have hoperator := g.hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht x u v
    (curvatureTensorVelocityRicci curvatureVelocity) hRicci
  apply hoperator.congr_deriv
  have hRicciEvolution' := hRicciEvolution u v
  have hLaplacian' := hLaplacian u v
  have hTrace' := hTrace
  simp only [curvatureOperatorTwoTensorVelocity]
  rw [hTrace', hRicciEvolution', hLaplacian']
  ring

/-! Construct the full curvature-evolution certificate from the actual
connection variation and the static three-dimensional contractions. -/

def HamiltonIveyCurvatureEvolutionCertificate.of_geometricContractions
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M)
    (A : ∀ z : M, TM z → TM z → TM z)
    (curvatureVelocity : ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hvelocity : ∀ (z : M) (a b c : TM z),
      curvatureVelocity z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov A t z a b c)
    (hvariation :
      TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
        (I := I) (M := M) cov A t)
    (hA : ∀ (X Y : Π y : M, TM y),
      (∀ y, MDiffAt (T% X) y) → (∀ y, MDiffAt (T% Y) y) →
        ∀ y, MDiffAt (T% (fun z => A z (X z) (Y z))) y)
    (hTrace :
      HamiltonIveyMetricTraceEvolution g cov hcov curvatureVelocity t x)
    (hOperatorLaplacian :
      HamiltonIveyCurvatureOperatorLaplacian g cov hcov hLevi hdim t x)
    (contractions :
      HamiltonIveyRicciTraceContractions
        g cov hcov hLevi hdim curvatureVelocity t x) :
    HamiltonIveyCurvatureEvolutionCertificate g cov hcov hLevi hdim t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hCurvature :
      ∀ (z : M) (a b c : TM z),
        HasDerivAt
          (fun τ => TimeDependentCovariantDerivative.curvatureTensor
            (I := I) (M := M) cov hcov τ z a b c)
          (curvatureVelocity z a b c) t := by
    intro z a b c
    exact
      (TimeDependentCovariantDerivative.hasDerivAt_curvatureTensor_of_hasConnectionTimeVariationAt
        (I := I) (M := M) cov hcov A (t := t) z hvariation hA a b c).congr_deriv
        (hvelocity z a b c).symm
  have hRicci :=
    hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi curvatureVelocity hCurvature
  have hRicciEvolution :=
    HamiltonIveyRicciTraceEvolution.of_geometricContractions
      g cov hcov hLevi hdim x curvatureVelocity
      contractions.b contractions.K contractions.Ric contractions.Scal
      contractions.H contractions.S
      contractions.hK contractions.hRicSymm contractions.hScal
      contractions.hHlast contractions.hHcomm contractions.hDiv
      contractions.hTrace contractions.hSsymm contractions.hRaw
      contractions.hLaplacian contractions.hReaction
  have hEvolution :=
    hasDerivAt_curvatureOperatorTwoTensor_of_connectionVariation_traceEvolution
      g cov hcov hLevi hdim gdot s hflow ht x curvatureVelocity
      hRicci hRicciEvolution hTrace hOperatorLaplacian
  exact HamiltonIveyCurvatureEvolutionCertificate.of_connectionVariation
    g cov hcov hLevi hdim x A curvatureVelocity hvelocity hvariation hA hEvolution

/-! The final public interface no longer accepts the curvature evolution PDE
as an independent premise.  It asks for the connection variation and the
static geometric contractions, derives a certificate at every time, and
feeds those certificates to the Hamilton--Ivey capstone. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_geometricEvolution
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (A : ∀ z : M, TM z → TM z → TM z)
    (curvatureVelocity : ∀ t : ℝ, ∀ z : M,
      TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z →ₗ[ℝ] TM z)
    (hvelocity : ∀ {t : ℝ}, t ∈ Icc 0 T → ∀ (z : M) (a b c : TM z),
      curvatureVelocity t z a b c =
        TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
          (I := I) (M := M) cov A t z a b c)
    (hvariation : ∀ {t : ℝ}, t ∈ Icc 0 T →
      TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
        (I := I) (M := M) cov A t)
    (hA : ∀ (X Y : Π y : M, TM y),
      (∀ y, MDiffAt (T% X) y) → (∀ y, MDiffAt (T% Y) y) →
        ∀ y, MDiffAt (T% (fun z => A z (X z) (Y z))) y)
    (hTrace : ∀ {t : ℝ}, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyMetricTraceEvolution g cov hcov
        (curvatureVelocity t) t x)
    (hOperatorLaplacian : ∀ {t : ℝ}, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureOperatorLaplacian g cov hcov hLevi hdim t x)
    (contractions : ∀ {t : ℝ}, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyRicciTraceContractions
        g cov hcov hLevi hdim (curvatureVelocity t) t x)
    (hShiftedTensorRegularity : ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T, ∀ x : M,
      g.HamiltonIveyShiftedTensorTraceRegularity
        cov hcov hLevi hdim t x)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ ricciVelocity' : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ,
        RicciFlow.HasIntrinsicRicciTimeDerivativeAt
          (I := I) (M := M) g ricciVelocity' t ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ y in 𝓝 x,
          MDiffAt
            (fun z : M =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y) ∧
        MDiffAt
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
            (CovariantDerivative.scalarDifferential (I := I)
              (fun z : M =>
                g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x ∧
        g.scalarLaplacian cov
            (fun _ y =>
              g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, y)) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
          ricciVelocity') :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let evolution : ∀ t : ℝ, t ∈ Icc 0 T → ∀ x : M,
      HamiltonIveyCurvatureEvolutionCertificate
        g cov hcov hLevi hdim t x := by
    intro t ht x
    exact HamiltonIveyCurvatureEvolutionCertificate.of_geometricContractions
      g cov hcov hLevi hdim gdot (Icc 0 T) hflow ht x A
      (curvatureVelocity t)
      (hvelocity (t := t) ht) (hvariation (t := t) ht) hA
      (hTrace (t := t) ht x)
      (hOperatorLaplacian (t := t) ht x)
      (contractions (t := t) ht x)
  exact hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvatureEvolutionCertificates
    g cov hcov hLevi hdim gdot hK hT hflow evolution
      hShiftedTensorRegularity hnuNeg hnuLower hScalarCont hcont hcontact

end CovariantDerivative.TimeDependentRiemannianMetric
