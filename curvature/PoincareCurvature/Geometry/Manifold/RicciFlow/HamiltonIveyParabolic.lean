module

public import HamiltonIveyReaction.Reaction
public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyScalarBarrier
public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicInvariant

/-!
# Parabolic Hamilton--Ivey invariant region for geometric curvature

This file joins three previously separate ingredients:

* the actual ordered curvature spectrum of a three-dimensional Riemannian
  metric;
* the Hamilton--Ivey pointwise reaction coercivity calculation; and
* the intrinsic compact-manifold scalar parabolic maximum principle.

The resulting theorem is stated directly for the eigenvalues of the genuine
curvature endomorphism.  Its remaining analytic input is the parabolic
inequality for the Hamilton--Ivey defect; this is the precise output required
from curvature evolution and the tensor/eigenvalue support argument.
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

open Bundle Filter Set Topology
open scoped Manifold ContDiff

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
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- The Hamilton--Ivey defect evaluated on the ordered eigenvalues of the
actual three-dimensional curvature endomorphism. -/
def hamiltonIveyDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) : ℝ :=
  HamiltonIveyReaction.defect K t
    (g.curvatureLambda cov hcov hLevi hdim t x)
    (g.curvatureMu cov hcov hLevi hdim t x)
    (g.curvatureNu cov hcov hLevi hdim t x)

/-- The zeroth-order Hamilton--Ivey reaction evaluated on the genuine
curvature spectrum. -/
def hamiltonIveyReactionTerm
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) : ℝ :=
  HamiltonIveyReaction.reaction K t
    (g.curvatureLambda cov hcov hLevi hdim t x)
    (g.curvatureMu cov hcov hLevi hdim t x)
    (g.curvatureNu cov hcov hLevi hdim t x)

/-- Hamilton--Ivey pinching for the genuine geometric curvature spectrum,
from the scalar lower barrier and the parabolic defect inequality supplied by
curvature evolution and the least-eigenvalue support construction. -/
theorem hamiltonIveyPinching_of_defect_parabolic_inequality
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (defectTimeDerivative : ℝ → M → ℝ)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt
        (fun s => g.hamiltonIveyDefect cov hcov hLevi hdim K s x)
        (defectTimeDerivative t x) t)
    (hfNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x,
        MDiffAt (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)) x)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov
          (g.hamiltonIveyDefect cov hcov hLevi hdim K) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        defectTimeDerivative t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ :=
    g.hamiltonIveyDefect cov hcov hLevi hdim K
  let q : ℝ → M → ℝ :=
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K
  apply g.parabolicNonnegativeInvariant cov w defectTimeDerivative q hcont htime
      hfNear hdf hpde
  · intro t ht x hwneg
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    have hscalar' :
        -3 * (K / (1 + K * t)) ≤
          HamiltonIveyReaction.scalar
            (g.curvatureLambda cov hcov hLevi hdim t x)
            (g.curvatureMu cov hcov hLevi hdim t x)
            (g.curvatureNu cov hcov hLevi hdim t x) := by
      simpa only [HamiltonIveyReaction.scalar, hsum] using hscalar t ht x
    exact (HamiltonIveyReaction.hamiltonIvey_reaction_coercive hK ht.1
      horder₁ horder₂ (hnuNeg t ht x) hscalar' hwneg).2.2
  · intro x
    have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    exact HamiltonIveyReaction.defect_zero_nonneg_of_least_eigenvalue_lower_bound
      hK
      (g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x)
      (g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x)
      (hnuNeg 0 hzero x) (hnuLower x)

/-- Geometric Hamilton--Ivey pinching from the exact scalar-curvature
evolution equation and the parabolic defect inequality.  The scalar lower
barrier required by reaction coercivity is derived internally from the
initial least-eigenvalue bound. -/
theorem hamiltonIveyPinching_of_scalar_evolution_and_defect_parabolic_inequality
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t)
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (defectTimeDerivative : ℝ → M → ℝ)
    (hDefectCont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hDefectTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt
        (fun s => g.hamiltonIveyDefect cov hcov hLevi hdim K s x)
        (defectTimeDerivative t x) t)
    (hDefectNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x,
        MDiffAt (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)
    (hDefectDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I)
            (g.hamiltonIveyDefect cov hcov hLevi hdim K t) y)) x)
    (hDefectPDE : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov
          (g.hamiltonIveyDefect cov hcov hLevi hdim K) t x +
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
        defectTimeDerivative t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  have hScalarInitial : ∀ x : M,
      -(3 : ℝ) * K ≤ g.scalarCurvature cov hcov 0 x := by
    intro x
    have horder₁ := g.curvatureLambda_ge_mu cov hcov hLevi hdim 0 x
    have horder₂ := g.curvatureMu_ge_nu cov hcov hLevi hdim 0 x
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim 0 x
    have hthreeNu :
        3 * g.curvatureNu cov hcov hLevi hdim 0 x ≤
          g.curvatureLambda cov hcov hLevi hdim 0 x +
            g.curvatureMu cov hcov hLevi hdim 0 x +
            g.curvatureNu cov hcov hLevi hdim 0 x := by
      linarith
    rw [hsum] at hthreeNu
    linarith [hnuLower x]
  have hScalarStrong := g.scalarCurvature_lowerBarrier_of_evolution cov hcov hdim
    hK.le hScalarCont hScalarTime hScalarNear hScalarDifferential hScalarInitial
  have hScalarWeak : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x := by
    intro t ht x
    have hden₁ : 0 < 1 + K * t := by
      nlinarith [mul_nonneg hK.le ht.1]
    have hden₂ : 0 < 1 + 2 * K * t := by
      nlinarith [mul_nonneg hK.le ht.1]
    have hcompare :
        -3 * (K / (1 + K * t)) ≤
          -(3 : ℝ) * K / (1 + 2 * K * t) := by
      calc
        -3 * (K / (1 + K * t)) =
            (-(3 : ℝ) * K) / (1 + K * t) := by ring
        _ ≤ (-(3 : ℝ) * K) / (1 + 2 * K * t) := by
          rw [div_le_div_iff₀ hden₁ hden₂]
          nlinarith [mul_nonneg (sq_nonneg K) ht.1]
    exact hcompare.trans (hScalarStrong t ht x)
  exact g.hamiltonIveyPinching_of_defect_parabolic_inequality cov hcov hLevi hdim
    hK hT hnuNeg hnuLower hScalarWeak defectTimeDerivative hDefectCont
    hDefectTime hDefectNear hDefectDifferential hDefectPDE

end CovariantDerivative.TimeDependentRiemannianMetric
