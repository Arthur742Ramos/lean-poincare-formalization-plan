module

public import HamiltonIveyReaction.Reaction
public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupportLaplacian
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

/-- The smooth test defect obtained by replacing the least eigenvalue with
its genuine spacetime Rayleigh support while retaining actual scalar
curvature. -/
def hamiltonIveySupportedDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) (p : ℝ × M) : ℝ :=
  HamiltonIveyReaction.nuProfile
      (g.scalarCurvature cov hcov p.1 p.2)
      (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) +
    3 + Real.log (K / (1 + K * p.1))

/-- The supported defect touches the actual Hamilton--Ivey defect at the
chosen spacetime contact point. -/
theorem hamiltonIveySupportedDefect_eq_at_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) :
    g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀ (t₀, x₀) =
      g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ := by
  rw [hamiltonIveySupportedDefect,
    g.curvatureNuSpacetimeSupport_eq_at_contact cov hcov hLevi hdim t₀ x₀,
    hamiltonIveyDefect, HamiltonIveyReaction.defect_eq_nuProfile]
  simp only [Prod.fst, Prod.snd]
  rw [HamiltonIveyReaction.scalar]
  rw [g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t₀ x₀]

/-- Wherever the Rayleigh support is negative and `R - support` is positive,
the actual defect lies below its smooth supported representative. -/
theorem hamiltonIveyDefect_le_supportedDefect
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M) (p : ℝ × M)
    (hnuSupport : g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    (hSupportNeg :
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0)
    (hScalarSubSupport : 0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) :
    g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2 ≤
      g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀ p := by
  have h := HamiltonIveyReaction.defect_le_nuProfile_of_upper_support
    (K := K) (t := p.1)
    (lambda := g.curvatureLambda cov hcov hLevi hdim p.1 p.2)
    (mu := g.curvatureMu cov hcov hLevi hdim p.1 p.2)
    (nu := g.curvatureNu cov hcov hLevi hdim p.1 p.2)
    (q := g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    hnuSupport hSupportNeg
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim p.1 p.2
  have hcond : 0 <
      HamiltonIveyReaction.scalar
          (g.curvatureLambda cov hcov hLevi hdim p.1 p.2)
          (g.curvatureMu cov hcov hLevi hdim p.1 p.2)
          (g.curvatureNu cov hcov hLevi hdim p.1 p.2) -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p := by
    rw [HamiltonIveyReaction.scalar, hsum]
    exact hScalarSubSupport
  have hout := h hcond
  simpa [hamiltonIveyDefect, hamiltonIveySupportedDefect,
    HamiltonIveyReaction.scalar, hsum] using hout

/-- At a bad contact point, the scalar-minus-support sign required for the
preceding comparison follows from the scalar barrier and the negative defect;
it is not an additional geometric assumption. -/
theorem scalarCurvature_sub_spacetimeSupport_pos_at_bad_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t₀ : ℝ} (hK : 0 < K) (ht₀ : 0 ≤ t₀) (x₀ : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (hscalar : -3 * (K / (1 + K * t₀)) ≤
      g.scalarCurvature cov hcov t₀ x₀)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ < 0) :
    0 < g.scalarCurvature cov hcov t₀ x₀ -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) := by
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t₀ x₀
  have hpos := HamiltonIveyReaction.lambda_add_mu_pos_of_defect_neg hK ht₀
    (g.curvatureLambda_ge_mu cov hcov hLevi hdim t₀ x₀)
    (g.curvatureMu_ge_nu cov hcov hLevi hdim t₀ x₀) hnu
    (by simpa [HamiltonIveyReaction.scalar, hsum] using hscalar)
    (by simpa [hamiltonIveyDefect] using hdefect)
  rw [g.curvatureNuSpacetimeSupport_eq_at_contact
    cov hcov hLevi hdim t₀ x₀]
  linarith

/-- Once the three open sign/support conditions hold near a bad contact, a
local minimum of the nonsmooth eigenvalue defect transfers to the smooth
Rayleigh-supported defect.  The contact equality and comparison are both
geometric theorems proved above. -/
theorem hamiltonIveySupportedDefect_isLocalMin
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t₀ : ℝ) (x₀ : M)
    (hmin : IsLocalMin
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2) (t₀, x₀))
    (hnuSupport : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p)
    (hSupportNeg : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0)
    (hScalarSubSupport : ∀ᶠ p in nhds (t₀, x₀),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p) :
    IsLocalMin
      (g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀)
      (t₀, x₀) := by
  rw [IsLocalMin, IsMinFilter] at hmin ⊢
  filter_upwards [hmin, hnuSupport, hSupportNeg, hScalarSubSupport] with
      p hpmin hpnu hpneg hppos
  rw [g.hamiltonIveySupportedDefect_eq_at_contact
    cov hcov hLevi hdim K t₀ x₀]
  exact hpmin.trans (g.hamiltonIveyDefect_le_supportedDefect
    cov hcov hLevi hdim K t₀ x₀ p hpnu hpneg hppos)

/-- At a negative-defect contact, ordinary continuity supplies all open
sign neighborhoods, while metric-square continuity supplies the genuine
least-eigenvalue upper support.  Thus the local-minimum transfer requires no
independent sign or comparison assumptions. -/
theorem hamiltonIveySupportedDefect_isLocalMin_at_bad_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    {K t₀ : ℝ} (hK : 0 < K) (ht₀ : 0 ≤ t₀) (x₀ : M)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (hscalar : -3 * (K / (1 + K * t₀)) ≤
      g.scalarCurvature cov hcov t₀ x₀)
    (hdefect : g.hamiltonIveyDefect cov hcov hLevi hdim K t₀ x₀ < 0)
    (hmin : IsLocalMin
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2) (t₀, x₀))
    (hnormContinuous : ContinuousAt
      (fun p : ℝ × M => (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2))
      (t₀, x₀))
    (hScalarContinuous : ContinuousAt
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2) (t₀, x₀))
    (hSupportContinuous : ContinuousAt
      (g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀) (t₀, x₀)) :
    IsLocalMin
      (g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t₀ x₀)
      (t₀, x₀) := by
  have hnuSupport := g.curvatureNu_le_spacetimeSupport_eventually
    cov hcov hLevi hdim t₀ x₀ hnormContinuous
  have hSupportNegAt :
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) < 0 := by
    rw [g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀]
    exact hnu
  have hSupportNeg : ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p < 0 :=
    hSupportContinuous.eventually (isOpen_Iio.mem_nhds hSupportNegAt)
  have hScalarSubSupportAt :=
    g.scalarCurvature_sub_spacetimeSupport_pos_at_bad_contact
      cov hcov hLevi hdim hK ht₀ x₀ hnu hscalar hdefect
  have hScalarSubSupport : ∀ᶠ p in nhds (t₀, x₀),
      0 < g.scalarCurvature cov hcov p.1 p.2 -
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p :=
    (hScalarContinuous.sub hSupportContinuous).eventually
      (isOpen_Ioi.mem_nhds hScalarSubSupportAt)
  exact g.hamiltonIveySupportedDefect_isLocalMin cov hcov hLevi hdim
    K t₀ x₀ hmin hnuSupport hSupportNeg hScalarSubSupport

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
