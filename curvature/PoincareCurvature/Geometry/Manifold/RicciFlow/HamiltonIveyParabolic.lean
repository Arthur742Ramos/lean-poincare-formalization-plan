module

public import HamiltonIveyReaction.Reaction
public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupportLaplacian
public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyScalarBarrier
public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarParabolicInvariant
public import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity

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

/-! The spatial scalar regularity used by the barrier and support arguments
is not an independent analytic input.  On each slice it follows from the
actual curvature tensor, metric raising, and the fibrewise trace. -/

theorem scalarCurvature_mdifferentiableAt_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov₂ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 2)
    (t : ℝ) (x : M) :
    MDiffAt (g.scalarCurvature cov hcov t) x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  change MDiffAt (CovariantDerivative.scalarCurvature (cov := cov t)) x
  exact RicciFlow.scalarCurvature_mdifferentiableAt_of_curvature
    (I := I) (M := M) (cov t) x

theorem eventually_mdifferentiableAt_scalarCurvature_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov₂ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 2)
    (t : ℝ) (x : M) :
    ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y := by
  exact Filter.Eventually.of_forall
    (fun y => g.scalarCurvature_mdifferentiableAt_of_curvature cov hcov hcov₂ t y)

/-! The Hilbert--Schmidt Ricci square is likewise independent of the chosen
Levi--Civita representative.  This lets intrinsic time-variation results be
transported back to the connection family used by the curvature spectrum. -/

theorem ricciNormSq_eq_of_isLeviCivita
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    {cov cov' : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)}
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hcov' : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov' t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hLevi' : g.IsLeviCivita cov') (t : ℝ) (x : M) :
    g.ricciNormSq cov hcov t x = g.ricciNormSq cov' hcov' t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov' t) 1 := hcov' t
  let b := stdOrthonormalBasis ℝ (TM x)
  change (∑ i, ∑ j,
      (g.ricciCurvature cov hcov t x (b i) (b j)) ^ 2) =
    ∑ i, ∑ j,
      (g.ricciCurvature cov' hcov' t x (b i) (b j)) ^ 2
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [g.ricciCurvature_eq_of_isLeviCivita hcov hcov' hLevi hLevi'
    t x (b i) (b j)]

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

/-! At a contact point, the support's time derivative can be propagated all
the way to the logarithmic Hamilton--Ivey defect.  This is the exact chain
rule calculation that turns the metric Ricci-flow equation and the Ricci
time-variation input into the `sdot` required by the support maximum
principle. -/

theorem hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
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
    {K t₀ : ℝ} (hK : 0 < K) {x₀ : M} (ht₀ : t₀ ∈ s)
    (ht₀_nonneg : 0 ≤ t₀)
    (hnu : g.curvatureNu cov hcov hLevi hdim t₀ x₀ < 0)
    (scalarVelocity ricciVelocity : ℝ)
    (hscalar : HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x₀) scalarVelocity t₀)
    (hricci : HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x₀
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀))
      ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t₀ x₀ (τ, x₀))
      (scalarVelocity /
          (-g.curvatureNu cov hcov hLevi hdim t₀ x₀) +
        (g.scalarCurvature cov hcov t₀ x₀ -
            g.curvatureNu cov hcov hLevi hdim t₀ x₀) /
          (g.curvatureNu cov hcov hLevi hdim t₀ x₀) ^ 2 *
          (scalarVelocity - 2 * ricciVelocity -
            (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
              g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) -
        K / (1 + K * t₀)) t₀ := by
  let R : ℝ → ℝ := fun τ => g.scalarCurvature cov hcov τ x₀
  let q : ℝ → ℝ := fun τ => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t₀ x₀ (τ, x₀)
  have hq := g.hasDerivAt_curvatureNuSpacetimeSupport_time_eigenvalue_form
    cov hcov hLevi hdim gdot s hflow ht₀ x₀ scalarVelocity ricciVelocity
    hscalar hricci
  have hq0 : q t₀ = g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
    exact g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀
  have hqneg : q t₀ < 0 := by
    rw [hq0]
    exact hnu
  have hq0ne : q t₀ ≠ 0 := hqneg.ne
  have hR : HasDerivAt R scalarVelocity t₀ := by simpa [R] using hscalar
  have hq' : HasDerivAt q
      (scalarVelocity - 2 * ricciVelocity -
        (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
          g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) t₀ := by
    simpa [q] using hq
  have hquot := hR.div hq'.neg (neg_ne_zero.mpr hq0ne)
  have hlogq := hq'.neg.log (neg_ne_zero.mpr hq0ne)
  have hden : 1 + K * t₀ ≠ 0 := by
    have hdenpos : 0 < 1 + K * t₀ := by
      nlinarith [mul_nonneg hK.le ht₀_nonneg]
    exact hdenpos.ne'
  have hlinear : HasDerivAt (fun τ : ℝ => 1 + K * τ) K t₀ := by
    have h := (hasDerivAt_const t₀ (1 : ℝ)).add
      ((hasDerivAt_id t₀).const_mul K)
    have hfun : (fun τ : ℝ => 1 + K * τ) =
        (fun x : ℝ => 1) + (fun y : ℝ => K * id y) := by
      funext τ
      simp
    rw [hfun]
    simpa only [zero_add, mul_one] using h
  have hscale := (hasDerivAt_const t₀ K).div hlinear hden
  have hlogscale := hscale.log (div_ne_zero hK.ne' hden)
  have htotal := (hquot.sub hlogq).add_const 3 |>.add hlogscale
  change HasDerivAt
    (fun τ => ((R τ) / (-q τ) - Real.log (-q τ) + 3) +
      Real.log (K / (1 + K * τ))) _ t₀
  apply htotal.congr_deriv
  simp only [R, q, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
    id_eq, zero_add, mul_one]
  rw [g.curvatureNuSpacetimeSupport_eq_at_contact
    cov hcov hLevi hdim t₀ x₀]
  field_simp [hnu.ne, hden, hK.ne']
  ring

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

/-! ### The support-form Hamilton--Ivey maximum principle

The ordered eigenvalue fields need not be differentiable when eigenvalues
cross.  The next theorem therefore uses the exact Rayleigh-supported defect
at each hypothetical bad contact.  Its contact certificate records the three
geometric ingredients that the support construction must provide (upper
support, negativity, and the scalar-minus-support sign), together with the
actual supported-defect time derivative, spatial regularity, and parabolic
inequality.  No derivative or Laplacian of the nonsmooth ordered defect is
assumed globally.
-/

/-- Hamilton--Ivey pinching from the exact spacetime Rayleigh support.  This is
the invariant-region theorem in the form needed for a tensor maximum principle;
the remaining evolution task is to derive the contact certificate from the
Ricci-flow curvature evolution equation. -/
theorem hamiltonIveyPinching_of_spacetime_support_certificate
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
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ sdot : ℝ,
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        (∀ᶠ p in 𝓝 (t, x),
          g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0) ∧
        (∀ᶠ p in 𝓝 (t, x),
          0 < g.scalarCurvature cov hcov p.1 p.2 -
            g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p) ∧
        HasDerivAt
          (fun τ : ℝ =>
            g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (τ, x))
          sdot t ∧
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
          g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤ sdot)
    : ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  let w : ℝ → M → ℝ :=
    g.hamiltonIveyDefect cov hcov hLevi hdim K
  let q : ℝ → M → ℝ :=
    g.hamiltonIveyReactionTerm cov hcov hLevi hdim K
  apply g.parabolicNonnegativeInvariant_of_upper_support cov w q hcont
  · intro t x ht hwneg
    obtain ⟨sdot, hupper, hneg, hscalarSupport, htime, hnear, hdiff, hpde⟩ :=
      hcontact ht hwneg
    refine ⟨fun p =>
        g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x p, sdot, ?_, ?_,
      htime, hnear, hdiff, hpde⟩
    · exact g.hamiltonIveySupportedDefect_eq_at_contact
        cov hcov hLevi hdim K t x
    · filter_upwards [hupper, hneg, hscalarSupport] with p hpupper hpneg hppos
      exact g.hamiltonIveyDefect_le_supportedDefect
        cov hcov hLevi hdim K t x p hpupper hpneg hppos
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

/-! The preceding support theorem is now paired with the genuine Ricci-flow
time-variation calculation.  The contact data below expose scalar and Ricci
derivatives, while the support derivative itself is constructed internally;
there is no free `defectTimeDerivative` or arbitrary contact speed left. -/

theorem hamiltonIveyPinching_of_ricciFlow_support_certificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuNeg : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hscalar : ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      ∃ scalarVelocity ricciVelocity,
        HasDerivAt
          (fun τ => g.scalarCurvature cov hcov τ x) scalarVelocity t ∧
        HasDerivAt
          (fun τ => g.ricciCurvature cov hcov τ x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
          ricciVelocity t ∧
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
        scalarVelocity /
            (-g.curvatureNu cov hcov hLevi hdim t x) +
          (g.scalarCurvature cov hcov t x -
              g.curvatureNu cov hcov hLevi hdim t x) /
            (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
            (scalarVelocity - 2 * ricciVelocity -
              (g.curvatureLambda cov hcov hLevi hdim t x +
                g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
          K / (1 + K * t)) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_spacetime_support_certificate
    cov hcov hLevi hdim hK hT hnuNeg hnuLower hscalar hcont
  intro t x ht hdefect
  obtain ⟨scalarVelocity, ricciVelocity, hscalarTime, hricciTime,
    hupper, hneg, hscalarSupport, hnear, hdiff, hpde⟩ := hcontact ht hdefect
  let sdot : ℝ :=
    scalarVelocity /
        (-g.curvatureNu cov hcov hLevi hdim t x) +
      (g.scalarCurvature cov hcov t x -
          g.curvatureNu cov hcov hLevi hdim t x) /
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
        (scalarVelocity - 2 * ricciVelocity -
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
      K / (1 + K * t)
  refine ⟨sdot, hupper, hneg, hscalarSupport, ?_, hnear, hdiff, ?_⟩
  · exact g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
      cov hcov hLevi hdim gdot (Icc 0 T) hflow hK ht ht.1
      (hnuNeg t ht x) scalarVelocity ricciVelocity hscalarTime hricciTime
  · simpa [sdot] using hpde

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
