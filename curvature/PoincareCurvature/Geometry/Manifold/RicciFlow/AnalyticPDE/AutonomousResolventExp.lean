import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The autonomous fundamental solution is the operator exponential

For a **time-independent** (autonomous) linear generator `A₀ : E →L[ℝ] E`, the campaign's resolvent
`fundamentalSolution` (built abstractly from any flow family `Φ` of the linear variational field via
Picard–Lindelöf / Grönwall uniqueness) coincides with Mathlib's analytic operator exponential:

`fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀)`.

This is the bridge from the `IsIntegralCurve`-based resolvent used throughout the smooth-dependence
layer to the analytic `NormedSpace.exp`.  It matters because `NormedSpace.exp` is analytic in its
argument, so this identity transports the exponential's analytic dependence on the operator to the
autonomous resolvent — precisely the smooth-dependence structure needed for the **frozen** (autonomous,
bounded-linear) geometric Ricci–DeTurck chart generator, whose fibre generator depends on the spatial
point.  Everything is proved from Mathlib's `hasDerivAt_exp_smul_const'` and the campaign's global
integral-curve uniqueness `eq_of_isIntegralCurve_of_eq_at`; no PDE or manifold content is used.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The operator-exponential curve solves the autonomous linear ODE.**  For a fixed generator
`A₀ : E →L[ℝ] E` and initial point `x`, the path `t ↦ exp ((t - t₀) • A₀) x` is a global integral
curve of the (time-independent) vector variational field `variationalFieldVec (fun _ => A₀)`, i.e. it
obeys `γ'(t) = A₀ (γ t)` everywhere.  Proved from Mathlib's `hasDerivAt_exp_smul_const'`
(`d/du exp (u • A₀) = A₀ * exp (u • A₀)`) precomposed with the shift `t ↦ t - t₀` and evaluated at the
fixed direction `x` via `HasDerivAt.clm_apply`. -/
theorem isIntegralCurve_exp_smul_const (A₀ : E →L[ℝ] E) (t₀ : ℝ) (x : E) :
    IsIntegralCurve (fun t => NormedSpace.exp ((t - t₀) • A₀) x)
      (variationalFieldVec (fun _ => A₀)) := by
  intro t
  have hbase : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) (t - t₀) :=
    hasDerivAt_exp_smul_const' A₀ (t - t₀)
  have hshift : HasDerivAt (fun t : ℝ => t - t₀) (1 : ℝ) t :=
    (hasDerivAt_id t).sub_const t₀
  have hcomp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) t := by
    have := HasDerivAt.scomp t hbase hshift
    simpa using this
  have hpt : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀) x)
      ((A₀ * NormedSpace.exp ((t - t₀) • A₀)) x) t := by
    have := HasDerivAt.clm_apply hcomp (hasDerivAt_const t x)
    simpa using this
  simpa [variationalFieldVec, ContinuousLinearMap.mul_apply] using hpt

/-! ### The affine autonomous ODE `y' = L y + b`

The frozen (autonomous) Ricci–DeTurck chart operator is **affine** in the section state,
`A τ s = L s + b`, so its Banach evolution solves the *affine* linear ODE `y' = L y + b`, **not** the
homogeneous one solved by `exp ((t - t₀) • L)`.  We solve the affine ODE explicitly and globally by the
classical augmentation trick: adjoin a scalar coordinate that carries the constant `b`.  On `E × ℝ` the
**augmented generator** `(v, s) ↦ (L v + s • b, 0)` is a genuine bounded linear operator whose scalar
coordinate is conserved (`≡ 1`), and the first coordinate of its operator-exponential orbit through
`(y₀, 1)` is the affine solution.  Everything reduces to `isIntegralCurve_exp_smul_const` on `E × ℝ`;
no PDE, integral, or manifold content is used. -/

/-- **The augmented generator** on `E × ℝ` turning the affine ODE `y' = L y + b` into a homogeneous
linear one: `(v, s) ↦ (L v + s • b, 0)`.  The scalar coordinate `s` carries the inhomogeneity `b` and
is conserved by the flow (its own derivative is `0`), so starting it at `1` reproduces the `+ b`. -/
noncomputable def affineAugment (L : E →L[ℝ] E) (b : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ E ℝ)
      + (ContinuousLinearMap.snd ℝ E ℝ).smulRight b).prod (0 : (E × ℝ) →L[ℝ] ℝ)

omit [CompleteSpace E] in
@[simp] theorem affineAugment_apply (L : E →L[ℝ] E) (b : E) (p : E × ℝ) :
    affineAugment L b p = (L p.1 + p.2 • b, 0) := by
  simp [affineAugment]

/-- **The affine autonomous fundamental solution** `y(t)`: the first coordinate of the augmented
operator-exponential orbit through `(y₀, 1)`.  It is the global solution of `y' = L y + b`,
`y t₀ = y₀`. -/
noncomputable def affineFundamentalSolution
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) : E :=
  (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)).1

/-- **The scalar coordinate is conserved.**  The second coordinate of the augmented orbit through
`(y₀, 1)` is identically `1`: it solves `s' = 0` with `s t₀ = 1`, so global constancy
(`is_const_of_deriv_eq_zero`) pins it to `1`.  This is exactly what turns the augmented flow's first
coordinate into the genuine `+ b` inhomogeneity. -/
theorem affineAugment_snd_orbit_eq_one (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)).2 = 1 := by
  have hsnd : ∀ s : ℝ,
      HasDerivAt (fun s => (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)).2) 0 s := by
    intro s
    have hc :
        HasDerivAt (fun s => NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))
          (affineAugment L b (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))) s := by
      simpa [variationalFieldVec] using
        isIntegralCurve_exp_smul_const (affineAugment L b) t₀ (y₀, 1) s
    have hproj := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt s hc
    simpa [Function.comp, ContinuousLinearMap.coe_snd', affineAugment_apply] using hproj
  have hconst :=
    is_const_of_deriv_eq_zero
      (f := fun s => (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)).2)
      (fun s => (hsnd s).differentiableAt) (fun s => (hsnd s).deriv) t t₀
  have h0 : (NormedSpace.exp ((t₀ - t₀) • affineAugment L b) (y₀, 1)).2 = 1 := by
    simp [sub_self, zero_smul, NormedSpace.exp_zero]
  exact hconst.trans h0

omit [CompleteSpace E] in
/-- **`y t₀ = y₀`.**  The affine fundamental solution starts at the initial value. -/
theorem affineFundamentalSolution_initial (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) :
    affineFundamentalSolution L b t₀ y₀ t₀ = y₀ := by
  simp [affineFundamentalSolution, sub_self, zero_smul, NormedSpace.exp_zero,
    ContinuousLinearMap.one_apply]

/-- **The affine fundamental solution solves the affine ODE `y' = L y + b`.**  For every time `t`,
`HasDerivAt (affineFundamentalSolution L b t₀ y₀) (L (affineFundamentalSolution L b t₀ y₀ t) + b) t`.
The augmented orbit is a global integral curve of the autonomous, bounded-linear augmented generator by
`isIntegralCurve_exp_smul_const`; projecting to the first coordinate and using that the scalar
coordinate stays `1` (`affineAugment_snd_orbit_eq_one`) yields the affine field `L y + b`.  This is the
Banach evolution of the frozen (affine) Ricci–DeTurck chart operator `A τ s = L s + b`. -/
theorem hasDerivAt_affineFundamentalSolution
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    HasDerivAt (affineFundamentalSolution L b t₀ y₀)
      (L (affineFundamentalSolution L b t₀ y₀ t) + b) t := by
  have hc :
      HasDerivAt (fun s => NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))
        (affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))) t := by
    simpa [variationalFieldVec] using
      isIntegralCurve_exp_smul_const (affineAugment L b) t₀ (y₀, 1) t
  have hproj := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t hc
  have hfst :
      HasDerivAt (affineFundamentalSolution L b t₀ y₀)
        ((affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))).1) t := by
    simpa [Function.comp, ContinuousLinearMap.coe_fst', affineFundamentalSolution] using hproj
  have hval :
      (affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))).1
        = L (affineFundamentalSolution L b t₀ y₀ t) + b := by
    rw [affineAugment_apply]
    simp only [affineFundamentalSolution]
    rw [affineAugment_snd_orbit_eq_one, one_smul]
  rw [hval] at hfst
  exact hfst

variable {Φ : E → ℝ → E} {t₀ : ℝ}

/-- **The autonomous fundamental solution is the operator exponential.**  For a *time-independent*
generator `A₀ : E →L[ℝ] E` the campaign resolvent (built from any flow family `Φ` of the linear
variational field anchored at `t₀`) equals `NormedSpace.exp ((t - t₀) • A₀)`.

Both sides are integral curves (at each fixed direction `x`) of the same globally
`‖A₀‖`-Lipschitz autonomous field `variationalFieldVec (fun _ => A₀)`, and both send `t₀ ↦ x`
(`Φ x t₀ = x` and `exp (0 • A₀) x = x`); global integral-curve uniqueness
(`eq_of_isIntegralCurve_of_eq_at`) forces them to agree at every time and every direction. -/
theorem fundamentalSolution_const_eq_exp {A₀ : E →L[ℝ] E} {K : ℝ≥0}
    (hA : ∀ t, ‖(fun _ : ℝ => A₀) t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec (fun _ => A₀)))
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀) := by
  ext x
  rw [fundamentalSolution_apply]
  refine eq_of_isIntegralCurve_of_eq_at (K := K) (t₁ := t₀)
    (fun s => lipschitzWith_variationalFieldVec hA s) (hΦ x)
    (isIntegralCurve_exp_smul_const A₀ t₀ x) ?_ t
  rw [h0]
  simp [NormedSpace.exp_zero]

/-- **The operator-exponential map is smooth.**  For a fixed scalar `s`, the map
`A₀ ↦ exp (s • A₀)` on `E →L[ℝ] E` is `ContDiff ℝ n` for every `n`.  Immediate from the analyticity of
`NormedSpace.exp` on the (complete) operator Banach algebra (`NormedSpace.exp_analytic`, whose power
series has infinite radius) composed with the smooth scalar rescaling `A₀ ↦ s • A₀`. -/
theorem contDiff_exp_smul_const (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun A₀ : E →L[ℝ] E => NormedSpace.exp (s • A₀)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (contDiff_const_smul s)

/-- **Smooth dependence of the autonomous resolvent on a parameter.**  If a family of autonomous
generators `A : X → (E →L[ℝ] E)` over a normed parameter space `X` is `C^n`, then the autonomous
resolvent `x ↦ exp (s • A x)` is `C^n`.  This transports smooth dependence of the generator to smooth
dependence of the resolvent — the parameter-smoothness form that, via `fundamentalSolution_const_eq_exp`,
turns spatial (`x`-dependent) smoothness of a frozen bounded-linear generator into spatial smoothness of
its Banach evolution, with no `IsIntegralCurve` bookkeeping. -/
theorem contDiff_exp_smul_of_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → (E →L[ℝ] E)} {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) (s : ℝ) :
    ContDiff ℝ n (fun x => NormedSpace.exp (s • A x)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (ContDiff.const_smul s hA)

/-- **Joint `(time, parameter)` smoothness of the parametrized autonomous resolvent.**  If a family of
autonomous generators `A : X → (E →L[ℝ] E)` over a normed parameter space `X` is `C^n`, then the
time-dependent resolvent `(t, x) ↦ exp ((t - t₀) • A x)` is jointly `C^n` on `ℝ × X`.  This is the exact
joint-smoothness shape a downstream realization consumes: for the frozen (autonomous, bounded-linear)
Ricci–DeTurck chart generator whose fibre generator `A x` depends `C^n`-smoothly on the spatial point `x`,
`fundamentalSolution_const_eq_exp` identifies its Banach evolution with `exp ((t - t₀) • A x)`, so this
lemma yields joint smoothness of that evolution in `(time, space)` — the parabolic-free regularity of a
0th-order generator's flow.  Assembled from the smoothness of `NormedSpace.exp`, the bilinear scalar
action, and the coordinate projections. -/
theorem contDiff_exp_sub_smul_of_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → (E →L[ℝ] E)} {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) (t₀ : ℝ) :
    ContDiff ℝ n (fun p : ℝ × X => NormedSpace.exp ((p.1 - t₀) • A p.2)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  have h1 : ContDiff ℝ n (fun p : ℝ × X => p.1 - t₀) :=
    ContDiff.sub contDiff_fst contDiff_const
  have h2 : ContDiff ℝ n (fun p : ℝ × X => A p.2) := ContDiff.comp hA contDiff_snd
  exact ContDiff.comp hana.contDiff (ContDiff.smul h1 h2)

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
