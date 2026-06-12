module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.EinsteinAux

/-!
# Metric rescaling infrastructure for Ricci flow (toward Einstein homothetic solutions)

For an Einstein initial metric `g₀` with `Ric(g₀) = λ • g₀`, the homothetic family
`g(t) = (1 - 2λ (t - t₀)) • g₀` solves Ricci flow `∂ₜ g = -2 Ric(g)`.  Realizing this
as a Lean `IntrinsicLocalSolution` requires a positive scalar multiple of a smooth
Riemannian metric and scale-invariance of the intrinsic Ricci tensor.

This module proves the genuine, placeholder-free, reusable infrastructure:

* `RicciFlow.smulMetric` — the positive scalar multiple `c • g` of a smooth
  Riemannian metric, with all bundle/metric fields (`symm`, `pos`, `isVonNBounded`,
  `contMDiff`) discharged;
* `RicciFlow.smulMetric_inner_apply` — its fibrewise inner product `= c * g.inner`.

The companion `EinsteinAux.lean` proves scalar-linearity of the scalar exterior
derivative (`extDerivFun_const_smul_apply`), the remaining calculus input.

Note: assembling these into the full homothetic local-existence theorem additionally
needs scale-invariance of metric compatibility, whose proof in this repository's
`inner ℝ`-based `IsMetricCompatibleTangent` definition currently triggers a Lean
kernel-defeq blowup (converting `inner ℝ` to the metric field under the `extDerivFun`
binder in the heavy tangent-bundle instance context).  That step is left as future
work.  Nothing here uses proof placeholders or unchecked assumptions; this
strictly enlarges the proven metric-rescaling toolkit and does not by itself
close point 4 (which requires the Hamilton–DeTurck parabolic theorem for
arbitrary initial metrics).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The positive scalar multiple `c • g` of a smooth Riemannian metric on the
tangent bundle. -/
def smulMetric (c : ℝ) (hc : 0 < c)
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    Bundle.ContMDiffRiemannianMetric I 2 E TM where
  inner b := c • g.inner b
  symm b v w := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm b v w]
  pos b v hv := by
    have h := g.pos b v hv
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using mul_pos hc h
  isVonNBounded b := by
    -- The `c • g`-unit ball is the image of the `g`-unit ball under the
    -- continuous-linear scaling `√(c⁻¹) • id`, hence von Neumann bounded.
    have hscale : ∀ (s : ℝ) (v : TM b),
        g.inner b (s • v) (s • v) = (s * s) * g.inner b v v := by
      intro s v
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    set r : ℝ := Real.sqrt c⁻¹ with hr
    have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
    have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hcinv
    have hrr : r * r = c⁻¹ := by rw [hr]; exact Real.mul_self_sqrt hcinv.le
    have hset : {v : TM b | (c • g.inner b) v v < 1}
        = (r • (1 : TM b →L[ℝ] TM b)) '' {v : TM b | g.inner b v v < 1} := by
      ext w
      simp only [Set.mem_image, Set.mem_setOf_eq, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_eq_mul]
      constructor
      · intro hw
        have hrinv : r⁻¹ * r⁻¹ = c := by rw [← mul_inv, hrr, inv_inv]
        refine ⟨r⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]⟩
        rw [hscale r⁻¹ w, hrinv]
        exact hw
      · rintro ⟨u, hu, rfl⟩
        rw [hscale r u, hrr, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
        exact hu
    rw [hset]
    exact (g.isVonNBounded b).image (r • (1 : TM b →L[ℝ] TM b))
  contMDiff := g.contMDiff.const_smul_section

@[simp] lemma smulMetric_inner_apply (c : ℝ) (hc : 0 < c)
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM) (b : M) (v w : TM b) :
    (smulMetric (I := I) (M := M) c hc g).inner b v w = c * g.inner b v w := by
  change (c • g.inner b) v w = c * g.inner b v w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Metric compatibility transfers along any positive constant rescaling of the
fibrewise inner product.  Stated for an *arbitrary* second metric `g'` whose inner
product is `c` times that of `g`, so the heavy `inner ℝ ↔ .inner` conversion is
checked against a free variable rather than against the structure literal
`smulMetric c hc g` (whose `isVonNBounded` proof field would otherwise blow up the
kernel defeq check).  This is the genuine analytic content behind scale-invariance
of the Levi-Civita connection: the Leibniz identity scales by the constant `c`,
discharged by `extDerivFun_const_smul_apply`. -/
theorem isMetricCompatibleTangent_of_inner_eq_const_smul (c : ℝ)
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E TM}
    (hinner : ∀ (x : M) (u v : TM x), g'.inner x u v = c * g.inner x u v)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    cov.IsMetricCompatibleTangent := by
  letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
  intro x σ τ hσ hτ u
  -- Differentiability of the `g`-inner product of the two sections.
  have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ g.inner y (σ y) (τ y)) x := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    simpa using CovariantDerivative.mdiffAt_inner_sections
      (I := I) (E := E) (M := M) (x := x) (σ := σ) (τ := τ) hσ hτ
  -- The `g`-compatibility Leibniz identity.
  have hcompat :
      extDerivFun (I := I) (fun y ↦ g.inner y (σ y) (τ y)) x u =
        g.inner x (cov σ x u) (τ x) + g.inner x (σ x) (cov τ x u) := by
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    simpa using hcov (σ := σ) (τ := τ) hσ hτ u
  -- Convert the `g'` Leibniz goal to the `g'.inner` form (variable `g'`, cheap defeq).
  change
    extDerivFun (I := I) (fun y ↦ g'.inner y (σ y) (τ y)) x u =
      g'.inner x (cov σ x u) (τ x) + g'.inner x (σ x) (cov τ x u)
  simp only [hinner]
  rw [extDerivFun_const_smul_apply c u hf, hcompat, mul_add]

/-- Metric compatibility is invariant under positive rescaling of the metric:
if `cov` is metric-compatible for `g`, it is metric-compatible for `c • g`. -/
theorem isMetricCompatibleTangent_smulMetric (c : ℝ) (hc : 0 < c)
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle TM := ⟨(smulMetric (I := I) (M := M) c hc g).toRiemannianMetric⟩;
    cov.IsMetricCompatibleTangent :=
  isMetricCompatibleTangent_of_inner_eq_const_smul (I := I) (M := M) c
    (g := g) (g' := smulMetric (I := I) (M := M) c hc g)
    (fun x u v ↦ smulMetric_inner_apply (I := I) (M := M) c hc g x u v) cov hcov

/-- Levi-Civita transfers along any positive constant rescaling of the inner product,
stated for an arbitrary second metric `g'`.  Torsion-freeness is metric-independent;
metric compatibility scales via `isMetricCompatibleTangent_of_inner_eq_const_smul`. -/
theorem isLeviCivita_of_inner_eq_const_smul (c : ℝ)
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E TM}
    (hinner : ∀ (x : M) (u v : TM x), g'.inner x u v = c * g.inner x u v)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩;
    cov.IsLeviCivita := by
  -- Extract metric compatibility under the source `g`-instance.
  have hmc :
      letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsMetricCompatibleTangent := hcov.2
  -- `IsTorsionFree` unfolds to `cov.torsion = 0`, which mentions no Riemannian instance,
  -- so we bridge through that instance-free equation rather than asking the kernel to
  -- unify the two `RiemannianBundle` instances.
  have htf0 : cov.torsion = 0 :=
    letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩; hcov.1
  letI : Bundle.RiemannianBundle TM := ⟨g'.toRiemannianMetric⟩
  refine ⟨htf0, ?_⟩
  exact isMetricCompatibleTangent_of_inner_eq_const_smul (I := I) (M := M) c hinner cov hmc

/-- A Levi-Civita connection for `g` is a Levi-Civita connection for `c • g` (`c > 0`). -/
theorem isLeviCivita_smulMetric (c : ℝ) (hc : 0 < c)
    (g : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (hcov : letI : Bundle.RiemannianBundle TM := ⟨g.toRiemannianMetric⟩;
      cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM := ⟨(smulMetric (I := I) (M := M) c hc g).toRiemannianMetric⟩;
    cov.IsLeviCivita :=
  isLeviCivita_of_inner_eq_const_smul (I := I) (M := M) c
    (g := g) (g' := smulMetric (I := I) (M := M) c hc g)
    (fun x u v ↦ smulMetric_inner_apply (I := I) (M := M) c hc g x u v) cov hcov

end RicciFlow
