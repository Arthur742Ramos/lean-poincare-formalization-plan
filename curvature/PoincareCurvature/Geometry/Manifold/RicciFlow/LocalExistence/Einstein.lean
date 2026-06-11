module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

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

end RicciFlow
