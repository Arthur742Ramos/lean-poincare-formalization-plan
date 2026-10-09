import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C0EndpointCompactPositivity
import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
# All-real-time C2 metric endpoint extensions with C0 prescribed velocity

SOURCE CANDIDATE, UNCOMPILED. This is an ordinary endpoint extension, not
a Ricci solution. The original MetricFamily type is used literally: every
real-time slice is a positive C2 Riemannian metric. The initial slice is the
literal supplied g0, and every fixed tangent component has the ordinary
two-sided prescribed derivative. Only manifold boundarylessness is used.

The scalar amplitude is clamped to a fixed compact positivity reserve for
all times, and equals signed time close to zero. Spatial C2 regularity of
the velocity is never assumed. No equation is asserted away from the single
endpoint, and canonical Point 4 remains open.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace RicciFlow.AnalyticPDE.C0Endpoint

open PoincareCurvature.Bundle.Trivialization

def endpointAmplitude (δ h : ℝ) : ℝ := max (-δ) (min δ h)

lemma abs_endpointAmplitude_le {δ : ℝ} (hδ : 0 < δ) (h : ℝ) :
    |endpointAmplitude δ h| ≤ δ := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

@[simp] lemma endpointAmplitude_zero {δ : ℝ} (hδ : 0 < δ) : endpointAmplitude δ 0 = 0 := by
  simp only [endpointAmplitude, min_eq_right hδ.le, max_eq_right (by linarith : -δ ≤ 0)]

lemma endpointAmplitude_eq_self {δ h : ℝ} (hh : |h| < δ) : endpointAmplitude δ h = h := by
  have hbounds := abs_lt.mp hh
  simp only [endpointAmplitude, min_eq_right hbounds.2.le, max_eq_right hbounds.1.le]

lemma endpointAmplitude_eventually_eq_id {δ : ℝ} (hδ : 0 < δ) :
    endpointAmplitude δ =ᶠ[𝓝 (0 : ℝ)] id := by
  have hb : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using Metric.ball_mem_nhds (0 : ℝ) hδ
  exact hb.mono fun h hh => endpointAmplitude_eq_self hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "BilE" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "Cover" => FiniteSmoothPreferredTrivializingCover I (F := E) (V := TM)

variable {d : ℕ}

def endpointTensor (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (δ h : ℝ) : ∀ x : M, T₂ x :=
  fun x => g₀.inner x + endpointAmplitude δ h • gaussianTensor v C b h x

@[simp] lemma endpointTensor_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) {δ : ℝ} (hδ : 0 < δ) :
    endpointTensor g₀ v C b δ 0 = g₀.inner := by
  funext x
  simp only [endpointTensor, endpointAmplitude_zero hδ, zero_smul, add_zero]

lemma endpointTensor_symmetric
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (δ h : ℝ)
    (x : M) (u w : TM x) : endpointTensor g₀ v C b δ h x u w =
      endpointTensor g₀ v C b δ h x w u := by
  simp only [endpointTensor, ContinuousLinearMap.add_apply, _root_.smul_apply, smul_eq_mul,
    g₀.symm x u w, gaussianTensor_symmetric v C b h x u w]

lemma contMDiff_two_endpointTensor
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) {δ : ℝ} (hδ : 0 < δ) (h : ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, BilE)) 2
      (fun x => TotalSpace.mk' BilE (E := T₂) x (endpointTensor g₀ v C b δ h x)) := by
  by_cases hh : h = 0
  · simpa only [hh, endpointTensor_zero g₀ v C b hδ] using g₀.contMDiff
  · exact g₀.contMDiff.add_section
      (contMDiff_const.smul_section (contMDiff_two_gaussianTensor v C b hh))

lemma hasDerivAt_endpointTensor_component_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) {δ : ℝ} (hδ : 0 < δ)
    (x : M) (u w : TM x) :
    HasDerivAt (fun h => endpointTensor g₀ v C b δ h x u w) (v.tensor x u w) 0 := by
  have hbase := (hasDerivAt_time_mul_gaussianTensor v C b x u w).const_add (g₀.inner x u w)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [endpointAmplitude_eventually_eq_id hδ] with h hh
  simp only [endpointTensor, ContinuousLinearMap.add_apply, _root_.smul_apply, smul_eq_mul, hh,
    id_eq]

/-- Reify the actual clamped tensor formula as a Riemannian metric at every
real time. The concrete reserve proof is an intermediate input here; the
exported construction below produces it internally. -/
def centeredMetric (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (hreserve : ∀ a : ℝ, |a| ≤ δ → ∀ h : ℝ, ∀ x : M, ∀ w : TM x, w ≠ 0 →
      0 < (g₀.inner x + a • gaussianTensor v C b h x) w w)
    (h : ℝ) : Bundle.ContMDiffRiemannianMetric I 2 E TM := by
  classical
  by_cases hh : h = 0
  · exact g₀
  · let B := endpointTensor g₀ v C b δ h
    have hBpos : ∀ x : M, ∀ w : TM x, w ≠ 0 → 0 < B x w w :=
      hreserve (endpointAmplitude δ h) (abs_endpointAmplitude_le hδ h) h
    refine {
      inner := B
      symm := endpointTensor_symmetric g₀ v C b δ h
      pos := hBpos
      isVonNBounded := ?_
      contMDiff := contMDiff_two_endpointTensor g₀ v C b hδ h }
    intro x
    letI : FiniteDimensional ℝ (TM x) := by
      change FiniteDimensional ℝ E
      infer_instance
    exact Bundle.ContinuousLinearMap.isVonNBounded_sublevel_one_of_pos (B x) (hBpos x)

@[simp] lemma centeredMetric_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (hreserve : ∀ a : ℝ, |a| ≤ δ → ∀ h : ℝ, ∀ x : M, ∀ w : TM x, w ≠ 0 →
      0 < (g₀.inner x + a • gaussianTensor v C b h x) w w) :
    centeredMetric g₀ v C b δ hδ hreserve 0 = g₀ := by
  simp only [centeredMetric, dite_true]

lemma centeredMetric_inner
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (hreserve : ∀ a : ℝ, |a| ≤ δ → ∀ h : ℝ, ∀ x : M, ∀ w : TM x, w ≠ 0 →
      0 < (g₀.inner x + a • gaussianTensor v C b h x) w w)
    (h : ℝ) (x : M) :
    (centeredMetric g₀ v C b δ hδ hreserve h).inner x = endpointTensor g₀ v C b δ h x := by
  classical
  by_cases hh : h = 0
  · simp only [hh, centeredMetric_zero, endpointTensor_zero g₀ v C b hδ]
  · simp only [centeredMetric, dif_neg hh]

/-- Endpoint-only construction with no atlas, smoothing, density, solver,
rank, or global-model-boundarylessness witness in the exported hypotheses.
The C0 velocity is interpreted in the actual tensor bundle using the literal
g0 background norm; its topology is the preexisting tensor-bundle topology.
No PointFourClosedManifoldContract inhabitant is asserted. -/
theorem exists_c2_metricFamily_with_c0_endpoint_velocity
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (t₀ : ℝ) :
    letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
    ∀ v : ContinuousSymmetricVelocity (I := I) (M := M),
      ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
        g t₀ = g₀ ∧ ∀ x : M, ∀ u w : TM x,
          HasDerivAt (fun t => RicciFlow.metricTensor g t x u w) (v.tensor x u w) t₀ := by
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  intro v
  let C : Cover := preferredCover (I := I) (M := M)
  let b := Module.finBasis ℝ E
  obtain ⟨δ, hδ, hreserve⟩ := exists_gaussianTensor_positivity_reserve g₀ v C b
  let g : RicciFlow.MetricFamily (I := I) (M := M) :=
    fun t => centeredMetric g₀ v C b δ hδ hreserve (t - t₀)
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, sub_self] using centeredMetric_zero g₀ v C b δ hδ hreserve
  · intro x u w
    have hcenter := hasDerivAt_endpointTensor_component_zero g₀ v C b hδ x u w
    have hshift : HasDerivAt (fun t : ℝ => t - t₀) 1 t₀ := by
      simpa only [sub_zero] using (hasDerivAt_id t₀).sub_const t₀
    have hcenter' : HasDerivAt
        (fun t => endpointTensor g₀ v C b δ (t - t₀) x u w) (v.tensor x u w) t₀ := by
      have hcenterAt : HasDerivAt (fun h => endpointTensor g₀ v C b δ h x u w)
          (v.tensor x u w) (t₀ - t₀) := by
        simpa only [sub_self] using hcenter
      simpa only [mul_one] using hcenterAt.comp t₀ hshift
    simpa only [g, RicciFlow.metricTensor, centeredMetric_inner] using hcenter'

end RicciFlow.AnalyticPDE.C0Endpoint
