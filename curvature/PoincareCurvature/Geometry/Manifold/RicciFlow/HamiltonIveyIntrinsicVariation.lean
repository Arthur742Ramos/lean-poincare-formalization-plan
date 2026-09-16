import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyParabolic
import PoincareCurvature.Geometry.Manifold.RicciFlow.MetricInverseVariation

/-!
# Intrinsic time variation for the Hamilton--Ivey support

The parabolic Hamilton--Ivey layer is phrased using an arbitrary smooth
Levi--Civita representative `cov`, because that is the connection family used
by the curvature spectrum.  The metric-variation layer, on the other hand,
packages the Ricci time derivative intrinsically as a bilinear tensor.  This
file is the transport bridge between the two APIs: it derives the scalar and
contact Ricci derivatives for the chosen representative from one genuine
intrinsic Ricci derivative.

No coordinate matrix or symmetrized readout is introduced here.  The only
auxiliary object is the canonical smooth Levi--Civita family used by the
intrinsic API, and all occurrences of it are eliminated by the proved
Levi--Civita invariance lemmas.
-/

noncomputable section

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

/-- The contact speed written directly from a genuine intrinsic Ricci-tensor
time derivative.  The scalar velocity is the metric-variation trace
`2 |Ric|² + tr_g(Ric')`, while the second velocity is the same tensor
derivative evaluated on the contact field. -/
def hamiltonIveyIntrinsicSupportSpeed
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M)
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ) : ℝ :=
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)
  let v : TM x := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t x x
  scalarVelocity / (-g.curvatureNu cov hcov hLevi hdim t x) +
    (g.scalarCurvature cov hcov t x -
        g.curvatureNu cov hcov hLevi hdim t x) /
      (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 *
      (scalarVelocity - 2 * ricciVelocity x v v -
        (g.curvatureLambda cov hcov hLevi hdim t x +
          g.curvatureMu cov hcov hLevi hdim t x) ^ 2) -
    K / (1 + K * t)

/-! The canonical smooth Levi--Civita family is kept local in the proofs
below.  These abbreviations make the transport equalities readable while
remaining definitionally tied to the repository's intrinsic API. -/

section IntrinsicTransport

variable [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

theorem hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (2 * g.ricciNormSq cov hcov t x +
        RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)) t := by
  let cov₀ : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
    TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov₀ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov₀ t) 1 := by
    intro τ
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g τ
  let hLevi₀ : g.IsLeviCivita cov₀ := by
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g
  have hIntrinsic : RicciFlow.IsIntrinsicRicciFlowOn
      (I := I) (M := M) g gdot s :=
    (RicciFlow.isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) g hcov gdot s hLevi).2 hflow
  have hcanonical :=
    hIntrinsic.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      ht (x := x) ricciVelocity hRicci
  have hscalarEq :
      (fun τ : ℝ => g.scalarCurvature cov hcov τ x) =
        (fun τ : ℝ => g.scalarCurvature cov₀ hcov₀ τ x) := by
    funext τ
    exact g.scalarCurvature_eq_of_isLeviCivita
      hcov hcov₀ hLevi hLevi₀ τ x
  have hnormEq :
      g.ricciNormSq cov₀ hcov₀ t x = g.ricciNormSq cov hcov t x := by
    exact g.ricciNormSq_eq_of_isLeviCivita
      hcov₀ hcov hLevi₀ hLevi t x
  rw [hscalarEq]
  rw [← hnormEq]
  exact hcanonical

theorem hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} (x : M) (u v : TM x)
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.ricciCurvature cov hcov τ x u v)
      (ricciVelocity x u v) t := by
  let cov₀ : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) :=
    TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov₀ : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov₀ t) 1 := by
    intro τ
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g τ
  let hLevi₀ : g.IsLeviCivita cov₀ := by
    exact TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g
  have hricciEq :
      (fun τ : ℝ => g.ricciCurvature cov hcov τ x u v) =
        (fun τ : ℝ => RicciFlow.intrinsicRicciTensor
          (I := I) (M := M) g τ x u v) := by
    funext τ
    have hchosen := g.ricciCurvature_eq_of_isLeviCivita
      hcov hcov₀ hLevi hLevi₀ τ x u v
    simpa [RicciFlow.intrinsicRicciTensor, RicciFlow.ricciTensor,
      cov₀, hcov₀] using hchosen
  rw [hricciEq]
  exact hRicci x u v

/-! The support speed can therefore be obtained from a single intrinsic
Ricci-tensor derivative.  This theorem is intentionally stated in terms of
the already-proved support-speed calculation, so the logarithmic chain rule
and the Rayleigh support evolution remain in one audited location. -/

theorem hasDerivAt_hamiltonIveySupportedDefect_time_of_intrinsicRicciTimeDerivative
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
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t₀) :
    HasDerivAt
      (fun τ => g.hamiltonIveySupportedDefect
        cov hcov hLevi hdim K t₀ x₀ (τ, x₀))
      ((2 * g.ricciNormSq cov hcov t₀ x₀ +
          RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
            (ricciVelocity x₀)) /
          (-g.curvatureNu cov hcov hLevi hdim t₀ x₀) +
        (g.scalarCurvature cov hcov t₀ x₀ -
            g.curvatureNu cov hcov hLevi hdim t₀ x₀) /
          (g.curvatureNu cov hcov hLevi hdim t₀ x₀) ^ 2 *
          ((2 * g.ricciNormSq cov hcov t₀ x₀ +
              RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
                (ricciVelocity x₀)) -
            2 * (ricciVelocity x₀
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)) -
            (g.curvatureLambda cov hcov hLevi hdim t₀ x₀ +
              g.curvatureMu cov hcov hLevi hdim t₀ x₀) ^ 2) -
        K / (1 + K * t₀)) t₀ := by
  let v : TM x₀ := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t₀ x₀ x₀
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t₀ x₀ +
      RicciFlow.metricTraceAt (I := I) (M := M) g t₀ x₀
        (ricciVelocity x₀)
  let contactRicciVelocity : ℝ := ricciVelocity x₀ v v
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht₀ (x := x₀) ricciVelocity hRicci
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi x₀ v v ricciVelocity hRicci
  have hs := g.hasDerivAt_hamiltonIveySupportedDefect_time_of_isRicciFlowOn
    cov hcov hLevi hdim gdot s hflow hK ht₀ ht₀_nonneg hnu
      scalarVelocity contactRicciVelocity hscalar hricci
  simpa [v, scalarVelocity, contactRicciVelocity] using hs

/-! The contact certificate can now expose one intrinsic Ricci derivative
instead of unrelated scalar and coordinate Ricci speeds.  The remaining
spatial support and PDE clauses are retained verbatim, since those are the
separate curvature-evolution obligations rather than time-variation data. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_support_certificate
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
      ∃ ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ,
        RicciFlow.HasIntrinsicRicciTimeDerivativeAt
          (I := I) (M := M) g ricciVelocity t ∧
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
          ricciVelocity) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_ricciFlow_support_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hscalar hcont
  intro t x ht hdefect
  obtain ⟨ricciVelocity, hRicci, hupper, hneg, hscalarSupport,
    hnear, hdiff, hpde⟩ := hcontact ht hdefect
  let v : TM x := g.curvatureNuContactVectorField
    cov hcov hLevi hdim t x x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x (ricciVelocity x)
  let contactRicciVelocity : ℝ := ricciVelocity x v v
  have hscalarTime :=
    g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x) ricciVelocity hRicci
  have hricciTime :=
    g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi x v v ricciVelocity hRicci
  refine ⟨scalarVelocity, contactRicciVelocity, hscalarTime, hricciTime,
    hupper, hneg, hscalarSupport, hnear, hdiff, ?_⟩
  simpa [hamiltonIveyIntrinsicSupportSpeed, scalarVelocity,
    contactRicciVelocity, v] using hpde

end IntrinsicTransport

end CovariantDerivative.TimeDependentRiemannianMetric
