import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyParabolic
import PoincareCurvature.Geometry.Manifold.RicciFlow.MetricInverseVariation
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ThreeDimensionalRicciNorm

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
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

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

/-- The genuine connection-Laplacian readout of the shifted curvature tensor
at a Hamilton--Ivey contact.  The local instances are part of this
definition, so a downstream contact certificate can refer to an ordinary
real-valued quantity without manufacturing a coordinate coefficient array. -/
def hamiltonIveyContactCurvatureLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
  exact connectionLaplacian (cov t₀)
    (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀) x₀
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)

@[simp] theorem hamiltonIveyContactCurvatureLaplacian_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t₀ x₀ =
      (letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
       letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
         ContinuousLinearMap.toNormedAddCommGroup
       letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
         ContinuousLinearMap.toNormedSpace
       letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
         ContinuousLinearMap.toNormedAddCommGroup
       letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
       connectionLaplacian (cov t₀)
         (g.curvatureNuShiftedContactTwoTensor cov hcov hLevi hdim t₀ x₀) x₀
         (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
         (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)) := by
  rfl

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

/-! The previous two transport lemmas combine with the metric variation to
give the time derivative of the actual lowered curvature operator.  This is
the tensorial quantity that enters the curvature evolution equation; no
coordinate matrix or symmetrized projection is used. -/

def curvatureOperatorTwoTensorVelocity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (t : ℝ) (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (y : M) (u v : TM y) : ℝ :=
  (2 * g.ricciNormSq cov hcov t y +
      RicciFlow.metricTraceAt (I := I) (M := M) g t y (ricciVelocity y)) *
      (g t).inner y u v -
    2 * g.scalarCurvature cov hcov t y *
      g.ricciCurvature cov hcov t y u v -
    2 * ricciVelocity y u v

theorem hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
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
    {t : ℝ} (ht : t ∈ s) (y : M) (u v : TM y)
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t) :
    HasDerivAt
      (fun τ => g.curvatureOperatorTwoTensor cov hcov τ y u v)
      (curvatureOperatorTwoTensorVelocity g cov hcov t ricciVelocity y u v) t := by
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := y) ricciVelocity hRicci
  have hmetric := hflow.2.1 ht y u v
  have hmetricEq := hflow.2.2 ht y u v
  change HasDerivAt (fun τ => (g τ).inner y u v) (gdot t y u v) t at hmetric
  rw [hmetricEq] at hmetric
  have hmetric' : HasDerivAt (fun τ => (g τ).inner y u v)
      (-2 * g.ricciCurvature cov hcov t y u v) t := by
    simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi y u v ricciVelocity hRicci
  have htotal := (hscalar.mul hmetric').sub (hricci.const_mul 2)
  change HasDerivAt
    (fun τ => g.scalarCurvature cov hcov τ y * (g τ).inner y u v -
      2 * g.ricciCurvature cov hcov τ y u v)
    _ t at htotal
  convert htotal using 1
  · rfl
  · simp [curvatureOperatorTwoTensorVelocity]
    ring

/-! The three-dimensional curvature reaction is recorded intrinsically as a
polynomial in the curvature endomorphism.  If `A` is that endomorphism and
`R` is scalar curvature, the algebraic part is

`Q(A) = 2 A^2 - R A + (lambda*mu + lambda*nu + mu*nu) I`.

The final term is the metric-variation contribution to a lowered curvature
component.  Thus this is an actual tensorial bilinear expression, rather
than an independently supplied scalar coefficient. -/

def curvatureOperatorReaction
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (u v : TM y) : ℝ :=
  let A := fun z : TM y =>
    g.curvatureEndomorphismApply cov hcov t y z
  let R := g.scalarCurvature cov hcov t y
  let e₂ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  (g t).inner y u
      ((2 : ℝ) • A (A v) - R • A v + e₂ • v) -
    2 * g.ricciCurvature cov hcov t y u (A v)

/-! The polynomial part of the curvature reaction is bundled as the actual
continuous endomorphism

`Q(A) = 2 A ∘ A - R A + (λ μ + λ ν + μ ν) Id`.

Keeping this object as a fibrewise linear map makes the tensorial reaction
available to downstream maximum-principle code without introducing a matrix
or a chosen eigenbasis. -/

def curvatureOperatorReactionEndomorphism
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) : TM y →L[ℝ] TM y := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let A : TM y →L[ℝ] TM y :=
    CovariantDerivative.ricciComplementEndomorphism (cov t) y
  let e₂ : ℝ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  exact (2 : ℝ) • (A.comp A) -
      g.scalarCurvature cov hcov t y • A +
      e₂ • ContinuousLinearMap.id ℝ (TM y)

@[simp] theorem curvatureOperatorReactionEndomorphism_apply
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (v : TM y) :
    curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v =
      (2 : ℝ) • g.curvatureEndomorphismApply cov hcov t y
          (g.curvatureEndomorphismApply cov hcov t y v) -
        g.scalarCurvature cov hcov t y •
          g.curvatureEndomorphismApply cov hcov t y v +
        (g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureMu cov hcov hLevi hdim t y +
          g.curvatureLambda cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y +
          g.curvatureMu cov hcov hLevi hdim t y *
            g.curvatureNu cov hcov hLevi hdim t y) • v := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  simp [curvatureOperatorReactionEndomorphism, curvatureEndomorphismApply]

theorem curvatureOperatorReaction_eq_inner_endomorphism_sub_ricci
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) (u v : TM y) :
    curvatureOperatorReaction g cov hcov hLevi hdim t y u v =
      (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) -
        2 * g.ricciCurvature cov hcov t y u
          (g.curvatureEndomorphismApply cov hcov t y v) := by
  simp [curvatureOperatorReaction, curvatureOperatorReactionEndomorphism,
    curvatureEndomorphismApply]

theorem curvatureOperatorReactionEndomorphism_isSymmetric
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (y : M) :
    ∀ u v : TM y,
      (g t).inner y
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y u) v =
        (g t).inner y u
          (curvatureOperatorReactionEndomorphism g cov hcov hLevi hdim t y v) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let A : TM y →L[ℝ] TM y :=
    CovariantDerivative.ricciComplementEndomorphism (cov t) y
  have hA : A.toLinearMap.IsSymmetric := by
    simpa [A] using
      (CovariantDerivative.ricciComplementEndomorphism_isSymmetric
        (cov t) (hLevi t).1 (hLevi t).2 y)
  have hAcomp : ∀ u v : TM y,
      Inner.inner ℝ ((A.comp A) u) v = Inner.inner ℝ u ((A.comp A) v) := by
    intro u v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact (hA (A u) v).trans (hA u (A v))
  have hAuv : ∀ u v : TM y,
      Inner.inner ℝ (A u) v = Inner.inner ℝ u (A v) := by
    intro u v
    exact hA u v
  let e₂ : ℝ :=
    g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureMu cov hcov hLevi hdim t y +
      g.curvatureLambda cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y +
      g.curvatureMu cov hcov hLevi hdim t y *
        g.curvatureNu cov hcov hLevi hdim t y
  intro u v
  change Inner.inner ℝ
      ((2 : ℝ) • (A.comp A) u -
        g.scalarCurvature cov hcov t y • A u + e₂ • u) v =
    Inner.inner ℝ u
      ((2 : ℝ) • (A.comp A) v -
        g.scalarCurvature cov hcov t y • A v + e₂ • v)
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hAcomp u v, hAuv u v]

theorem curvatureOperatorReaction_apply_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hA : g.curvatureEndomorphismApply cov hcov t x V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    rw [hV]
    exact g.curvatureEndomorphismApply_curvatureNuEigenvector
      cov hcov hLevi hdim t x
  have hA' : (CovariantDerivative.ricciComplementEndomorphism (cov t) x) V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    simpa [curvatureEndomorphismApply] using hA
  have hA_smul :
      g.curvatureEndomorphismApply cov hcov t x
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) =
        (g.curvatureNu cov hcov hLevi hdim t x) •
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) := by
    unfold curvatureEndomorphismApply
    rw [map_smul, hA']
  have hRic_smul :
      g.ricciCurvature cov hcov t x V
          ((g.curvatureNu cov hcov hLevi hdim t x) • V) =
        (g.curvatureNu cov hcov hLevi hdim t x) *
          g.ricciCurvature cov hcov t x V V := by
    change CovariantDerivative.ricciCurvature (cov := cov t) x V
        ((g.curvatureNu cov hcov hLevi hdim t x) • V) = _
    rw [map_smul]
    rfl
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hinner' : Inner.inner ℝ V V = 1 := by
    change (g t).inner x V V = 1
    exact hinner
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  change curvatureOperatorReaction g cov hcov hLevi hdim t x V V = _
  change _ = (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x V V
  simp only [curvatureOperatorReaction] at ⊢
  rw [hA, hA_smul]
  rw [hRic_smul]
  change Inner.inner ℝ V _ - _ = _
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
    hinner']
  rw [← hsum]
  ring_nf

/-! The reaction at the least curvature direction is the product of the two
spectral gaps.  The Ricci contraction used here is recovered from the
eigenvector equation for the genuine Ricci-complement endomorphism; it is not
an independently supplied coefficient identity. -/

theorem curvatureOperatorReaction_apply_contact_eq_gap_product
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      (g.curvatureLambda cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) *
        (g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hA : g.curvatureEndomorphismApply cov hcov t x V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    rw [hV]
    exact g.curvatureEndomorphismApply_curvatureNuEigenvector
      cov hcov hLevi hdim t x
  have hA' : (CovariantDerivative.ricciComplementEndomorphism (cov t) x) V =
      (g.curvatureNu cov hcov hLevi hdim t x) • V := by
    simpa [curvatureEndomorphismApply] using hA
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hinner' : Inner.inner ℝ V V = 1 := by
    change (g t).inner x V V = 1
    exact hinner
  have hnorm : ‖V‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hinner'
  have hquad := CovariantDerivative.inner_ricciComplementEndomorphism
    (cov t) x V
  have hRic : 2 * g.ricciCurvature cov hcov t x V V =
      g.curvatureLambda cov hcov hLevi hdim t x +
        g.curvatureMu cov hcov hLevi hdim t x := by
    have hAinner := congrArg (fun z : TM x => Inner.inner ℝ z V) hA'
    have hAinner' :
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
          g.curvatureNu cov hcov hLevi hdim t x := by
      calc
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
            Inner.inner ℝ
              ((g.curvatureNu cov hcov hLevi hdim t x) • V) V := hAinner
        _ = g.curvatureNu cov hcov hLevi hdim t x * ‖V‖ ^ 2 := by
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        _ = g.curvatureNu cov hcov hLevi hdim t x := by rw [hnorm, mul_one]
    have hquad' :
        Inner.inner ℝ
            (CovariantDerivative.ricciComplementEndomorphism (cov t) x V) V =
          g.scalarCurvature cov hcov t x -
            2 * g.ricciCurvature cov hcov t x V V := by
      simpa [CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature,
        CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature,
        curvatureEndomorphismApply, hnorm] using hquad
    have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
      cov hcov hLevi hdim t x
    rw [hAinner'] at hquad'
    rw [← hsum] at hquad'
    linarith
  have hreaction :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using g.curvatureOperatorReaction_apply_contact
      cov hcov hLevi hdim t x
  change curvatureOperatorReaction g cov hcov hLevi hdim t x V V = _
  rw [hreaction]
  calc
    (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x *
            (2 * g.ricciCurvature cov hcov t x V V) := by ring
    _ = (g.curvatureLambda cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) *
        (g.curvatureMu cov hcov hLevi hdim t x -
          g.curvatureNu cov hcov hLevi hdim t x) := by
      rw [hRic]
      ring

theorem curvatureOperatorReaction_apply_contact_nonneg
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    0 ≤ curvatureOperatorReaction g cov hcov hLevi hdim t x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  rw [curvatureOperatorReaction_apply_contact_eq_gap_product
    g cov hcov hLevi hdim t x]
  have hMuNu := g.curvatureMu_ge_nu cov hcov hLevi hdim t x
  have hLambdaMu := g.curvatureLambda_ge_mu cov hcov hLevi hdim t x
  have hLambdaNu : g.curvatureNu cov hcov hLevi hdim t x ≤
      g.curvatureLambda cov hcov hLevi hdim t x := le_trans hMuNu hLambdaMu
  exact mul_nonneg (sub_nonneg.mpr hLambdaNu) (sub_nonneg.mpr hMuNu)

/-! In dimension three the Ricci norm in the intrinsic metric-variation
formula is exactly Hamilton--Ivey's scalar curvature reaction polynomial.
This is an algebraic identity for the genuine raised Ricci endomorphism, not
an assumption about a coordinate coefficient presentation. -/

theorem two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    2 * g.ricciNormSq cov hcov t x =
      HamiltonIveyReaction.scalarReaction
        (g.curvatureLambda cov hcov hLevi hdim t x)
        (g.curvatureMu cov hcov hLevi hdim t x)
        (g.curvatureNu cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have h := CovariantDerivative.two_mul_ricciNormSq_eq_threeDimensionalCurvatureReaction
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)
  dsimp [HamiltonIveyReaction.scalarReaction]
  convert h using 1
  · rfl
  · simp [CovariantDerivative.TimeDependentRiemannianMetric.ricciNormSq,
      curvatureLambda, curvatureMu, curvatureNu, curvatureEigenvalues,
      CovariantDerivative.threeDimensionalCurvatureLambda,
      CovariantDerivative.threeDimensionalCurvatureMu,
      CovariantDerivative.threeDimensionalCurvatureNu]
    ring

/-! With the intrinsic metric-variation trace identified with the scalar
Laplacian, the scalar-curvature derivative has exactly the Hamilton--Ivey
reaction form.  The trace equality is kept as an explicit hypothesis until
the full contracted-Bianchi/curvature-evolution bridge is proved. -/

theorem hasDerivAt_scalarCurvature_eq_hamiltonIveyReaction_add_laplacian
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
    {t : ℝ} (ht : t ∈ s) {x : M}
    (ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (htrace : RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (ricciVelocity x) =
      g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) :
    HasDerivAt
      (fun τ => g.scalarCurvature cov hcov τ x)
      (HamiltonIveyReaction.scalarReaction
          (g.curvatureLambda cov hcov hLevi hdim t x)
          (g.curvatureMu cov hcov hLevi hdim t x)
          (g.curvatureNu cov hcov hLevi hdim t x) +
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) t := by
  have h := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x) ricciVelocity hRicci
  convert h using 1
  rw [two_mul_ricciNormSq_eq_hamiltonIveyScalarReaction
    g cov hcov hLevi hdim t x, htrace]

/-! If the actual lowered curvature component satisfies the reaction-form
evolution identity, uniqueness of derivatives identifies its velocity with
the contact reaction.  This is the reusable interface for the curvature
evolution theorem, while leaving that theorem itself as an explicit
geometric obligation. -/

theorem curvatureOperatorTwoTensorVelocity_eq_of_curvatureOperatorReactionEvolution
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
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hEvolution :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) t) :
    g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x -
        2 * g.curvatureNu cov hcov hLevi hdim t x *
          g.ricciCurvature cov hcov t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  have hoperator := g.hasDerivAt_curvatureOperatorTwoTensor_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht x V V ricciVelocity hRicci
  have hEvolution' :
      HasDerivAt (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x V V)
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x V V) t := by
    simpa [V] using hEvolution
  have hvel := hoperator.unique hEvolution'
  have hreaction := curvatureOperatorReaction_apply_contact g cov hcov hLevi hdim t x
  have hreactionV :
      curvatureOperatorReaction g cov hcov hLevi hdim t x V V =
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hreaction
  have hvel' :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    rw [hvel, hreactionV]
    ring
  simpa [V] using hvel'

/-! At a contact eigenvector, the genuine lowered-curvature velocity gives the
time derivative of the Rayleigh support after the quotient correction.  The
assumption below is the exact contact evaluation of the curvature evolution
identity; isolating it here records the remaining geometric bridge without
silently replacing it by a coordinate or symmetrized coefficient statement. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
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
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hcurv :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x) =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
              (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  let V : TM x := g.curvatureNuContactVectorField cov hcov hLevi hdim t x x
  let scalarVelocity : ℝ :=
    2 * g.ricciNormSq cov hcov t x +
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
        (ricciVelocity x)
  let contactRicciVelocity : ℝ := ricciVelocity x V V
  have hscalar := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi gdot s hflow ht (x := x) ricciVelocity hRicci
  have hricci := g.hasDerivAt_ricciCurvature_of_intrinsicRicciTimeDerivative
    cov hcov hLevi x V V ricciVelocity hRicci
  have hq := g.hasDerivAt_curvatureNuSpacetimeSupport_time_eigenvalue_form
    cov hcov hLevi hdim gdot s hflow ht x scalarVelocity contactRicciVelocity
    hscalar hricci
  have hRic := g.two_mul_ricci_curvatureNuEigenvector_eq_lambda_add_mu
    cov hcov hLevi hdim t x
  have hV : V = g.curvatureNuEigenvector cov hcov hLevi hdim t x := by
    simp [V, curvatureNuContactVectorField,
      firstOrderParallelSmoothExtend_apply_center]
  have hinner : (g t).inner x V V = 1 := by
    rw [hV]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t x
  have hsum := g.curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hcov hLevi hdim t x
  have hrel :
      scalarVelocity - 2 * contactRicciVelocity -
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2 =
        g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V +
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    have hRic' : 2 * g.ricciCurvature cov hcov t x V V =
        g.curvatureLambda cov hcov hLevi hdim t x +
          g.curvatureMu cov hcov hLevi hdim t x := by
      simpa [V, curvatureNuContactVectorField,
        firstOrderParallelSmoothExtend_apply_center] using hRic
    have hRminus :
        g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x =
          g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x := by
      linarith [hsum]
    have hprod :
        2 * (g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x) *
            g.ricciCurvature cov hcov t x V V =
          (g.curvatureLambda cov hcov hLevi hdim t x +
            g.curvatureMu cov hcov hLevi hdim t x) ^ 2 := by
      calc
        2 * (g.scalarCurvature cov hcov t x -
            g.curvatureNu cov hcov hLevi hdim t x) *
              g.ricciCurvature cov hcov t x V V =
            (g.scalarCurvature cov hcov t x -
              g.curvatureNu cov hcov hLevi hdim t x) *
              (2 * g.ricciCurvature cov hcov t x V V) := by ring
        _ = (g.curvatureLambda cov hcov hLevi hdim t x +
              g.curvatureMu cov hcov hLevi hdim t x) ^ 2 := by
          rw [hRic', hRminus]
          ring
    simp only [scalarVelocity, contactRicciVelocity,
      curvatureOperatorTwoTensorVelocity]
    rw [hinner]
    ring_nf
    linarith [hprod]
  have hcurvV :
      g.curvatureOperatorTwoTensorVelocity cov hcov t ricciVelocity x V V =
        g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
          g.curvatureLambda cov hcov hLevi hdim t x *
            g.curvatureMu cov hcov hLevi hdim t x -
          2 * g.curvatureNu cov hcov hLevi hdim t x *
            g.ricciCurvature cov hcov t x V V := by
    simpa [V] using hcurv
  apply hq.congr_deriv
  rw [hrel, hcurvV]
  ring

/-! The preceding contact-support derivative can now consume the reaction-form
curvature evolution directly.  The only input not proved in this file is the
actual time derivative of the curvature component; its right-hand side is
required to be the intrinsic connection Laplacian plus the displayed
curvature polynomial. -/

theorem hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorReactionEvolution
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
    (ricciVelocity : ∀ z : M, TM z →ₗ[ℝ] TM z →ₗ[ℝ] ℝ)
    (hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
      (I := I) (M := M) g ricciVelocity t)
    (hEvolution :
      HasDerivAt
        (fun τ => g.curvatureOperatorTwoTensor cov hcov τ x
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
          (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x))
        (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
          curvatureOperatorReaction g cov hcov hLevi hdim t x
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)
            (g.curvatureNuContactVectorField cov hcov hLevi hdim t x x)) t) :
    HasDerivAt
      (fun τ => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t x (τ, x))
      (g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        (g.curvatureNu cov hcov hLevi hdim t x) ^ 2 +
        g.curvatureLambda cov hcov hLevi hdim t x *
          g.curvatureMu cov hcov hLevi hdim t x) t := by
  have hcurv :=
    g.curvatureOperatorTwoTensorVelocity_eq_of_curvatureOperatorReactionEvolution
      cov hcov hLevi hdim gdot s hflow ht x ricciVelocity hRicci hEvolution
  exact g.hasDerivAt_curvatureNuSpacetimeSupport_time_of_curvatureOperatorEvolution
    cov hcov hLevi hdim gdot s hflow ht x ricciVelocity hRicci hcurv

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

/-! Finally, the scalar lower barrier can be fed from the same intrinsic
Ricci-time derivative.  The only additional geometric datum is the trace
identity `tr_g(Ric') = ΔR`; this is precisely the contracted-Bianchi/curvature
evolution bridge and is kept explicit rather than replaced by an arbitrary
scalar time derivative. -/

theorem scalarCurvature_hamiltonIvey_lowerBarrier_of_intrinsicRicciTimeDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 ≤ K)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      -3 * (K / (1 + K * t)) ≤ g.scalarCurvature cov hcov t x := by
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
  have hScalarTime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => g.scalarCurvature cov hcov s x)
        (g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x +
          2 * g.ricciNormSq cov hcov t x) t := by
    intro t ht x
    have h := g.hasDerivAt_scalarCurvature_of_intrinsicRicciTimeDerivative
      cov hcov hLevi gdot (Icc 0 T) hflow ht (x := x)
        (ricciVelocity t) (hRicci ht)
    have htr := htrace t ht x
    convert h using 1
    rw [htr]
    ring
  have hScalarStrong := g.scalarCurvature_lowerBarrier_of_evolution
    cov hcov hdim hK hScalarCont hScalarTime hScalarNear
      hScalarDifferential hScalarInitial
  intro t ht x
  have hden₁ : 0 < 1 + (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
  have hden₂ : 0 < 1 + 2 * (K : ℝ) * t := by
    nlinarith [mul_nonneg hK ht.1]
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

/-! A single capstone now combines the intrinsic scalar barrier, the
intrinsic contact derivative, and the support maximum principle. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_trace_certificate
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
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
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
  have hscalar := g.scalarCurvature_hamiltonIvey_lowerBarrier_of_intrinsicRicciTimeDerivative
    cov hcov hLevi hdim gdot hK.le hflow hnuLower hScalarCont hScalarNear
      hScalarDifferential ricciVelocity hRicci htrace
  exact g.hamiltonIveyPinching_of_intrinsicRicciFlow_support_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hscalar hcont hcontact

/-! The next interface exposes the spatial contact inequality through the
actual shifted curvature tensor.  In particular, the certificate no longer
contains a free scalar Laplacian equality: it stores the explicit regularity
data consumed by the proved quotient/connection-Laplacian bridge.  The only
remaining contact inequality is the curvature-evolution estimate itself. -/

/- The regularity structure is defined next to the bridge theorem in
HamiltonIveySupportLaplacian.lean, where its dependent bundle instances are
elaborated in the same context as the bridge. -/
theorem HamiltonIveySupportLaplacianCertificate.eq_connectionLaplacian
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K : ℝ) (t₀ : ℝ) (x₀ : M)
    (c : HamiltonIveySupportLaplacianCertificate
      g cov hcov hLevi hdim t₀ x₀) :
    g.scalarLaplacian cov
        (fun _ y => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, y)) t₀ x₀ =
      g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t₀ x₀ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (TM x →L[ℝ] ℝ) := fun _ =>
    ContinuousLinearMap.toNormedSpace
  letI : ∀ x : M, NormedAddCommGroup (T₂ x) := fun _ =>
    ContinuousLinearMap.toNormedAddCommGroup
  letI : ∀ x : M, NormedSpace ℝ (T₂ x) := fun _ => inferInstance
  simpa [hamiltonIveyContactCurvatureLaplacian] using
    g.scalarLaplacian_curvatureNuSpacetimeSupport_eq_connectionLaplacian
      cov hcov hLevi hdim t₀ x₀ c.U c.hU c.hx₀ c.hden c.hq c.hd c.ha
      c.hDq c.hDd c.hDa c.hh c.hV c.hfirst c.hdf c.hsecondV

structure HamiltonIveyCurvatureContactCertificate
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (K t : ℝ) (x : M) where
  ricciVelocity : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ
  hRicci : RicciFlow.HasIntrinsicRicciTimeDerivativeAt
    (I := I) (M := M) g ricciVelocity t
  hupper : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hneg : ∀ᶠ p in 𝓝 (t, x),
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p < 0
  hscalarSupport : ∀ᶠ p in 𝓝 (t, x),
    0 < g.scalarCurvature cov hcov p.1 p.2 -
      g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t x p
  hnear : ∀ᶠ y in 𝓝 x,
    MDiffAt
      (fun z : M =>
        g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y
  hdiff : MDiffAt
    (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
      (CovariantDerivative.scalarDifferential (I := I)
        (fun z : M =>
          g.hamiltonIveySupportedDefect cov hcov hLevi hdim K t x (t, z)) y)) x
  hSupport : HamiltonIveySupportLaplacianCertificate
    g cov hcov hLevi hdim t x
  /-- The curvature-evolution contact estimate, expressed through the
  genuine connection Laplacian of the shifted curvature tensor. -/
  hCurvatureEvolution :
    g.hamiltonIveyContactCurvatureLaplacian cov hcov hLevi hdim t x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
        ricciVelocity
  /-- The scalar supported-defect inequality consumed by the maximum
  principle.  Its derivation from `hCurvatureEvolution` is the remaining
  chain-rule/evolution bridge, so it is recorded explicitly rather than
  silently identifying two different Laplacians. -/
  hEvolution :
    g.scalarLaplacian cov
        (fun _ y => g.hamiltonIveySupportedDefect
          cov hcov hLevi hdim K t x (t, y)) t x +
        g.hamiltonIveyReactionTerm cov hcov hLevi hdim K t x ≤
      g.hamiltonIveyIntrinsicSupportSpeed cov hcov hLevi hdim K t x
        ricciVelocity

/-! The structured certificate is directly consumable by the capstone above.
This is the exact reduction from the geometric connection-Laplacian contact
inequality to the scalar supported-defect inequality required by the compact
maximum principle. -/

theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_curvature_contact_certificate
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
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hScalarNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in 𝓝 x, MDiffAt (g.scalarCurvature cov hcov t) y)
    (hScalarDifferential : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential
            (I := I) (g.scalarCurvature cov hcov t) y)) x)
    (ricciVelocity : ∀ t : ℝ, ∀ x : M,
      TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hRicci : ∀ {t : ℝ}, t ∈ Icc 0 T →
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I) (M := M) g (ricciVelocity t) t)
    (htrace : ∀ t ∈ Icc 0 T, ∀ x : M,
      RicciFlow.metricTraceAt (I := I) (M := M) g t x
          (ricciVelocity t x) =
        g.scalarLaplacian cov (g.scalarCurvature cov hcov) t x)
    (hcont : ContinuousOn
      (fun p : ℝ × M =>
        g.hamiltonIveyDefect cov hcov hLevi hdim K p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveyCurvatureContactCertificate
        g cov hcov hLevi hdim K t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply g.hamiltonIveyPinching_of_intrinsicRicciFlow_and_trace_certificate
    cov hcov hLevi hdim gdot hK hT hflow hnuNeg hnuLower hScalarCont
    hScalarNear hScalarDifferential ricciVelocity hRicci htrace hcont
  intro t x ht hdefect
  let c := hcontact ht hdefect
  refine ⟨c.ricciVelocity, c.hRicci, c.hupper, c.hneg, c.hscalarSupport,
    c.hnear, c.hdiff, ?_⟩
  exact c.hEvolution

end IntrinsicTransport

end CovariantDerivative.TimeDependentRiemannianMetric
