module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODE
public import Mathlib.Analysis.Calculus.Deriv.Prod

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Time-derivative adapters for `C^3` gauge-pulled metrics

This thin module records reusable scalar forms of the static, non-identity
gauge-pullback time-derivative calculation.  The dynamic case still requires the
full chain-rule identity for a time-dependent diffeomorphism family.
-/

@[expose] public noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Model-space scalar chain rule for a time-dependent bilinear form evaluated on
two time-dependent vector paths.  This is the finite-dimensional algebraic core
of the dynamic gauge-pullback derivative calculation. -/
theorem hasDerivAt_bilinearForm_apply_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {B : ℝ → V →L[ℝ] W →L[ℝ] ℝ} {B' : V →L[ℝ] W →L[ℝ] ℝ}
    {u : ℝ → V} {u' : V} {v : ℝ → W} {v' : W} {t : ℝ}
    (hB : HasDerivAt B B' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun τ : ℝ => B τ (u τ) (v τ))
      (B' (u t) (v t) + B t u' (v t) + B t (u t) v') t := by
  have hfirst : HasDerivAt (fun τ : ℝ => B τ (u τ)) (B' (u t) + B t u') t :=
    hB.clm_apply hu
  have hsecond : HasDerivAt (fun τ : ℝ => (B τ (u τ)) (v τ))
      ((B' (u t) + B t u') (v t) + (B t (u t)) v') t :=
    hfirst.clm_apply hv
  simpa [ContinuousLinearMap.add_apply, add_assoc] using hsecond

/-- Model-space chain rule for a bilinear-form field depending on time and a
moving base point.  This isolates the `B`-component derivative in the coordinate
model of a dynamic gauge-pulled metric. -/
theorem hasDerivAt_bilinearFormField_along_curve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Bfield : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ}
    {Bfield' : ℝ × V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ)}
    {y : ℝ → V} {y' : V} {t : ℝ}
    (hB : HasFDerivAt Bfield Bfield' (t, y t))
    (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ : ℝ => Bfield (τ, y τ)) (Bfield' (1, y')) t := by
  have hpair : HasDerivAt (fun τ : ℝ => (τ, y τ)) (1, y') t := by
    simpa using (hasDerivAt_id t).prodMk hy
  simpa [Function.comp_def] using
    (HasFDerivAt.comp_hasDerivAt (x := t) (l := Bfield) (l' := Bfield')
      (f := fun τ : ℝ => (τ, y τ)) hB hpair)

/-- Model-space chain rule for `B(t) (A(t) u) (A(t) v)`, the coordinate form of
a pulled-back metric component when `A(t)` is the tangent map of the gauge. -/
theorem hasDerivAt_bilinearForm_linear_apply_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {B' : V →L[ℝ] V →L[ℝ] ℝ}
    {A : ℝ → V →L[ℝ] V} {A' : V →L[ℝ] V} {t : ℝ}
    (hB : HasDerivAt B B' t) (hA : HasDerivAt A A' t) (u v : V) :
    HasDerivAt (fun τ : ℝ => B τ (A τ u) (A τ v))
      (B' (A t u) (A t v) + B t (A' u) (A t v) + B t (A t u) (A' v)) t := by
  have hu : HasDerivAt (fun τ : ℝ => A τ u) (A' u) t := by
    simpa using hA.clm_apply (hasDerivAt_const (x := t) (c := u))
  have hv : HasDerivAt (fun τ : ℝ => A τ v) (A' v) t := by
    simpa using hA.clm_apply (hasDerivAt_const (x := t) (c := v))
  exact hasDerivAt_bilinearForm_apply_apply hB hu hv

/-- Coordinate gauge-flow specialization of
`hasDerivAt_bilinearForm_linear_apply_apply`: if the tangent map `A(t)` has
time derivative `D ∘ A(t)`, then the two vector-slot derivative terms are the
expected covariant/Lie-derivative contributions. -/
theorem hasDerivAt_bilinearForm_linear_apply_apply_of_comp_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {B' : V →L[ℝ] V →L[ℝ] ℝ}
    {A : ℝ → V →L[ℝ] V} {D : V →L[ℝ] V} {t : ℝ}
    (hB : HasDerivAt B B' t) (hA : HasDerivAt A (D.comp (A t)) t) (u v : V) :
    HasDerivAt (fun τ : ℝ => B τ (A τ u) (A τ v))
      (B' (A t u) (A t v) +
        B t (D (A t u)) (A t v) +
        B t (A t u) (D (A t v))) t := by
  simpa [ContinuousLinearMap.comp_apply] using
    hasDerivAt_bilinearForm_linear_apply_apply (B := B) (B' := B') (A := A)
      (A' := D.comp (A t)) (t := t) hB hA u v

/-- Combined coordinate-model chain rule for a bilinear-form field along a
moving base point and a tangent-map operator satisfying the variational equation.

This is the model-space algebraic shape of the remaining dynamic
gauge-pullback calculation:
`Bfield(τ, y(τ)) (A(τ)u) (A(τ)v)`. -/
theorem hasDerivAt_bilinearFormField_linear_apply_apply_along_curve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Bfield : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ}
    {Bfield' : ℝ × V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ)}
    {y : ℝ → V} {y' : V}
    {A : ℝ → V →L[ℝ] V} {D : V →L[ℝ] V} {t : ℝ}
    (hB : HasFDerivAt Bfield Bfield' (t, y t))
    (hy : HasDerivAt y y' t)
    (hA : HasDerivAt A (D.comp (A t)) t) (u v : V) :
    HasDerivAt (fun τ : ℝ => Bfield (τ, y τ) (A τ u) (A τ v))
      (Bfield' (1, y') (A t u) (A t v) +
        Bfield (t, y t) (D (A t u)) (A t v) +
        Bfield (t, y t) (A t u) (D (A t v))) t := by
  exact hasDerivAt_bilinearForm_linear_apply_apply_of_comp_deriv
    (B := fun τ : ℝ => Bfield (τ, y τ))
    (B' := Bfield' (1, y')) (A := A) (D := D) (t := t)
    (hasDerivAt_bilinearFormField_along_curve (Bfield := Bfield)
      (Bfield' := Bfield') (y := y) (y' := y') (t := t) hB hy)
    hA u v

namespace ModelGaugeFlowODE

namespace VariationalLocalFlowSolution

/-- Exact scalar chain rule along a variational model flow.

This is the ODE-driven heart of the dynamic gauge-pullback calculation: the base
curve contributes `f(t, y(t))`, while the tangent map contributes
`Df(t, y(t)) ∘ A(t)` in both vector slots. -/
theorem hasDerivAt_bilinearFormField_tangent_apply_apply_of_mem_Ioo
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {x : V} (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {Bfield : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ}
    {Bfield' : ℝ × V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ)}
    (hB : HasFDerivAt Bfield Bfield' (t, α.flow (x, t))) (u v : V) :
    HasDerivAt
      (fun τ : ℝ ↦
        Bfield (τ, α.flow (x, τ))
          (α.tangent x τ u) (α.tangent x τ v))
      (Bfield' (1, f t (α.flow (x, t)))
          (α.tangent x t u) (α.tangent x t v) +
        Bfield (t, α.flow (x, t))
          ((Df t (α.flow (x, t))) (α.tangent x t u))
          (α.tangent x t v) +
        Bfield (t, α.flow (x, t))
          (α.tangent x t u)
          ((Df t (α.flow (x, t))) (α.tangent x t v))) t := by
  exact hasDerivAt_bilinearFormField_linear_apply_apply_along_curve
    (Bfield := Bfield) (Bfield' := Bfield')
    (y := fun τ : ℝ ↦ α.flow (x, τ))
    (y' := f t (α.flow (x, t)))
    (A := fun τ : ℝ ↦ α.tangent x τ)
    (D := Df t (α.flow (x, t))) (t := t)
    hB (α.flow_hasDerivAt_of_mem_Ioo hx ht)
    (α.tangent_hasDerivAt_of_mem_Ioo hx ht) u v

/-- Eventual-equality transfer form of
`hasDerivAt_bilinearFormField_tangent_apply_apply_of_mem_Ioo`. -/
theorem hasDerivAt_of_eventuallyEq_bilinearFormField_tangent_apply_apply_of_mem_Ioo
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r)
    {x : V} (hx : x ∈ closedBall x₀ r) {t : ℝ} (ht : t ∈ Ioo tmin tmax)
    {scalar : ℝ → ℝ}
    {Bfield : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ}
    {Bfield' : ℝ × V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ)}
    {u v : V}
    (heq : scalar =ᶠ[𝓝 t]
      fun τ : ℝ ↦
        Bfield (τ, α.flow (x, τ))
          (α.tangent x τ u) (α.tangent x τ v))
    (hB : HasFDerivAt Bfield Bfield' (t, α.flow (x, t)))
    {value : ℝ}
    (hvalue :
      Bfield' (1, f t (α.flow (x, t)))
          (α.tangent x t u) (α.tangent x t v) +
        Bfield (t, α.flow (x, t))
          ((Df t (α.flow (x, t))) (α.tangent x t u))
          (α.tangent x t v) +
        Bfield (t, α.flow (x, t))
          (α.tangent x t u)
          ((Df t (α.flow (x, t))) (α.tangent x t v)) =
        value) :
    HasDerivAt scalar value t := by
  have hderiv :=
    α.hasDerivAt_bilinearFormField_tangent_apply_apply_of_mem_Ioo hx ht hB u v
  simpa [hvalue] using hderiv.congr_of_eventuallyEq heq

end VariationalLocalFlowSolution

end ModelGaugeFlowODE

/-- Local-coordinate transfer form of
`hasDerivAt_bilinearForm_linear_apply_apply`: if a scalar function is eventually
equal near `t` to the chart expression `B(τ) (A(τ) u) (A(τ) v)`, then it has
the same derivative.  This is the adapter needed when the geometric pullback
scalar is identified with the model expression only after restricting to a
coordinate neighborhood. -/
theorem hasDerivAt_of_eventuallyEq_bilinearForm_linear_apply_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → ℝ}
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {B' : V →L[ℝ] V →L[ℝ] ℝ}
    {A : ℝ → V →L[ℝ] V} {A' : V →L[ℝ] V} {t : ℝ}
    (u v : V)
    (heq : f =ᶠ[𝓝 t] fun τ : ℝ => B τ (A τ u) (A τ v))
    (hB : HasDerivAt B B' t) (hA : HasDerivAt A A' t) :
    HasDerivAt f
      (B' (A t u) (A t v) + B t (A' u) (A t v) + B t (A t u) (A' v)) t :=
  (hasDerivAt_bilinearForm_linear_apply_apply
    (B := B) (B' := B') (A := A) (A' := A') (t := t) hB hA u v).congr_of_eventuallyEq
      heq

/-- Local-coordinate transfer form of the tangent-map-shaped derivative case
`A'(t) = D ∘ A(t)`. -/
theorem hasDerivAt_of_eventuallyEq_bilinearForm_linear_apply_apply_of_comp_deriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → ℝ}
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {B' : V →L[ℝ] V →L[ℝ] ℝ}
    {A : ℝ → V →L[ℝ] V} {D : V →L[ℝ] V} {t : ℝ}
    (u v : V)
    (heq : f =ᶠ[𝓝 t] fun τ : ℝ => B τ (A τ u) (A τ v))
    (hB : HasDerivAt B B' t) (hA : HasDerivAt A (D.comp (A t)) t) :
    HasDerivAt f
      (B' (A t u) (A t v) +
        B t (D (A t u)) (A t v) +
        B t (A t u) (D (A t v))) t :=
  (hasDerivAt_bilinearForm_linear_apply_apply_of_comp_deriv
    (B := B) (B' := B') (A := A) (D := D) (t := t) hB hA u v).congr_of_eventuallyEq
      heq

namespace SmoothSelfDiffeomorph3Family

/-- The scalar derivative obligation for a `C^3` time-dependent diffeomorphism
family pulling back a metric family.  This is the primitive chain-rule target
left by the non-identity dynamic gauge time-regularity problem. -/
def PullbackMetricInnerDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
    HasDerivAt
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v))
      (gdot t x u v) t

/-- Coordinate-level sufficient data for the dynamic gauge-pullback scalar
derivative.

For each scalar component of the pulled-back metric, this asks for a local
model-space representation `B(τ) (A(τ) uE) (A(τ) vE)`, derivative data for the
metric component `B` and tangent map `A`, and the equality between the resulting
model derivative and the proposed geometric tensor component `gdot`.
-/
def CoordinatePullbackMetricInnerDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
    ∃ (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
      (B' : E →L[ℝ] E →L[ℝ] ℝ)
      (A : ℝ → E →L[ℝ] E)
      (D : E →L[ℝ] E)
      (uE vE : E),
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ B τ (A τ uE) (A τ vE)) ∧
      HasDerivAt B B' t ∧
      HasDerivAt A (D.comp (A t)) t ∧
      B' (A t uE) (A t vE) +
          B t (D (A t uE)) (A t vE) +
          B t (A t uE) (D (A t vE)) =
        gdot t x u v

/-- Preferred model-coordinate scalar expression for the component of a
gauge-pulled metric at a fixed base point and tangent-vector pair. -/
noncomputable def pullbackMetricInnerCoordinateModel
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TangentSpace I x) : ℝ → ℝ := fun τ =>
  let TM := (TangentSpace I : M → Type _)
  let TStar := fun y : M => TM y →L[ℝ] ℝ
  let OneF := E →L[ℝ] ℝ
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  let uE : E := (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx u
  let vE : E := (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx v
  let A : E →L[ℝ] E :=
    ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
      ((Φ τ).pushforwardTangent x)
  let B : E →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.inCoordinates E TM OneF TStar
      ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x))
  B (A uE) (A vE)

/-- Source tangent vector written in the model coordinates of the tangent
trivialization centered at its base point. -/
noncomputable def sourceTangentCoordinate
    (x : M) (u : TangentSpace I x) : E :=
  let TM := (TangentSpace I : M → Type _)
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx u

/-- The tangent-map coordinate operator `A(τ)` in the preferred coordinate model
for a gauge-pulled metric component. -/
noncomputable def pullbackMetricTangentCoordinateMap
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (t τ : ℝ) (x : M) : E →L[ℝ] E :=
  let TM := (TangentSpace I : M → Type _)
  ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
    ((Φ τ).pushforwardTangent x)

/-- The moving bilinear-form coordinate `B(τ)` in the preferred coordinate model
for a gauge-pulled metric component. -/
noncomputable def pullbackMetricBilinearCoordinateMap
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t τ : ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let TM := (TangentSpace I : M → Type _)
  let TStar := fun y : M => TM y →L[ℝ] ℝ
  let OneF := E →L[ℝ] ℝ
  ContinuousLinearMap.inCoordinates E TM OneF TStar
    ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x))

/-- The preferred coordinate scalar model is exactly `B(τ) (A(τ)u) (A(τ)v)`
for the named moving bilinear-coordinate and tangent-coordinate maps. -/
theorem pullbackMetricInnerCoordinateModel_eq_components
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t τ : ℝ) (x : M) (u v : TangentSpace I x) :
    pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v τ =
      pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x
        (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x
          (sourceTangentCoordinate (I := I) x u))
        (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x
          (sourceTangentCoordinate (I := I) x v)) := by
  simp [pullbackMetricInnerCoordinateModel, pullbackMetricBilinearCoordinateMap,
    pullbackMetricTangentCoordinateMap, sourceTangentCoordinate]

/-- Concrete formula for the moving bilinear coordinate component `B(τ)`: it is
the metric at the moved point, with model vectors pulled back through the target
tangent trivialization. -/
theorem pullbackMetricBilinearCoordinateMap_apply_eq
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t τ : ℝ) (x : M)
    (hφx : (Φ τ) x ∈
      (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet)
    (uE vE : E) :
    pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x uE vE =
      (g τ).inner ((Φ τ) x)
        (((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ τ) x) hφx).symm uE)
        (((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ τ) x) hφx).symm vE) := by
  let TM := (TangentSpace I : M → Type _)
  change
    (ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x)))
        uE vE =
      (g τ).inner ((Φ τ) x)
        (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ τ) x) hφx).symm uE)
        (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ τ) x) hφx).symm vE)
  erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
    (F := E) (W := TM) (x0 := (Φ t) x) (x := (Φ τ) x)
    hφx ((g τ).inner ((Φ τ) x)) uE vE]

/-- At the base time, the moving bilinear coordinate component is just the metric
in the tangent trivialization centered at the same point. -/
theorem pullbackMetricBilinearCoordinateMap_self_apply_eq
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (uE vE : E) :
    pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x uE vE =
      (g t).inner ((Φ t) x)
        (((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ t) x) (FiberBundle.mem_baseSet_trivializationAt' ((Φ t) x))).symm uE)
        (((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
          ((Φ t) x) (FiberBundle.mem_baseSet_trivializationAt' ((Φ t) x))).symm vE) :=
  pullbackMetricBilinearCoordinateMap_apply_eq (I := I) (M := M) Φ g t t x
    (FiberBundle.mem_baseSet_trivializationAt' ((Φ t) x)) uE vE

/-- The two-variable metric-coordinate field underlying the moving bilinear
component `B(τ)`.  The second argument is a model coordinate in the chart
centered at `p`; it is converted back to a manifold point before reading the
metric in the tangent trivialization centered at `p`. -/
noncomputable def metricBilinearCoordinateField
    (g : MetricFamily (I := I) (M := M)) (p : M) :
    ℝ × E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun z ↦
    let TM := (TangentSpace I : M → Type _)
    let TStar := fun y : M => TM y →L[ℝ] ℝ
    let OneF := E →L[ℝ] ℝ
    let y : M := (extChartAt I p).symm z.2
    ContinuousLinearMap.inCoordinates E TM OneF TStar p y p y ((g z.1).inner y)

/-- Near a time where the gauge image remains in the preferred chart, the
concrete moving bilinear component is the two-variable metric-coordinate field
evaluated along the coordinate curve of the moved base point. -/
theorem pullbackMetricBilinearCoordinateMap_eventuallyEq_metricBilinearCoordinateField
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M)
    (hmem : ∀ᶠ τ in 𝓝 t,
      (Φ τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet) :
    (fun τ : ℝ ↦
      pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        metricBilinearCoordinateField (I := I) (M := M) g ((Φ t) x)
          (τ, (extChartAt I ((Φ t) x)) ((Φ τ) x))) := by
  filter_upwards [hmem] with τ hτ
  ext uE vE
  let TM := (TangentSpace I : M → Type _)
  have hsrc_ext : (Φ τ) x ∈ (extChartAt I ((Φ t) x)).source := by
    simpa [TM, extChartAt_source] using hτ
  have hy :
      (extChartAt I ((Φ t) x)).symm ((extChartAt I ((Φ t) x)) ((Φ τ) x)) =
        (Φ τ) x := by
    exact PartialEquiv.left_inv _ hsrc_ext
  change
    (ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x))
        uE) vE =
    (ContinuousLinearMap.inCoordinates E TM (E →L[ℝ] ℝ) (fun y : M => TM y →L[ℝ] ℝ)
      ((Φ t) x)
      ((extChartAt I ((Φ t) x)).symm ((extChartAt I ((Φ t) x)) ((Φ τ) x)))
      ((Φ t) x)
      ((extChartAt I ((Φ t) x)).symm ((extChartAt I ((Φ t) x)) ((Φ τ) x)))
      ((g τ).inner
        ((extChartAt I ((Φ t) x)).symm ((extChartAt I ((Φ t) x)) ((Φ τ) x))))
        uE) vE
  rw [hy]

/-- Concrete formula for the tangent-coordinate component `A(τ)`: it is the
pushforward tangent map read in the source and target tangent trivializations. -/
theorem pullbackMetricTangentCoordinateMap_apply_eq
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (t τ : ℝ) (x : M)
    (hφx : (Φ τ) x ∈
      (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet)
    (uE : E) :
    pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x uE =
      ((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
        ((Φ τ) x) hφx)
        ((Φ τ).pushforwardTangent x
          (((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearEquivAt ℝ x
            (FiberBundle.mem_baseSet_trivializationAt' x)).symm uE)) := by
  let TM := (TangentSpace I : M → Type _)
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  change
    ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
        ((Φ τ).pushforwardTangent x) uE =
      ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx)
        ((Φ τ).pushforwardTangent x
          (((trivializationAt E TM x).continuousLinearEquivAt ℝ x hx).symm uE))
  rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x) (x := x)
    (y₀ := (Φ t) x) (y := (Φ τ) x) (ϕ := (Φ τ).pushforwardTangent x) hx hφx]
  rw [show (Φ τ).pushforwardTangent x = mfderiv I I ((Φ τ) : M → M) x by
    simpa using (Φ τ).pushforwardTangent_eq_mfderiv x]
  simpa [TM]

/-- The tangent-coordinate component applied to a source tangent vector is the
pushforward tangent vector in target model coordinates. -/
theorem pullbackMetricTangentCoordinateMap_sourceTangentCoordinate_eq
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (t τ : ℝ) (x : M)
    (hφx : (Φ τ) x ∈
      (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet)
    (u : TangentSpace I x) :
    pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x
        (sourceTangentCoordinate (I := I) x u) =
      ((trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).continuousLinearEquivAt ℝ
        ((Φ τ) x) hφx)
        ((Φ τ).pushforwardTangent x u) := by
  have h :=
    pullbackMetricTangentCoordinateMap_apply_eq
      (I := I) (M := M) Φ t τ x hφx (sourceTangentCoordinate (I := I) x u)
  simpa [sourceTangentCoordinate] using h

/-- Once the gauge image lies in the target trivialization centered at the
time-`t` image, the named coordinate model is definitionally the geometric
pullback scalar.  This avoids expanding the full bundled pullback bilinear-form
coordinate theorem in later derivative proofs. -/
theorem pullbackMetricInnerCoordinateModel_eq
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t τ : ℝ) (x : M) (u v : TangentSpace I x)
    (hφx : (Φ τ) x ∈
      (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet) :
    pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v τ =
      (g τ).inner ((Φ τ) x)
        ((Φ τ).pushforwardTangent x u)
        ((Φ τ).pushforwardTangent x v) := by
  let TM := (TangentSpace I : M → Type _)
  let TStar := fun y : M => TM y →L[ℝ] ℝ
  let OneF := E →L[ℝ] ℝ
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  let uE : E := (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx u
  let vE : E := (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx v
  let A : E →L[ℝ] E :=
    ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
      ((Φ τ).pushforwardTangent x)
  let Bc : E →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.inCoordinates E TM OneF TStar
      ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x))
  have hsource_u :
      ((trivializationAt E TM x).continuousLinearEquivAt ℝ x hx).symm uE = u := by
    simp [uE]
  have hsource_v :
      ((trivializationAt E TM x).continuousLinearEquivAt ℝ x hx).symm vE = v := by
    simp [vE]
  have hA_u :
      A uE =
        ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx)
          ((Φ τ).pushforwardTangent x u) := by
    change ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
        ((Φ τ).pushforwardTangent x) uE =
      ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx)
        ((Φ τ).pushforwardTangent x u)
    rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x) (x := x)
      (y₀ := (Φ t) x) (y := (Φ τ) x) (ϕ := (Φ τ).pushforwardTangent x) hx hφx]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [show ((↑((Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt E (TangentSpace I : M → Type _) x) x hx).symm) :
        E →L[ℝ] TangentSpace I x) uE) = u by
      simpa [TM] using hsource_u]
    simpa [TM]
  have hA_v :
      A vE =
        ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx)
          ((Φ τ).pushforwardTangent x v) := by
    change ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
        ((Φ τ).pushforwardTangent x) vE =
      ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx)
        ((Φ τ).pushforwardTangent x v)
    rw [ContinuousLinearMap.inCoordinates_eq (x₀ := x) (x := x)
      (y₀ := (Φ t) x) (y := (Φ τ) x) (ϕ := (Φ τ).pushforwardTangent x) hx hφx]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [show ((↑((Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt E (TangentSpace I : M → Type _) x) x hx).symm) :
        E →L[ℝ] TangentSpace I x) vE) = v by
      simpa [TM] using hsource_v]
    simpa [TM]
  have hB_eval :
      Bc (A uE) (A vE) =
        (g τ).inner ((Φ τ) x)
          (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm (A uE))
          (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm (A vE)) := by
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := (Φ t) x) (x := (Φ τ) x) hφx ((g τ).inner ((Φ τ) x)) (A uE) (A vE)]
  have hAu_back :
      ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm (A uE) =
        (Φ τ).pushforwardTangent x u := by
    rw [hA_u]
    simpa using
      (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm_apply_apply
        ((Φ τ).pushforwardTangent x u))
  have hAv_back :
      ((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm (A vE) =
        (Φ τ).pushforwardTangent x v := by
    rw [hA_v]
    simpa using
      (((trivializationAt E TM ((Φ t) x)).continuousLinearEquivAt ℝ ((Φ τ) x) hφx).symm_apply_apply
        ((Φ τ).pushforwardTangent x v))
  calc
    pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v τ = Bc (A uE) (A vE) := by
      simp [pullbackMetricInnerCoordinateModel, TM, TStar, OneF, uE, vE, A, Bc]
    _ = (g τ).inner ((Φ τ) x)
        ((Φ τ).pushforwardTangent x u)
        ((Φ τ).pushforwardTangent x v) := by
      rw [hB_eval, hAu_back, hAv_back]

/-- Eventual chart membership upgrades the named coordinate model to the
geometric pullback scalar near the reference time. -/
theorem eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TangentSpace I x)
    (hmem : ∀ᶠ τ in 𝓝 t,
      (Φ τ) x ∈
        (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet) :
    (fun τ : ℝ ↦
      (g τ).inner ((Φ τ) x)
        ((Φ τ).pushforwardTangent x u)
        ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
      pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v := by
  filter_upwards [hmem] with τ hτ
  exact (pullbackMetricInnerCoordinateModel_eq
    (I := I) (M := M) Φ g t τ x u v hτ).symm

/-- The remaining coordinate-model derivative obligation after the geometric
scalar has been identified with `pullbackMetricInnerCoordinateModel`.

This is the next hard mathematical target for positive-dimensional dynamic
gauges: prove derivative data for the coordinate metric component `B(τ)` and
the tangent-map coordinate operator `A(τ)` in the named model expression. -/
def CoordinatePullbackMetricModelDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
    ∃ (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
      (B' : E →L[ℝ] E →L[ℝ] ℝ)
      (A : ℝ → E →L[ℝ] E)
      (D : E →L[ℝ] E)
      (uE vE : E),
      pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ B τ (A τ uE) (A τ vE)) ∧
      HasDerivAt B B' t ∧
      HasDerivAt A (D.comp (A t)) t ∧
      B' (A t uE) (A t vE) +
          B t (D (A t uE)) (A t vE) +
          B t (A t uE) (D (A t vE)) =
        gdot t x u v

/-- Field-level sufficient data for the named coordinate-model derivative.

This splits the remaining model derivative into a moving bilinear-form field
`Bfield(τ, y(τ))` and the tangent-map coordinate operator `A(τ)`. -/
def CoordinatePullbackMetricFieldDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
    ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
      (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
      (y : ℝ → E)
      (y' : E)
      (A : ℝ → E →L[ℝ] E)
      (D : E →L[ℝ] E)
      (uE vE : E),
      pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v =ᶠ[𝓝 t]
          (fun τ : ℝ ↦ Bfield (τ, y τ) (A τ uE) (A τ vE)) ∧
      HasFDerivAt Bfield Bfield' (t, y t) ∧
      HasDerivAt y y' t ∧
      HasDerivAt A (D.comp (A t)) t ∧
      Bfield' (1, y') (A t uE) (A t vE) +
          Bfield (t, y t) (D (A t uE)) (A t vE) +
          Bfield (t, y t) (A t uE) (D (A t vE)) =
        gdot t x u v

/-- Concrete component-derivative data for the preferred coordinate pullback
model. This names the final positive-dimensional moving-coordinate obligations:
differentiate the concrete `B(τ)` and `A(τ)` components and identify their
scalar chain-rule value with the proposed geometric velocity. -/
def CoordinatePullbackMetricComponentDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
    ∃ (B' : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E),
      HasDerivAt
        (fun τ : ℝ ↦
          pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x)
        B' t ∧
      HasDerivAt
        (fun τ : ℝ ↦
          pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x)
        (D.comp (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x)) t ∧
      B'
          (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
            (sourceTangentCoordinate (I := I) x u))
          (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
            (sourceTangentCoordinate (I := I) x v)) +
          pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
            (D (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
              (sourceTangentCoordinate (I := I) x u)))
            (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
              (sourceTangentCoordinate (I := I) x v)) +
          pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
            (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
              (sourceTangentCoordinate (I := I) x u))
            (D (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
              (sourceTangentCoordinate (I := I) x v))) =
        gdot t x u v

/-- Concrete component-derivative form of
`CoordinatePullbackMetricModelDerivativeOn`.

This is the main remaining moving-coordinate calculation in local coordinates:
differentiate the named moving bilinear coordinate `B(τ)` and the named
tangent-coordinate map `A(τ)`, then check that the resulting scalar is the
geometric velocity component. -/
theorem coordinatePullbackMetricModelDerivativeOn_of_components
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hdata : CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) Φ g gdot s) :
    CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro t ht x u v
  obtain ⟨B', D, hB, hA, hvalue⟩ := hdata ht x u v
  refine ⟨(fun τ : ℝ ↦ pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x),
    B', (fun τ : ℝ ↦ pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x), D,
    sourceTangentCoordinate (I := I) x u, sourceTangentCoordinate (I := I) x v,
    ?_, hB, hA, hvalue⟩
  filter_upwards with τ
  exact pullbackMetricInnerCoordinateModel_eq_components
    (I := I) (M := M) Φ g t τ x u v

/-- Restrict field-level coordinate-model derivative data to a smaller time set. -/
theorem CoordinatePullbackMetricFieldDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hfield : CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot t)
    (hst : s ⊆ t) :
    CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro τ hτ x u v
  exact hfield (hst hτ) x u v

/-- A variational model flow supplies the moving-base and tangent-map derivative
clauses in the field-level coordinate pullback calculation.

The remaining hypotheses are exactly the chart-identification and metric-field
component derivative/evaluation facts.  Thus the ODE part of the dynamic
gauge-pullback chain rule is discharged by `VariationalLocalFlowSolution` on
the interior Picard interval. -/
theorem coordinatePullbackMetricFieldDerivativeOn_of_variationalLocalFlow
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df t₀ x₀ r)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (uE vE : E),
          pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield (τ, α.flow (xE, τ))
                  (α.tangent xE τ uE) (α.tangent xE τ vE)) ∧
          HasFDerivAt Bfield Bfield' (t, α.flow (xE, t)) ∧
          Bfield' (1, f t (α.flow (xE, t)))
              (α.tangent xE t uE) (α.tangent xE t vE) +
              Bfield (t, α.flow (xE, t))
                ((Df t (α.flow (xE, t))) (α.tangent xE t uE))
                (α.tangent xE t vE) +
              Bfield (t, α.flow (xE, t))
                (α.tangent xE t uE)
                ((Df t (α.flow (xE, t))) (α.tangent xE t vE)) =
            gdot t x u v) :
    CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot (Ioo tmin tmax) := by
  intro t ht x u v
  obtain ⟨xE, hxE, Bfield, Bfield', uE, vE, hmodel_eq, hBfield, hvalue⟩ :=
    hdata ht x u v
  exact ⟨Bfield, Bfield', (fun τ : ℝ ↦ α.flow (xE, τ)), f t (α.flow (xE, t)),
    (fun τ : ℝ ↦ α.tangent xE τ), Df t (α.flow (xE, t)), uE, vE,
    hmodel_eq, hBfield, α.flow_hasDerivAt_of_mem_Ioo hxE ht,
    α.tangent_hasDerivAt_of_mem_Ioo hxE ht, hvalue⟩

/-- A variational model flow supplies the tangent-map derivative clause in the
coordinate-model pullback calculation when the moving bilinear-form component
has already been differentiated directly in time.

This version is useful when the metric-component derivative is obtained from an
already-composed readout, rather than from a full Fréchet derivative of a
two-variable field `Bfield(t, y)`. -/
theorem coordinatePullbackMetricModelDerivativeOn_of_variationalLocalFlow
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df t₀ x₀ r)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
          (B' : E →L[ℝ] E →L[ℝ] ℝ)
          (uE vE : E),
          pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ B τ (α.tangent xE τ uE) (α.tangent xE τ vE)) ∧
          HasDerivAt B B' t ∧
          B' (α.tangent xE t uE) (α.tangent xE t vE) +
              B t ((Df t (α.flow (xE, t))) (α.tangent xE t uE))
                (α.tangent xE t vE) +
              B t (α.tangent xE t uE)
                ((Df t (α.flow (xE, t))) (α.tangent xE t vE)) =
            gdot t x u v) :
    CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot
      (Ioo tmin tmax) := by
  intro t ht x u v
  obtain ⟨xE, hxE, B, B', uE, vE, hmodel_eq, hB, hvalue⟩ := hdata ht x u v
  exact ⟨B, B', (fun τ : ℝ ↦ α.tangent xE τ),
    Df t (α.flow (xE, t)), uE, vE, hmodel_eq, hB,
    α.tangent_hasDerivAt_of_mem_Ioo hxE ht, hvalue⟩

/-- A variational model flow supplies the concrete tangent-coordinate derivative
for `A(τ)` and, together with a moving bilinear-form field derivative, supplies
the concrete `B(τ)` derivative.

This is the component-level version of the variational bridge: callers identify
the named concrete coordinate components
`pullbackMetricBilinearCoordinateMap` and `pullbackMetricTangentCoordinateMap`
with a local variational flow, and the theorem packages the resulting
`CoordinatePullbackMetricComponentDerivativeOn` data. -/
theorem coordinatePullbackMetricComponentDerivativeOn_of_variationalLocalFlow
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df t₀ x₀ r)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)),
          (fun τ : ℝ ↦
            pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ Bfield (τ, α.flow (xE, τ))) ∧
          (fun τ : ℝ ↦
            pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ α.tangent xE τ) ∧
          HasFDerivAt Bfield Bfield' (t, α.flow (xE, t)) ∧
          Bfield' (1, f t (α.flow (xE, t)))
              (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                (sourceTangentCoordinate (I := I) x u))
              (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                (sourceTangentCoordinate (I := I) x v)) +
              pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
                ((Df t (α.flow (xE, t)))
                  (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                    (sourceTangentCoordinate (I := I) x u)))
                (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                  (sourceTangentCoordinate (I := I) x v)) +
              pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
                (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                  (sourceTangentCoordinate (I := I) x u))
                ((Df t (α.flow (xE, t)))
                  (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                    (sourceTangentCoordinate (I := I) x v))) =
            gdot t x u v) :
    CoordinatePullbackMetricComponentDerivativeOn (I := I) (M := M) Φ g gdot
      (Ioo tmin tmax) := by
  intro t ht x u v
  obtain ⟨xE, hxE, Bfield, Bfield', hB_eq, hA_eq, hBfield, hvalue⟩ :=
    hdata ht x u v
  have hA_t :
      pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x =
        α.tangent xE t :=
    show t ∈ {τ : ℝ |
      pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x =
        α.tangent xE τ} from
      mem_of_mem_nhds hA_eq
  refine ⟨Bfield' (1, f t (α.flow (xE, t))), Df t (α.flow (xE, t)), ?_, ?_,
    hvalue⟩
  · have hBderiv :
        HasDerivAt (fun τ : ℝ ↦ Bfield (τ, α.flow (xE, τ)))
          (Bfield' (1, f t (α.flow (xE, t)))) t :=
      hasDerivAt_bilinearFormField_along_curve
        (Bfield := Bfield) (Bfield' := Bfield')
        (y := fun τ : ℝ ↦ α.flow (xE, τ))
        (y' := f t (α.flow (xE, t))) (t := t)
        hBfield (α.flow_hasDerivAt_of_mem_Ioo hxE ht)
    exact hBderiv.congr_of_eventuallyEq hB_eq
  · have hAderiv :
        HasDerivAt (fun τ : ℝ ↦ α.tangent xE τ)
          ((Df t (α.flow (xE, t))).comp (α.tangent xE t)) t :=
      α.tangent_hasDerivAt_of_mem_Ioo hxE ht
    have hAconcrete :
        HasDerivAt
          (fun τ : ℝ ↦
            pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x)
          ((Df t (α.flow (xE, t))).comp (α.tangent xE t)) t :=
      hAderiv.congr_of_eventuallyEq hA_eq
    simpa [hA_t] using hAconcrete

/-- Time-only metric-coordinate derivatives plus a variational tangent-map
identification supply the concrete component package.

This is the route aligned with finite-cover Banach readout theorems: the
bilinear coordinate component `B(τ)` has already been differentiated as a
time-only curve, while the variational model flow supplies the tangent-coordinate
operator derivative. -/
theorem coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df t₀ x₀ r)
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ B' : E →L[ℝ] E →L[ℝ] ℝ,
          HasDerivAt
            (fun τ : ℝ ↦
              pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t τ x)
            B' t ∧
          (fun τ : ℝ ↦
            pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ α.tangent xE τ) ∧
          B'
              (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                (sourceTangentCoordinate (I := I) x u))
              (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                (sourceTangentCoordinate (I := I) x v)) +
              pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
                ((Df t (α.flow (xE, t)))
                  (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                    (sourceTangentCoordinate (I := I) x u)))
                (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                  (sourceTangentCoordinate (I := I) x v)) +
              pullbackMetricBilinearCoordinateMap (I := I) (M := M) Φ g t t x
                (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                  (sourceTangentCoordinate (I := I) x u))
                ((Df t (α.flow (xE, t)))
                  (pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x
                    (sourceTangentCoordinate (I := I) x v))) =
            gdot t x u v) :
    CoordinatePullbackMetricComponentDerivativeOn (I := I) (M := M) Φ g gdot
      (Ioo tmin tmax) := by
  intro t ht x u v
  obtain ⟨xE, hxE, B', hB, hA_eq, hvalue⟩ := hdata ht x u v
  have hA_t :
      pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t t x =
        α.tangent xE t :=
    show t ∈ {τ : ℝ |
      pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x =
        α.tangent xE τ} from
      mem_of_mem_nhds hA_eq
  refine ⟨B', Df t (α.flow (xE, t)), hB, ?_, hvalue⟩
  have hAderiv :
      HasDerivAt (fun τ : ℝ ↦ α.tangent xE τ)
        ((Df t (α.flow (xE, t))).comp (α.tangent xE t)) t :=
    α.tangent_hasDerivAt_of_mem_Ioo hxE ht
  have hAconcrete :
      HasDerivAt
        (fun τ : ℝ ↦
          pullbackMetricTangentCoordinateMap (I := I) (M := M) Φ t τ x)
        ((Df t (α.flow (xE, t))).comp (α.tangent xE t)) t :=
    hAderiv.congr_of_eventuallyEq hA_eq
  simpa [hA_t] using hAconcrete

/-- Field-level moving-bilinear-form derivative data implies derivative data for
the named coordinate model. -/
theorem coordinatePullbackMetricModelDerivativeOn_of_field
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hfield : CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot s) :
    CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro t ht x u v
  obtain ⟨Bfield, Bfield', y, y', A, D, uE, vE, hmodel_eq,
    hBfield, hy, hA, hvalue⟩ := hfield ht x u v
  exact ⟨fun τ : ℝ ↦ Bfield (τ, y τ), Bfield' (1, y'), A, D, uE, vE,
    hmodel_eq,
    hasDerivAt_bilinearFormField_along_curve
      (Bfield := Bfield) (Bfield' := Bfield') (y := y) (y' := y') (t := t)
      hBfield hy,
    hA, hvalue⟩

/-- Restrict coordinate-model scalar pullback derivative data to a smaller time
set. -/
theorem CoordinatePullbackMetricModelDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hmodel : CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot t)
    (hst : s ⊆ t) :
    CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro τ hτ x u v
  exact hmodel (hst hτ) x u v

/-- Coordinate-model derivative data plus a chart-local equality between the
geometric scalar and the named coordinate model gives the original coordinate
derivative package. -/
theorem coordinatePullbackMetricInnerDerivativeOn_of_model
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hmodel : CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro t ht x u v
  obtain ⟨B, B', A, D, uE, vE, hmodel_eq, hB, hA, hvalue⟩ := hmodel ht x u v
  exact ⟨B, B', A, D, uE, vE, (hgeom ht x u v).trans hmodel_eq, hB, hA, hvalue⟩

/-- Once eventual chart equality is known, coordinate-model derivative data
implies the named geometric scalar derivative target. -/
theorem pullbackMetricInnerDerivativeOn_of_coordinateModel
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hmodel : CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s :=
by
  intro t ht x u v
  obtain ⟨B, B', A, D, uE, vE, hmodel_eq, hB, hA, hvalue⟩ := hmodel ht x u v
  have hderiv :
      HasDerivAt
        (fun τ : ℝ ↦
          (g τ).inner ((Φ τ) x)
            ((Φ τ).pushforwardTangent x u)
            ((Φ τ).pushforwardTangent x v))
        (B' (A t uE) (A t vE) +
          B t (D (A t uE)) (A t vE) +
          B t (A t uE) (D (A t vE))) t :=
    hasDerivAt_of_eventuallyEq_bilinearForm_linear_apply_apply_of_comp_deriv
      (B := B) (B' := B') (A := A) (D := D) (t := t) uE vE
      ((hgeom ht x u v).trans hmodel_eq) hB hA
  simpa [hvalue] using hderiv

/-- Field-level coordinate derivative data plus chart-local equality implies the
named geometric scalar derivative target. -/
theorem pullbackMetricInnerDerivativeOn_of_coordinateField
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hfield : CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s :=
  pullbackMetricInnerDerivativeOn_of_coordinateModel (I := I) (M := M)
    (coordinatePullbackMetricModelDerivativeOn_of_field (I := I) (M := M) hfield)
    hgeom

/-- Restrict named scalar pullback derivative data to a smaller time set. -/
theorem PullbackMetricInnerDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hinner : PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot t)
    (hst : s ⊆ t) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro τ hτ x u v
  exact hinner (hst hτ) x u v

/-- Restrict coordinate-level scalar pullback derivative data to a smaller time
set. -/
theorem CoordinatePullbackMetricInnerDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hcoord : CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot t)
    (hst : s ⊆ t) :
    CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro τ hτ x u v
  exact hcoord (hst hτ) x u v

/-- Coordinate-level scalar derivative data implies the actual geometric
pullback scalar derivative.  This is the bridge from chart calculations to the
named dynamic gauge time-regularity target. -/
theorem pullbackMetricInnerDerivativeOn_of_coordinate
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hcoord : CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro t ht x u v
  obtain ⟨B, B', A, D, uE, vE, heq, hB, hA, hvalue⟩ := hcoord ht x u v
  have hderiv :
      HasDerivAt
        (fun τ : ℝ ↦
          (g τ).inner ((Φ τ) x)
            ((Φ τ).pushforwardTangent x u)
            ((Φ τ).pushforwardTangent x v))
        (B' (A t uE) (A t vE) +
          B t (D (A t uE)) (A t vE) +
          B t (A t uE) (D (A t vE))) t :=
    hasDerivAt_of_eventuallyEq_bilinearForm_linear_apply_apply_of_comp_deriv
      (B := B) (B' := B') (A := A) (D := D) (t := t) uE vE heq hB hA
  simpa [hvalue] using hderiv

/-- Coordinate-level scalar derivative data packages directly as the tensor
time derivative of the gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hcoord : CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M) (Φ := Φ) (g := g) (gdot := gdot) (s := s)
    (pullbackMetricInnerDerivativeOn_of_coordinate (I := I) (M := M) hcoord)

/-- Coordinate-model scalar derivative data packages directly as the tensor
time derivative of the gauge-pulled metric family once chart-local equality with
the geometric scalar is known. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hmodel : CoordinatePullbackMetricModelDerivativeOn (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M) (Φ := Φ) (g := g) (gdot := gdot) (s := s)
    (pullbackMetricInnerDerivativeOn_of_coordinateModel
      (I := I) (M := M) hmodel hgeom)

/-- Field-level coordinate derivative data packages directly as tensor
time-regularity once chart-local equality with the geometric scalar is known. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hfield : CoordinatePullbackMetricFieldDerivativeOn (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s :=
  hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeOn (I := I) (M := M)
    (coordinatePullbackMetricModelDerivativeOn_of_field (I := I) (M := M) hfield)
    hgeom

/-- Concrete component derivatives plus chart-local equality imply the
coordinate-level scalar derivative package. -/
theorem coordinatePullbackMetricInnerDerivativeOn_of_components
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hdata : CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    CoordinatePullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s :=
  coordinatePullbackMetricInnerDerivativeOn_of_model (I := I) (M := M)
    (coordinatePullbackMetricModelDerivativeOn_of_components (I := I) (M := M) hdata)
    hgeom

/-- Concrete component derivatives plus chart-local equality imply tensor
time-regularity of the gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hdata : CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) Φ g gdot s)
    (hgeom : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      (fun τ : ℝ ↦
        (g τ).inner ((Φ τ) x)
          ((Φ τ).pushforwardTangent x u)
          ((Φ τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
        pullbackMetricInnerCoordinateModel (I := I) (M := M) Φ g t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s :=
  hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeOn (I := I) (M := M)
    (coordinatePullbackMetricModelDerivativeOn_of_components (I := I) (M := M) hdata)
    hgeom

/-- A named scalar inner-product derivative obligation packages as the tensor
time derivative of the gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hinner : PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M) (Φ := Φ) (g := g) (gdot := gdot) (s := s)
    hinner

/-- Tensor time-regularity of a gauge-pulled metric yields the named scalar
inner-product derivative obligation. -/
theorem pullbackMetricInnerDerivativeOn_of_hasTimeDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (Φ.pullbackMetricFamily g) gdot s) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s := by
  intro t ht x u v
  exact Φ.pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeOn
    (I := I) (M := M) hderiv ht x u v

/-- The scalar inner-product derivative obligation is equivalent to tensor
time-regularity of the `C^3` gauge-pulled metric family. -/
theorem pullbackMetricInnerDerivativeOn_iff_hasTimeDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ} :
    PullbackMetricInnerDerivativeOn (I := I) (M := M) Φ g gdot s ↔
      HasTimeDerivativeOn (I := I) (M := M) (Φ.pullbackMetricFamily g) gdot s := by
  constructor
  · exact hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeOn (I := I) (M := M)
  · exact pullbackMetricInnerDerivativeOn_of_hasTimeDerivativeOn (I := I) (M := M)

/-- Scalar form of the time derivative of a metric pulled back by a fixed
non-identity `C^3` diffeomorphism. -/
theorem const_pullbackMetricFamily_inner_hasDerivAt
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g gdot s)
    {t : ℝ} (ht : t ∈ s) (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ : ℝ ↦
        (g τ).inner ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ) x)
          (((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ).pushforwardTangent x u))
          (((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ).pushforwardTangent x v)))
      (gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) t := by
  simpa [SmoothSelfDiffeomorph3Family.const] using
    hderiv ht (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)

/-- Static scalar derivative hypotheses repackage to the tensor
time-derivative statement for a fixed `C^3` diffeomorphism pullback. -/
theorem const_pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hinner : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TangentSpace I x,
      HasDerivAt
        (fun τ : ℝ ↦
          (g τ).inner
            ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ) x)
            (((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ).pushforwardTangent x u))
            (((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ τ).pushforwardTangent x v)))
        (gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) t) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ).pullbackMetricFamily g)
      (fun t x u v ↦
        gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M)
    (Φ := SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ)
    (g := g)
    (gdot := fun t x u v ↦
      gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (s := s)
    hinner

/-- The existing tensor proof of the fixed non-identity pullback calculation also
supplies the named scalar derivative obligation. -/
theorem const_pullbackMetricInnerDerivativeOn
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g gdot s) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.const (I := I) (M := M) φ) g
      (fun t x u v ↦
        gdot t (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v)) s := by
  intro t ht x u v
  exact const_pullbackMetricFamily_inner_hasDerivAt
    (I := I) (M := M) φ hderiv ht x u v

/-- The identity `C^3` gauge turns ordinary metric time-regularity into the
named scalar derivative obligation. -/
theorem id_pullbackMetricInnerDerivativeOn
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g gdot s) :
    PullbackMetricInnerDerivativeOn (I := I) (M := M)
      (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) g gdot s := by
  refine pullbackMetricInnerDerivativeOn_of_hasTimeDerivativeOn (I := I) (M := M) ?_
  simpa [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily] using hderiv

end SmoothSelfDiffeomorph3Family

namespace Diffeomorph3GaugeFlowOn

/-- A raw gauge-flow witness supplies the chart-local equality between the
geometric pullback scalar and the preferred coordinate model at every time where
the raw flow equation holds on a neighborhood. -/
theorem eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : s ∈ 𝓝 t)
    (g : MetricFamily (I := I) (M := M))
    (x : M) (u v : TangentSpace I x) :
    (fun τ : ℝ ↦
      (g τ).inner ((G.maps3 τ) x)
        ((G.maps3 τ).pushforwardTangent x u)
        ((G.maps3 τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
      SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
        (I := I) (M := M) G.maps3 g t x u v :=
  SmoothSelfDiffeomorph3Family.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) G.maps3 g t x u v
    (G.eventually_mem_trivializationAt_eval hs x)

/-- Closed-Picard-interval specialization of
`eventuallyEq_geometric_pullbackMetricInnerCoordinateModel` at interior times. -/
theorem eventuallyEq_geometric_pullbackMetricInnerCoordinateModel_of_mem_Ioo
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ t : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    (ht : t ∈ Ioo tmin tmax)
    (g : MetricFamily (I := I) (M := M))
    (x : M) (u v : TangentSpace I x) :
    (fun τ : ℝ ↦
      (g τ).inner ((G.maps3 τ) x)
        ((G.maps3 τ).pushforwardTangent x u)
        ((G.maps3 τ).pushforwardTangent x v)) =ᶠ[𝓝 t]
      SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
        (I := I) (M := M) G.maps3 g t x u v := by
  exact SmoothSelfDiffeomorph3Family.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) G.maps3 g t x u v
    (G.eventually_mem_trivializationAt_eval_of_mem_Ioo ht x)

/-- For a raw gauge flow whose time set is a neighborhood of each of its times,
derivative data for the named coordinate model is enough to produce the
coordinate derivative package for the geometric pullback scalar. -/
theorem coordinatePullbackMetricInnerDerivativeOn_of_model
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hmodel : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricModelDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricInnerDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s :=
  SmoothSelfDiffeomorph3Family.coordinatePullbackMetricInnerDerivativeOn_of_model
    (I := I) (M := M) hmodel
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Raw gauge-flow version of the coordinate-model derivative bridge to the
named geometric scalar target. -/
theorem pullbackMetricInnerDerivativeOn_of_coordinateModel
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hmodel : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricModelDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricInnerDerivativeOn_of_coordinateModel
    (I := I) (M := M) hmodel
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Raw gauge-flow version of the coordinate-model derivative bridge directly
to tensor time-regularity. -/
theorem hasTimeDerivativeOn_of_coordinateModel
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hmodel : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricModelDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeOn
    (I := I) (M := M) hmodel
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Raw gauge-flow version of the field-level coordinate derivative bridge to
the named geometric scalar target. -/
theorem pullbackMetricInnerDerivativeOn_of_coordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hfield : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s :=
  SmoothSelfDiffeomorph3Family.pullbackMetricInnerDerivativeOn_of_coordinateField
    (I := I) (M := M) hfield
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Raw gauge-flow version of the field-level coordinate derivative bridge
directly to tensor time-regularity. -/
theorem hasTimeDerivativeOn_of_coordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hfield : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeOn
    (I := I) (M := M) hfield
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Raw gauge flows supply the moving-base coordinate derivative `y'(t)` in the
field-level coordinate package at times where the raw time set is a
neighborhood. -/
theorem coordinatePullbackMetricFieldDerivativeOn_of_baseCoordinate
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (A : ℝ → E →L[ℝ] E)
          (D : E →L[ℝ] E)
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield
                  (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
                  (A τ uE) (A τ vE)) ∧
          HasFDerivAt Bfield Bfield'
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
          HasDerivAt A (D.comp (A t)) t ∧
          Bfield'
              (1, tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x)
                ((G.maps3 t) x) (X t ((G.maps3 t) x)))
              (A t uE) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (D (A t uE)) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (A t uE) (D (A t vE)) =
            gdot t x u v) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s := by
  intro t ht x u v
  obtain ⟨Bfield, Bfield', A, D, uE, vE, hmodel_eq, hBfield, hA, hvalue⟩ :=
    hdata ht x u v
  exact ⟨Bfield, Bfield',
    (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)),
    tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
      (X t ((G.maps3 t) x)),
    A, D, uE, vE, hmodel_eq, hBfield,
    G.hasDerivAt_extChartAt_eval (hs (t := t) ht) x, hA, hvalue⟩

/-- Raw gauge flows plus derivative data for the named metric-coordinate field
and the concrete tangent-coordinate map produce the field-level coordinate
package.  The local scalar model equality is supplied automatically by the
concrete `B(τ)`/`A(τ)` formulas. -/
theorem coordinatePullbackMetricFieldDerivativeOn_of_metricCoordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (D : E →L[ℝ] E),
          HasFDerivAt
            (SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
              (I := I) (M := M) g ((G.maps3 t) x))
            Bfield' (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
          HasDerivAt
            (fun τ : ℝ ↦
              SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t τ x)
            (D.comp
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x)) t ∧
          Bfield'
              (1, tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x)
                ((G.maps3 t) x) (X t ((G.maps3 t) x)))
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) g ((G.maps3 t) x)
                (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u)))
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
                (I := I) (M := M) g ((G.maps3 t) x)
                (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
                (D (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) =
            gdot t x u v) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s := by
  refine G.coordinatePullbackMetricFieldDerivativeOn_of_baseCoordinate hs ?_
  intro t ht x u v
  obtain ⟨Bfield', D, hBfield, hA, hvalue⟩ := hdata ht x u v
  refine ⟨SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
      (I := I) (M := M) g ((G.maps3 t) x),
    Bfield',
    (fun τ : ℝ ↦ SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
      (I := I) (M := M) G.maps3 t τ x),
    D,
    SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u,
    SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v,
    ?_, hBfield, hA, hvalue⟩
  have hcomponents :
      SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
          (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
        (fun τ : ℝ ↦
          SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
              (I := I) (M := M) G.maps3 g t τ x
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
            (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x
              (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) := by
    filter_upwards with τ
    exact SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel_eq_components
      (I := I) (M := M) G.maps3 g t τ x u v
  have hB :
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
          (I := I) (M := M) G.maps3 g t τ x) =ᶠ[𝓝 t]
      (fun τ : ℝ ↦
        SmoothSelfDiffeomorph3Family.metricBilinearCoordinateField
          (I := I) (M := M) g ((G.maps3 t) x)
          (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))) :=
    SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap_eventuallyEq_metricBilinearCoordinateField
      (I := I) (M := M) G.maps3 g t x
      (G.eventually_mem_trivializationAt_eval (hs (t := t) ht) x)
  filter_upwards [hcomponents, hB] with τ hcomponentsτ hBτ
  rw [hcomponentsτ, hBτ]

/-- Raw gauge flow plus field-level data whose moving base point is the actual
gauge-flow coordinate curve gives tensor time-regularity at neighborhood-times. -/
theorem hasTimeDerivativeOn_of_baseCoordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ s →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (A : ℝ → E →L[ℝ] E)
          (D : E →L[ℝ] E)
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield
                  (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
                  (A τ uE) (A τ vE)) ∧
          HasFDerivAt Bfield Bfield'
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
          HasDerivAt A (D.comp (A t)) t ∧
          Bfield'
              (1, tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x)
                ((G.maps3 t) x) (X t ((G.maps3 t) x)))
              (A t uE) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (D (A t uE)) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (A t uE) (D (A t vE)) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot s :=
  G.hasTimeDerivativeOn_of_coordinateField hs
    (G.coordinatePullbackMetricFieldDerivativeOn_of_baseCoordinate hs hdata)

/-- Raw gauge-flow bridge from concrete coordinate-component derivatives directly
to tensor time-regularity. -/
theorem hasTimeDerivativeOn_of_coordinateComponents
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 g gdot s) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot s :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
    (I := I) (M := M) hdata
    (fun {t} ht x u v ↦ G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (t := t) (hs (t := t) ht) g x u v)

/-- Closed-Picard-interval raw gauge-flow version of the coordinate-model bridge
on the open interior interval. -/
theorem hasTimeDerivativeOn_Ioo_of_coordinateModel
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hmodel : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricModelDerivativeOn
      (I := I) (M := M) G.maps3 g gdot (Ioo tmin tmax)) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeOn
    (I := I) (M := M) hmodel
    (fun {t} ht x u v ↦
      G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel_of_mem_Ioo
        (t := t) ht g x u v)

/-- Closed-Picard raw gauge flow plus a variational model flow whose moving
bilinear-form component has been differentiated directly in time gives interior
time-regularity for the gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_Ioo_of_variationalLocalFlowModel
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {τ₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
          (B' : E →L[ℝ] E →L[ℝ] ℝ)
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ B τ (α.tangent xE τ uE) (α.tangent xE τ vE)) ∧
          HasDerivAt B B' t ∧
          B' (α.tangent xE t uE) (α.tangent xE t vE) +
              B t ((Df t (α.flow (xE, t))) (α.tangent xE t uE))
                (α.tangent xE t vE) +
              B t (α.tangent xE t uE)
                ((Df t (α.flow (xE, t))) (α.tangent xE t vE)) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  G.hasTimeDerivativeOn_Ioo_of_coordinateModel
    (SmoothSelfDiffeomorph3Family.coordinatePullbackMetricModelDerivativeOn_of_variationalLocalFlow
      (I := I) (M := M) (Φ := G.maps3) (g := g) (gdot := gdot) α hdata)

/-- Closed-Picard-interval raw gauge-flow version of the field-level coordinate
derivative bridge on the open interior interval. -/
theorem hasTimeDerivativeOn_Ioo_of_coordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hfield : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot (Ioo tmin tmax)) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeOn
    (I := I) (M := M) hfield
    (fun {t} ht x u v ↦
      G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel_of_mem_Ioo
        (t := t) ht g x u v)

/-- Closed-Picard raw gauge flows supply the moving-base coordinate derivative
`y'(t)` in the field-level coordinate package.

The remaining hypotheses are the metric-field Fréchet derivative, the
tangent-coordinate derivative, the local coordinate identification, and the
scalar velocity identity. -/
theorem coordinatePullbackMetricFieldDerivativeOn_Ioo_of_baseCoordinate
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (A : ℝ → E →L[ℝ] E)
          (D : E →L[ℝ] E)
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield
                  (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
                  (A τ uE) (A τ vE)) ∧
          HasFDerivAt Bfield Bfield'
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
          HasDerivAt A (D.comp (A t)) t ∧
          Bfield'
              (1, tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x)
                ((G.maps3 t) x) (X t ((G.maps3 t) x)))
              (A t uE) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (D (A t uE)) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (A t uE) (D (A t vE)) =
            gdot t x u v) :
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) G.maps3 g gdot (Ioo tmin tmax) := by
  intro t ht x u v
  obtain ⟨Bfield, Bfield', A, D, uE, vE, hmodel_eq, hBfield, hA, hvalue⟩ :=
    hdata ht x u v
  exact ⟨Bfield, Bfield',
    (fun τ : ℝ ↦ (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x)),
    tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x) ((G.maps3 t) x)
      (X t ((G.maps3 t) x)),
    A, D, uE, vE, hmodel_eq, hBfield,
    G.hasDerivAt_extChartAt_eval_of_mem_Ioo ht x, hA, hvalue⟩

/-- Closed-Picard raw gauge flow plus field-level data whose moving base point is
the actual gauge-flow coordinate curve gives interior time-regularity. -/
theorem hasTimeDerivativeOn_Ioo_of_baseCoordinateField
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (A : ℝ → E →L[ℝ] E)
          (D : E →L[ℝ] E)
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield
                  (τ, (extChartAt I ((G.maps3 t) x)) ((G.maps3 τ) x))
                  (A τ uE) (A τ vE)) ∧
          HasFDerivAt Bfield Bfield'
            (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x)) ∧
          HasDerivAt A (D.comp (A t)) t ∧
          Bfield'
              (1, tangentCoordChange I ((G.maps3 t) x) ((G.maps3 t) x)
                ((G.maps3 t) x) (X t ((G.maps3 t) x)))
              (A t uE) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (D (A t uE)) (A t vE) +
              Bfield (t, (extChartAt I ((G.maps3 t) x)) ((G.maps3 t) x))
                (A t uE) (D (A t vE)) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  G.hasTimeDerivativeOn_Ioo_of_coordinateField
    (G.coordinatePullbackMetricFieldDerivativeOn_Ioo_of_baseCoordinate hdata)

/-- Closed-Picard-interval raw gauge-flow bridge from concrete
coordinate-component derivatives directly to interior tensor time-regularity. -/
theorem hasTimeDerivativeOn_Ioo_of_coordinateComponents
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn
      (I := I) (M := M) G.maps3 g gdot (Ioo tmin tmax)) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricComponentDerivatives
    (I := I) (M := M) hdata
    (fun {t} ht x u v ↦
      G.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel_of_mem_Ioo
        (t := t) ht g x u v)

/-- Closed-Picard raw gauge flow plus a variational model flow whose concrete
moving-coordinate components are identified locally gives interior
time-regularity for the gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_Ioo_of_variationalLocalFlowComponents
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {τ₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)),
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
              (I := I) (M := M) G.maps3 g t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ Bfield (τ, α.flow (xE, τ))) ∧
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ α.tangent xE τ) ∧
          HasFDerivAt Bfield Bfield' (t, α.flow (xE, t)) ∧
          Bfield' (1, f t (α.flow (xE, t)))
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
                (I := I) (M := M) G.maps3 g t t x
                ((Df t (α.flow (xE, t)))
                  (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                    (I := I) (M := M) G.maps3 t t x
                    (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u)))
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
                (I := I) (M := M) G.maps3 g t t x
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
                ((Df t (α.flow (xE, t)))
                  (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                    (I := I) (M := M) G.maps3 t t x
                    (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  G.hasTimeDerivativeOn_Ioo_of_coordinateComponents
    (SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalLocalFlow
      (I := I) (M := M) (Φ := G.maps3) (g := g) (gdot := gdot) α hdata)

/-- Closed-Picard raw gauge flow plus time-only concrete `B(τ)` derivatives and
a variational tangent-map identification gives interior time-regularity for the
gauge-pulled metric family. -/
theorem hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {τ₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ B' : E →L[ℝ] E →L[ℝ] ℝ,
          HasDerivAt
            (fun τ : ℝ ↦
              SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
                (I := I) (M := M) G.maps3 g t τ x)
            B' t ∧
          (fun τ : ℝ ↦
            SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
              (I := I) (M := M) G.maps3 t τ x) =ᶠ[𝓝 t]
              (fun τ : ℝ ↦ α.tangent xE τ) ∧
          B'
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
              (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                (I := I) (M := M) G.maps3 t t x
                (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
                (I := I) (M := M) G.maps3 g t t x
                ((Df t (α.flow (xE, t)))
                  (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                    (I := I) (M := M) G.maps3 t t x
                    (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u)))
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v)) +
              SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap
                (I := I) (M := M) G.maps3 g t t x
                (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                  (I := I) (M := M) G.maps3 t t x
                  (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x u))
                ((Df t (α.flow (xE, t)))
                  (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
                    (I := I) (M := M) G.maps3 t t x
                    (SmoothSelfDiffeomorph3Family.sourceTangentCoordinate (I := I) x v))) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  G.hasTimeDerivativeOn_Ioo_of_coordinateComponents
    (SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap
      (I := I) (M := M) (Φ := G.maps3) (g := g) (gdot := gdot) α hdata)

/-- Closed-Picard raw gauge flow plus variational model-flow chart data gives
interior time-regularity for the gauge-pulled metric family in one step. -/
theorem hasTimeDerivativeOn_Ioo_of_variationalLocalFlow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {tmin tmax t₀ : ℝ}
    (G : Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Icc tmin tmax) t₀)
    {τ₀ : Icc tmin tmax}
    {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E}
    {x₀ : E} {r : ℝ≥0}
    (α : ModelGaugeFlowODE.VariationalLocalFlowSolution f Df τ₀ x₀ r)
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hdata : ∀ ⦃t : ℝ⦄, t ∈ Ioo tmin tmax →
      ∀ x : M, ∀ u v : TangentSpace I x,
        ∃ xE : E, xE ∈ closedBall x₀ r ∧
        ∃ (Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
          (Bfield' : ℝ × E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
          (uE vE : E),
          SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
              (I := I) (M := M) G.maps3 g t x u v =ᶠ[𝓝 t]
              (fun τ : ℝ ↦
                Bfield (τ, α.flow (xE, τ))
                  (α.tangent xE τ uE) (α.tangent xE τ vE)) ∧
          HasFDerivAt Bfield Bfield' (t, α.flow (xE, t)) ∧
          Bfield' (1, f t (α.flow (xE, t)))
              (α.tangent xE t uE) (α.tangent xE t vE) +
              Bfield (t, α.flow (xE, t))
                ((Df t (α.flow (xE, t))) (α.tangent xE t uE))
                (α.tangent xE t vE) +
              Bfield (t, α.flow (xE, t))
                (α.tangent xE t uE)
                ((Df t (α.flow (xE, t))) (α.tangent xE t vE)) =
            gdot t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) (G.maps3.pullbackMetricFamily g) gdot
      (Ioo tmin tmax) :=
  G.hasTimeDerivativeOn_Ioo_of_coordinateField
    (SmoothSelfDiffeomorph3Family.coordinatePullbackMetricFieldDerivativeOn_of_variationalLocalFlow
      (I := I) (M := M) (Φ := G.maps3) (g := g) (gdot := gdot) α hdata)

end Diffeomorph3GaugeFlowOn

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- Fixed-IVP named scalar derivative data for all gauge-pulled metrics in a
geometric `C^3` DeTurck gauge-flow bundle. -/
def PullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn
      (I := I) (M := M) (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP coordinate-level scalar derivative data for all gauge-pulled
metrics in a geometric `C^3` DeTurck gauge-flow bundle. -/
def CoordinatePullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricInnerDerivativeOn
      (I := I) (M := M) (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP coordinate-model derivative data for all gauge-pulled metrics in a
geometric `C^3` DeTurck gauge-flow bundle. -/
def CoordinatePullbackMetricModelDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricModelDerivativeOn
      (I := I) (M := M) (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP field-level derivative data for all gauge-pulled metrics in a
geometric `C^3` DeTurck gauge-flow bundle. -/
def CoordinatePullbackMetricFieldDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricFieldDerivativeOn
      (I := I) (M := M) (G.maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Coordinate-level fixed-IVP scalar data implies the named geometric scalar
derivative data used by the gauge-pulled metric routes. -/
theorem pullbackMetricInnerDerivativeData_of_coordinate
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    G.PullbackMetricInnerDerivativeData := by
  intro sol
  exact SmoothSelfDiffeomorph3Family.pullbackMetricInnerDerivativeOn_of_coordinate
    (I := I) (M := M) (hcoord sol)

/-- Coordinate-model fixed-IVP data implies coordinate-level scalar data once
the solution time set is a neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_model
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData := by
  intro sol
  refine SmoothSelfDiffeomorph3Family.coordinatePullbackMetricInnerDerivativeOn_of_model
    (I := I) (M := M) (hmodel sol) ?_
  intro t ht x u v
  let R : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    { maps3 := G.maps3 sol
      anchored := G.anchored sol
      satisfies := G.satisfies sol }
  exact R.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) (t := t) (htime sol ht)
    sol.1.toIntrinsicDeTurckSolution.metric x u v

/-- Field-level fixed-IVP data implies coordinate-level scalar data once the
solution time set is a neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_field
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData := by
  intro sol
  refine SmoothSelfDiffeomorph3Family.coordinatePullbackMetricInnerDerivativeOn_of_model
    (I := I) (M := M)
    (SmoothSelfDiffeomorph3Family.coordinatePullbackMetricModelDerivativeOn_of_field
      (I := I) (M := M) (hfield sol)) ?_
  intro t ht x u v
  let R : Diffeomorph3GaugeFlowOn (I := I) (M := M)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
    { maps3 := G.maps3 sol
      anchored := G.anchored sol
      satisfies := G.satisfies sol }
  exact R.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
    (I := I) (M := M) (t := t) (htime sol ht)
    sol.1.toIntrinsicDeTurckSolution.metric x u v

/-- Coordinate-model fixed-IVP data packages directly as the tensor time
derivative for every gauge-pulled metric in the bundle, provided the solution
time sets are neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeOn
    (I := I) (M := M)
    ((G.coordinatePullbackMetricInnerDerivativeData_of_model htime hmodel) sol)

/-- Field-level fixed-IVP data packages directly as the tensor time derivative
for every gauge-pulled metric in the bundle, provided the solution time sets are
neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeOn
    (I := I) (M := M)
    ((G.coordinatePullbackMetricInnerDerivativeData_of_field htime hfield) sol)

/-- Coordinate-level fixed-IVP scalar data packages directly as the tensor time
derivative for every gauge-pulled metric in the bundle. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeOn
    (I := I) (M := M) (hcoord sol)

/-- Fixed-IVP named scalar data packages as the time derivative required by
the gauge-pulled metric theorem routes. -/
theorem hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeOn
    (I := I) (M := M) (hinner sol)

/-- The tensor time-derivative package for every member of a fixed-IVP bundle
recovers the named scalar derivative data. -/
theorem pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    G.PullbackMetricInnerDerivativeData := by
  intro sol
  exact SmoothSelfDiffeomorph3Family.pullbackMetricInnerDerivativeOn_of_hasTimeDerivativeOn
    (I := I) (M := M) (hpullDerivative sol)

/-- Fixed-IVP geometric bundle scalar data is equivalent to the tensor
time-derivative package for every member of the bundle. -/
theorem pullbackMetricInnerDerivativeData_iff_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    G.PullbackMetricInnerDerivativeData ↔
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hinner sol
    exact G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner sol
  · intro hpullDerivative
    exact G.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn hpullDerivative

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- Theorem-family named scalar derivative data for all gauge-pulled metrics in a
geometric `C^3` DeTurck gauge-flow family. -/
def PullbackMetricInnerDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    (G.forInitialValueProblem ivp).PullbackMetricInnerDerivativeData

/-- Theorem-family coordinate-level scalar derivative data for all
gauge-pulled metrics in a geometric `C^3` DeTurck gauge-flow family. -/
def CoordinatePullbackMetricInnerDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    (G.forInitialValueProblem ivp).CoordinatePullbackMetricInnerDerivativeData

/-- Theorem-family coordinate-model derivative data for all gauge-pulled metrics
in a geometric `C^3` DeTurck gauge-flow family. -/
def CoordinatePullbackMetricModelDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    (G.forInitialValueProblem ivp).CoordinatePullbackMetricModelDerivativeData

/-- Theorem-family field-level derivative data for all gauge-pulled metrics in a
geometric `C^3` DeTurck gauge-flow family. -/
def CoordinatePullbackMetricFieldDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    (G.forInitialValueProblem ivp).CoordinatePullbackMetricFieldDerivativeData

/-- Coordinate-level theorem-family scalar data implies the named geometric
scalar derivative data used by the gauge-pulled metric routes. -/
theorem pullbackMetricInnerDerivativeData_of_coordinate
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    G.PullbackMetricInnerDerivativeData := by
  intro ivp
  exact (G.forInitialValueProblem ivp).pullbackMetricInnerDerivativeData_of_coordinate
    (I := I) (M := M) (hcoord ivp)

/-- Coordinate-model theorem-family data implies coordinate-level scalar data
once each solution time set is a neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_model
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData := by
  intro ivp
  exact (G.forInitialValueProblem ivp).coordinatePullbackMetricInnerDerivativeData_of_model
    (I := I) (M := M) (htime ivp) (hmodel ivp)

/-- Field-level theorem-family data implies coordinate-level scalar data once
each solution time set is a neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_field
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData := by
  intro ivp
  exact (G.forInitialValueProblem ivp).coordinatePullbackMetricInnerDerivativeData_of_field
    (I := I) (M := M) (htime ivp) (hfield ivp)

/-- Coordinate-model theorem-family data packages directly as the tensor time
derivative for every induced gauge-pulled metric, provided the solution time
sets are neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    (I := I) (M := M) (htime ivp) (hmodel ivp) sol

/-- Field-level theorem-family data packages directly as the tensor time
derivative for every induced gauge-pulled metric, provided the solution time
sets are neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    (I := I) (M := M) (htime ivp) (hfield ivp) sol

/-- Coordinate-level theorem-family scalar data packages directly as the tensor
time derivative for every induced gauge-pulled metric. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    (I := I) (M := M) (hcoord ivp) sol

/-- Theorem-family named scalar data packages as the time derivative required by
the gauge-pulled metric theorem routes. -/
theorem hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    (I := I) (M := M) (hinner ivp) sol

/-- The tensor time-derivative package for every member of a theorem-family
bundle recovers the named scalar derivative data. -/
theorem pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    G.PullbackMetricInnerDerivativeData := by
  intro ivp
  exact (G.forInitialValueProblem ivp).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (I := I) (M := M) (fun sol ↦ hpullDerivative ivp sol)

/-- Theorem-family geometric bundle scalar data is equivalent to the tensor
time-derivative package for every member of the family. -/
theorem pullbackMetricInnerDerivativeData_iff_hasTimeDerivativeOn
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    G.PullbackMetricInnerDerivativeData ↔
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          HasTimeDerivativeOn (I := I) (M := M)
            ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
            sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hinner ivp sol
    exact G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner ivp sol
  · intro hpullDerivative
    exact G.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn hpullDerivative

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

namespace IntrinsicDeTurckGaugeFlowExistence

/-- Fixed-IVP named scalar derivative data for the geometric gauge-flow bundle
induced by raw intrinsic DeTurck gauge-flow existence. -/
def PullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  G.toDiffeomorph3GaugeFlow.PullbackMetricInnerDerivativeData

/-- Fixed-IVP coordinate-level scalar derivative data for the geometric
gauge-flow bundle induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  G.toDiffeomorph3GaugeFlow.CoordinatePullbackMetricInnerDerivativeData

/-- Fixed-IVP coordinate-model derivative data for the geometric gauge-flow
bundle induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricModelDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  G.toDiffeomorph3GaugeFlow.CoordinatePullbackMetricModelDerivativeData

/-- Fixed-IVP field-level derivative data for the geometric gauge-flow bundle
induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricFieldDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) : Prop :=
  G.toDiffeomorph3GaugeFlow.CoordinatePullbackMetricFieldDerivativeData

/-- Coordinate-level fixed-IVP scalar data implies the named geometric scalar
derivative data for a raw intrinsic DeTurck gauge-flow witness. -/
theorem pullbackMetricInnerDerivativeData_of_coordinate
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    G.PullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlow.pullbackMetricInnerDerivativeData_of_coordinate
    (I := I) (M := M) hcoord

/-- Coordinate-model fixed-IVP data implies coordinate-level scalar data for raw
intrinsic DeTurck gauge-flow existence once solution time sets are neighborhoods
of their times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_model
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlow.coordinatePullbackMetricInnerDerivativeData_of_model
    (I := I) (M := M) htime hmodel

/-- Field-level fixed-IVP data implies coordinate-level scalar data for raw
intrinsic DeTurck gauge-flow existence once solution time sets are neighborhoods
of their times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_field
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlow.coordinatePullbackMetricInnerDerivativeData_of_field
    (I := I) (M := M) htime hfield

/-- Raw gauge-flow existence plus coordinate-model data gives the required time
derivative of the induced gauge-pulled metric, provided solution time sets are
neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlow.hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    (I := I) (M := M) htime hmodel sol

/-- Raw gauge-flow existence plus field-level data gives the required time
derivative of the induced gauge-pulled metric, provided solution time sets are
neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlow.hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    (I := I) (M := M) htime hfield sol

/-- Raw gauge-flow existence plus coordinate-level scalar data gives the
required time derivative of the induced gauge-pulled metric. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlow.hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    (I := I) (M := M) hcoord sol

/-- Fixed-IVP raw gauge-flow existence plus named scalar data gives the required
time derivative of the induced gauge-pulled metric. -/
theorem hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlow).gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlow.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    (I := I) (M := M) hinner sol

/-- The tensor time-derivative package for every member of a fixed-IVP raw
gauge-flow existence witness recovers the named scalar derivative data. -/
theorem pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    G.PullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlow.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (I := I) (M := M) hpullDerivative

/-- Fixed-IVP raw gauge-flow scalar data is equivalent to the tensor
time-derivative package for every induced gauge-pulled metric. -/
theorem pullbackMetricInnerDerivativeData_iff_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    G.PullbackMetricInnerDerivativeData ↔
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.flow sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlow).gauge sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hinner sol
    exact G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner sol
  · intro hpullDerivative
    exact G.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn hpullDerivative

/-- The fixed-IVP chosen-background identity raw `C^3` gauge-flow carries the
named scalar derivative data expected by the time-derivative routes. -/
theorem identityOfChosenBackground_pullbackMetricInnerDerivativeData
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M) ivp).PullbackMetricInnerDerivativeData := by
  refine (IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground
    (E := E) (H := H) (I := I) (M := M) ivp).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn ?_
  intro sol
  simpa [IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground,
    IntrinsicDeTurckGaugeFlowExistence.identityOfChosenBackground] using
    IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) ivp sol

/-- The fixed-IVP subsingleton-tangent identity raw `C^3` gauge-flow carries the
named scalar derivative data expected by the time-derivative routes. -/
theorem identityOfSubsingletonTangent_pullbackMetricInnerDerivativeData
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M) ivp).PullbackMetricInnerDerivativeData := by
  refine (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
    (E := E) (H := H) (I := I) (M := M) ivp).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn ?_
  intro sol
  simpa [IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent,
    IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent] using
    IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) ivp sol

/-- Fixed-IVP model-space synonym of
`identityOfSubsingletonTangent_pullbackMetricInnerDerivativeData`. -/
theorem identityOfSubsingletonModel_pullbackMetricInnerDerivativeData
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonModel
      (E := E) (H := H) (I := I) (M := M) ivp).PullbackMetricInnerDerivativeData := by
  refine (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonModel
    (E := E) (H := H) (I := I) (M := M) ivp).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn ?_
  intro sol
  simpa [IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonModel,
    IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonModel] using
    IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonModel_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) ivp sol

/-- Fixed-IVP empty-manifold synonym of the identity raw `C^3` gauge-flow scalar data. -/
theorem identityOfIsEmpty_pullbackMetricInnerDerivativeData
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M) ivp).PullbackMetricInnerDerivativeData := by
  refine (IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty
    (E := E) (H := H) (I := I) (M := M) ivp).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn ?_
  intro sol
  simpa [IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfIsEmpty,
    IntrinsicDeTurckGaugeFlowExistence.identityOfIsEmpty] using
    IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfIsEmpty_hpullDerivative
      (E := E) (H := H) (I := I) (M := M) ivp sol

end IntrinsicDeTurckGaugeFlowExistence

namespace IntrinsicDeTurckGaugeFlowExistenceFamily

/-- Theorem-family named scalar derivative data for the geometric gauge-flow
family induced by raw intrinsic DeTurck gauge-flow existence. -/
def PullbackMetricInnerDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  G.toDiffeomorph3GaugeFlowFamily.PullbackMetricInnerDerivativeData

/-- Theorem-family coordinate-level scalar derivative data for the geometric
gauge-flow family induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricInnerDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  G.toDiffeomorph3GaugeFlowFamily.CoordinatePullbackMetricInnerDerivativeData

/-- Theorem-family coordinate-model derivative data for the geometric gauge-flow
family induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricModelDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  G.toDiffeomorph3GaugeFlowFamily.CoordinatePullbackMetricModelDerivativeData

/-- Theorem-family field-level derivative data for the geometric gauge-flow
family induced by raw intrinsic DeTurck gauge-flow existence. -/
def CoordinatePullbackMetricFieldDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) : Prop :=
  G.toDiffeomorph3GaugeFlowFamily.CoordinatePullbackMetricFieldDerivativeData

/-- Coordinate-level theorem-family scalar data implies the named geometric
scalar derivative data for a raw intrinsic DeTurck gauge-flow family. -/
theorem pullbackMetricInnerDerivativeData_of_coordinate
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    G.PullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlowFamily.pullbackMetricInnerDerivativeData_of_coordinate
    (I := I) (M := M) hcoord

/-- Coordinate-model theorem-family data implies coordinate-level scalar data
for raw intrinsic DeTurck gauge-flow existence once each solution time set is a
neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_model
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlowFamily.coordinatePullbackMetricInnerDerivativeData_of_model
    (I := I) (M := M) htime hmodel

/-- Field-level theorem-family data implies coordinate-level scalar data for raw
intrinsic DeTurck gauge-flow existence once each solution time set is a
neighborhood of each of its times. -/
theorem coordinatePullbackMetricInnerDerivativeData_of_field
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData) :
    G.CoordinatePullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlowFamily.coordinatePullbackMetricInnerDerivativeData_of_field
    (I := I) (M := M) htime hfield

/-- Raw theorem-family gauge-flow existence plus coordinate-model data gives the
required time derivative of every induced gauge-pulled metric, provided solution
time sets are neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hmodel : G.CoordinatePullbackMetricModelDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow ivp sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlowFamily.hasTimeDerivativeOn_of_coordinatePullbackMetricModelDerivativeData
    (I := I) (M := M) htime hmodel ivp sol

/-- Raw theorem-family gauge-flow existence plus field-level data gives the
required time derivative of every induced gauge-pulled metric, provided solution
time sets are neighborhoods of their times. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t)
    (hfield : G.CoordinatePullbackMetricFieldDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow ivp sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlowFamily.hasTimeDerivativeOn_of_coordinatePullbackMetricFieldDerivativeData
    (I := I) (M := M) htime hfield ivp sol

/-- Raw theorem-family gauge-flow existence plus coordinate-level scalar data
gives the required time derivative of every induced gauge-pulled metric. -/
theorem hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow ivp sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlowFamily.hasTimeDerivativeOn_of_coordinatePullbackMetricInnerDerivativeData
    (I := I) (M := M) hcoord ivp sol

/-- Theorem-family raw gauge-flow existence plus named scalar data gives the
required time derivative of every induced gauge-pulled metric. -/
theorem hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      (((G.flow ivp sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.toDiffeomorph3GaugeFlowFamily.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    (I := I) (M := M) hinner ivp sol

/-- The tensor time-derivative package for every member of a theorem-family raw
gauge-flow existence witness recovers the named scalar derivative data. -/
theorem pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.flow ivp sol).maps3).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    G.PullbackMetricInnerDerivativeData :=
  G.toDiffeomorph3GaugeFlowFamily.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (I := I) (M := M) hpullDerivative

/-- Theorem-family raw gauge-flow scalar data is equivalent to the tensor
time-derivative package for every induced gauge-pulled metric. -/
theorem pullbackMetricInnerDerivativeData_iff_hasTimeDerivativeOn
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    G.PullbackMetricInnerDerivativeData ↔
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          HasTimeDerivativeOn (I := I) (M := M)
            (((G.flow ivp sol).maps3).pullbackMetricFamily
              sol.1.toIntrinsicDeTurckSolution.metric)
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
            sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hinner ivp sol
    exact G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner ivp sol
  · intro hpullDerivative
    exact G.pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn hpullDerivative

/-- The chosen-background identity raw `C^3` gauge-flow family carries the named
scalar derivative data expected by the time-derivative routes. -/
theorem identityOfChosenBackground_pullbackMetricInnerDerivativeData :
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground
      (E := E) (H := H) (I := I) (M := M)).PullbackMetricInnerDerivativeData :=
  (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground
    (E := E) (H := H) (I := I) (M := M)).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground_hpullDerivative
        (E := E) (H := H) (I := I) (M := M) ivp sol)

/-- The subsingleton-tangent identity raw `C^3` gauge-flow family carries the
named scalar derivative data expected by the time-derivative routes. -/
theorem identityOfSubsingletonTangent_pullbackMetricInnerDerivativeData
    [∀ x : M, Subsingleton ((TangentSpace I : M → Type _) x)] :
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent
      (E := E) (H := H) (I := I) (M := M)).PullbackMetricInnerDerivativeData :=
  (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent
    (E := E) (H := H) (I := I) (M := M)).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent_hpullDerivative
        (E := E) (H := H) (I := I) (M := M) ivp sol)

/-- Model-space synonym of
`identityOfSubsingletonTangent_pullbackMetricInnerDerivativeData`. -/
theorem identityOfSubsingletonModel_pullbackMetricInnerDerivativeData
    [Subsingleton E] :
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonModel
      (E := E) (H := H) (I := I) (M := M)).PullbackMetricInnerDerivativeData :=
  (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonModel
    (E := E) (H := H) (I := I) (M := M)).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonModel_hpullDerivative
        (E := E) (H := H) (I := I) (M := M) ivp sol)

/-- Empty-manifold synonym of the identity raw `C^3` gauge-flow scalar data. -/
theorem identityOfIsEmpty_pullbackMetricInnerDerivativeData
    [IsEmpty M] :
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfIsEmpty
      (E := E) (H := H) (I := I) (M := M)).PullbackMetricInnerDerivativeData :=
  (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfIsEmpty
    (E := E) (H := H) (I := I) (M := M)).pullbackMetricInnerDerivativeData_of_hasTimeDerivativeOn
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfIsEmpty_hpullDerivative
        (E := E) (H := H) (I := I) (M := M) ivp sol)

end IntrinsicDeTurckGaugeFlowExistenceFamily

/-- A theorem-family chosen-background DeTurck package becomes gauge-reducible
from named scalar derivative data for a geometric `C^3` gauge-flow family. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative G
    (fun ivp sol ↦ G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
      hinner ivp sol)

/-- Intrinsic Ricci-flow theorem-family projection from named scalar derivative
data for a geometric `C^3` gauge-flow family. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    G hinner).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from named scalar derivative
data for a geometric `C^3` gauge-flow family. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    G hinner).toOrdinary

/-- A theorem-family chosen-background DeTurck package becomes gauge-reducible
from raw `C^3` gauge-flow existence plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistencePullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyPullbackMetricInnerDerivative
    G.toDiffeomorph3GaugeFlowFamily hinner

/-- Intrinsic Ricci-flow theorem-family projection from raw `C^3` gauge-flow
existence plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistencePullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistencePullbackMetricInnerDerivative
    G hinner).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from raw `C^3` gauge-flow
existence plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistencePullbackMetricInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistencePullbackMetricInnerDerivative
    G hinner).toOrdinary

/-- A fixed-IVP chosen-background DeTurck package becomes gauge-reducible from
named scalar derivative data for a geometric `C^3` gauge-flow bundle. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative G
    (fun sol ↦ G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner sol)

/-- Intrinsic Ricci-flow fixed-IVP projection from named scalar derivative data
for a geometric `C^3` gauge-flow bundle. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    G hinner).toIntrinsic

/-- Ordinary Ricci-flow fixed-IVP projection from named scalar derivative data
for a geometric `C^3` gauge-flow bundle. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    G hinner).toOrdinary

/-- A fixed-IVP chosen-background DeTurck package becomes gauge-reducible from
raw `C^3` gauge-flow existence plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistencePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundlePullbackMetricInnerDerivative
    G.toDiffeomorph3GaugeFlow hinner

/-- Intrinsic Ricci-flow fixed-IVP projection from raw `C^3` gauge-flow
existence plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistencePullbackMetricInnerDerivative
    G hinner).toIntrinsic

/-- Ordinary Ricci-flow fixed-IVP projection from raw `C^3` gauge-flow existence
plus named scalar derivative data. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistencePullbackMetricInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistencePullbackMetricInnerDerivative
    G hinner).toOrdinary

end RicciFlow
