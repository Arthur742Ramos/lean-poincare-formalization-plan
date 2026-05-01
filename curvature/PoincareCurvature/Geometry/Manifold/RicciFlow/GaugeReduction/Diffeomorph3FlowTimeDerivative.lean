module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence

set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Time-derivative adapters for `C^3` gauge-pulled metrics

This thin module records reusable scalar forms of the static, non-identity
gauge-pullback time-derivative calculation.  The dynamic case still requires the
full chain-rule identity for a time-dependent diffeomorphism family.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology

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
