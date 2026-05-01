module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative

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

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

end RicciFlow
