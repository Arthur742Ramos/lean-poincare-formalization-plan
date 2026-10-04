/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.LinearReadoutSecondDerivative
import PoincareCurvature.Geometry.Manifold.RicciFlow.ChosenLeviCivitaCoordinateChristoffel
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatEllipticity

/-!
# The actual frozen metric principal part on a holonomic finite cylinder

Freeze a genuine metric slice in its preferred fixed coordinate frame. The
existing geometric tensor-heat coefficient is exactly the finite inverse-metric
Hessian contraction. The finite-cylinder input is the proved closed derivative
graph, not an independent collection of jets. Its compatibility certificates
identify the bounded Cauchy operator with the actual coordinate differential
operator on the open time interval. Tensor output remains `(j,i)`.

This is differential-operator identification only, not a semigroup, nonlinear
solver, manifold realization, uniqueness theorem, or Point-4 completion.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace RicciFlow.AnalyticPDE

open CovariantDerivative PoincareCurvature.PreferredCoordinateFrame
open PoincareCurvature.CoordinateMatrixJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [I.Boundaryless]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M] {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TW" => (Fin d × Fin d → ℝ)

/-- The preferred tangent frame pulled into its own chart is the model basis. -/
theorem localFrameInChart_preferred_eq_basis
    (p : M) (b : Module.Basis (Fin d) ℝ E) {z : E}
    (hz : z ∈ (extChartAt I p).target) (a : Fin d) :
    localFrameInChart (I := I) p (trivialization (I := I) p) b a z = b a := by
  unfold localFrameInChart
  rw [ModelWithCorners.Boundaryless.range_eq_univ, VectorField.mpullbackWithin_univ]
  change VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm
    (frame (I := I) p b a) z =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (b a)
  exact mpullback_frame_eq_const (I := I) p b hz a

/-- The actual metric slice selects the Riemannian bundle used by the existing
frozen geometric principal coefficient; no background metric is silently used. -/
def chosenLCFrozenTensorHeatPrincipalCoefficient
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x₀ : M) :
    (E →L[ℝ] E →L[ℝ] TW) →L[ℝ] TW :=
  letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle tStar
  frozenLocalTensorHeatPrincipalCoefficient (I := I) p (trivialization (I := I) p) b x₀

/-- The actual preferred-frame inverse Gram matrix equals the inverse of the
actual metric-coordinate matrix, derived from the existing actual Gram theorem. -/
theorem chosenLC_localFrameInverseGramMatrix_eq_inverse
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}
    (hx₀ : x₀ ∈ (extChartAt I p).source) :
    letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
    localFrameInverseGramMatrix (I := I) (trivialization (I := I) p) b x₀ =
      inverse (chosenLCMetricCoordinates g tStar p b)
        (chosenLCCoordinatePoint (I := I) p b x₀) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
  change localFrameInverseGramMatrix (I := I) (trivialization (I := I) p) b x₀ =
    (show Matrix (Fin d) (Fin d) ℝ from chosenLCMetricCoordinates g tStar p b
      (chosenLCCoordinatePoint (I := I) p b x₀))⁻¹
  rw [chosenLCMetricCoordinates_eq_Gram g tStar p b hx₀]
  rfl

/-- Actual inverse-metric identification of the existing frozen principal part. -/
theorem chosenLCFrozenTensorHeatPrincipalCoefficient_apply
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}
    (hx₀ : x₀ ∈ (extChartAt I p).source)
    (Q : E →L[ℝ] E →L[ℝ] TW) (out : Fin d × Fin d) :
    chosenLCFrozenTensorHeatPrincipalCoefficient g tStar p b x₀ Q out =
      ∑ a : Fin d, ∑ c : Fin d,
        inverse (chosenLCMetricCoordinates g tStar p b)
          (chosenLCCoordinatePoint (I := I) p b x₀) a c * Q (b a) (b c) out := by
  letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle tStar
  change frozenLocalTensorHeatPrincipalCoefficient (I := I)
    p (trivialization (I := I) p) b x₀ Q out = _
  rw [frozenLocalTensorHeatPrincipalCoefficient, localTensorHeatPrincipalCoefficient,
    movingFramePrincipalCoefficient_apply]
  have hz₀ := (extChartAt I p).map_source hx₀
  simp only [localFrameInverseGramMatrixInChart_apply (I := I) p _ b hx₀,
    chosenLC_localFrameInverseGramMatrix_eq_inverse g tStar p b hx₀,
    localFrameInChart_preferred_eq_basis (I := I) p b hz₀]

/-- The existing bounded Cauchy operator with its metric frozen to the actual slice. -/
def chosenLCFrozenTensorHeatCauchyL
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x₀ : M) (t₀ T α : ℝ) :
    FiniteParabolicC2AlphaBanach E TW t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E TW α (parabolicFiniteCylinder E t₀ T) :=
  letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle tStar
  frozenTensorHeatCauchyL (I := I) p (trivialization (I := I) p) b x₀ t₀ T α

/-- Genuine tensor coordinate readout, preserving the existing output reversal. -/
def finiteCylinderTensorReadout
    (b : Module.Basis (Fin d) ℝ E) {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    (s : ℝ) (ξ : Fin d → ℝ) (i j : Fin d) : ℝ :=
  FiniteParabolicC2AlphaBanach.value u (s, toModel b ξ) (j, i)

/-- Compatibility identifies the actual iterated spatial derivative after the
finite-basis change of model. No extra candidate regularity is needed. -/
theorem second_finiteCylinderTensorReadout
    (b : Module.Basis (Fin d) ℝ E) {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    {s : ℝ} (hs : s ∈ Set.Ioc t₀ T) (ξ : Fin d → ℝ) (a c i j : Fin d) :
    second (finiteCylinderTensorReadout b u s) ξ a c i j =
      FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, toModel b ξ)
        (b a) (b c) (j, i) := by
  have h := PoincareCurvature.second_fderiv_linear_readout
    (toModel b).toContinuousLinearMap
    (ContinuousLinearMap.proj (j, i) : TW →L[ℝ] ℝ)
    (fun y => FiniteParabolicC2AlphaBanach.value u (s, y))
    (fun y => FiniteParabolicC2AlphaBanach.spaceDeriv u (s, y))
    (FiniteParabolicC2AlphaBanach.hasFDerivAt_space u hs)
    ξ (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, toModel b ξ))
    (FiniteParabolicC2AlphaBanach.hasFDerivAt_spaceDeriv u hs (toModel b ξ))
    (coordinateVector a) (coordinateVector c)
  simpa only [second, finiteCylinderTensorReadout, ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe, coordinateVector, toModel_coordinateVector] using h

/-- On the open time interval the stored compatible time derivative is the
actual derivative of the tensor coordinate readout. -/
theorem deriv_finiteCylinderTensorReadout
    (b : Module.Basis (Fin d) ℝ E) {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    {s : ℝ} (hs : s ∈ Set.Ioo t₀ T) (ξ : Fin d → ℝ) (i j : Fin d) :
    deriv (fun r => finiteCylinderTensorReadout b u r ξ i j) s =
      FiniteParabolicC2AlphaBanach.timeDeriv u (s, toModel b ξ) (j, i) := by
  exact ((ContinuousLinearMap.proj (j, i) : TW →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
    (FiniteParabolicC2AlphaBanach.hasDerivAt_time u hs (toModel b ξ))).deriv

/-- Evaluation on `(t₀,T]` identifies the metric Hessian trace. At the terminal
time the time slot retains its stored compatible meaning. -/
theorem evalCLM_chosenLCFrozenTensorHeatCauchyL
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}
    (hx₀ : x₀ ∈ (extChartAt I p).source) {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    {s : ℝ} (hs : s ∈ Set.Ioc t₀ T) (ξ : Fin d → ℝ) (i j : Fin d) :
    ParabolicC0AlphaBanach.evalCLM (s, toModel b ξ)
        (show (s, toModel b ξ) ∈ parabolicFiniteCylinder E t₀ T from
          mem_parabolicFiniteCylinder.mpr ⟨hs.1, hs.2⟩)
        (chosenLCFrozenTensorHeatCauchyL g tStar p b x₀ t₀ T α u) (j, i) =
      FiniteParabolicC2AlphaBanach.timeDeriv u (s, toModel b ξ) (j, i) -
        ∑ a : Fin d, ∑ c : Fin d,
          inverse (chosenLCMetricCoordinates g tStar p b)
            (chosenLCCoordinatePoint (I := I) p b x₀) a c *
            second (finiteCylinderTensorReadout b u s) ξ a c i j := by
  letI : Bundle.RiemannianBundle TM := ⟨(g tStar).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle tStar
  have hz : (s, toModel b ξ) ∈ parabolicFiniteCylinder E t₀ T :=
    mem_parabolicFiniteCylinder.mpr ⟨hs.1, hs.2⟩
  have h := congrFun (evalCLM_frozenTensorHeatCauchyL (I := I)
    p (trivialization (I := I) p) b x₀ u (s, toModel b ξ) hz) (j, i)
  change _ = FiniteParabolicC2AlphaBanach.timeDeriv u (s, toModel b ξ) (j, i) -
    chosenLCFrozenTensorHeatPrincipalCoefficient g tStar p b x₀
      (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, toModel b ξ)) (j, i) at h
  rw [chosenLCFrozenTensorHeatPrincipalCoefficient_apply g tStar p b hx₀] at h
  simpa only [chosenLCFrozenTensorHeatCauchyL,
    second_finiteCylinderTensorReadout b u hs] using h

/-- The genuine holonomic frozen Cauchy action, with actual time differentiation
and the actual inverse-metric spatial Hessian trace on the open time interval. -/
theorem evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives
    (g : MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}
    (hx₀ : x₀ ∈ (extChartAt I p).source) {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    {s : ℝ} (hs : s ∈ Set.Ioo t₀ T) (ξ : Fin d → ℝ) (i j : Fin d) :
    ParabolicC0AlphaBanach.evalCLM (s, toModel b ξ)
        (show (s, toModel b ξ) ∈ parabolicFiniteCylinder E t₀ T from
          mem_parabolicFiniteCylinder.mpr ⟨hs.1, hs.2.le⟩)
        (chosenLCFrozenTensorHeatCauchyL g tStar p b x₀ t₀ T α u) (j, i) =
      deriv (fun r => finiteCylinderTensorReadout b u r ξ i j) s -
        ∑ a : Fin d, ∑ c : Fin d,
          inverse (chosenLCMetricCoordinates g tStar p b)
            (chosenLCCoordinatePoint (I := I) p b x₀) a c *
            second (finiteCylinderTensorReadout b u s) ξ a c i j := by
  rw [deriv_finiteCylinderTensorReadout b u hs]
  exact evalCLM_chosenLCFrozenTensorHeatCauchyL g tStar p b hx₀ u ⟨hs.1, hs.2.le⟩ ξ i j

end RicciFlow.AnalyticPDE
