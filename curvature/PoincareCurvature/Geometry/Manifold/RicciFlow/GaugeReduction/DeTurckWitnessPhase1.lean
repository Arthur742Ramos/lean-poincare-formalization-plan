/-
Phase 1 of VariationalWitness construction: model field and derivative.

This module defines the model vector field `f` and its derivative `Df` for the
DeTurck variational witness, using `deTurckGaugeCoordinateField` (which is
DEFINED as the chart representative of `intrinsicDeTurckGaugeField` via
`mfderiv`).

CRITICAL: We use `deTurckGaugeCoordinateField`, NOT `deTurckVectorOfJet`.
The coordinate/intrinsic bridge is built into the definition, avoiding the
unproved bridge obligation.

CONVENTION: `intrinsicDeTurckGaugeField` is the negated DeTurck vector field;
`deTurckGaugeCoordinateField` preserves this negation.

BUILD NOTE: The `VariationalLocalFlowSolution` construction (via
`ModelGaugeFlowODE.ofProductClosedBallEstimates`) is BLOCKED by the build
deadlock: `ModelGaugeFlowODE` imports `Diffeomorph3FlowExistence`, which
fails with "Fields missing: `variational`" (G2 audit failure).
-/
module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCoordinatePicardEstimates

open RicciFlow

/-- The model vector field for the witness: the coordinate DeTurck field.

Uses `RicciFlow.deTurckGaugeCoordinateField`, which is DEFINED as the chart
representative of `intrinsicDeTurckGaugeField` (the negated DeTurck field)
via `mfderiv`. The coordinate/intrinsic bridge is built into the definition,
avoiding the unproved "critical open obligation" for `deTurckVectorOfJet`
(the explicit 2-jet formula). -/
noncomputable def DeTurckWitnessPhase1.witnessModelField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I (⊤ : ℕ∞) M] [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) : ℝ → E → E :=
  deTurckGaugeCoordinateField g background p₀

/-- The derivative of the model field: the Fréchet derivative in space. -/
noncomputable def DeTurckWitnessPhase1.witnessModelDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I (⊤ : ℕ∞) M] [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) : ℝ → E → E →L[ℝ] E :=
  deTurckGaugeCoordinateDerivative g background p₀

/-- The derivative is the Fréchet derivative of the field (by definition). -/
theorem DeTurckWitnessPhase1.witnessModelDerivative_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I (⊤ : ℕ∞) M] [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t : ℝ) (y : E) :
    DeTurckWitnessPhase1.witnessModelDerivative g background p₀ t y =
      fderiv ℝ (DeTurckWitnessPhase1.witnessModelField g background p₀ t) y := by
  rfl
