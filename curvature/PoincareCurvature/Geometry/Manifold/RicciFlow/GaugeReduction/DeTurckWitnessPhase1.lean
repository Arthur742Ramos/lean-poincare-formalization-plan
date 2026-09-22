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

The theorem `variationalLocalFlowSolution_of_picardEstimates` below now carries
out the cycle-free model-space construction from the component estimates.  It
still takes the explicit `C²`/joint-continuity regularity package as input;
constructing that geometric package for the genuine DeTurck field remains a
separate Phase-1b obligation.
-/
module
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCoordinatePicardEstimates
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODECore
public import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckPicardRegularityReduction

open RicciFlow
open Metric Set
open scoped Manifold ContDiff Topology NNReal

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

/-! ## Cycle-free Picard-flow construction -/

/-- Construct the model-space variational flow from the genuine component
Picard estimates for the coordinate DeTurck field.

The estimate theorem now exposes `t₀ ∈ Icc tmin tmax`; this is needed to form
the dependent time-point argument of `VariationalLocalFlowSolution`.  The
construction below invokes the cycle-free `ModelGaugeFlowODECore` constructor
and derives the product-field continuity and norm bounds from the component
estimates.  It therefore constructs an actual variational ODE solution, while
leaving the geometric `C²`/joint-continuity hypotheses explicit. -/
theorem DeTurckWitnessPhase1.variationalLocalFlowSolution_of_picardEstimates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I (⊤ : ℕ∞) M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (hreg : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ 2
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
        (ball (extChartAt I p₀ p₀) ((a : ℝ) + 1)))
    (hjoint : ContinuousOn
      (fun p : ℝ × E =>
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1 p.2,
          fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1) p.2))
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ)))
    (hjoint2 : ContinuousOn
      (fun p : ℝ × E =>
        fderiv ℝ
          (fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ))) :
    ∃ (tmin tmax : ℝ) (r : ℝ≥0) (t₀' : Icc tmin tmax)
      (_α : @ModelGaugeFlowODE.VariationalLocalFlowSolution
        E _ _ (DeTurckWitnessPhase1.witnessModelField g background p₀)
        (DeTurckWitnessPhase1.witnessModelDerivative g background p₀)
        tmin tmax t₀' (extChartAt I p₀ p₀) r),
      t₀'.1 = t₀ := by
  let f : ℝ → E → E := DeTurckWitnessPhase1.witnessModelField g background p₀
  let Df : ℝ → E → E →L[ℝ] E :=
    DeTurckWitnessPhase1.witnessModelDerivative g background p₀
  let y₀ : E := extChartAt I p₀ p₀
  obtain ⟨tmin, tmax, r, Kf, KD, Lf, BA, BD, ht₀, hest⟩ :=
    deTurckGaugeCoordinatePicardEstimates
      (I := I) (M := M) g background p₀ t₀ a ha (1 : E →L[ℝ] E)
      hreg hjoint hjoint2
  rcases hest with ⟨hf_lip, hest⟩
  rcases hest with ⟨hDf_lip, hest⟩
  rcases hest with ⟨hf_bound, hest⟩
  rcases hest with ⟨hA_bound, hest⟩
  rcases hest with ⟨hD_bound, hest⟩
  rcases hest with ⟨hf_cont, hest⟩
  rcases hest with ⟨hDf_cont, hmul⟩
  have hf_lip' : ∀ t ∈ Icc tmin tmax,
      LipschitzOnWith Kf (f t) (closedBall y₀ (a : ℝ)) := by
    simpa [f, y₀, DeTurckWitnessPhase1.witnessModelField] using hf_lip
  have hDf_lip' : ∀ t ∈ Icc tmin tmax,
      LipschitzOnWith KD (Df t) (closedBall y₀ (a : ℝ)) := by
    simpa [Df, y₀, DeTurckWitnessPhase1.witnessModelDerivative] using hDf_lip
  have hf_bound' : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall y₀ (a : ℝ),
      ‖f t y‖ ≤ (Lf : ℝ) := by
    simpa [f, y₀, DeTurckWitnessPhase1.witnessModelField] using hf_bound
  have hD_bound' : ∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall y₀ (a : ℝ),
      ‖Df t y‖₊ ≤ BD := by
    simpa [Df, y₀, DeTurckWitnessPhase1.witnessModelDerivative] using hD_bound
  have hf_cont' : ∀ y ∈ closedBall y₀ (a : ℝ),
      ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax) := by
    simpa [f, y₀, DeTurckWitnessPhase1.witnessModelField] using hf_cont
  have hDf_cont' : ∀ y ∈ closedBall y₀ (a : ℝ),
      ContinuousOn (fun t : ℝ => Df t y) (Icc tmin tmax) := by
    simpa [Df, y₀, DeTurckWitnessPhase1.witnessModelDerivative] using hDf_cont
  have hcont : ∀ z ∈ closedBall (y₀, (1 : E →L[ℝ] E)) (a : ℝ),
      ContinuousOn
        (fun t : ℝ => ModelGaugeFlowODE.variationalVectorField f Df t z)
        (Icc tmin tmax) := by
    intro z hz
    have hzprod : z.1 ∈ closedBall y₀ (a : ℝ) ∧
        z.2 ∈ closedBall (1 : E →L[ℝ] E) (a : ℝ) := by
      have hz' : z ∈ closedBall y₀ (a : ℝ) ×ˢ
          closedBall (1 : E →L[ℝ] E) (a : ℝ) := by
        rw [closedBall_prod_same y₀ (1 : E →L[ℝ] E) (a : ℝ)]
        exact hz
      exact hz'
    have hlin : ContinuousOn
        (fun t : ℝ => (Df t z.1).comp z.2) (Icc tmin tmax) := by
      simpa using hDf_cont' z.1 hzprod.1 |>.clm_comp
        (continuousOn_const (c := z.2))
    simpa [ModelGaugeFlowODE.variationalVectorField] using
      (hf_cont' z.1 hzprod.1).prodMk hlin
  have hnorm : ∀ t ∈ Icc tmin tmax,
      ∀ z ∈ closedBall (y₀, (1 : E →L[ℝ] E)) (a : ℝ),
        ‖ModelGaugeFlowODE.variationalVectorField f Df t z‖ ≤
          max Lf (BD * BA) := by
    intro t ht z hz
    have hzprod : z.1 ∈ closedBall y₀ (a : ℝ) ∧
        z.2 ∈ closedBall (1 : E →L[ℝ] E) (a : ℝ) := by
      have hz' : z ∈ closedBall y₀ (a : ℝ) ×ˢ
          closedBall (1 : E →L[ℝ] E) (a : ℝ) := by
        rw [closedBall_prod_same y₀ (1 : E →L[ℝ] E) (a : ℝ)]
        exact hz
      exact hz'
    have hD_bound'' : ‖Df t z.1‖ ≤ (BD : ℝ) := by
      exact_mod_cast hD_bound' t ht z.1 hzprod.1
    have hA_bound'' : ‖z.2‖ ≤ (BA : ℝ) := by
      exact_mod_cast hA_bound z.2 hzprod.2
    have hlin : ‖(Df t z.1).comp z.2‖ ≤ (BD * BA : ℝ≥0) := by
      calc
        ‖(Df t z.1).comp z.2‖ ≤ ‖Df t z.1‖ * ‖z.2‖ :=
          (Df t z.1).opNorm_comp_le z.2
        _ ≤ (BD : ℝ) * (BA : ℝ) := by gcongr
        _ = (BD * BA : ℝ≥0) := by rw [NNReal.coe_mul]
    rw [ModelGaugeFlowODE.variationalVectorField, Prod.norm_mk]
    exact max_le_max (hf_bound' t ht z.1 hzprod.1) hlin
  let t₀' : Icc tmin tmax := ⟨t₀, ht₀⟩
  refine ⟨tmin, tmax, r, t₀', ?_, rfl⟩
  exact ModelGaugeFlowODE.VariationalLocalFlowSolution.ofProductClosedBallEstimates
      (f := f) (Df := Df) (t₀ := t₀') (x₀ := y₀) (r := r) (R := r)
      hf_lip' hDf_lip' hA_bound hD_bound' hcont hnorm
      (by simpa [t₀'] using hmul) le_rfl

/-- Construct the same model-space variational flow after applying the proven
smooth-jet regularity reduction.

This packages the dependency chain
`SmoothDeTurckJetMap` + joint continuity of its jet
`→ hreg ∧ hjoint ∧ hjoint2 → VariationalLocalFlowSolution`.  The jet map and
its joint-continuity hypothesis remain explicit geometric inputs; this theorem
only composes the already-proved calculus reduction with the cycle-free ODE
constructor above. -/
theorem DeTurckWitnessPhase1.variationalLocalFlowSolution_of_smoothJetMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
    [IsManifold I (⊤ : ℕ∞) M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [SigmaCompactSpace M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (J : Type*) [NormedAddCommGroup J] [NormedSpace ℝ J]
    (JM : SmoothDeTurckJetMap
      (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀)
      (extChartAt I p₀ p₀) ((a : ℝ) + 1) J)
    (hS : ContinuousOn JM.S
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ
        closedBall (extChartAt I p₀ p₀) ((a : ℝ) + 1))) :
    ∃ (tmin tmax : ℝ) (r : ℝ≥0) (t₀' : Icc tmin tmax)
      (_α : @ModelGaugeFlowODE.VariationalLocalFlowSolution
        E _ _ (DeTurckWitnessPhase1.witnessModelField g background p₀)
        (DeTurckWitnessPhase1.witnessModelDerivative g background p₀)
        tmin tmax t₀' (extChartAt I p₀ p₀) r),
      t₀'.1 = t₀ := by
  obtain ⟨hreg, hjoint, hjoint2⟩ :=
    smoothJetMap_implies_picardRegularity
      (I := I) (M := M) g background p₀ t₀ a ha J JM hS
  exact variationalLocalFlowSolution_of_picardEstimates
    (I := I) (M := M) g background p₀ t₀ a ha hreg hjoint hjoint2
