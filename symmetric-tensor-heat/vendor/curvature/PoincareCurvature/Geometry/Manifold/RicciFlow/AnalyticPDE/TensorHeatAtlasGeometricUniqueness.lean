import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasClosedReconstruction
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.FiniteTensorHeatUniqueness

/-!
# Geometric zero-data uniqueness for a represented tensor heat field

The analytic input here is joint continuity of the complete tensor norm of
the canonical closed-time atlas reconstruction. All spatial differentiability
comes from the actual finite classical field, and its heat equation is the
genuine connection heat operator. No differential Bochner identity is
assumed: the fixed-metric theorem proves the required inequality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- The ambient smooth Riemannian bundle structure has an explicit smooth
metric witness with exactly its existing fiber inner products. -/
private noncomputable def compatibleSmoothMetric :
    Bundle.ContMDiffRiemannianMetric I 2 E TM := by
  let g : Bundle.RiemannianMetric TM := RiemannianBundle.g
  let hexists :=
    (inferInstance : IsContMDiffRiemannianBundle I 2 E TM).exists_contMDiff
  let g' := Classical.choose hexists
  have hg' := (Classical.choose_spec hexists).1
  have hinner := (Classical.choose_spec hexists).2
  have hgg : g' = g.inner := by
    funext x
    ext v w
    change g' x v w = g.inner x v w
    rw [← hinner x v w]
    rfl
  exact {
    inner := g.inner
    symm := g.symm
    pos := g.pos
    isVonNBounded := g.isVonNBounded
    contMDiff := by simpa only [← hgg] using hg'
  }

private theorem compatibleSmoothMetric_eq_bundleMetric :
    (compatibleSmoothMetric (I := I) (E := E) (M := M)).toRiemannianMetric =
      (RiemannianBundle.g : Bundle.RiemannianMetric TM) := by
  rfl

/-- Zero-data uniqueness for the unprojected represented geometric tensor
heat field. The closed-time energy continuity follows from the canonical
atlas reconstruction and the inverse-Gram local-frame identity. -/
theorem atlasFieldOfHigher_zero_of_zeroDataHeat
    : ∀ (cov : CovariantDerivative I E TM)
      [ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1]
      {b : Module.Basis (Fin d) ℝ E}
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ T α)
      (u : HigherCoefficientSpace cov A),
      cov.IsMetricCompatibleTangent →
      atlasInitialTrace cov A u = 0 →
      (∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
        (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x = 0) →
      ∀ t ∈ Ioc t₀ A.commonTerminalTime,
        (atlasFieldOfHigher cov A u).toFun t = 0 := by
  let g₀ := compatibleSmoothMetric (I := I) (E := E) (M := M)
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  intro cov hcov b A u hmetric htrace hheat
  have hcont : ContinuousOn
      (fun p : ℝ × M => covariantTwoTensorNormSq
        (closedAtlasFieldOfHigher cov A u p.1) p.2)
      (Icc t₀ A.commonTerminalTime ×ˢ (Set.univ : Set M)) :=
    (A.continuous_closedAtlasFieldOfHigher_normSq cov u).continuousOn
  have hinitial : ∀ x : M, closedAtlasFieldOfHigher cov A u t₀ x = 0 := by
    intro x
    rw [A.closedAtlasFieldOfHigher_initial cov u, htrace]
    rfl
  have hzeroOpen : ∀ t ∈ Ioo t₀ A.commonTerminalTime,
      (atlasFieldOfHigher cov A u).toFun t = 0 :=
    CovariantDerivative.TimeDependentRiemannianMetric.finiteClassicalTensorHeatField_eq_zero_of_closedExtension
      g₀ cov (atlasFieldOfHigher cov A u)
      (closedAtlasFieldOfHigher cov A u) hmetric hcont
      (fun t ht => A.closedAtlasFieldOfHigher_eq_atlasFieldOfHigher cov u t ht)
      hinitial hheat
  exact A.atlasFieldOfHigher_zero_on_Ioc_of_open_zero cov u hzeroOpen

end RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
