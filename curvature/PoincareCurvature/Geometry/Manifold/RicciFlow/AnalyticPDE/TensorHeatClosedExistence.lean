import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasAffineCorrection
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasLocalUniqueness

/-!
# Closed-manifold tensor-heat existence without atlas assumptions

This file combines compact-atlas construction, the quantitative short-time
commutator contraction, and the arbitrary-trace affine correction.  The
result quantifies only over the geometric background and the time/Holder
parameters: the finite atlas and its strict commutator lift are conclusions,
not hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 4000000

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance closedExistenceThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance closedExistenceThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance closedExistenceThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance closedExistenceThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance closedExistenceThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance closedExistenceThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance closedExistenceThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- **Short-time existence for the tensor heat equation on a closed
Riemannian manifold, with no atlas or parametrix hypothesis.**

The theorem constructs a positive terminal time, a finite normalized atlas,
and the strict commutator lift.  For every higher atlas initial extension and
every atlas Holder source, the resulting classical field has the prescribed
geometric initial trace, solves the actual intrinsic connection heat
equation, and satisfies the explicit finite-atlas Schauder estimate.

The atlas data are part of the conclusion so subsequent intrinsic data-space
encoders can target the single atlas selected here without adding an analytic
solvability assumption. -/
theorem exists_short_affine_tensorHeat_solver
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (S : ℝ) (_hS : t₀ < S)
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ S α)
      (K : CommutatorLift cov A),
      HasLocalZeroTraceUniqueness cov A ∧
        ∀ (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A),
          FiniteClassicalTensorHeatField.HasInitialTrace cov
              (affineCorrectedField cov A K h f) (atlasInitialTrace cov A h) ∧
            (∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
              (affineCorrectedField cov A K h f).tensorHeatOperator cov t ht x =
                A.physicalAtlasSourceSlice cov f t x) ∧
            ‖affineLocalSolutionFamily cov A h
                (affineCorrectedCoordinateSource cov K h f)‖ ≤
              ‖h‖ + ‖localSolutionFamilyL cov A‖ *
                (1 - ‖K.toContinuousLinearMap‖)⁻¹ *
                  ‖f - localCoordinateCauchyFamilyL cov A h +
                    higherAtlasCommutatorLiftL cov A h‖ := by
  obtain ⟨A₀, hmargin⟩ := exists_atlas_with_frozen_margin cov b hT hα hα1
  obtain ⟨S, hS, hST, ⟨K⟩⟩ :=
    exists_restrictedTerminalAtlas_commutatorLift cov A₀
  let A := A₀.restrictTerminalAtlas cov hS hST
  refine ⟨S, hS, A, K,
    hasLocalZeroTraceUniqueness_restrictTerminalAtlas
      cov A₀ hmargin hS hST, ?_⟩
  intro h f
  refine ⟨hasInitialTrace_affineCorrectedField cov A K h f, ?_, ?_⟩
  · intro t ht x
    exact affineCorrectedField_tensorHeatOperator cov A K h f t ht x
  · exact norm_affineCorrectedSolutionFamily_le cov K h f

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
