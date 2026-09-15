module

public import PoincareCurvature.Analysis.LocalExtremaSecondDerivative
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart

/-!
# Scalar Laplacians at local extrema

This file begins the intrinsic maximum-principle bridge.  In particular, a
local minimum on a boundaryless manifold is proved to be a critical point;
this is not included as an assumption in later geometric arguments.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1500000

open Bundle FiberBundle Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)

/-- A scalar function has zero intrinsic differential at a local minimum on
a boundaryless manifold. -/
theorem scalarDifferential_eq_zero_of_isLocalMin
    {f : M → ℝ} {x : M} (hmin : IsLocalMin f x) (hf : MDiffAt f x) :
    scalarDifferential (I := I) f x = 0 := by
  let φ := extChartAt I x
  let z := φ x
  have hxSource : x ∈ φ.source := by
    simpa [φ] using mem_extChartAt_source x
  have hzTarget : z ∈ φ.target := φ.map_source hxSource
  have hsymm : φ.symm z = x := φ.left_inv hxSource
  have hsymmCont : ContinuousAt φ.symm z := by
    simpa [φ, z] using continuousAt_extChartAt_symm (I := I) x
  have hchartMin :
      IsLocalMin (writtenInExtChartAt I 𝓘(ℝ) x f) z := by
    have hbase : IsLocalMin f (φ.symm z) := by simpa [hsymm] using hmin
    have hcomp := hbase.comp_continuous hsymmCont
    simpa [writtenInExtChartAt, φ, z, Function.comp_def,
      chartAt_self_eq] using hcomp
  have hchartCritical :
      fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) z = 0 :=
    hchartMin.fderiv_eq_zero
  ext u
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  calc
    scalarDifferential (I := I) f x u = mvfderiv (I := I) f x (X x) := by
      rw [scalarDifferential_apply, show X x = u by simp [X, smoothExtend_apply]]
    _ = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) z
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X
            (Set.range I) z) := by
      simpa [φ, z] using mvfderiv_apply_eq_fderivWithin_fixedChart
        (I := I) (g := f) (X := X) (p := x) (y := x) hxSource hf
    _ = 0 := by
      rw [I.range_eq_univ, fderivWithin_univ, hchartCritical]
      exact ContinuousLinearMap.zero_apply _

end CovariantDerivative
