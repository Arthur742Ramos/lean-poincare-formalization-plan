import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2MappedAffineGenerator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFrozenInverse
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.BoundarylessInitialMetricLocalization

/-!
# Literal initial metric inverse-Gram coefficients of normalized scalar heat

Source candidate, uncompiled. The Riemannian structure is installed from g0
inside the public coordinate constructor and proofs. Preferred coordinate size
d and orthonormal tangent size finrank(TM p) remain distinct. The canonical
inverse-metric tensor, evaluated on genuine basis coordinate functionals,
identifies the structural L L-transpose coefficients with the literal inverse
Gram matrix. No metric coefficient identity, generator or background oracle is
supplied. Scalar normalization does not change the preferred tensor frame.

Only the right initial generator is identified. Positive-time PDE, Schauder
range identification and nonlinear interval Ricci flow remain separate goals.
-/

noncomputable section

open Bundle FiberBundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology BigOperators
open PoincareCurvature.PreferredCoordinateFrame

namespace RicciFlow.AnalyticPDE

open CovariantDerivative

variable {E : Type*} [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
    [finiteE : FiniteDimensional ℝ E] [completeE : CompleteSpace E]
    {H : Type*} [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [topM : TopologicalSpace M] [chartM : ChartedSpace H M] [hausdorffM : T2Space M]
    [manifoldM : IsManifold I ∞ M] [boundarylessM : BoundarylessManifold I M]
    [smoothTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)

include normE spaceE finiteE completeE topH topM chartM hausdorffM manifoldM boundarylessM smoothTangent

section InternalRiemannianProof

variable [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

private theorem preferred_chartCoordinate_eq_basisAt
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (hp : p ∈ (trivialization (I := I) p).baseSet) (v : TM p) :
    (toModel b).symm
        (extChartDerivativeEquivAt (I := I) p p (mem_extChartAt_source p) v) =
      ((trivialization (I := I) p).basisAt b hp).equivFun v := by
  change b.equivFun
      (extChartDerivativeEquivAt (I := I) p p (mem_extChartAt_source p) v) =
    (b.map ((trivialization (I := I) p).linearEquivAt ℝ p hp).symm).equivFun v
  rw [Module.Basis.map_equivFun]
  change b.equivFun
      (extChartDerivativeEquivAt (I := I) p p (mem_extChartAt_source p) v) =
    b.equivFun ((trivialization (I := I) p).linearEquivAt ℝ p hp v)
  congr 1
  rw [extChartDerivativeEquivAt_apply,
    ← TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (x₀ := p) (x := p) (by
        simpa only [extChartAt_source] using (mem_extChartAt_source (I := I) p))]
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivialization (I := I) p) hp v).trans
      (Bundle.Trivialization.linearEquivAt_apply
        (trivialization (I := I) p) p hp v).symm

private theorem chartOrthonormal_coefficient_eq_local_inverseGram
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (hp : p ∈ (trivialization (I := I) p).baseSet) (i j : Fin d) :
    affineSpatialGramCoefficient
        ((chartOrthonormalSpatialEquiv (I := I) p p (mem_extChartAt_source p)).trans
          (toModel b).symm) i j =
      localFrameInverseGramMatrix (I := I) (trivialization (I := I) p) b p i j := by
  classical
  let _ : FiniteDimensional ℝ (TM p) := VectorBundle.finiteDimensional ℝ E TM p
  let bas : Module.Basis (Fin d) ℝ (TM p) :=
    (trivialization (I := I) p).basisAt b hp
  let o : OrthonormalBasis (Fin (Module.finrank ℝ (TM p))) ℝ (TM p) :=
    stdOrthonormalBasis ℝ (TM p)
  have hframe (s : Fin d) :
      (trivialization (I := I) p).localFrame b s p = bas s :=
    Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := trivialization (I := I) p) (b := b) hp
  have hcoord (k : Fin (Module.finrank ℝ (TM p))) (s : Fin d) :
      ((chartOrthonormalSpatialEquiv (I := I) p p (mem_extChartAt_source p)).trans
        (toModel b).symm) (Pi.single k 1) s = bas.equivFun (o k) s := by
    change (toModel b).symm
      (chartOrthonormalSpatialEquiv (I := I) p p (mem_extChartAt_source p)
        (Pi.single k 1)) s = bas.equivFun (o k) s
    rw [chartOrthonormalSpatialEquiv_single]
    change (toModel b).symm (mfderiv% (extChartAt I p) p (o k)) s = bas.equivFun (o k) s
    rw [← extChartDerivativeEquivAt_apply
      (I := I) p p (mem_extChartAt_source p) (o k)]
    exact congrFun (preferred_chartCoordinate_eq_basisAt (I := I) p b hp (o k)) s
  let K : TM p →ₗ[ℝ] TM p →ₗ[ℝ] ℝ :=
    { toFun := fun v => (bas.coord i v) • bas.coord j
      map_add' := by
        intro v w
        simp only [map_add, add_smul]
      map_smul' := by
        intro c v
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, smul_smul] }
  have hK (v w : TM p) : K v w = bas.equivFun v i * bas.equivFun w j := rfl
  have hleft : TensorProduct.lift K (InnerProductSpace.canonicalCovariantTensor (TM p)) =
      localFrameInverseGramMatrix (I := I) (trivialization (I := I) p) b p i j := by
    rw [bilinearContraction_eq_sum_localFrame_inverseGram
      (I := I) K (trivialization (I := I) p) b hp]
    simp [hK, hframe, Module.Basis.equivFun_apply, Module.Basis.repr_self_apply,
      mul_ite, ite_mul]
  have hright : TensorProduct.lift K (InnerProductSpace.canonicalCovariantTensor (TM p)) =
      ∑ k : Fin (Module.finrank ℝ (TM p)), bas.equivFun (o k) i * bas.equivFun (o k) j := by
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum (TM p) o, map_sum]
    simp only [TensorProduct.lift.tmul, hK]
  calc
    _ = ∑ k : Fin (Module.finrank ℝ (TM p)), bas.equivFun (o k) i * bas.equivFun (o k) j := by
      unfold affineSpatialGramCoefficient
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoord k i, hcoord k j]
    _ = TensorProduct.lift K (InnerProductSpace.canonicalCovariantTensor (TM p)) := hright.symm
    _ = _ := hleft

end InternalRiemannianProof

/-- Actual orthonormal tangent coordinates mapped through the chart differential
and then into the unchanged preferred finite coordinates. The metric is g0. -/
def initialMetricOrthonormalCoordinateEquiv
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) :
    (Fin (Module.finrank ℝ (TM p)) → ℝ) ≃L[ℝ] (Fin d → ℝ) := by
  letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  exact (chartOrthonormalSpatialEquiv (I := I) p p (mem_extChartAt_source p)).trans
    (toModel b).symm

/-- The normalized scalar generator coefficients are precisely the inverse of
the literal initial metric matrix in the preferred tensor-component frame.
Explicit Matrix.inv avoids pointwise inversion of the iterated function type. -/
theorem initialMetricOrthonormalCoefficient_eq_literal_inverseGram
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (i j : Fin d) :
    affineSpatialGramCoefficient (initialMetricOrthonormalCoordinateEquiv g₀ p b) i j =
      (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
        (Matrix.of (initialMetricCoordinates g₀ p b
          (initialMetricCoordinatePoint (I := I) p b)))) i j := by
  classical
  letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  have hp : p ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (mem_extChartAt_source (I := I) p)
  have hcoeff := chartOrthonormal_coefficient_eq_local_inverseGram (I := I) p b hp i j
  change affineSpatialGramCoefficient
    ((chartOrthonormalSpatialEquiv (I := I) p p (mem_extChartAt_source p)).trans
      (toModel b).symm) i j = _
  rw [hcoeff]
  have hgram : Matrix.of
      (localFrameGramMatrix (I := I) (trivialization (I := I) p) b p) =
      Matrix.of (initialMetricCoordinates g₀ p b
        (initialMetricCoordinatePoint (I := I) p b)) := by
    ext s t
    change g₀.inner p (frame (I := I) p b s p) (frame (I := I) p b t p) =
      initialMetricCoordinates g₀ p b (initialMetricCoordinatePoint (I := I) p b) s t
    symm
    simp only [initialMetricCoordinates, initialMetricCoordinatePoint, scalarReadout,
      Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
    rfl
  change (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
      (Matrix.of (localFrameGramMatrix (I := I) (trivialization (I := I) p) b p))) i j = _
  exact congrArg (fun A : Matrix (Fin d) (Fin d) ℝ =>
    (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv A) i j) hgram

/-- The constructed scalar path, normalized by the literal g0 metric and mapped
back, has the actual right initial frozen inverse-metric Hessian contraction. -/
theorem hasDerivWithinAt_initialMetricMappedHeat_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E)
    (D : EuclideanBoundedC2Data d) (z : Fin d → ℝ) :
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D
        (initialMetricCoordinatePoint (I := I) p b)
        (initialMetricOrthonormalCoordinateEquiv g₀ p b) t z)
      (∑ i : Fin d, ∑ j : Fin d,
        (@Inv.inv (Matrix (Fin d) (Fin d) ℝ) Matrix.inv
          (Matrix.of (initialMetricCoordinates g₀ p b
            (initialMetricCoordinatePoint (I := I) p b)))) i j * D.second i j z)
      (Ici 0) 0 := by
  simpa only [initialMetricOrthonormalCoefficient_eq_literal_inverseGram] using
    hasDerivWithinAt_mappedAffineHeatFlowPath_zero D
      (initialMetricCoordinatePoint (I := I) p b)
      (initialMetricOrthonormalCoordinateEquiv g₀ p b) z

end RicciFlow.AnalyticPDE
