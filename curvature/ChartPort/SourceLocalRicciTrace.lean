import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
Exact local proofs from Arthur742Ramos/lean-poincare-formalization-plan,
commit 5185c1abd500e997414401af3fe6a533dd3a3b47,
curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean.
Original names: RicciFlow.repr_basisAt_eq_localFrameCoeff and
RicciFlow.ricciCurvature_eq_sum_localFrameCoeff. The namespace avoids collisions
if the complete original module is imported later. Exact original source,
ambient context, statements, proofs and source receipts accompany this extraction.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology
namespace ChartPort.SourceLocalRicciTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]


local notation "TM" => (TangentSpace I : M → Type _)

lemma repr_basisAt_eq_localFrameCoeff
    {ι : Type*} (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (V : TM x) (k : ι) :
    ((trivializationAt E TM x0).basisAt b hx).repr V k
      = (trivializationAt E TM x0).localFrameCoeff I b k x V := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have h := (trivializationAt E TM x0).localFrameCoeff_apply_of_mem_baseSet (I := I) b hx
    (Function.update (0 : Π y : M, TM y) x V) k
  simpa using h.symm

lemma ricciCurvature_eq_sum_localFrameCoeff
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [cov.ContMDiffCovariantDerivative 1]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (u w : TM x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      ∑ k, (trivializationAt E TM x0).localFrameCoeff I b k x
        (CovariantDerivative.curvatureTensor (cov := cov) x
          ((trivializationAt E TM x0).localFrame b k x) u w) := by
  classical
  rw [CovariantDerivative.ricciCurvature_apply,
    LinearMap.trace_eq_matrix_trace ℝ ((trivializationAt E TM x0).basisAt b hx), Matrix.trace]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    CovariantDerivative.ricciEndomorphism_apply,
    (trivializationAt E TM x0).localFrame_apply_of_mem_baseSet b hx]
  exact ChartPort.SourceLocalRicciTrace.repr_basisAt_eq_localFrameCoeff b x0 hx _ k

end ChartPort.SourceLocalRicciTrace
