import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorNormSq

/-! A local-frame contraction formula for the intrinsic two-tensor energy. -/

@[expose] public noncomputable section

set_option autoImplicit false

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- The intrinsic Hilbert--Schmidt square, contracted in a genuine local
frame with the inverse Riemannian Gram matrix. -/
theorem covariantTwoTensorNormSq_eq_sum_inverseGram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ∀ x : M, T₂ x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    covariantTwoTensorNormSq (I := I) (E := E) h x =
      ∑ i, ∑ j,
        (((show Matrix ι ι ℝ from localFrameGramMatrix (I := I) e b x)⁻¹ :
          Matrix ι ι ℝ) i j) *
          inner ℝ
            (raisedCovariantTwoTensor (I := I) (E := E) h x
              (e.localFrame b i x))
            (raisedCovariantTwoTensor (I := I) (E := E) h x
              (e.localFrame b j x)) := by
  rw [covariantTwoTensorNormSq_eq_trace_gram]
  rw [congrFun (covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
    (I := I) (E := E) (covariantTwoTensorGram (I := I) (E := E) h)) x]
  rw [endomorphismTrace_eq_sum_localFrame
    (I := I) (M := M) (F := E) (V := TM)
    (raisedCovariantTwoTensor (I := I) (E := E)
      (covariantTwoTensorGram (I := I) (E := E) h)) e b hx]
  apply Finset.sum_congr rfl
  intro i _hi
  change e.localFrameCoeff I b i x
      (rieszMap (I := I) x
        (covariantTwoTensorGram (I := I) (E := E) h x
          (e.localFrame b i x))) = _
  rw [localFrameCoeff_rieszMap (I := I) (E := E) e b
    (omega := fun y => covariantTwoTensorGram (I := I) (E := E) h y
      (e.localFrame b i y)) hx i]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [covariantTwoTensorGram_apply]

end CovariantDerivative
