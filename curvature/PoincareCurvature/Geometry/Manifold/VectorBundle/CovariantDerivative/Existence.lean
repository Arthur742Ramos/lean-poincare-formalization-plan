module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Existence of covariant derivatives

This file constructs local flat covariant derivatives from trivializations, then globalizes them via
a smooth partition of unity. The resulting theorem only gives existence of some affine connection; it
does not yet solve the Levi-Civita correction problem.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

namespace Bundle.Trivialization

section Local

variable [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Module.Basis ι ℝ F)

/-- The flat covariant derivative attached to a local frame coming from a trivialization. -/
def frameCovariantDerivative (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ F) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
  fun σ x ↦
    ∑ i : ι, (extDerivFun ((LinearMap.piApply (e.localFrame_coeff I b i)) σ) x).smulRight
      (e.localFrame b i x)

theorem isCovariantDerivativeOn_frameCovariantDerivative
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) :
    IsCovariantDerivativeOn F (frameCovariantDerivative (I := I) e b) e.baseSet := by
  classical
  refine
    { add := ?_
      leibniz := ?_ }
  · intro σ τ x hσ hτ hx
    have hcoeffσ :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrame_coeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hcoeffτ :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrame_coeff I e b i)) τ) x := by
      intro i
      exact mdifferentiableAt_localFrame_coeff (I := I) (e := e) (b := b) (s := τ) hx hτ i
    calc
      frameCovariantDerivative (I := I) e b (σ + τ) x
          = ∑ i : ι,
              (extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) (σ + τ)) x).smulRight
                (e.localFrame b i x) := rfl
      _ = ∑ i : ι,
            ((extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x).smulRight
                (e.localFrame b i x) +
              (extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) τ) x).smulRight
                (e.localFrame b i x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcoord :
                  extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y + τ y)) x =
                    extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y)) x +
                      extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (τ y)) x := by
                simpa [map_add] using
                  (extDerivFun_add (I := I)
                    (g := fun y ↦ (localFrame_coeff I e b i y) (σ y))
                    (g' := fun y ↦ (localFrame_coeff I e b i y) (τ y)) (hcoeffσ i) (hcoeffτ i))
              calc
                (extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y + τ y)) x).smulRight
                    (e.localFrame b i x)
                    = (extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y)) x +
                        extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (τ y)) x).smulRight
                        (e.localFrame b i x) := by
                          simpa using congrArg (fun A ↦ A.smulRight (e.localFrame b i x)) hcoord
                _ = (extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y)) x).smulRight
                      (e.localFrame b i x) +
                    (extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (τ y)) x).smulRight
                      (e.localFrame b i x) := by
                        ext w
                        simp [ContinuousLinearMap.smulRight_apply, add_smul]
      _ = frameCovariantDerivative (I := I) e b σ x +
            frameCovariantDerivative (I := I) e b τ x := by
              simp [frameCovariantDerivative, Finset.sum_add_distrib]
  · intro σ g x hσ hg hx
    ext v
    have hcoeff :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrame_coeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hprod :
        ∀ i,
          extDerivFun
              ((LinearMap.piApply (localFrame_coeff I e b i)) (g • σ)) x v
            = g x * extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v
                + ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x
                    * extDerivFun g x v := by
      intro i
      have hs :
          ((LinearMap.piApply (localFrame_coeff I e b i)) (g • σ)) =
            fun y ↦ g y * ((LinearMap.piApply (localFrame_coeff I e b i)) σ) y := by
        funext y
        simp [LinearMap.piApply_apply, Pi.smul_apply, map_smul]
      have hi :
          extDerivFun (I := I) (fun y ↦ g y * (localFrame_coeff I e b i y) (σ y)) x =
            g x • extDerivFun (I := I) (fun y ↦ (localFrame_coeff I e b i y) (σ y)) x +
              (localFrame_coeff I e b i x) (σ x) • extDerivFun (I := I) g x := by
        have hmul := (hg.hasMFDerivAt.mul (hcoeff i).hasMFDerivAt).mfderiv
        unfold extDerivFun
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa [hs, ContinuousLinearMap.smulRight_apply, mul_comm, mul_left_comm,
        mul_assoc] using congr(($hi v))
    have hframe :
        ∑ i : ι, ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x • e.localFrame b i x = σ x := by
      simpa [LinearMap.piApply_apply] using (e.eq_sum_localFrame_coeff_smul (I := I) (b := b)
        (s := σ) (x' := x) hx).symm
    have hframeCov :
        ∑ i : ι, extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v •
            e.localFrame b i x =
          frameCovariantDerivative (I := I) e b σ x v := by
      simp [frameCovariantDerivative, ContinuousLinearMap.smulRight_apply]
    calc
      frameCovariantDerivative (I := I) e b (g • σ) x v
          = ∑ i,
              (g x * extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v
                + ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x * extDerivFun g x v) •
                e.localFrame b i x := by
              simp [frameCovariantDerivative]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [ContinuousLinearMap.smulRight_apply] using
                congrArg (fun a ↦ a • e.localFrame b i x) (hprod i)
      _ = ∑ i : ι,
            (g x * extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v) •
              e.localFrame b i x
          + ∑ i : ι,
              (((LinearMap.piApply (localFrame_coeff I e b i)) σ) x * extDerivFun g x v) •
                e.localFrame b i x := by
              simp_rw [add_smul]
              rw [Finset.sum_add_distrib]
      _ = g x • ∑ i : ι,
            extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v •
              e.localFrame b i x
          + extDerivFun g x v • ∑ i : ι,
              ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x • e.localFrame b i x := by
              congr 1
              · calc
                  ∑ i : ι,
                      (g x * extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          g x •
                            (extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g x • ∑ i : ι,
                        extDerivFun ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x v •
                          e.localFrame b i x := by
                            rw [Finset.smul_sum]
              · calc
                  ∑ i : ι,
                      (((LinearMap.piApply (localFrame_coeff I e b i)) σ) x * extDerivFun g x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          extDerivFun g x v •
                            (((LinearMap.piApply (localFrame_coeff I e b i)) σ) x •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [mul_comm, smul_smul]
                  _ = extDerivFun g x v • ∑ i : ι,
                        ((LinearMap.piApply (localFrame_coeff I e b i)) σ) x • e.localFrame b i x := by
                            rw [Finset.smul_sum]
      _ = g x • frameCovariantDerivative (I := I) e b σ x v + extDerivFun g x v • σ x := by
            rw [hframeCov, hframe]

end Local

end Bundle.Trivialization

namespace CovariantDerivative

section Global

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [IsManifold I ∞ M] [ContMDiffVectorBundle 1 F V I]
  [T2Space M] [SigmaCompactSpace M]

/-- Every finite-dimensional smooth real vector bundle over a Hausdorff σ-compact manifold admits a
global covariant derivative. -/
theorem nonempty : Nonempty (CovariantDerivative I F V) := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ F) ℝ F :=
    Module.Basis.ofVectorSpace ℝ F
  obtain ⟨ρ, hρ⟩ :
      ∃ ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M),
        ρ.IsSubordinate (fun x ↦ (trivializationAt F V x).baseSet) :=
    SmoothPartitionOfUnity.exists_isSubordinate (ι := M) (I := I) (M := M)
      (s := (Set.univ : Set M)) isClosed_univ
      (fun x ↦ (trivializationAt F V x).baseSet)
      (fun x ↦ (trivializationAt F V x).open_baseSet)
      (by
        intro x _
        exact Set.mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F V x⟩)
  let cov :
      (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
    fun σ x ↦
      ∑ i ∈ ρ.fintsupport x, ρ i x •
        Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ x
  let s : M → Set M := fun x ↦
    { y | ρ.fintsupport y ⊆ ρ.fintsupport x } ∩
      ⋂ i ∈ ρ.fintsupport x, (trivializationAt F V i).baseSet
  have hscover : ⋃ x, s x = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine Set.mem_iUnion.2 ⟨y, ?_⟩
      refine ⟨show ρ.fintsupport y ⊆ ρ.fintsupport y from subset_rfl, ?_⟩
      refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro hi
      exact hρ i ((ρ.mem_fintsupport_iff (x₀ := y) i).1 hi)
  have hcov : ∀ x, IsCovariantDerivativeOn F cov (s x) := by
    intro x
    refine
      { add := ?_
        leibniz := ?_ }
    · intro σ τ y hσ hτ hy
      have hySub : ρ.fintsupport y ⊆ ρ.fintsupport x := hy.1
      have hyBase :
          ∀ i ∈ ρ.fintsupport x, y ∈ (trivializationAt F V i).baseSet := by
        intro i hi
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 i) hi
      have hsum :
          cov (σ + τ) y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                (σ + τ) y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumσ :
          cov σ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumτ :
          cov τ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b τ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      rw [hsum, hsumσ, hsumτ]
      calc
        ∑ i ∈ ρ.fintsupport x, (ρ i) y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (σ + τ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  σ y +
                (ρ i) y •
                  Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                    τ y) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).add hσ hτ (hyBase i hi), smul_add]
        _ = ∑ i ∈ ρ.fintsupport x, (ρ i) y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + ∑ i ∈ ρ.fintsupport x, (ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  τ y := by
                rw [Finset.sum_add_distrib]
    · intro σ g y hσ hg hy
      have hySub : ρ.fintsupport y ⊆ ρ.fintsupport x := hy.1
      have hyBase :
          ∀ i ∈ ρ.fintsupport x, y ∈ (trivializationAt F V i).baseSet := by
        intro i hi
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 i) hi
      have hsum :
          ∑ i ∈ ρ.fintsupport x, ρ i y = 1 := by
        apply ρ.sum_finsupport'
        trivial
        exact (ρ.finsupport_subset_fintsupport (x₀ := y)).trans hySub
      have hsumσ :
          cov σ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumgσ :
          cov (g • σ) y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                (g • σ) y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      rw [hsumgσ, hsumσ]
      calc
        ∑ i ∈ ρ.fintsupport x, ρ i y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (g • σ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((g y * ρ i y) •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y +
                ρ i y • (extDerivFun g y).smulRight (σ y)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).leibniz hσ hg (hyBase i hi), smul_add, smul_smul]
                rw [mul_comm]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + (∑ i ∈ ρ.fintsupport x, ρ i y) • (extDerivFun g y).smulRight (σ y) := by
              rw [Finset.sum_add_distrib]
              congr 1
              · calc
                  ∑ i ∈ ρ.fintsupport x,
                      (g y * ρ i y) •
                        Bundle.Trivialization.frameCovariantDerivative (I := I)
                          (trivializationAt F V i) b σ y
                    = ∑ i ∈ ρ.fintsupport x,
                        g y •
                          ((ρ i y) •
                            Bundle.Trivialization.frameCovariantDerivative (I := I)
                              (trivializationAt F V i) b σ y) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g y • ∑ i ∈ ρ.fintsupport x,
                        (ρ i y) •
                          Bundle.Trivialization.frameCovariantDerivative (I := I)
                            (trivializationAt F V i) b σ y := by
                              rw [Finset.smul_sum]
              · rw [Finset.sum_smul]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              (trivializationAt F V i).frameCovariantDerivative (I := I) b σ y
            + (extDerivFun g y).smulRight (σ y) := by
              rw [hsum]
              simp
  exact ⟨CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover
    (s := s) (cov := cov) hcov hscover⟩

end Global

end CovariantDerivative
