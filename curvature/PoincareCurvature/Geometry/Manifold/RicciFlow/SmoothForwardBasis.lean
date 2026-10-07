module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardRegularity
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Finite-basis characterization of joint chart metric smoothness

The sums use the given basis, including an empty basis. All regularity
statements use the original forward time interval and chart base set.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow.SmoothForward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]

/-- On the chart base set, arbitrary metric coefficients are finite linear
combinations of the coefficients on basis pairs. -/
theorem chartGramComponent_eq_sum_basis (b : Module.Basis ι ℝ E)
    (g : Metric (I := I) (M := M)) (x₀ : M) (u v : E) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartGramComponent g x₀ u v x =
      ∑ i, ∑ j, b.repr u i * (b.repr v j * chartGramComponent g x₀ (b i) (b j) x) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let L := e.symmL ℝ x
  have hL (w : E) : e.symm x w = L w := (e.symmL_apply hx w).symm
  change g.inner x (e.symm x u) (e.symm x v) =
    ∑ i, ∑ j, b.repr u i * (b.repr v j * g.inner x (e.symm x (b i)) (e.symm x (b j)))
  simp_rw [hL]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Checking every pair in any finite basis is equivalent to checking every
fixed model-vector pair on the same forward chart domain. -/
theorem jointlySmoothOn_iff_basis (b : Module.Basis ι ℝ E)
    (g : MetricFamily (I := I) (M := M)) (a terminal : ℝ) :
    JointlySmoothOn g a terminal ↔
      ∀ (x₀ : M) (i j : ι),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M => chartGramComponent (g p.1) x₀ (b i) (b j) p.2)
          (Set.Ico a terminal ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  constructor
  · intro hg x₀ i j
    exact hg x₀ (b i) (b j)
  · intro hg x₀ u v
    classical
    have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => ∑ i, ∑ j,
          b.repr u i * (b.repr v j * chartGramComponent (g p.1) x₀ (b i) (b j) p.2))
        (Set.Ico a terminal ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      apply contMDiffOn_finsetSum
      intro i hi
      apply contMDiffOn_finsetSum
      intro j hj
      exact contMDiffOn_const.mul (contMDiffOn_const.mul (hg x₀ i j))
    exact hs.congr (fun p hp => chartGramComponent_eq_sum_basis b (g p.1) x₀ u v hp.2)

end RicciFlow.SmoothForward
