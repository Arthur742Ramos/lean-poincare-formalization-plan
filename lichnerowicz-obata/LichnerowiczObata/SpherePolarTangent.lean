module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import LichnerowiczObata.PolarMetricNondegeneracy

/-! # Manifold angular tangents in the polar derivative -/

@[expose] public noncomputable section
open scoped Manifold
namespace LichnerowiczObata

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]

/-- The differential of sphere inclusion supplies intrinsic angular
tangent vectors; the radial component is left unchanged. -/
def spherePolarTangentInclusion (u : Metric.sphere (0 : P) 1) :
    TangentSpace (𝓡 n) u × ℝ →L[ℝ] P × ℝ :=
  (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

theorem spherePolarTangentInclusion_orthogonal (u : Metric.sphere (0 : P) 1)
    (v : TangentSpace (𝓡 n) u × ℝ) :
    inner ℝ (u : P) (spherePolarTangentInclusion u v).1 = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) u]
  exact ⟨v.1, rfl⟩

theorem spherePolarTangentInclusion_injective (u : Metric.sphere (0 : P) 1) :
    Function.Injective (spherePolarTangentInclusion (n := n) u) := by
  intro x y hxy
  have hf := congrArg Prod.fst hxy
  have hs := congrArg Prod.snd hxy
  apply Prod.ext
  · exact injective_mvfderiv_subtypeVal_sphere u hf
  · exact hs

/-- Polar injectivity on the orthogonal angular hyperplane becomes genuine
injectivity on the sphere manifold tangent and radial parameter space. -/
theorem polar_derivative_sphere_tangent_injective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : Metric.sphere (0 : P) 1) (D : P × ℝ →L[ℝ] V)
    (hD : Set.InjOn D {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    Function.Injective (D.comp (spherePolarTangentInclusion (n := n) u)) := by
  intro x y hxy
  apply spherePolarTangentInclusion_injective u
  exact hD (spherePolarTangentInclusion_orthogonal u x)
    (spherePolarTangentInclusion_orthogonal u y) hxy

section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Joint ambient differentiability restricts to the actual angular sphere
and radial manifold, with its standard sphere charts. -/
theorem mdifferentiableAt_sphere_polar_restriction {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r)) :
    MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P)
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P)
      (fun q : Metric.sphere (0 : P) 1 × ℝ => (q.1 : P)) (u, r) :=
    hc.comp (f := Prod.fst) (g := Subtype.val) (u, r) mdifferentiableAt_fst
  have hi : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P × ℝ)
      (fun q : Metric.sphere (0 : P) 1 × ℝ => ((q.1 : P), q.2)) (u, r) :=
    hf.prodMk_space mdifferentiableAt_snd
  exact hΦ.comp (u, r) hi

end Restriction
end LichnerowiczObata
