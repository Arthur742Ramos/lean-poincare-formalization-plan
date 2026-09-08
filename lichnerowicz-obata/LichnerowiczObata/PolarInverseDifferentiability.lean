module

public import LichnerowiczObata.OpenRegionHomeomorph
public import LichnerowiczObata.SpherePolarTangent

/-! # Differentiable inverses on the regular polar cylinder -/

@[expose] public noncomputable section
open TopologicalSpace
open scoped Manifold Topology
namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]

/-- A single partial homeomorphism for the full regular polar cylinder has
a differentiable inverse everywhere there. The derivative assumptions refer
to the specified ambient parameter map, not to an independently chosen map. -/
theorem exists_differentiable_polar_inverse
    (J : Opens ℝ) (U : Opens M)
    (Q : Metric.sphere (0 : P) 1 × J ≃ₜ U)
    (q₀ : Metric.sphere (0 : P) 1 × J) (Φ : P × ℝ → M)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1)
    (hjet : ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
      MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r) ∧
      Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
        {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : P) 1 × ℝ) M,
      e.source = {q | q.2 ∈ J} ∧ e.target = U ∧
      (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
      ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ J,
        MDifferentiableAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm (Φ ((u : P), r)) := by
  obtain ⟨e, hsource, htarget, hforward⟩ := exists_polar_region_partialHomeomorph
    (Metric.sphere (0 : P) 1) J U Q q₀
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) hQ
  refine ⟨e, hsource, htarget, hforward, ?_⟩
  intro u r hr
  have hx : (u, r) ∈ e.source := by rw [hsource]; exact hr
  have he := hforward (u, r) hx
  obtain ⟨D, hD, hd⟩ := exists_sphere_polar_derivative_equiv u r hDim
    (hjet u r hr).1 (hjet u r hr).2
  apply mdifferentiableAt_local_inverse_of_equiv
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) e.symm (u, r) D hd
  · rw [← he]
    exact e.symm.continuousAt (e.map_source hx)
  · rw [← he]
    exact e.left_inv hx
  · have ht : Φ ((u : P), r) ∈ e.target := by rw [← he]; exact e.map_source hx
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact (hforward (e.symm y) (e.map_target hy)).symm.trans (e.right_inv hy)

end LichnerowiczObata
