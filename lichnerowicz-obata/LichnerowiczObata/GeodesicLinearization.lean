module

public import LichnerowiczObata.SmoothConnectionCoordinates
public import LichnerowiczObata.FlowVariationEquation

/-! # The geodesic equation at zero velocity -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology BigOperators

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The geodesic acceleration is quadratic in velocity, so its first
derivative vanishes at zero velocity, including position perturbations. -/
theorem hasFDerivAt_coordinateGeodesicSpray_zero
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) :
    HasFDerivAt (coordinateGeodesicSpray cov b c)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (z, 0) := by
  classical
  let Γ := fun y => frameConnectionCoefficients cov (trivializationAt E TM c)
    b ((extChartAt I c).symm y)
  have hΓ (i j : ι) : DifferentiableAt ℝ (fun q : E × E => Γ q.1 (b i) (b j)) (z, 0) := by
    have hg : DifferentiableAt ℝ (fun y => Γ y (b i) (b j)) z :=
      ((contDiffOn_coordinateConnection_basis 1 cov hm ht b c i j).contDiffAt
        ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt (by norm_num)
    exact DifferentiableAt.comp (𝕜 := ℝ) (f := fun q : E × E => q.1)
      (g := fun y : E => Γ y (b i) (b j)) (z, (0 : E)) hg differentiableAt_fst
  have hi (i : ι) : DifferentiableAt ℝ (fun q : E × E => b.repr q.2 i) (z, 0) :=
    (b.coord i).toContinuousLinearMap.differentiableAt.comp (z, (0 : E)) differentiableAt_snd
  have hterm (i j : ι) : HasFDerivAt (fun q : E × E =>
      (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j)) (0 : E × E →L[ℝ] E) (z, 0) := by
    have hh := ((hi i).hasFDerivAt.mul (hi j).hasFDerivAt).smul (hΓ i j).hasFDerivAt
    convert hh using 1 <;> first | rfl | simp
  have hacc : HasFDerivAt (fun q : E × E => Γ q.1 q.2 q.2) (0 : E × E →L[ℝ] E) (z, 0) := by
    have he : (fun q : E × E => Γ q.1 q.2 q.2) =
        fun q => ∑ i, ∑ j, (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j) := by
      funext q
      exact bilinear_diagonal_basis_expansion b (Γ q.1) q.2
    rw [he]
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm i j))
    simpa using hs
  convert (hasFDerivAt_snd (p := (z, (0 : E)))).prodMk hacc.neg using 1 <;>
    first | rfl | simp

/-- At rest, the geodesic linearization sends a perturbation to its velocity
component and has zero linear acceleration. -/
theorem fderiv_coordinateGeodesicSpray_zero_apply
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) (u v : E) :
    fderiv ℝ (coordinateGeodesicSpray cov b c) (z, 0) (u, v) = (v, 0) := by
  rw [(hasFDerivAt_coordinateGeodesicSpray_zero cov hm ht b c hz).fderiv]
  rfl

/-- Every actual geodesic solution starting at zero velocity is locally
stationary, by uniqueness of the constructed smooth ODE. -/
theorem coordinate_geodesic_at_rest_eventually
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target) {α : ℝ → E × E}
    (hα : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hzero : α 0 = (z, 0)) : α =ᶠ[𝓝 (0 : ℝ)] (fun _ => (z, 0)) := by
  have hD : IsOpen ((extChartAt I c).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target c).prod isOpen_univ
  have hp : (z, (0 : E)) ∈ (extChartAt I c).target ×ˢ (univ : Set E) := ⟨hz, mem_univ _⟩
  have hs := (contDiffOn_coordinateGeodesicSpray 1 cov hm ht b c).contDiffAt (hD.mem_nhds hp)
  obtain ⟨L, V, hV, hLip⟩ := hs.exists_lipschitzOnWith
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), α s ∈ V :=
    hα.self_of_nhds.continuousAt.preimage_mem_nhds (by rwa [hzero])
  have hconst : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun _ : ℝ => (z, (0 : E)))
        (coordinateGeodesicSpray cov b c (z, 0)) s ∧ (z, (0 : E)) ∈ V := by
    apply Filter.Eventually.of_forall
    intro s
    refine ⟨?_, mem_of_mem_nhds hV⟩
    convert hasDerivAt_const s (z, (0 : E)) using 1 <;>
      first | rfl | simp [coordinateGeodesicSpray]
  exact ODE_solution_unique_of_eventually (Filter.Eventually.of_forall (fun _ => hLip))
    (hα.and hmem) hconst hzero

/-- The spatial derivative of an actual smooth geodesic flow obeys the
flat linear system along its stationary zero-velocity solution. -/
theorem hasDerivAt_geodesic_flow_variation_at_rest
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z : E}
    (hz : z ∈ (extChartAt I c).target)
    {α : (E × E) × ℝ → E × E} {U : Set ((E × E) × ℝ)}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U)
    (hode : ∀ q ∈ U, HasDerivAt (fun s => α (q.1, s))
      (coordinateGeodesicSpray cov b c (α q)) q.2)
    {t : ℝ} (hpt : ((z, 0), t) ∈ U) (hrest : α ((z, 0), t) = (z, 0)) (v : E × E) :
    HasDerivAt (fun s => fderiv ℝ α ((z, 0), s) (v, 0))
      ((fderiv ℝ α ((z, 0), t) (v, 0)).2, 0) t := by
  have hv : DifferentiableAt ℝ (coordinateGeodesicSpray cov b c) (α ((z, 0), t)) := by
    rw [hrest]
    exact (hasFDerivAt_coordinateGeodesicSpray_zero cov hm ht b c hz).differentiableAt
  have hd := hasDerivAt_flow_variation hU hα hode hpt hv v
  rw [hrest, fderiv_coordinateGeodesicSpray_zero_apply cov hm ht b c hz] at hd
  exact hd

end LichnerowiczObata
