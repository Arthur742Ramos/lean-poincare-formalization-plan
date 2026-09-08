module

public import AlmostSchur.MetricConnectionCoordinates
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Metric differentiation on arbitrary coordinate vectors -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A fixed coordinate vector gives a smooth local tangent section. -/
theorem contMDiffAt_coordinateConstant (c x : M) (hx : x ∈ (chartAt H c).source) (u : E) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, (trivializationAt E TM c).symmL ℝ y u⟩ : TangentBundle I M)) x := by
  let e := trivializationAt E TM c
  have hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, e.symmL ℝ y u⟩ : TangentBundle I M)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff]
    apply (contMDiffOn_const (c := u)).congr
    intro y hy
    simp only [e.symmL_apply hy, e.mk_symm hy]
    exact congrArg Prod.snd (e.apply_symm_apply' (x := u) hy)
  exact hs.contMDiffAt (e.open_baseSet.mem_nhds hx)

/-- Coordinate metric differentiation for arbitrary vectors is forced by
the genuine connection's metric compatibility. -/
theorem fderiv_coordinateMetric_pairing (cov : CovariantDerivative I E TM)
    (hcov : tangentMetricCompatible cov) (c x : M) (hx : x ∈ (chartAt H c).source)
    (d u w : E) :
    let e := trivializationAt E TM c
    fderiv ℝ ((fun y => inner ℝ (e.symmL ℝ y u) (e.symmL ℝ y w)) ∘
      (extChartAt I c).symm) (extChartAt I c x) d =
      inner ℝ (cov (fun y => e.symmL ℝ y u) x (e.symmL ℝ x d)) (e.symmL ℝ x w) +
        inner ℝ (e.symmL ℝ x u) (cov (fun y => e.symmL ℝ y w) x (e.symmL ℝ x d)) := by
  let e := trivializationAt E TM c
  have hu := (contMDiffAt_coordinateConstant (I := I) c x hx u).mdifferentiableAt (by norm_num)
  have hw := (contMDiffAt_coordinateConstant (I := I) c x hx w).mdifferentiableAt (by norm_num)
  have hd := fderiv_chart_comp
    (fun y => inner ℝ (e.symmL ℝ y u) (e.symmL ℝ y w)) c x hx
    (MDifferentiableAt.inner_bundle (F := E) (E := TM) hu hw) d
  exact hd.trans (CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hcov
    (fun y => e.symmL ℝ y d) hu hw)

end LichnerowiczObata
