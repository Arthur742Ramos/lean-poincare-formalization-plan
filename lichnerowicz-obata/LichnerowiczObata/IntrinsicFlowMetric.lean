module

public import LichnerowiczObata.ConstructedRadialMetric
public import LichnerowiczObata.AngularMetricEvolution

/-! # Intrinsic interpretation of coordinate flow variations -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Undoing the output trivialization recovers the actual tangent map from
the derivative of a map written in two fixed charts. -/
theorem symmL_fderiv_chart_map {ψ : M → M} (c₀ c₁ x : M)
    (hin : x ∈ (chartAt H c₀).source) (hout : ψ x ∈ (chartAt H c₁).source)
    (hψ : MDiffAt ψ x) (v : E) :
    (trivializationAt E TM c₁).symmL ℝ (ψ x)
      (fderiv ℝ (((extChartAt I c₁) ∘ ψ) ∘ (extChartAt I c₀).symm)
        (extChartAt I c₀ x) v) =
      mfderiv I I ψ x ((trivializationAt E TM c₀).symmL ℝ x v) := by
  have ho := mdifferentiableAt_extChartAt (I := I) hout
  have hd := fderiv_chart_comp ((extChartAt I c₁) ∘ ψ) c₀ x hin (ho.comp x hψ) v
  have hchain : mvfderiv I ((extChartAt I c₁) ∘ ψ) x
      ((trivializationAt E TM c₀).symmL ℝ x v) =
      mvfderiv I (extChartAt I c₁) (ψ x)
        (mfderiv I I ψ x ((trivializationAt E TM c₀).symmL ℝ x v)) := by
    exact mfderiv_comp_apply x ho hψ _
  have hd' := hd.trans hchain
  have hchart : mvfderiv I (extChartAt I c₁) (ψ x) =
      (trivializationAt E TM c₁).continuousLinearMapAt ℝ (ψ x) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt hout).symm
  rw [hchart] at hd'
  have he := congrArg ((trivializationAt E TM c₁).symmL ℝ (ψ x)) hd'
  simpa only [(trivializationAt E TM c₁).symmL_continuousLinearMapAt hout] using he

omit [FiniteDimensional ℝ E] in
/-- A spatial direction of a jointly differentiable family is the derivative
of its fixed-time slice. -/
theorem fderiv_family_spatial {φ : E × ℝ → E} {p : E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (p, t)) (v : E) :
    fderiv ℝ φ (p, t) (v, 0) = fderiv ℝ (fun y => φ (y, t)) p v := by
  have hi : HasFDerivAt (fun y : E => (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p) using 1 <;> rfl
  have hd := (hφ.hasFDerivAt.comp p hi).fderiv
  exact (congrArg (fun L : E →L[ℝ] E => L v) hd).symm

/-- Coordinate spatial variations of an actual manifold family represent its
intrinsic fixed-time tangent map on the natural open chart domain. -/
theorem symmL_fderiv_chartFlow {η : M × ℝ → M} {S : Set (M × ℝ)}
    (hS : IsOpen S) (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η S)
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hpt : (p, t) ∈ chartFlowDomain (I := I) η S c₀ c₁) (v : E) :
    let x := (extChartAt I c₀).symm p
    (trivializationAt E TM c₁).symmL ℝ (η (x, t))
      (fderiv ℝ (chartFlow (I := I) η c₀ c₁) (p, t) (v, 0)) =
      mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x v) := by
  let x := (extChartAt I c₀).symm p
  have hin : x ∈ (chartAt H c₀).source := by
    simpa only [extChartAt_source] using (extChartAt I c₀).map_target hpt.1.1
  have hp : extChartAt I c₀ x = p := (extChartAt I c₀).right_inv hpt.1.1
  have hD := isOpen_chartFlowDomain (I := I) hS hη.continuousOn c₀ c₁
  have hφ : DifferentiableAt ℝ (chartFlow (I := I) η c₀ c₁) (p, t) :=
    ((contDiffOn_chartFlow_domain (n := 1) hη c₀ c₁).contDiffAt
      (hD.mem_nhds hpt)).differentiableAt (by norm_num)
  have hηx : MDiffAt η (x, t) :=
    ((hη _ hpt.1.2).contMDiffAt (hS.mem_nhds hpt.1.2)).mdifferentiableAt (by norm_num)
  have hs : MDiffAt (fun y => η (y, t)) x :=
    hηx.comp x (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  dsimp only
  rw [fderiv_family_spatial hφ v]
  have he := symmL_fderiv_chart_map c₀ c₁ x hin hpt.2 hs v
  rw [hp] at he
  exact he

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The coordinate metric of spatial variations is their genuine intrinsic
inner product, so it does not depend on the chosen output chart. -/
theorem coordinate_flow_metric_eq_intrinsic {η : M × ℝ → M} {S : Set (M × ℝ)}
    (hS : IsOpen S) (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η S)
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hpt : (p, t) ∈ chartFlowDomain (I := I) η S c₀ c₁) (v w : E) :
    let x := (extChartAt I c₀).symm p
    let φ := chartFlow (I := I) η c₀ c₁
    coordinateMetricBilinear (I := I) c₁ (φ (p, t))
      (fderiv ℝ φ (p, t) (v, 0)) (fderiv ℝ φ (p, t) (w, 0)) =
      inner ℝ (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x v))
        (mfderiv I I (fun y => η (y, t)) x ((trivializationAt E TM c₀).symmL ℝ x w)) := by
  dsimp only
  rw [coordinateMetricBilinear_apply]
  have he : (extChartAt I c₁).symm (chartFlow (I := I) η c₀ c₁ (p, t)) =
      η ((extChartAt I c₀).symm p, t) :=
    (extChartAt I c₁).left_inv (by simpa using hpt.2)
  rw [he, symmL_fderiv_chartFlow hS hη c₀ c₁ hpt v,
    symmL_fderiv_chartFlow hS hη c₀ c₁ hpt w]

end LichnerowiczObata
