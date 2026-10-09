import ChartPort.ChosenChartConnectionCoefficients
import ChartPort.ChosenBundledCurvatureChartBridge
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs

noncomputable section
open Bundle FiberBundle Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem chartLocalFrame_contMDiffOn_goodSet (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (chartLocalFrame (I := I) α j))
      (chartLeviCivitaGoodSet (I := I) α) :=
  (chartLocalFrame_contMDiffOn_baseSet α j).mono (fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx)

theorem chartLocalFrame_mlieBracket_zero (α : M) (a b : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    VectorField.mlieBracket I (chartLocalFrame (I := I) α a) (chartLocalFrame (I := I) α b) x = 0 := by
  have hopen := chartLeviCivitaGoodSet_isOpen (I := I) α
  have ha := ((chartLocalFrame_contMDiffOn_goodSet α a).contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt (by simp)
  have hb := ((chartLocalFrame_contMDiffOn_goodSet α b).contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt (by simp)
  rw [mlieBracket_eq_chart_fderiv_diff_general (I := I) α x _ _
    (chartLeviCivitaGoodSet_mem_extChartAt_source hx) (chartLeviCivitaGoodSet_mem_baseSet hx)
    (chartLeviCivitaGoodSet_extChartAt_mem_interior hx) ha hb,
    chartLocalFrame_pullback_fderiv_zero α b hx, chartLocalFrame_pullback_fderiv_zero α a hx]
  simp

theorem christoffelCorrection_frameDirection_component
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (a k : Fin (Module.finrank ℝ E)) (Y : E) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet) :
    (chartModelBasis E).repr (christoffelCorrection (I := I) g α x Y
      (chartLocalFrame (I := I) α a x)) k =
      ∑ j : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α a j k (extChartAt I α x) *
        (chartModelBasis E).repr Y j := by
  classical
  rw [christoffelCorrection_apply]
  have hdir : trivToE (I := I) α x (chartLocalFrame (I := I) α a x) = chartModelBasis E a :=
    chartLocalFrame_repr_of_mem α a hx
  rw [hdir]
  simp [map_sum, map_smul, Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply,
    mul_comm, -chartModelBasis_apply, -chartChristoffel_def]

theorem chartLeviCivita_frameDirection_component
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (a k : Fin (Module.finrank ℝ E)) {σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) (chartLeviCivitaGoodSet (I := I) α)) :
    (chartModelBasis E).repr (trivToE (I := I) α x
      (chartLeviCivita (I := I) g α σ x (chartLocalFrame (I := I) α a x))) k =
      partialDeriv (E := E) a (fun y : E => (chartModelBasis E).repr
        ((chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm) y) k) (extChartAt I α x) +
      ∑ j : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α a j k (extChartAt I α x) *
        (chartModelBasis E).repr (chartE_section_repr (I := I) α σ x) j := by
  have hbase := chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hdir : trivToE (I := I) α x (chartLocalFrame (I := I) α a x) = chartModelBasis E a :=
    chartLocalFrame_repr_of_mem α a hbase
  have hpull := (chartE_pullback_contDiffOn_goodSet (I := I) α hσ).contDiffAt
    ((chartLeviCivitaGoodSet_image_isOpen (I := I) α).mem_nhds (Set.mem_image_of_mem _ hx))
  have hd := hpull.differentiableAt (by simp)
  have hcoord := (((chartModelBasis E).coord k).toContinuousLinearMap.hasFDerivAt).comp
    (extChartAt I α x) hd.hasFDerivAt
  have hderiv : (chartModelBasis E).repr
      (fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) (chartModelBasis E a)) k =
      partialDeriv (E := E) a (fun y : E => (chartModelBasis E).repr
        ((chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm) y) k) (extChartAt I α x) := by
    unfold partialDeriv
    have hfun :
        (((chartModelBasis E).coord k).toContinuousLinearMap ∘
          (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)) =
        (fun y : E => (chartModelBasis E).repr
          ((chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm) y) k) := by
      funext y
      exact Module.Basis.coord_apply _ _ _
    rw [← hfun, hcoord.fderiv]
    exact (Module.Basis.coord_apply _ _ _).symm
  rw [chartLeviCivita_apply (I := I) g α σ hx,
    trivToE_trivFromE (I := I) α hbase, hdir, map_add]
  simp only [Finsupp.add_apply]
  rw [hderiv, christoffelCorrection_frameDirection_component g α a k _ hbase]

theorem chartLeviCivita_frame_repr_component
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartModelBasis E).repr (chartE_section_repr (I := I) α
      (fun y => chartLeviCivita (I := I) g α (chartLocalFrame (I := I) α c) y
        (chartLocalFrame (I := I) α b y)) x) k =
      chartChristoffel (I := I) g α b c k (extChartAt I α x) := by
  classical
  change (chartModelBasis E).repr (trivToE (I := I) α x
    (chartLeviCivita (I := I) g α (chartLocalFrame (I := I) α c) x
      (chartLocalFrame (I := I) α b x))) k = _
  rw [chartLeviCivita_chartLocalFrame_apply g α b c hx,
    trivToE_trivFromE (I := I) α (chartLeviCivitaGoodSet_mem_baseSet hx)]
  simp [map_sum, map_smul, Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply,
    -chartModelBasis_apply, -chartChristoffel_def]

theorem eventually_chartLeviCivita_frame_pullback_component
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E => (chartModelBasis E).repr
      ((chartE_section_repr (I := I) α
        (fun z => chartLeviCivita (I := I) g α (chartLocalFrame (I := I) α c) z
          (chartLocalFrame (I := I) α b z)) ∘ (extChartAt I α).symm) y) k)
      =ᶠ[𝓝 (extChartAt I α x)] chartChristoffel (I := I) g α b c k := by
  filter_upwards [(chartLeviCivitaGoodSet_image_isOpen (I := I) α).mem_nhds
    (Set.mem_image_of_mem _ hx)] with y hy
  rcases hy with ⟨z, hz, rfl⟩
  rw [Function.comp_apply, (extChartAt I α).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source hz)]
  exact chartLeviCivita_frame_repr_component g α b c k hz

theorem chartLeviCivita_frame_pullback_partialDeriv
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (a b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    partialDeriv (E := E) a (fun y : E => (chartModelBasis E).repr
      ((chartE_section_repr (I := I) α
        (fun z => chartLeviCivita (I := I) g α (chartLocalFrame (I := I) α c) z
          (chartLocalFrame (I := I) α b z)) ∘ (extChartAt I α).symm) y) k)
        (extChartAt I α x) =
      partialDeriv (E := E) a (chartChristoffel (I := I) g α b c k) (extChartAt I α x) := by
  unfold partialDeriv
  rw [(eventually_chartLeviCivita_frame_pullback_component g α b c k hx).fderiv_eq]

section Chosen
variable [BoundarylessManifold I M]

theorem chartAlong_nested_frame_component
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (a b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartModelBasis E).repr (trivToE (I := I) α x
      (chartAlong g α (chartLocalFrame (I := I) α a)
        (chartAlong g α (chartLocalFrame (I := I) α b) (chartLocalFrame (I := I) α c)) x)) k =
      partialDeriv (E := E) a (chartChristoffel (I := I) g α b c k) (extChartAt I α x) +
      ∑ m : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α a m k (extChartAt I α x) *
        chartChristoffel (I := I) g α b c m (extChartAt I α x) := by
  have hinner := chartAlong_contMDiffOn_goodSet g α
    (chartLocalFrame_contMDiffOn_goodSet α b) (chartLocalFrame_contMDiffOn_goodSet α c)
  change (chartModelBasis E).repr (trivToE (I := I) α x
    (chartLeviCivita (I := I) g α _ x (chartLocalFrame (I := I) α a x))) k = _
  rw [chartLeviCivita_frameDirection_component g α a k hx hinner]
  unfold chartAlong
  rw [chartLeviCivita_frame_pullback_partialDeriv g α a b c k hx]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [chartLeviCivita_frame_repr_component g α b c m hx]

theorem chartCurvatureCommutator_frame_component_eq_chartRiemannTensor
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M)
    (a b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartModelBasis E).repr (trivToE (I := I) α x
      (chartCurvatureCommutator g α (chartLocalFrame (I := I) α a)
        (chartLocalFrame (I := I) α b) (chartLocalFrame (I := I) α c) x)) k =
      chartRiemannTensor (I := I) g α c a b k (extChartAt I α x) := by
  classical
  have hbracket := chartLocalFrame_mlieBracket_zero α a b hx
  have hzero : chartAlong g α
      (VectorField.mlieBracket I (chartLocalFrame (I := I) α a) (chartLocalFrame (I := I) α b))
      (chartLocalFrame (I := I) α c) x = 0 := by
    change chartLeviCivita (I := I) g α _ x _ = 0
    rw [hbracket, map_zero]
  unfold chartCurvatureCommutator
  rw [Pi.sub_apply, Pi.sub_apply, hzero, sub_zero, map_sub, map_sub]
  simp only [Finsupp.sub_apply]
  rw [chartAlong_nested_frame_component g α a b c k hx,
    chartAlong_nested_frame_component g α b a c k hx]
  have hbc : chartChristoffel (I := I) g α b c k = chartChristoffel (I := I) g α c b k :=
    funext (fun y => chartChristoffel_symm (I := I) g α b c k y)
  have hac : chartChristoffel (I := I) g α a c k = chartChristoffel (I := I) g α c a k :=
    funext (fun y => chartChristoffel_symm (I := I) g α a c k y)
  rw [hbc, hac, chartRiemannTensor_def]
  have hsum :
      (∑ m : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α a m k (extChartAt I α x) *
        chartChristoffel (I := I) g α b c m (extChartAt I α x)) -
      (∑ m : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α b m k (extChartAt I α x) *
        chartChristoffel (I := I) g α a c m (extChartAt I α x)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α a m k (extChartAt I α x) *
          chartChristoffel (I := I) g α c b m (extChartAt I α x) -
        chartChristoffel (I := I) g α b m k (extChartAt I α x) *
          chartChristoffel (I := I) g α c a m (extChartAt I α x)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [chartChristoffel_symm (I := I) g α b c m,
      chartChristoffel_symm (I := I) g α a c m]
  linear_combination hsum

/-- Actual output coefficient of the actual bundled curvature on three chart-frame arguments. -/
def timeFamilyChosenChartCurvatureComponent
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (a b c k : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  ((trivializationAt E (TangentSpace I : M → Type _) α).localFrameCoeff I (chartModelBasis E) k x)
    (CovariantDerivative.curvatureTensor (cov := timeFamilyChosen g t) x
      (chartLocalFrame (I := I) α a x) (chartLocalFrame (I := I) α b x) (chartLocalFrame (I := I) α c x))

theorem timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (a b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    timeFamilyChosenChartCurvatureComponent g t α a b c k x =
      chartRiemannTensor (I := I) (g t) α c a b k (extChartAt I α x) := by
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  unfold timeFamilyChosenChartCurvatureComponent
  rw [timeFamilyChosen_curvatureTensor_eq_chartCommutator g t α hx
    (chartLocalFrame_contMDiffOn_goodSet α a) (chartLocalFrame_contMDiffOn_goodSet α b)
    (chartLocalFrame_contMDiffOn_goodSet α c)]
  rw [chartLocalFrameCoeff_eq_modelRepr α k
    (σ := chartCurvatureCommutator (g t) α (chartLocalFrame (I := I) α a)
      (chartLocalFrame (I := I) α b) (chartLocalFrame (I := I) α c))
    (chartLeviCivitaGoodSet_mem_baseSet hx)]
  exact chartCurvatureCommutator_frame_component_eq_chartRiemannTensor (g t) α a b c k hx

end Chosen
end ChartPort
