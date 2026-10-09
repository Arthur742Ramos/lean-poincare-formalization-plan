import ChartPort.BoundarylessChartCoverage
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth

noncomputable section
open Bundle FiberBundle Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The actual Mathlib local frame of the actual chart trivialization and upstream basis. -/
abbrev chartLocalFrame (α : M) (i : Fin (Module.finrank ℝ E)) : Π x : M, TangentSpace I x :=
  (trivializationAt E (TangentSpace I : M → Type _) α).localFrame (chartModelBasis E) i

theorem chartLocalFrame_eq_chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet) :
    chartLocalFrame (I := I) α i x = chartBasisVecFiber (I := I) α i x := by
  rw [chartLocalFrame, Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
  simp [Bundle.Trivialization.basisAt, chartBasisVecFiber,
    Bundle.Trivialization.linearEquivAt_symm_apply]

theorem chartLocalFrame_contMDiffOn_baseSet (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% (chartLocalFrame (I := I) α j))
      (trivializationAt E (TangentSpace I : M → Type _) α).baseSet :=
  (trivializationAt E (TangentSpace I : M → Type _) α).contMDiffOn_localFrame_baseSet
    (I := I) (n := (∞ : WithTop ℕ∞)) (chartModelBasis E) j

theorem chartLocalFrame_repr_of_mem (α : M) (j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet) :
    chartE_section_repr (I := I) α (chartLocalFrame (I := I) α j) x = chartModelBasis E j := by
  rw [chartE_section_repr_eq_trivialization_snd (I := I) α _ hx]
  rw [chartLocalFrame_eq_chartBasisVecFiber α j hx]
  exact trivializationAt_chartBasisVec_snd (I := I) α j hx

/-- The pullback coordinates are constant on a genuine open chart-good-set image. -/
theorem eventually_chartLocalFrame_pullback_constant (α : M) (j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartE_section_repr (I := I) α (chartLocalFrame (I := I) α j) ∘ (extChartAt I α).symm)
      =ᶠ[𝓝 (extChartAt I α x)] (fun _ : E => chartModelBasis E j) := by
  have hopen := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have himage : extChartAt I α x ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨x, hx, rfl⟩
  filter_upwards [hopen.mem_nhds himage] with y hy
  rcases hy with ⟨z, hz, rfl⟩
  rw [Function.comp_apply, (extChartAt I α).left_inv
    (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hz)]
  exact chartLocalFrame_repr_of_mem α j (chartLeviCivitaGoodSet_mem_baseSet (I := I) hz)

theorem chartLocalFrame_pullback_fderiv_zero (α : M) (j : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    fderiv ℝ (chartE_section_repr (I := I) α (chartLocalFrame (I := I) α j) ∘
      (extChartAt I α).symm) (extChartAt I α x) = 0 := by
  rw [(eventually_chartLocalFrame_pullback_constant α j hx).fderiv_eq]
  simp

theorem christoffelCorrection_chartLocalFrame (g : RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (α : M) (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet) :
    christoffelCorrection (I := I) g α x (chartModelBasis E j) (chartLocalFrame (I := I) α i x) =
      ∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α i j k (extChartAt I α x) •
        chartModelBasis E k := by
  classical
  rw [christoffelCorrection_apply]
  have hdir : trivToE (I := I) α x (chartLocalFrame (I := I) α i x) = chartModelBasis E i :=
    chartLocalFrame_repr_of_mem α i hx
  rw [hdir]
  simp [Module.Basis.repr_self, Finsupp.single_apply, -chartModelBasis_apply, -chartChristoffel_def]

theorem chartLeviCivita_chartLocalFrame_apply (g : RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (α : M) (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α (chartLocalFrame (I := I) α j) x (chartLocalFrame (I := I) α i x) =
      trivFromE (I := I) α x
        (∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) g α i j k (extChartAt I α x) •
          chartModelBasis E k) := by
  rw [chartLeviCivita_apply (I := I) g α _ hx,
    chartLocalFrame_pullback_fderiv_zero α j hx]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  rw [chartLocalFrame_repr_of_mem α j (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx),
    christoffelCorrection_chartLocalFrame g α i j (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)]

theorem chartLocalFrameCoeff_eq_modelRepr (α : M) (k : Fin (Module.finrank ℝ E))
    {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet) :
    ((trivializationAt E (TangentSpace I : M → Type _) α).localFrameCoeff I (chartModelBasis E) k x) (σ x) =
      (chartModelBasis E).repr (trivToE (I := I) α x (σ x)) k := by
  rw [(trivializationAt E (TangentSpace I : M → Type _) α).localFrameCoeff_eq_coeff
    (I := I) (b := chartModelBasis E) (s := σ) hx]
  rw [← chartE_section_repr_eq_trivialization_snd (I := I) α σ hx]
  rfl

section Chosen
variable [BoundarylessManifold I M]

theorem timeFamilyChosen_chartLocalFrame_apply
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    timeFamilyChosen g t (chartLocalFrame (I := I) α j) x (chartLocalFrame (I := I) α i x) =
      trivFromE (I := I) α x
        (∑ k : Fin (Module.finrank ℝ E), chartChristoffel (I := I) (g t) α i j k (extChartAt I α x) •
          chartModelBasis E k) := by
  have hbase := chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hdiff := ((chartLocalFrame_contMDiffOn_baseSet α j).contMDiffAt
    ((trivializationAt E (TangentSpace I : M → Type _) α).open_baseSet.mem_nhds hbase)).mdifferentiableAt
      (by simp)
  exact (timeFamilyChosen_eq_chartLeviCivita g t α hx hdiff (chartLocalFrame (I := I) α i x)).trans
    (chartLeviCivita_chartLocalFrame_apply (g t) α i j hx)

/-- Actual local-frame coefficient: i is direction, j is section, k is output. -/
def timeFamilyChosenChartCoefficient
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ((trivializationAt E (TangentSpace I : M → Type _) α).localFrameCoeff I (chartModelBasis E) k x)
    (timeFamilyChosen g t (chartLocalFrame (I := I) α j) x (chartLocalFrame (I := I) α i x))

theorem timeFamilyChosenChartCoefficient_eq_chartChristoffel
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    timeFamilyChosenChartCoefficient g t α i j k x =
      chartChristoffel (I := I) (g t) α i j k (extChartAt I α x) := by
  classical
  unfold timeFamilyChosenChartCoefficient
  rw [chartLocalFrameCoeff_eq_modelRepr α k
    (σ := fun y => timeFamilyChosen g t (chartLocalFrame (I := I) α j) y
      (chartLocalFrame (I := I) α i y))
    (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)]
  rw [timeFamilyChosen_chartLocalFrame_apply g t α i j hx,
    trivToE_trivFromE (I := I) α (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)]
  simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finset.sum_apply,
    -chartModelBasis_apply, -chartChristoffel_def]

end Chosen
end ChartPort
