module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatGeometricRegularity
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity

/-!
# Actual tensor Laplacian from a C¹ connection and a local C² tensor

The coordinate identity uses only first differentiability of the induced
connection coefficients.  This module discharges the raw certificates from a
C¹ tangent connection and a tensor that is C² on the open frame patch.  The
first covariant derivative and its scalar readouts are derived internally.
No C² connection, C³ metric, or induced-three regularity oracle is used.

The output index is `(q, p)`, following the existing tensor-frame convention.
This supporting identity does not establish Hölder coefficient estimates or
Ricci-flow local existence.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

open Set Filter Bundle FiberBundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

namespace RicciFlow.AnalyticPDE

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance weakRegularityTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance weakRegularityTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance weakRegularityTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance weakRegularityTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance weakRegularityThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance weakRegularityThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance weakRegularityThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance weakRegularityThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "W" => (ι × ι → ℝ)
local notation "DW" => (E →L[ℝ] W)
local notation "D2W" => (E →L[ℝ] E →L[ℝ] W)

@[reducible] local instance weakCoefficientCoordinateNormedAddCommGroup :
    NormedAddCommGroup W := tensorCoordinateNormedAddCommGroup
@[reducible] local instance weakCoefficientCoordinateNormedSpace :
    NormedSpace ℝ W := tensorCoordinateNormedSpace
@[reducible] local instance weakCoefficientFirstNormedAddCommGroup :
    NormedAddCommGroup DW := tensorCoordinateFirstNormedAddCommGroup
@[reducible] local instance weakCoefficientFirstNormedSpace :
    NormedSpace ℝ DW := tensorCoordinateFirstNormedSpace
@[reducible] local instance weakCoefficientSecondNormedAddCommGroup :
    NormedAddCommGroup D2W := tensorCoordinateSecondNormedAddCommGroup
@[reducible] local instance weakCoefficientSecondNormedSpace :
    NormedSpace ℝ D2W := tensorCoordinateSecondNormedSpace
@[reducible] local instance weakCoefficientPrincipalNormedAddCommGroup :
    NormedAddCommGroup (D2W →L[ℝ] W) :=
  tensorCoordinatePrincipalNormedAddCommGroup
@[reducible] local instance weakCoefficientPrincipalNormedSpace :
    NormedSpace ℝ (D2W →L[ℝ] W) := tensorCoordinatePrincipalNormedSpace
@[reducible] local instance weakCoefficientFirstMapNormedAddCommGroup :
    NormedAddCommGroup (DW →L[ℝ] W) :=
  tensorCoordinateFirstCoefficientNormedAddCommGroup
@[reducible] local instance weakCoefficientFirstMapNormedSpace :
    NormedSpace ℝ (DW →L[ℝ] W) :=
  tensorCoordinateFirstCoefficientNormedSpace
@[reducible] local instance weakCoefficientZeroNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W) :=
  tensorCoordinateZeroNormedAddCommGroup
@[reducible] local instance weakCoefficientZeroNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W) := tensorCoordinateZeroNormedSpace

/-- The fixed-chart matrix of a locally `C²` covariant two-tensor is `C²`
on the overlap of the chart and tensor-frame domains.  This packages the
induced tensor trivialization, so later operator identities do not need
coordinate regularity as a separate hypothesis. -/
theorem contDiffOn_localTensorCoordinates_of_contMDiffOn_two
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hh : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)) e.baseSet) :
    ContDiffOn ℝ 2
      (localTensorCoordinates (I := I) chartCenter e b h)
      ((extChartAt I chartCenter).target ∩
        (extChartAt I chartCenter).symm ⁻¹' e.baseSet) := by
  let e₂ := localTwoTensorTrivialization (I := I) e
  let b₂ := continuousTwoTensorBasis b
  have he₂ : e₂.baseSet = e.baseSet := by
    ext x
    simp [e₂, localTwoTensorTrivialization,
      localCovectorTrivialization, localRealLineTrivialization]
  have hhOn : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)) e₂.baseSet :=
    by simpa only [he₂] using hh
  have hcoeff : ∀ out : ι × ι, ContMDiffOn I 𝓘(ℝ) 2
      (localTwoTensorComponent (I := I) e b h out) e.baseSet := by
    intro out
    have hc := contMDiffOn_baseSet_localFrameCoeff
      (I := I) (e := e₂) (b := b₂) hhOn out
    rw [he₂] at hc
    convert hc using 1 <;> rfl
  rw [contDiffOn_pi]
  intro out
  apply CovariantDerivative.contDiffOn_writtenInExtChartAt_of_contMDiffOn
    (I := I) (p := chartCenter) (hcoeff out)
  · exact Set.inter_subset_left
  intro z hz
  exact hz.2

/-- Automatic actual-Laplacian identity on the open frame patch.  The only
connection-regularity premise is C¹ for the base tangent connection; tensor
regularity is local C².  All coordinate and first-covariant-derivative
certificates are constructed in the proof. -/
theorem connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_baseC1_and_localC2
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative cov 1]
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hh : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)) e.baseSet)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I chartCenter).source)
    (p q : ι) :
    connectionLaplacian cov h y
        (e.localFrame b p y) (e.localFrame b q y) =
      (localTensorHeatPrincipalCoefficient (I := I) chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinateSecondDerivative (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y)) +
        localTensorHeatFirstCoefficient (I := I) cov chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinateDerivative (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y)) +
        localTensorHeatZeroCoefficient (I := I) cov chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinates (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y))) (q, p) := by
  letI : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    contMDiffCovariantDerivative_covariantTwoTensor_one (I := I) cov
  let e₂ := localTwoTensorTrivialization (I := I) e
  let b₂ := continuousTwoTensorBasis b
  let e₃ := localThreeTensorTrivialization (I := I) e
  let b₃ := continuousThreeTensorBasis b
  have he₂ : e₂.baseSet = e.baseSet := by
    ext x
    simp [e₂, localTwoTensorTrivialization,
      localCovectorTrivialization, localRealLineTrivialization]
  have he₃ : e₃.baseSet = e.baseSet := by
    ext x
    simp [e₃, localThreeTensorTrivialization,
      localTwoTensorTrivialization, localCovectorTrivialization,
      localRealLineTrivialization]
  have hregFrame : ∀ z ∈ e.baseSet,
      MDiffAt
        (fun w => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) w (h w)) z := by
    intro z hz
    exact (((hh z hz).contMDiffAt (e.open_baseSet.mem_nhds hz)).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
  have hregChart : ∀ z ∈ e.baseSet, ∀ out : ι × ι,
      MDiffAt (localTwoTensorComponent (I := I) e b h out) z := by
    intro z hz out
    have hz₂ : z ∈ e₂.baseSet := by simpa [he₂] using hz
    have hc := mdifferentiableAt_localFrameCoeff
      (I := I) (e := e₂) (b := b₂) (s := h)
      hz₂ (hregFrame z hz) out
    convert hc using 1 <;> rfl
  have hhOn : ContMDiffOn I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (1 + 1)
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)) e.baseSet := by
    have hone : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
    simpa only [hone] using hh
  have hcovOn :=
    (contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (I := I)
      (cov := covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) e.open_baseSet).contMDiff hhOn
  have hcovFirst : MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) z
        (covariantTwoTensorCovariantDerivative cov h z)) y :=
    ((hcovOn y hyFrame).contMDiffAt
      (e.open_baseSet.mem_nhds hyFrame)).mdifferentiableAt one_ne_zero
  have hlocalFirst : ∀ out : ι × ι, ∀ j : ι,
      MDiffAt (localFirstCovariantComponent (I := I) cov e b h out j) y := by
    intro out j
    have hy₃ : y ∈ e₃.baseSet := by simpa [he₃] using hyFrame
    have hc := mdifferentiableAt_localFrameCoeff
      (I := I) (e := e₃) (b := b₃)
      (s := covariantTwoTensorCovariantDerivative cov h)
      hy₃ hcovFirst (out, j)
    have hevent :
        localThreeTensorComponent (I := I) e b
            (covariantTwoTensorCovariantDerivative cov h) (out, j) =ᶠ[nhds y]
          localFirstCovariantComponent (I := I) cov e b h out j := by
      filter_upwards [e.open_baseSet.mem_nhds hyFrame] with z hz
      exact localThreeTensorComponent_covariantTwoTensorDerivative_eq_first
        (I := I) cov e b hz (hregFrame z hz) out j
    exact hc.congr_of_eventuallyEq hevent.symm
  let s := (extChartAt I chartCenter).target ∩
    (extChartAt I chartCenter).symm ⁻¹' e.baseSet
  let z := (extChartAt I chartCenter) y
  have hz : z ∈ s := by
    refine ⟨(extChartAt I chartCenter).map_source hyChart, ?_⟩
    change (extChartAt I chartCenter).symm
      ((extChartAt I chartCenter) y) ∈ e.baseSet
    rw [(extChartAt I chartCenter).left_inv hyChart]
    exact hyFrame
  have hs : IsOpen s :=
    (continuousOn_extChartAt_symm (I := I) chartCenter).isOpen_inter_preimage
      (isOpen_extChartAt_target chartCenter) e.open_baseSet
  have hsrange : s ⊆ Set.range I :=
    Set.Subset.trans Set.inter_subset_left
      (extChartAt_target_subset_range chartCenter)
  have hU₂ : ContDiffOn ℝ 2
      (localTensorCoordinates (I := I) chartCenter e b h) s := by
    simpa [s] using contDiffOn_localTensorCoordinates_of_contMDiffOn_two
      (I := I) chartCenter e b hh
  have hUAt : ContDiffAt ℝ 2
      (localTensorCoordinates (I := I) chartCenter e b h) z :=
    (hU₂ z hz).contDiffAt (hs.mem_nhds hz)
  have huAt : DifferentiableWithinAt ℝ
      (localTensorCoordinates (I := I) chartCenter e b h)
      (Set.range I) z :=
    (hUAt.differentiableAt (by norm_num)).differentiableWithinAt
  have huNear : ∀ᶠ w in nhdsWithin z (Set.range I), DifferentiableWithinAt ℝ
      (localTensorCoordinates (I := I) chartCenter e b h)
      (Set.range I) w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hs.mem_nhds hz)] with w hw
    exact (((hU₂ w hw).contDiffAt (hs.mem_nhds hw)).differentiableAt
      (by norm_num)).differentiableWithinAt
  have hDU₁ : ContDiffOn ℝ 1
      (localTensorCoordinateDerivative (I := I) chartCenter e b h) s := by
    exact CovariantDerivative.contDiffOn_fderivWithin_range
      (I := I) hs hsrange hU₂
  have hDu : DifferentiableWithinAt ℝ
      (localTensorCoordinateDerivative (I := I) chartCenter e b h)
      (Set.range I) z :=
    (((hDU₁ z hz).contDiffAt (hs.mem_nhds hz)).differentiableAt
      (by norm_num)).differentiableWithinAt
  have hV : ∀ i : ι, DifferentiableWithinAt ℝ
      (localFrameInChart (I := I) chartCenter e b i)
      (Set.range I) z := by
    intro i
    have hV₂ := CovariantDerivative.contDiffOn_localFrameInChart
      (I := I) chartCenter e b i
    exact ((((hV₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) z hz).contDiffAt
      (hs.mem_nhds hz)).differentiableAt (by norm_num)).differentiableWithinAt
  have hgamma₂ : ∀ out input : ι × ι, ∀ j : ι,
      DifferentiableWithinAt ℝ
        (localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j) (Set.range I) z := by
    intro out input j
    have hg := CovariantDerivative.contDiffOn_localTwoTensorConnectionCoefficientInChart_one
      (I := I) cov chartCenter e b out input j
    exact (((hg z hz).contDiffAt
      (hs.mem_nhds hz)).differentiableAt (by norm_num)).differentiableWithinAt
  exact connectionLaplacian_apply_eq_localTensorHeatSecondOrder
    (I := I) cov chartCenter e b hregFrame hregChart hyFrame hyChart
      hcovFirst hlocalFirst huAt huNear hDu hV hgamma₂ p q

end RicciFlow.AnalyticPDE
