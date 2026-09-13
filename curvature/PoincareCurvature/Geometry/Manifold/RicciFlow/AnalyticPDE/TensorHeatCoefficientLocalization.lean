import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalizedInverse
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.CompactCoefficientExtension
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatGeometricRegularity

/-!
# Producing localized tensor-heat coefficient data

This legacy-import bridge combines chart-local `C¹` coefficient fields,
compactly supported extensions, and a normalized cutoff into the exact
quantitative data consumed by `TensorHeatLocalizedInverse`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology ContDiff

namespace RicciFlow
namespace AnalyticPDE

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

@[reducible] local instance coefficientLocalizationFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

namespace TensorHeatLocalizedCoefficientData

/-- Assemble quantitative localization data from a normalized cutoff and
three compactly supported coefficient extensions. -/
def ofExtensions
    (χ : NormalizedCutoffControl X)
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (Aext : CompactCoefficientExtension X _ A₀ K U)
    (Bext : CompactCoefficientExtension X _ B₀ K U)
    (Cext : CompactCoefficientExtension X _ C₀ K U)
    (center : X) : TensorHeatLocalizedCoefficientData X W where
  cutoff := χ.cutoff
  principal := Aext.extension
  first := Bext.extension
  zero := Cext.extension
  center := center
  cutoffBound := 1
  cutoffLipschitz := χ.lipschitzBound
  supportRadius := χ.supportRadius
  principalLipschitz := Aext.lipschitzBound
  firstBound := Bext.bound
  firstLipschitz := Bext.lipschitzBound
  zeroBound := Cext.bound
  zeroLipschitz := Cext.lipschitzBound
  cutoffBound_nonneg := by norm_num
  cutoffLipschitz_nonneg := χ.lipschitzBound_nonneg
  supportRadius_nonneg := χ.supportRadius_nonneg
  principalLipschitz_nonneg := Aext.lipschitzBound_nonneg
  firstBound_nonneg := Bext.bound_nonneg
  firstLipschitz_nonneg := Bext.lipschitzBound_nonneg
  zeroBound_nonneg := Cext.bound_nonneg
  zeroLipschitz_nonneg := Cext.lipschitzBound_nonneg
  norm_cutoff_le := χ.abs_le_one
  cutoff_lipschitz := χ.abs_sub_le
  support_radius := χ.support_norm_le
  principal_lipschitz := Aext.norm_sub_le
  norm_first_le := Bext.norm_le
  first_lipschitz := Bext.norm_sub_le
  norm_zero_le := Cext.norm_le
  zero_lipschitz := Cext.norm_sub_le

/-- Three chart-local `C¹` coefficient fields admit simultaneous compactly
supported quantitative localization on any compact core inside their common
open domain.  The resulting fields agree with the originals near the core,
and the cutoff itself equals one there. -/
theorem exists_of_contDiffOn
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ 1 A₀ U)
    (hB : ContDiffOn ℝ 1 B₀ U)
    (hC : ContDiffOn ℝ 1 C₀ U)
    (center : X) :
    ∃ D : TensorHeatLocalizedCoefficientData X W,
      D.center = center ∧
      (∀ᶠ x in nhdsSet K, D.principal x = A₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.first x = B₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.zero x = C₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.cutoff x = 1) := by
  obtain ⟨χ, _hχsupp, hχone, _hχrange⟩ :=
    exists_normalizedCutoffControl_one_nhdsSet_of_isCompact hK hU hKU
  obtain ⟨Aext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hA
  obtain ⟨Bext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hB
  obtain ⟨Cext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hC
  refine ⟨ofExtensions χ Aext Bext Cext center, ?_⟩
  exact ⟨rfl, Aext.eventuallyEq_original, Bext.eventuallyEq_original,
    Cext.eventuallyEq_original, hχone⟩

/-- Assemble localized coefficient data with the two logically distinct
localizations separated: the coefficient extensions agree with the original
fields near the unscaled compact core `K`, while the normalized cutoff is one
on the closed unit ball in the rescaled variable.  This is the form needed to
identify the localized operator with the genuine chart operator. -/
theorem exists_of_contDiffOn_unitCutoff
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ 1 A₀ U)
    (hB : ContDiffOn ℝ 1 B₀ U)
    (hC : ContDiffOn ℝ 1 C₀ U)
    (center : X) :
    ∃ D : TensorHeatLocalizedCoefficientData X W,
      D.center = center ∧
      (∀ᶠ x in nhdsSet K, D.principal x = A₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.first x = B₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.zero x = C₀ x) ∧
      (∀ x ∈ Metric.closedBall (0 : X) 1, D.cutoff x = 1) := by
  obtain ⟨χ, hχone, _hχsupp⟩ :=
    exists_normalizedCutoffControl_one_on_closedBall (X := X)
  obtain ⟨Aext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hA
  obtain ⟨Bext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hB
  obtain ⟨Cext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hC
  refine ⟨ofExtensions χ Aext Bext Cext center, ?_⟩
  exact ⟨rfl, Aext.eventuallyEq_original, Bext.eventuallyEq_original,
    Cext.eventuallyEq_original, hχone⟩

/-- If the chosen chart center belongs to the compact core, the localized
principal field has exactly the original principal coefficient there. -/
theorem principal_center_eq_of_mem
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    (D : TensorHeatLocalizedCoefficientData X W) {K : Set X}
    (hA : ∀ᶠ x in nhdsSet K, D.principal x = A₀ x)
    (hc : D.center ∈ K) :
    D.principal D.center = A₀ D.center := by
  have hnhds : ∀ᶠ x in nhds D.center, D.principal x = A₀ x :=
    (mem_nhdsSet_iff_forall.mp hA) D.center hc
  exact hnhds.self_of_nhds

end TensorHeatLocalizedCoefficientData

/-! ## Actual connection-Laplacian coefficients -/

open Bundle FiberBundle CovariantDerivative
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

variable {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

/- Select the same model and fiber norms as the geometric regularity theorem,
so its induced-connection class hypotheses refer to definitionally identical
two- and three-covariant-tensor bundles. -/
@[reducible] local instance localizationTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance localizationTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance localizationTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance localizationTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance localizationThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance localizationThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance localizationThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance localizationThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x

/-- End-to-end local solvability for the coefficient fields derived from the
actual connection Laplacian.  The only analytic input is `C¹` regularity of
those three *defined* coefficient fields on the chosen chart domain; no
coordinate operator or differential identity is postulated. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn
    (cov : CovariantDerivative I E TM)
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hxK : (extChartAt I p) x ∈ K)
    (hA : ContDiffOn ℝ 1
      (localTensorHeatPrincipalCoefficient (I := I) p e b) U)
    (hB : ContDiffOn ℝ 1
      (localTensorHeatFirstCoefficient (I := I) cov p e b) U)
    (hC : ContDiffOn ℝ 1
      (localTensorHeatZeroCoefficient (I := I) cov p e b) U)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) x ∧
      (∀ᶠ z in nhdsSet K,
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)) := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ⟩ :=
    TensorHeatLocalizedCoefficientData.exists_of_contDiffOn
      hK hU hKU hA hB hC ((extChartAt I p) x)
  have hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
    have hc := TensorHeatLocalizedCoefficientData.principal_center_eq_of_mem
      D hDA (hDcenter ▸ hxK)
    rw [hDcenter]
    rw [hDcenter] at hc
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hc
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, ?_⟩
  exact exists_radius_localizedTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter

/-- End-to-end local solvability for the actual connection-Laplacian
coefficients, retaining the canonical zero-initial-trace identity supplied by
the localized inverse construction. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_zeroTrace
    (cov : CovariantDerivative I E TM)
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hxK : (extChartAt I p) x ∈ K)
    (hA : ContDiffOn ℝ 1
      (localTensorHeatPrincipalCoefficient (I := I) p e b) U)
    (hB : ContDiffOn ℝ 1
      (localTensorHeatFirstCoefficient (I := I) cov p e b) U)
    (hC : ContDiffOn ℝ 1
      (localTensorHeatZeroCoefficient (I := I) cov p e b) U)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) x ∧
      (∀ᶠ z in nhdsSet K,
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ⟩ :=
    TensorHeatLocalizedCoefficientData.exists_of_contDiffOn
      hK hU hKU hA hB hC ((extChartAt I p) x)
  have hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
    have hc := TensorHeatLocalizedCoefficientData.principal_center_eq_of_mem
      D hDA (hDcenter ▸ hxK)
    rw [hDcenter]
    rw [hDcenter] at hc
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hc
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, ?_⟩
  exact exists_radius_localizedTensorHeatSolutionL_zeroTrace
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter

/-- Local right-invertibility for the coefficient fields of the genuine
connection Laplacian, with all coefficient regularity derived from the
Riemannian metric, the moving frame, and the induced tensor connections.

Unlike `exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn`, this
statement has no hypotheses asserting regularity of the assembled coordinate
operators. -/
theorem exists_radius_actualLocalTensorHeatSolutionL
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)) := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hpTarget : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨hpTarget, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients (I := I) cov p e b
  exact exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn
    (I := I) cov p e b hpFrame (mem_extChartAt_source p)
      (K := K) (U := U) isCompact_singleton
      hU (by simpa [K] using hpU) (by simp [K])
      hA hB hC hT hα hα1

/-- Local right-invertibility for the genuine connection Laplacian together
with the canonical zero-initial-trace identity, with coefficient regularity
derived from the geometric data. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_zeroTrace
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hpTarget : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨hpTarget, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients (I := I) cov p e b
  exact exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_zeroTrace
    (I := I) cov p e b hpFrame (mem_extChartAt_source p)
      (K := K) (U := U) isCompact_singleton
      hU (by simpa [K] using hpU) (by simp [K])
      hA hB hC hT hα hα1

/-- Local solvability for the genuine connection-Laplacian coefficients with
arbitrary initial data represented by a higher-parabolic extension.  Besides
the operator identities, this returns the actual affine solution and its
Schauder bound for every forcing and extension. -/
theorem exists_radius_actualLocalTensorHeatSolution_with_initialTrace
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 ∧
          ∀ (h : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
            (q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)),
            ∃ u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
              FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) u = q ∧
              FiniteParabolicC2AlphaBanach.initialTraceL hT hα u =
                FiniteParabolicC2AlphaBanach.initialTraceL hT hα h ∧
              ‖u‖ ≤ ‖h‖ + ‖Q‖ *
                ‖q - FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) h‖ := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, hsolve⟩ :=
    exists_radius_actualLocalTensorHeatSolutionL_zeroTrace
      (I := I) cov p e hpFrame b hT hα hα1
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨Q, hPQ, htrace⟩ := hsolve r hr hrδ
  refine ⟨Q, hPQ, htrace, ?_⟩
  intro h q
  exact LinearParabolicParametrix.exists_solution_with_trace_of_rightInverse_zeroTrace
    (FiniteParabolicC2AlphaBanach.initialTraceL hT hα)
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL
      (D.principalField hα hα1 r) (D.firstField hα hα1 r)
      (D.zeroField hα hα1 r)) Q hPQ htrace h q

/-- Local solvability for the genuine connection-Laplacian coefficients with
an arbitrary bounded spatial `C^{2,α}` initial datum.  The datum is extended
constantly in time and the zero-trace inverse corrects its equation defect,
so the returned solution has exactly the prescribed canonical trace together
with an explicit affine Schauder estimate. -/
theorem exists_radius_actualLocalTensorHeatSolution_with_spatialInitialData
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 ∧
          ∀ (D₀ : BoundedSpatialC2AlphaData E W₂ α)
            (q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)),
            ∃ u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
              FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) u = q ∧
              FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = D₀.value ∧
              ‖u‖ ≤
                ‖D₀.timeIndependentExtension (t₀ := t₀) (T := T) hα‖ +
                ‖Q‖ *
                  ‖q - FiniteParabolicC2AlphaBanach.coordinateCauchyL
                    (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                    (D.zeroField hα hα1 r)
                    (D₀.timeIndependentExtension
                      (t₀ := t₀) (T := T) hα)‖ := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, hsolve⟩ :=
    exists_radius_actualLocalTensorHeatSolution_with_initialTrace
      (I := I) cov p e hpFrame b hT hα hα1
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨Q, hPQ, htrace, hsolveQ⟩ := hsolve r hr hrδ
  refine ⟨Q, hPQ, htrace, ?_⟩
  intro D₀ q
  obtain ⟨u, hPu, huTrace, huNorm⟩ :=
    hsolveQ (D₀.timeIndependentExtension (t₀ := t₀) (T := T) hα) q
  refine ⟨u, hPu, ?_, huNorm⟩
  rw [huTrace, D₀.initialTraceL_timeIndependentExtension hT hα]

end AnalyticPDE
end RicciFlow
