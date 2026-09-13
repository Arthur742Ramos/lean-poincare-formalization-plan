import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoordinateOperator

/-!
# Geometric regularity of the tensor heat coefficients

This file derives the `C¹` regularity required by the local parabolic
construction from the actual Riemannian inverse metric, moving tangent frame,
and induced connections on covariant two- and three-tensors.  In particular,
the assembled principal, first-order, and zeroth-order coefficient fields are
not independent analytic hypotheses.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

open Set Filter Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance regularityOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance regularityOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance regularityOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance regularityOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance regularityTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  coordinateTwoModelNormedAddCommGroup
@[reducible] local instance regularityTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := coordinateTwoModelNormedSpace
@[reducible] local instance regularityTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance regularityTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := coordinateTwoFiberNormedSpace x
@[reducible] local instance regularityThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  coordinateThreeModelNormedAddCommGroup
@[reducible] local instance regularityThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  coordinateThreeModelNormedSpace
@[reducible] local instance regularityThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance regularityThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := coordinateThreeFiberNormedSpace x

local instance regularityOneTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ T₀
local instance regularityOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ) E TM ℝ T₀
local instance regularityOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ) E TM ℝ T₀
local instance regularityOneContMDiffVectorBundle :
    ContMDiffVectorBundle 3 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance regularityTwoTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance regularityTwoFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance regularityTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance regularityTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 3 (E →L[ℝ] E →L[ℝ] ℝ) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance regularityThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance regularityThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance regularityThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance regularityThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 3 (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiffOn_writtenInExtChartAt_of_contMDiffOn
    {n : WithTop ℕ∞} [IsManifold I n M]
    {f : M → ℝ} {p : M} {u : Set M} {s : Set E}
    (hf : ContMDiffOn I (modelWithCornersSelf ℝ ℝ) n f u)
    (hst : s ⊆ (extChartAt I p).target)
    (hsu : MapsTo (extChartAt I p).symm s u) :
    ContDiffOn ℝ n (writtenInExtChartAt I (modelWithCornersSelf ℝ ℝ) p f) s := by
  rw [← contMDiffOn_iff_contDiffOn]
  have hsymm := (contMDiffOn_extChartAt_symm (I := I) (n := n) p).mono hst
  have hcomp := hf.comp hsymm hsu
  simpa [writtenInExtChartAt] using hcomp

theorem contDiffOn_localFrameInChart
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i : ι) :
    ContDiffOn ℝ 2 (localFrameInChart (I := I) p e b i)
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet) := by
  letI selfTangentNormedAddCommGroup (z : E) :
      NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ E) z) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI selfTangentNormedSpace (z : E) :
      NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ E) z) :=
    inferInstanceAs (NormedSpace ℝ E)
  let s := (extChartAt I p).target
  let t := e.baseSet
  have hV : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) 2
      (T% (e.localFrame b i)) t :=
    e.contMDiffOn_localFrame_baseSet (I := I)
      (n := (2 : WithTop ℕ∞)) b i
  have hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 3
      (extChartAt I p).symm s := contMDiffOn_extChartAt_symm p
  have hf' : ∀ z ∈ s ∩ (extChartAt I p).symm ⁻¹' t,
      (mfderiv[s] (extChartAt I p).symm z).IsInvertible := by
    intro z hz
    have hrange : Set.range I ∈ nhds z :=
      mem_of_superset ((isOpen_extChartAt_target p).mem_nhds hz.1)
        (extChartAt_target_subset_range p)
    have hsnhds : s ∈ nhds z := (isOpen_extChartAt_target p).mem_nhds hz.1
    simpa [mfderivWithin_of_mem_nhds hsnhds,
      mfderivWithin_of_mem_nhds hrange] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := I) hz.1)
  have hpull : ContMDiffOn (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E).tangent 2
      (T% (VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (e.localFrame b i) s))
      (s ∩ (extChartAt I p).symm ⁻¹' t) :=
    hV.mpullbackWithin_vectorField_inter hf hf'
      (isOpen_extChartAt_target p).uniqueMDiffOn (by norm_num)
  have hpair :=
    (contMDiff_tangentBundleModelSpaceHomeomorph
      (I := modelWithCornersSelf ℝ E) (n := (2 : WithTop ℕ∞))).comp_contMDiffOn hpull
  rw [← modelWithCornersSelf_prod, contMDiffOn_iff_contDiffOn] at hpair
  have hpullModel := contDiffOn_snd.comp hpair (fun _ _ => Set.mem_univ _)
  have hpullModel' : ContDiffOn ℝ 2
      (VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (e.localFrame b i) s)
      (s ∩ (extChartAt I p).symm ⁻¹' t) := by
    simpa [Function.comp_def] using hpullModel
  refine hpullModel'.congr fun z hz => ?_
  unfold localFrameInChart VectorField.mpullbackWithin
  have hsnhds : s ∈ nhds z := (isOpen_extChartAt_target p).mem_nhds hz.1
  have hrange : Set.range I ∈ nhds z :=
    mem_of_superset hsnhds (extChartAt_target_subset_range p)
  rw [mfderivWithin_of_mem_nhds hsnhds,
    mfderivWithin_of_mem_nhds hrange]

theorem contDiffOn_localFrameInverseGramMatrixInChart
    [IsContMDiffRiemannianBundle I 2 E TM]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i j : ι) :
    ContDiffOn ℝ 2
      (localFrameInverseGramMatrixInChart (I := I) p e b i j)
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet) := by
  have hmatrix := contMDiffOn_localFrameGramMatrix_inv
    (I := I) (E := E) e b e.open_baseSet (Set.Subset.rfl)
  rw [contMDiffOn_pi_space] at hmatrix
  have hi := hmatrix i
  rw [contMDiffOn_pi_space] at hi
  have hij := hi j
  apply contDiffOn_writtenInExtChartAt_of_contMDiffOn (I := I) (p := p) hij
  · exact Set.inter_subset_left
  intro z hz
  exact hz.2

theorem contDiffOn_fderivWithin_range
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (hs : IsOpen s) (hsrange : s ⊆ Set.range I)
    (hf : ContDiffOn ℝ 2 f s) :
    ContDiffOn ℝ 1 (fun z => fderivWithin ℝ f (Set.range I) z) s := by
  have hderiv : ContDiffOn ℝ 1 (fderiv ℝ f) s :=
    hf.fderiv_of_isOpen hs
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  refine hderiv.congr fun z hz => ?_
  exact fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f)
    (s := Set.range I) (x := z)
    (mem_of_superset (hs.mem_nhds hz) hsrange)

set_option backward.isDefEq.respectTransparency true in
theorem contMDiffOn_localTwoTensorConnectionCoefficient
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 2]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : ι × ι) (i : ι) :
    ContMDiffOn I 𝓘(ℝ) 2
      (localTwoTensorConnectionCoefficient (I := I) cov e b out input i)
      e.baseSet := by
  let e₂ := localTwoTensorTrivialization (I := I) e
  let b₂ := continuousTwoTensorBasis b
  have hframe3 := e₂.contMDiffOn_localFrame_baseSet
    (I := I) (n := (3 : WithTop ℕ∞)) b₂ input
  have hlocal2 :=
    contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
      (I := I)
      (cov := covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) e₂.open_baseSet
  have hcov2 := hlocal2.contMDiff hframe3
  have he₂ : e₂.baseSet = e.baseSet := by
    ext x
    simp [e₂, localTwoTensorTrivialization,
      localCovectorTrivialization, localRealLineTrivialization]
  rw [he₂] at hcov2
  have hframe2 := e.contMDiffOn_localFrame_baseSet (I := I)
    (n := (2 : WithTop ℕ∞)) b i
  have happ := hcov2.clm_bundle_apply hframe2
  have hcoeff := contMDiffOn_localFrameCoeff
    (I := I) (e := e₂) (b := b₂)
    (t := e.baseSet) e.open_baseSet (by
      intro x hx
      simp [e₂, localTwoTensorTrivialization,
        localCovectorTrivialization, localRealLineTrivialization, hx]) happ out
  convert hcoeff using 1 <;> rfl

set_option backward.isDefEq.respectTransparency true in
theorem contMDiffOn_localThreeTensorConnectionCoefficient
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : (ι × ι) × ι) (i : ι) :
    ContMDiffOn I 𝓘(ℝ) 1
      (localThreeTensorConnectionCoefficient (I := I) cov e b out input i)
      e.baseSet := by
  let e₃ := localThreeTensorTrivialization (I := I) e
  let b₃ := continuousThreeTensorBasis b
  have hframe2 := e₃.contMDiffOn_localFrame_baseSet
    (I := I) (n := (2 : WithTop ℕ∞)) b₃ input
  have hlocal3 :=
    contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (I := I)
      (cov := covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) e₃.open_baseSet
  have hcov3 := hlocal3.contMDiff hframe2
  have he₃ : e₃.baseSet = e.baseSet := by
    ext x
    simp [e₃, localThreeTensorTrivialization,
      localTwoTensorTrivialization, localCovectorTrivialization,
      localRealLineTrivialization]
  rw [he₃] at hcov3
  have htangent1 := e.contMDiffOn_localFrame_baseSet (I := I)
    (n := (1 : WithTop ℕ∞)) b i
  have happ := hcov3.clm_bundle_apply htangent1
  have hcoeff := contMDiffOn_localFrameCoeff
    (I := I) (e := e₃) (b := b₃)
    (t := e.baseSet) e.open_baseSet (by
      intro x hx
      simp [e₃, localThreeTensorTrivialization,
        localTwoTensorTrivialization, localCovectorTrivialization,
        localRealLineTrivialization, hx]) happ out
  convert hcoeff using 1 <;> rfl

set_option backward.isDefEq.respectTransparency true

theorem contDiffOn_localTwoTensorConnectionCoefficientInChart
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 2]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : ι × ι) (i : ι) :
    ContDiffOn ℝ 2
      (localTwoTensorConnectionCoefficientInChart (I := I)
        cov p e b out input i)
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet) := by
  apply contDiffOn_writtenInExtChartAt_of_contMDiffOn (I := I) (p := p)
    (contMDiffOn_localTwoTensorConnectionCoefficient (I := I) cov e b out input i)
  · exact Set.inter_subset_left
  intro z hz
  exact hz.2

theorem contDiffOn_localThreeTensorConnectionCoefficientInChart
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : (ι × ι) × ι) (i : ι) :
    ContDiffOn ℝ 1
      (localThreeTensorConnectionCoefficientInChart (I := I)
        cov p e b out input i)
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet) := by
  apply contDiffOn_writtenInExtChartAt_of_contMDiffOn (I := I) (p := p)
    (contMDiffOn_localThreeTensorConnectionCoefficient (I := I) cov e b out input i)
  · exact Set.inter_subset_left
  intro z hz
  exact hz.2

end CovariantDerivative

namespace RicciFlow.AnalyticPDE

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance actualRegularityTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance actualRegularityTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance actualRegularityTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance actualRegularityTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance actualRegularityThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance actualRegularityThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance actualRegularityThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance actualRegularityThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "W" => (ι × ι → ℝ)
local notation "DW" => (E →L[ℝ] W)
local notation "D2W" => (E →L[ℝ] E →L[ℝ] W)

@[reducible] local instance actualCoefficientCoordinateNormedAddCommGroup :
    NormedAddCommGroup W := tensorCoordinateNormedAddCommGroup
@[reducible] local instance actualCoefficientCoordinateNormedSpace :
    NormedSpace ℝ W := tensorCoordinateNormedSpace
@[reducible] local instance actualCoefficientFirstNormedAddCommGroup :
    NormedAddCommGroup DW := tensorCoordinateFirstNormedAddCommGroup
@[reducible] local instance actualCoefficientFirstNormedSpace :
    NormedSpace ℝ DW := tensorCoordinateFirstNormedSpace
@[reducible] local instance actualCoefficientSecondNormedAddCommGroup :
    NormedAddCommGroup D2W := tensorCoordinateSecondNormedAddCommGroup
@[reducible] local instance actualCoefficientSecondNormedSpace :
    NormedSpace ℝ D2W := tensorCoordinateSecondNormedSpace
@[reducible] local instance actualCoefficientPrincipalNormedAddCommGroup :
    NormedAddCommGroup (D2W →L[ℝ] W) :=
  tensorCoordinatePrincipalNormedAddCommGroup
@[reducible] local instance actualCoefficientPrincipalNormedSpace :
    NormedSpace ℝ (D2W →L[ℝ] W) := tensorCoordinatePrincipalNormedSpace
@[reducible] local instance actualCoefficientFirstMapNormedAddCommGroup :
    NormedAddCommGroup (DW →L[ℝ] W) :=
  tensorCoordinateFirstCoefficientNormedAddCommGroup
@[reducible] local instance actualCoefficientFirstMapNormedSpace :
    NormedSpace ℝ (DW →L[ℝ] W) :=
  tensorCoordinateFirstCoefficientNormedSpace
@[reducible] local instance actualCoefficientZeroNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W) :=
  tensorCoordinateZeroNormedAddCommGroup
@[reducible] local instance actualCoefficientZeroNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W) := tensorCoordinateZeroNormedSpace

theorem contDiffOn_actualTensorHeatCoefficients
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) :
    let s := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
    ContDiffOn ℝ 1
        (localTensorHeatPrincipalCoefficient (I := I) p e b) s ∧
      ContDiffOn ℝ 1
        (localTensorHeatFirstCoefficient (I := I) cov p e b) s ∧
      ContDiffOn ℝ 1
        (localTensorHeatZeroCoefficient (I := I) cov p e b) s := by
  let s := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  have hs : IsOpen s :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hsrange : s ⊆ Set.range I :=
    Set.Subset.trans Set.inter_subset_left (extChartAt_target_subset_range p)
  have hgInv2 : ∀ i j, ContDiffOn ℝ 2
      (localFrameInverseGramMatrixInChart (I := I) p e b i j) s :=
    fun i j => CovariantDerivative.contDiffOn_localFrameInverseGramMatrixInChart (I := I) p e b i j
  have hV2 : ∀ i, ContDiffOn ℝ 2
      (localFrameInChart (I := I) p e b i) s :=
    fun i => CovariantDerivative.contDiffOn_localFrameInChart (I := I) p e b i
  have hDV : ∀ i, ContDiffOn ℝ 1
      (localFrameDerivativeInChart (I := I) p e b i) s := by
    intro i
    change ContDiffOn ℝ 1
      (fun z => fderivWithin ℝ
        (localFrameInChart (I := I) p e b i) (Set.range I) z) s
    exact CovariantDerivative.contDiffOn_fderivWithin_range
      (I := I) hs hsrange (hV2 i)
  have hgamma2_2 : ∀ out input i, ContDiffOn ℝ 2
      (localTwoTensorConnectionCoefficientInChart (I := I)
        cov p e b out input i) s :=
    fun out input i =>
      CovariantDerivative.contDiffOn_localTwoTensorConnectionCoefficientInChart (I := I) cov p e b out input i
  have hgamma3 : ∀ out input i, ContDiffOn ℝ 1
      (localThreeTensorConnectionCoefficientInChart (I := I)
        cov p e b out input i) s :=
    fun out input i =>
      CovariantDerivative.contDiffOn_localThreeTensorConnectionCoefficientInChart (I := I) cov p e b out input i
  have hDgamma2 : ∀ out input i, ContDiffOn ℝ 1
      (localTwoTensorConnectionCoefficientDerivativeInChart (I := I)
        cov p e b out input i) s := by
    intro out input i
    change ContDiffOn ℝ 1
      (fun z => fderivWithin ℝ
        (localTwoTensorConnectionCoefficientInChart (I := I)
          cov p e b out input i) (Set.range I) z) s
    exact CovariantDerivative.contDiffOn_fderivWithin_range
      (I := I) hs hsrange (hgamma2_2 out input i)
  have hgInv1 : ∀ i j, ContDiffOn ℝ 1
      (localFrameInverseGramMatrixInChart (I := I) p e b i j) s :=
    fun i j => (hgInv2 i j).of_le (by norm_num)
  have hV1 : ∀ i, ContDiffOn ℝ 1
      (localFrameInChart (I := I) p e b i) s :=
    fun i => (hV2 i).of_le (by norm_num)
  have hgamma2_1 : ∀ out input i, ContDiffOn ℝ 1
      (localTwoTensorConnectionCoefficientInChart (I := I)
        cov p e b out input i) s :=
    fun out input i => (hgamma2_2 out input i).of_le (by norm_num)
  exact ⟨
    contDiffOn_localTensorHeatPrincipalCoefficient
      (I := I) p e b hgInv1 hV1,
    contDiffOn_localTensorHeatFirstCoefficient
      (I := I) cov p e b hgInv1 hV1 hDV hgamma2_1 hgamma3,
    contDiffOn_localTensorHeatZeroCoefficient
      (I := I) cov p e b hgInv1 hV1 hgamma2_1 hDgamma2 hgamma3⟩

end RicciFlow.AnalyticPDE
