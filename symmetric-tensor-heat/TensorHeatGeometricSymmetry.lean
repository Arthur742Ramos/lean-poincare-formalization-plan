import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasSymmetricWellPosedness
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasGeometricUniqueness

/-! Transposition of the unprojected geometric heat operator.

This is a step toward symmetry preservation, not a uniqueness theorem.
No symmetrized solution readout occurs in the statement or proof.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.unusedSectionVars false

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]
  {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance geometricSymmetryTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance geometricSymmetryTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance geometricSymmetryThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance geometricSymmetryThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance geometricSymmetryThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance geometricSymmetryThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance geometricSymmetryThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance geometricSymmetryThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance geometricSymmetryThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- The unprojected reconstructed field has a transpose that solves the
transposed tensor heat equation. This uses the actual induced connection
Laplacian on differentiable geometric sections. -/
theorem atlasFieldOfHigher_transpose_tensorHeatOperator
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (v w : TangentSpace I x) :
    (atlasFieldOfHigher cov A (transposeHigherFamily cov A u)).tensorHeatOperator
        cov t ht x v w =
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x w v := by
  let U := atlasFieldOfHigher cov A u
  let Ut := atlasFieldOfHigher cov A (transposeHigherFamily cov A u)
  have ht' : t ∈ Ioc t₀ A.commonTerminalTime := ⟨ht.1, ht.2.le⟩
  have heq : (Ut.slice cov t ht').1 =
      transposeTensorSection (U.slice cov t ht').1 := by
    funext y
    ext a c
    exact atlasFieldOfHigher_transpose_toFun cov A u t ht' y a c
  have hlap := connectionLaplacian_flip_of_mem_domain cov
    (U.slice cov t ht') (Ut.slice cov t ht') heq x v w
  have hlap' : connectionLaplacian cov (Ut.toFun t) x v w =
      connectionLaplacian cov (U.toFun t) x w v := by
    simpa only [FiniteClassicalTensorHeatField.slice] using hlap
  have htime := atlasFieldOfHigher_transpose_timeDerivative cov A u t ht x v w
  change Ut.timeDerivative t x v w - connectionLaplacian cov (Ut.toFun t) x v w =
    U.timeDerivative t x w v - connectionLaplacian cov (U.toFun t) x w v
  rw [htime, hlap']

/-- Transposition preserves the intrinsic tensor heat equation when its source
is symmetric. This is the PDE side of the uniqueness argument; it does not
assert that the atlas coefficient witness is itself unique among different
representations of the same geometric initial tensor. -/
theorem atlasFieldOfHigher_transpose_solves_of_symmetric_source
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (f : ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hf : ∀ t (_ht : t ∈ Ioo t₀ A.commonTerminalTime) x v w,
      f t x w v = f t x v w)
    (hu : ∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x = f t x) :
    ∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
      (atlasFieldOfHigher cov A (transposeHigherFamily cov A u)).tensorHeatOperator
        cov t ht x = f t x := by
  intro t ht x
  ext v w
  rw [atlasFieldOfHigher_transpose_tensorHeatOperator cov A u t ht x v w]
  calc
    (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x w v =
        f t x w v := congrArg (fun L :
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => L w v)
            (hu t ht x)
    _ = f t x v w := hf t ht x v w

/-- The unprojected transpose has the transposed initial trace. In particular,
when the geometric datum is symmetric, both reconstructed fields have the
same trace and solve the same geometric Cauchy problem. -/
theorem atlasFieldOfHigher_transpose_hasInitialTrace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (u₀ : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hu : FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) u₀) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A (transposeHigherFamily cov A u))
      (transposeTensorSection u₀) := by
  intro x
  let flipL : (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →L[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    CovariantDerivative.flipLastTwo (I := I) x
  have hlim : Tendsto
      (fun t : ℝ => flipL ((atlasFieldOfHigher cov A u).toFun t x))
      (nhdsWithin t₀ (Ioc t₀ A.commonTerminalTime))
      (nhds (flipL (u₀ x))) :=
    flipL.continuous.continuousAt.tendsto.comp (hu x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htranspose := atlasFieldOfHigher_transpose_toFun cov A u t ht x
  ext v w
  change ((atlasFieldOfHigher cov A u).toFun t x w v) = _
  simpa [flipL, transposeTensorSection_apply] using
    (htranspose v w).symm

/-- A represented solution of the geometric Cauchy problem is specified by
its *global* initial tensor and source. Unlike `AtlasSpatialClassicalSolution`,
this predicate does not prescribe each local coefficient trace or the strong
atlas equation. Its uniqueness is the missing geometric obligation. -/
def GeometricAtlasCauchySolution
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u₀ : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (f : ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (u : HigherCoefficientSpace cov A) : Prop :=
  FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) u₀ ∧
    ∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x = f t x

/-- A global geometric initial condition determines the tensor reconstructed
from the atlas coefficient traces, even though it need not determine those
coefficient traces individually. This is the exact direction available from
the current reconstruction theorem. -/
theorem geometricAtlasCauchySolution_initialTensor
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u₀ : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (f : ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (u : HigherCoefficientSpace cov A)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u) :
    atlasInitialTrace cov A u = u₀ := by
  funext x
  let _ : NeBot (nhdsWithin t₀ (Ioc t₀ A.commonTerminalTime)) :=
    left_nhdsWithin_Ioc_neBot (A.lt_commonTerminalTime cov)
  exact tendsto_nhds_unique (A.hasInitialTrace_atlasFieldOfHigher cov u x) (hu.1 x)

/-- The represented geometric solution class is closed under slot
transposition when its global Cauchy data are symmetric. -/
theorem geometricAtlasCauchySolution_transpose
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u₀ : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (f : ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (u : HigherCoefficientSpace cov A)
    (hD : ∀ x v w, u₀ x v w = u₀ x w v)
    (hf : ∀ t (_ht : t ∈ Ioo t₀ A.commonTerminalTime) x v w,
      f t x w v = f t x v w)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u) :
    GeometricAtlasCauchySolution cov A u₀ f
      (transposeHigherFamily cov A u) := by
  have hDflip : transposeTensorSection u₀ = u₀ := by
    funext x
    ext v w
    exact hD x w v
  constructor
  · rw [← hDflip]
    exact atlasFieldOfHigher_transpose_hasInitialTrace cov A u u₀ hu.1
  · exact atlasFieldOfHigher_transpose_solves_of_symmetric_source
      cov A u f hf hu.2

/-- Every existing strong atlas solution is a represented solution of the
global geometric Cauchy problem. The converse, needed to transfer coefficient
uniqueness to geometric uniqueness, is not asserted here. -/
theorem atlasSpatialClassicalSolution_geometric
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A)
    (hu : AtlasSpatialClassicalSolution cov Hlift D f u) :
    GeometricAtlasCauchySolution cov A
      (spatialInitialTensor cov A D)
      (fun t x => A.physicalAtlasSourceSlice cov f t x) u :=
  ⟨hu.2.1, hu.2.2⟩

/-- The current atlas construction supplies a solution of the geometric
Cauchy problem for every represented spatial datum and source. This is the
existence half in the global-data class; it does not claim uniqueness there. -/
theorem exists_geometricAtlasCauchySolution
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A) :
    ∃ u : HigherCoefficientSpace cov A,
      GeometricAtlasCauchySolution cov A
        (spatialInitialTensor cov A D)
        (fun t x => A.physicalAtlasSourceSlice cov f t x) u := by
  obtain ⟨u, hu, _⟩ :=
    existsUnique_atlasSpatialClassicalSolution cov hunique Hlift D f
  exact ⟨u, atlasSpatialClassicalSolution_geometric cov Hlift D f u hu⟩

/-- Geometric uniqueness, if established for every represented classical
solution with the same geometric Cauchy data, forces the *ordinary* atlas
reconstruction to be symmetric. The uniqueness hypothesis is deliberately
explicit: coefficient uniqueness with fixed chartwise traces does not supply
it. -/
theorem atlasFieldOfHigher_symmetric_of_geometric_uniqueness
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (u₀ : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (f : ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hD : ∀ x v w, u₀ x v w = u₀ x w v)
    (hf : ∀ t (_ht : t ∈ Ioo t₀ A.commonTerminalTime) x v w,
      f t x w v = f t x v w)
    (htrace : FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) u₀)
    (hu : ∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x = f t x)
    (hunique : ∀ v : HigherCoefficientSpace cov A,
      FiniteClassicalTensorHeatField.HasInitialTrace cov
        (atlasFieldOfHigher cov A v) u₀ →
      (∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
        (atlasFieldOfHigher cov A v).tensorHeatOperator cov t ht x = f t x) →
      ∀ t, t ∈ Ioc t₀ A.commonTerminalTime →
        (atlasFieldOfHigher cov A v).toFun t =
          (atlasFieldOfHigher cov A u).toFun t) :
    ∀ t, t ∈ Ioc t₀ A.commonTerminalTime → ∀ x v w,
      (atlasFieldOfHigher cov A u).toFun t x v w =
        (atlasFieldOfHigher cov A u).toFun t x w v := by
  have hDflip : transposeTensorSection u₀ = u₀ := by
    funext x
    ext v w
    exact hD x w v
  have hflipTrace := atlasFieldOfHigher_transpose_hasInitialTrace
    cov A u u₀ htrace
  rw [hDflip] at hflipTrace
  have hflipPDE := atlasFieldOfHigher_transpose_solves_of_symmetric_source
    cov A u f hf hu
  intro t ht x v w
  have heq := hunique (transposeHigherFamily cov A u)
    hflipTrace hflipPDE t ht
  have heqx := congrArg (fun s => s x v w) heq
  rw [atlasFieldOfHigher_transpose_toFun cov A u t ht x v w] at heqx
  exact heqx.symm

/-! ## Difference of geometric classical solutions -/

/-- The difference of two genuine finite-interval tensor fields retains the
spatial connection-Laplacian domain and temporal derivative. -/
def geometricDifference
    (cov : CovariantDerivative I E TM)
    (U V : FiniteClassicalTensorHeatField cov t₀ T) :
    FiniteClassicalTensorHeatField cov t₀ T where
  toFun t x := U.toFun t x - V.toFun t x
  slice_mem t ht := by
    change (U.toFun t - V.toFun t) ∈ ConnectionLaplacianDomain cov
    exact Submodule.sub_mem (ConnectionLaplacianDomain cov)
      (U.slice_mem t ht) (V.slice_mem t ht)
  timeDerivative t x := U.timeDerivative t x - V.timeDerivative t x
  hasTimeDerivative := by
    intro t ht x a b
    have h := (U.hasTimeDerivative t ht x a b).sub
      (V.hasTimeDerivative t ht x a b)
    have hfun :
        (fun s : ℝ => U.toFun s x a b) -
            (fun s : ℝ => V.toFun s x a b) =
          (fun s : ℝ => U.toFun s x a b - V.toFun s x a b) := by
      funext s
      rfl
    rw [hfun] at h
    simpa only [sub_apply] using h

@[simp] theorem geometricDifference_toFun
    (cov : CovariantDerivative I E TM)
    (U V : FiniteClassicalTensorHeatField cov t₀ T)
    (t : ℝ) (x : M) :
    (geometricDifference cov U V).toFun t x =
      U.toFun t x - V.toFun t x := rfl

/-- The intrinsic connection heat operator is linear on genuine classical
fields; the spatial part uses the linear map on its second-order domain. -/
theorem geometricDifference_tensorHeatOperator
    (cov : CovariantDerivative I E TM)
    (U V : FiniteClassicalTensorHeatField cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioo t₀ T) (x : M) :
    (geometricDifference cov U V).tensorHeatOperator cov t ht x =
      U.tensorHeatOperator cov t ht x -
        V.tensorHeatOperator cov t ht x := by
  have hLap :
      connectionLaplacian cov (U.toFun t - V.toFun t) x =
        connectionLaplacian cov (U.toFun t) x -
          connectionLaplacian cov (V.toFun t) x := by
    have h := (connectionLaplacianLinearMapAt cov x).map_sub
      (U.slice cov t ⟨ht.1, ht.2.le⟩)
      (V.slice cov t ⟨ht.1, ht.2.le⟩)
    simpa only [connectionLaplacianLinearMapAt_apply, Submodule.coe_sub,
      FiniteClassicalTensorHeatField.slice] using h
  change
    (U.timeDerivative t x - V.timeDerivative t x) -
      connectionLaplacian cov (U.toFun t - V.toFun t) x =
    (U.timeDerivative t x - connectionLaplacian cov (U.toFun t) x) -
      (V.timeDerivative t x - connectionLaplacian cov (V.toFun t) x)
  rw [hLap]
  abel

/-- The initial trace of the difference is the difference of the traces. -/
theorem geometricDifference_hasInitialTrace
    (cov : CovariantDerivative I E TM)
    (U V : FiniteClassicalTensorHeatField cov t₀ T)
    (U₀ V₀ : ∀ x : M, T₂ x)
    (hU : FiniteClassicalTensorHeatField.HasInitialTrace cov U U₀)
    (hV : FiniteClassicalTensorHeatField.HasInitialTrace cov V V₀) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (geometricDifference cov U V) (U₀ - V₀) := by
  intro x
  simpa only [geometricDifference_toFun, Pi.sub_apply] using
    (hU x).sub (hV x)

/-- Two classical solutions with the same geometric initial tensor and source
have a genuine homogeneous difference field. This reduces their uniqueness to
the zero-data estimate, which remains to be proved. -/
theorem geometricDifference_zeroData
    (cov : CovariantDerivative I E TM)
    (U V : FiniteClassicalTensorHeatField cov t₀ T)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (hU₀ : FiniteClassicalTensorHeatField.HasInitialTrace cov U u₀)
    (hV₀ : FiniteClassicalTensorHeatField.HasInitialTrace cov V u₀)
    (hU : ∀ t (ht : t ∈ Ioo t₀ T) x,
      U.tensorHeatOperator cov t ht x = f t x)
    (hV : ∀ t (ht : t ∈ Ioo t₀ T) x,
      V.tensorHeatOperator cov t ht x = f t x) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
        (geometricDifference cov U V) 0 ∧
      ∀ t (ht : t ∈ Ioo t₀ T) x,
        (geometricDifference cov U V).tensorHeatOperator cov t ht x = 0 := by
  constructor
  · simpa using geometricDifference_hasInitialTrace cov U V u₀ u₀ hU₀ hV₀
  · intro t ht x
    rw [geometricDifference_tensorHeatOperator cov U V t ht x,
      hU t ht x, hV t ht x, sub_self]

/-! ## Linearity of represented reconstruction -/

private theorem higherValue_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u v : FiniteParabolicC2AlphaBanach E V t₀ T α)
    (z : ℝ × E) :
    FiniteParabolicC2AlphaBanach.value (u - v) z =
      FiniteParabolicC2AlphaBanach.value u z -
        FiniteParabolicC2AlphaBanach.value v z := by
  rw [sub_eq_add_neg, FiniteParabolicC2AlphaBanach.value_add]
  have hneg : FiniteParabolicC2AlphaBanach.value (-v) z =
      -FiniteParabolicC2AlphaBanach.value v z := by
    have hv : -v = (-1 : ℝ) • v := (neg_one_smul ℝ v).symm
    rw [hv, FiniteParabolicC2AlphaBanach.value_smul, neg_one_smul]
  rw [hneg, sub_eq_add_neg]

/-- The ordinary local tensor reconstruction is linear in its higher jet.
This holds for the actual field, without projecting onto symmetric tensors. -/
theorem localFieldOfHigher_toFun_sub
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (i : A.cover.Index)
    (u v : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (t : ℝ) (x : M) :
    (localFieldOfHigher cov A i (u - v)).toFun t x =
      (localFieldOfHigher cov A i u).toFun t x -
        (localFieldOfHigher cov A i v).toFun t x := by
  let s := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let ξ := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let S := cutoffLocalTensorSynthesisAt (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i) x
  have hnorm : normalizedHigherSolution (u - v) =
      normalizedHigherSolution u - normalizedHigherSolution v := by
    simp [normalizedHigherSolution]
  change S (FiniteParabolicC2AlphaBanach.value
      (normalizedHigherSolution (u - v)) (s, ξ)) =
    S (FiniteParabolicC2AlphaBanach.value (normalizedHigherSolution u) (s, ξ)) -
      S (FiniteParabolicC2AlphaBanach.value (normalizedHigherSolution v) (s, ξ))
  rw [hnorm]
  rw [higherValue_sub, map_sub]

/-- The unprojected atlas reconstruction respects subtraction. -/
theorem atlasFieldOfHigher_toFun_sub
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u v : HigherCoefficientSpace cov A) (t : ℝ) (x : M) :
    (atlasFieldOfHigher cov A (u - v)).toFun t x =
      (atlasFieldOfHigher cov A u).toFun t x -
        (atlasFieldOfHigher cov A v).toFun t x := by
  simp only [atlasFieldOfHigher_toFun, Pi.sub_apply,
    localFieldOfHigher_toFun_sub, Finset.sum_sub_distrib]

/-- The stored temporal derivative of the ordinary atlas reconstruction is
linear on the open time interval. The proof uses uniqueness of genuine time
derivatives, so no extra formula for the totalized values outside the interval
is needed. -/
theorem atlasFieldOfHigher_timeDerivative_sub
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u v : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) :
    (atlasFieldOfHigher cov A (u - v)).timeDerivative t x =
      (atlasFieldOfHigher cov A u).timeDerivative t x -
        (atlasFieldOfHigher cov A v).timeDerivative t x := by
  let W := atlasFieldOfHigher cov A (u - v)
  let U := atlasFieldOfHigher cov A u
  let V := atlasFieldOfHigher cov A v
  ext a c
  have hdiff := (U.hasTimeDerivative t ht x a c).sub
    (V.hasTimeDerivative t ht x a c)
  have hfun : (fun s : ℝ => W.toFun s x a c) =
      (fun s : ℝ => U.toFun s x a c) -
        (fun s : ℝ => V.toFun s x a c) := by
    funext s
    change W.toFun s x a c = U.toFun s x a c - V.toFun s x a c
    exact congrArg (fun h : T₂ x => h a c)
      (atlasFieldOfHigher_toFun_sub cov A u v s x)
  rw [← hfun] at hdiff
  exact (W.hasTimeDerivative t ht x a c).unique hdiff

/-- The actual intrinsic connection heat operator respects subtraction of
represented, unprojected atlas fields. -/
theorem atlasFieldOfHigher_tensorHeatOperator_sub
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u v : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) :
    (atlasFieldOfHigher cov A (u - v)).tensorHeatOperator cov t ht x =
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x -
        (atlasFieldOfHigher cov A v).tensorHeatOperator cov t ht x := by
  let W := atlasFieldOfHigher cov A (u - v)
  let U := atlasFieldOfHigher cov A u
  let V := atlasFieldOfHigher cov A v
  have hfield : W.toFun t = U.toFun t - V.toFun t := by
    funext y
    exact atlasFieldOfHigher_toFun_sub cov A u v t y
  have hLap :
      connectionLaplacian cov (W.toFun t) x =
        connectionLaplacian cov (U.toFun t) x -
          connectionLaplacian cov (V.toFun t) x := by
    have h := (connectionLaplacianLinearMapAt cov x).map_sub
      (U.slice cov t ⟨ht.1, ht.2.le⟩)
      (V.slice cov t ⟨ht.1, ht.2.le⟩)
    rw [hfield]
    simpa only [connectionLaplacianLinearMapAt_apply, Submodule.coe_sub,
      FiniteClassicalTensorHeatField.slice] using h
  change W.timeDerivative t x - connectionLaplacian cov (W.toFun t) x =
    (U.timeDerivative t x - connectionLaplacian cov (U.toFun t) x) -
      (V.timeDerivative t x - connectionLaplacian cov (V.toFun t) x)
  rw [atlasFieldOfHigher_timeDerivative_sub cov A u v t ht x, hLap]
  abel

/-- Subtracting two represented solutions with the same *global* Cauchy data
gives a represented homogeneous solution. No equality of their individual
chartwise traces is used or claimed. -/
theorem geometricAtlasCauchySolution_sub
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (u v : HigherCoefficientSpace cov A)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u)
    (hv : GeometricAtlasCauchySolution cov A u₀ f v) :
    GeometricAtlasCauchySolution cov A 0 0 (u - v) := by
  constructor
  · intro x
    have h := (hu.1 x).sub (hv.1 x)
    have h' : Tendsto
        (fun t : ℝ => (atlasFieldOfHigher cov A (u - v)).toFun t x)
        (nhdsWithin t₀ (Ioc t₀ A.commonTerminalTime))
        (nhds (u₀ x - u₀ x)) := by
      convert h using 1
      funext t
      exact atlasFieldOfHigher_toFun_sub cov A u v t x
    simpa using h'
  · intro t ht x
    rw [atlasFieldOfHigher_tensorHeatOperator_sub cov A u v t ht x,
      hu.2 t ht x, hv.2 t ht x, sub_self]
    simp

/-- The global geometric heat equation identifies the *physical readout* of
the strong atlas source residual. It does not identify the individual source
coefficients: that additional injectivity or localization is exactly what a
transfer to `StrongAtlasSolutionEquation` would require. -/
theorem atlasFieldOfHigher_physicalStrongResidual
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (Hlift : StrongCommutatorLift cov A)
    (u : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (hu : ∀ t (ht : t ∈ Ioo t₀ A.commonTerminalTime) x,
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov f t x)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    A.physicalAtlasSourceSlice cov
        (localCoordinateCauchyFamilyL cov A u) t x =
      A.physicalAtlasSourceSlice cov
        (f + Hlift.higherMap u) t x := by
  have h := atlasFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
    cov A u t ht x
  rw [hu t ht x, ← Hlift.realizesHigher u t ht x] at h
  rw [A.physicalAtlasSourceSlice_add cov]
  exact (sub_eq_iff_eq_add).mp h.symm

/-- The exact remaining uniqueness obligation for the represented geometric
class. It is a mathematical estimate problem, not a consequence of the
chartwise strong atlas uniqueness theorem. -/
def HasRepresentedZeroDataUniqueness
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α) : Prop :=
  ∀ w : HigherCoefficientSpace cov A,
    GeometricAtlasCauchySolution cov A 0 0 w →
    ∀ t, t ∈ Ioc t₀ A.commonTerminalTime →
      (atlasFieldOfHigher cov A w).toFun t = 0

/-- The intrinsic tensor energy maximum principle proves represented
zero-data uniqueness from the global geometric Cauchy condition. -/
theorem hasRepresentedZeroDataUniqueness
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (hmetric : cov.IsMetricCompatibleTangent) :
    HasRepresentedZeroDataUniqueness cov A := by
  intro w hw t ht
  have htrace : atlasInitialTrace cov A w = 0 :=
    geometricAtlasCauchySolution_initialTensor cov A 0 0 w hw
  exact A.atlasFieldOfHigher_zero_of_zeroDataHeat cov w hmetric htrace hw.2 t ht

/-- Zero-data uniqueness in the represented class implies uniqueness for
arbitrary represented solutions with equal global Cauchy data. -/
theorem geometricAtlasCauchySolution_unique_of_zeroData
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (hzero : HasRepresentedZeroDataUniqueness cov A)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (u v : HigherCoefficientSpace cov A)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u)
    (hv : GeometricAtlasCauchySolution cov A u₀ f v) :
    ∀ t, t ∈ Ioc t₀ A.commonTerminalTime →
      (atlasFieldOfHigher cov A u).toFun t =
        (atlasFieldOfHigher cov A v).toFun t := by
  intro t ht
  have hw := hzero (u - v)
    (geometricAtlasCauchySolution_sub cov A u₀ f u v hu hv) t ht
  funext x
  have hx := congrArg (fun s => s x) hw
  rw [atlasFieldOfHigher_toFun_sub cov A u v t x] at hx
  exact sub_eq_zero.mp hx

/-- A zero-data estimate for represented geometric solutions makes symmetry a
consequence of the heat equation and symmetric Cauchy data. The field here is
the ordinary, unprojected atlas reconstruction. -/
theorem geometricAtlasCauchySolution_symmetric_of_zeroData
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (hzero : HasRepresentedZeroDataUniqueness cov A)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (u : HigherCoefficientSpace cov A)
    (hD : ∀ x v w, u₀ x v w = u₀ x w v)
    (hf : ∀ t (_ht : t ∈ Ioo t₀ A.commonTerminalTime) x v w,
      f t x w v = f t x v w)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u) :
    ∀ t, t ∈ Ioc t₀ A.commonTerminalTime → ∀ x v w,
      (atlasFieldOfHigher cov A u).toFun t x v w =
        (atlasFieldOfHigher cov A u).toFun t x w v := by
  let ut := transposeHigherFamily cov A u
  have hut : GeometricAtlasCauchySolution cov A u₀ f ut :=
    geometricAtlasCauchySolution_transpose cov A u₀ f u hD hf hu
  intro t ht x v w
  have heq := geometricAtlasCauchySolution_unique_of_zeroData
    cov A hzero u₀ f u ut hu hut t ht
  have heqx := congrArg (fun s => s x v w) heq
  rw [atlasFieldOfHigher_transpose_toFun cov A u t ht x v w] at heqx
  exact heqx

/-- Under geometric zero-data uniqueness, the historical averaged readout
agrees with the ordinary reconstruction on the actual solution interval.
This is an equality theorem, not a substitute for proving that uniqueness. -/
theorem symmetrizedAtlasField_eq_at_of_zeroData
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas cov b t₀ T α)
    (hzero : HasRepresentedZeroDataUniqueness cov A)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (u : HigherCoefficientSpace cov A)
    (hD : ∀ x v w, u₀ x v w = u₀ x w v)
    (hf : ∀ t (_ht : t ∈ Ioo t₀ A.commonTerminalTime) x v w,
      f t x w v = f t x v w)
    (hu : GeometricAtlasCauchySolution cov A u₀ f u) :
    ∀ t, t ∈ Ioc t₀ A.commonTerminalTime →
      (symmetrizedAtlasField cov A u).toFun t =
        (atlasFieldOfHigher cov A u).toFun t := by
  intro t ht
  funext x
  ext v w
  have hsym := geometricAtlasCauchySolution_symmetric_of_zeroData
    cov A hzero u₀ f u hD hf hu t ht x v w
  simp only [symmetrizedAtlasField_toFun, Pi.smul_apply, Pi.add_apply,
    smul_apply, add_apply, smul_eq_mul]
  rw [atlasFieldOfHigher_transpose_toFun cov A u t ht x v w, ← hsym]
  ring

/-- If a zero-data uniqueness principle holds for this full classical-field
type, then any two solutions with the same data agree. This is a conditional
reduction only: the field type records pointwise initial trace, and a proof of
the premise may need additional uniform Hölder control. -/
theorem geometricUniqueness_of_zeroDataUniqueness
    (cov : CovariantDerivative I E TM)
    (hzero : ∀ W : FiniteClassicalTensorHeatField cov t₀ T,
      FiniteClassicalTensorHeatField.HasInitialTrace cov W 0 →
      (∀ t (ht : t ∈ Ioo t₀ T) x,
        W.tensorHeatOperator cov t ht x = 0) →
      ∀ t, t ∈ Ioc t₀ T → W.toFun t = 0)
    (U V : FiniteClassicalTensorHeatField cov t₀ T)
    (u₀ : ∀ x : M, T₂ x)
    (f : ℝ → ∀ x : M, T₂ x)
    (hU₀ : FiniteClassicalTensorHeatField.HasInitialTrace cov U u₀)
    (hV₀ : FiniteClassicalTensorHeatField.HasInitialTrace cov V u₀)
    (hU : ∀ t (ht : t ∈ Ioo t₀ T) x,
      U.tensorHeatOperator cov t ht x = f t x)
    (hV : ∀ t (ht : t ∈ Ioo t₀ T) x,
      V.tensorHeatOperator cov t ht x = f t x) :
    ∀ t, t ∈ Ioc t₀ T → U.toFun t = V.toFun t := by
  obtain ⟨htrace, hPDE⟩ :=
    geometricDifference_zeroData cov U V u₀ f hU₀ hV₀ hU hV
  intro t ht
  funext x
  have hx := congrArg (fun s => s x)
    (hzero (geometricDifference cov U V) htrace hPDE t ht)
  change U.toFun t x - V.toFun t x = 0 at hx
  exact sub_eq_zero.mp hx

end RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
