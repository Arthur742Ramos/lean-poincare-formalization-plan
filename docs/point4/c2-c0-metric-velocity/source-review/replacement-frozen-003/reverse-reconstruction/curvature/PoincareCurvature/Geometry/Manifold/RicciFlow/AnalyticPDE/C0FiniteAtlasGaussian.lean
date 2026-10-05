import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C0GaussianEndpoint
import PoincareCurvature.Analysis.PreferredCoordinateFrame
import PoincareCurvature.Geometry.Manifold.VectorBundle.FiniteSmoothTrivializingCover
import PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.NormalizedCutoff
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalReconstruction

/-!
# Concrete finite-atlas Gaussian smoothing of continuous symmetric tensors

SOURCE CANDIDATE, UNCOMPILED. The finite cover and compact coordinate cutoffs
are constructed from compactness, preferred chart/frame data, and manifold
boundarylessness. A supplied analytic regularizer is never used.

The velocity is a continuous section of the actual covariant-two-tensor
bundle, not a C2 tensor, a Holder tensor, or a collection of formal scalars.
The partition, charts, and tangent frames remain fixed as h varies.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace RicciFlow.AnalyticPDE.C0Endpoint

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.PreferredCoordinateFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "BilE" => (E →L[ℝ] E →L[ℝ] ℝ)

@[reducible] local instance endpointTwoModelNormedAddCommGroup :
    NormedAddCommGroup BilE := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance endpointTwoModelNormedSpace :
    NormedSpace ℝ BilE := ContinuousLinearMap.toNormedSpace
@[reducible] local instance endpointTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance endpointTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := ContinuousLinearMap.toNormedSpace

/-- Literal C0 regularity in the actual tensor-bundle topology. No positive
Holder exponent or differentiability assumption occurs in this structure. -/
structure ContinuousSymmetricVelocity where
  tensor : ∀ x : M, T₂ x
  continuous : Continuous (fun x => TotalSpace.mk' BilE (E := T₂) x (tensor x))
  symmetric : ∀ x (u v : TM x), tensor x u v = tensor x v u

variable {d : ℕ}

def velocityComponent (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (j k : Fin d) (x : M) : ℝ :=
  v.tensor x (frame (I := I) p b j x) (frame (I := I) p b k x)

lemma continuousOn_velocityComponent
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (j k : Fin d) :
    ContinuousOn (velocityComponent v p b j k) (trivialization (I := I) p).baseSet := by
  have hj := (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
    (I := I) (e := trivialization (I := I) p) (n := (2 : ℕ∞ω)) b j).continuous
  have hk := (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
    (I := I) (e := trivialization (I := I) p) (n := (2 : ℕ∞ω)) b k).continuous
  have h := v.continuous.continuousOn.clm_bundle_apply₂ hj hk
  have hprod := (Bundle.Trivial.homeomorphProd M ℝ).continuous.comp_continuousOn h
  simpa only [velocityComponent, frame, Bundle.Trivial.homeomorphProd_apply,
    TotalSpace.toProd] using hprod.snd

def velocityCoordinates (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (j k : Fin d) (z : Fin d → ℝ) : ℝ :=
  velocityComponent v p b j k ((extChartAt I p).symm (toModel b z))

def coordinateAnalysisDomain (p : M) (b : Module.Basis (Fin d) ℝ E) : Set (Fin d → ℝ) :=
  (toModel b) ⁻¹' preferredCoordinateAnalysisDomain (I := I) (F := E) (V := TM) p

lemma continuousOn_velocityCoordinates
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (j k : Fin d) :
    ContinuousOn (velocityCoordinates v p b j k) (coordinateAnalysisDomain (I := I) p b) := by
  have hmodel := (continuousOn_velocityComponent v p b j k).comp
    ((continuousOn_extChartAt_symm (I := I) p).mono inter_subset_left)
    (fun z hz => hz.2)
  exact hmodel.comp (toModel b).continuous.continuousOn (fun z hz => hz)

lemma velocityCoordinates_symmetric
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (p : M) (b : Module.Basis (Fin d) ℝ E) (j k : Fin d) (z : Fin d → ℝ) :
    velocityCoordinates v p b j k z = velocityCoordinates v p b k j z :=
  v.symmetric _ _ _

variable [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local notation "Cover" => FiniteSmoothPreferredTrivializingCover I (F := E) (V := TM)

def preferredCover : Cover := FiniteSmoothPreferredTrivializingCover.chosen
  (I := I) (F := E) (V := TM)

lemma isOpen_coordinateAnalysisDomain (p : M) (b : Module.Basis (Fin d) ℝ E) :
    IsOpen (coordinateAnalysisDomain (I := I) p b) := by
  have hopen : IsOpen (preferredCoordinateAnalysisDomain (I := I) (F := E) (V := TM) p) :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target (I := I) p)
      (trivializationAt E TM p).open_baseSet
  exact hopen.preimage (toModel b).continuous

def finiteCoordinatePiece (C : Cover) (b : Module.Basis (Fin d) ℝ E)
    (i : C.Index) : Set (Fin d → ℝ) :=
  (toModel b).symm '' (C.coordinatePieces i : Set E)

lemma isCompact_finiteCoordinatePiece (C : Cover) (b : Module.Basis (Fin d) ℝ E)
    (i : C.Index) : IsCompact (finiteCoordinatePiece C b i) :=
  (C.coordinatePieces i).isCompact.image (toModel b).symm.continuous

lemma finiteCoordinatePiece_subset_domain (C : Cover) (b : Module.Basis (Fin d) ℝ E)
    (i : C.Index) : finiteCoordinatePiece C b i ⊆ coordinateAnalysisDomain (I := I) (i : M) b := by
  rintro z ⟨w, hw, rfl⟩
  simpa only [coordinateAnalysisDomain, mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    using C.coordinatePieces_subset_preferredCoordinateAnalysisDomain i hw

/-- Concrete Euclidean buffer data, selected internally for a compact piece
of the already-fixed preferred atlas. -/
structure CoordinateBuffer (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) where
  control : NormalizedCutoffControl (Fin d → ℝ)
  support_subset : tsupport control.cutoff ⊆ coordinateAnalysisDomain (I := I) (i : M) b
  one_nhds : ∀ᶠ z in nhdsSet (finiteCoordinatePiece C b i), control.cutoff z = 1

lemma nonempty_coordinateBuffer (C : Cover) (b : Module.Basis (Fin d) ℝ E)
    (i : C.Index) : Nonempty (CoordinateBuffer C b i) := by
  obtain ⟨χ, hχsupp, hχone, _hχIcc⟩ :=
    exists_normalizedCutoffControl_one_nhdsSet_of_isCompact
      (isCompact_finiteCoordinatePiece C b i)
      (isOpen_coordinateAnalysisDomain (I := I) (i : M) b)
      (finiteCoordinatePiece_subset_domain C b i)
  exact ⟨⟨χ, hχsupp, hχone⟩⟩

def coordinateBuffer (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) :
    CoordinateBuffer C b i := Classical.choice (nonempty_coordinateBuffer C b i)

/-- Multiplication by a compact buffer supported in the continuity domain
erases the arbitrary totalization of the coefficient outside that domain. -/
lemma continuous_mul_of_tsupport_subset {X : Type*} [TopologicalSpace X]
    {χ q : X → ℝ} {U : Set X} (hχ : Continuous χ) (hU : IsOpen U)
    (hsupp : tsupport χ ⊆ U) (hq : ContinuousOn q U) :
    Continuous (fun x => χ x * q x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.continuousAt.mul ((hq x (hsupp hx)).continuousAt (hU.mem_nhds (hsupp hx)))
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [hy]

def localizedVelocityFunction (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (j k : Fin d)
    (z : Fin d → ℝ) : ℝ :=
  (coordinateBuffer C b i).control.cutoff z * velocityCoordinates v (i : M) b j k z

lemma continuous_localizedVelocityFunction
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (j k : Fin d) :
    Continuous (localizedVelocityFunction v C b i j k) :=
  continuous_mul_of_tsupport_subset
    (coordinateBuffer C b i).control.contDiff_three.continuous
    (isOpen_coordinateAnalysisDomain (I := I) (i : M) b)
    (coordinateBuffer C b i).support_subset
    (continuousOn_velocityCoordinates v (i : M) b j k)

lemma hasCompactSupport_localizedVelocityFunction
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (j k : Fin d) :
    HasCompactSupport (localizedVelocityFunction v C b i j k) :=
  (coordinateBuffer C b i).control.compactSupport.mul_right

def localizedVelocityBcf (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (j k : Fin d) :
    BoundedContinuousFunction (Fin d → ℝ) ℝ :=
  _root_.ofCompactSupport (localizedVelocityFunction v C b i j k)
    (continuous_localizedVelocityFunction v C b i j k)
    (hasCompactSupport_localizedVelocityFunction v C b i j k)

lemma uniformContinuous_localizedVelocityBcf
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (j k : Fin d) :
    UniformContinuous (localizedVelocityBcf v C b i j k : (Fin d → ℝ) → ℝ) :=
  (hasCompactSupport_localizedVelocityFunction v C b i j k).uniformContinuous_of_continuous
    (continuous_localizedVelocityFunction v C b i j k)

def gaussianMatrix (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (h : ℝ)
    (z : Fin d → ℝ) (j k : Fin d) : ℝ :=
  (gaussianPath (localizedVelocityBcf v C b i j k) h z +
    gaussianPath (localizedVelocityBcf v C b i k j) h z) / 2

lemma gaussianMatrix_symmetric
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (h : ℝ)
    (z : Fin d → ℝ) (j k : Fin d) :
    gaussianMatrix v C b i h z j k = gaussianMatrix v C b i h z k j := by
  simp only [gaussianMatrix, add_comm]

lemma contDiff_two_gaussianMatrix
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ 2 (gaussianMatrix v C b i h) := by
  rw [contDiff_pi]
  intro j
  rw [contDiff_pi]
  intro k
  exact ((contDiff_two_gaussianPath (localizedVelocityBcf v C b i j k) hh).add
    (contDiff_two_gaussianPath (localizedVelocityBcf v C b i k j) hh)).div_const 2

def chartCoordinate (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M) : Fin d → ℝ :=
  (toModel b).symm (extChartAt I p x)

def gaussianMatrixOnManifold (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (h : ℝ)
    (x : M) : Fin d → Fin d → ℝ :=
  gaussianMatrix v C b i h (chartCoordinate (I := I) (i : M) b x)

lemma contMDiffOn_gaussianMatrixOnManifold
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) {h : ℝ} (hh : h ≠ 0) :
    ContMDiffOn I 𝓘(ℝ, Fin d → Fin d → ℝ) 2 (gaussianMatrixOnManifold v C b i h)
      (preferredAnalysisDomain I (F := E) (V := TM) (i : M)) := by
  have hmodel : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin d → Fin d → ℝ) 2
      (fun z : E => gaussianMatrix v C b i h ((toModel b).symm z)) :=
    contMDiff_iff_contDiff.mpr ((contDiff_two_gaussianMatrix v C b i hh).comp
      (toModel b).symm.contDiff)
  exact hmodel.contMDiffOn.comp
    ((contMDiffOn_extChartAt (I := I) (H := H) (n := 2) (x := (i : M))).mono
      inter_subset_left) (fun _ _ => mem_univ _)

/-- The actual tensor approximant, assembled with the fixed original atlas
and its finite smooth partition. The value h = 0 is a C0 tensor and is used
only to certify the endpoint jet; no C2 assertion is made about that slice. -/
def gaussianTensor (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (h : ℝ) : ∀ x : M, T₂ x :=
  fun x => ∑ i : C.Index, cutoffLocalTensorOfMatrix (I := I)
    (C.trivialization i) b (C.partition i) (gaussianMatrixOnManifold v C b i h) x

lemma gaussianTensor_symmetric
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (h : ℝ) (x : M) (u w : TM x) :
    gaussianTensor v C b h x u w = gaussianTensor v C b h x w u := by
  simp only [gaussianTensor, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact cutoffLocalTensorOfMatrix_isSymmetric (C.trivialization i) b (C.partition i)
    (gaussianMatrixOnManifold v C b i h)
    (fun x j k => gaussianMatrix_symmetric v C b i h _ j k) x u w

lemma contMDiff_two_gaussianTensor
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) {h : ℝ} (hh : h ≠ 0) :
    ContMDiff I (I.prod 𝓘(ℝ, BilE)) 2
      (fun x => TotalSpace.mk' BilE (E := T₂) x (gaussianTensor v C b h x)) := by
  classical
  have hs : ∀ i : C.Index,
      ContMDiff I (I.prod 𝓘(ℝ, BilE)) 2
        (fun x => TotalSpace.mk' BilE (E := T₂) x
          (cutoffLocalTensorOfMatrix (I := I) (C.trivialization i) b (C.partition i)
            (gaussianMatrixOnManifold v C b i h) x)) := by
    intro i
    exact contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
      (i : M) (C.trivialization i) b (C.partition i)
      (gaussianMatrixOnManifold v C b i h)
      (isOpen_preferredAnalysisDomain I (F := E) (V := TM) (i : M))
      inter_subset_right ((C.partition i).contMDiff.of_le (by simp))
      (C.pieces_subset_preferredAnalysisDomain i)
      (contMDiffOn_gaussianMatrixOnManifold v C b i hh)
  simpa only [gaussianTensor] using
    (ContMDiff.sum_section (s := Finset.univ) fun i _ => hs i)

lemma continuousAt_gaussianMatrix_zero
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (z : Fin d → ℝ) :
    ContinuousAt (fun h => gaussianMatrix v C b i h z) 0 := by
  apply continuousAt_pi.2
  intro j
  apply continuousAt_pi.2
  intro k
  have hj : ContinuousAt (fun h => gaussianPath (localizedVelocityBcf v C b i j k) h z) 0 :=
    (BoundedContinuousFunction.lipschitz_eval_const z).continuous.continuousAt.comp
      (continuousAt_gaussianPath_zero (localizedVelocityBcf v C b i j k)
        (uniformContinuous_localizedVelocityBcf v C b i j k))
  have hk : ContinuousAt (fun h => gaussianPath (localizedVelocityBcf v C b i k j) h z) 0 :=
    (BoundedContinuousFunction.lipschitz_eval_const z).continuous.continuousAt.comp
      (continuousAt_gaussianPath_zero (localizedVelocityBcf v C b i k j)
        (uniformContinuous_localizedVelocityBcf v C b i k j))
  exact (hj.add hk).div_const 2

lemma localTensorOfMatrix_eq_at
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis (Fin d) ℝ E)
    (q : M → Fin d → Fin d → ℝ) (x : M) (hx : x ∈ e.baseSet)
    (B : T₂ x)
    (hB : ∀ j k, q x j k = B (e.localFrame b j x) (e.localFrame b k x)) :
    localTensorOfMatrix e b q x = B := by
  apply ContinuousLinearMap.toLinearMap₁₂_injective
  apply (b.map (e.linearEquivAt ℝ x hx).symm).ext
  intro j
  apply (b.map (e.linearEquivAt ℝ x hx).symm).ext
  intro k
  have h := localTensorOfMatrix_localFrame e b q hx j k
  rw [hB j k] at h
  simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    Module.Basis.map_apply, e.localFrame_apply_of_mem_baseSet b hx] using h

lemma gaussianMatrixOnManifold_zero_of_mem_piece
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index)
    (x : M) (hx : x ∈ (C.pieces i : Set M)) (j k : Fin d) :
    gaussianMatrixOnManifold v C b i 0 x j k =
      velocityComponent v (i : M) b j k x := by
  have hz : chartCoordinate (I := I) (i : M) b x ∈ finiteCoordinatePiece C b i := by
    exact ⟨extChartAt I (i : M) x, ⟨x, hx, rfl⟩, rfl⟩
  have hχ := (coordinateBuffer C b i).one_nhds.self_of_nhdsSet
    (chartCoordinate (I := I) (i : M) b x) hz
  have hxSource := C.pieces_subset_chartSource i hx
  simp only [gaussianMatrixOnManifold, gaussianMatrix, gaussianPath_zero]
  change (localizedVelocityFunction v C b i j k (chartCoordinate (I := I) (i : M) b x) +
    localizedVelocityFunction v C b i k j (chartCoordinate (I := I) (i : M) b x)) / 2 = _
  simp only [localizedVelocityFunction, hχ, one_mul, velocityCoordinates, chartCoordinate,
    ContinuousLinearEquiv.apply_symm_apply, (extChartAt I (i : M)).left_inv hxSource]
  have hsym : velocityComponent v (i : M) b k j x = velocityComponent v (i : M) b j k x :=
    v.symmetric x _ _
  rw [hsym]
  ring

/-- The zero-parameter finite Gaussian reconstruction is exactly the given
continuous tensor. All buffers equal one where their partition contributes. -/
lemma gaussianTensor_zero
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) :
    gaussianTensor v C b 0 = v.tensor := by
  classical
  funext x
  have hpartition : ∑ i : C.Index, C.partition i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ x)
  unfold gaussianTensor cutoffLocalTensorOfMatrix
  have heach : ∀ i : C.Index,
      C.partition i x • localTensorOfMatrix (C.trivialization i) b
        (gaussianMatrixOnManifold v C b i 0) x = C.partition i x • v.tensor x := by
    intro i
    by_cases hψ : C.partition i x = 0
    · simp [hψ]
    · have hx : x ∈ (C.pieces i : Set M) := subset_closure (Function.mem_support.2 hψ)
      have hxBase := C.pieces_subset_baseSet i hx
      congr 1
      exact localTensorOfMatrix_eq_at (C.trivialization i) b
        (gaussianMatrixOnManifold v C b i 0) x hxBase (v.tensor x)
        (fun j k => gaussianMatrixOnManifold_zero_of_mem_piece v C b i x hx j k)
  rw [Finset.sum_congr rfl (fun i _ => heach i), ← Finset.sum_smul, hpartition, one_smul]

lemma continuousAt_gaussianTensor_component_zero
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (x : M) (u w : TM x) :
    ContinuousAt (fun h => gaussianTensor v C b h x u w) 0 := by
  classical
  have hi : ∀ i : C.Index,
      ContinuousAt (fun h => cutoffLocalTensorOfMatrix (C.trivialization i) b
        (C.partition i) (gaussianMatrixOnManifold v C b i h) x u w) 0 := by
    intro i
    by_cases hx : x ∈ (C.trivialization i).baseSet
    · have hq := continuousAt_gaussianMatrix_zero v C b i
        (chartCoordinate (I := I) (i : M) b x)
      have hmat := (matrixBilinearSynthesis b).continuous.continuousAt.comp hq
      have heval := (hmat.clm_apply (continuousAt_const
        (c := tangentCoordCLM (C.trivialization i) x hx u))).clm_apply
        (continuousAt_const (c := tangentCoordCLM (C.trivialization i) x hx w))
      simpa only [cutoffLocalTensorOfMatrix, localTensorOfMatrix, dif_pos hx,
        ContinuousLinearMap.bilinearComp_apply, matrixBilinearSynthesis_apply,
        gaussianMatrixOnManifold, _root_.smul_apply, smul_eq_mul] using
        (continuousAt_const (c := C.partition i x)).mul heval
    · simpa only [cutoffLocalTensorOfMatrix, localTensorOfMatrix, dif_neg hx,
        smul_zero, ContinuousLinearMap.zero_apply] using
        (continuousAt_const (c := (0 : ℝ)))
  simpa only [gaussianTensor, _root_.sum_apply] using
    (tendsto_finsetSum Finset.univ fun i _ => hi i)

/-- Ordinary two-sided component derivative of the actual finite-atlas
Gaussian perturbation. The prescribed velocity only has C0 regularity. -/
lemma hasDerivAt_time_mul_gaussianTensor
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (x : M) (u w : TM x) :
    HasDerivAt (fun h : ℝ => h * gaussianTensor v C b h x u w) (v.tensor x u w) 0 := by
  have h := hasDerivAt_time_mul_of_continuousAt
    (continuousAt_gaussianTensor_component_zero v C b x u w)
  simpa only [gaussianTensor_zero] using h

end RicciFlow.AnalyticPDE.C0Endpoint
