import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasSymmetricWellPosedness

/-!
# Short-time heat well-posedness for symmetric covariant two-tensors

The statement exposes the geometric equation independently of the proof
development.  The rough Laplacian is the orthonormal trace of the second
covariant derivative, expanded using Mathlib's manifold derivative and the
given tangent connection.  The conclusion constructs finite-atlas coefficient
spaces and their geometric readouts.  For every represented symmetric spatial
datum and symmetric parabolic source, there is a unique coefficient witness
whose readout has the asserted initial trace, is fiberwise symmetric, solves
the actual tensor heat equation, and satisfies a global finite-atlas Schauder
estimate.

This is deliberately a theorem for the constructed finite-atlas Holder data
class.  It does not assert that every bare intrinsic section has such a
coefficient representation, and uniqueness is of the atlas coefficient
witness in the constructed classical class.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 4000000

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace SymmetricTensorHeatEntry

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance challengeTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
@[reducible] local instance challengeTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance challengeTwoTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
local instance challengeTwoFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
local instance challengeTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) (fun x => TM x →L[ℝ] ℝ)
@[reducible] local instance challengeThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
@[reducible] local instance challengeThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
@[reducible] local instance challengeThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance
local instance challengeThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance challengeThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance challengeThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- A connection on covariant two-tensors is the one induced by `cov` when it
obeys the actual three-slot Leibniz formula on differentiable sections. -/
def IsInducedTwoTensorConnection
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂) : Prop :=
  ∀ (h : ∀ x : M, T₂ x) (U V : ∀ x : M, TM x) (x : M),
    MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x →
      MDiffAt (T% U) x → MDiffAt (T% V) x →
      ∀ X : TM x,
        cov₂ h x X (U x) (V x) =
          mvfderiv (I := I) (fun y => h y (U y) (V y)) x X
            - h x (cov U x X) (V x) - h x (U x) (cov V x X)

/-- A connection on covariant three-tensors is the one induced by `cov` when
it obeys the actual four-slot Leibniz formula on differentiable sections. -/
def IsInducedThreeTensorConnection
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) : Prop :=
  ∀ (K : ∀ x : M, T₃ x) (U V W : ∀ x : M, TM x) (x : M),
    MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y (K y)) x →
      MDiffAt (T% U) x → MDiffAt (T% V) x →
      MDiffAt (T% W) x → ∀ X : TM x,
        cov₃ K x X (U x) (V x) (W x) =
          mvfderiv (I := I) (fun y => K y (U y) (V y) (W y)) x X
            - K x (cov U x X) (V x) (W x)
            - K x (U x) (cov V x X) (W x)
            - K x (U x) (V x) (cov W x X)

/-- The actual rough Laplacian `tr_g(∇²h)` evaluated on two tangent
vectors, with the positive-coordinate sign convention.  The two tensor
connections are constrained by `IsInducedTwoTensorConnection` and
`IsInducedThreeTensorConnection` in the selected theorem. -/
def connectionLaplacianApply
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (h : ∀ x : M, T₂ x)
    (x : M) (u v : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  ∑ i : Fin (Module.finrank ℝ (TM x)),
    cov₃ (cov₂ h) x (b i) (b i) u v

/-- Fiberwise symmetry of a covariant two-tensor section. -/
def IsSymmetricSection (h : ∀ x : M, T₂ x) : Prop :=
  ∀ x : M, ∀ u v : TM x, h x u v = h x v u

/-- Pointwise initial trace from the finite forward interval. -/
def HasInitialTrace (t₀ S : ℝ) (u : ℝ → ∀ x : M, T₂ x)
    (u₀ : ∀ x : M, T₂ x) : Prop :=
  ∀ x : M, Tendsto (fun t : ℝ => u t x)
    (nhdsWithin t₀ (Ioc t₀ S)) (nhds (u₀ x))

/-- Temporal differentiability after evaluation on arbitrary fiber vectors. -/
def HasTimeDerivative (t₀ S : ℝ)
    (u du : ℝ → ∀ x : M, T₂ x) : Prop :=
  ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M, ∀ a b : TM x,
    HasDerivAt (fun s : ℝ => u s x a b) (du t x a b) t

/-- The componentwise tensor heat equation with the explicitly expanded
connection Laplacian above. -/
def SolvesTensorHeat
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (t₀ S : ℝ)
    (u du f : ℝ → ∀ x : M, T₂ x) : Prop :=
  ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M, ∀ a b : TM x,
    du t x a b - connectionLaplacianApply cov₂ cov₃ (u t) x a b = f t x a b

/-- Metric compatibility written as the genuine manifold Leibniz rule. -/
def IsMetricCompatibleTangent (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {U V : ∀ y : M, TM y},
    MDiffAt (T% U) x → MDiffAt (T% V) x → ∀ w : TM x,
      mvfderiv (I := I) (fun y => inner ℝ (U y) (V y)) x w =
        inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)

/-- The torsion-free, metric-compatible Levi--Civita conditions. -/
def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0 ∧ IsMetricCompatibleTangent cov

/-- The complete Mathlib-facing statement.  The existential types are the
finite-atlas initial, source, and higher-coefficient spaces constructed by the
proof.  Their readout maps expose every geometric conclusion, while
`coordinateClass` records the precise unique atlas solution class rather than
claiming uniqueness among unrepresented bare fields. -/
def completeStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [Nontrivial E]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [CompactSpace M] [SigmaCompactSpace M]
    [I.Boundaryless] [Nonempty M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    (cov₂ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    [cov₂.ContMDiffCovariantDerivative 1]
    [cov₂.ContMDiffCovariantDerivative 2]
    [cov₃.ContMDiffCovariantDerivative 1]
    (t₀ α : ℝ),
    let inducedTwo : Prop :=
      ∀ (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (U V : ∀ x : M, TangentSpace I x) (x : M),
        MDiffAt (fun y => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ]
            TangentSpace I z →L[ℝ] ℝ) y (h y)) x →
        MDiffAt (T% U) x → MDiffAt (T% V) x →
        ∀ X : TangentSpace I x,
          cov₂ h x X (U x) (V x) =
            mvfderiv (I := I) (fun y => h y (U y) (V y)) x X
              - h x (cov U x X) (V x) - h x (U x) (cov V x X)
    let inducedThree : Prop :=
      ∀ (K : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (U V W : ∀ x : M, TangentSpace I x) (x : M),
        MDiffAt (fun y => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M => TangentSpace I z →L[ℝ]
            TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (K y)) x →
        MDiffAt (T% U) x → MDiffAt (T% V) x → MDiffAt (T% W) x →
        ∀ X : TangentSpace I x,
          cov₃ K x X (U x) (V x) (W x) =
            mvfderiv (I := I) (fun y => K y (U y) (V y) (W y)) x X
              - K x (cov U x X) (V x) (W x)
              - K x (U x) (cov V x X) (W x)
              - K x (U x) (V x) (cov W x X)
    let roughLaplacian := fun
        (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (x : M) (u v : TangentSpace I x) =>
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
      let b := stdOrthonormalBasis ℝ (TangentSpace I x)
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        cov₃ (cov₂ h) x (b i) (b i) u v
    let symmetric := fun
        (h : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ x : M, ∀ u v : TangentSpace I x, h x u v = h x v u
    let initialTrace := fun (S : ℝ)
        (u : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ)
        (u₀ : ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ x : M, Tendsto (fun t : ℝ => u t x)
        (nhdsWithin t₀ (Ioc t₀ S)) (nhds (u₀ x))
    let timeDerivative := fun (S : ℝ)
        (u du : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M,
        ∀ a b : TangentSpace I x,
          HasDerivAt (fun s : ℝ => u s x a b) (du t x a b) t
    let solves := fun (S : ℝ)
        (u du f : ℝ → ∀ x : M, TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] ℝ) =>
      ∀ t : ℝ, t ∈ Ioo t₀ S → ∀ x : M,
        ∀ a b : TangentSpace I x,
          du t x a b - roughLaplacian (u t) x a b = f t x a b
    let metricCompatible : Prop :=
      ∀ {x : M} {U V : ∀ y : M, TangentSpace I y},
        MDiffAt (T% U) x → MDiffAt (T% V) x →
        ∀ w : TangentSpace I x,
          mvfderiv (I := I) (fun y => inner ℝ (U y) (V y)) x w =
            inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)
    let leviCivita : Prop := cov.torsion = 0 ∧ metricCompatible
    leviCivita → inducedTwo → inducedThree →
    0 < α → α < 1 →
    ∃ (S : ℝ), t₀ < S ∧
      ∃ (Initial Source Solution : Type u)
        (initialTensor : Initial →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (sourceTensor : Source → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTensor : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTimeDerivative : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (initialSize : Initial → ℝ) (sourceNorm : Source → ℝ)
        (solutionNorm : Solution → ℝ)
        (coordinateClass : Initial → Source → Solution → Prop)
        (C : ℝ),
        Nonempty Initial ∧ Nonempty Source ∧ Nonempty Solution ∧ 0 ≤ C ∧
        (∀ D, 0 ≤ initialSize D) ∧ (∀ f, 0 ≤ sourceNorm f) ∧
        (∀ D f,
          symmetric (initialTensor D) →
          (∀ t, t ∈ Ioo t₀ S → symmetric (sourceTensor f t)) →
          ∃! q : Solution,
            coordinateClass D f q ∧
            timeDerivative S (solutionTensor q) (solutionTimeDerivative q) ∧
            initialTrace S (solutionTensor q) (initialTensor D) ∧
            (∀ t, t ∈ Ioc t₀ S →
              symmetric (solutionTensor q t)) ∧
            solves S (solutionTensor q) (solutionTimeDerivative q) (sourceTensor f)) ∧
        (∀ D f q, coordinateClass D f q →
          solutionNorm q ≤ C * (initialSize D + sourceNorm f))

private theorem canonicalTwo_apply_eq
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (h : ∀ x : M, T₂ x) (x : M)
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x) :
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x =
      cov₂ h x := by
  ext X u v
  let U := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x u
  let V := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x v
  have hU : MDiffAt (T% U) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x u).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x v).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  rw [_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    cov hh X u v]
  have H := hcov₂ h U V x hh hU hV X
  simpa [U, V, _root_.CovariantDerivative.smoothExtend_apply] using H.symm

private theorem canonicalThree_apply_eq
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (K : ∀ x : M, T₃ x) (x : M)
    (hK : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y (K y)) x) :
    _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov K x =
      cov₃ K x := by
  ext X u v w
  let U := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x u
  let V := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x v
  let W := _root_.CovariantDerivative.smoothExtend
    (I := I) (F := E) (V := TM) x w
  have hU : MDiffAt (T% U) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x u).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hV : MDiffAt (T% V) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x v).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hW : MDiffAt (T% W) x :=
    ((_root_.CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x w).of_le (by simp) x).mdifferentiableAt
      one_ne_zero
  have hKU : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (K y (U y))) x :=
    hK.clm_bundle_apply hU
  unfold _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative
  simp only [_root_.CovariantDerivative.inducedHomCovariantDerivative, dif_pos hK]
  rw [_root_.CovariantDerivative.inducedHomAtOfMDiff_apply]
  change
    (_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
        (fun y => K y (U y)) x X) v w -
      K x (cov (_root_.CovariantDerivative.smoothExtend
          (I := I) (F := E) (V := TM) x u) x X) v w = _
  rw [_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    cov hKU X v w]
  have H := hcov₃ K U V W x hK hU hV hW X
  simp only [U, V, W, _root_.CovariantDerivative.smoothExtend_apply] at H ⊢
  linear_combination H.symm

private theorem canonicalTwoRegularity
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (k : ℕ∞ω) [cov₂.ContMDiffCovariantDerivative k]
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (hk : (1 : ℕ∞ω) ≤ k + 1) :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov) k where
  contMDiff := ⟨by
    intro h hh
    have heq :
        _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov h =
          cov₂ h := by
      funext x
      apply canonicalTwo_apply_eq cov cov₂ hcov₂ h x
      exact ((hh.contMDiffAt (isOpen_univ.mem_nhds (mem_univ x))).of_le hk).mdifferentiableAt
        one_ne_zero
    rw [heq]
    exact (inferInstance : cov₂.ContMDiffCovariantDerivative k).contMDiff.contMDiff hh⟩

private theorem canonicalThreeRegularity
    (cov : CovariantDerivative I E TM)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (k : ℕ∞ω) [cov₃.ContMDiffCovariantDerivative k]
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (hk : (1 : ℕ∞ω) ≤ k + 1) :
    _root_.CovariantDerivative.ContMDiffCovariantDerivative
      (_root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov) k where
  contMDiff := ⟨by
    intro K hK
    have heq :
        _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov K =
          cov₃ K := by
      funext x
      apply canonicalThree_apply_eq cov cov₃ hcov₃ K x
      exact ((hK.contMDiffAt (isOpen_univ.mem_nhds (mem_univ x))).of_le hk).mdifferentiableAt
        one_ne_zero
    rw [heq]
    exact (inferInstance : cov₃.ContMDiffCovariantDerivative k).contMDiff.contMDiff hK⟩

private theorem connectionLaplacianApply_eq_canonical
    (cov : CovariantDerivative I E TM)
    (cov₂ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ) T₂)
    (cov₃ : CovariantDerivative I
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃)
    (hcov₂ : IsInducedTwoTensorConnection cov cov₂)
    (hcov₃ : IsInducedThreeTensorConnection cov cov₃)
    (h : _root_.CovariantDerivative.ConnectionLaplacianDomain
      (E := E) (I := I) (M := M) cov)
    (x : M) (u v : TM x) :
    connectionLaplacianApply cov₂ cov₃ h.1 x u v =
      _root_.CovariantDerivative.connectionLaplacian cov h.1 x u v := by
  let canonical₂ :=
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
  have h₂ : canonical₂ h.1 = cov₂ h.1 := by
    funext y
    exact canonicalTwo_apply_eq cov cov₂ hcov₂ h.1 y (h.2.1 y)
  have hcov₃eq :
      _root_.CovariantDerivative.covariantThreeTensorCovariantDerivative cov
          (cov₂ h.1) x = cov₃ (cov₂ h.1) x := by
    apply canonicalThree_apply_eq cov cov₃ hcov₃ (cov₂ h.1) x
    rw [← h₂]
    exact h.2.2 x
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [_root_.CovariantDerivative.connectionLaplacian_eq_sum_orthonormalBasis
    cov h.1 x b]
  unfold connectionLaplacianApply
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← hcov₃eq, ← h₂]
  rfl

private theorem strongAtlasSchauderConstant_nonneg
    {t₀ T α : ℝ} {d : ℕ}
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.StrongCommutatorLift
      cov A) :
    0 ≤ RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.strongAtlasSchauderConstant
      cov Hlift := by
  have hpos : 0 < 1 - ‖Hlift.sourceLift.toContinuousLinearMap‖ :=
    sub_pos.mpr Hlift.sourceLift.norm_lt_one
  unfold RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.strongAtlasSchauderConstant
  positivity

private def zeroSpatialData {d : ℕ} {α : ℝ} :
    RicciFlow.AnalyticPDE.BoundedSpatialC2AlphaData E
      (Fin d × Fin d → ℝ) α where
  value := BoundedContinuousFunction.const E 0
  spaceDeriv := BoundedContinuousFunction.const E 0
  spaceSecondDeriv := BoundedContinuousFunction.const E 0
  holderConstant := 0
  holderConstant_nonneg := le_rfl
  value_holder := by
    intro x y
    change ‖(0 : Fin d × Fin d → ℝ) - 0‖ ≤ 0 * dist x y ^ α
    simp
  spaceDeriv_holder := by
    intro x y
    change ‖(0 : E →L[ℝ] (Fin d × Fin d → ℝ)) - 0‖ ≤ 0 * dist x y ^ α
    simp
  spaceSecondDeriv_holder := by
    intro x y
    rw [BoundedContinuousFunction.const_apply]
    simp only [zero_mul, sub_self]
    exact le_of_eq
      (@norm_zero (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) inferInstance)
  hasFDerivAt_value := by
    intro x
    change HasFDerivAt (fun _ : E => (0 : Fin d × Fin d → ℝ))
      (0 : E →L[ℝ] (Fin d × Fin d → ℝ)) x
    exact hasFDerivAt_const (x := x) (c := (0 : Fin d × Fin d → ℝ))
  hasFDerivAt_spaceDeriv := by
    intro x
    change HasFDerivAt
      (fun _ : E => (0 : E →L[ℝ] (Fin d × Fin d → ℝ)))
      (0 : E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) x
    exact hasFDerivAt_const (x := x)
      (c := (0 : E →L[ℝ] (Fin d × Fin d → ℝ)))

theorem symmetricTensorHeatShortTimeWellPosed : completeStatement := by
  dsimp only [completeStatement]
  intro E instNorm instSpace instFD instComplete instNontrivial H instTopH I M
    instTopM instCharted instT2 instManifold instCompact instSigma instBoundary
    instNonempty instRiem instRiemSmooth instVB cov instCov cov₂ cov₃
    instCov₂One instCov₂Two instCov₃One
    t₀ α hLevi hcov₂ hcov₃ hα hα1
  letI canonicalTwoOne := canonicalTwoRegularity cov cov₂ 1 hcov₂ (by norm_num)
  letI canonicalTwoTwo := canonicalTwoRegularity cov cov₂ 2 hcov₂ (by norm_num)
  letI canonicalThreeOne := canonicalThreeRegularity cov cov₃ 1 hcov₃ (by norm_num)
  have hLevi' : _root_.CovariantDerivative.IsLeviCivita cov := by
    refine ⟨hLevi.1, ?_⟩
    intro x U V hU hV w
    exact hLevi.2 hU hV w
  let b := Module.finBasis ℝ E
  let Traw := t₀ + 1
  have hTraw : t₀ < Traw := by dsimp [Traw]; linarith
  obtain ⟨Sraw, hSraw, hSrawT, A, Hlift, hunique, hwell⟩ :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.exists_short_symmetric_tensorHeat_wellPosed
      cov hLevi' b hTraw hα hα1
  let S := A.commonTerminalTime
  have hS : t₀ < S := A.lt_commonTerminalTime cov
  refine ⟨S, hS, ?_⟩
  let Initial :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.AtlasSpatialInitialData cov A
  let Source :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.SourceSpace cov A
  let Solution :=
    RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.HigherCoefficientSpace cov A
  let initialTensor : Initial → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun D => RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.spatialInitialTensor
      cov A D
  let sourceTensor : Source → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun f t => A.physicalAtlasSourceSlice cov f t
  let solutionTensor : Solution → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q => (A.symmetrizedAtlasField cov q).toFun
  let solutionTimeDerivative : Solution → ℝ → ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun q => (A.symmetrizedAtlasField cov q).timeDerivative
  let initialSize : Initial → ℝ :=
    fun D => A.spatialInitialSize cov D
  let sourceNorm : Source → ℝ := fun f => ‖f‖
  let solutionNorm : Solution → ℝ := fun q => ‖q‖
  let coordinateClass : Initial → Source → Solution → Prop :=
    fun D f q => A.SymmetricAtlasSpatialClassicalSolution cov Hlift D f q
  let C := A.strongAtlasSchauderConstant cov Hlift
  refine ⟨Initial, Source, Solution, initialTensor, sourceTensor,
    solutionTensor, solutionTimeDerivative, initialSize, sourceNorm,
    solutionNorm, coordinateClass, C, ?_⟩
  refine ⟨⟨fun _ => zeroSpatialData⟩, ⟨0⟩, ⟨0⟩,
    strongAtlasSchauderConstant_nonneg cov Hlift, ?_, ?_, ?_, ?_⟩
  · intro D
    exact A.spatialInitialSize_nonneg cov D
  · intro f
    exact norm_nonneg f
  · intro D f hD hf
    have hD' :
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.AtlasSpatialInitialData.IsSymmetric
          cov D := by
      exact hD
    have hf' :
        RicciFlow.AnalyticPDE.FiniteTensorHeatParametrixAtlas.SourceSpace.IsSymmetric
          cov f := by
      exact hf
    obtain ⟨q, hq, huniq⟩ := (hwell D f hD' hf').1
    refine ⟨q, ⟨hq, ?_, hq.2.1, hq.2.2.1, ?_⟩, ?_⟩
    · exact (A.symmetrizedAtlasField cov q).hasTimeDerivative
    · intro t ht x a c
      have hP := hq.2.2.2 t ht x
      have hPeval := congrArg
        (fun k : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => k a c) hP
      have hlap := connectionLaplacianApply_eq_canonical cov cov₂ cov₃
        hcov₂ hcov₃
        ((A.symmetrizedAtlasField cov q).slice cov t ⟨ht.1, ht.2.le⟩) x a c
      have hlap' : connectionLaplacianApply cov₂ cov₃
          ((A.symmetrizedAtlasField cov q).toFun t) x a c =
          _root_.CovariantDerivative.connectionLaplacian cov
            ((A.symmetrizedAtlasField cov q).toFun t) x a c := hlap
      change
        (A.symmetrizedAtlasField cov q).timeDerivative t x a c -
          connectionLaplacianApply cov₂ cov₃
            ((A.symmetrizedAtlasField cov q).toFun t) x a c =
          A.physicalAtlasSourceSlice cov f t x a c
      rw [hlap']
      exact hPeval
    · intro q' hq'
      exact huniq q' hq'.1
  · intro D f q hq
    exact A.norm_le_strongAtlasSchauderConstant_mul_symmetricData
      cov hunique Hlift D f q hq

end SymmetricTensorHeatEntry
