module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic

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
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

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
    (cov₃ : CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) : Prop :=
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

theorem symmetricTensorHeatShortTimeWellPosed : completeStatement := by
  sorry

end SymmetricTensorHeatEntry
