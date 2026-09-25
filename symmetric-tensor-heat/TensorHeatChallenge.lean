module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
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

universe u v

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

/-- The parabolic metric used by the finite-atlas Hölder norms: time has
weight two and space has weight one. -/
def parabolicDistance {X : Type u} [PseudoMetricSpace X]
    (p q : ℝ × X) : ℝ :=
  max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)

/-- An explicit, single-radius parabolic `C⁰ᵃ` certificate.  The displayed
radius simultaneously dominates a sup bound and a Hölder seminorm bound. -/
def HasParabolicC0AlphaNormLe {X : Type u} {V : Type v} [PseudoMetricSpace X]
    [NormedAddCommGroup V] (t₀ S α N : ℝ) (f : ℝ × X → V) : Prop :=
  ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧
    (∀ z, z.1 ∈ Ioc t₀ S → ‖f z‖ ≤ B) ∧
    ∀ p, p.1 ∈ Ioc t₀ S → ∀ q, q.1 ∈ Ioc t₀ S →
      ‖f p - f q‖ ≤ H * parabolicDistance p q ^ α

/-- A concrete bounded spatial `C²ᵃ` jet with its genuine first and second
Fréchet derivatives and one displayed norm radius. -/
def HasSpatialC2AlphaNormLe {X : Type u} {V : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (α N : ℝ) (f : X → V) (df : X → X →L[ℝ] V)
    (d2f : X → X →L[ℝ] X →L[ℝ] V) : Prop :=
  0 ≤ N ∧
    (∀ x, ‖f x‖ ≤ N) ∧ (∀ x, ‖df x‖ ≤ N) ∧
    (∀ x, ‖d2f x‖ ≤ N) ∧
    (∀ x y, ‖f x - f y‖ ≤ N * dist x y ^ α) ∧
    (∀ x y, ‖df x - df y‖ ≤ N * dist x y ^ α) ∧
    (∀ x y, ‖d2f x - d2f y‖ ≤ N * dist x y ^ α) ∧
    (∀ x, HasFDerivAt f (df x) x) ∧
    ∀ x, HasFDerivAt df (d2f x) x

/-- A concrete finite-cylinder `C²⁺ᵃ,¹⁺ᵃ/²` jet.  All four
components have genuine parabolic Hölder bounds controlled by the displayed
Schauder norm, and the derivative fields are the actual derivatives. -/
def HasParabolicC2AlphaNormLe {X : Type u} {V : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t₀ S α N : ℝ) (f : ℝ × X → V)
    (df : ℝ × X → X →L[ℝ] V)
    (d2f : ℝ × X → X →L[ℝ] X →L[ℝ] V)
    (dtf : ℝ × X → V) : Prop :=
  HasParabolicC0AlphaNormLe t₀ S α N f ∧
    HasParabolicC0AlphaNormLe t₀ S α N df ∧
    HasParabolicC0AlphaNormLe t₀ S α N d2f ∧
    HasParabolicC0AlphaNormLe t₀ S α N dtf ∧
    (∀ t, t ∈ Ioc t₀ S → ∀ x, HasFDerivAt (fun y => f (t, y)) (df (t, x)) x) ∧
    (∀ t, t ∈ Ioc t₀ S → ∀ x,
      HasFDerivAt (fun y => df (t, y)) (d2f (t, x)) x) ∧
    ∀ t, t ∈ Ioo t₀ S → ∀ x,
      HasDerivAt (fun s => f (s, x)) (dtf (t, x)) t

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
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I],
    let tangent := (TangentSpace I : M → Type _)
    let twoTensor := fun x : M => tangent x →L[ℝ] tangent x →L[ℝ] ℝ
    letI (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
        NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
        NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedSpace
    letI (x : M) : NormedAddCommGroup (twoTensor x) := inferInstance
    letI (x : M) : NormedSpace ℝ (twoTensor x) := inferInstance
    letI : TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) twoTensor) :=
      Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
        (RingHom.id ℝ) E tangent (E →L[ℝ] ℝ)
        (fun x => tangent x →L[ℝ] ℝ)
    letI : FiberBundle (E →L[ℝ] E →L[ℝ] ℝ) twoTensor :=
      Bundle.ContinuousLinearMap.fiberBundle
        (RingHom.id ℝ) E tangent (E →L[ℝ] ℝ)
        (fun x => tangent x →L[ℝ] ℝ)
    letI : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) twoTensor :=
      Bundle.ContinuousLinearMap.vectorBundle
        (RingHom.id ℝ) E tangent (E →L[ℝ] ℝ)
        (fun x => tangent x →L[ℝ] ℝ)
    letI threeModelNormedAddCommGroup (V : Type u)
        [NormedAddCommGroup V] [NormedSpace ℝ V] :
        NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI threeModelNormedSpace (V : Type u)
        [NormedAddCommGroup V] [NormedSpace ℝ V] :
        NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedSpace
    letI (x : M) : NormedAddCommGroup (tangent x →L[ℝ] twoTensor x) :=
      threeModelNormedAddCommGroup (tangent x)
    letI (x : M) : NormedSpace ℝ (tangent x →L[ℝ] twoTensor x) :=
      threeModelNormedSpace (tangent x)
    letI : TopologicalSpace (TotalSpace
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => tangent x →L[ℝ] twoTensor x)) :=
      Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
        (RingHom.id ℝ) E tangent (E →L[ℝ] E →L[ℝ] ℝ) twoTensor
    letI : FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => tangent x →L[ℝ] twoTensor x) :=
      Bundle.ContinuousLinearMap.fiberBundle
        (RingHom.id ℝ) E tangent (E →L[ℝ] E →L[ℝ] ℝ) twoTensor
    letI : VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => tangent x →L[ℝ] twoTensor x) :=
      Bundle.ContinuousLinearMap.vectorBundle
        (RingHom.id ℝ) E tangent (E →L[ℝ] E →L[ℝ] ℝ) twoTensor
    ∀ (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
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
    let Matrix := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ
    letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] Matrix) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] Matrix) :=
      ContinuousLinearMap.toNormedSpace
    let parabolicMetric := fun (p q : ℝ × E) =>
      max (Real.sqrt |p.1 - q.1|) (dist p.2 q.2)
    let hasParabolicC0 := fun (S N : ℝ) (f : ℝ × E → Matrix) =>
      ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧
        (∀ z, z.1 ∈ Ioc t₀ S → ‖f z‖ ≤ B) ∧
        ∀ p, p.1 ∈ Ioc t₀ S → ∀ q, q.1 ∈ Ioc t₀ S →
          ‖f p - f q‖ ≤ H * parabolicMetric p q ^ α
    let hasParabolicC0First := fun (S N : ℝ)
        (f : ℝ × E → E →L[ℝ] Matrix) =>
      ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧
        (∀ z, z.1 ∈ Ioc t₀ S → ‖f z‖ ≤ B) ∧
        ∀ p, p.1 ∈ Ioc t₀ S → ∀ q, q.1 ∈ Ioc t₀ S →
          ‖f p - f q‖ ≤ H * parabolicMetric p q ^ α
    let hasParabolicC0Second := fun (S N : ℝ)
        (f : ℝ × E → E →L[ℝ] E →L[ℝ] Matrix) =>
      ∃ B ≥ 0, ∃ H ≥ 0, B + H ≤ N ∧
        (∀ z, z.1 ∈ Ioc t₀ S → ‖f z‖ ≤ B) ∧
        ∀ p, p.1 ∈ Ioc t₀ S → ∀ q, q.1 ∈ Ioc t₀ S →
          ‖f p - f q‖ ≤ H * parabolicMetric p q ^ α
    let hasSpatialC2 := fun (N : ℝ) (f : E → Matrix)
        (df : E → E →L[ℝ] Matrix)
        (d2f : E → E →L[ℝ] E →L[ℝ] Matrix) =>
      0 ≤ N ∧
        (∀ x, ‖f x‖ ≤ N) ∧ (∀ x, ‖df x‖ ≤ N) ∧
        (∀ x, ‖d2f x‖ ≤ N) ∧
        (∀ x y, ‖f x - f y‖ ≤ N * dist x y ^ α) ∧
        (∀ x y, ‖df x - df y‖ ≤ N * dist x y ^ α) ∧
        (∀ x y, ‖d2f x - d2f y‖ ≤ N * dist x y ^ α) ∧
        (∀ x, HasFDerivAt f (df x) x) ∧
        ∀ x, HasFDerivAt df (d2f x) x
    let hasParabolicC2 := fun (S N : ℝ) (f : ℝ × E → Matrix)
        (df : ℝ × E → E →L[ℝ] Matrix)
        (d2f : ℝ × E → E →L[ℝ] E →L[ℝ] Matrix)
        (dtf : ℝ × E → Matrix) =>
      hasParabolicC0 S N f ∧
        hasParabolicC0First S N df ∧
        hasParabolicC0Second S N d2f ∧
        hasParabolicC0 S N dtf ∧
        (∀ t, t ∈ Ioc t₀ S → ∀ x,
          HasFDerivAt (fun y => f (t, y)) (df (t, x)) x) ∧
        (∀ t, t ∈ Ioc t₀ S → ∀ x,
          HasFDerivAt (fun y => df (t, y)) (d2f (t, x)) x) ∧
        ∀ t, t ∈ Ioo t₀ S → ∀ x,
          HasDerivAt (fun s => f (s, x)) (dtf (t, x)) t
    leviCivita → inducedTwo → inducedThree →
    0 < α → α < 1 →
    ∃ (S : ℝ), t₀ < S ∧
      ∃ (Tcoord : ℝ), t₀ < Tcoord ∧
      ∃ (Index Initial Source Solution : Type u)
        (_indexFinite : Finite Index) (_indexNonempty : Nonempty Index)
        (initialTensor : Initial →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (sourceTensor : Source → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTensor : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionTimeDerivative : Solution → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (initialLocalTensor : Initial → Index →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (sourceLocalTensor : Source → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionLocalTensor : Solution → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (solutionLocalTimeDerivative : Solution → Index → ℝ →
          ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (atlasCoordinate : Index → M → E)
        (atlasBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
        (atlasFrame : Index → Fin (Module.finrank ℝ E) →
          ∀ x : M, TangentSpace I x)
        (atlasWeight : Index → M → ℝ)
        (atlasCenter : Index → M) (atlasRadius : Index → ℝ)
        (normalizedTimeCoordinate : Index → ℝ → ℝ)
        (sourceRescale : Index → ℝ)
        (initialValue : Initial → Index → E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSpaceDeriv : Initial → Index → E →
          E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSpaceSecondDeriv : Initial → Index → E →
          E →L[ℝ] E →L[ℝ]
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialHolderConstant : Initial → Index → ℝ)
        (sourceValue : Source → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionValue : Solution → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionSpaceDeriv : Solution → Index → ℝ × E →
          E →L[ℝ] (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionSpaceSecondDeriv : Solution → Index → ℝ × E →
          E →L[ℝ] E →L[ℝ]
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (solutionTimeDerivCoordinate : Solution → Index → ℝ × E →
          (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ))
        (initialSize : Initial → ℝ) (sourceNorm : Source → ℝ)
        (solutionNorm : Solution → ℝ)
        (coordinateClass : Initial → Source → Solution → Prop)
        (C : ℝ),
        Nonempty Initial ∧ Nonempty Source ∧ Nonempty Solution ∧ 0 ≤ C ∧
        ((∀ i, 0 < atlasRadius i) ∧
          (∀ i x, atlasCoordinate i x =
            (atlasRadius i)⁻¹ •
              ((extChartAt I (atlasCenter i)) x -
                (extChartAt I (atlasCenter i)) (atlasCenter i))) ∧
          (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (atlasWeight i)) ∧
          (∀ i, tsupport (atlasWeight i) ⊆
            (extChartAt I (atlasCenter i)).source) ∧
          (∀ x, ∃ i, x ∈ (extChartAt I (atlasCenter i)).source) ∧
          (∀ i t, normalizedTimeCoordinate i t =
            t₀ + (atlasRadius i)⁻¹ ^ 2 * (t - t₀)) ∧
          (∀ i, sourceRescale i = (atlasRadius i)⁻¹ ^ 2)) ∧
        (∀ i p x, atlasFrame i p x =
          (trivializationAt E (TangentSpace I : M → Type _)
            (atlasCenter i)).localFrame atlasBasis p x) ∧
        (∀ x, ∑ᶠ i, atlasWeight i x = 1) ∧
        (∀ i x, 0 ≤ atlasWeight i x) ∧
        (∀ i, 0 < sourceRescale i) ∧
        (∀ i t, t ∈ Ioo t₀ S →
          normalizedTimeCoordinate i t ∈ Ioc t₀ Tcoord) ∧
        (∀ i x, atlasWeight i x ≠ 0 → ∀ v,
          ∃ a : Fin (Module.finrank ℝ E) → ℝ,
          v = ∑ p, a p • atlasFrame i p x) ∧
        (∀ D x, initialTensor D x = ∑ᶠ i, initialLocalTensor D i x) ∧
        (∀ f t x, sourceTensor f t x = ∑ᶠ i, sourceLocalTensor f i t x) ∧
        (∀ q t, t ∈ Ioc t₀ S → ∀ x a b,
          solutionTensor q t x a b =
            ∑ᶠ i, solutionLocalTensor q i t x a b) ∧
        (∀ q t, t ∈ Ioo t₀ S → ∀ x a b,
          solutionTimeDerivative q t x a b =
            ∑ᶠ i, solutionLocalTimeDerivative q i t x a b) ∧
        (∀ D i x, atlasWeight i x = 0 → initialLocalTensor D i x = 0) ∧
        (∀ f i t x, atlasWeight i x = 0 → sourceLocalTensor f i t x = 0) ∧
        (∀ q i t x, atlasWeight i x = 0 → solutionLocalTensor q i t x = 0) ∧
        (∀ q i t x, atlasWeight i x = 0 →
          solutionLocalTimeDerivative q i t x = 0) ∧
        (∀ D i x p k,
          initialLocalTensor D i x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * initialValue D i (atlasCoordinate i x) (k, p)) ∧
        (∀ f i t x p k,
          sourceLocalTensor f i t x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * (sourceRescale i *
              sourceValue f i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p))) ∧
        (∀ q i t, t ∈ Ioc t₀ S → ∀ x p k,
          solutionLocalTensor q i t x (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x *
              solutionValue q i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p)) ∧
        (∀ q i t, t ∈ Ioo t₀ S → ∀ x p k,
          solutionLocalTimeDerivative q i t x
              (atlasFrame i p x) (atlasFrame i k x) =
            atlasWeight i x * (sourceRescale i *
              solutionTimeDerivCoordinate q i (normalizedTimeCoordinate i t,
                atlasCoordinate i x) (k, p))) ∧
        Function.Injective (fun D =>
          (initialValue D, initialSpaceDeriv D,
            initialSpaceSecondDeriv D, initialHolderConstant D)) ∧
        Function.Injective sourceValue ∧
        Function.Injective (fun q =>
          (solutionValue q, solutionSpaceDeriv q,
            solutionSpaceSecondDeriv q, solutionTimeDerivCoordinate q)) ∧
        (∀ (v : Index → BoundedContinuousFunction E Matrix)
            (dv : Index → BoundedContinuousFunction E (E →L[ℝ] Matrix))
            (d2v : Index → BoundedContinuousFunction E
              (E →L[ℝ] E →L[ℝ] Matrix))
            (H : Index → ℝ),
          (∀ i, 0 ≤ H i) →
          (∀ i x y, ‖v i x - v i y‖ ≤ H i * dist x y ^ α) →
          (∀ i x y, ‖dv i x - dv i y‖ ≤ H i * dist x y ^ α) →
          (∀ i x y, ‖d2v i x - d2v i y‖ ≤ H i * dist x y ^ α) →
          (∀ i x, HasFDerivAt (v i) (dv i x) x) →
          (∀ i x, HasFDerivAt (dv i) (d2v i x) x) →
          ∃ D : Initial,
            (∀ i x, initialValue D i x = v i x) ∧
            (∀ i x, initialSpaceDeriv D i x = dv i x) ∧
            (∀ i x, initialSpaceSecondDeriv D i x = d2v i x) ∧
            (∀ i, initialHolderConstant D i = H i) ∧
            initialSize D = ∑ᶠ i,
              max (‖v i‖ + H i)
                (max (‖dv i‖ + H i) (‖d2v i‖ + H i))) ∧
        (∀ (c : Index → ℝ × E → Matrix) (N : Index → ℝ),
          (∀ i, hasParabolicC0 Tcoord (N i) (c i)) →
          ∃ f : Source,
            (∀ i z, z.1 ∈ Ioc t₀ Tcoord → sourceValue f i z = c i z) ∧
            sourceNorm f ≤ ∑ᶠ i, N i) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ D, ∀ i x, initialValue D i x = c i) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ f, ∀ i z, z.1 ∈ Ioc t₀ Tcoord → sourceValue f i z = c i) ∧
        (∀ c : Index →
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
          ∃ q, ∀ i z, z.1 ∈ Ioc t₀ Tcoord → solutionValue q i z = c i) ∧
        (∀ D i, hasSpatialC2 (initialSize D)
          (initialValue D i) (initialSpaceDeriv D i)
          (initialSpaceSecondDeriv D i)) ∧
        (∀ f i, hasParabolicC0 Tcoord (sourceNorm f)
          (sourceValue f i)) ∧
        (∀ D, 0 ≤ initialSize D) ∧ (∀ f, 0 ≤ sourceNorm f) ∧
        (∀ q, timeDerivative S (solutionTensor q) (solutionTimeDerivative q)) ∧
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
        (∀ D f q r,
          initialTrace S (solutionTensor q) (initialTensor D) →
          initialTrace S (solutionTensor r) (initialTensor D) →
          solves S (solutionTensor q) (solutionTimeDerivative q) (sourceTensor f) →
          solves S (solutionTensor r) (solutionTimeDerivative r) (sourceTensor f) →
          ∀ t, t ∈ Ioc t₀ S → solutionTensor q t = solutionTensor r t) ∧
        (∀ D f q, coordinateClass D f q →
          (∀ i, hasParabolicC2 Tcoord (solutionNorm q)
            (solutionValue q i) (solutionSpaceDeriv q i)
            (solutionSpaceSecondDeriv q i) (solutionTimeDerivCoordinate q i)) ∧
          solutionNorm q ≤ C * (initialSize D + sourceNorm f))

theorem symmetricTensorHeatShortTimeWellPosed : completeStatement := by
  sorry

end SymmetricTensorHeatEntry
