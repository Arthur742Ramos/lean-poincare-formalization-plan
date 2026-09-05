import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Diffeomorphism transport of connections and curvature

This Challenge isolates a genuine manifold-level transport theorem from the
repository's Ricci-flow development.  A bundled `C^2` self-diffeomorphism
induces an invertible tangent map; the pulled-back affine connection is given
by the displayed pushforward/pullback formula, and `curvatureAux` is the
displayed covariant-derivative commutator.  The selected results prove raw
curvature and torsion transport and preservation of metric compatibility and
the Levi–Civita property.

The metric compatibility statements quantify over an independently supplied
smooth target metric whose inner product satisfies the explicit pullback
formula.  Thus the result is about actual tangent bundles and covariant
derivatives, not an unconstrained endomorphism or scalar-family model.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

theorem connectionDifferenceTraceOneForm._proof_1 : Nat.AtLeastTwo (1 + 1) :=
  Nat.instAtLeastTwoHAddOfNat 1

end RicciFlow

local notation "palomarRegularityTwo" =>
  @OfNat.ofNat (WithTop ENat) (nat_lit 2)
    (@instOfNatAtLeastTwo (WithTop ENat) (nat_lit 2) (@WithTop.natCast ENat ENat.instNatCast)
      RicciFlow.connectionDifferenceTraceOneForm._proof_1)

local notation "palomarDefinitionRegularityTwo" =>
  @OfNat.ofNat (WithTop ENat) (nat_lit 2)
    (@instOfNatAtLeastTwo (WithTop ENat) (nat_lit 2) (@WithTop.natCast ENat ENat.instNatCast)
      (@Nat.instAtLeastTwoHAddOfNat
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V]
  [VectorBundle 𝕜 F V]

def along (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

abbrev curvatureAux (cov : CovariantDerivative I F V)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [hREGroup : NormedAddCommGroup E] [hRESpace : NormedSpace ℝ E]
  {H : Type*} [hRHTop : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [hRMTop : TopologicalSpace M] [hRCharted : ChartedSpace H M]
  [hRFinite : FiniteDimensional ℝ E] [hRComplete : CompleteSpace E]
  [hRManifold : IsManifold I palomarDefinitionRegularityTwo M]
  [hRRiemannian : RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

def IsTorsionFree (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0

def IsMetricCompatibleTangent
    (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

end CovariantDerivative

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle palomarDefinitionRegularityTwo E (TangentSpace I : M → Type _) I]

abbrev SmoothSelfDiffeomorph2 := M ≃ₘ^palomarRegularityTwo⟮I, I⟯ M

namespace SmoothSelfDiffeomorph2

variable (φ : SmoothSelfDiffeomorph2 (I := I) (M := M))

noncomputable abbrev tangentMap (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (φ x) :=
  φ.mfderivToContinuousLinearEquiv (by simp) x

abbrev pushforwardTangent (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I (φ x) := φ.tangentMap x

abbrev pullbackTangent (x : M) :
    TangentSpace I (φ x) →L[ℝ] TangentSpace I x := (φ.tangentMap x).symm

def pushforwardVectorField
    (X : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun y ↦
    cast (congrArg (fun z : M => TangentSpace I z) (φ.apply_symm_apply y))
      (φ.pushforwardTangent (φ.symm y) (X (φ.symm y)))

def pullbackVectorField
    (X : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun x ↦ φ.pullbackTangent x (X (φ x))

noncomputable def pullbackCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := fun X x ↦
    (φ.pullbackTangent x).comp <|
      (cov (φ.pushforwardVectorField X) (φ x)).comp (φ.pushforwardTangent x)
  isCovariantDerivativeOnUniv := by
    have _hT2 : T2Space M := inferInstance
    have _hFinite : FiniteDimensional ℝ E := inferInstance
    have _hComplete : CompleteSpace E := inferInstance
    have _hManifold : IsManifold I ∞ M := inferInstance
    have _hTangent : ContMDiffVectorBundle palomarDefinitionRegularityTwo E (TangentSpace I : M → Type _) I := inferInstance
    sorry

end SmoothSelfDiffeomorph2

end RicciFlow

namespace PoincareCurvature.Palomar

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle palomarRegularityTwo E (TangentSpace I : M → Type _) I]

theorem curvatureAux_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y σ : Π x : M, TangentSpace I x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ =
      φ.pullbackVectorField
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ)) := by
  sorry

theorem curvatureAux_pullbackCovariantDerivative_apply
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y σ : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ x =
      φ.pullbackTangent x
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ) (φ x)) := by
  sorry

theorem torsion_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    ((φ.pullbackCovariantDerivative cov).torsion x) (X x) (Y x) =
      φ.pullbackTangent x
        ((cov.torsion (φ x)) (φ.pushforwardTangent x (X x))
          (φ.pushforwardTangent x (Y x))) := by
  sorry

theorem isTorsionFree_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsTorsionFree) :
    (φ.pullbackCovariantDerivative cov).IsTorsionFree := by
  sorry

theorem isMetricCompatibleTangent_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)}
    (hinner : ∀ x : M, ∀ u v : TangentSpace I x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent := by
  sorry

theorem isLeviCivita_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)}
    (hinner : ∀ x : M, ∀ u v : TangentSpace I x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita := by
  sorry

end PoincareCurvature.Palomar
