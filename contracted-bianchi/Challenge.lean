module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Double-contracted second Bianchi identity

The Challenge surface is deliberately independent of the candidate's local curvature library.
It states the corrected connection commutator directly, with the smooth extensions used to
evaluate tangent vectors supplied explicitly.  The proof-side project may instantiate those
extensions with its canonical construction.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace ContractedBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

/- The pointwise operation `∇_X σ`. -/
noncomputable def along
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun x ↦ cov σ x (X x)

/- The raw curvature commutator, including the Lie-bracket correction. -/
noncomputable def curvatureAux
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  along cov X (along cov Y Z) - along cov Y (along cov X Z) -
    along cov (VectorField.mlieBracket I X Y) Z

/- The covariant derivative of the curvature operator, with all correction terms displayed. -/
noncomputable def secondBianchiAux
    (X Y Z W : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  along cov X (curvatureAux cov Y Z W) -
    curvatureAux cov (along cov X Y) Z W -
    curvatureAux cov Y (along cov X Z) W -
    curvatureAux cov Y Z (along cov X W)

/- Metric compatibility written as the metric Leibniz rule used by the proof. -/
def IsMetricCompatibleTangent : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

/- Evaluate the explicit field-level derivative on tangent vectors at `x`. -/
noncomputable def curvatureCovariantDerivative
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (p a b c : TangentSpace I x) : TangentSpace I x :=
  secondBianchiAux cov (extension x p) (extension x a) (extension x b) (extension x c) x

noncomputable def curvatureCovariantDerivativeInner
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (p a b c d : TangentSpace I x) : ℝ :=
  inner ℝ (curvatureCovariantDerivative cov extension x p a b c) (extension x d x)

theorem contractedSecondBianchi
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (extension : ∀ x : M, TangentSpace I x → Π y : M, TangentSpace I y)
    (x : M) (hT : cov.torsion = 0)
    (hmetric : IsMetricCompatibleTangent cov)
    (hvalue : ∀ v : TangentSpace I x, extension x v x = v)
    (hext : ∀ v : TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (extension x v)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x))
    (w : TangentSpace I x) :
    (∑ i, ∑ k, curvatureCovariantDerivativeInner
      cov extension x w (b k) (b i) (b i) (b k)) =
    2 * ∑ i, ∑ k, curvatureCovariantDerivativeInner
      cov extension x (b i) (b k) (b i) w (b k) := by
  sorry

end ContractedBianchi
