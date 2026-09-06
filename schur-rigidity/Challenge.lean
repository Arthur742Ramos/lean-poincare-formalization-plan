module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Schur rigidity: an independent statement using explicit connection curvature.
Ricci and scalar curvature are the displayed orthonormal contractions of that
curvature. The covariant divergence uses the actual manifold differential and
both connection corrections. No differential identity is an assumption. -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff BigOperators

namespace SchurEntry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

def along (X Z : ∀ x : M, (TangentSpace I : M → Type _) x) : ∀ x : M, (TangentSpace I : M → Type _) x := fun x ↦ cov Z x (X x)

/-- The actual connection curvature, including its Lie-bracket correction. -/
def curvature (X Y Z : ∀ x : M, (TangentSpace I : M → Type _) x) : ∀ x : M, (TangentSpace I : M → Type _) x :=
  along cov X (along cov Y Z) - along cov Y (along cov X Z) -
    along cov (VectorField.mlieBracket I X Y) Z

def MetricCompatible : Prop :=
  ∀ {x : M} {U V : ∀ y : M, (TangentSpace I : M → Type _) y}, MDiffAt (T% U) x → MDiffAt (T% V) x →
    ∀ w : (TangentSpace I : M → Type _) x, mvfderiv (I := I) (fun y ↦ inner ℝ (U y) (V y)) x w =
      inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)

variable (extension : ∀ x : M, (TangentSpace I : M → Type _) x → ∀ y : M, (TangentSpace I : M → Type _) y)


/-- Ricci is the first/output trace of the explicit curvature operator. -/
def ricci (x : M) (u v : (TangentSpace I : M → Type _) x) : ℝ :=
  letI : FiniteDimensional ℝ ((TangentSpace I : M → Type _) x) := VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ ((TangentSpace I : M → Type _) x)
  ∑ i, inner ℝ (curvature cov (extension x (b i)) (extension x u) (extension x v) x) (b i)

def scalar (x : M) : ℝ :=
  letI : FiniteDimensional ℝ ((TangentSpace I : M → Type _) x) := VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ ((TangentSpace I : M → Type _) x)
  ∑ i, ricci cov extension x (b i) (b i)

def einstein (x : M) (u v : (TangentSpace I : M → Type _) x) : ℝ :=
  ricci cov extension x u v - scalar cov extension x / 2 * inner ℝ u v

/-- Corrected derivative of a bilinear tensor field, not an abstract derivative. -/
def tensorDerivative (A : ∀ x : M, (TangentSpace I : M → Type _) x → (TangentSpace I : M → Type _) x → ℝ)
    (x : M) (p u v : (TangentSpace I : M → Type _) x) : ℝ :=
  mvfderiv (I := I) (fun y ↦ A y (extension x u y) (extension x v y)) x p -
    A x (cov (extension x u) x p) v - A x u (cov (extension x v) x p)

def divergence (A : ∀ x : M, (TangentSpace I : M → Type _) x → (TangentSpace I : M → Type _) x → ℝ)
    (x : M) (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) : ℝ :=
  ∑ i, tensorDerivative cov extension A x (b i) (b i) w

variable
  (hvalue : ∀ (x : M) (v : (TangentSpace I : M → Type _) x), extension x v x = v)
  (hext : ∀ (x : M) (v : (TangentSpace I : M → Type _) x), ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (extension x v)))
  (hT : cov.torsion = 0) (hmetric : MetricCompatible cov)

include hvalue hext hT hmetric

theorem geometricContractedBianchi (x : M)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) :
    divergence cov extension (ricci cov extension) x b w =
      (1 / 2 : ℝ) * mvfderiv (I := I) (scalar cov extension) x w := by
  sorry

theorem divergenceEinstein (x : M)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ ((TangentSpace I : M → Type _) x)) (w : (TangentSpace I : M → Type _) x) :
    divergence cov extension (einstein cov extension) x b w = 0 := by
  sorry

theorem schur [ConnectedSpace M]
    (hn : 3 ≤ Module.finrank ℝ E) (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ x u v, ricci cov extension x u v = f x * inner ℝ u v) :
    ∃ c : ℝ, ∀ x, f x = c := by
  sorry

theorem threeDimensionalEinstein_constantCurvature [ConnectedSpace M]
    (hn : Module.finrank ℝ E = 3) (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f)
    (hRic : ∀ x u v, ricci cov extension x u v = f x * inner ℝ u v) :
    ∃ K : ℝ, ∀ (x : M) (u v z t : (TangentSpace I : M → Type _) x),
      inner ℝ (curvature cov (extension x u) (extension x v) (extension x z) x) t =
        K * (inner ℝ u t * inner ℝ v z - inner ℝ u z * inner ℝ v t) := by
  sorry

end SchurEntry
