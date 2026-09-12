module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Sharp scalar comparison and lifespan for positive Einstein Ricci flow

The Challenge states every geometric object explicitly using Mathlib only.
Curvature is the corrected connection commutator, Ricci and scalar curvature are
orthonormal contractions, and the Ricci-flow equation is a componentwise time
derivative. The conclusion includes the exact reciprocal Type-I-rate scalar profile and
one-sided scalar blow-up at extinction. No evolution equation, maximum
principle, singularity profile, or lifespan bound is an input hypothesis.
-/

@[expose] public noncomputable section

open Bundle
open Filter Topology
open scoped Manifold ContDiff BigOperators

namespace EinsteinComparisonEntry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual corrected curvature commutator of the connection. -/
def curvature
    (cov : CovariantDerivative I E TM)
    (X Y Z : ∀ x : M, TM x) : ∀ x : M, TM x :=
  (fun x ↦ cov (fun y ↦ cov Z y (Y y)) x (X x)) -
  (fun x ↦ cov (fun y ↦ cov Z y (X y)) x (Y x)) -
  (fun x ↦ cov Z x (VectorField.mlieBracket I X Y x))

/-- Ricci curvature as the first/output trace of the corrected curvature. -/
def ricci
    (g : ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (extension : ∀ x : M, TM x → ∀ y : M, TM y)
    (x : M) (u v : TM x) : ℝ := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, inner ℝ (curvature cov (extension x (b i)) (extension x u) (extension x v) x) (b i)

/-- Scalar curvature as the metric trace of Ricci curvature. -/
def scalar
    (g : ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM)
    (extension : ∀ x : M, TM x → ∀ y : M, TM y)
    (x : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  exact ∑ i, ricci g cov extension x (b i) (b i)

/-- Metric compatibility written as the actual manifold Leibniz rule. -/
def metricCompatible
    (g : ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM) : Prop :=
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  ∀ {x : M} {U V : ∀ y : M, TM y},
    MDiffAt (T% U) x → MDiffAt (T% V) x → ∀ w : TM x,
      mvfderiv (I := I) (fun y ↦ inner ℝ (U y) (V y)) x w =
        inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)

/-- The torsion-free, metric-compatible Levi-Civita conditions. -/
def leviCivita
    (g : ContMDiffRiemannianMetric I 2 E TM)
    (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0 ∧ metricCompatible g cov

def homotheticFactor (lam t₀ t : ℝ) : ℝ := 1 - 2 * lam * (t - t₀)

def extinctionTime (lam t₀ : ℝ) : ℝ := t₀ + 1 / (2 * lam)

def quadraticScalarBarrier (n r₀ t₀ t : ℝ) : ℝ :=
  r₀ / (1 - (2 / n) * r₀ * (t - t₀))

/-- Positive Einstein data generates an exact Ricci flow up to its singular
time. Its scalar curvature attains the quadratic comparison barrier, equals the
reciprocal Type-I-rate scalar profile and tends to positive infinity, while the
homothetic metric cannot remain positive definite at that time. Every geometric
operation is inlined so Comparator can check one closed proposition without
asking the renderer to reconstruct dependent helper signatures. -/
def completeStatement : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [Nontrivial E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M] [CompactSpace M] [Nonempty M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (g₀ : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
    (cov₀ : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov₀.ContMDiffCovariantDerivative 1]
    (extension : ∀ x : M, TangentSpace I x → ∀ y : M, TangentSpace I y)
    (_hvalue : ∀ (x : M) (v : TangentSpace I x), extension x v x = v)
    (_hext : ∀ (x : M) (v : TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (extension x v)))
    (lam t₀ : ℝ),
    let curvature
        (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
        (X Y Z : ∀ x : M, TangentSpace I x) : ∀ x : M, TangentSpace I x :=
      (fun x ↦ cov (fun y ↦ cov Z y (Y y)) x (X x)) -
      (fun x ↦ cov (fun y ↦ cov Z y (X y)) x (Y x)) -
      (fun x ↦ cov Z x (VectorField.mlieBracket I X Y x))
    let ricci
        (g : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
        (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
        (x : M) (u v : TangentSpace I x) : ℝ := by
      letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
      let b := stdOrthonormalBasis ℝ (TangentSpace I x)
      exact ∑ i, inner ℝ
        (curvature cov (extension x (b i)) (extension x u) (extension x v) x) (b i)
    let scalar
        (g : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
        (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
        (x : M) : ℝ := by
      letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
      let b := stdOrthonormalBasis ℝ (TangentSpace I x)
      exact ∑ i, ricci g cov x (b i) (b i)
    let metricCompatible
        (g : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
        (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
      letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ {x : M} {U V : ∀ y : M, TangentSpace I y},
        MDiffAt (T% U) x → MDiffAt (T% V) x → ∀ w : TangentSpace I x,
          mvfderiv (I := I) (fun y ↦ inner ℝ (U y) (V y)) x w =
            inner ℝ (cov U x w) (V x) + inner ℝ (U x) (cov V x w)
    let leviCivita
        (g : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _))
        (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
      cov.torsion = 0 ∧ metricCompatible g cov
    let homotheticFactor (lam t₀ t : ℝ) : ℝ := 1 - 2 * lam * (t - t₀)
    let extinctionTime (lam t₀ : ℝ) : ℝ := t₀ + 1 / (2 * lam)
    let quadraticScalarBarrier (n r₀ t₀ t : ℝ) : ℝ :=
      r₀ / (1 - (2 / n) * r₀ * (t - t₀))
    0 < lam → leviCivita g₀ cov₀ →
      (∀ (x : M) (u v : TangentSpace I x),
        ricci g₀ cov₀ x u v = lam * g₀.inner x u v) →
      ∃ g : ℝ → ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _),
        (∀ {t : ℝ}, t < extinctionTime lam t₀ →
          ∀ (x : M) (u v : TangentSpace I x),
            (g t).inner x u v = homotheticFactor lam t₀ t * g₀.inner x u v) ∧
        (∀ {t : ℝ}, t < extinctionTime lam t₀ → leviCivita (g t) cov₀) ∧
        (∀ {t : ℝ}, t < extinctionTime lam t₀ →
          ∀ (x : M) (u v : TangentSpace I x),
            HasDerivAt (fun s ↦ (g s).inner x u v)
              ((-2 : ℝ) * ricci (g t) cov₀ x u v) t) ∧
        (∀ {t : ℝ}, t < extinctionTime lam t₀ → ∀ x : M,
          scalar (g t) cov₀ x =
            quadraticScalarBarrier (Module.finrank ℝ E : ℝ)
              ((Module.finrank ℝ E : ℝ) * lam) t₀ t) ∧
        (∀ {t : ℝ}, t < extinctionTime lam t₀ → ∀ x : M,
          scalar (g t) cov₀ x =
            (Module.finrank ℝ E : ℝ) /
              (2 * (extinctionTime lam t₀ - t))) ∧
        (∀ x : M, Tendsto (fun t : ℝ => scalar (g t) cov₀ x)
          (𝓝[<] extinctionTime lam t₀) atTop) ∧
        (extinctionTime lam t₀ - t₀ =
          (Module.finrank ℝ E : ℝ) /
            (2 * ((Module.finrank ℝ E : ℝ) * lam))) ∧
        ({t : ℝ | 0 < homotheticFactor lam t₀ t} =
          Set.Iio (extinctionTime lam t₀)) ∧
        ¬ ∃ gstar : ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _),
          ∀ (x : M) (u v : TangentSpace I x),
            gstar.inner x u v =
              homotheticFactor lam t₀ (extinctionTime lam t₀) * g₀.inner x u v

theorem einsteinScalarComparisonAndSharpLifespan : completeStatement := by
  sorry

end EinsteinComparisonEntry
