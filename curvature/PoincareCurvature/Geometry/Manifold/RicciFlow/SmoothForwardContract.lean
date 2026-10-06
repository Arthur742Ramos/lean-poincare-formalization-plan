module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence
public import PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardRegularity
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Separate smooth forward Point-4 target

This is a strong, smooth, forward endpoint contract. It is not the canonical
C² contract. No general construction theorem or upstream port is supplied.
The Ricci tensor below is the repository's genuine chosen-Levi-Civita tensor.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow.SmoothForward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Convert the smooth metric family componentwise to the existing C² record. -/
def c2Family (g : MetricFamily (I := I) (M := M)) :
    RicciFlow.MetricFamily (I := I) (M := M) := fun t => toC2 (g t)

/-- The equation is right-sided at the initial time and ordinary at interior
times after the usual local-neighborhood conversion. It asserts no equation
at the excluded terminal time or on negative/past times. -/
def ForwardEquation (g : MetricFamily (I := I) (M := M)) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.Ico a b, ∀ x : M, ∀ u v : TangentSpace I x,
    HasDerivWithinAt (fun s : ℝ => (g s).inner x u v)
      ((-2 : ℝ) * RicciFlow.intrinsicRicciTensor (c2Family g) t x u v)
      (Set.Ici a) t

/-- The identical strong class is used for the constructed solution and every
competitor. An all-real index does not assert all-real joint regularity. -/
structure StrongSolution (a : ℝ) (g₀ : Metric (I := I) (M := M)) where
  terminalTime : ℝ
  terminal_gt : a < terminalTime
  metric : MetricFamily (I := I) (M := M)
  initial_eq : metric a = g₀
  joint_smooth : JointlySmoothOn metric a terminalTime
  equation : ForwardEquation metric a terminalTime

/-- Restriction preserves the same one-sided initial convention. -/
def StrongSolution.restrict {a : ℝ} {g₀ : Metric (I := I) (M := M)}
    (sol : StrongSolution a g₀) (c : ℝ) (hac : a < c)
    (hcb : c ≤ sol.terminalTime) : StrongSolution a g₀ where
  terminalTime := c
  terminal_gt := hac
  metric := sol.metric
  initial_eq := sol.initial_eq
  joint_smooth := sol.joint_smooth.restrict hcb
  equation := fun t ht => sol.equation t ⟨ht.1, lt_of_lt_of_le ht.2 hcb⟩

/-- A genuine empty-manifold construction; no general existence is claimed. -/
def strongSolutionOfIsEmpty [IsEmpty M] (a : ℝ) (g₀ : Metric (I := I) (M := M)) :
    StrongSolution a g₀ where
  terminalTime := a + 1
  terminal_gt := lt_add_one a
  metric := fun _ => g₀
  initial_eq := rfl
  joint_smooth := fun x₀ => isEmptyElim x₀
  equation := fun _ _ x => isEmptyElim x

omit [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M] in
theorem metric_eq_of_isEmpty [IsEmpty M]
    (g h : Metric (I := I) (M := M)) (x : M) (u v : TangentSpace I x) :
    g.inner x u v = h.inner x u v := isEmptyElim x

/-- Existence for all smooth initial metrics and uniqueness against all strong
smooth competitors on their common half-open forward interval. -/
structure ExistenceUniquenessFamily where
  exists_solution :
    ∀ (a : ℝ) (g₀ : Metric (I := I) (M := M)), Nonempty (StrongSolution a g₀)
  unique_metric :
    ∀ (a : ℝ) (g₀ : Metric (I := I) (M := M)) (sol₁ sol₂ : StrongSolution a g₀),
      ∀ t ∈ Set.Ico a (min sol₁.terminalTime sol₂.terminalTime),
        ∀ x : M, ∀ u v : TangentSpace I x,
          (sol₁.metric t).inner x u v = (sol₂.metric t).inner x u v

/-- The degenerate empty case has an actual package, including existence. -/
theorem existenceUniquenessFamilyOfIsEmpty [IsEmpty M] :
    ExistenceUniquenessFamily (I := I) (M := M) where
  exists_solution := fun a g₀ => ⟨strongSolutionOfIsEmpty a g₀⟩
  unique_metric := fun _ _ _ _ _ _ x => isEmptyElim x

universe u v w

/-- Expected type for a separately named general target. Positive rank is
explicitly scoped. Empty manifolds are included. No solver, Ricci identity,
upstream certificate, or desired existence/uniqueness result is a premise. -/
abbrev PointFourSmoothForwardModelContract :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless],
      ExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)

end RicciFlow.SmoothForward
