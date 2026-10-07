module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth forward metric regularity

This additive interface does not construct a general Ricci flow.
The canonical C² Point-4 contract and its completion audit are unchanged.
Chart coefficients are evaluated on every pair of fixed model vectors.
On finite-dimensional models this is the usual joint chart-Gram condition;
the finite-basis comparison with the qualified upstream API is a separate bridge.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow.SmoothForward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev Metric := Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

abbrev MetricFamily := ℝ → Metric (I := I) (M := M)

/-- Lower the spatial smoothness degree while preserving every metric component. -/
def toC2 (g : Metric (I := I) (M := M)) :
    Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _) :=
  { inner := g.inner
    symm := g.symm
    pos := g.pos
    isVonNBounded := g.isVonNBounded
    contMDiff := g.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top) }

@[simp] theorem toC2_inner (g : Metric (I := I) (M := M))
    (x : M) (u v : TangentSpace I x) :
    (toC2 g).inner x u v = g.inner x u v := rfl

/-- Metric coefficients in the actual tangent-bundle chart trivialization.
No auxiliary curvature, solver or analytic certificate is an input. -/
def chartGramComponent (g : Metric (I := I) (M := M))
    (x₀ : M) (u v : E) (x : M) : ℝ :=
  g.inner x
    ((trivializationAt E (TangentSpace I) x₀).symm x u)
    ((trivializationAt E (TangentSpace I) x₀).symm x v)

/-- Strong solution/competitor regularity, jointly in time and space, up to
the forward initial endpoint. The terminal endpoint is excluded. -/
def JointlySmoothOn (g : MetricFamily (I := I) (M := M)) (a b : ℝ) : Prop :=
  ∀ (x₀ : M) (u v : E),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => chartGramComponent (g p.1) x₀ u v p.2)
      (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

theorem JointlySmoothOn.restrict {g : MetricFamily (I := I) (M := M)}
    {a b c : ℝ} (hg : JointlySmoothOn g a b) (hc : c ≤ b) :
    JointlySmoothOn g a c := by
  intro x₀ u v
  exact (hg x₀ u v).mono
    (Set.prod_mono_left (fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 hc⟩))

theorem JointlySmoothOn.chart_continuous {g : MetricFamily (I := I) (M := M)}
    {a b : ℝ} (hg : JointlySmoothOn g a b) (x₀ : M) (u v : E) :
    ContinuousOn
      (fun p : ℝ × M => chartGramComponent (g p.1) x₀ u v p.2)
      (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
  (hg x₀ u v).continuousOn

end RicciFlow.SmoothForward
