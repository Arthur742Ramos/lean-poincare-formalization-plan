import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Headlines
import DifferentialGeometry.Geometry.Metric.Completeness

/-!
# Bonnet--Myers

This module presents the complete-metric interface to the actual comparison
proof in `DifferentialGeometry`.  The curvature term is the library's
Levi--Civita Ricci tensor, not an abstract curvature field.  The imported
proof supplies the minimizing-geodesic, second-variation, and compactness
arguments; this file only gives the focused public names used by this
repository.

The upstream proof is pinned in `lakefile.toml` to commit
`1b535dd102b94cc42b107cca27059687888f08b3`.
-/

@[expose] public noncomputable section

open Set Bundle Manifold
open scoped Bundle Manifold ContDiff ENNReal Topology

namespace BonnetMyers

open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

/-! The pointwise lower-bound predicate uses the actual Ricci tensor. -/

abbrev RicciLowerBound (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
    (I := I) g κ

/-! The input completeness assertion is completeness for the metric induced by
the supplied Riemannian metric, not completeness of an unrelated ambient
metric instance. -/

abbrev CompleteMetric (g : SmoothRiemannianMetric I M) : Prop :=
  DifferentialGeometry.RiemannianMetricComplete (I := I) g

/-!
**Bonnet--Myers diameter theorem.**  If the actual Ricci tensor satisfies
`Ric ≥ (n - 1) K g` with `K > 0`, then the induced extended metric has diameter
at most `π / √K`.

The conclusion is stated as `Metric.ediam`, the canonical extended diameter
used by Mathlib for a possibly non-finite metric diameter.  The proof itself
also establishes finiteness and compactness below.
-/
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem diameter_le
    (g : SmoothRiemannianMetric I M)
    (hcomplete : CompleteMetric (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciLowerBound (I := I) g
      (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    Metric.ediam (Set.univ : Set M) ≤
      ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_of_ricci_bound
      (I := I) (E := E) g hdim hK hRic hEnorm

/-! **Bonnet--Myers compactness theorem.** -/
theorem compactSpace
    (g : SmoothRiemannianMetric I M)
    (hcomplete : CompleteMetric (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciLowerBound (I := I) g
      (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    CompactSpace M := by
  exact DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_complete_metric
      (I := I) (E := E) g hcomplete hdim hK hRic

/-! The combined headline used by the focused entry. -/
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem bonnet_myers
    (g : SmoothRiemannianMetric I M)
    (hcomplete : CompleteMetric (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciLowerBound (I := I) g
      (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    CompactSpace M ∧
      (letI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
       letI : TopologicalSpace.MetrizableSpace M :=
        Manifold.metrizableSpace I M
       letI : T3Space M := inferInstance
       letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
       letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
       letI : PseudoEMetricSpace M :=
        (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
       letI : CompleteSpace M := hcomplete.complete
      Metric.ediam (Set.univ : Set M) ≤
        ENNReal.ofReal (Real.pi / Real.sqrt K)) := by
  exact ⟨compactSpace g hcomplete hdim hK hRic,
    diameter_le g hcomplete hdim hK hRic⟩

end BonnetMyers
