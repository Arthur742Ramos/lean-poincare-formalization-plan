import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckJointFieldCompactGaugeFlow
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.DeTurckRaisedGaugeField

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.all false

/-!
# Compact gauge flow from time-dependent metric raising data

This module instantiates the joint-field compact-flow assembly with the actual
intrinsic DeTurck gauge field.  The metric-raising pipeline supplies local
joint smoothness of the raised field; the local sections are globalized over
the compact manifold, and the pointwise metric-dual identity identifies that
raised field with `intrinsicDeTurckGaugeField`.

The time-dependent smooth metric, inner-product compatibility with the
repository's `C²` metric family, and joint smoothness of the negated traced
DeTurck one-form remain explicit analytic inputs.  They are the genuine
time--space regularity boundary, not conclusions inferred from slicewise
`MetricFamily` or `ConnectionFamily` data.
-/

open scoped Manifold Topology ContDiff
open Bundle

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow
open RicciFlow.AnalyticPDE.SmoothDependenceCk
open PoincareCurvature.ParametrizedInner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Construct the compact `C³` DeTurck gauge flow from a jointly smooth
time-dependent metric raise of the actual traced DeTurck one-form.

The `C²` metric family `g` defines the intrinsic DeTurck field.  The smooth
metric family `gSmooth` is required only as a raising regularity witness and
must have the same fibrewise inner product as `g`. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_raised_intrinsicDeTurckGaugeField
    [I.Boundaryless] [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (gSmooth : ℝ → Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ E)
    (hinner : ∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
      (g t).inner x v w = (gSmooth t).inner x v w)
    (hmetric : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M =>
            (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) p.2
          ((gSmooth p.1).inner p.2)))
    (hform : ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) p.2
          (-intrinsicDeTurckOneForm (I := I) (M := M) g background p.1 p.2))) :
    ∃ ε > 0, Nonempty
      (Diffeomorph3GaugeFlowOn (I := I) (M := M)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background)
        (Set.Ioo (-ε) ε) 0) := by
  have hraisedLoc : ∀ x : M, ∃ s : Set M, IsOpen s ∧ x ∈ s ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M =>
          TotalSpace.mk' E p.2
            (@raisedGaugeField E _ _ H _ I ∞ M _ _ E _ _
              (TangentSpace I : M → Type _)
              (by exact inferInstance)
              (fun _ => by exact inferInstance)
              (fun _ => by exact inferInstance)
              (by exact TangentSpace.fiberBundle)
              (by exact TangentSpace.vectorBundle)
              (gSmooth p.1)
              (-intrinsicDeTurckOneForm (I := I) (M := M) g background p.1)
              _ _ _ bas p.2))
        (Set.univ ×ˢ s) := by
    intro x
    obtain ⟨s, hs, hxs, hcont⟩ :=
      @exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection
        E _ _ H _ I ∞ M _ _ E _ _ (TangentSpace I : M → Type _)
        (by exact inferInstance)
        (fun _ => by exact inferInstanceAs (NormedAddCommGroup E))
        (fun _ => by exact inferInstanceAs (NormedSpace ℝ E))
        (by exact TangentSpace.fiberBundle) (by exact TangentSpace.vectorBundle)
        (by exact ‹ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I›)
        gSmooth (fun t y => -intrinsicDeTurckOneForm
          (I := I) (M := M) g background t y) _ _ _ bas hmetric hform x
    exact ⟨s, hs, hxs, hcont⟩
  have hraised : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M =>
        TotalSpace.mk' E p.2
          (@raisedGaugeField E _ _ H _ I ∞ M _ _ E _ _
            (TangentSpace I : M → Type _)
            (by exact inferInstance)
            (fun _ => by exact inferInstance)
            (fun _ => by exact inferInstance)
            (by exact TangentSpace.fiberBundle)
            (by exact TangentSpace.vectorBundle)
            (gSmooth p.1)
            (-intrinsicDeTurckOneForm (I := I) (M := M) g background p.1)
            _ _ _ bas p.2)) :=
    contMDiff_of_locally_contMDiffOn_univ_prod hraisedLoc
  have hXfield : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M =>
        (⟨p.2, intrinsicDeTurckGaugeField
          (I := I) (M := M) g background p.1 p.2⟩ : TangentBundle I M)) := by
    refine hraised.congr (fun p => ?_)
    exact congrArg (fun v : TangentSpace I p.2 =>
      (⟨p.2, v⟩ : TangentBundle I M))
      (by
        simpa [intrinsicDeTurckGaugeField] using
          (neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg_of_inner_eq
            (I := I) (M := M) g gSmooth background p.1
            (fun y v w => hinner p.1 y v w) bas p.2))
  exact exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_joint_coherent_field
    (I := I) (M := M)
    (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background) hXfield

end PoincareCurvature.GaugeFlowAssembly
