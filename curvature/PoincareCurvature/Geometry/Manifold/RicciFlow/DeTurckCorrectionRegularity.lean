module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree

/-!
# Continuity of the covariant derivative of the intrinsic DeTurck vector field

The intrinsic Ricci–DeTurck reaction term is built from the *symmetrized covariant derivative* of the
intrinsic DeTurck vector field, `intrinsicDeTurckCorrection g background t x u v = (g t).inner x (∇W u) v
+ (g t).inner x u (∇W v)`, where `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g
background t)`.  Seeing this as a `ContinuousSectionSpace` value (the geometric operator `A` of the
Ricci–DeTurck chart) requires that `∇W` be a *continuous* `Hom(TM, TM)`-section for a merely-`C¹`
DeTurck vector field.

This module supplies exactly that regularity by consuming the fiber-norm-free tangent-bundle level
downgrade `CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one`
(a `C¹` covariant derivative on the tangent bundle sends a `C¹` section to a *continuous*
`Hom(TM, TM)`-section).  Because that downgrade carries **no** `Π` fiber-norm hypothesis, applying it to
`chosenLeviCivitaFamily g t` — whose `C¹` covariant-derivative class comes from
`someContMDiffLeviCivitaConnection_contMDiff` — does **not** re-trigger the transported-instance norm
diamond on `NormedAddCommGroup (TangentSpace I x)` (Riemannian vs. flat-`E`).

* `chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero` — the canonical smooth Levi-Civita slice
  is a `C⁰` covariant derivative on every open set.
* `intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero` /
  `intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero` — for a `C¹` background connection
  slice, `∇W` is a continuous `Hom(TM, TM)`-section (locally, resp. globally).
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)

/-- The canonical smooth Levi-Civita slice of a metric family is a `C⁰` covariant derivative on every
open set: it sends a `C¹` vector field to a *continuous* `Hom(TM, TM)`-section.  Obtained by feeding the
`C¹` covariant-derivative class of `chosenLeviCivitaFamily` (from
`someContMDiffLeviCivitaConnection_contMDiff`) to the fiber-norm-free tangent-bundle level downgrade. -/
theorem chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 0
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun u := by
  haveI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  exact
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      hu

/-- For a `C¹` background connection slice, the covariant derivative
`∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` of the intrinsic
DeTurck vector field is a **continuous** `Hom(TM, TM)`-section on every open set.  This is the
regularity input that lets the intrinsic Ricci–DeTurck reaction term be read as a continuous section
(a `ContinuousSectionSpace` value). -/
theorem intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {u : Set M} (hu : IsOpen u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) u := by
  have hchosen0 := chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero (I := I) (M := M) g t hu
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) :=
    intrinsicDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
      (I := I) (M := M) g background t hbackground
  exact hchosen0.contMDiff (by simpa using hW.contMDiffOn)

/-- Global version of `intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero`: for a `C¹`
background connection slice, `∇W` is a continuous `Hom(TM, TM)`-section on all of `M`. -/
theorem intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) := by
  rw [← contMDiffOn_univ]
  exact intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (I := I) (M := M) g background t hbackground isOpen_univ

end RicciFlow
