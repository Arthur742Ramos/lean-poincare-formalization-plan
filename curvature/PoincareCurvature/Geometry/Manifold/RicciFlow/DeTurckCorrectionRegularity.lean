module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
public import PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

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

local instance instDeTurckBilENormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance instDeTurckBilENormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

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

/-- The covariant part of the intrinsic DeTurck correction, `x ↦ (g t).inner x ∘L ∇W`, is a
continuous `BilinearFormBundle` section for a `C¹` background connection slice.  This is the
fiberwise composition of the `C²` metric section with the continuous `Hom(TM, TM)`-section `∇W`,
proved via the fiber-norm-free bundle-level `clm_bundle_comp`. -/
theorem metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (((g t).inner x).comp
          ((chosenLeviCivitaFamily (I := I) (M := M) g t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x))) := by
  have hmetric :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x ((g t).toSection x)) :=
    ((g t).contMDiff_toSection).of_le (by norm_num)
  have hW := intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (I := I) (M := M) g background t hbackground
  exact hmetric.clm_bundle_comp hW

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- Fiberwise slot-flip preserves continuity of a `BilinearFormBundle` section, fiber-norm-free.
In preferred local coordinates the flip is the fixed model slot-flip `ContinuousLinearMap.flipBilinear`,
so this mirrors `Bundle.contMDiff_symmetrizeBilinearSection` but with the flip operator and without any
`Π` fiber-norm hypothesis (the tangent-bundle readout `trivializationAt_bilinearFormBundle_apply_eq`
needs only the vector-bundle structure). -/
theorem contMDiff_flipBilinearFormSection_tangent_zero
    {s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x}
    (hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (s x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x ((s x).flip)) := by
  intro x0
  have hsx := hs x0
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
      (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := s) x0] at hsx
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
      (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := fun x ↦ (s x).flip) x0]
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 0
      (fun x ↦ ContinuousLinearMap.flipBilinear (E := E)
        ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2)) x0 := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.flipBilinear (E := E)).contMDiffAt (n := 0)).comp x0 hsx
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [((trivializationAt E TM x0).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E TM x0))] with x hx
  ext u v
  rw [ContinuousLinearMap.flipBilinear_apply_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx ((s x).flip) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx (s x) v u]
  exact ContinuousLinearMap.flip_apply (s x) _ _

/-- The intrinsic DeTurck correction, at the scalar level, is the metric-composition covariant term
`C1 = (g t).inner ∘L ∇W` symmetrized with its slot-flip: `intrinsicDeTurckCorrection = C1 + flip C1`.
Combined with the continuity of `C1`
(`metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`) and of `flip C1`
(`contMDiff_flipBilinearFormSection_tangent_zero`), this exhibits the intrinsic Ricci–DeTurck reaction
term as a sum of two continuous `BilinearFormBundle` sections. -/
lemma intrinsicDeTurckCorrection_eq_metricComp_add_flip
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v =
      (((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) u v +
      ((((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)).flip) u v := by
  simp only [intrinsicDeTurckCorrection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  congr 1
  exact (g t).symm x u _

/-- The intrinsic DeTurck correction packaged as a genuine `BilinearFormBundle` section:
`C1 + flip C1`, where `C1 = (g t).inner ∘L ∇W`.  Each summand is ascribed to the bundle-fiber type
`BilinearFormBundle (V := TM) x` (rather than the raw tangent synonym) so the section-level `+`
resolves through the vector-bundle `Add`. -/
noncomputable def intrinsicDeTurckCorrectionSection
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
  @HAdd.hAdd
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x) instHAdd
    (fun x ↦ ((g t).inner x).comp
      ((chosenLeviCivitaFamily (I := I) (M := M) g t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x))
    (fun x ↦ (((g t).inner x).comp
      ((chosenLeviCivitaFamily (I := I) (M := M) g t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)).flip)

@[simp] lemma intrinsicDeTurckCorrectionSection_apply
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x u v =
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := by
  simp only [intrinsicDeTurckCorrectionSection, Pi.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, intrinsicDeTurckCorrection_apply]
  congr 1
  exact (g t).symm x _ u

/-- The intrinsic DeTurck correction is a continuous `BilinearFormBundle` section for a `C¹`
background connection slice.  This is the symmetrized covariant part of the intrinsic Ricci–DeTurck
reaction term (`C1 + flip C1`), assembled fiber-norm-free from
`metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`,
`contMDiff_flipBilinearFormSection_tangent_zero`, and `ContMDiff.add_section`.  Reading the intrinsic
Ricci–DeTurck right-hand side as a `ContinuousSectionSpace` value (the geometric operator `A`) consumes
exactly this regularity. -/
theorem intrinsicDeTurckCorrectionSection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x)) := by
  have hC1 := metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (I := I) (M := M) g background t hbackground
  have hflip := contMDiff_flipBilinearFormSection_tangent_zero hC1
  exact hC1.add_section hflip

/-- The intrinsic Ricci–DeTurck right-hand side, packaged as a `BilinearFormBundle` section, is
`(-2) • (Ricci section) + (DeTurck correction section)`.  Given *any* continuous `BilinearFormBundle`
section `rs` representing the intrinsic Ricci tensor (`rs x u v = intrinsicRicciTensor g t x u v`), the
combination `(-2 : ℝ) • rs + intrinsicDeTurckCorrectionSection g background t` is a **continuous**
`BilinearFormBundle` section that agrees pointwise with the geometric Ricci–DeTurck operator
`intrinsicRicciDeTurckRHS`.  This assembles the geometric operator `A`'s value section out of its two
halves — the second-order Ricci part (supplied as the honest continuous-section input `rs`) and the
already-continuous lower-order DeTurck reaction term
(`intrinsicDeTurckCorrectionSection_contMDiff_zero`) — via the vector-bundle section algebra
(`ContMDiff.const_smul_section`, `ContMDiff.add_section`).  It reduces the remaining `A`-regularity
obstruction for the Ricci–DeTurck chart to the single input that the Ricci tensor is a continuous
`BilinearFormBundle` section. -/
theorem exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (rs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (hrsCont : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rs x)))
    (hrsApply : ∀ (x : M) (u v : TM x),
      rs x u v = intrinsicRicciTensor (I := I) (M := M) g t x u v) :
    ∃ rhs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x,
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rhs x)) ∧
      ∀ (x : M) (u v : TM x),
        rhs x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  have hsmul := hrsCont.const_smul_section (a := (-2 : ℝ))
  have hcont := hsmul.add_section
    (intrinsicDeTurckCorrectionSection_contMDiff_zero (I := I) (M := M) g background t hbackground)
  refine ⟨_, hcont, ?_⟩
  intro x u v
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, intrinsicDeTurckCorrectionSection_apply,
    hrsApply, intrinsicRicciDeTurckRHS_apply, intrinsicRicciFlowRHS_apply, ricciFlowRHS_apply,
    intrinsicRicciTensor_apply]

end RicciFlow
