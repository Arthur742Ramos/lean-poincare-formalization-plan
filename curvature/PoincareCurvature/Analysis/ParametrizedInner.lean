/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smoothness of a *parametrized* fibrewise bilinear form on a vector bundle

Mathlib's `ContMDiffWithinAt.inner_bundle` proves that, on a Riemannian vector bundle, the scalar
product `⟪v m, w m⟫` of two smooth sections is smooth.  Its smoothness of the metric is supplied by
the typeclass `[IsContMDiffRiemannianBundle IB n F E]`, which fixes *one* metric on the bundle.

For a genuinely **time-dependent** metric `g_t` on the tangent bundle — the setting of Ricci flow —
that single-metric typeclass is not enough: as the time parameter varies, the fibrewise bilinear form
`g_t.inner x : E x →L[ℝ] E x →L[ℝ] ℝ` traces a family that must be controlled *jointly* in `(t, x)`.

This module records the parametrized version of `inner_bundle`, in which the fibrewise bilinear form
`g : Π y, E y →L[ℝ] E y →L[ℝ] ℝ` is supplied as an **explicit jointly-smooth section** (over a base
map `b : M → B`), rather than through the `IsContMDiffRiemannianBundle` instance.  The conclusion is
that evaluating it on two jointly-smooth sections is jointly smooth.  Instantiating the parameter
manifold `M := ℝ × M` and `b := Prod.snd` yields the joint `(t, x)` smoothness of a time-dependent
metric evaluated on fixed frame vectors — the missing input for the space-time Gram matrix used by
the Ricci–DeTurck gauge field.

The proof is exactly the internal argument of `inner_bundle` (`ContMDiffWithinAt.clm_bundle_apply₂`
into the trivial `ℝ`-bundle, then read off the fibre component), with the metric section made an
explicit hypothesis instead of extracted from the typeclass.
-/

open Manifold Bundle
open scoped Manifold Topology

namespace PoincareCurvature.ParametrizedInner

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}
  {g : ∀ y : B, E y →L[ℝ] E y →L[ℝ] ℝ}

/-- **Parametrized `inner_bundle`, within a set at a point.**  If a fibrewise bilinear form section
`g` (over a base map `b : M → B`) and two sections `v w` are all `C^n` jointly in the parameter `m`,
then the scalar `m ↦ g (b m) (v m) (w m)` is `C^n`.  This is the version of
`ContMDiffWithinAt.inner_bundle` in which the metric section is an explicit hypothesis rather than an
`IsContMDiffRiemannianBundle` instance, so it applies to a time-dependent metric. -/
lemma contMDiffWithinAt_metricSection_apply₂
    (hg : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) s x := by
  have hres : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x :=
    hg.clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [contMDiffWithinAt_totalSpace] at hres
  exact hres.2

/-- **Parametrized `inner_bundle`, at a point.** -/
lemma contMDiffAt_metricSection_apply₂
    (hg : ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) x := by
  rw [← contMDiffWithinAt_univ] at hg hv hw ⊢
  exact contMDiffWithinAt_metricSection_apply₂ hg hv hw

/-- **Parametrized `inner_bundle`, on a set.** -/
lemma contMDiffOn_metricSection_apply₂
    (hg : ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) s :=
  fun m hm ↦ contMDiffWithinAt_metricSection_apply₂ (hg m hm) (hv m hm) (hw m hm)

/-- **Parametrized `inner_bundle`, everywhere.** -/
lemma contMDiff_metricSection_apply₂
    (hg : ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))))
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) :=
  fun m ↦ contMDiffAt_metricSection_apply₂ (hg m) (hv m) (hw m)

end

end PoincareCurvature.ParametrizedInner
