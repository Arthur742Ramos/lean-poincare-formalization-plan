module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHom
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Regularity of induced hom-bundle connections

This file proves the regularity fact used by the intrinsic Hamilton--Ivey
operator: a C1 connection on each input bundle induces a C1 connection
on the hom bundle.  The proof is local and uses the actual induced-connection
product rule on local frames.

The real-line base case is proved from the manifold derivative-section theorem
and is used to build the regularity of the induced cotangent connection.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [∀ x, FiniteDimensional ℝ (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 2 F₁ V₁ I] [ContMDiffVectorBundle 2 F₂ V₂ I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "Hom₁₂" => (fun x : M => V₁ x →L[ℝ] V₂ x)

/-- The ordinary real-line connection has the regularity expected of a
C1 covariant derivative. -/
theorem contMDiffCovariantDerivative_realLine :
    ContMDiffCovariantDerivative
      (trivialCovariantDerivative (I := I) (M := M) ℝ) 1 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro σ hσ x
  have hσx : ContMDiffAt I 𝓘(ℝ) 2 (fun y => σ y) x := by
    have hσxTotal : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun y => TotalSpace.mk' ℝ y (σ y)) x := by
      simpa only [one_add_one_eq_two] using
        ((hσ x (Set.mem_univ x)).contMDiffAt
          (isOpen_univ.mem_nhds (Set.mem_univ x)))
    simpa [Bundle.Trivial.eq_trivialization, Bundle.Trivial.trivialization_apply] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).contMDiffAt_section_iff
        (n := (2 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' x)).mp hσxTotal
  simpa [trivialCovariantDerivative] using
    ((hσx.extDerivSection (E := E) (m := (1 : WithTop ℕ∞))
      (n := (2 : WithTop ℕ∞)) (by norm_num)).contMDiffWithinAt :
        ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
          (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y
            (trivialCovariantDerivative (I := I) (M := M) ℝ σ y)) Set.univ x)

set_option maxHeartbeats 3000000 in
/-- A C1 pair of bundle connections induces a C1 hom-bundle
connection. -/
theorem contMDiffCovariantDerivative_inducedHom
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    [ContMDiffCovariantDerivative cov₁ 1]
    [ContMDiffCovariantDerivative cov₂ 1] :
    ContMDiffCovariantDerivative
      (inducedHomCovariantDerivative cov₁ cov₂) 1 := by
  refine ⟨?_⟩
  refine { contMDiff := ?_ }
  intro φ hφ
  have hφOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) Set.univ := by
    simpa only [one_add_one_eq_two, contMDiffOn_univ] using hφ
  have hresult : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (F₁ →L[ℝ] F₂))) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] (F₁ →L[ℝ] F₂))
        (E := fun z : M => TangentSpace I z →L[ℝ] (V₁ z →L[ℝ] V₂ z)) y
        ((inducedHomCovariantDerivative cov₁ cov₂) φ y)) := by
    intro x
    let eT := trivializationAt E TM x
    let bT := Module.finBasis ℝ E
    let e₁ := trivializationAt F₁ V₁ x
    let b₁ := Module.finBasis ℝ F₁
    have hxT : x ∈ eT.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt E TM x
    have hx₁ : x ∈ e₁.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := TM) (E₂ := Hom₁₂) (F₂ := F₁ →L[ℝ] F₂)
      x bT ?_
    intro i
    refine contMDiffAt_homBundle_of_forall_apply_localFrame
      (IB := I) (E₁ := V₁) (E₂ := V₂) x b₁ ?_
    intro j
    let X : ∀ y : M, TM y := eT.localFrame bT i
    let Y : ∀ y : M, V₁ y := e₁.localFrame b₁ j
    have hXOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y (X y)) eT.baseSet := by
      exact (eT.contMDiffOn_localFrame_baseSet (I := I) (n := (1 : WithTop ℕ∞))
        bT i)
    have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y (X y)) x := by
      exact (hXOn x hxT).contMDiffAt (eT.open_baseSet.mem_nhds hxT)
    have hYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₁)) 2
        (fun y => TotalSpace.mk' F₁ y (Y y)) e₁.baseSet := by
      exact e₁.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞))
        b₁ j
    have hY : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 2
        (fun y => TotalSpace.mk' F₁ y (Y y)) x := by
      exact (hYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁On : ContMDiffCovariantDerivativeOn F₁ 1 cov₁.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
        e₁.open_baseSet
    have hcov₂On : ContMDiffCovariantDerivativeOn F₂ 1 cov₂.toFun e₁.baseSet :=
      contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
        e₁.open_baseSet
    have hcov₁YOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) e₁.baseSet := by
      exact hcov₁On.contMDiff hYOn
    have hcov₁Y : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₁)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₁)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₁ z) y
          (cov₁ Y y)) x := by
      exact (hcov₁YOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₁)) 1
        (fun y => TotalSpace.mk' F₁ y ((cov₁ Y y) (X y))) x := by
      exact hcov₁Y.clm_bundle_apply hX
    have hφAt : ContMDiffAt I
        (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
        (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) y (φ y)) x := by
      exact (hφOn x (Set.mem_univ x)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ x))
    have hφAt₁ := hφAt.of_le (by norm_num :
      (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
    have hφcov₁YX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 1
        (fun y => TotalSpace.mk' F₂ y (φ y ((cov₁ Y y) (X y)))) x := by
      exact hφAt₁.clm_bundle_apply hcov₁YX
    have hφYOn : ContMDiffOn I (I.prod 𝓘(ℝ, F₂)) 2
        (fun y => TotalSpace.mk' F₂ y (φ y (Y y))) e₁.baseSet := by
      intro z hz
      have hφRestrict : ContMDiffWithinAt I
          (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 2
          (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂)
            (E := Hom₁₂) y (φ y)) e₁.baseSet z := by
        exact (hφOn z (Set.mem_univ z)).mono
          (Set.subset_univ e₁.baseSet)
      exact ContMDiffWithinAt.clm_bundle_apply
        (F₁ := F₁) (F₂ := F₂) (E₁ := V₁) (E₂ := V₂)
        (b := fun w : M => w)
        hφRestrict (hYOn z hz)
    have hcov₂φYOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) e₁.baseSet := by
      exact hcov₂On.contMDiff hφYOn
    have hcov₂φY : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] F₂)
          (E := fun z : M => TangentSpace I z →L[ℝ] V₂ z) y
          (cov₂ (fun z => φ z (Y z)) y)) x := by
      exact (hcov₂φYOn x hx₁).contMDiffAt (e₁.open_baseSet.mem_nhds hx₁)
    have hcov₂φYX : ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) 1
        (fun y => TotalSpace.mk' F₂ y
          ((cov₂ (fun z => φ z (Y z)) y) (X y))) x := by
      exact hcov₂φY.clm_bundle_apply hX
    have hsum := hcov₂φYX.sub_section hφcov₁YX
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds hx₁] with y hy
    have hφy : MDiffAt
        (fun z => TotalSpace.mk' (F₁ →L[ℝ] F₂)
          (E := Hom₁₂) z (φ z)) y := by
      exact (((hφOn y (Set.mem_univ y)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ y))).mdifferentiableAt (by norm_num))
    have hYy : MDiffAt
        (fun z => TotalSpace.mk' F₁ z (Y z)) y := by
      exact ((hYOn y hy).contMDiffAt (e₁.open_baseSet.mem_nhds hy)).mdifferentiableAt
        (by norm_num)
    have hpoint := congrArg (fun q : V₂ y => TotalSpace.mk' F₂ y q)
      (inducedHomCovariantDerivative_apply_section_general
        cov₁ cov₂ hφy hYy (X y))
    simpa [X, Y] using hpoint

  simpa only [contMDiffOn_univ] using hresult

end CovariantDerivative
