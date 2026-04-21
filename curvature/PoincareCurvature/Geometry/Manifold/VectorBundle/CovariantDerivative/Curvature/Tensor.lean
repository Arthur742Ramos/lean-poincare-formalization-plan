module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Raw
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Tensorial curvature

This file packages the raw curvature commutator into a fibrewise multilinear map
by evaluating it on canonical smooth extensions of fibre vectors.

The smooth extensions are built from `extend` sections multiplied by a fixed
smooth bump function chosen inside the base set of `trivializationAt`. This
keeps the construction linear in the fibre input while ensuring the sections are
globally smooth enough for repeated covariant differentiation.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)

section SmoothExtend

noncomputable def smoothExtendBumpData (x : M) :
    {φ : SmoothBumpFunction I x // tsupport φ ⊆ (trivializationAt F V x).baseSet} := by
  classical
  let t := trivializationAt F V x
  have ht : t.baseSet ∈ nhds x := by
    exact t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V x)
  have hφ :
      ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ t.baseSet :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp ht
  exact ⟨Classical.choose hφ, (Classical.choose_spec hφ).2⟩

noncomputable def smoothExtendBump (x : M) : SmoothBumpFunction I x :=
  (smoothExtendBumpData (I := I) (F := F) (V := V) x).1

lemma tsupport_smoothExtendBump_subset (x : M) :
    tsupport (smoothExtendBump (I := I) (F := F) (V := V) x) ⊆
      (trivializationAt F V x).baseSet :=
  (smoothExtendBumpData (I := I) (F := F) (V := V) x).2

lemma contMDiffOn_extend_baseSet_two {x : M} (v : V x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (extend F v)) (trivializationAt F V x).baseSet := by
  let t := trivializationAt F V x
  suffices ContMDiffOn I 𝓘(ℝ, F) 2 (fun y ↦ (t ⟨y, extend F v y⟩).2) t.baseSet by
    intro y hy
    rw [t.contMDiffWithinAt_section _ hy]
    exact this y hy
  let w : F := (t ⟨x, v⟩).2
  have hw : ContMDiffOn I 𝓘(ℝ, F) 2 (fun _y ↦ w) t.baseSet := contMDiffOn_const
  exact hw.congr (fun y hy ↦ by simp [extend, t, w, hy])

lemma contMDiffOn_extend_baseSet_one {x : M} (v : V x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) 1 (T% (extend F v)) (trivializationAt F V x).baseSet :=
  (contMDiffOn_extend_baseSet_two (I := I) (F := F) (V := V) v).of_le (by simp)

lemma extend_add {x : M} (v w : V x) :
    extend F (v + w) = extend F v + extend F w := by
  let t := trivializationAt F V x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  funext y
  change (t.symmₗ ℝ y) ((t ⟨x, v + w⟩).2) =
      (t.symmₗ ℝ y) ((t ⟨x, v⟩).2) + (t.symmₗ ℝ y) ((t ⟨x, w⟩).2)
  rw [show (t ⟨x, v + w⟩).2 = (t ⟨x, v⟩).2 + (t ⟨x, w⟩).2 by
    simpa [t.coe_linearMapAt_of_mem hx] using (t.linearMapAt ℝ x).map_add v w]
  exact (t.symmₗ ℝ y).map_add _ _

lemma extend_smul {x : M} (c : ℝ) (v : V x) :
    extend F (c • v) = c • extend F v := by
  let t := trivializationAt F V x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  funext y
  change (t.symmₗ ℝ y) ((t ⟨x, c • v⟩).2) = c • (t.symmₗ ℝ y) ((t ⟨x, v⟩).2)
  have hcv : t.linearMapAt ℝ x (c • v) = (t ⟨x, c • v⟩).2 := by
    simpa using congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hx) (c • v)
  have hv : t.linearMapAt ℝ x v = (t ⟨x, v⟩).2 := by
    simpa using congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hx) v
  rw [← hcv, (t.linearMapAt ℝ x).map_smul, hv]
  exact (t.symmₗ ℝ y).map_smul c _

/-- A canonical smooth global extension of a fibre vector, linear in the fibre input. -/
noncomputable def smoothExtend
    (I : ModelWithCorners ℝ E H) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle 2 F V I]
    (x : M) (v : V x) : Π y : M, V y :=
  ((smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ) • extend F v)

lemma smoothExtend_apply (x : M) (v : V x) :
    smoothExtend (I := I) (F := F) (V := V) x v x = v := by
  simp [smoothExtend]

lemma smoothExtend_add (x : M) (v w : V x) :
    smoothExtend (I := I) (F := F) (V := V) x (v + w) =
      smoothExtend (I := I) (F := F) (V := V) x v +
        smoothExtend (I := I) (F := F) (V := V) x w := by
  funext y
  simp [smoothExtend, extend_add, smul_add]

lemma smoothExtend_smul (x : M) (c : ℝ) (v : V x) :
    smoothExtend (I := I) (F := F) (V := V) x (c • v) =
      c • smoothExtend (I := I) (F := F) (V := V) x v := by
  funext y
  simp [smoothExtend, extend_smul, smul_smul, mul_comm]

lemma smoothExtend_contMDiff_two (x : M) (v : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 2
      (fun y ↦
        TotalSpace.mk' F y (smoothExtend (I := I) (F := F) (V := V) x v y)) := by
  let φ : SmoothBumpFunction I x := smoothExtendBump (I := I) (F := F) (V := V) x
  have hφ : ContMDiff I 𝓘(ℝ) 2 (φ : M → ℝ) := by
    have hφω : ContMDiff I 𝓘(ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (φ : M → ℝ) := φ.contMDiff
    have hle : (2 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hφω.of_le hle
  have hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (extend F v))
      (trivializationAt F V x).baseSet :=
    contMDiffOn_extend_baseSet_two (I := I) (F := F) (V := V) v
  simpa [smoothExtend] using
    ContMDiffOn.smul_section_of_tsupport
      (u := (trivializationAt F V x).baseSet)
      (n := 2) (ψ := (smoothExtendBump (I := I) (F := F) (V := V) x : M → ℝ))
      hφ.contMDiffOn (trivializationAt F V x).open_baseSet
      (tsupport_smoothExtendBump_subset (I := I) (F := F) (V := V) x) hv

lemma smoothExtend_contMDiff_one (x : M) (v : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) 1
      (fun y ↦
        TotalSpace.mk' F y (smoothExtend (I := I) (F := F) (V := V) x v y)) :=
  (smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x v).of_le (by simp)

end SmoothExtend

section CurvatureTensor

variable (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]

private lemma mdifferentiableAt_along_of_contMDiff
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    MDiffAt (T% (cov.along X σ)) x := by
  exact ((cov.contMDiff_along (n := 1) hX hσ) x).mdifferentiableAt one_ne_zero

private lemma along_add_right_of_contMDiff
    {X : Π x : M, TM x} {σ τ : Π x : M, V x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
    cov.along X (σ + τ) = cov.along X σ + cov.along X τ := by
  funext z
  exact cov.along_add_right_apply (x := z) (X := X)
    ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
    ((hτ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))

private lemma along_const_smul_right_apply
    {X : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hσ : MDiffAt (T% σ) x) :
    cov.along X (c • σ) x = c • cov.along X σ x := by
  simpa using
    (cov.along_smul_right_apply (x := x) (X := X) (f := fun _ ↦ c)
      mdifferentiableAt_const hσ)

private lemma along_const_smul_right_of_contMDiff
    {X : Π x : M, TM x} {σ : Π x : M, V x} (c : ℝ)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.along X (c • σ) = c • cov.along X σ := by
  funext z
  exact cov.along_const_smul_right_apply (x := z) c
    ((hσ z).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))

private lemma curvatureAux_add_left_apply
    {X X' Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (X + X') Y σ x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X' Y σ x := by
  have hYX : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hY'X : MDiffAt (T% (cov.along X' σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX' hσ
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hX'x : MDiffAt (T% X') x := (hX' x).mdifferentiableAt one_ne_zero
  have h1 :
      cov.along (X + X') (cov.along Y σ) x =
        cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_add_left X X' (cov.along Y σ))
  have h2 :
      cov.along Y (cov.along (X + X') σ) x =
        cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x := by
    rw [cov.along_add_left]
    exact cov.along_add_right_apply (x := x) (X := Y) hYX hY'X
  have h3 :
      cov.along (VectorField.mlieBracket I (X + X') Y) σ x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X' Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_add_left hXx hX'x, map_add]
  calc
    cov.curvatureAux (X + X') Y σ x
        = cov.along (X + X') (cov.along Y σ) x -
            cov.along Y (cov.along (X + X') σ) x -
            cov.along (VectorField.mlieBracket I (X + X') Y) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X' (cov.along Y σ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y (cov.along X' σ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X' Y) σ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X' (cov.along Y σ) x - cov.along Y (cov.along X' σ) x -
          cov.along (VectorField.mlieBracket I X' Y) σ x) := by
            abel_nf
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X' Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_left_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux (c • X) Y σ x = c • cov.curvatureAux X Y σ x := by
  have hYX : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt one_ne_zero
  have hXsmul : cov.along (c • X) σ = c • cov.along X σ := by
    simpa using (cov.along_smul_left (f := fun _ ↦ c) X σ)
  have h1 :
      cov.along (c • X) (cov.along Y σ) x = c • cov.along X (cov.along Y σ) x := by
    simp [CovariantDerivative.along, map_smul]
  have h2 :
      cov.along Y (cov.along (c • X) σ) x = c • cov.along Y (cov.along X σ) x := by
    rw [hXsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYX
  have h3 :
      cov.along (VectorField.mlieBracket I (c • X) Y) σ x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_const_smul_left hXx, map_smul]
  calc
    cov.curvatureAux (c • X) Y σ x
        = cov.along (c • X) (cov.along Y σ) x -
            cov.along Y (cov.along (c • X) σ) x -
            cov.along (VectorField.mlieBracket I (c • X) Y) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_add_middle_apply
    {X Y Y' : Π x : M, TM x} {σ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y' y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (Y + Y') σ x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X Y' σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hY'σ : MDiffAt (T% (cov.along Y' σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY' hσ
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hY'x : MDiffAt (T% Y') x := (hY' x).mdifferentiableAt one_ne_zero
  have h1 :
      cov.along X (cov.along (Y + Y') σ) x =
        cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x := by
    rw [cov.along_add_left]
    exact cov.along_add_right_apply (x := x) (X := X) hYσ hY'σ
  have h2 :
      cov.along (Y + Y') (cov.along X σ) x =
        cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x := by
    simpa using congrArg (fun s => s x) (cov.along_add_left Y Y' (cov.along X σ))
  have h3 :
      cov.along (VectorField.mlieBracket I X (Y + Y')) σ x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X Y') σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_add_right hYx hY'x, map_add]
  calc
    cov.curvatureAux X (Y + Y') σ x
        = cov.along X (cov.along (Y + Y') σ) x -
            cov.along (Y + Y') (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X (Y + Y')) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X (cov.along Y' σ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y' (cov.along X σ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X Y') σ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X (cov.along Y' σ) x - cov.along Y' (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y') σ x) := by
            abel_nf
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X Y' σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_middle_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X (c • Y) σ x = c • cov.curvatureAux X Y σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt one_ne_zero
  have hYsmul : cov.along (c • Y) σ = c • cov.along Y σ := by
    simpa using (cov.along_smul_left (f := fun _ ↦ c) Y σ)
  have h1 :
      cov.along X (cov.along (c • Y) σ) x = c • cov.along X (cov.along Y σ) x := by
    rw [hYsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYσ
  have h2 :
      cov.along (c • Y) (cov.along X σ) x = c • cov.along Y (cov.along X σ) x := by
    simp [CovariantDerivative.along, map_smul]
  have h3 :
      cov.along (VectorField.mlieBracket I X (c • Y)) σ x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    simp [CovariantDerivative.along, VectorField.mlieBracket_const_smul_right hYx, map_smul]
  calc
    cov.curvatureAux X (c • Y) σ x
        = cov.along X (cov.along (c • Y) σ) x -
            cov.along (c • Y) (cov.along X σ) x -
            cov.along (VectorField.mlieBracket I X (c • Y)) σ x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_add_right_apply
    {X Y : Π x : M, TM x} {σ τ : Π x : M, V x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y)))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (τ y))) :
    cov.curvatureAux X Y (σ + τ) x =
      cov.curvatureAux X Y σ x + cov.curvatureAux X Y τ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hYτ : MDiffAt (T% (cov.along Y τ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hτ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hXτ : MDiffAt (T% (cov.along X τ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hτ
  have hYadd : cov.along Y (σ + τ) = cov.along Y σ + cov.along Y τ :=
    cov.along_add_right_of_contMDiff hσ hτ
  have hXadd : cov.along X (σ + τ) = cov.along X σ + cov.along X τ :=
    cov.along_add_right_of_contMDiff hσ hτ
  have h1 :
      cov.along X (cov.along Y (σ + τ)) x =
        cov.along X (cov.along Y σ) x + cov.along X (cov.along Y τ) x := by
    rw [hYadd]
    exact cov.along_add_right_apply (x := x) (X := X) hYσ hYτ
  have h2 :
      cov.along Y (cov.along X (σ + τ)) x =
        cov.along Y (cov.along X σ) x + cov.along Y (cov.along X τ) x := by
    rw [hXadd]
    exact cov.along_add_right_apply (x := x) (X := Y) hXσ hXτ
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) (σ + τ) x =
        cov.along (VectorField.mlieBracket I X Y) σ x +
          cov.along (VectorField.mlieBracket I X Y) τ x := by
    exact cov.along_add_right_apply (x := x) (X := VectorField.mlieBracket I X Y)
      ((hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
      ((hτ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
  calc
    cov.curvatureAux X Y (σ + τ) x
        = cov.along X (cov.along Y (σ + τ)) x -
            cov.along Y (cov.along X (σ + τ)) x -
            cov.along (VectorField.mlieBracket I X Y) (σ + τ) x := by
              simp [CovariantDerivative.curvatureAux]
    _ = (cov.along X (cov.along Y σ) x + cov.along X (cov.along Y τ) x) -
          (cov.along Y (cov.along X σ) x + cov.along Y (cov.along X τ) x) -
          (cov.along (VectorField.mlieBracket I X Y) σ x +
            cov.along (VectorField.mlieBracket I X Y) τ x) := by
              rw [h1, h2, h3]
    _ = (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) +
        (cov.along X (cov.along Y τ) x - cov.along Y (cov.along X τ) x -
          cov.along (VectorField.mlieBracket I X Y) τ x) := by
            abel_nf
    _ = cov.curvatureAux X Y σ x + cov.curvatureAux X Y τ x := by
          simp [CovariantDerivative.curvatureAux]

private lemma curvatureAux_smul_right_apply
    {X Y : Π x : M, TM x} {σ : Π x : M, V x} {x : M} (c : ℝ)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (σ y))) :
    cov.curvatureAux X Y (c • σ) x = c • cov.curvatureAux X Y σ x := by
  have hYσ : MDiffAt (T% (cov.along Y σ)) x := cov.mdifferentiableAt_along_of_contMDiff hY hσ
  have hXσ : MDiffAt (T% (cov.along X σ)) x := cov.mdifferentiableAt_along_of_contMDiff hX hσ
  have hYsmul : cov.along Y (c • σ) = c • cov.along Y σ :=
    cov.along_const_smul_right_of_contMDiff c hσ
  have hXsmul : cov.along X (c • σ) = c • cov.along X σ :=
    cov.along_const_smul_right_of_contMDiff c hσ
  have h1 :
      cov.along X (cov.along Y (c • σ)) x = c • cov.along X (cov.along Y σ) x := by
    rw [hYsmul]
    exact cov.along_const_smul_right_apply (x := x) c hYσ
  have h2 :
      cov.along Y (cov.along X (c • σ)) x = c • cov.along Y (cov.along X σ) x := by
    rw [hXsmul]
    exact cov.along_const_smul_right_apply (x := x) c hXσ
  have h3 :
      cov.along (VectorField.mlieBracket I X Y) (c • σ) x =
        c • cov.along (VectorField.mlieBracket I X Y) σ x := by
    exact cov.along_const_smul_right_apply (x := x) c
      ((hσ x).mdifferentiableAt (by simp : (2 : WithTop ℕ∞) ≠ 0))
  calc
    cov.curvatureAux X Y (c • σ) x
        = cov.along X (cov.along Y (c • σ)) x -
            cov.along Y (cov.along X (c • σ)) x -
            cov.along (VectorField.mlieBracket I X Y) (c • σ) x := by
              simp [CovariantDerivative.curvatureAux]
    _ = c • cov.along X (cov.along Y σ) x -
          c • cov.along Y (cov.along X σ) x -
          c • cov.along (VectorField.mlieBracket I X Y) σ x := by
            rw [h1, h2, h3]
    _ = c • (cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
          cov.along (VectorField.mlieBracket I X Y) σ x) := by
            rw [smul_sub, smul_sub]
    _ = c • cov.curvatureAux X Y σ x := by
          simp [CovariantDerivative.curvatureAux]

/-- The bundled curvature tensor, built from canonical smooth extensions of fibre vectors. -/
noncomputable def curvatureTensor (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] V x →ₗ[ℝ] V x := by
  refine
    { toFun := fun u ↦
        { toFun := fun v ↦
            { toFun := fun w ↦
                cov.curvatureAux
                  (smoothExtend (I := I) (F := E) (V := TM) x u)
                  (smoothExtend (I := I) (F := E) (V := TM) x v)
                  (smoothExtend (I := I) (F := F) (V := V) x w) x
              map_add' := by
                intro w w'
                simpa [smoothExtend_add] using
                  cov.curvatureAux_add_right_apply
                    (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                    (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                    (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
                    (hτ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w')
              map_smul' := by
                intro c w
                simpa [smoothExtend_smul] using
                  cov.curvatureAux_smul_right_apply c
                    (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                    (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                    (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }
          map_add' := by
            intro v v'
            ext w
            simpa [smoothExtend_add] using
              cov.curvatureAux_add_middle_apply
                (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                (hY' := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v')
                (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
          map_smul' := by
            intro c v
            ext w
            simpa [smoothExtend_smul] using
              cov.curvatureAux_smul_middle_apply c
                (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
                (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
                (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }
      map_add' := by
        intro u u'
        ext v w
        simpa [smoothExtend_add] using
          cov.curvatureAux_add_left_apply
            (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
            (hX' := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u')
            (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
            (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w)
      map_smul' := by
        intro c u
        ext v w
        simpa [smoothExtend_smul] using
          cov.curvatureAux_smul_left_apply c
            (hX := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u)
            (hY := smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x v)
            (hσ := smoothExtend_contMDiff_two (I := I) (F := F) (V := V) x w) }

@[simp]
lemma curvatureTensor_apply (x : M) (u v : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u v w =
      cov.curvatureAux
        (smoothExtend (I := I) (F := E) (V := TM) x u)
        (smoothExtend (I := I) (F := E) (V := TM) x v)
        (smoothExtend (I := I) (F := F) (V := V) x w) x := rfl

@[simp]
lemma curvatureTensor_swap (x : M) (u v : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u v w = -curvatureTensor (cov := cov) x v u w := by
  simpa [curvatureTensor_apply] using
    congrArg (fun s => s x) <| cov.curvatureAux_swap
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (Y := smoothExtend (I := I) (F := E) (V := TM) x v)
      (σ := smoothExtend (I := I) (F := F) (V := V) x w)

@[simp]
lemma curvatureTensor_self (x : M) (u : TM x) (w : V x) :
    curvatureTensor (cov := cov) x u u w = 0 := by
  simpa [curvatureTensor_apply] using
    congrArg (fun s => s x) <| cov.curvatureAux_self
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (σ := smoothExtend (I := I) (F := F) (V := V) x w)

end CurvatureTensor

end CovariantDerivative
