module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Levi-Civita connections

This file introduces torsion-free and Levi-Civita predicates for affine connections on the tangent
bundle of a Riemannian manifold, proves uniqueness, and constructs Levi-Civita connections from an
arbitrary affine connection by the standard correction formula.

The main result is the expected uniqueness statement at the current mathlib boundary:
if two affine connections are both torsion-free and metric-compatible, then their difference
one-form vanishes.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable instance tangentSpaceFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

/-- An affine connection is torsion-free if its torsion tensor vanishes. -/
def IsTorsionFree (cov : CovariantDerivative I E TM) : Prop :=
  cov.torsion = 0

/-- Metric compatibility for an affine connection on the tangent bundle with respect to the ambient
Riemannian bundle structure. -/
def IsMetricCompatibleTangent (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        extDerivFun (fun y ↦ ⟪σ y, τ y⟫) x u =
          ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫

/-- A Levi-Civita connection is a torsion-free, metric-compatible affine connection. -/
def IsLeviCivita (cov : CovariantDerivative I E TM) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

variable {cov cov' : CovariantDerivative I E TM}

lemma difference_apply_tm (cov cov' : CovariantDerivative I E TM)
    {x : M} {σ : Π x : M, TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) :
    CovariantDerivative.difference cov cov' x (σ x) =
      (cov σ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
        (cov' σ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
  simpa [CovariantDerivative.difference] using
    (IsCovariantDerivativeOn.difference_apply
      (hcov := CovariantDerivative.isCovariantDerivativeOn cov)
      (hcov' := CovariantDerivative.isCovariantDerivativeOn cov')
      (x := x) (s := Set.univ) (hx := by trivial) (σ := σ) (hσ := hσ))

lemma difference_apply_eq_extend_tm (cov cov' : CovariantDerivative I E TM)
    {x : M} (v : TangentSpace I x) :
    CovariantDerivative.difference cov cov' x v =
      (cov (extend E v) x : TangentSpace I x →L[ℝ] TangentSpace I x) -
        (cov' (extend E v) x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
  simpa using
    (difference_apply_tm cov cov'
      (x := x) (σ := extend E v) (mdifferentiableAt_extend (I := I) (F := E) v))

lemma difference_inner_eq_neg_of_metricCompatible
    (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsMetricCompatibleTangent) (hcov' : cov'.IsMetricCompatibleTangent)
    (x : M) (u : TangentSpace I x) (v w : TangentSpace I x) :
    ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ =
      -⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ := by
  let σ : Π y : M, TangentSpace I y := extend E v
  let τ : Π y : M, TangentSpace I y := extend E w
  have hσ : MDiffAt (T% σ) x := by
    simpa [σ] using (mdifferentiableAt_extend (I := I) (F := E) v)
  have hτ : MDiffAt (T% τ) x := by
    simpa [τ] using (mdifferentiableAt_extend (I := I) (F := E) w)
  have h₁ : extDerivFun (fun y ↦ ⟪σ y, τ y⟫) x u =
      ⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫ := hcov hσ hτ u
  have h₂ : extDerivFun (fun y ↦ ⟪σ y, τ y⟫) x u =
      ⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫ := hcov' hσ hτ u
  have hsub :
      (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
        (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) = 0 := by
    linarith
  have hdiff :
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫ = 0 := by
    calc
      ⟪cov σ x u - cov' σ x u, τ x⟫ + ⟪σ x, cov τ x u - cov' τ x u⟫
          = (⟪cov σ x u, τ x⟫ + ⟪σ x, cov τ x u⟫) -
              (⟪cov' σ x u, τ x⟫ + ⟪σ x, cov' τ x u⟫) := by
            simp [inner_sub_left, inner_sub_right]
            ring
      _ = 0 := hsub
  have hsum :
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ +
          ⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ = 0 := by
    have hdiffσ := difference_apply_tm cov cov' (x := x) (σ := σ) hσ
    have hdiffτ := difference_apply_tm cov cov' (x := x) (σ := τ) hτ
    have hdiffσ' :
        CovariantDerivative.difference cov cov' x v =
          (cov σ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
            (cov' σ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
      simpa [σ] using hdiffσ
    have hdiffτ' :
        CovariantDerivative.difference cov cov' x w =
          (cov τ x : TangentSpace I x →L[ℝ] TangentSpace I x) -
            (cov' τ x : TangentSpace I x →L[ℝ] TangentSpace I x) := by
      simpa [τ] using hdiffτ
    rw [hdiffσ', hdiffτ']
    simpa [σ, τ] using hdiff
  linarith

lemma difference_symm_of_isTorsionFree (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsTorsionFree) (hcov' : cov'.IsTorsionFree)
    (x : M) (u v : TangentSpace I x) :
    (CovariantDerivative.difference cov cov' x v) u =
      (CovariantDerivative.difference cov cov' x u) v := by
  have hcov_zero : CovariantDerivative.torsion cov x u v = 0 := by
    simpa [CovariantDerivative.IsTorsionFree] using congr(($hcov x u v))
  have hcov'_zero : CovariantDerivative.torsion cov' x u v = 0 := by
    simpa [CovariantDerivative.IsTorsionFree] using congr(($hcov' x u v))
  have hcov_eq :
      cov (extend E v) x u - cov (extend E u) x v =
        VectorField.mlieBracket I (extend E u) (extend E v) x := by
    have haux :
        cov (extend E v) x u - cov (extend E u) x v -
          VectorField.mlieBracket I (extend E u) (extend E v) x = 0 := by
      simpa [hcov_zero] using (CovariantDerivative.torsion_apply_eq_extend cov (x := x) u v).symm
    exact sub_eq_zero.mp haux
  have hcov'_eq :
      cov' (extend E v) x u - cov' (extend E u) x v =
        VectorField.mlieBracket I (extend E u) (extend E v) x := by
    have haux :
        cov' (extend E v) x u - cov' (extend E u) x v -
          VectorField.mlieBracket I (extend E u) (extend E v) x = 0 := by
      simpa [hcov'_zero] using
        (CovariantDerivative.torsion_apply_eq_extend cov' (x := x) u v).symm
    exact sub_eq_zero.mp haux
  have hEq :
      cov (extend E v) x u - cov (extend E u) x v =
        cov' (extend E v) x u - cov' (extend E u) x v := by
    rw [hcov_eq, hcov'_eq]
  have hdiff :
      cov (extend E v) x u - cov' (extend E v) x u =
        cov (extend E u) x v - cov' (extend E u) x v := by
    have htmp :=
      congrArg
        (fun z ↦ z + (cov (extend E u) x v - cov' (extend E v) x u))
        hEq
    abel_nf at htmp ⊢
    exact htmp
  simpa [difference_apply_eq_extend_tm cov cov' v, difference_apply_eq_extend_tm cov cov' u]
    using hdiff

theorem difference_eq_zero_of_isLeviCivita (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita) :
    CovariantDerivative.difference cov cov' = 0 := by
  ext x v u
  apply ext_inner_right ℝ
  intro w
  have h₁ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x u v w
  have h₂ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x w u v
  have h₃ := difference_inner_eq_neg_of_metricCompatible cov cov' hcov.2 hcov'.2
    x v w u
  have hs₁ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x w u
  have hs₂ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x v w
  have hs₃ := difference_symm_of_isTorsionFree cov cov' hcov.1 hcov'.1 x u v
  have hneg :
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ =
        -⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ := by
    calc
      ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫
          = -⟪v, (CovariantDerivative.difference cov cov' x w) u⟫ := h₁
      _ = -⟪(CovariantDerivative.difference cov cov' x w) u, v⟫ := by rw [real_inner_comm]
      _ = -⟪(CovariantDerivative.difference cov cov' x u) w, v⟫ := by rw [hs₁]
      _ = ⟪u, (CovariantDerivative.difference cov cov' x v) w⟫ := by
        linarith
      _ = ⟪(CovariantDerivative.difference cov cov' x v) w, u⟫ := by rw [real_inner_comm]
      _ = ⟪(CovariantDerivative.difference cov cov' x w) v, u⟫ := by rw [hs₂]
      _ = -⟪w, (CovariantDerivative.difference cov cov' x u) v⟫ := by
        linarith
      _ = -⟪(CovariantDerivative.difference cov cov' x u) v, w⟫ := by rw [real_inner_comm]
      _ = -⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ := by rw [hs₃]
  have hzero : ⟪(CovariantDerivative.difference cov cov' x v) u, w⟫ = 0 := by
    linarith
  simpa using hzero

lemma eq_of_isLeviCivita (cov cov' : CovariantDerivative I E TM)
    (hcov : cov.IsLeviCivita) (hcov' : cov'.IsLeviCivita)
    {x : M} {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  have hdiff : CovariantDerivative.difference cov cov' = 0 :=
    difference_eq_zero_of_isLeviCivita cov cov' hcov hcov'
  have hzero : CovariantDerivative.difference cov cov' x (σ x) = 0 := by
    simpa using congr(($hdiff x (σ x)))
  have hmaps : cov σ x - cov' σ x = 0 := by
    simpa [difference_apply_tm cov cov' hσ] using hzero
  exact sub_eq_zero.mp hmaps

theorem affineConnection_nonempty [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty (CovariantDerivative I E TM) :=
  CovariantDerivative.nonempty (I := I) (F := E) (V := TM)

section Existence

variable (cov : CovariantDerivative I E TM)

noncomputable def metricDefectAux (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) :
    TangentSpace I x →L[ℝ] ℝ :=
  extDerivFun (I := I) (fun y ↦ ⟪σ y, τ y⟫) x -
    (InnerProductSpace.toDual ℝ (TangentSpace I x) (τ x)).comp (cov σ x) -
    (InnerProductSpace.toDual ℝ (TangentSpace I x) (σ x)).comp (cov τ x)

lemma metricDefectAux_apply (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) (u : TangentSpace I x) :
    metricDefectAux cov x σ τ u =
      extDerivFun (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u -
        ⟪cov σ x u, τ x⟫ - ⟪σ x, cov τ x u⟫ := by
  simp [metricDefectAux, real_inner_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma metricDefectAux_symm (cov : CovariantDerivative I E TM) (x : M)
    (σ τ : Π y : M, TangentSpace I y) :
    metricDefectAux cov x σ τ = metricDefectAux cov x τ σ := by
  ext u
  rw [metricDefectAux_apply, metricDefectAux_apply]
  simp [real_inner_comm, add_assoc, add_left_comm, add_comm]
  ring_nf

lemma mdiffAt_inner_sections {x : M}
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := by
  rcases (show IsContMDiffRiemannianBundle I 1 E TM from inferInstance).exists_contMDiff with
    ⟨g, hg, hinner⟩
  have hgAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (g y)) x := by
    exact hg.mdifferentiableAt one_ne_zero
  have happly : MDifferentiableAt I (I.prod 𝓘(ℝ))
      (fun y : M ↦ TotalSpace.mk' ℝ y (g y (σ y) (τ y))) x := by
    apply MDifferentiableAt.clm_bundle_apply₂ (IB := I) (IM := I)
      (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TM) (E₂ := TM) (E₃ := fun _ : M ↦ ℝ) (b := fun y : M ↦ y)
    · exact hgAt
    · exact hσ
    · exact hτ
  let e : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    trivializationAt ℝ (fun _ : M ↦ ℝ) x
  have hex : (TotalSpace.mk' ℝ x (g x (σ x) (τ x)) : TotalSpace ℝ (fun _ : M ↦ ℝ)) ∈ e.source := by
    simpa [e] using
      FiberBundle.mem_trivializationAt_source ℝ (fun _ : M ↦ ℝ)
        (TotalSpace.mk' ℝ x (g x (σ x) (τ x)))
  have hiff :=
    (Bundle.Trivialization.mdifferentiableAt_totalSpace_iff (IB := I) (IM := I) (e := e)
      (f := fun y : M ↦ TotalSpace.mk' ℝ y (g y (σ y) (τ y))) (x₀ := x) hex).mp happly
  simpa [e, hinner] using hiff.2

theorem metricDefectAux_tensorial_left (cov : CovariantDerivative I E TM) (x : M)
    (τ : Π y : M, TangentSpace I y) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I E (fun σ ↦ metricDefectAux cov x σ τ) x := by
  refine ⟨?_, ?_⟩
  · intro f σ hf hσ
    ext u
    have hinner : MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := mdiffAt_inner_sections (hσ := hσ) (hτ := hτ)
    have hprod :
        extDerivFun (I := I) (fun y ↦ f y * ⟪σ y, τ y⟫) x u =
          f x * extDerivFun (I := I) (fun y ↦ ⟪σ y, τ y⟫) x u +
            ⟪σ x, τ x⟫ * extDerivFun (I := I) f x u := by
      have hmul := (hf.hasMFDerivAt.mul hinner.hasMFDerivAt).mfderiv
      unfold extDerivFun
      simpa [mul_comm, mul_left_comm, mul_assoc] using congr(($hmul u))
    have hcov :=
      (CovariantDerivative.isCovariantDerivativeOn cov).leibniz hσ hf (x := x)
    have hcovu :
        cov (f • σ) x u = f x • cov σ x u + extDerivFun (I := I) f x u • σ x := by
      simpa using congr(($hcov u))
    rw [metricDefectAux_apply]
    conv_rhs =>
      rw [show (f x • cov.metricDefectAux x σ τ) u = f x * (cov.metricDefectAux x σ τ) u by rfl]
      rw [show (cov.metricDefectAux x σ τ) u = metricDefectAux cov x σ τ u by rfl]
      rw [metricDefectAux_apply]
    simp [hprod, hcovu, Pi.smul_apply, inner_add_left, real_inner_smul_left]
    ring_nf
  · intro σ σ' hσ hσ'
    ext u
    have hinnerσ : MDiffAt (fun y ↦ ⟪σ y, τ y⟫) x := mdiffAt_inner_sections (hσ := hσ) (hτ := hτ)
    have hinnerσ' : MDiffAt (fun y ↦ ⟪σ' y, τ y⟫) x :=
      mdiffAt_inner_sections (hσ := hσ') (hτ := hτ)
    have hinner :
        extDerivFun (I := I) (fun y ↦ ⟪(σ + σ') y, τ y⟫) x =
          extDerivFun (I := I) (fun y ↦ ⟪σ y, τ y⟫) x +
            extDerivFun (I := I) (fun y ↦ ⟪σ' y, τ y⟫) x := by
      have hsum :
          (fun y ↦ ⟪(σ + σ') y, τ y⟫) =
            (fun y ↦ ⟪σ y, τ y⟫) + fun y ↦ ⟪σ' y, τ y⟫ := by
        funext y
        simp [inner_add_left]
      rw [hsum, extDerivFun_add hinnerσ hinnerσ']
    have hcov :=
      (CovariantDerivative.isCovariantDerivativeOn cov).add hσ hσ' (x := x)
    rw [metricDefectAux_apply]
    rw [show (cov.metricDefectAux x σ τ + cov.metricDefectAux x σ' τ) u =
        (cov.metricDefectAux x σ τ) u + (cov.metricDefectAux x σ' τ) u by rfl]
    rw [show (cov.metricDefectAux x σ τ) u = metricDefectAux cov x σ τ u by rfl]
    rw [show (cov.metricDefectAux x σ' τ) u = metricDefectAux cov x σ' τ u by rfl]
    rw [metricDefectAux_apply, metricDefectAux_apply, hinner]
    simp [hcov, inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm]
    ring_nf

theorem metricDefectAux_tensorial_right (cov : CovariantDerivative I E TM) (x : M)
    (σ : Π y : M, TangentSpace I y) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I E (fun τ ↦ metricDefectAux cov x σ τ) x := by
  let hleft := metricDefectAux_tensorial_left cov x σ hσ
  refine ⟨?_, ?_⟩
  · intro f τ hf hτ
    calc
      metricDefectAux cov x σ (f • τ)
          = metricDefectAux cov x (f • τ) σ := by
              simpa using metricDefectAux_symm cov x σ (f • τ)
      _ = f x • metricDefectAux cov x τ σ := hleft.smul hf hτ
      _ = f x • metricDefectAux cov x σ τ := by
            rw [metricDefectAux_symm cov x τ σ]
  · intro τ τ' hτ hτ'
    calc
      metricDefectAux cov x σ (τ + τ')
          = metricDefectAux cov x (τ + τ') σ := by
              simpa using metricDefectAux_symm cov x σ (τ + τ')
      _ = metricDefectAux cov x τ σ + metricDefectAux cov x τ' σ :=
            hleft.add hτ hτ'
      _ = metricDefectAux cov x σ τ + metricDefectAux cov x σ τ' := by
            rw [metricDefectAux_symm cov x τ σ,
              metricDefectAux_symm cov x τ' σ]

/-- The pointwise metric defect of an affine connection, viewed as a trilinear map. Its arguments are
ordered as `(v, w, u)`, so `cov.metricDefect x v w u` equals the usual defect
`Dₓ(u, v, w)`. -/
noncomputable def metricDefect (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂
    (I := I) (F := E) (F' := E)
    (fun σ τ ↦ metricDefectAux cov x σ τ) x
    (fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
    (fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)

lemma metricDefect_apply (cov : CovariantDerivative I E TM) (x : M) (u v w : TangentSpace I x) :
    cov.metricDefect x v w u =
      extDerivFun (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u -
        ⟪cov (extend E v) x u, w⟫ - ⟪v, cov (extend E w) x u⟫ := by
  have h := congrArg (fun f ↦ f u)
    (TensorialAt.mkHom₂_apply_eq_extend
      (I := I) (F := E) (F' := E)
      (Φ := fun σ τ ↦ metricDefectAux cov x σ τ) (x := x)
      (hΦ₁ := fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
      (hΦ₂ := fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)
      v w)
  simpa [metricDefect, metricDefectAux_apply] using h

lemma metricDefect_apply_sections (cov : CovariantDerivative I E TM) {x : M}
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.metricDefect x (σ x) (τ x) = metricDefectAux cov x σ τ := by
  simpa [metricDefect] using
    (TensorialAt.mkHom₂_apply
      (I := I) (F := E) (F' := E)
      (Φ := fun σ τ ↦ metricDefectAux cov x σ τ) (x := x)
      (hΦ₁ := fun τ hτ ↦ metricDefectAux_tensorial_left cov x τ hτ)
      (hΦ₂ := fun σ hσ ↦ metricDefectAux_tensorial_right cov x σ hσ)
      hσ hτ)

lemma metricDefect_symm (cov : CovariantDerivative I E TM) (x : M) (v w : TangentSpace I x) :
    cov.metricDefect x v w = cov.metricDefect x w v := by
  ext u
  simp only [metricDefect_apply]
  have hext : extDerivFun (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u =
      extDerivFun (I := I) (fun y ↦ ⟪extend E w y, extend E v y⟫) x u := by
    have hswap :
        (fun y ↦ ⟪extend E v y, extend E w y⟫) =
          fun y ↦ ⟪extend E w y, extend E v y⟫ := by
      funext y
      exact real_inner_comm _ _
    rw [hswap]
  linarith [hext, real_inner_comm (cov (extend E v) x u) w,
            real_inner_comm v (cov (extend E w) x u)]

lemma isMetricCompatibleTangent_iff_metricDefect_eq_zero
    (cov : CovariantDerivative I E TM) :
    cov.IsMetricCompatibleTangent ↔
      ∀ (x : M) (v w : TangentSpace I x), cov.metricDefect x v w = 0 := by
  constructor
  · intro h x v w
    ext u
    simp only [ContinuousLinearMap.zero_apply, metricDefect_apply]
    have hcompat :=
      h (x := x) (σ := extend E v) (τ := extend E w)
        (by simpa using (mdifferentiableAt_extend (I := I) (F := E) v))
        (by simpa using (mdifferentiableAt_extend (I := I) (F := E) w))
        u
    have hcompat' : extDerivFun (I := I) (fun y ↦ ⟪extend E v y, extend E w y⟫) x u =
        ⟪cov (extend E v) x u, w⟫ + ⟪v, cov (extend E w) x u⟫ := by simpa using hcompat
    linarith
  · intro h
    intro x σ τ hσ hτ u
    have haux : metricDefectAux cov x σ τ = 0 := by
      rw [← cov.metricDefect_apply_sections (x := x) hσ hτ]
      exact h x (σ x) (τ x)
    have hauxu : metricDefectAux cov x σ τ u = 0 := by
      simpa using congr(($haux u))
    rw [metricDefectAux_apply] at hauxu
    linarith

noncomputable def correctionFunctional (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦
        LinearMap.toContinuousLinearMap
          { toFun := fun u ↦
              LinearMap.toContinuousLinearMap
                { toFun := fun w ↦
                    (cov.metricDefect x v w u + cov.metricDefect x u w v -
                        cov.metricDefect x u v w -
                        ⟪cov.torsion x u v, w⟫ + ⟪cov.torsion x v w, u⟫ -
                        ⟪cov.torsion x w u, v⟫) / 2
                  map_add' := by
                    intro w₁ w₂
                    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
                      inner_add_right, inner_add_left, add_div]
                    linarith
                  map_smul' := by
                    intro c w
                    simp only [ContinuousLinearMap.map_smulₛₗ, RingHom.id_apply,
                      ContinuousLinearMap.smul_apply, real_inner_smul_right,
                      real_inner_smul_left, smul_eq_mul, mul_div_assoc]
                    linarith }
            map_add' := by
              intro u₁ u₂
              ext w
              have hD₁ :
                  cov.metricDefect x v w (u₁ + u₂) =
                    cov.metricDefect x v w u₁ + cov.metricDefect x v w u₂ := by
                simpa using (cov.metricDefect x v w).map_add u₁ u₂
              have hD₂ :
                  cov.metricDefect x (u₁ + u₂) w v =
                    cov.metricDefect x u₁ w v + cov.metricDefect x u₂ w v := by
                simpa [ContinuousLinearMap.add_apply] using
                  congrArg (fun f ↦ f w v) ((cov.metricDefect x).map_add u₁ u₂)
              have hD₃ :
                  cov.metricDefect x (u₁ + u₂) v w =
                    cov.metricDefect x u₁ v w + cov.metricDefect x u₂ v w := by
                simpa [ContinuousLinearMap.add_apply] using
                  congrArg (fun f ↦ f v w) ((cov.metricDefect x).map_add u₁ u₂)
              have hT₁ :
                  ⟪cov.torsion x (u₁ + u₂) v, w⟫ =
                    ⟪cov.torsion x u₁ v, w⟫ + ⟪cov.torsion x u₂ v, w⟫ := by
                simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                  congrArg (fun f ↦ ⟪f v, w⟫) ((cov.torsion x).map_add u₁ u₂)
              have hT₂ :
                  ⟪cov.torsion x v w, u₁ + u₂⟫ =
                    ⟪cov.torsion x v w, u₁⟫ + ⟪cov.torsion x v w, u₂⟫ := by
                rw [inner_add_right]
              have hT₃ :
                  ⟪cov.torsion x w (u₁ + u₂), v⟫ =
                    ⟪cov.torsion x w u₁, v⟫ + ⟪cov.torsion x w u₂, v⟫ := by
                simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                  congrArg (fun z ↦ ⟪z, v⟫) ((cov.torsion x w).map_add u₁ u₂)
              simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, add_div]
              field_simp
              ring
            map_smul' := by
              intro c u
              ext w
              have hD₁ :
                  cov.metricDefect x v w (c • u) = c * cov.metricDefect x v w u := by
                simpa [smul_eq_mul, RingHom.id_apply] using
                  (cov.metricDefect x v w).map_smulₛₗ c u
              have hD₂ :
                  cov.metricDefect x (c • u) w v = c * cov.metricDefect x u w v := by
                simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ f w v) ((cov.metricDefect x).map_smulₛₗ c u)
              have hD₃ :
                  cov.metricDefect x (c • u) v w = c * cov.metricDefect x u v w := by
                simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ f v w) ((cov.metricDefect x).map_smulₛₗ c u)
              have hT₁ :
                  ⟪cov.torsion x (c • u) v, w⟫ = c * ⟪cov.torsion x u v, w⟫ := by
                simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                  smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ ⟪f v, w⟫) ((cov.torsion x).map_smulₛₗ c u)
              have hT₂ :
                  ⟪cov.torsion x v w, c • u⟫ = c * ⟪cov.torsion x v w, u⟫ := by
                simpa [smul_eq_mul] using real_inner_smul_right (cov.torsion x v w) u c
              have hT₃ :
                  ⟪cov.torsion x w (c • u), v⟫ = c * ⟪cov.torsion x w u, v⟫ := by
                simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                  smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun z ↦ ⟪z, v⟫) ((cov.torsion x w).map_smulₛₗ c u)
              simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, mul_div_assoc]
              field_simp
              ring }
      map_add' := by
        intro v₁ v₂
        ext u w
        have hD₁ :
            cov.metricDefect x (v₁ + v₂) w u =
              cov.metricDefect x v₁ w u + cov.metricDefect x v₂ w u := by
          simpa [ContinuousLinearMap.add_apply] using
            congrArg (fun f ↦ f w u) ((cov.metricDefect x).map_add v₁ v₂)
        have hD₂ :
            cov.metricDefect x u w (v₁ + v₂) =
              cov.metricDefect x u w v₁ + cov.metricDefect x u w v₂ := by
          simpa using (cov.metricDefect x u w).map_add v₁ v₂
        have hD₃ :
            cov.metricDefect x u (v₁ + v₂) w =
              cov.metricDefect x u v₁ w + cov.metricDefect x u v₂ w := by
          simpa [ContinuousLinearMap.add_apply] using
            congrArg (fun f ↦ f w) ((cov.metricDefect x u).map_add v₁ v₂)
        have hT₁ :
            ⟪cov.torsion x u (v₁ + v₂), w⟫ =
              ⟪cov.torsion x u v₁, w⟫ + ⟪cov.torsion x u v₂, w⟫ := by
          simpa [inner_add_left] using
            congrArg (fun z ↦ ⟪z, w⟫) ((cov.torsion x u).map_add v₁ v₂)
        have hT₂ :
            ⟪cov.torsion x (v₁ + v₂) w, u⟫ =
              ⟪cov.torsion x v₁ w, u⟫ + ⟪cov.torsion x v₂ w, u⟫ := by
          simpa [ContinuousLinearMap.add_apply, inner_add_left] using
            congrArg (fun f ↦ ⟪f w, u⟫) ((cov.torsion x).map_add v₁ v₂)
        have hT₃ :
            ⟪cov.torsion x w u, v₁ + v₂⟫ =
              ⟪cov.torsion x w u, v₁⟫ + ⟪cov.torsion x w u, v₂⟫ := by
          rw [inner_add_right]
        simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, add_div]
        field_simp
        ring
      map_smul' := by
        intro c v
        ext u w
        have hD₁ :
            cov.metricDefect x (c • v) w u = c * cov.metricDefect x v w u := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w u) ((cov.metricDefect x).map_smulₛₗ c v)
        have hD₂ :
            cov.metricDefect x u w (c • v) = c * cov.metricDefect x u w v := by
          simpa [smul_eq_mul, RingHom.id_apply] using
            (cov.metricDefect x u w).map_smulₛₗ c v
        have hD₃ :
            cov.metricDefect x u (c • v) w = c * cov.metricDefect x u v w := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w) ((cov.metricDefect x u).map_smulₛₗ c v)
        have hT₁ :
            ⟪cov.torsion x u (c • v), w⟫ = c * ⟪cov.torsion x u v, w⟫ := by
          simpa [real_inner_smul_left, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun z ↦ ⟪z, w⟫) ((cov.torsion x u).map_smulₛₗ c v)
        have hT₂ :
            ⟪cov.torsion x (c • v) w, u⟫ = c * ⟪cov.torsion x v w, u⟫ := by
          simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
            smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ ⟪f w, u⟫) ((cov.torsion x).map_smulₛₗ c v)
        have hT₃ :
            ⟪cov.torsion x w u, c • v⟫ = c * ⟪cov.torsion x w u, v⟫ := by
          simpa [smul_eq_mul] using real_inner_smul_right (cov.torsion x w u) v c
        simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, mul_div_assoc]
        field_simp
        ring }

noncomputable def rieszMap (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma rieszMap_apply_inner (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (w : TangentSpace I x) :
    ⟪rieszMap (I := I) x φ, w⟫ = φ w := by
  simpa [rieszMap] using InnerProductSpace.toDual_symm_apply

/-- The one-form correcting an arbitrary affine connection to the Levi-Civita connection. -/
noncomputable def leviCivitaCorrection (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ (rieszMap (I := I) x).comp (correctionFunctional cov x v)
      map_add' := by
        intro v₁ v₂
        ext u
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.map_add, map_add]
      map_smul' := by
        intro c v
        ext u
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.map_smulₛₗ, RingHom.id_apply] }

lemma leviCivitaCorrection_inner (x : M) (v u w : TangentSpace I x) :
    2 * ⟪cov.leviCivitaCorrection x v u, w⟫ =
      cov.metricDefect x v w u + cov.metricDefect x u w v - cov.metricDefect x u v w -
        ⟪cov.torsion x u v, w⟫ + ⟪cov.torsion x v w, u⟫ - ⟪cov.torsion x w u, v⟫ := by
  change 2 * ⟪rieszMap (I := I) x (correctionFunctional cov x v u), w⟫ = _
  rw [rieszMap_apply_inner]
  simp [correctionFunctional]
  ring

lemma torsion_addOneForm_apply
    (A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (u v : TangentSpace I x) :
    (cov.addOneForm A).torsion x u v =
      cov.torsion x u v + A x v u - A x u v := by
  calc
    (cov.addOneForm A).torsion x u v
        = (cov.addOneForm A) (extend E v) x u - (cov.addOneForm A) (extend E u) x v -
            VectorField.mlieBracket I (extend E u) (extend E v) x := by
              simpa using (CovariantDerivative.torsion_apply_eq_extend
                (cov := cov.addOneForm A) (x := x) u v)
    _ = cov (extend E v) x u + A x v u - (cov (extend E u) x v + A x u v) -
          VectorField.mlieBracket I (extend E u) (extend E v) x := by
            simpa [CovariantDerivative.addOneForm, sub_eq_add_neg, add_assoc,
              add_left_comm, add_comm]
    _ = (cov (extend E v) x u - cov (extend E u) x v -
          VectorField.mlieBracket I (extend E u) (extend E v) x) + A x v u - A x u v := by
          abel
    _ = cov.torsion x u v + A x v u - A x u v := by
          symm
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg (fun z ↦ z + A x v u - A x u v)
              (CovariantDerivative.torsion_apply_eq_extend (cov := cov) (x := x) u v)

lemma metricDefect_addOneForm_apply
    (A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (u v w : TangentSpace I x) :
    (cov.addOneForm A).metricDefect x v w u =
      cov.metricDefect x v w u - ⟪A x v u, w⟫ - ⟪v, A x w u⟫ := by
  rw [metricDefect_apply (cov := cov.addOneForm A), metricDefect_apply (cov := cov)]
  simp [CovariantDerivative.addOneForm, inner_add_left, inner_add_right, add_assoc,
    add_left_comm, add_comm, sub_eq_add_neg]
  ring_nf

lemma leviCivitaCorrection_sub_eq_neg_torsion (x : M)
    (u v : TangentSpace I x) :
    cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v = - cov.torsion x u v := by
  apply ext_inner_right ℝ
  intro w
  have h₁ := cov.leviCivitaCorrection_inner x v u w
  have h₂ := cov.leviCivitaCorrection_inner x u v w
  have hD :
      cov.metricDefect x u v w = cov.metricDefect x v u w := by
    simpa using congrArg (fun f ↦ f w) (cov.metricDefect_symm x u v)
  have hT₁ : ⟪cov.torsion x v u, w⟫ = -⟪cov.torsion x u v, w⟫ := by
    rw [cov.torsion_antisymm (x := x) v u]
    simp
  have hT₂ : ⟪cov.torsion x u w, v⟫ = -⟪cov.torsion x w u, v⟫ := by
    rw [cov.torsion_antisymm (x := x) u w]
    simp
  have hT₃ : ⟪cov.torsion x w v, u⟫ = -⟪cov.torsion x v w, u⟫ := by
    rw [cov.torsion_antisymm (x := x) w v]
    simp
  have hscalar :
      ⟪cov.leviCivitaCorrection x v u, w⟫ - ⟪cov.leviCivitaCorrection x u v, w⟫ =
        -⟪cov.torsion x u v, w⟫ := by
    linarith
  have hscalar' :
      ⟪cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v, w⟫ =
        -⟪cov.torsion x u v, w⟫ := by
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using hscalar
  calc
    ⟪cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v, w⟫
        = -⟪cov.torsion x u v, w⟫ := hscalar'
    _ = ⟪-cov.torsion x u v, w⟫ := by rw [inner_neg_left]

lemma correctedConnection_isTorsionFree :
    (cov.addOneForm cov.leviCivitaCorrection).IsTorsionFree := by
  unfold IsTorsionFree
  ext x u v
  rw [torsion_addOneForm_apply (A := cov.leviCivitaCorrection)]
  calc
    cov.torsion x u v + cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v
        = cov.torsion x u v +
            (cov.leviCivitaCorrection x v u - cov.leviCivitaCorrection x u v) := by
              abel
    _ = cov.torsion x u v + (-cov.torsion x u v) := by
          rw [leviCivitaCorrection_sub_eq_neg_torsion (x := x) u v]
    _ = 0 := by abel

lemma correctedConnection_metricDefect_eq_zero (x : M)
    (v w : TangentSpace I x) :
    (cov.addOneForm cov.leviCivitaCorrection).metricDefect x v w = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.zero_apply]
  have hdef := metricDefect_addOneForm_apply
    (A := cov.leviCivitaCorrection) x u v w
  have h₁ := cov.leviCivitaCorrection_inner x v u w
  have h₂ : 2 * ⟪v, cov.leviCivitaCorrection x w u⟫ =
      cov.metricDefect x w v u + cov.metricDefect x u v w - cov.metricDefect x u w v -
        ⟪cov.torsion x u w, v⟫ + ⟪cov.torsion x w v, u⟫ - ⟪cov.torsion x v u, w⟫ := by
    simpa [real_inner_comm] using cov.leviCivitaCorrection_inner x w u v
  have hD :
      cov.metricDefect x w v u = cov.metricDefect x v w u := by
    simpa using congrArg (fun f ↦ f u) (cov.metricDefect_symm x w v)
  have hT₁ : ⟪cov.torsion x u w, v⟫ = -⟪cov.torsion x w u, v⟫ := by
    rw [cov.torsion_antisymm (x := x) u w]
    simp
  have hT₂ : ⟪cov.torsion x w v, u⟫ = -⟪cov.torsion x v w, u⟫ := by
    rw [cov.torsion_antisymm (x := x) w v]
    simp
  have hT₃ : ⟪cov.torsion x v u, w⟫ = -⟪cov.torsion x u v, w⟫ := by
    rw [cov.torsion_antisymm (x := x) v u]
    simp
  have hsum :
      ⟪cov.leviCivitaCorrection x v u, w⟫ + ⟪v, cov.leviCivitaCorrection x w u⟫ =
        cov.metricDefect x v w u := by
    linarith
  rw [metricDefect_addOneForm_apply (A := cov.leviCivitaCorrection)]
  linarith

lemma correctedConnection_isMetricCompatible :
    (cov.addOneForm cov.leviCivitaCorrection).IsMetricCompatibleTangent :=
  (isMetricCompatibleTangent_iff_metricDefect_eq_zero
    (cov.addOneForm cov.leviCivitaCorrection)).mpr
    (fun x v w => cov.correctedConnection_metricDefect_eq_zero x v w)

/-- The Levi-Civita connection obtained by correcting an arbitrary affine connection. -/
noncomputable def leviCivitaConnection : CovariantDerivative I E TM :=
  cov.addOneForm cov.leviCivitaCorrection

theorem leviCivitaConnection_isLeviCivita :
    (leviCivitaConnection cov).IsLeviCivita := by
  exact ⟨cov.correctedConnection_isTorsionFree, cov.correctedConnection_isMetricCompatible⟩

end Existence

/-- The tangent bundle of a smooth finite-dimensional Riemannian manifold admits a Levi-Civita
connection. -/
theorem leviCivitaConnection_nonempty [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    Nonempty { cov : CovariantDerivative I E TM // cov.IsLeviCivita } := by
  rcases affineConnection_nonempty (I := I) (E := E) (M := M) with ⟨cov⟩
  exact ⟨⟨leviCivitaConnection cov, leviCivitaConnection_isLeviCivita cov⟩⟩

theorem exists_leviCivitaConnection [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ cov : CovariantDerivative I E TM, cov.IsLeviCivita := by
  rcases leviCivitaConnection_nonempty (I := I) (E := E) (M := M) with ⟨⟨cov, hcov⟩⟩
  exact ⟨cov, hcov⟩

end CovariantDerivative
