module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence

/-!
# Fiber-norm-free tangent-bundle frame covariant-derivative regularity

The frame–covariant-derivative regularity chain in `Existence.lean` (culminating in the level
downgrade `CovariantDerivative.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one`)
is stated in that file's variable context, which carries the auto-included — but genuinely *unused*
(the compiler reports them) — fiber-norm hypotheses `[∀ x, NormedAddCommGroup (V x)]` /
`[∀ x, NormedSpace ℝ (V x)]`.

To apply that chain to the geometric Ricci–DeTurck operator we need it at the **tangent bundle**
`V = TangentSpace I`.  There the *pointwise* `NormedAddCommGroup (TangentSpace I x)` is resolvable by
the bundle machinery through the synonym `TangentSpace I x = E`, but the *Π-instance*
`∀ x, NormedAddCommGroup (TangentSpace I x)` (which the `Existence` versions require, because their
building block `Bundle.Trivialization.frameCovariantDerivative` carries it in its signature) is **not**
synthesizable from the synonym.  Supplying it by hand (`RiemannianBundle`/`letI`) then yields a
defeq-but-not-syntactic diamond against the synonym norm used by the hom-bundle machinery.

This module re-establishes the frame covariant-derivative regularity **directly at the tangent
bundle**, with *no* Π fiber-norm hypothesis: it introduces a fiber-norm-free tangent-bundle copy
`frameCovariantDerivativeTangent` of `Bundle.Trivialization.frameCovariantDerivative`, and transcribes
the `smulRight`-product and frame regularity lemmas (specialized to `F = E`, `V = TangentSpace I`).
Every fiber-norm the proofs need is *pointwise* and resolves through the synonym uniformly, so no
diamond arises.  These are the fiber-norm-free building blocks the geometric-operator regularity (the
covariant derivative of a `C¹` vector field is a continuous `Hom(TM, TM)`-section) is assembled from.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TStar" => (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)

namespace CovariantDerivative

namespace TangentFrame

/-- Tangent-bundle copy of `ContinuousLinearMap.inCoordinates_smulRight_eq`. -/
lemma inCoordinates_smulRight_eq
    {x₀ x : M} {φ : TangentSpace I x →L[ℝ] ℝ} {v : TangentSpace I x}
    (hxT : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hxV : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) =
      (ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v) := by
  ext u
  have hleft :
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
          (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) u =
        ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (TotalSpace.mk' E x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := by
    simpa [ContinuousLinearMap.smulRight_apply] using congrArg (fun L : E →L[ℝ] E => L u)
      (ContinuousLinearMap.inCoordinates_eq (F := E) (E := (TangentSpace I : M → Type _))
        (F' := E) (E' := (TangentSpace I : M → Type _)) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
        (ϕ := φ.smulRight v) hxT hxV)
  have hphi :
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ u =
        φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
          hxT).symm u) := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L u)
      (ContinuousLinearMap.inCoordinates_eq (F := E) (E := (TangentSpace I : M → Type _))
        (F' := ℝ) (E' := fun _ : M ↦ ℝ) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
        (ϕ := φ) hxT (by simp))
  have hsymm :
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxT).symm u =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symm x u := by
    simpa using
      (Trivialization.symm_continuousLinearEquivAt_eq
        (e := trivializationAt E (TangentSpace I : M → Type _) x₀) (R := ℝ) (b := x) hxT u)
  let a : ℝ := φ ((trivializationAt E (TangentSpace I : M → Type _) x₀).symm x u)
  have hsmulV :
      ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x (a • v))).2 =
        a • ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x v)).2 := by
    simpa using ((trivializationAt E (TangentSpace I : M → Type _) x₀).linear (R := ℝ) hxV).map_smul a v
  calc
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) u
      = ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (TotalSpace.mk' E x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := hleft
    _ = a • ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hsymm]
          simpa [a] using hsmulV
    _ = ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ u •
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hphi, hsymm]
    _ = ((ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v)) u := by
          simp [ContinuousLinearMap.smulRight_apply]

/-- Tangent-bundle copy of `ContMDiffAt.smulRightSection_of_level`. -/
theorem contMDiffAt_smulRightSection_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, TangentSpace I x} {x₀ : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) x₀)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (v x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x))) x₀ := by
  rw [contMDiffAt_hom_bundle (IB := I) (IM := I) (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
    (F₂ := E) (E₂ := (TangentSpace I : M → Type _))
    (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x)))]
  refine ⟨contMDiffAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n
    (fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
      (TangentSpace I : M → Type _) x₀ x x₀ x ((φ x).smulRight (v x))) x₀
  let Φ : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
      x₀ x x₀ x (φ x)
  let Vc : M → E := fun x ↦
    ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x (v x))).2
  have hΦ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) n Φ x₀ := by
    simpa [Φ] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
        (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x))).mp hφ).2)
  have hxV : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hVc : ContMDiffAt I 𝓘(ℝ, E) n Vc x₀ := by
    simpa [Vc] using
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).contMDiffAt_section_iff (n := n) hxV).mp hv
  have hcoord :
      (fun x ↦
        (ContinuousLinearMap.smulRightL ℝ E E) (Φ x) (Vc x)) =ᶠ[𝓝 x₀]
      (fun x ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
          (TangentSpace I : M → Type _) x₀ x x₀ x ((φ x).smulRight (v x))) := by
    have hT :
        ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      exact (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀)
    filter_upwards [hT] with x hxT
    rw [inCoordinates_smulRight_eq (I := I) hxT hxT]
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hcoord.symm
  exact (contMDiffAt_const.clm_apply hΦ).clm_apply hVc

/-- Tangent-bundle copy of `ContMDiffOn.smulRightSection_of_level`. -/
theorem contMDiffOn_smulRightSection_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, TangentSpace I x} {s : Set M}
    (hs : IsOpen s)
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) s)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (v x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x))) s := by
  intro x hx
  exact (contMDiffAt_smulRightSection_of_level
    ((hφ x hx).contMDiffAt (hs.mem_nhds hx))
    ((hv x hx).contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

/-- Fiber-norm-free tangent-bundle copy of `Bundle.Trivialization.frameCovariantDerivative`: the
local frame–connection expression `∑ᵢ d(coeffᵢ σ) ⊗ frameᵢ`, stated directly for the tangent bundle
so that no Π fiber-norm hypothesis is needed. -/
def frameCovariantDerivativeTangent
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x ↦
    ∑ i : ι, (extDerivFun ((LinearMap.piApply (e.localFrame_coeff I b i)) σ) x).smulRight
      (e.localFrame b i x)

/-- Tangent-bundle, fiber-norm-free copy of
`Bundle.Trivialization.contMDiffOn_frameCovariantDerivative_of_level`: on a trivialization patch the
frame covariant derivative of a `C^{n+1}` vector field is a `C^n` `Hom(TM, TM)`-section. -/
theorem contMDiffOn_frameCovariantDerivativeTangent_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {σ : Π x : M, TangentSpace I x}
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun x ↦ TotalSpace.mk' E x (σ x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        (frameCovariantDerivativeTangent (I := I) e b σ x)) u := by
  classical
  simpa [frameCovariantDerivativeTangent] using
    (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦ by
      have hcoeff : ContMDiffOn I 𝓘(ℝ) (n + 1)
          ((LinearMap.piApply (e.localFrame_coeff I b i)) σ) u :=
        contMDiffOn_localFrame_coeff (I := I) (e := e) (b := b) hu hu' hσ i
      have hext : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
          (fun x ↦
            TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
              (extDerivFun ((LinearMap.piApply (e.localFrame_coeff I b i)) σ) x)) u := by
        intro x hx
        exact (((hcoeff x hx).contMDiffAt (hu.mem_nhds hx)).extDerivSection
          (I := I) (E := E) (m := n) (n := n + 1)
          (le_refl _)).contMDiffWithinAt
      have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u := by
        exact
          (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
            (n := n) (b := b) i).mono hu'
      exact contMDiffOn_smulRightSection_of_level (I := I) hu hext hframe)

/-- Tangent-bundle copy of
`CovariantDerivative.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one`: a
globally `C¹` covariant derivative on the tangent bundle restricts to a `C¹` covariant derivative on
every open set (needs no Π fiber-norm). -/
theorem contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 1 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 2 ψ := ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TangentSpace I y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u)
        (n := (2 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% τ) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (T% σ) y :=
      (((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    have hτy : MDiffAt (T% τ) y :=
      (hτ.contMDiffAt.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy (hwopen.mem_nhds hy)
      (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := THom) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

end TangentFrame

end CovariantDerivative
