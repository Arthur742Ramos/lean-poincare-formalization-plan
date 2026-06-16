/-
Smoothness building blocks for the variational/flow-regularity bootstrap toward
smooth dependence of ODE flows on the initial condition (roadmap point 4, Item 2).

The flow `Φ` of a `C^{n}` field `f` has spatial Jacobian `DΦ` solving the
*variational equation*, whose vector field is `w(z) = (f z.1, (Df z.1).comp z.2)`
on the augmented space `V × (V →L[ℝ] V)`. Since `Df = fderiv f` is `C^{n-1}`, the
variational field is `C^{n-1}`; applying the first-order smooth-dependence result to
it raises the flow's regularity by one. Iterating bootstraps `C¹ → C³`.

These lemmas supply the smoothness facts that drive that recursion:

* `contDiff_clm_comp` — the composition of two `C^n` operator-valued maps is `C^n`;
* `contDiff_variationalField` — the variational field inherits `C^n` from `f` and `Df`;
* `contDiff_fderiv_of_contDiff_succ` — the regularity drop `f ∈ C^{n+1} ⟹ fderiv f ∈ C^n`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Prod

open scoped Topology
open Set

namespace PoincareCurvature.VariationalSmoothness

/-- The composition of two `C^n` continuous-linear-map-valued maps is `C^n`. This is
the load-bearing smoothness fact for the variational field's linear second
component. -/
theorem contDiff_clm_comp {𝕜 X U V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {n : WithTop ℕ∞} {g : X → (V →L[𝕜] W)} {h : X → (U →L[𝕜] V)}
    (hg : ContDiff 𝕜 n g) (hh : ContDiff 𝕜 n h) :
    ContDiff 𝕜 n (fun x => (g x).comp (h x)) :=
  hg.clm_comp hh

/-- **The variational vector field inherits `C^n` smoothness.** The augmented field
`z ↦ (f z.1, (Df z.1).comp z.2)` on `V × (V →L[ℝ] V)` is `C^n` whenever `f` and `Df`
are. In the flow bootstrap one applies this with `Df = fderiv f` (which is `C^{n-1}`
when `f` is `C^n`), so the variational field is `C^{n-1}`. -/
theorem contDiff_variationalField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {f : V → V} {Df : V → (V →L[ℝ] V)}
    (hf : ContDiff ℝ n f) (hDf : ContDiff ℝ n Df) :
    ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => (f z.1, (Df z.1).comp z.2)) := by
  refine ContDiff.prodMk ?_ ?_
  · exact hf.comp contDiff_fst
  · exact (hDf.comp contDiff_fst).clm_comp contDiff_snd

/-- **Regularity drop.** The Fréchet derivative of a `C^{n+1}` map is `C^n`. This is
what makes `Df = fderiv f` available at level `n-1` when `f` is `C^n`, supplying the
input to `contDiff_variationalField` at each rung of the bootstrap. -/
theorem contDiff_fderiv_of_contDiff_succ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {f : V → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun x => fderiv ℝ f x) := by
  have hf' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by
    rwa [show ((n : WithTop ℕ∞) + 1) = ((n + 1 : ℕ) : WithTop ℕ∞) by push_cast; ring]
  exact (contDiff_succ_iff_fderiv.mp hf').2.2

/-- The variational field built from `f` and its own derivative `fderiv f` is `C^n`
when `f` is `C^{n+1}` — the precise per-rung statement of the bootstrap recursion. -/
theorem contDiff_variationalField_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {f : V → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun z : V × (V →L[ℝ] V) => (f z.1, (fderiv ℝ f z.1).comp z.2)) :=
  contDiff_variationalField (hf.of_le (by exact_mod_cast Nat.le_succ n))
    (contDiff_fderiv_of_contDiff_succ hf)

/-! ### The smooth-dependence bootstrap engine

These lemmas assemble into the recursion that proves the ODE flow map is spatially
`C^k`. The structure: the base flow paired with its Jacobian is the flow of the
augmented variational field on `V × (V →L V)`; if that augmented flow is `C^n`, its
second-component projection (the Jacobian) is `C^n`, and a flow that is differentiable
everywhere with a `C^n` Jacobian is `C^{n+1}`. Recursing from the `C¹` base case
(the variational equation, supplied by the project's variational layer) bootstraps to
any finite order. -/

/-- **C¹ packaging.** A map that is Fréchet-differentiable everywhere with a
*continuous* derivative is `C¹`. This is precisely the bridge from the project's
existing `HasFDerivAt`-of-the-flow-slice + continuous-tangent results to a `ContDiff 1`
statement the induction can consume. -/
theorem contDiff_one_of_hasFDerivAt_continuous {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {g' : V → (V →L[ℝ] W)}
    (hderiv : ∀ x, HasFDerivAt g (g' x) x) (hcont : Continuous g') :
    ContDiff ℝ 1 g := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
  have hfd : fderiv ℝ g = g' := funext fun x => (hderiv x).fderiv
  rw [hfd]
  exact hcont

/-- The Jacobian (second component of the augmented flow from initial data `(x, 1)`)
inherits the augmented flow's `C^n` smoothness. -/
theorem jacobian_contDiff_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hΨ : ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ n (fun x : V => (Ψ (x, (1 : V →L[ℝ] V)) t).2) :=
  contDiff_snd.comp (hΨ.comp (ContDiff.prodMk contDiff_id contDiff_const))

/-- The base flow (first component of the augmented flow from initial data `(x, 1)`)
inherits the augmented flow's `C^n` smoothness. -/
theorem baseFlow_contDiff_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hΨ : ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ n (fun x : V => (Ψ (x, (1 : V →L[ℝ] V)) t).1) :=
  contDiff_fst.comp (hΨ.comp (ContDiff.prodMk contDiff_id contDiff_const))

/-- **The bootstrap inductive step.** A map that is Fréchet-differentiable everywhere
with a `C^n` derivative is `C^{n+1}`. Applied with `g = x ↦ Φ_t x` and `Dg = ` the
variational Jacobian (which is `C^n` by the augmented-flow recursion), this raises the
flow's spatial regularity by one — the reusable engine of the smooth-dependence
bootstrap. -/
theorem flow_contDiff_succ_of_jacobian_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Dg : V → (V →L[ℝ] V)}
    (hderiv : ∀ x, HasFDerivAt g (Dg x) x)
    (hjac : ContDiff ℝ (n : WithTop ℕ∞) Dg) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) g := by
  have hdiff : Differentiable ℝ g := fun x => (hderiv x).differentiableAt
  have hfd : fderiv ℝ g = Dg := by funext x; exact (hderiv x).fderiv
  rw [contDiff_succ_iff_fderiv]
  refine ⟨hdiff, ?_, ?_⟩
  · intro hω; exact absurd hω (by exact_mod_cast (WithTop.natCast_ne_top n))
  · rw [hfd]; exact hjac

/-- **The full bootstrap step, assembled.** If the base flow `g` is differentiable
everywhere with Jacobian `Dg` equal to the second-component projection of a `C^n`
augmented flow `Ψ`, then `g` is `C^{n+1}`. This composes the projection lemma with the
inductive step: it reduces "flow `C^{n+1}`" to "augmented flow `C^n`", which the next
rung of the recursion (or the `C¹` base case) supplies. -/
theorem flow_contDiff_succ_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hderiv : ∀ x, HasFDerivAt g ((Ψ (x, (1 : V →L[ℝ] V)) t).2) x)
    (hΨ : ContDiff ℝ (n : WithTop ℕ∞) (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) g :=
  flow_contDiff_succ_of_jacobian_contDiff hderiv
    (jacobian_contDiff_of_augmented_flow_contDiff hΨ)

end PoincareCurvature.VariationalSmoothness
