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

end PoincareCurvature.VariationalSmoothness
