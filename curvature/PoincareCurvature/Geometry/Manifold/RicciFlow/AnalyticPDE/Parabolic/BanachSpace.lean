module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Normed.Group.SeparationQuotient
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Algebra.SeparationQuotient.Section

set_option linter.unusedSectionVars false

/-!
# The parabolic `C^{0,α}` Banach space

`Parabolic/FunctionSpace.lean` exhibits the parabolic `C^{0,α}` functions on a time-space set `s` as a
**complete seminormed real vector space** (a semi-Banach space): the submodule
`parabolicC0AlphaSubmodule X E α s` carries the bundled seminormed structure
`parabolicC0AlphaSubmodule.seminormedAddCommGroup`, the completeness fact
`parabolicC0AlphaSubmodule.completeSpace`, and the scalar structure
`parabolicC0AlphaSubmodule.normedSpace`.  Those are supplied as `def`s rather than global instances
because the underlying function-space subtype already carries the *pointwise product* topology; the
seminorm topology has to live on a dedicated carrier that displaces it.

This module supplies that carrier and the resulting **genuine Banach space**.

* `ParabolicC0AlphaSpace X E α s` — a type synonym for the parabolic `C^{0,α}` submodule whose
  *canonical* `SeminormedAddCommGroup` / `NormedSpace ℝ` / `CompleteSpace` instances are the parabolic
  Hölder ones (not the ambient pointwise ones).  This is the semi-Banach space as a first-class type.
* `ParabolicC0AlphaBanach X E α s := SeparationQuotient (ParabolicC0AlphaSpace X E α s)` — the honest
  **separated** parabolic `C^{0,α}` normed space: functions modulo agreement on `s` (`‖·‖ = 0 ↔ · = 0`).
  Mathlib's separation-quotient machinery upgrades the complete seminormed structure to a genuine
  `NormedAddCommGroup` + `CompleteSpace` + `NormedSpace ℝ` — i.e. a **Banach space**.
* `ParabolicC0AlphaBanach.mk` — the quotient projection, with the norm readout
  `‖mk u‖ = parabolicC0AlphaNorm α u s`.

Everything is proved sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.  This closes
the "only point separation remains for the genuine Banach instance" gap for the parabolic Hölder
function space (the `C^0`-level function-space realisation the Ricci–DeTurck Banach chart consumes).
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- **The semi-Banach carrier of the parabolic `C^{0,α}` space.**  A type synonym for
`parabolicC0AlphaSubmodule X E α s` whose canonical topology/uniformity is the parabolic `C^{0,α}`
seminorm one, isolating it from the ambient pointwise product topology on the underlying function
subtype. -/
def ParabolicC0AlphaSpace (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Type _ :=
  parabolicC0AlphaSubmodule X E α s

namespace ParabolicC0AlphaSpace

/-- Reinterpret a parabolic `C^{0,α}` submodule element on the seminormed carrier (identity map). -/
def ofSubmodule (u : parabolicC0AlphaSubmodule X E α s) : ParabolicC0AlphaSpace X E α s := u

/-- Recover the parabolic `C^{0,α}` submodule element underneath a seminormed carrier element
(identity map). -/
def toSubmodule (u : ParabolicC0AlphaSpace X E α s) : parabolicC0AlphaSubmodule X E α s := u

/-- The underlying time-space function of a seminormed parabolic `C^{0,α}` element. -/
def toFun (u : ParabolicC0AlphaSpace X E α s) : (ℝ × X) → E := (toSubmodule u : (ℝ × X) → E)

/-- The parabolic `C^{0,α}` seminormed additive-group structure is the canonical additive-group
structure on the carrier. -/
noncomputable instance : SeminormedAddCommGroup (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.seminormedAddCommGroup (X := X) (E := E) α s

/-- The parabolic `C^{0,α}` scalar structure is the canonical `ℝ`-module normed structure on the
carrier. -/
noncomputable instance : NormedSpace ℝ (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.normedSpace (X := X) (E := E) α s

/-- With `E` complete, the parabolic `C^{0,α}` semi-normed carrier is complete: a `C^{0,α}`-Cauchy
sequence of parabolic `C^{0,α}` functions converges in the `C^{0,α}` norm. -/
instance [CompleteSpace E] : CompleteSpace (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.completeSpace (X := X) (E := E) α s

/-- The carrier norm is the parabolic `C^{0,α}` norm of the underlying function. -/
theorem norm_def (u : ParabolicC0AlphaSpace X E α s) :
    ‖u‖ = parabolicC0AlphaNorm α (toFun u) s :=
  rfl

/-- Distance on the carrier is the parabolic `C^{0,α}` norm of the pointwise difference. -/
theorem dist_def (u v : ParabolicC0AlphaSpace X E α s) :
    dist u v = parabolicC0AlphaNorm α (fun z => toFun u z - toFun v z) s :=
  parabolicC0AlphaSubmodule.seminormedAddCommGroup_dist (X := X) (E := E) α s u v

end ParabolicC0AlphaSpace

/-- **The parabolic `C^{0,α}` Banach space.**  The separation quotient of the complete seminormed
carrier `ParabolicC0AlphaSpace X E α s`: parabolic `C^{0,α}` functions on `s` identified when they
agree on `s` (equivalently, when their difference has zero parabolic `C^{0,α}` norm).  Mathlib's
`SeparationQuotient` upgrades the complete *seminormed* structure to a genuine `NormedAddCommGroup`
(point separation) while preserving completeness and the `ℝ`-vector-space structure, exhibiting the
parabolic Hölder space as an honest **Banach space**. -/
def ParabolicC0AlphaBanach (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (α : ℝ) (s : Set (ℝ × X)) : Type _ :=
  SeparationQuotient (ParabolicC0AlphaSpace X E α s)

namespace ParabolicC0AlphaBanach

/-- The genuine (separated) normed additive group structure of the parabolic `C^{0,α}` Banach space. -/
noncomputable instance : NormedAddCommGroup (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (NormedAddCommGroup (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- The parabolic `C^{0,α}` Banach space is an `ℝ`-normed vector space. -/
noncomputable instance : NormedSpace ℝ (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (NormedSpace ℝ (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- With `E` complete, the parabolic `C^{0,α}` Banach space is complete — a genuine Banach space. -/
instance [CompleteSpace E] : CompleteSpace (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (CompleteSpace (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- The Banach-space quotient projection: send a parabolic `C^{0,α}` function to its class modulo
agreement on `s`. -/
def mk (u : ParabolicC0AlphaSpace X E α s) : ParabolicC0AlphaBanach X E α s :=
  SeparationQuotient.mk u

/-- The projection is surjective. -/
theorem mk_surjective : Function.Surjective (mk : ParabolicC0AlphaSpace X E α s → _) :=
  SeparationQuotient.surjective_mk

/-- **Norm readout of the projection.**  The Banach norm of the class of `u` is the parabolic
`C^{0,α}` norm of the underlying function — the quotient is *isometric* on representatives. -/
theorem norm_mk (u : ParabolicC0AlphaSpace X E α s) :
    ‖mk u‖ = parabolicC0AlphaNorm α (ParabolicC0AlphaSpace.toFun u) s := by
  change ‖SeparationQuotient.mk u‖ = _
  rw [SeparationQuotient.norm_mk, ParabolicC0AlphaSpace.norm_def]

/-- **Norm readout on submodule representatives.**  The Banach norm of the class of a parabolic
`C^{0,α}` submodule element is the parabolic `C^{0,α}` norm of its underlying function. -/
theorem norm_mk_ofSubmodule (u : parabolicC0AlphaSubmodule X E α s) :
    ‖mk (ParabolicC0AlphaSpace.ofSubmodule u)‖ = parabolicC0AlphaNorm α (u : (ℝ × X) → E) s :=
  norm_mk (ParabolicC0AlphaSpace.ofSubmodule u)

/-- **Point separation.**  Two representatives project to the same Banach class iff their difference
has zero parabolic `C^{0,α}` norm, i.e. they agree (in the `C^{0,α}` sense) on `s`. -/
theorem mk_eq_mk_iff (u v : ParabolicC0AlphaSpace X E α s) :
    mk u = mk v ↔ parabolicC0AlphaNorm α (fun z => ParabolicC0AlphaSpace.toFun u z
        - ParabolicC0AlphaSpace.toFun v z) s = 0 := by
  change SeparationQuotient.mk u = SeparationQuotient.mk v ↔ _
  rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff, ParabolicC0AlphaSpace.dist_def]

/-- **The projection as a continuous `ℝ`-linear map.**  `mk` packaged as a bounded operator
`ParabolicC0AlphaSpace →L[ℝ] ParabolicC0AlphaBanach` (`SeparationQuotient.mkCLM`). -/
def mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s :=
  SeparationQuotient.mkCLM ℝ (ParabolicC0AlphaSpace X E α s)

@[simp]
theorem mkL_apply (u : ParabolicC0AlphaSpace X E α s) : mkL u = mk u := rfl

/-- The projection operator has operator norm `≤ 1` (it is `1`-Lipschitz; in fact norm-preserving on
representatives, `norm_mk`). -/
theorem norm_mkL_le : ‖(mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] _)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
  rw [one_mul, mkL_apply]
  exact le_of_eq (SeparationQuotient.norm_mk u)

/-- **A continuous `ℝ`-linear section of the projection.**  `SeparationQuotient.outCLM` chooses, for
each Banach class, a representative parabolic `C^{0,α}` function, continuously and linearly, with
`mk (outL x) = x`. -/
noncomputable def outL : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaSpace X E α s :=
  SeparationQuotient.outCLM ℝ (ParabolicC0AlphaSpace X E α s)

/-- The section is a right inverse of the projection: `mk (outL x) = x`. -/
@[simp]
theorem mk_outL (x : ParabolicC0AlphaBanach X E α s) : mk (outL x) = x :=
  SeparationQuotient.mk_outCLM ℝ x

/-- The projection composed with the section is the identity. -/
theorem mkL_comp_outL :
    (mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] _).comp outL = ContinuousLinearMap.id ℝ _ :=
  SeparationQuotient.mkCLM_comp_outCLM ℝ (ParabolicC0AlphaSpace X E α s)

/-- **The section is an isometry.**  `‖outL x‖ = ‖x‖`: the parabolic `C^{0,α}` norm of the chosen
representative equals the Banach norm of the class (the projection is norm-preserving, so its section
is an isometric linear embedding of the Banach space into the semi-Banach carrier). -/
theorem norm_outL (x : ParabolicC0AlphaBanach X E α s) : ‖outL x‖ = ‖x‖ := by
  conv_rhs => rw [← mk_outL x]
  exact (SeparationQuotient.norm_mk (outL x)).symm

/-- The section is injective. -/
theorem outL_injective :
    Function.Injective (outL : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaSpace X E α s) :=
  Function.LeftInverse.injective mk_outL

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
