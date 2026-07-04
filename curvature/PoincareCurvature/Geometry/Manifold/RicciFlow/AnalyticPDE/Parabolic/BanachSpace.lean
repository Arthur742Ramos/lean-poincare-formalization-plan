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

/-- **Domain monotonicity of the parabolic `C^{0,α}` norm.**  Restricting a parabolic `C^{0,α}`
function to a subset can only decrease its `C^{0,α}` norm (both the sup part and the Hölder-seminorm
part are monotone in the domain). -/
theorem parabolicC0AlphaNorm_mono_domain {u : ℝ × X → E} {s t : Set (ℝ × X)}
    (hts : t ⊆ s) (hu : ParabolicC0AlphaOn α u s) :
    parabolicC0AlphaNorm α u t ≤ parabolicC0AlphaNorm α u s :=
  add_le_add (parabolicSupNorm_mono_domain hts hu.boundedOn)
    (parabolicHolderSeminorm_mono_domain hts hu.holderOn)

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

/-- Restriction to a subset `t ⊆ s`, as a linear map on the seminormed carriers (it does not change
the underlying function, only the domain of the parabolic estimates). -/
def restrictLM {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaSpace X E α s →ₗ[ℝ] ParabolicC0AlphaSpace X E α t :=
  parabolicC0AlphaSubmodule.restrictLinearMap hts

@[simp]
theorem toFun_restrictLM {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    toFun (restrictLM hts u) = toFun u :=
  rfl

/-- **Restriction is norm-nonincreasing.**  Restriction to a subset `t ⊆ s` is a bounded linear map
of operator norm `≤ 1` on the seminormed carriers (`parabolicC0AlphaNorm_mono_domain`). -/
noncomputable def restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace X E α t :=
  LinearMap.mkContinuous (restrictLM hts) 1 (fun u => by
    rw [one_mul]
    show parabolicC0AlphaNorm α (toFun (restrictLM hts u)) t ≤ parabolicC0AlphaNorm α (toFun u) s
    rw [toFun_restrictLM]
    exact parabolicC0AlphaNorm_mono_domain hts (toSubmodule u).2)

@[simp]
theorem toFun_restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    toFun (restrictL hts u) = toFun u :=
  rfl

/-- The restriction operator on the carrier has operator norm `≤ 1`. -/
theorem norm_restrictL_le {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ‖restrictL (X := X) (E := E) (α := α) (s := s) (t := t) hts‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

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

/-- **Restriction descends to the Banach spaces.**  Restriction to a subset `t ⊆ s` — well-defined on
classes because it is norm-nonincreasing, so it sends functions that agree on `s` to functions that
agree on `t` — is a bounded operator `ParabolicC0AlphaBanach … s →L[ℝ] ParabolicC0AlphaBanach … t`
(`SeparationQuotient.liftCLM` of the composite `mk ∘ (carrier restriction)`). -/
noncomputable def restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α t :=
  SeparationQuotient.liftCLM ((mkL (s := t)).comp (ParabolicC0AlphaSpace.restrictL hts))
    (fun u u' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.restrictL hts u)
          (ParabolicC0AlphaSpace.restrictL hts u') ≤ dist u u' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        calc ‖ParabolicC0AlphaSpace.restrictL hts (u - u')‖
            ≤ ‖ParabolicC0AlphaSpace.restrictL hts‖ * ‖u - u'‖ :=
              (ParabolicC0AlphaSpace.restrictL hts).le_opNorm _
          _ ≤ 1 * ‖u - u'‖ := by
              gcongr; exact ParabolicC0AlphaSpace.norm_restrictL_le hts
          _ = ‖u - u'‖ := one_mul _
      exact le_antisymm (hle.trans h0.le) dist_nonneg)

/-- **Restriction commutes with the projection.**  On the class of a representative `u`, restriction
is the class of the restricted representative. -/
@[simp]
theorem restrictL_mk {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    restrictL hts (mk u) = mk (ParabolicC0AlphaSpace.restrictL hts u) :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The restriction operator on the Banach spaces has operator norm `≤ 1`. -/
theorem norm_restrictL_le {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ‖restrictL (X := X) (E := E) (α := α) (s := s) (t := t) hts‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [one_mul, restrictL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_restrictL]
  exact parabolicC0AlphaNorm_mono_domain hts (ParabolicC0AlphaSpace.toSubmodule u).2

end ParabolicC0AlphaBanach

namespace ParabolicC0AlphaSpace

/-- **Restriction to the full domain is the identity (pointwise).**  Restricting a carrier element
along `s ⊆ s` returns the same element (the underlying function is unchanged and the parabolic
`C^{0,α}` witness is proof-irrelevant). -/
@[simp]
theorem restrictL_self_apply (u : ParabolicC0AlphaSpace X E α s) :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s) u = u :=
  Subtype.ext rfl

/-- **Restriction is functorial (projective system), pointwise.**  Restricting a carrier element
from `s` to `t` and then to `r ⊆ t` gives the same element as restricting directly from `s` to
`r`. -/
@[simp]
theorem restrictL_comp_apply {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t)
    (u : ParabolicC0AlphaSpace X E α s) :
    restrictL hrt (restrictL hts u) = restrictL (hrt.trans hts) u :=
  Subtype.ext rfl

/-- **Restriction to the full domain is the identity operator.** -/
theorem restrictL_self :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaSpace X E α s) := by
  ext u
  simp

/-- **Restriction is functorial (projective system) at the operator level.**  The parabolic
`C^{0,α}` restriction operators form a projective system: `restrictL (r ⊆ t)` composed with
`restrictL (t ⊆ s)` is `restrictL (r ⊆ s)`. -/
theorem restrictL_comp {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t) :
    (restrictL hrt).comp (restrictL hts)
      = restrictL (X := X) (E := E) (α := α) (s := s) (hrt.trans hts) := by
  ext u
  simp

/-- **Point evaluation at a space-time point, as a linear map on the carrier.**  Reads off the value
`u z` of a parabolic `C^{0,α}` function; it is linear because the carrier's additive/scalar
operations are the pointwise ones on the underlying function (composition of the submodule inclusion
with `Pi` evaluation). -/
def evalLM (z : ℝ × X) : ParabolicC0AlphaSpace X E α s →ₗ[ℝ] E :=
  (LinearMap.proj z).comp (parabolicC0AlphaSubmodule X E α s).subtype

@[simp]
theorem evalLM_apply (z : ℝ × X) (u : ParabolicC0AlphaSpace X E α s) :
    evalLM z u = toFun u z :=
  rfl

/-- **Point evaluation at `z ∈ s` is a bounded linear functional** on the parabolic `C^{0,α}`
carrier, of operator norm `≤ 1`: the value `u z` is dominated by the parabolic `C^{0,α}` norm.  (The
sup part of the norm already controls the pointwise value on `s`.) -/
noncomputable def evalCLM (z : ℝ × X) (hz : z ∈ s) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] E :=
  LinearMap.mkContinuous (evalLM z) 1 (fun u => by
    rw [one_mul, norm_def]
    exact norm_le_parabolicC0AlphaNorm ((toSubmodule u).2).boundedOn hz)

@[simp]
theorem evalCLM_apply (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz u = toFun u z :=
  rfl

/-- **Pointwise domination for the carrier evaluation:** `‖u z‖ ≤ ‖u‖` for `z ∈ s`. -/
theorem norm_evalCLM_apply_le (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    ‖evalCLM z hz u‖ ≤ ‖u‖ := by
  rw [norm_def]
  exact norm_le_parabolicC0AlphaNorm ((toSubmodule u).2).boundedOn hz

/-- Point evaluation on the carrier has operator norm `≤ 1`. -/
theorem norm_evalCLM_le (z : ℝ × X) (hz : z ∈ s) :
    ‖evalCLM (X := X) (E := E) (α := α) (s := s) z hz‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Point evaluation is compatible with restriction (cone coherence, pointwise).**  The parabolic
`C^{0,α}` point-evaluation functionals are a compatible cone over the restriction projective system:
evaluating at `z ∈ t` after restricting to `t ⊆ s` equals evaluating at `z` on `s` (stated
pointwise; both sides read off the underlying value `u z`). -/
@[simp]
theorem evalCLM_restrictL_apply {t : Set (ℝ × X)} (hts : t ⊆ s) (z : ℝ × X) (hz : z ∈ t)
    (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (restrictL hts u) = evalCLM z (hts hz) u :=
  rfl

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Restriction to the full domain is the identity (pointwise) on the Banach space.** -/
@[simp]
theorem restrictL_self_apply (x : ParabolicC0AlphaBanach X E α s) :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s) x = x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, ParabolicC0AlphaSpace.restrictL_self_apply]

/-- **Restriction is functorial (projective system), pointwise, on the Banach space.** -/
@[simp]
theorem restrictL_comp_apply {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t)
    (x : ParabolicC0AlphaBanach X E α s) :
    restrictL hrt (restrictL hts x) = restrictL (hrt.trans hts) x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, restrictL_mk, restrictL_mk,
    ParabolicC0AlphaSpace.restrictL_comp_apply]

/-- **Restriction to the full domain is the identity operator on the Banach space.** -/
theorem restrictL_self :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaBanach X E α s) := by
  ext x
  simp

/-- **Restriction is functorial (projective system) at the operator level on the Banach space.**
The parabolic `C^{0,α}` Banach restriction operators form a projective system: `restrictL (r ⊆ t)`
composed with `restrictL (t ⊆ s)` is `restrictL (r ⊆ s)`.  This is the categorical data that gluing
of local Ricci–DeTurck Banach-chart solutions across overlapping charts (the chart-closure data)
consumes. -/
theorem restrictL_comp {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t) :
    (restrictL hrt).comp (restrictL hts)
      = restrictL (X := X) (E := E) (α := α) (s := s) (hrt.trans hts) := by
  ext x
  simp

/-- **Point evaluation at `z ∈ s` descends to the Banach space.**  Two parabolic `C^{0,α}` functions
identified in the separation quotient (they agree on `s`, having zero-norm difference) have the same
value at any `z ∈ s`, so point evaluation is well defined on classes — a bounded linear functional
`ParabolicC0AlphaBanach X E α s →L[ℝ] E` of operator norm `≤ 1`.  This is the functional that reads
off the value of a Ricci–DeTurck Banach-chart solution at a space-time point. -/
noncomputable def evalCLM (z : ℝ × X) (hz : z ∈ s) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] E :=
  SeparationQuotient.liftCLM
    (M := ParabolicC0AlphaSpace X E α s) (N := E) (R := ℝ) (S := ℝ) (σ := RingHom.id ℝ)
    (ParabolicC0AlphaSpace.evalCLM z hz)
    (fun (u u' : ParabolicC0AlphaSpace X E α s) (hins : Inseparable u u') => by
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hz0 : ‖u - u'‖ = 0 := by rw [← dist_eq_norm]; exact h0
      have hb : ‖ParabolicC0AlphaSpace.evalCLM z hz (u - u')‖ ≤ ‖u - u'‖ :=
        ParabolicC0AlphaSpace.norm_evalCLM_apply_le z hz (u - u')
      rw [hz0] at hb
      have hb0 : ParabolicC0AlphaSpace.evalCLM z hz (u - u') = 0 := norm_le_zero_iff.mp hb
      rw [map_sub, sub_eq_zero] at hb0
      exact hb0)

/-- On the class of a representative `u`, point evaluation is the value of that representative. -/
@[simp]
theorem evalCLM_mk (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (mk u) = ParabolicC0AlphaSpace.evalCLM z hz u :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The value of point evaluation on a class is the value of any representative at `z`. -/
theorem evalCLM_mk_apply (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (mk u) = ParabolicC0AlphaSpace.toFun u z :=
  rfl

/-- Point evaluation on the Banach space has operator norm `≤ 1`. -/
theorem norm_evalCLM_le (z : ℝ × X) (hz : z ∈ s) :
    ‖evalCLM (X := X) (E := E) (α := α) (s := s) z hz‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [one_mul, evalCLM_mk, norm_mk]
  exact ParabolicC0AlphaSpace.norm_evalCLM_apply_le z hz u

/-- **Point evaluation is compatible with restriction (cone coherence, pointwise) on the Banach
space.**  The parabolic `C^{0,α}` Banach point-evaluation functionals are a compatible cone over the
restriction projective system — the coherence that keeps the point-values of glued Ricci–DeTurck
Banach-chart solutions consistent across overlapping charts. -/
@[simp]
theorem evalCLM_restrictL_apply {t : Set (ℝ × X)} (hts : t ⊆ s) (z : ℝ × X) (hz : z ∈ t)
    (x : ParabolicC0AlphaBanach X E α s) :
    evalCLM z hz (restrictL hts x) = evalCLM z (hts hz) x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, evalCLM_mk, evalCLM_mk,
    ParabolicC0AlphaSpace.evalCLM_restrictL_apply]

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
