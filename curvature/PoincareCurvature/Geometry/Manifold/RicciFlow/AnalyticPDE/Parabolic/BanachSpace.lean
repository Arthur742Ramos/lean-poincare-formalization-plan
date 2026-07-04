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

/-! ### Precomposition (change-of-variables) norm bounds

The operator underlying gluing across overlapping charts, the DeTurck gauge-diffeomorphism action,
and parabolic Schauder scaling is precomposition `u ↦ u ∘ φ` by a map `φ : ℝ × Y → ℝ × X` of the
space-time base.  The three lemmas below control the parabolic `C^{0,α}` norm of `u ∘ φ` when `φ`
maps `t` into `s` and expands parabolic distance by at most a factor `L`.  They are the norm-level
core the bounded precomposition operator `precompL` is built on (generalising `restrictL`, which is
the special case `φ = ` inclusion, `L = 1`). -/

/-- **Precomposition does not increase the parabolic sup norm.**  If `φ` maps `t` into `s`, then the
sup norm of `u ∘ φ` on `t` is at most the sup norm of `u` on `s`. -/
theorem parabolicSupNorm_comp_mapsTo {Y : Type*} [PseudoMetricSpace Y] {u : ℝ × X → E}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ∃ B ≥ (0 : ℝ), ParabolicBoundedWith B u s) (hmaps : Set.MapsTo φ t s) :
    parabolicSupNorm (fun p => u (φ p)) t ≤ parabolicSupNorm u s := by
  refine parabolicSupNorm_le (parabolicSupNorm_nonneg u s) ?_
  intro p hp
  exact (parabolicBoundedWith_parabolicSupNorm hu) (hmaps hp)

/-- **Precomposition scales the parabolic Hölder seminorm by `L ^ α`.**  If `φ` maps `t` into `s`
and `parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q`, then the Hölder seminorm of
`u ∘ φ` on `t` is at most `L ^ α` times the Hölder seminorm of `u` on `s`. -/
theorem parabolicHolderSeminorm_comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y]
    {L : ℝ} {u : ℝ × X → E} {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ L ^ α * parabolicHolderSeminorm α u s := by
  have hbase : ParabolicHolderWith (parabolicHolderSeminorm α u s) α u s :=
    parabolicHolderWith_parabolicHolderSeminorm hu
  have hcomp : ParabolicHolderWith (parabolicHolderSeminorm α u s * L ^ α) α
      (fun p => u (φ p)) t :=
    hbase.comp_parabolicDistanceLe (parabolicHolderSeminorm_nonneg α u s) hα hL hmaps hφ
  have hle : parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ parabolicHolderSeminorm α u s * L ^ α :=
    parabolicHolderSeminorm_le
      (mul_nonneg (parabolicHolderSeminorm_nonneg α u s) (Real.rpow_nonneg hL α)) hcomp
  exact hle.trans_eq (mul_comm _ _)

/-- **The parabolic `C^{0,α}` norm of a precomposition.**  Combining the sup and Hölder bounds:
`‖u ∘ φ‖_{C^{0,α}(t)} ≤ max 1 (L ^ α) · ‖u‖_{C^{0,α}(s)}` when `φ` maps `t` into `s` and expands
parabolic distance by at most `L`.  For a parabolic-nonexpanding change of variables (`L ≤ 1`,
`0 ≤ α`) the factor is `1`, so precomposition is norm-nonincreasing. -/
theorem parabolicC0AlphaNorm_comp_parabolicDistanceLe_le {Y : Type*} [PseudoMetricSpace Y]
    {L : ℝ} {u : ℝ × X → E} {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    parabolicC0AlphaNorm α (fun p => u (φ p)) t
      ≤ max 1 (L ^ α) * parabolicC0AlphaNorm α u s := by
  have hsup : parabolicSupNorm (fun p => u (φ p)) t ≤ parabolicSupNorm u s :=
    parabolicSupNorm_comp_mapsTo hu.boundedOn hmaps
  have hhol : parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ L ^ α * parabolicHolderSeminorm α u s :=
    parabolicHolderSeminorm_comp_parabolicDistanceLe hu.holderOn hα hL hmaps hφ
  have hBs : 0 ≤ parabolicSupNorm u s := parabolicSupNorm_nonneg u s
  have hHs : 0 ≤ parabolicHolderSeminorm α u s := parabolicHolderSeminorm_nonneg α u s
  have hmax1 : (1 : ℝ) ≤ max 1 (L ^ α) := le_max_left _ _
  have hmaxL : L ^ α ≤ max 1 (L ^ α) := le_max_right _ _
  have hsup' : parabolicSupNorm u s ≤ max 1 (L ^ α) * parabolicSupNorm u s := by
    have h := mul_le_mul_of_nonneg_right hmax1 hBs
    rwa [one_mul] at h
  have hhol' : L ^ α * parabolicHolderSeminorm α u s
      ≤ max 1 (L ^ α) * parabolicHolderSeminorm α u s :=
    mul_le_mul_of_nonneg_right hmaxL hHs
  have key : parabolicC0AlphaNorm α (fun p => u (φ p)) t
      ≤ parabolicSupNorm u s + L ^ α * parabolicHolderSeminorm α u s :=
    add_le_add hsup hhol
  refine key.trans ?_
  have hstep : parabolicSupNorm u s + L ^ α * parabolicHolderSeminorm α u s
      ≤ max 1 (L ^ α) * parabolicSupNorm u s
        + max 1 (L ^ α) * parabolicHolderSeminorm α u s := add_le_add hsup' hhol'
  refine hstep.trans_eq ?_
  unfold parabolicC0AlphaNorm
  ring

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

/-- **The point-evaluation functionals separate points of the Banach space.**  A parabolic `C^{0,α}`
Banach element is completely determined by its values at the space-time points of `s`: two classes
are equal iff they agree under every point-evaluation `evalCLM z hz` (`z ∈ s`).  Equivalently, the
Banach space is faithfully represented by the family of its values on `s` — the fact that a
Ricci–DeTurck Banach-chart solution is determined by its space-time values. -/
theorem eq_iff_forall_evalCLM (x y : ParabolicC0AlphaBanach X E α s) :
    x = y ↔ ∀ (z : ℝ × X) (hz : z ∈ s), evalCLM z hz x = evalCLM z hz y := by
  constructor
  · rintro rfl z hz; rfl
  · intro h
    obtain ⟨u, rfl⟩ := mk_surjective x
    obtain ⟨v, rfl⟩ := mk_surjective y
    have hpt : ∀ z ∈ s, ParabolicC0AlphaSpace.toFun u z = ParabolicC0AlphaSpace.toFun v z := by
      intro z hz
      have hz' := h z hz
      rwa [evalCLM_mk_apply, evalCLM_mk_apply] at hz'
    rw [mk_eq_mk_iff]
    set w : ℝ × X → E :=
      fun z => ParabolicC0AlphaSpace.toFun u z - ParabolicC0AlphaSpace.toFun v z with hw
    have hw0 : ∀ z ∈ s, w z = 0 := fun z hz => by
      simp only [hw, sub_eq_zero]; exact hpt z hz
    have hbound : ParabolicC0AlphaWith 0 0 α w s :=
      ⟨fun p hp => by simp [hw0 p hp], fun p hp q hq => by simp [hw0 p hp, hw0 q hq]⟩
    have hle : parabolicC0AlphaNorm α w s ≤ 0 := by
      simpa using parabolicC0AlphaNorm_le (le_refl 0) (le_refl 0) hbound
    exact le_antisymm hle (parabolicC0AlphaNorm_nonneg α w s)

end ParabolicC0AlphaBanach

/-- **Operator bound for fiberwise post-composition.**  Post-composing a parabolic `C^{0,α}`
function `u` with a continuous linear value map `L : E →L[ℝ] F` scales the parabolic `C^{0,α}` norm by
at most `‖L‖`: `‖L ∘ u‖_{C^{0,α}} ≤ ‖L‖ · ‖u‖_{C^{0,α}}`.  Both the sup part and the Hölder-seminorm
part scale by `‖L‖` (the operator-application closure `ParabolicC0AlphaWith.continuousLinearMap`), and
the parabolic `C^{0,α}` norm is their sum. -/
theorem parabolicC0AlphaNorm_continuousLinearMap_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {u : ℝ × X → E} (hu : ParabolicC0AlphaOn α u s) :
    parabolicC0AlphaNorm α (fun z => L (u z)) s ≤ ‖L‖ * parabolicC0AlphaNorm α u s := by
  have hself : ParabolicC0AlphaWith (parabolicSupNorm u s) (parabolicHolderSeminorm α u s) α u s :=
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu
  have hL : ParabolicC0AlphaWith (‖L‖ * parabolicSupNorm u s)
      (‖L‖ * parabolicHolderSeminorm α u s) α (fun z => L (u z)) s :=
    hself.continuousLinearMap L
  have hbound := parabolicC0AlphaNorm_le
    (mul_nonneg (norm_nonneg L) (parabolicSupNorm_nonneg u s))
    (mul_nonneg (norm_nonneg L) (parabolicHolderSeminorm_nonneg α u s)) hL
  refine hbound.trans (le_of_eq ?_)
  rw [parabolicC0AlphaNorm]; ring

namespace ParabolicC0AlphaSpace

/-- **Fiberwise post-composition with a continuous linear value map, on the seminormed carrier.**
Sends a parabolic `C^{0,α}` function `u` to `z ↦ L (u z)`, as an `ℝ`-linear map of the carriers
(reuses `parabolicC0AlphaSubmodule.continuousLinearMap`). -/
def compLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaSpace X E α s →ₗ[ℝ] ParabolicC0AlphaSpace X F α s :=
  parabolicC0AlphaSubmodule.continuousLinearMap L

@[simp]
theorem toFun_compLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (compLM L u) = fun z => L (toFun u z) :=
  rfl

/-- **Fiberwise post-composition is a bounded operator of norm `≤ ‖L‖` on the carriers.**  Applying a
continuous linear value map `L : E →L[ℝ] F` pointwise to a parabolic `C^{0,α}` function is a bounded
`ℝ`-linear map `ParabolicC0AlphaSpace … E … →L[ℝ] ParabolicC0AlphaSpace … F …` of operator norm
`≤ ‖L‖` (`parabolicC0AlphaNorm_continuousLinearMap_le`). -/
noncomputable def compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace X F α s :=
  LinearMap.mkContinuous (compLM L) ‖L‖ (fun u => by
    show parabolicC0AlphaNorm α (fun z => L (toFun u z)) s ≤ ‖L‖ * parabolicC0AlphaNorm α (toFun u) s
    exact parabolicC0AlphaNorm_continuousLinearMap_le L (toSubmodule u).2)

@[simp]
theorem toFun_compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (compL L u) = fun z => L (toFun u z) :=
  rfl

/-- The carrier post-composition operator has operator norm `≤ ‖L‖`. -/
theorem norm_compL_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ‖compL (X := X) (E := E) (α := α) (s := s) (F := F) L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Fiberwise post-composition descends to the Banach spaces.**  Applying a continuous linear value
map `L : E →L[ℝ] F` pointwise is well defined on Banach classes — it is `‖L‖`-Lipschitz, so it sends
functions that agree on `s` to functions that agree on `s` — giving a bounded operator
`ParabolicC0AlphaBanach … E … →L[ℝ] ParabolicC0AlphaBanach … F …`
(`SeparationQuotient.liftCLM` of `mk ∘ (carrier post-composition)`).  This is the functional-analytic
operation of applying a fiberwise bundle morphism / coordinate change to a Ricci–DeTurck Banach-chart
solution. -/
noncomputable def compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X F α s :=
  SeparationQuotient.liftCLM (mkL.comp (ParabolicC0AlphaSpace.compL L))
    (fun u u' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.compL L u) (ParabolicC0AlphaSpace.compL L u')
          ≤ ‖L‖ * dist u u' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        calc ‖ParabolicC0AlphaSpace.compL L (u - u')‖
            ≤ ‖ParabolicC0AlphaSpace.compL L‖ * ‖u - u'‖ :=
              (ParabolicC0AlphaSpace.compL L).le_opNorm _
          _ ≤ ‖L‖ * ‖u - u'‖ := by
              gcongr; exact ParabolicC0AlphaSpace.norm_compL_le L
      exact le_antisymm (hle.trans (le_of_eq (by rw [h0, mul_zero]))) dist_nonneg)

/-- **Post-composition commutes with the projection.**  On the class of a representative `u`,
post-composition is the class of the post-composed representative. -/
@[simp]
theorem compL_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    compL L (mk u) = mk (ParabolicC0AlphaSpace.compL L u) :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The Banach post-composition operator has operator norm `≤ ‖L‖`. -/
theorem norm_compL_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ‖compL (X := X) (E := E) (α := α) (s := s) (F := F) L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [compL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_compL]
  exact parabolicC0AlphaNorm_continuousLinearMap_le L (ParabolicC0AlphaSpace.toSubmodule u).2

/-- **Point evaluation of a post-composed class is the value map applied to the point value (cone
coherence with the fiber map).**  Reading off the space-time value of a Ricci–DeTurck chart solution
after applying a fiberwise bundle morphism `L` is `L` applied to the value of the original solution. -/
@[simp]
theorem evalCLM_compL_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (z : ℝ × X) (hz : z ∈ s) (x : ParabolicC0AlphaBanach X E α s) :
    evalCLM z hz (compL L x) = L (evalCLM z hz x) := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  simp only [compL_mk, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_compL]

/-- **Post-composition by the identity is the identity operator.** -/
theorem compL_id :
    compL (X := X) (E := E) (α := α) (s := s) (ContinuousLinearMap.id ℝ E)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaBanach X E α s) := by
  ext x
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.id_apply, compL_mk]
  rfl

/-- **Post-composition is functorial in the value map (composition).**  Applying `L₂ ∘ L₁` fiberwise
is applying `L₁` and then `L₂` — the parabolic `C^{0,α}` Banach post-composition operators form a
covariant functor of the value space. -/
theorem compL_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L₂ : F →L[ℝ] G) (L₁ : E →L[ℝ] F) :
    compL (X := X) (α := α) (s := s) (L₂.comp L₁)
      = (compL L₂).comp (compL L₁) := by
  ext x
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.comp_apply, compL_mk, compL_mk, compL_mk]
  rfl

end ParabolicC0AlphaBanach

/-- **Self-bound: the parabolic `C^{0,α}` norm is an admissible `ParabolicC0AlphaNormLe` bound.**  Its
own sup norm and Hölder seminorm are simultaneously achieved (`parabolicC0AlphaWith_parabolicSupNorm_…`)
and sum to the parabolic `C^{0,α}` norm. -/
theorem parabolicC0AlphaNormLe_norm {u : ℝ × X → E} (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaNormLe (parabolicC0AlphaNorm α u s) α u s :=
  ⟨parabolicSupNorm u s, parabolicSupNorm_nonneg u s,
    parabolicHolderSeminorm α u s, parabolicHolderSeminorm_nonneg α u s, le_of_eq rfl,
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu⟩

/-- **`ParabolicC0AlphaNormLe` dominates the parabolic `C^{0,α}` norm.**  Any admissible combined bound
`N` is at least the parabolic `C^{0,α}` norm. -/
theorem parabolicC0AlphaNorm_le_of_normLe {N : ℝ} {u : ℝ × X → E}
    (h : ParabolicC0AlphaNormLe N α u s) : parabolicC0AlphaNorm α u s ≤ N := by
  obtain ⟨B, hB, H, hH, hsum, hctrl⟩ := h
  exact (parabolicC0AlphaNorm_le hB hH hctrl).trans hsum

/-- **Bilinear multiplication bound.**  For a continuous bilinear map `L : E →L[ℝ] F →L[ℝ] G`, the
pointwise product `z ↦ L (a z) (v z)` obeys the parabolic `C^{0,α}` algebra estimate
`‖L(a,v)‖_{C^{0,α}} ≤ ‖L‖ · ‖a‖_{C^{0,α}} · ‖v‖_{C^{0,α}}` (the operator form of the parabolic
`C^{0,α}` product inequality that a Ricci–DeTurck coefficient multiplication consumes). -/
theorem parabolicC0AlphaNorm_continuousLinearMap₂_le {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    {a : ℝ × X → E} {v : ℝ × X → F} (ha : ParabolicC0AlphaOn α a s) (hv : ParabolicC0AlphaOn α v s) :
    parabolicC0AlphaNorm α (fun z => L (a z) (v z)) s
      ≤ ‖L‖ * parabolicC0AlphaNorm α a s * parabolicC0AlphaNorm α v s :=
  parabolicC0AlphaNorm_le_of_normLe
    ((parabolicC0AlphaNormLe_norm ha).continuousLinearMap₂ L (parabolicC0AlphaNormLe_norm hv))

namespace parabolicC0AlphaSubmodule

/-- **Frozen-coefficient bilinear multiplication as a linear map on the submodules.**  For a fixed
parabolic `C^{0,α}` coefficient field `a` and a continuous bilinear map `L`, the assignment
`v ↦ (z ↦ L (a z) (v z))` is an `ℝ`-linear map of parabolic `C^{0,α}` submodules (linear in the second
argument, the closure coming from `ParabolicC0AlphaOn.continuousLinearMap₂`). -/
def continuousLinearMap₂Coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : parabolicC0AlphaSubmodule X E α s) :
    parabolicC0AlphaSubmodule X F α s →ₗ[ℝ] parabolicC0AlphaSubmodule X G α s where
  toFun v := ⟨fun z => L (a z) (v z), a.2.continuousLinearMap₂ L v.2⟩
  map_add' v w := by
    ext z
    simp
  map_smul' c v := by
    ext z
    simp

@[simp]
theorem continuousLinearMap₂Coeff_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : parabolicC0AlphaSubmodule X E α s) (v : parabolicC0AlphaSubmodule X F α s) (z : ℝ × X) :
    continuousLinearMap₂Coeff (X := X) (E := E) (α := α) (s := s) L a v z = L (a z) (v z) :=
  rfl

end parabolicC0AlphaSubmodule

namespace ParabolicC0AlphaSpace

/-- Frozen-coefficient multiplication `v ↦ (z ↦ L (a z) (v z))` on the seminormed carriers. -/
def mulCoeffLM {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaSpace X F α s →ₗ[ℝ] ParabolicC0AlphaSpace X G α s :=
  parabolicC0AlphaSubmodule.continuousLinearMap₂Coeff L (toSubmodule a)

@[simp]
theorem toFun_mulCoeffLM {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    toFun (mulCoeffLM L a v) = fun z => L (toFun a z) (toFun v z) :=
  rfl

/-- **Frozen-coefficient multiplication is a bounded operator of norm `≤ ‖L‖ · ‖a‖` on the carriers.**
For a fixed parabolic `C^{0,α}` coefficient field `a`, multiplication `v ↦ (z ↦ L (a z) (v z))` by a
continuous bilinear map `L` is a bounded `ℝ`-linear map with operator norm `≤ ‖L‖ · ‖a‖` — the
frozen-coefficient linear operator at the heart of parabolic Schauder theory. -/
noncomputable def mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaSpace X F α s →L[ℝ] ParabolicC0AlphaSpace X G α s :=
  LinearMap.mkContinuous (mulCoeffLM L a) (‖L‖ * ‖a‖) (fun v => by
    show parabolicC0AlphaNorm α (fun z => L (toFun a z) (toFun v z)) s
        ≤ ‖L‖ * parabolicC0AlphaNorm α (toFun a) s * parabolicC0AlphaNorm α (toFun v) s
    exact parabolicC0AlphaNorm_continuousLinearMap₂_le L (toSubmodule a).2 (toSubmodule v).2)

@[simp]
theorem toFun_mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    toFun (mulCoeffL L a v) = fun z => L (toFun a z) (toFun v z) :=
  rfl

/-- The carrier frozen-coefficient operator has operator norm `≤ ‖L‖ · ‖a‖`. -/
theorem norm_mulCoeffL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ‖mulCoeffL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L a‖ ≤ ‖L‖ * ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg a)) _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Frozen-coefficient multiplication descends to the Banach spaces.**  For a fixed parabolic
`C^{0,α}` coefficient field `a`, multiplication `v ↦ (z ↦ L (a z) (v z))` by a continuous bilinear map
`L` is well defined on Banach classes (it is `(‖L‖·‖a‖)`-Lipschitz), giving a bounded operator
`ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …` of norm `≤ ‖L‖ · ‖a‖`.  This is the
frozen-coefficient linear operator whose invertibility the Ricci–DeTurck Schauder estimates
control. -/
noncomputable def mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaBanach X F α s →L[ℝ] ParabolicC0AlphaBanach X G α s :=
  SeparationQuotient.liftCLM (mkL.comp (ParabolicC0AlphaSpace.mulCoeffL L a))
    (fun v v' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist v v' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.mulCoeffL L a v) (ParabolicC0AlphaSpace.mulCoeffL L a v')
          ≤ ‖ParabolicC0AlphaSpace.mulCoeffL L a‖ * dist v v' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact (ParabolicC0AlphaSpace.mulCoeffL L a).le_opNorm _
      exact le_antisymm (hle.trans (le_of_eq (by rw [h0, mul_zero]))) dist_nonneg)

/-- **Frozen-coefficient multiplication commutes with the projection.** -/
@[simp]
theorem mulCoeffL_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L a (mk v) = mk (ParabolicC0AlphaSpace.mulCoeffL L a v) :=
  SeparationQuotient.liftCLM_mk _ _ v

/-- The Banach frozen-coefficient operator has operator norm `≤ ‖L‖ · ‖a‖`. -/
theorem norm_mulCoeffL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ‖mulCoeffL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L a‖ ≤ ‖L‖ * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg a))
    (fun x => ?_)
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [mulCoeffL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_mulCoeffL]
  have := parabolicC0AlphaNorm_continuousLinearMap₂_le L
    (ParabolicC0AlphaSpace.toSubmodule a).2 (ParabolicC0AlphaSpace.toSubmodule v).2
  simpa only [ParabolicC0AlphaSpace.norm_def, mul_assoc] using this

/-- **Point evaluation of a frozen-coefficient product is the bilinear map applied to the point
values.**  Reading off the space-time value of `L(a, ·)` applied to a chart solution `x` at `z` is
`L (a z) (evalCLM z x)` — the pointwise algebra coherence of the frozen-coefficient operator. -/
@[simp]
theorem evalCLM_mulCoeffL_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (z : ℝ × X) (hz : z ∈ s)
    (x : ParabolicC0AlphaBanach X F α s) :
    evalCLM z hz (mulCoeffL L a x) = L (ParabolicC0AlphaSpace.toFun a z) (evalCLM z hz x) := by
  obtain ⟨v, rfl⟩ := mk_surjective x
  simp only [mulCoeffL_mk, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_mulCoeffL]

end ParabolicC0AlphaBanach

namespace ParabolicC0AlphaSpace

/-- **Frozen-coefficient multiplication is additive in the coefficient (carrier).**  `L(a + a', v) =
L(a, v) + L(a', v)` pointwise, from the linearity of `L` in its first argument. -/
theorem mulCoeffL_add_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a a' : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L (a + a') v = mulCoeffL L a v + mulCoeffL L a' v := by
  apply Subtype.ext
  funext z
  show L (toFun a z + toFun a' z) (toFun v z)
      = L (toFun a z) (toFun v z) + L (toFun a' z) (toFun v z)
  rw [map_add, ContinuousLinearMap.add_apply]

/-- **Frozen-coefficient multiplication is homogeneous in the coefficient (carrier).**  `L(c • a, v) =
c • L(a, v)` pointwise. -/
theorem mulCoeffL_smul_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (c : ℝ)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L (c • a) v = c • mulCoeffL L a v := by
  apply Subtype.ext
  funext z
  show L (c • toFun a z) (toFun v z) = c • L (toFun a z) (toFun v z)
  rw [map_smul, ContinuousLinearMap.smul_apply]

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Banach frozen-coefficient multiplication is additive in the coefficient.**  As operators
`ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …`, `mulCoeffL L (a + a')
= mulCoeffL L a + mulCoeffL L a'`. -/
theorem mulCoeffL_add_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a a' : ParabolicC0AlphaSpace X E α s) :
    mulCoeffL (X := X) (s := s) (G := G) L (a + a') = mulCoeffL L a + mulCoeffL L a' := by
  ext x
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.add_apply, mulCoeffL_mk, mulCoeffL_mk, mulCoeffL_mk,
    ParabolicC0AlphaSpace.mulCoeffL_add_coeff, ← mkL_apply, ← mkL_apply, ← mkL_apply, map_add]

/-- **Banach frozen-coefficient multiplication is homogeneous in the coefficient.**  As operators,
`mulCoeffL L (c • a) = c • mulCoeffL L a`. -/
theorem mulCoeffL_smul_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (c : ℝ)
    (a : ParabolicC0AlphaSpace X E α s) :
    mulCoeffL (X := X) (s := s) (G := G) L (c • a) = c • mulCoeffL L a := by
  ext x
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.smul_apply, mulCoeffL_mk, mulCoeffL_mk,
    ParabolicC0AlphaSpace.mulCoeffL_smul_coeff, ← mkL_apply, ← mkL_apply, map_smul]

/-- **The parabolic `C^{0,α}` bounded bilinear multiplication operator.**  Packaging the
frozen-coefficient family `a ↦ mulCoeffL L a` as a single bounded `ℝ`-linear map
`ParabolicC0AlphaSpace … E … →L[ℝ] (ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …)`
of operator norm `≤ ‖L‖`.  Together with the boundedness of each `mulCoeffL L a` this exhibits the
genuine bounded bilinear parabolic `C^{0,α}` multiplication `‖L(a, v)‖ ≤ ‖L‖ · ‖a‖ · ‖v‖` — the
algebra structure a nonlinear Ricci–DeTurck Banach-chart RHS is built from. -/
noncomputable def mulL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ParabolicC0AlphaSpace X E α s →L[ℝ]
      (ParabolicC0AlphaBanach X F α s →L[ℝ] ParabolicC0AlphaBanach X G α s) :=
  LinearMap.mkContinuous
    { toFun := fun a => mulCoeffL L a
      map_add' := mulCoeffL_add_coeff L
      map_smul' := fun c a => mulCoeffL_smul_coeff L c a }
    ‖L‖ (fun a => norm_mulCoeffL_le L a)

/-- On a coefficient `a`, the bounded bilinear multiplication is the frozen-coefficient operator. -/
@[simp]
theorem mulL_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    mulL L a = mulCoeffL L a :=
  rfl

/-- The bounded bilinear multiplication operator has operator norm `≤ ‖L‖`. -/
theorem norm_mulL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ‖mulL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
