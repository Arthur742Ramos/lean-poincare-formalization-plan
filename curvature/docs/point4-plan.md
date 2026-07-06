
### Progress (2026-07-05, later) — the non-scalar bilinear-conjugation reaction generator is BUILT (both halves of the prior "concrete next target" landed)

The tangent-bundle-conjugation bypass proposed by the previous probe finding is now fully realised,
sorry-free and axiom-clean, in `VectorBundle/RiemannianSection.lean`:

* `ContinuousAt.clm_flip` — `ContinuousAt h x₀ → ContinuousAt (fun x => (h x).flip) x₀` (via the
  isometric `flipₗᵢ`); the `ContinuousAt` closure companion for the flip half of `bilinearComp`.
* `Bundle.continuous_bilinearComp_section` (section `BilinearConjugation`, seminormed-fibre `W`) —
  **THE reaction continuity lemma**: for a continuous `BilinearFormBundle` section `s` and a continuous
  tangent-endomorphism section `P : Π x, W x →L[ℝ] W x`, `x ↦ (s x).bilinearComp (P x) (P x)` is a
  continuous `BilinearFormBundle` section.  Built *directly on sections* — the double-hom bundle readout
  reduces (via `trivializationAt_bilinearFormBundle_apply_eq` + `ContinuousLinearMap.inCoordinates_eq`)
  to a fibre-level `bilinearComp` of the two continuous coordinate readouts, closed by
  `ContinuousAt.clm_comp`/`ContinuousAt.clm_flip`.  **This is the bypass of the triple-nested
  `Hom(BilW, BilW)` instance-synthesis wall** (never forms the endo bundle of `BilW`).
* `ContinuousLinearMap.norm_bilinearComp_le` — `‖f.bilinearComp gE gF‖ ≤ ‖f‖·‖gE‖·‖gF‖` (fibre-level
  size estimate; `opNorm_flip` + submultiplicative `opNorm_comp_le`).
* `…ContinuousSectionSpace.bilinearConjFieldLinearMap` / `bilinearConjField` (+ `_apply`, `_norm_le`)
  in `PreferredBilinearNormControl` — **the `smulField`/`endoField` analogue for the non-scalar
  reaction**: `s ↦ (x ↦ (s x).bilinearComp (P x) (P x))` packaged as a genuine
  `CSS(BilW) →L[ℝ] CSS(BilW)` bounded operator of op-norm `≤ C` under the trivialization-distorted,
  `‖P‖²`-weighted fibre bound.  This is the `L t : CSS →L CSS` shape the affine section-space `picard`
  field consumes — WITHOUT `endoField`/the triple-hom bundle.

**Concrete next target.**  The zeroth-order non-scalar reaction generator now exists end-to-end.  To
assemble the geometric `A`: (i) express the intrinsic Ricci–DeTurck reaction (already available as a
continuous `BilinearFormBundle` *value* section in `DeTurckCorrectionRegularity.lean`) through — or
alongside — one or more `bilinearConjField` conjugations by concrete continuous `Hom(TM, TM)` sections
(the DeTurck `∇W` endomorphism is already a continuous `Hom(TM,TM)` section there); (ii) combine with
the model mild/heat-semigroup principal part into the time-dependent `A` and its `picard`
bounded+Lipschitz data; (iii) feed the section-space Picard bridge.  The reaction-operator obstruction
of GAP 2 is now closed at the section-space-operator level; the remaining GAP-2 core is the
second-order principal part and the joint (t,x) picard bounds for the *geometric* operator.

### Progress (2026-07-06) — the DeTurck reaction operator has the CORRECT shape (two-sided derivation, not conjugation)

A ground-truth read of `intrinsicDeTurckCorrection` (DeTurck.lean:893) confirmed the DeTurck
correction is the **derivation** `(g t).inner x (∇W u) v + (g t).inner x u (∇W v)` — one-sided in each
slot — **not** the conjugation `s(P·, P·)` that the previous session's `bilinearConjField` supplies.
The conjugation is the wrong algebraic shape for this term.  This session built the correct shape,
sorry-free and axiom-clean, in `VectorBundle/RiemannianSection.lean`:

* `Bundle.continuous_bilinearComp₂_section` — the two-*different*-endomorphism generalization of
  `continuous_bilinearComp_section`: for continuous `BilinearFormBundle` section `s` and two continuous
  tangent-endomorphism sections `P, Q`, `x ↦ (s x).bilinearComp (P x) (Q x)` is a continuous
  `BilinearFormBundle` section (the readout is the continuous `bilinearComp` of the three readouts).
* `…ContinuousSectionSpace.bilinearCompField` (+ `_apply`, `_norm_le`) — the general two-endomorphism
  bounded operator `s ↦ (x ↦ (s x).bilinearComp (P x) (Q x))` : `CSS(BilW) →L[ℝ] CSS(BilW)` of op-norm
  `≤` the `‖P‖·‖Q‖`-weighted trivialization-distorted fiber bound.  Subsumes `bilinearConjField`
  (`Q = P`).
* `…ContinuousSectionSpace.bilinearDerivationField` (+ `_apply`, `_apply_apply`, `_norm_le`) — **THE
  frozen-coefficient DeTurck reaction operator**: the derivation
  `s ↦ (x ↦ (s x).bilinearComp (P x) id + (s x).bilinearComp id (P x))`, pointwise
  `(u,v) ↦ s x (P x u) v + s x u (P x v)`, as a genuine `CSS(BilW) →L[ℝ] CSS(BilW)` bounded operator of
  op-norm `≤ 2C`.  Built as the sum of the one-sided `bilinearCompField` instances `(P, id)`/`(id, P)`
  via the `‖id‖ ≤ 1` folding of a single `‖P‖`-weighted fiber bound.  With `P = ∇W` (the continuous
  `Hom(TM,TM)` DeTurck endomorphism already available in `DeTurckCorrectionRegularity.lean`) this is
  **exactly** `intrinsicDeTurckCorrection` read as a bounded section-space operator with the
  endomorphism coefficient frozen — a valid `L t : CSS →L[ℝ] CSS` for the affine section-space Picard
  route (`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_boundedLinear_generator_source`).

**Concrete next target.**  The zeroth-order geometric reaction now has a bounded-operator inhabitant of
the *correct* shape.  Two honest continuations, in priority order:
  (1) *Assembly*: the connective lemma identifying `bilinearDerivationField (∇W)` applied to the
      metric-as-section with `intrinsicDeTurckCorrectionSection` — pins `P := ∇W`, `s := g t`, and uses
      `bilinearDerivationField_apply_apply` + the metric/section identity `(g t).inner = metricSection`.
      This needs the chart cover data (`et`/`Kc`), so it is naturally proved at the chart-`A`
      construction site.
  (2) *The long pole*: the SECOND-ORDER principal part.  The reaction (`L t`) is done as a bounded
      generator; the remaining GAP-2 core is the mild/heat-semigroup principal part for the geometric
      operator and the realization decode (parabolic smoothness of the Banach solution).  NOT more
      reaction primitives.

### Progress (2026-07-06, later) — the DeTurck reaction ↔ geometric-correction fiber-value BRIDGE is BUILT, and the operator-instantiation wall is precisely diagnosed

New module `RicciFlow/DeTurckReactionAssembly.lean` (imports both `DeTurckCorrectionRegularity` and
`VectorBundle/RiemannianSection`), sorry-free and axiom-clean:

* `metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection` — **the DeTurck half of the
  chart `A` `geometric` field, at the fiber-value level**: for any `ContinuousSectionSpace` element
  `sMetric` agreeing pointwise with the metric `(g t).inner`, the frozen-`∇W` two-sided derivation
  `sMetric x (∇W x u) v + sMetric x u (∇W x v)` equals `intrinsicDeTurckCorrectionSection g background
  t x u v` pointwise (with `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background
  t)`).  This is EXACTLY the value `ContinuousSectionSpace.bilinearDerivationField` produces
  (`bilinearDerivationField_apply_apply`); composing the two identifies the abstract bounded reaction
  operator with the concrete geometric Ricci–DeTurck reaction term on the metric section.  Stated at the
  fiber-value level so it is **wall-free** and directly consumable once the operator is formed.

**Diagnosed blocker (the operator-instantiation wall).**  Forming
`ContinuousSectionSpace.bilinearDerivationField` itself at `W := TangentSpace I` (to get a genuine
`CSS →L[ℝ] CSS` for the affine section-space Picard route) is blocked by a two-layer instance diamond,
NOT a math gap:
  1. the size datum `‖P x‖` needs `Norm (TangentSpace I x →L[ℝ] TangentSpace I x)`, only reachable via
     the defeq `TangentSpace I x = E` (`inferInstanceAs (Norm (E →L[ℝ] E))`) — instance search does not
     unfold `TangentSpace`; providing it as a `local instance` fixes THIS layer; but
  2. the bound `‖(et i).symmL ℝ x‖` then fails with an **honest topology diamond on the bilinear fiber**
     `E →L[ℝ] E →L[ℝ] ℝ`: `Trivialization.symmL` elaborates its fiber with the metric topology
     `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`, while `et i` carries the vector-bundle CLM
     topology `ContinuousLinearMap.topologicalSpaceTotalSpace …` (defeq but not syntactically equal), so
     `et i` cannot fill `symmL`'s trivialization slot.
This is a DEFINITION-SITE fix (in `RiemannianSection.lean`): `bilinearDerivationField`'s hbound is
phrased through `symmL`/`continuousLinearMapAt`, which triggers the fiber topology diamond at
`W = TangentSpace`.  No existing code instantiates any of the section-space fiber operators
(`smulField`/`endoField`/`bilinearCompField`/`bilinearDerivationField`) at `TangentSpace` — they are all
abstract-`V`; this is the first concrete tangent instantiation and it exposes the wall.

**Concrete next target.**  Provide, at the `RiemannianSection` definition site, a diamond-free
`bilinearDerivationField` bound variant (state hbound via the coordinate readout norm rather than
`symmL`, or pin the bilinear-fiber topology to the CLM one) so the operator becomes instantiable at
`TangentSpace`; then feed `bilinearDerivationField (∇W) + source` to
`exists_banachEvolutionLocalSolutionIn_continuousSectionSpace_of_boundedLinear_generator_source`.  The
fiber-value identity above is then composed to discharge the DeTurck part of the chart `geometric`
field.  (The section-level full-RHS assembly `-2•rs + deTurckCorrection = intrinsicRicciDeTurckRHS`
already exists as `exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection`.)
