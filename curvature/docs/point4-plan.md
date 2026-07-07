
### Progress (2026-07-06, EVENING) — ✅ the `BilinearFormBundle` topology-instance diamond is RESOLVED at the definition site; the geometric reaction operator now produces a genuine section-space Banach evolution solution AND its literal `IsPicardLindelof` picard datum

The HARD Path-A/Path-B diamond documented in the previous note (below) is **CLOSED**, and the
section-space Picard bridge now applies verbatim to the concrete `BilinearFormBundle` continuous
section space.  Five additive, sorry-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`)
landings across three files:

**Root cause (confirmed) and fix.**  The whole section-space Picard bridge chain is *fibre-norm-free*:
every estimate is at the Banach `F`-norm / coordinate-readout level, and the fibre
`[∀ x, SeminormedAddCommGroup (V x)]` was present *only* to supply the section-space fibre topology —
baking Path A (`SeminormedAddCommGroup → … → TopologicalSpace`) into the bridge's `ContinuousSectionSpace`
type, which then failed to unify with the concrete double-`CLM` fibre `BilW x = W x →L[ℝ] W x →L[ℝ] ℝ`
carrying Path B (`ContinuousLinearMap.topologicalSpace`).  Fix = restate the bridge chain with the
fibre topology as an *explicit* `[∀ x, TopologicalSpace (V x)]` binder (+ bare `AddCommGroup`/`Module`),
so the section-space topology is synthesised in the caller's context (= Path B for `BilW`).  Done
**additively** (`_topFibre` copies; no existing declaration touched):

* `ContinuousSection.lean` (new `TopologicalFibreCoordControl` section): `norm_le_of_forall_coord_norm_le_topFibre`,
  `continuousOn_of_forall_coord_continuousOn_topFibre`, `exists_forall_mem_Icc_coord_norm_le_of_continuousOn_topFibre`
  — the three fibre-norm-free coordinate helpers, copied from the seminormed-section originals with
  the explicit-topology fibre binder (proofs port verbatim).
* `AnalyticPDE/SectionSpacePicard.lean`: `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound_topFibre`,
  `sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound_topFibre`,
  `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre`
  — the centre-bound `IsPicardLindelof` constructor, the fixed-window `BanachEvolutionLocalSolutionIn`
  bridge, and the *auto-window* forward-time `IsPicardLindelof` chooser, all with the explicit-topology
  fibre.

**End-to-end validation (new file `AnalyticPDE/GeometricReactionPicard.lean`, imports RiemannianSection
+ SectionSpacePicard).**  The `_topFibre` bridges are applied to the concrete affine frozen-coefficient
DeTurck reaction `A s = bilinearDerivationFieldLinearMap … s + b`, consuming its already-proved
coordinate `hlip` (`2·Kp·dist`) / `hcenter` (`2·Kp·‖σ0‖+‖b‖`) bounds (with `hcont` trivial — the frozen
operator is constant in time):

* `bilinearDerivationFieldLinearMap_add_source_banachEvolutionLocalSolutionIn_exists` — a genuine
  `Nonempty (BanachEvolutionLocalSolutionIn A locus t₀ σ0)` on `[t₀,T]` under `(Mc+K·a)·(T−t₀)≤a` and
  `closedBall σ0 a ⊆ locus`.  **The first section-space Banach evolution solution from the GEOMETRIC
  reaction operator (not a model heat-semigroup)** — the object a `RicciDeTurckChartClosureData.realization`
  decode consumes.
* `bilinearDerivationFieldLinearMap_add_source_exists_forwardTime_isPicardLindelof` — the literal chart
  `picard`-field shape `∃ T Mc, IsPicardLindelof A … σ0 a 0 (Mc+K·a) K` with the endpoint `T` chosen
  automatically (no `hLa` needed), from `Kp` + a reference window `T₀` + radius `a>0`.

**Fractions of `{A, picard, realization, encode}` now in hand (frozen reaction representative).**  `A`
= the affine `bilinearDerivationFieldLinearMap … + b` (DONE, elaborates + composes through the bridge
at the concrete `BilW`).  `picard` = **DONE** for this representative: both `IsPicardLindelof` (auto-window)
and `BanachEvolutionLocalSolutionIn` are now produced from the geometric coordinate bounds.  Remaining:
extend `A` from the frozen affine reaction to the actual mild/regularised Ricci–DeTurck RHS (the
`(-2)Ric` principal part is `C⁰`-unbounded — needs the mild representative), then the `realization`
decode (`RicciDeTurckSmoothRealizationData.of_…`, SmoothRealization.lean) of the Banach solution into a
genuine `ChosenIntrinsicDeTurckLocalSolution`, and `encode`.

**Concrete next target.**  Feed
`bilinearDerivationFieldLinearMap_add_source_banachEvolutionLocalSolutionIn_exists` (specialised to the
tangent bundle `W := TM` with `P := ∇W` the frozen DeTurck coefficient about `g0` and `b := (-2)•Ric =
intrinsicRicciFlowRHSSectionSpace`) into the `realization` decode.  The remaining obstruction is the
`W := TM` specialisation (the raw tangent-fibre `‖·‖` synthesis wall), for which the `inCoordinates`
readout `Kp`-bound is the intended clean-model-fibre input; and the mild upgrade of the `(-2)Ric`
principal part.

### Progress (2026-07-06, later) — affine chart-`A` coordinate hlip/hcenter data assembled; ⚠️ the section-space Picard bridge hits a HARD topology-instance diamond on `BilinearFormBundle`

Two additive, sorry-free, axiom-clean landings on the geometric-`A` critical path:

* `…ContinuousSectionSpace.coord_add_apply` (`VectorBundle/ContinuousSection.lean`) — generic
  coordinate additivity `(coord (s+t)).1 i x = (coord s).1 i x + (coord t).1 i x`, the companion of
  `coord_zero_apply` (via `toCompatibleCoordFamilySubmoduleContinuousLinearMap` + `map_add`).
* `bilinearDerivationFieldLinearMap_add_source_coord_dist_le` / `_add_source_coord_norm_le`
  (`VectorBundle/RiemannianSection.lean`) — the **affine chart-`A`** coordinate `hlip`/`hcenter` data
  for `A s = L s + b` (frozen DeTurck reaction `L` + fixed source `b`): `dist(coord(A s))(coord(A s'))
  ≤ 2·Kp·dist s s'` (same Lipschitz const as `L` — the source cancels, via `coord_add_apply` +
  `add_sub_add_right_eq_sub`) and `‖coord(A σ)‖ ≤ 2·Kp·‖σ‖ + ‖b‖`.  This is exactly the section-space
  Picard `hlip`/`hcenter` shape for the affine chart operator at the metric state.

**⚠️ CRITICAL BLOCKER FOUND — the section-space Picard bridge cannot yet be applied to the concrete
`BilinearFormBundle` CSS (a topology-instance diamond).**  Attempting "step 2" (feeding the landed
coordinate bounds to `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn`
/ `sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound` in
`AnalyticPDE/SectionSpacePicard.lean`) fails as follows:
  * `ContinuousSectionSpace` takes the fibre topology `[∀ x, TopologicalSpace (V x)]` as a **separate
    instance arg** (ContinuousSection.lean line ~39).
  * On the double-CLM fibre `BilW x = W x →L W x →L ℝ`, that instance has TWO defeq-but-syntactically-
    distinct spellings: **Path B** = `ContinuousLinearMap.topologicalSpace` (what the concrete
    `BilinearFormBundle` world uses — the coord lemmas, and the `FiberBundle`/`VectorBundle` instances,
    are all baked at Path B at their elaboration site) vs **Path A** =
    `(SeminormedAddCommGroup …).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace` (what the bridge
    DERIVES, since for its abstract `V` only `SeminormedAddCommGroup (V x)` is in scope; Path A is
    baked into the bridge's type, NOT a controllable binder).
  * `rfl` confirms Path A ≡ Path B is **defeq even for abstract CLMs** — but Lean's ordered
    application-time `isDefEq` (and instance synthesis, which uses keyed matching) does NOT bridge the
    two spellings: feeding a Path-B `σ0` to the Path-A bridge type-mismatches on the topology arg;
    forcing Path A globally (a high-priority `@[reducible]` local instance) makes `FiberBundle` and
    `σ0` synthesise fine, but the derived-topology metavar `?SemiCLM` inside the bridge stays
    unassigned during the `σ0` check (projection-non-injectivity `(?SemiCLM x).toPMS.toUS.toTS =?=
    <concrete>` deadlock), AND the coord lemmas remain baked at Path B so `exact hb` still needs the
    un-bridged defeq.

**RECOMMENDED DEFINITION-SITE FIX (next session's highest-leverage target).**  Make one side's fibre
topology match the other's *spelling*, so no cross-file defeq is needed.  Cleanest options:
  1. Restate the SectionSpacePicard bridge family to take `[∀ x, TopologicalSpace (V x)]` as an
     EXPLICIT binder placed *before* `[∀ x, SeminormedAddCommGroup (V x)]` (so the CSS fibre topology
     is synthesised in the caller's context = Path B for `BilW`, consistent with `FiberBundle`), with
     the seminormed structure only supplying the norm — requires checking the bridge's proof does not
     rely on the fibre topology being *definitionally* the seminormed one; OR
  2. Re-base the `BilinearFormBundle` coord-lemma chain in RiemannianSection on the seminormed-derived
     (Path A) fibre topology (a `letI`/section-local instance forcing Path A for the whole
     `PreferredBilinearNormControl` derivations), so the coord lemmas are baked at Path A and match the
     bridge directly.
Either unblocks "step 2" (BanachEvolutionLocalSolutionIn / IsPicardLindelof for the geometric `A`).
The affine `hlip`/`hcenter` data above is then consumed verbatim.

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

### Progress (2026-07-06, later) — the `bilinearDerivationField`-at-`TangentSpace` wall is DEEPER than `symmL`: it is the structural `SeminormedAddCommGroup(TM x)`-vs-canonical-bundle-topology diamond + a `whnf` performance wall. The prior "diamond-free `symmL` variant" target is NECESSARY BUT NOT SUFFICIENT.

A ground-truth reproduction (throwaway module, reverted) of forming
`ContinuousSectionSpace.bilinearDerivationField (F := F) (W := TangentSpace I) …` established the exact
failure chain, in order:

1. **`hbound` norms (fixable).**  `‖(et i).symmL ℝ x‖`, `‖(et i).continuousLinearMapAt ℝ x‖`, `‖P x‖`
   fail `Norm` synthesis at `TangentSpace` because `Norm (TangentSpace I x →L[ℝ] …)` and the bilinear
   symm/clm norms are not reached (instance search does not unfold `TangentSpace`).  These are ALL
   dischargeable by copying the `SmoothApproxClosure.lean` **local-instance preamble** (lines 41–92) and
   ADDING three more `change Norm (BilF →L BilF)` / `change Norm (F →L F)` local instances for the
   bilinear `symmL`/`clmAt` fiber and for `Norm (TM x →L[ℝ] TM x)` (`‖P x‖`).  With the full preamble the
   `hbound` type elaborates cleanly.  (Empirically confirmed: line-52 `hbound` error disappears.)

2. **base `FiberBundle F TM` / `VectorBundle ℝ F TM` at the operator site (the real wall).**  The operator's
   variable block simultaneously demands `[∀ x, SeminormedAddCommGroup (W x)]` AND `[FiberBundle F W]` /
   `[VectorBundle ℝ F W]` on `W := TangentSpace I`.  At `TM` these two families CONFLICT on
   `TopologicalSpace (TM x)`: the repo-global `instNormedAddCommGroupTangentSpace` (flat-`E`, priority 70)
   supplies the fibre norm whose `toTopologicalSpace` is the flat-`E` norm topology, while
   `TangentSpace.fiberBundle`/`.vectorBundle` (which is what `[FiberBundle F TM]` must come from — the
   manifold's tangent bundle is genuinely non-trivial, so this instance CANNOT be flat) carries the
   canonical `deriving`-produced `TangentSpace.instTopologicalSpace`.  These two `TopologicalSpace (TM x)`
   terms are DEFEQ (both are `E`'s norm topology) but NOT syntactically equal, so `FiberBundle F TM`
   synthesised at the operator site does not match `TangentSpace.fiberBundle`, and the whole application
   fails with `failed to synthesize FiberBundle F (TangentSpace I)` even when `[FiberBundle F TM]` and
   `[VectorBundle ℝ F TM]` are placed EXPLICITLY in the binder.  Everything downstream
   (`MemTrivializationAtlas (trivializationAt BilF BilW (x0 i))`) cascades from this one failure.

3. **`whnf` performance wall (FUNDAMENTAL — hits the bare linear map, not just the bounded operator).**
   Once layers (1)–(2) are pinned by local instances, forming the operator does NOT fail fast — it grinds
   `>11 min` without terminating (deterministic `whnf` timeout territory).  This is NOT specific to
   `symmL`, to the `hbound`, or to the bounded-operator packaging: a follow-up probe forming ONLY the raw
   `bilinearCompFieldLinearMap (F := F) (W := TM) …` LINEAR MAP (no norms, no bound, abstract `et`) with the
   minimal `pTMNACG/pTMNS/pTMFB/pTMVB` preamble ALSO grinds `>90 s` and does not terminate at
   `maxHeartbeats 1000000`.  The cost is intrinsic to reducing `BilinearFormBundle (V := TM)` /
   `ContinuousLinearMap.topologicalSpaceTotalSpace` and the tangent trivialization readouts inside
   `continuous_bilinearComp₂_section`.  So the definition-site fix must ALSO defeat this blow-up (e.g.
   `@[irreducible]`/opaque wrappers around the TM bilinear-bundle trivialization terms, or a cheaper
   concrete bundle representation), independently of the instance-diamond fix.

**Why the plan's prior "symmL-only" target is insufficient.**  `SmoothApproxClosure.lean` proves the
diamond is *navigable for `symmL` bounds and CSS operations* (it states `‖(trivializationAt F TM (x0 i)).symmL ℝ x‖`
via the TANGENT trivialization and never re-synthesises base `VectorBundle ℝ F TM` in a conflicting
context).  But that navigation does NOT extend to `bilinearDerivationField`, whose signature forces the
`SeminormedAddCommGroup(TM x)` ⨯ `FiberBundle F TM` conflict AND triggers the `whnf` blow-up.  A diamond-free
`symmL` variant alone therefore will not make the operator instantiable — layers (2) and (3) remain.

**Revised concrete next target (definition-site fix, `RiemannianSection.lean`).**  Provide a
`TangentSpace`-SPECIALISED reaction operator that (i) takes the base `FiberBundle`/`VectorBundle` and the
fibre `SeminormedAddCommGroup` as EXPLICIT arguments pinned to ONE mutually-consistent instance (so the
topology diamond cannot arise), (ii) phrases its bound through the model-fibre coordinate readout only
(never `‖s x‖`/`‖P x‖` on `TM x`), and (iii) is `whnf`-cheap by never forcing reduction of
`trivializationAt BilF BilW` (work through `continuousLinearMapAt`/`coord` eval lemmas, which DID elaborate
at `TangentSpace`, not `symmL`).  Note the chart's `A : ℝ → CSS → CSS` field is a bare FUNCTION — the
bounded operator is only needed to discharge the `picard`/`lipschitz` estimate fields, so the specialised
operator can be scoped narrowly to those estimates.  The geometric RHS *source* is already a named CSS
value (`intrinsicRicciDeTurckRHSSectionSpace` + `_apply`/`_symm`); only the reaction/principal
*estimate operator* remains blocked.

### Progress (2026-07-06, later) — the SECTION-SPACE self-DeTurck reduction landed: the named Ricci–DeTurck RHS value collapses to the pure Ricci-flow source `(-2)•Ric` in the flowing metric's own Levi-Civita gauge

Three sorry-free, axiom-clean lemmas (only `propext`/`Classical.choice`/`Quot.sound`), purely additive:

* `intrinsicRicciDeTurckRHS_chosenLeviCivitaFamily_eq_intrinsicRicciFlowRHS` (DeTurck.lean) — the
  RAW family-level specialization of `intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita`
  to `background := chosenLeviCivitaFamily g` (LC hypothesis discharged by
  `chosenLeviCivitaFamily_isLeviCivita`): `intrinsicRicciDeTurckRHS g (chosenLeviCivitaFamily g) =
  intrinsicRicciFlowRHS g`.  This is EXACTLY the reduction the chart-closure `chartRHS_eq_intrinsic`
  obligation needs — that `RicciDeTurckChartClosureData.of_smoothMetricSectionCurve_…` field identifies
  the chart operator along the solution with `intrinsicRicciDeTurckRHS (spatial sol).metric
  (chosenLeviCivitaFamily (spatial sol).metric)`, which by this lemma equals
  `intrinsicRicciFlowRHS (spatial sol).metric` = `(-2)•Ric` (the flowing metric's DeTurck term vanishes
  in its own LC gauge).
* `intrinsicRicciDeTurckRHSSectionSpace_apply_eq_intrinsicRicciFlowRHS_of_isLeviCivita`
  (DeTurckCorrectionRegularity.lean) — the SECTION-SPACE companion (general LC background): the named
  `intrinsicRicciDeTurckRHSSectionSpace` value reads out pointwise as `intrinsicRicciFlowRHS g` when the
  background is Levi-Civita for `g`.
* `intrinsicRicciDeTurckRHSSectionSpace_chosenLeviCivitaFamily_apply_eq_intrinsicRicciFlowRHS` — the
  directly-consumable specialization to `chosenLeviCivitaFamily g` with the canonical `C¹` witness
  `someContMDiffLeviCivitaConnection_contMDiff`.

**Ground-truth reconfirmations this session (no new work needed):** the `_of_isLeviCivita` vanishing
chain (`intrinsicDeTurckVectorField/Correction_eq_zero_of_isLeviCivita`) already exists; `CovariantDerivative.difference`
is a Mathlib def (`.../CovariantDerivative/Basic.lean`) with `difference_apply_eq_extend`/`IsCovariantDerivativeOn.zero`;
and the geometric reaction *operator* `bilinearDerivationField` at `W := TangentSpace I` remains blocked
by the documented 3-layer `BilinearFormBundle`-at-`TM` wall (norm-instance / `SeminormedAddCommGroup`-vs-canonical-bundle-topology
diamond / `whnf` blow-up on `trivializationAt BilF BilW`).  The self-DeTurck reduction does NOT sidestep
that wall for a *strictly parabolic* chart: in the self-LC gauge the reaction genuinely vanishes but the
principal `(-2)•Ric` is still 2nd-order/`C⁰`-unbounded, so the mild/regularised reaction operator with a
FIXED background remains the picard blocker.

**Concrete next target.**  Either (a) the definition-site `whnf`-cheap, instance-pinned
`TangentSpace`-specialized reaction operator (unblocks `L t : CSS →L CSS` for the affine picard route),
or (b) the `decode : positiveDefiniteLocus → MetricFamily` (positive-definite section → bundled metric
family) needed for the chart `A`'s `geometric` field — `positiveDefiniteLocus = {s | ∀ x v, v ≠ 0 →
0 < s x v v}` currently carries no metric-decode, and the `geometric` field is trivial once a section
decodes to a metric whose `intrinsicRicciDeTurckRHSSectionSpace` reproduces `A`.

### Progress (2026-07-06, later still) — symmetric-locus content of the affine-split summands landed; and a SHARPENED ground-truth diagnosis of the `bilinearDerivationField`-at-`TM` wall (the `RiemannianBundle` cracks layer 1 but two new layers appear)

**Committed (sorry-free, axiom-clean `propext`/`Classical.choice`/`Quot.sound`, additive):**

* `intrinsicRicciFlowRHSSectionSpace_symm` (DeTurckCorrectionRegularity.lean) — the named
  second-order source value `b = (-2)•Ric` of the chart split `A τ s = reaction s + b` is pointwise
  symmetric, via `intrinsicRicciFlowRHS_symm` (needs only the ambient `IsManifold` smoothness
  instances; **no** background hypothesis).
* `intrinsicDeTurckCorrectionSectionSpace_symm` — the named zeroth-order DeTurck reaction value is
  pointwise symmetric, unconditionally, via `intrinsicDeTurckCorrection_symm`.
  Together they certify both named summands of the geometric Ricci–DeTurck RHS lie in the symmetric
  locus — the directly-consumable symmetric-locus obligation on each half of the chart's `geometric`
  field.

**SHARPENED WALL DIAGNOSIS (empirical, read-only scratch probes at `W := TangentSpace I`).**  The prior
note said the `‖P x‖` datum is "only reachable through `TangentSpace I x = E`".  Ground truth is richer:

* **Layer 1 — the single tangent CLM norm `Norm (TM x →L[ℝ] TM x)` (the `‖P x‖ = ‖∇W x‖` datum).**
  By *default* it FAILS to synthesize (even though `NormedAddCommGroup (TM x)` and `NormedSpace ℝ (TM x)`
  both DO, via `TM x = E` reducibility) — the `hasOpNorm` instance cannot bridge the reducibility gap.
  It IS defeq-providable as `(inferInstance : Norm (E →L[ℝ] E))`.  **Crucially, it synthesizes cleanly
  under `letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩`** — the metric-induced
  `instNormedAddCommGroupOfRiemannianBundle…` gives a fiber norm whose topology *is* the bundle
  topology, and then `Norm (TM x →L TM x)`, `SeminormedAddCommGroup (TM x)`, and `FiberBundle E TM` all
  synthesize *mutually consistently*.  So layer 1 is CRACKABLE with a `RiemannianBundle` `letI`.
* **Layer 2 (NEW) — the nested/bilinear tangent CLM norm `Norm (TM x →L[ℝ] TM x →L[ℝ] ℝ)`
  (`= Norm (BilW x)`).**  This BLOWS UP: by default it fails, and even *under* `letI : RiemannianBundle`
  it hits the `synthInstance` heartbeat ceiling (deterministic timeout) — a genuine synthesis blow-up,
  not a mere missing instance.  This is why any fiber-level reaction bound stated on the raw
  `b : TM x →L TM x →L ℝ` (e.g. `‖b.bilinearComp P id + b.bilinearComp id P‖ ≤ 2‖b‖‖P‖`) is
  UN-ELABORABLE at `TM`.  The bound MUST be phrased through the model-fibre readout in the clean
  `E →L[ℝ] E →L[ℝ] ℝ` (where the CSS coordinate readout already lives), never the raw `‖BilW x‖`.
* **Layer 3 — the `symmL` metric-topology diamond on `BilW`.**  Forming `bilinearDerivationField
  (W := TM) … hbound` under `letI : RiemannianBundle` no longer fails on `‖P x‖`, but the `hbound`
  STATEMENT itself now mis-elaborates: `(et i).symmL ℝ x` is sought against a trivialization whose fibre
  carries `PseudoMetricSpace.…toTopologicalSpace` (the RiemannianBundle-induced metric topology on the
  `BilF`/`BilW` fibre) while `et i` provides `ContinuousLinearMap.topologicalSpace` — the two are
  propositionally equal but instance-path-distinct, so `symmL` drops fibre metavariables.  (Without the
  `RiemannianBundle` `letI`, `symmL` elaborates fine but layer 1 blocks `‖P x‖`.)

**Consequence for the definition-site fix (revised, precise).**  The `TangentSpace`-specialised reaction
operator must (i) obtain `‖P x‖` NOT from a raw `Norm (TM x →L TM x)` but from the **model-fibre
readout** `‖ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (P x)‖ ∈ E →L[ℝ] E` (clean, no
`RiemannianBundle`, no blow-up), and (ii) phrase its whole `hbound` through the `BilF`-readout so that
neither `Norm (BilW x)` (layer 2) nor `symmL`-under-metric-topology (layer 3) is ever forced.  The
`RiemannianBundle`-`letI` route is a dead end past layer 1 (it trades layer 1 for layers 2+3).  The
readout route is the only one that stays in the clean model fibres throughout.

**Concrete next target (unchanged in spirit, sharpened).**  A `bilinearCompField`/`bilinearDerivationField`
variant whose `hbound` hypothesis is a bound on the `(et i)`-readout of the *composite* (or on
`‖inCoordinates … (P x)‖`), proved via the readout identity already internal to
`continuous_bilinearComp_section` (`readout((s x).bilinearComp (P x) (Q x)) =
(readout s).bilinearComp (readout P)(readout Q)`), so the operator elaborates at `TM` with *default*
instances and clean `E →L[ℝ] E →L[ℝ] ℝ` norms only.  Extract that readout identity as a standalone
lemma first (it is the reusable core), then rebuild the bound on top of it.

### Progress (2026-07-06, still later) — the readout-route fibre toolkit for the geometric DeTurck reaction's `hlip` bound is COMPLETE: the coordinate Lipschitz constant `2‖readout P‖` is now proved at `W := TangentSpace I` in the clean model fibre

Building directly on the just-extracted readout identity + norm bound
(`trivializationAt_bilinearFormBundle_bilinearComp_readout_eq` / `_le`), five sorry-free,
axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive lemmas landed in
`VectorBundle/RiemannianSection.lean` (section `BilinearConjugation`):

* `trivializationAt_bilinearFormBundle_readout_add` / `_readout_sub` — the `BilinearFormBundle`
  trivialization readout is additive / subtractive in the fibre value (`readout(b ± c) = readout b ±
  readout c` on the base set), via the fiberwise-linear `trivializationAt_bilinearFormBundle_apply_eq`.
  The readout-linearity inputs any coordinate difference/Lipschitz bound in the CSS consumes.
* `inCoordinates_id_eq_id` (`inCoordinates F W F W x₀ x x₀ x (id (W x)) = id F` on the base set, via
  `inCoordinates_eq` + `ContinuousLinearEquiv.coe_comp_coe_symm`) and `norm_inCoordinates_id_le`
  (`‖·‖ ≤ 1` via `ContinuousLinearMap.norm_id_le`) — the `‖id‖`-slot facts.
* `norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_le` — the model-fibre readout
  **norm bound for the CORRECT DeTurck reaction shape** (a two-sided *derivation*, not a conjugation):
  `‖readout((s x).bilinearComp (P x) id + (s x).bilinearComp id (P x))‖ ≤ 2·‖readout(s x)‖·‖inCoord
  P‖`.  Built from the plain composition readout bound on each one-sided summand + `readout_add` +
  `norm_inCoordinates_id_le`.
* `norm_trivializationAt_bilinearFormBundle_deTurckDerivation_readout_sub_le` — **the coordinate
  Lipschitz bound = the fibre content of the section-space Picard `hlip` field**: for a common frozen
  `P`, `‖readout(deriv(s x)) − readout(deriv(s' x))‖ ≤ 2·‖inCoord P‖·‖readout(s x) − readout(s' x)‖`.
  Proof: combine the two state readouts into the readout of their fibrewise difference
  (`readout_sub`), use derivation-value linearity (`bilinearComp` linear in slot 1), and apply the
  derivation size bound to the difference section.

**Why this is on the critical path (verified, not speculative).**  `ContinuousSection.lean:103`
proves `coordContinuousMap (e := et i) (Kc i) … s x = (et i (T% s x.1)).2` **by `rfl`** — the CSS
coordinate `(equivCompatibleCoordFamilySubmodule … σ).1 i x` IS the trivialization readout
`(trivializationAt BilF BilW (x0 i) (mk x (σ x))).2`.  The bridge
`sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound`
(`SectionSpacePicard.lean:467`) consumes `hlip : dist (coord (A t s) i x) (coord (A t s') i x) ≤ K ·
dist s s'`, and `dist` in the model fibre `BilF` is `‖· − ·‖`.  So the `_readout_sub_le` lemma above
supplies the pointwise Lipschitz constant `K = 2·sup‖inCoord P‖` for the frozen-coefficient DeTurck
reaction `A t s = (u,v) ↦ s x (P x u) v + s x u (P x v)` — entirely in the clean model fibre, hence
elaborating at `W := TangentSpace I` where the raw `‖BilW x‖`/`‖TM x →L TM x‖` fibre norms are
un-synthesizable.  This closes the reaction-operator's `hlip` obstruction at the *fibre* level via the
readout route (never forming the bundled `CSS →L CSS` operator, so the `whnf` blow-up wall is
sidestepped).

**Concrete next target.**  Assemble the fibre `_readout_sub_le` bound into the actual bridge `hlip`
field: (i) define the frozen-coefficient reaction as a map `A : ℝ → CSS → CSS` on the underlying
sections (`s ↦ x ↦ (s x).bilinearComp (P x) id + (s x).bilinearComp id (P x)`; continuity is
`continuous_bilinearComp₂_section`), (ii) rewrite the bridge's `dist (coord (A t s) i x) (coord (A t
s') i x)` through `coordContinuousMap_apply` (= readout) and `dist_eq_norm`, (iii) apply
`_readout_sub_le` with `‖inCoord P‖ ≤ K/2` uniform over the finite cover (a `Finite κ` sup, since each
`Kc i` is compact and `inCoord P` is continuous).  Then the centre bound `hcenter` follows from
`_deTurckDerivation_readout_le` at `x0` and the same uniform sup; `hcont` from
`continuous_bilinearComp₂_section` in `t`.  This yields the frozen reaction's `picard` data; the
principal `(-2)•Ric` source is already the named CSS value `intrinsicRicciFlowRHSSectionSpace`.

### Progress (2026-07-06, later) — the frozen DeTurck-reaction's section-space Picard `hlip` + `hcenter` are ASSEMBLED into the exact bridge coordinate form, at `W := TangentSpace I`

Five sorry-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive
declarations landed in `VectorBundle/RiemannianSection.lean` (section `PreferredBilinearNormControl`),
turning the fibre readout toolkit into the actual `A`/`picard` coordinate obligations:

* `bilinearDerivationFieldLinearMap` (+ `_apply`) — the **unbundled** frozen reaction as a plain
  `CSS →ₗ[ℝ] CSS`, `s ↦ (x ↦ (s x).bilinearComp (P x) id + (s x).bilinearComp id (P x))`, built as the
  sum of two `bilinearCompFieldLinearMap` instances.  Crucially it needs NO raw fiber-norm `hbound`
  (unlike the bundled `bilinearDerivationField`), so it elaborates at `W := TangentSpace I`; this is
  the exact `A t s` shape the section-space Picard bridge consumes as a plain `ℝ → CSS → CSS` map.
* `bilinearFormBundle_coord_eq_trivializationAt_readout` — the **coord ↔ readout bridge**: for
  `et i := trivializationAt BilF BilW (x0 i)`, the CSS coordinate `(equivCompatibleCoordFamilySubmodule
  σ).1 i x` equals the raw fibre readout `(trivializationAt BilF BilW (x0 i) ⟨x, σ x⟩).2`.  Composes
  `coord_apply` with the on-baseSet identity `continuousLinearMapAt = (e ⟨x,·⟩).2`
  (`coe_linearMapAt_of_mem`).  This translates the `coord` language the Picard bridge states its
  `hlip`/`hcenter` in into the `trivializationAt`-readout language the model-fibre
  `_deTurckDerivation_readout_*` estimates are proved in.
* `bilinearDerivationFieldLinearMap_coord_dist_le` — **the `hlip` field**: `dist (coord (D s) i x)
  (coord (D s') i x) ≤ 2·Kp·dist s s'` where `Kp` is any uniform bound on `‖inCoordinates F W F W
  (x0 i) x (x0 i) x (P x)‖` over the finite cover.  EXACTLY the `hlip` hypothesis of
  `sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound` /
  `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn`, with
  `K := 2·Kp`.  Proof: coord→readout bridge, then the clean-model-fibre
  `_deTurckDerivation_readout_sub_le` (Lipschitz const `2‖inCoord P‖`), then `coord_dist_le_dist`.
* `bilinearDerivationFieldLinearMap_coord_norm_le` — **the `hcenter` field**: `‖coord (D σ) i x‖ ≤
  2·Kp·‖σ‖`.  At `σ := x0` (the initial metric section) this is the `hcenter` datum `‖coord (A t x0)
  i x‖ ≤ Mc` with `Mc := 2·Kp·‖x0‖`.  Companion route via `_deTurckDerivation_readout_le` +
  `coord_norm_le_norm`.

**Fractions of `{A, picard}` now constructed (reaction summand).**  For the frozen reaction operator:
`A` = `bilinearDerivationFieldLinearMap` (DONE, elaborates at `TM`).  `picard` inputs: `hlip` DONE,
`hcenter` DONE (via `_coord_norm_le` at `x0`), `hcont` = `continuousOn_const` (frozen ⇒ trivial at the
use-site).  So the reaction summand's full `picard` triple is in hand at the fibre/coordinate level.

**Concrete next target.**  The PACKAGING into `IsPicardLindelof`/`BanachEvolutionLocalSolutionIn`
must live in a file importing BOTH `RiemannianSection` (these lemmas) AND `AnalyticPDE/SectionSpacePicard`
(the bridge) — `RiemannianSection` does not import the Picard layer.  In that assembly file: feed
`_coord_dist_le` (as `hlip`, `K := 2·Kp`) and `continuousOn_const` (as `hcont`) into
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn` to obtain a
real `IsPicardLindelof` for the frozen reaction; then add the `(-2)•Ric` source `b`
(`intrinsicRicciFlowRHSSectionSpace`, constant in `s`) — `hlip` is unchanged (affine, `b` cancels in
the difference), `hcenter` gains `‖coord b‖`; and identify `P := ∇W` (the frozen DeTurck coefficient
about `g0`) with its `inCoordinates` size bound `Kp` supplied by compactness.  That yields the chart's
`picard`, whose decode is `realization`.

### Progress (2026-07-06, later) — the tangent-bundle DeTurck reaction OPERATOR now exists on the concrete `BilinearFormBundle` section space, and its affine `A = Ricci-source + reaction` reproduces the full geometric `intrinsicRicciDeTurckRHS` on the metric state

Empirically confirmed the recurring blocker: the abstract generic-fibre operator
`ContinuousSectionSpace.bilinearDerivationFieldLinearMap` **cannot be instantiated at
`W := TangentSpace I`** — forming it there fails to synthesize `FiberBundle E (TangentSpace I)`
(equivalently the un-synthesizable `Π`-fibre-norm `[∀ x, SeminormedAddCommGroup (TangentSpace I x)]`
diamond documented in `DowngradeNormFree.lean`). Note the `Continuous`→`Continuous` composition helper
`Bundle.continuous_bilinearComp₂_section` is blocked for the same reason (it carries the fibre-norm
section variable).

Four sorry-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive declarations
landed, sidestepping the wall via the **fiber-norm-free bundle section algebra** (`clm_bundle_comp`,
`contMDiff_flipBilinearFormSection_tangent_zero`, `add_section`) bridged to `Continuous` through
`contMDiff_zero_iff`:

* `bilinearFormSectionDeTurckReaction` (+`_apply`, +`_contMDiff_zero`, in `DeTurckCorrectionRegularity`)
  — the **generic-section** frozen-`P` symmetrized DeTurck derivation
  `x ↦ (s x).comp (P x) + ((s x).comp (P x)).flip` (fiber value `s(Pu,v)+s(Pv,u)`), generalizing
  `intrinsicDeTurckCorrectionSection` (the *metric*-section case, `P:=∇W`) to an arbitrary continuous
  section; `_apply` closes the `TangentSpace`-fibre `flip` instance-diamond via `congr`/defeq.
* `deTurckReactionSectionMap` (+`_apply`) — the reaction as a genuine **`CSS(TM) → CSS(TM)` operator**
  on the concrete `BilinearFormBundle` continuous section space the chart operator `A` acts on;
  well-definedness discharged fiber-norm-free. This is the tangent-bundle reaction operator the generic
  machinery could not provide.
* `deTurckReactionSectionMap_metricSection_apply_eq_intrinsicDeTurckCorrection` (in
  `DeTurckReactionAssembly`) — the operator with `P:=∇W` on the metric section **equals the geometric
  `intrinsicDeTurckCorrection`** (symmetrized fiber value matched via `ContMDiffRiemannianMetric.symm`).
* `deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS` —
  the affine `intrinsicRicciFlowRHSSectionSpace g t + deTurckReactionSectionMap ∇W (metric)` reproduces
  the **full geometric `intrinsicRicciDeTurckRHS`** on the metric state: the center-point verification
  of the chart `A`'s `geometric` field, in terms of the concrete TM operator + named Ricci source.

**Concrete next target.** Establish the section-space **coordinate `hlip`/`hcenter` bounds** for
`deTurckReactionSectionMap` (Lipschitz-in-`s`, since it is linear in `s`) directly at `TM`, then feed
the affine `A t s = intrinsicRicciFlowRHSSectionSpace g t + deTurckReactionSectionMap ∇W s` into the
already-committed topological-fibre section-space Picard bridge to obtain a genuine `IsPicardLindelof`
for the concrete tangent-bundle chart operator — the chart's `picard` field — with the `geometric`
field already anchored on the metric state above.

### Progress (2026-07-06, later 2) — the concrete tangent-bundle DeTurck reaction OPERATOR now has readout size bounds AT `TM`, and the TM AddCommGroup/VectorBundle diamond is mapped precisely

Six sorry-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive declarations
landed in the new `AnalyticPDE/GeometricReactionCoordBounds.lean`:

* `Bundle.readout_add_nf` / `readout_sub_nf` / `comp_readout_eq_nf` — the **fiber-norm-free** readout
  algebra: the trivialization readout is additive/subtractive in the fibre value, and carries a fibre
  first-slot composition `B.comp Q` to the *model*-fibre `(readout B).comp (inCoordinates … Q)`, all with
  only `AddCommGroup`/`Module`/`TopologicalSpace` fibre binders (no `SeminormedAddCommGroup`, no
  `bilinearComp`).
* `Bundle.flip_readout_eq_sn` / `norm_deTurckReaction_readout_le_sn` — the readout slot-flip identity and
  the `comp+flip`-shape reaction readout size bound `≤ 2·‖readout B‖·‖inCoord Q‖` (generic seminorm `W`).
* `RicciFlow.deTurckReactionSectionMap_readout_split` / `_readout_norm_le_two_comp` /
  `_readout_norm_le_of_comp_bound` — the **real geometric operator at `TM`**:
  `readout(deTurckReactionSectionMap … σ x) = readout((σ x).comp (P x)) + readout(((σ x).comp (P x)).flip)`,
  hence `‖readout(deTurck σ x)‖ ≤ 2·‖readout((σ x).comp (P x))‖`, hence `≤ 2·Kp·‖readout(σ x)‖` given a
  composition-readout bound `Kp`.  This is the `K = 2·Kp` section-space Picard `hlip`/`hcenter` fibre
  content for the concrete operator, obtained by connecting through the operator's own `Pi.add`-value
  (`readout_add_nf` + `rfl`) and discharging the flip readout fiber-norm-free via
  `trivializationAt_bilinearFormBundle_apply_eq` + definitional `flip_apply` (`rfl`).

**The diamond, mapped.**  `TangentSpace I x` is a non-reducible `def := E` deriving `AddCommGroup`/`Module`
but no norm; `instNormedAddCommGroupTangentSpace` (priority 70, flat-`E`) adds one.  This gives two defeq
but non-syntactic `AddCommGroup`/`Module` paths.  `bilinearComp`/`ContinuousLinearMap.flip` use the flat-`E`
path, while the operator's `Pi.add` uses the deriving path.  Empirically: `readout_add_nf` (no
`inCoordinates`) synthesizes at `TM`; but any lemma **statement** naming `inCoordinates E TM … (P x)`
(comp readout bound, coord=readout bridge) forces `VectorBundle ℝ E TM` on the flat-`E` path, clashing
with the section space's deriving path → `FiberBundle` synth failure or `isDefEq` timeout; and
`deTurckReactionSectionMap` in `coord` position makes `isDefEq` diverge (>4M heartbeats) even to state.

**Concrete next targets.** (A) the composition-readout `Kp` bound at `TM` phrased so `inCoordinates` does
not appear in the statement (supply `Kp := ‖inCoord P‖` from a generic-`W` site, or prove inline via
`trivializationAt_bilinearFormBundle_apply_eq`); (B) a `_topFibre`-style restatement of
`coord_apply`/`equivCompatibleCoordFamilySubmodule` (fibre `AddCommGroup`/`Module` as explicit binders) so
`coord = readout` holds at `TM`, then feed the operator readout bounds into the topological-fibre
section-space Picard bridge for the chart's `picard`.

### Progress (2026-07-06, later 3) — the geometric DeTurck reaction operator now has a CONCRETE `inCoordinates` readout size bound AND a fiber-norm-free `coord = readout` bridge at `TM`; the remaining `hlip`/`hcenter` are blocked by the section-NORM (metric) vs operator (hom) fibre-topology diamond

Three sorry-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive declarations
landed (new module `AnalyticPDE/GeometricReactionPicardTangent.lean` + additions to
`AnalyticPDE/GeometricReactionCoordBounds.lean`):

* `deTurckReactionSectionMap_comp_readout_norm_le_inCoordinates` /
  `deTurckReactionSectionMap_readout_norm_le_inCoordinates` (in `GeometricReactionCoordBounds`) — the
  **concrete `Kp` readout bound**: `‖readout(deTurckReactionSectionMap … σ x)‖ ≤
  2·‖inCoordinates E TM E TM x0 x x0 x (P x)‖·‖readout(σ x)‖`, at `TM`.  **Key empirical finding:
  naming `inCoordinates E TM E TM …` in a readout-bound STATEMENT elaborates fine at `TM`** (the plan's
  earlier "diamond blocks any `inCoordinates` statement" warning was over-broad — it only bites in
  `coord` position / when the section-norm is involved).  Supplies the `hcomp` hypothesis of the
  already-committed `deTurckReactionSectionMap_readout_norm_le_of_comp_bound` with a concrete
  `Kp := ‖inCoord (P x)‖`.
* `bilinearFormBundle_coord_eq_trivializationAt_readout_tangent` (plain sections) +
  `deTurckReactionSectionMap_coord_eq_readout` (operator corollary), in `GeometricReactionPicardTangent`
  — the **fiber-norm-free `coord = readout` bridge at `TM`**: `(coord σ).1 i x = (trivializationAt BilF
  BilW (x0 i) ⟨x, σ x⟩).2`.  The existing `bilinearFormBundle_coord_eq_trivializationAt_readout` demands
  `[∀ x, SeminormedAddCommGroup (W x)]` (Π-fibre-seminorm) → fails to synthesize `FiberBundle E TM`.
  **Resolution: prove it directly at `TM` by unfolding the `coord` definition (`coord_apply`'s simp set:
  `equivCompatibleCoordFamilySubmodule`, `toSubtype`, …, `linearMapAt_apply`) ON THE GOAL** — so the
  goal's own hom-bundle fibre topology (`ContinuousLinearMap.topologicalSpace`) is used consistently —
  rather than via `coord_apply`/`rw` (which re-synthesize the metric fibre topology and mismatch).
  Two plumbing facts discovered: (i) a bare-section binder `s`'s CoeFun `s x` leaves `et`/`hKc`
  metavars in the RHS ("function expected") — write **`s.toFun x`** instead; (ii) `coord_apply` cannot
  be *applied* to the operator (its `[∀ x, TopologicalSpace (V x)]` synthesizes the metric topology,
  clashing with the operator's hom topology), so the direct-unfold is essential.

**THE REMAINING BLOCKER (precise) — `hlip`/`hcenter` need the section NORM, which forces the metric
fibre topology, which isDefEq-DIVERGES against the operator's hom fibre topology.**  Both the
`_topFibre` Picard bridge inputs reduce to `‖coord σ i x‖ ≤ ‖σ‖` / `dist(coord s)(coord s') ≤ dist s s'`
i.e. `coord_norm_le_norm` / `coord_dist_le_dist`.  These lemmas are *fiber-norm-free in their section
binders*, BUT their conclusion mentions `‖s‖` (the section-space `NormedAddCommGroup`), whose instance
pulls in `[∀ x, SeminormedAddCommGroup (BilW x)]` → the **metric** fibre topology
`PseudoMetricSpace.toUniformSpace.toTopologicalSpace` on `BilW x`.  The concrete operator
`deTurckReactionSectionMap` (fiber-norm-free) produces sections whose type carries the **hom-bundle**
topology `ContinuousLinearMap.topologicalSpace`.  Applying `coord_norm_le_norm`/`coord_dist_le_dist` (or
even `apply`, or with `(V := BilW)` pinned) to a hom-typed operator section triggers
`(deterministic) timeout at whnf/isDefEq` (2M heartbeats) unifying the hom-vs-metric fibre topology on
`BilW x = TangentSpace I x →L TangentSpace I x →L ℝ`.  Root cause: the `TangentSpace I x` derived-module
(`def := E`) vs norm-module (`instNormedAddCommGroupTangentSpace`) `AddCommGroup` diamond (documented in
`DowngradeNormFree.lean`), propagated to `BilW x`, makes the two fibre topologies defeq-but-not-cheaply
so.  The `coord = readout` *equality* dodged this (unfold on the goal); the `≤ ‖σ‖` *inequality* cannot,
because `‖σ‖` itself is the metric-typed object.

**Concrete next target.** Provide a **hom-topology-native** `‖coord σ i x‖ ≤ ‖σ‖` /
`dist(coord s i x)(coord s' i x) ≤ dist s s'` for the `BilinearFormBundle`-at-`TM` section space, so the
operator's readout bounds become the `_topFibre` Picard `hlip`/`hcenter`.  Options: (a) reprove
`coord_norm_le_norm`/`coord_dist_le_dist` with the fibre topology as an EXPLICIT binder pinned to the
hom-bundle topology (a `_topFibre` variant of these two lemmas — none currently exists; only
`norm_le_of_forall_coord_norm_le_topFibre` (the reverse direction) does); or (b) a definition-site
alignment making `BilinearFormBundle`'s hom fibre topology defeq-cheap to the operator-norm metric
topology at `TM`.  With that single lemma, feed the frozen `A s = deTurckReactionSectionMap ∇W s + b`
(`hcont = continuousOn_const`) into
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre`
(which derives `Mc` internally) to obtain the chart's `picard`.

### Progress (2026-07-06, later 4) — the METRIC-vs-HOM fibre-topology blocker is RESOLVED, and the frozen geometric DeTurck reaction operator now has a genuine `IsPicardLindelof` at `W := TangentSpace I`

The precise blocker recorded in "later 3" (the section-NORM `hlip`/`hcenter` forcing the metric fibre
topology, isDefEq-diverging against the operator's hom fibre topology) is **CLOSED**.  Nine sorry-free,
axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), purely-additive declarations landed across
`ContinuousSection.lean`, `GeometricReactionCoordBounds.lean`, `GeometricReactionPicardTangent.lean`:

* **`coord_dist_le_dist_topFibre` / `coord_norm_le_norm_topFibre`** (+ helpers
  `coordContinuousMap_dist_le_dist_topFibre`, `coord_zero_apply_topFibre`), in the
  `TopologicalFibreCoordControl` section of `ContinuousSection.lean` — the pointwise `1`-Lipschitz
  coordinate contraction `dist (coord s i x) (coord t i x) ≤ dist s t` and norm-nonexpansiveness
  `‖coord s i x‖ ≤ ‖s‖`, restated with the fibre topology as an EXPLICIT `[∀ x, TopologicalSpace (V x)]`
  binder instead of derived from `SeminormedAddCommGroup (V x)`.  Every step is at the section-space
  `NormedAddCommGroup` / coordinate-family Banach-`F` level (`equivCompatibleCoordFamilySubmodule` is a
  definitional isometry), never touching a fibre norm, so the seminormed-fibre proofs port verbatim.
  **Empirically VALIDATED**: these apply DIRECTLY to `deTurckReactionSectionMap` operator sections at
  `TM` — no `whnf`/isDefEq divergence.  This is the "single lemma" the "later 3" concrete-next-target
  requested; it is the hom-topology-native `hlip`/`hcenter` handoff.

* **`deTurckReactionSectionMap_readout_eq_inCoordinates`** (value formula) +
  **`_readout_sub_norm_le_inCoordinates`** / **`_readout_sub_dist_le_inCoordinates`** +
  **`bilinearReaction_model_sub_norm_le`**, in `GeometricReactionCoordBounds.lean` — the operator's
  trivialization readout equals the model-fibre reaction value `(readout σx).comp Q + ((readout σx).comp
  Q).flip` (`Q := inCoordinates … (P x)`), via `_readout_split` + fiber-norm-free `comp_readout_eq_nf` +
  an INLINE flip identity through `trivializationAt_bilinearFormBundle_apply_eq` (dodging
  `flip_readout_eq_sn`, whose `[FiberBundle E TM]`/Π-fibre-seminorm binders fail to synthesize at `TM`);
  whence the readout DIFFERENCE is Lipschitz-in-state: `‖readout(deTurck s x) − readout(deTurck s' x)‖ ≤
  2·‖inCoord Px‖·‖readout(s x) − readout(s' x)‖` (reaction affine-linear in the bilinear slot; model
  bound via `opNorm_add_le`/`opNorm_flip`/`opNorm_comp_le`).  `dist_eq_norm` on the `BilF` fibre must be
  applied with EXPLICIT endpoints (the bare-goal `SeminormedAddGroup` metavar is "stuck" — the `BilF`
  diamond).

* **`deTurckReactionSectionMap_coord_dist_le_inCoordinates`** (the `hlip` field) +
  **`deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates`** (the `picard` datum),
  in `GeometricReactionPicardTangent.lean` — the concrete tangent-bundle operator obeys
  `dist (coord (deTurck s) i x) (coord (deTurck s') i x) ≤ 2·Kp·dist s s'` for any per-point
  `‖inCoord (xc i) x (P x)‖ ≤ Kp` (coord→readout, dist-form readout bound, readout→coord,
  `coord_dist_le_dist_topFibre`; `BilF`↔`TM` baseSet via `simpa`); and — given a UNIFORM `Kp` over the
  finite compact cover — the frozen (time-independent) reaction operator `t ↦ deTurckReactionSectionMap
  … hP` satisfies `IsPicardLindelof` about any initial section `σ₀`, radius `a`, Lipschitz `2·Kp`,
  auto-chosen forward endpoint `T ∈ (t₀, T₀]` and centre `Mc`.  Assembled by feeding the `hlip` bound
  (`K := 2·Kp`) and `continuousOn_const` (frozen ⇒ trivial `hcont`) to
  `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre`.

**Fractions of `{A, picard}` now constructed (frozen reaction summand).**  `A` = the concrete TM
operator `deTurckReactionSectionMap` (DONE earlier).  `picard`: `hlip` DONE (coordinate bound), `hcont`
DONE (`continuousOn_const`), and the `IsPicardLindelof` PACKAGING DONE — modulo a single UNIFORM-`Kp`
hypothesis.  So the frozen reaction's `IsPicardLindelof` is CONSTRUCTED at `TM`, Path B, diamond-free.

**Concrete next target.**  Discharge the uniform-`Kp` hypothesis: prove
`ContinuousOn (fun x ↦ ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)) (Kc i)`
(the existing `continuousAt_inCoordinates_of_continuous_homSection` gives continuity ONLY at the trivialization
centre `xc i`; a baseSet-wide `ContinuousOn` is needed — unfold `inCoordinates` and use the trivialization
coordinate-change continuity + `hP`), then `IsCompact.exists_bound_of_continuousOn` per `i` + a `Finite κ`
sup gives the uniform `Kp`.  Then add the `(-2)•Ric` source (affine: `hlip` unchanged since `b` cancels
in the difference; `hcont` still trivial if `Ric` is frozen at `g₀`, else time-continuous) and identify
`P := ∇W` (`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`) to obtain the chart's actual
`picard`, whose Banach evolution solution decodes to `RicciDeTurckChartClosureData.realization`.

### Progress (2026-07-06, later 5) — the frozen geometric DeTurck reaction operator's `IsPicardLindelof` is now UNCONDITIONAL at `TM` (uniform-`Kp` discharged by compactness)

Three further sorry-free, axiom-clean declarations landed in `GeometricReactionPicardTangent.lean`
(plus the reusable `continuousOn_inCoordinates_of_continuous_homSection` in `ContinuousSection.lean`):

* **`continuousOn_inCoordinates_of_continuous_homSection`** (`ContinuousSection.lean`, seminormed-fibre
  section) — strengthens `continuousAt_inCoordinates_of_continuous_homSection` (continuity only AT the
  centre) to `ContinuousOn` on the whole hom-bundle base set, via `hom_trivializationAt_apply` + the hom
  trivialization's continuity on its source.
* **`contOn_inCoord_tangent`** — the same `ContinuousOn` proved DIRECTLY at `TM` (the seminormed-fibre
  lemma above cannot be applied at `TM`: it re-requests `[FiberBundle E TM]` under the seminormed-fibre
  binder and hits the documented `FiberBundle E (TangentSpace I)` synth wall).  The inline proof at `TM`
  succeeds (the `THom` hom trivialization and its continuity synthesize fine in the `RicciFlow` context).
* **`exists_uniform_inCoord_bound`** — a UNIFORM `Kp` over the finite compact cover:
  `contOn_inCoord_tangent` per `i` + `IsCompact.exists_bound_of_continuousOn` on each `Kc i` +
  `Finite κ` sup.  This DISCHARGES the uniform-`Kp` hypothesis by compactness + continuity of `P`.
* **`deTurckReactionSectionMap_exists_isPicardLindelof`** — the UNCONDITIONAL frozen-reaction picard:
  combining `exists_uniform_inCoord_bound` with the conditional
  `_exists_isPicardLindelof_of_uniform_inCoordinates`, the frozen reaction operator satisfies
  `IsPicardLindelof` about any `σ₀` with NO uniform-`Kp` hypothesis — only continuity of `P` and the
  compact cover.  `BilinearFormBundle`↔`THom` trivializing sets coincide (both reduce to the `TangentSpace`
  trivializing set) via `simpa`.

**GAP 2 geometric-A `picard` status.**  For the FROZEN reaction operator `t ↦ deTurckReactionSectionMap
… ∇W`, the `IsPicardLindelof` datum is now FULLY CONSTRUCTED at `TM`, Path B, diamond-free, unconditional.

**Concrete next target.**  (i) Add the `(-2)•Ric` affine source `b := intrinsicRicciFlowRHSSectionSpace
g₀`: `hlip` is UNCHANGED (the fixed `b` cancels in the coordinate difference — `coord_add_apply`);
`hcont` stays `continuousOn_const` if `b` is frozen at `g₀` (else time-continuous); `hcenter`/`Mc` gains
`‖coord b‖`.  (ii) Identify `P := ∇W = (chosenLeviCivitaFamily g₀ t)(intrinsicDeTurckVectorField g₀
background t)` (continuity from `intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`), giving
the chart's actual `picard`.  (iii) Decode the resulting `BanachEvolutionLocalSolutionIn` to
`RicciDeTurckChartClosureData.realization` and supply `encode`, then feed `chart`+`D` to the bridge
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData`.

### Progress (2026-07-06, later 6) — the CONCRETE geometric frozen operator's `BanachEvolutionLocalSolutionIn` is now built end-to-end; the `geometric`-vs-`hbound` FORMULATION QUESTION resolved

Four sorry-free, axiom-clean declarations landed (in `GeometricReactionPicardTangent.lean`, plus one
reusable primitive in `ContinuousSection.lean`):

* **`coord_add_apply_topFibre`** (`ContinuousSection.lean`, `TopologicalFibreCoordControl` section) — the
  fibre-topology-native additivity of the compact coordinate readout,
  `(coord (s+t)).1 i x = (coord s).1 i x + (coord t).1 i x`, with an explicit
  `[∀ x, TopologicalSpace (V x)]` binder (the seminormed-fibre `coord_add_apply` does not apply at `TM`).
  This is the affine handoff the `BilinearFormBundle` hom fibre needs (verbatim port of `coord_add_apply`).
* **`deTurckReactionSectionMap_add_source_exists_isPicardLindelof`** (+ `_of_uniform_inCoordinates`) —
  UNCONDITIONAL `IsPicardLindelof` for the AFFINE operator `A t s = deTurckReactionSectionMap … hP s + b`
  (frozen reaction + a FIXED source `b`).  The fixed `b` is diagnostic-free for `hlip`: it contributes the
  same coordinate summand to `A t s` and `A t s'`, cancelling in the coordinate distance
  (`coord_add_apply_topFibre` then `dist_add_right`), so the reaction's `hlip` bound (Lipschitz `2·Kp`) is
  unchanged; `hcont` stays `continuousOn_const`; `Mc` (absorbing `‖coord b‖`) is derived by the bridge;
  uniform `Kp` discharged by `exists_uniform_inCoord_bound`.
* **`deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn`** — feeds that
  `IsPicardLindelof` to `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`
  (section space complete via `instCompleteSpace`, model fibre `BilF` complete) → a genuine
  `BanachEvolutionLocalSolutionIn` in any locus containing the Picard ball `closedBall σ₀ a`.
* **`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`** — the CONCRETE geometric
  specialisation: `P := ∇W = (chosenLeviCivitaFamily g t)(intrinsicDeTurckVectorField g background t)`
  (continuity from `intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, `C¹` background),
  `b := intrinsicRicciFlowRHSSectionSpace … g t` (the named `(-2)•Ric` CSS value).  The frozen geometric
  operator's Banach evolution solution is now constructed end-to-end, unconditional.

**FORMULATION QUESTION — RESOLVED (decisive for the next session).**  The chart's `geometric` field
(equivalently `hgeom` of `TimeDependentGeometricRicciDeTurckBanachChart.ofLipschitzBoundedContinuous`,
`SmoothRealization.lean:8395`) demands `chart.A τ s x u v = intrinsicRicciDeTurckRHS g background τ x u v`
POINTWISE for EVERY `s` in the positive-definite locus.  This FORCES `chart.A` to BE the genuine
(nonlinear, 2nd-order) Ricci–DeTurck RHS on the locus — a fixed FROZEN/mild linear operator agrees with
it only at the single metric section `s = (g t).toSection`, never for all `s` (ground-truth: the ONLY
non-vacuous `geometric :=` provider in the library is the empty-manifold case
`IsEmptyChartClosure.lean:119`; every other is a pass-through).  But `ofLipschitzBoundedContinuous` ALSO
demands `hbound : ‖A t x‖ ≤ L` on the C⁰ closed ball, which the genuine 2nd-order operator VIOLATES
(C⁰-unbounded).  Hence **the mild/bounded shortcut CANNOT close `geometric` + `hbound` simultaneously; the
genuine operator + a parabolic Schauder a-priori bound (GAP 2 long pole) is the only route** — the
Schauder bound is precisely what makes the genuine operator bounded on a Hölder ball (not the C⁰ ball).
The frozen-operator picard/Banach machinery built this session (and `coord_add_apply_topFibre`) is the
reusable linearisation/reference infrastructure the eventual Schauder chart will consume, but it does NOT
by itself inhabit `chart.A`.

**Fractions of `{A, picard, realization, encode}`.**  `A`: the frozen geometric operator + its Banach
solution are DONE, but the genuine `chart.A` (satisfying `geometric` on the whole locus) is NOT — it needs
the Schauder-bounded genuine operator.  `picard`: DONE for the frozen operator; for the genuine operator
it awaits the Schauder `hbound`.  `realization`/`encode`: still 0 (both are parametrised by a genuine
`chart`, which is not yet inhabited for positive-dimensional `M`).

**Concrete next target.**  Prove a genuine PIECE of the parabolic Schauder a-priori bound for the genuine
Ricci–DeTurck operator that yields `hbound : ‖A t x‖ ≤ L` on a Hölder ball about `g₀` (the missing
ingredient of `ofLipschitzBoundedContinuous`'s `hbound` in a Schauder norm), building on the completed
model heat-kernel Schauder toolkit (`heatMild*` / `HeatKernelParabolicC0Alpha`).  Do NOT attempt to make a
frozen linear operator serve as `chart.A` — `geometric` provably forbids it for positive-dimensional `M`.

### Progress (2026-07-06, later 7) — Item 2 GAP 1: the chart-conjugation `C³` transfer that lifts the model flow tower to compact-`M` slice regularity is BUILT (both routes); and the Item-3 `picard` structural blocker SHARPENED

**Strategic pivot this session.** A ground-truth read-only re-audit of the Item-3 chart route sharpened
the prior formulation resolution into a *structural* blocker: the chart field
`picard : IsPicardLindelof chart.A … a 0 L Kpic` is Mathlib's `IsPicardLindelof`, whose `norm_le`
field demands `∀ t x ∈ closedBall (g₀.toSection) a, ‖chart.A t x‖ ≤ L` **in the `ContinuousSectionSpace`
(C⁰/sup) norm on a C⁰ ball**.  For positive-dimensional `M` the `realization` decode forces `chart.A`
to agree, along its Banach solution, with the genuine 2nd-order Ricci–DeTurck RHS (a `C²`-input,
C⁰-unbounded operator), which is not even a well-defined `CSS → CSS` map, let alone C⁰-bounded on a C⁰
ball.  So **no Hölder/Schauder a-priori bound inhabits `picard` as typed** — the ball in `norm_le` is
the C⁰ `CSS` ball, not a Hölder ball.  The frozen-operator picard/Banach machinery (all prior sessions)
is genuine but off this critical path.  Given that, the session pivoted to the **tractable GAP 1**
(Item 2 compact chart-transfer), where the model-manifold `C³` smooth-dependence tower is DONE and the
compact **gluing** machinery (`Diffeomorph3FlowExistence.exists_…_gaugeFlow_…_localGluingData_…`) is
DONE — the missing link is constructing the per-chart local `C³` flow data from the tower.

**Ground-truth GAP-1 map.**  The compact gauge-flow has two routes, both reducing to *local, chart-
confined* `C³` regularity of the flow slices (never the global crossing-charts problem):
* Route A (`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`) needs
  `hslicesC3` = `∀ t, ContMDiff I I 3 (Φ t)` (global slice `C³`).
* Route B (the `…_localGluingData_…` gluing family) needs, per chart `i` and time `t`,
  `RicciFlow.LocalGluingData 3 (Fₗ i t) (Gₗ i t) (U t i) (V t i)`, whose only analytic fields are
  `forward_contMDiffOn`/`backward_contMDiffOn` = `ContMDiffOn I I 3` on chart-confined opens.

Nothing in the library constructed either from the model tower.  Three sorry-free, axiom-clean
declarations landed in `GaugeReduction/GaugeFlowAssembly.lean` closing exactly this link:

* **`contMDiffOn_of_extChartAt_conjugation`** — the core transfer: if on an open `U ⊆ (chartAt x₀).source`
  the map `F` is represented in the extended charts at `x₀`/`F x₀` by a globally-`C³` model map
  `Ψ : E → E` (`extChartAt I (F x₀) (F x) = Ψ (extChartAt I x₀ x)` on `U`) and `F` maps `U` into the
  source chart at `F x₀`, then `ContMDiffOn I I 3 F U`.  Proof: factor `F =
  (extChartAt I (F x₀)).symm ∘ Ψ ∘ (extChartAt I x₀)` on `U` (chart left-inverse), compose the two
  `ContMDiffOn` chart maps (`contMDiffOn_extChartAt`/`_symm`) with `Ψ` (`contMDiff_iff_contDiff`).
* **`localGluingData_ofChartConjugation`** — bundles the transfer for the forward slice `F` and its
  local inverse `G` (plus open-ness, mapping, mutual-inverse data) into exactly
  `RicciFlow.LocalGluingData 3 F G U V` — the Route B per-chart `hlocal` input.
* **`contMDiff_of_forall_extChartAt_conjugation`** — glues per-point chart-conjugation witnesses into
  global `ContMDiff I I 3 F` (`ContMDiff` = `∀ x, ContMDiffAt`, each via `ContMDiffOn.contMDiffAt` on
  the neighbourhood) — the `ContMDiff I I 3 (Φ t)` content of Route A's `hslicesC3`.

**Fractions of GAP 1.**  The tower→compact `C³`-regularity *transfer interface* is now DONE for both
routes: given, per chart, the model `C³` representative `Ψ` and the chart-representation identity
`hconj`, the local/global slice `C³` regularity (and the `LocalGluingData 3` package) follow with zero
sorry/axiom.

**Concrete next target.**  Produce `Ψ` and `hconj` from the *actual* compact flow: (i) the tangent-chart
push of the `C³` DeTurck gauge field `X` is a `ContDiff ℝ 3` model field `v` on the chart target;
(ii) its model flow `Ψ` (from `SmoothDependenceManifold.exists_flow_diffeomorph_three`) is globally
`C³`; (iii) `hconj` — the manifold flow slice reads in charts as `Ψ` — follows from integral-curve
uniqueness (the manifold flow's chart representation solves the pushed ODE).  Feeding those to the three
transfer lemmas above discharges `hslicesC3` / the `hlocal` `LocalGluingData 3`, closing GAP 1
unconditionally.  Do NOT route the genuine 2nd-order operator through `chart.A`'s C⁰ `picard` — the
`IsPicardLindelof.norm_le` C⁰-ball bound provably forbids it for positive-dimensional `M`.

### Progress (2026-07-06, later 8) — Item 2 GAP 1: the RAW-flow (C³-free) chart-representation derivative toolkit is BUILT; and the Item-3 picard/realization tension is RE-AUDITED (weaker than "structurally impossible")

**Ground-truth re-audit of the Item-3 blocker (sharpens, and partly WALKS BACK, later-7's "structurally
impossible" claim).**  Reading the actual field types: the chart's `geometric` field
(`AnalyticPDE.lean:4022`) is `∀ τ s ∈ locus, ∃ g background, A τ s = intrinsicRicciDeTurckRHS g background τ`
— the metric family `g` and connection `background` are existentially quantified **per `(τ,s)`**, so
`geometric` does NOT force `chart.A` to BE the genuine operator (a state-independent representative
satisfies it by choosing `g,background` freely).  Decisively, the `realization` binding constraint is the
`RicciDeTurckSmoothRealizationData` field `chartRHS_eq_intrinsic` (`SmoothRealization.lean:2432`):
`chart.A t (sol.curve t) x u v = intrinsicRicciDeTurckRHS metric background t x u v` **only along the
solution curve** `sol.curve t` (a smooth metric section via `metric_eq_curve`), NOT on the whole C⁰ ball.
So `picard` (C⁰-bounded `A` on a C⁰ ball) and `realization` are RECONCILABLE: `chart.A` may be a
bounded/regularised operator that coincides with the genuine 2nd-order RHS only along ONE constructed
smooth solution curve.  The catch: that smooth realization `metric` (with `metricTensor metric = sol.curve`)
must be a genuine Ricci–DeTurck flow — i.e. it is exactly what the geometric gauge flow (Items 1 & 2)
supplies.  **Conclusion: the Item-3 chart closure genuinely DEPENDS on Items 1 & 2; the critical path runs
through the geometric flow (GAP 1), confirming the pivot.**

**What landed (all in `GaugeReduction/GaugeFlowAssembly.lean`, sorry-free, axiom-clean).**  The last
session built the tower→compact chart-conjugation *transfer interface*
(`contMDiffOn_of_extChartAt_conjugation` etc.), whose `hconj` input rests on the flow curve's chart
representation solving a model ODE.  Every repo lemma providing that
(`Diffeomorph3GaugeFlowOn.hasDerivWithinAt_extChartAt_eval*`) is stated on `Diffeomorph3GaugeFlowOn`,
which **presupposes `C³`** — circular for `hslicesC3` (which must ESTABLISH `C³` from the *raw* compact
flow, known only `C¹`).  The missing brick is the **raw (C³-free) analogue**, now proved as four lemmas:
* **`hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt`** — for an abstract curve `γ : ℝ → M`
  satisfying the bare flow ODE `HasMFDerivWithinAt … γ s t ((1).smulRight w)` (the hypothesis shape the
  compact flow supplies pre-regularity), the chart representation `τ ↦ extChartAt I p (γ τ)` in any
  preferred chart containing `γ t` has within-set derivative `tangentCoordChange I (γ t) p (γ t) w`.
  Proof = model ODE chain rule (`hasMFDerivWithinAt_extChartAt` ∘ `hγ`, then
  `mfderiv_chartAt_eq_tangentCoordChange`).  This is the C³-free analogue of
  `Diffeomorph3GaugeFlowOn.hasDerivWithinAt_extChartAt_eval_of_mem_source`.
* **`hasDerivWithinAt_extChartAt_comp_self_of_hasMFDerivWithinAt`** — centered (`p := γ t`) form via
  `tangentCoordChange_self`, derivative = the flow velocity `w`.
* **`hasDerivAt_extChartAt_comp_of_hasMFDerivWithinAt`** (+ `_self`) — on the OPEN flow window
  `Set.Ioo (-ε) ε` (a `𝓝 t` at interior times), the within-set derivative upgrades to a full `HasDerivAt`
  (`HasDerivWithinAt.hasDerivAt`), the form Mathlib's `IsIntegralCurve`/`ODE_solution_unique` uniqueness
  API consumes.

**Fractions of GAP 1.**  The raw compact flow's chart representation is now known to solve a model ODE
(as `HasDerivAt`, on the open window) with ZERO spatial-regularity assumption — the datum the model-`C³`
smooth-dependence tower and integral-curve uniqueness need to pin `Φ t`'s chart rep to a model-`C³` flow.
Remaining for `hslicesC3`: (i) the chart-pushforward model field `vpush` (via `(extChartAt I p).symm`) is
globally `C^{3,1}` so `exists_flow_diffeomorph_three` yields the model flow `Ψ` (the genuine analytic
long-pole — `tangentCoordChange`/transition-map regularity); (ii) integral-curve uniqueness identifies
`Φ t`'s chart rep with `Ψ`, giving `hconj`; (iii) compose the source→target chart transition and cover
the (compact) trajectory by finitely many charts for arbitrary window-`t`.

**Concrete next target.**  Prove the chart-pushforward field identity feeding uniqueness: the raw flow's
chart rep is an integral curve of the pushed field `vpush τ q := tangentCoordChange I ((extChartAt I p).symm q)
p ((extChartAt I p).symm q) (X τ ((extChartAt I p).symm q))` on a chart-confined sub-window (immediate from
`hasDerivAt_extChartAt_comp_of_hasMFDerivWithinAt` + `PartialEquiv.left_inv`), then the single-chart
`hconj` from `eqOn_Icc_of_lipschitzOnWith` (ModelGaugeFlowODE) once `vpush` is shown Lipschitz — the first
genuine consumer of the raw-flow chart-rep toolkit.  Do NOT rebuild trivial-case chart closures.

### Progress (2026-07-06, later 9) — Item 2 GAP 1: the chart-pushforward field `vpush` is DEFINED, the raw flow's chart rep is PROVED to be its integral curve, and the temporal integral-curve UNIQUENESS + the fixed-chart-target `C³` transfer are BUILT (the temporal→spatial bridge, modulo the model flow `Ψ` + its `C³`)

**What landed (all in `GaugeReduction/GaugeFlowAssembly.lean`, sorry-free, axiom-clean:
`{propext, Classical.choice, Quot.sound}`).**  The previous session left the raw (`C³`-free) chart-rep
derivative toolkit and named the concrete next target: the pushed field `vpush` and the raw flow's chart
rep as its integral curve.  That target is now DONE, plus the uniqueness consumer and the transfer variant
it needs:

* **`chartPushforwardField`** (the `vpush` of the plan) — `noncomputable def … (X : ℝ → M → E) (p : M)
  (τ : ℝ) (q : E) : E := tangentCoordChange I ((extChartAt I p).symm q) p ((extChartAt I p).symm q)
  (X τ ((extChartAt I p).symm q))`.  **Key formulation choice**: typing the base field as `X : ℝ → M → E`
  (into the model space, not a point-dependent `TangentSpace I x`) removes ALL dependent-type obstruction
  from the chart-image reduction below — `X τ y : E` unconditionally, so the `left_inv` rewrite has a
  type-correct motive.  This is the model-space vector field `f : ℝ → E → E` feeding the model ODE
  uniqueness API.
* **`chartPushforwardField_extChartAt`** — at a chart image `q = extChartAt I p y` with `y ∈ source`, the
  field reduces (via `PartialEquiv.left_inv`) to `tangentCoordChange I y p y (X τ y)`.
* **`hasDerivWithinAt_extChartAt_comp_chartPushforwardField`** (+ **`hasDerivAt_…`**) — **the raw flow's
  chart rep IS an integral curve of `chartPushforwardField`**: for `γ` solving the bare manifold flow ODE
  `HasMFDerivWithinAt … ((1).smulRight (X t (γ t)))` with `γ t ∈ (extChartAt I p).source`, the chart rep
  `τ ↦ extChartAt I p (γ τ)` has derivative `chartPushforwardField I X p t (extChartAt I p (γ t))` — i.e.
  exactly the `ModelGaugeFlowODE.LocalFlowSolution`-shaped datum `HasDerivWithinAt (flow) (f t (flow t)) s
  t`, with NO spatial regularity assumed.  The first genuine consumer of the raw-flow chart-rep toolkit.
* **`extChartAt_comp_eqOn_of_lipschitzOnWith`** — the integral-curve UNIQUENESS: the raw flow's chart rep
  equals ANY co-integral curve `g : ℝ → E` of the same `chartPushforwardField` that agrees at an interior
  time, provided the field is `LipschitzOnWith K` on a state tube containing both curves (via Mathlib
  `ODE_solution_unique_of_mem_Ioo`, consuming `hasDerivAt_extChartAt_comp_chartPushforwardField`).  With
  `g := ` the model flow curve `τ ↦ Ψ τ (extChartAt I p x)` this is step (ii): it pins the chart rep to
  the model flow `Ψ`.
* **`contMDiffOn_of_extChartAt_conjugation'`** — the chart-conjugation `C³` transfer with an INDEPENDENT
  target chart centre `y₀` (the original hardcodes `F x₀`).  The temporal identity uses a single fixed
  chart `p` for source AND target, so its fixed-time spatial identity `extChartAt I p (Φ t x) =
  Ψ t (extChartAt I p x)` has target centre `p ≠ Φ t p`; this variant lets that identity discharge
  `ContMDiffOn I I 3 (Φ t)` on the chart patch — the spatial-`C³` (`hslicesC3`) payoff of step (iii).

**How they compose (the temporal→spatial bridge, now complete modulo the model flow).**  For a flow slice
`Φ t` on a chart-confined patch `U`: apply `extChartAt_comp_eqOn_of_lipschitzOnWith` per `x ∈ U` (with
`γ := fun τ ↦ Φ τ x`, `g := fun τ ↦ Ψ τ (extChartAt I p x)`) → temporal `EqOn`; evaluate at `t` →
`hconj : ∀ x ∈ U, extChartAt I p (Φ t x) = Ψ t (extChartAt I p x)`; feed to
`contMDiffOn_of_extChartAt_conjugation'` (`x₀ = y₀ = p`) with `hΨ : ContDiff ℝ 3 (Ψ t)` →
`ContMDiffOn I I 3 (Φ t) U`; glue over a finite chart cover via
`contMDiff_of_forall_extChartAt_conjugation`.  **Every step now exists EXCEPT the model flow `Ψ` itself
and its two regularity inputs**: (a) `chartPushforwardField` is `LipschitzOnWith` on a tube (`hlip`), and
(b) `Ψ τ` is `ContDiff ℝ 3` in the initial condition — BOTH are the `tangentCoordChange`/transition-map
regularity + `exists_flow_diffeomorph_three` smooth-dependence long-pole.

**Fractions of GAP 1.**  Steps (ii) [integral-curve uniqueness] and the target-centre-flexible half of
(iii) [spatial-`C³` transfer] are DONE.  The remaining GAP-1 core is the single analytic long-pole (i):
construct the model flow `Ψ` of `chartPushforwardField` and prove it `C³` in the initial condition, which
reduces to (a) `chartPushforwardField` `Lipschitz`/`C^{3,1}` in `q` — the crux being regularity of the
VARYING-source-centre `tangentCoordChange I y p y` (both slots move with `y`), NOT the fixed-centre
`continuousOn_tangentCoordChange` — and (b) feeding it to `exists_flow_diffeomorph_three`.

**Concrete next target.**  Attack the long-pole bottom-up: prove `chartPushforwardField` is `ContinuousOn`
(then `LipschitzOnWith`, on a chart-confined tube) in `q`, decomposing `q ↦ (extChartAt I p).symm q`
(chart-symm continuity) ∘ `y ↦ tangentCoordChange I y p y` (the varying-centre transition-map regularity —
the genuine crux; look for a joint-continuity/`ContMDiff` route via `tangentBundleCore` or the
`contMDiffOn_ext_coord_change` chain, NOT the fixed-centre lemma) ∘ `y ↦ X τ y` (base-field regularity).
Do NOT rebuild trivial-case chart closures; the fixed-chart temporal→spatial bridge above is the route.

### Progress (2026-07-06, later 10) — Item 2 GAP 1: the chart-pushforward field regularity chain is DONE (`ContinuousOn` → `ContDiffOn` → `LipschitzOnWith`), and the "varying-centre" formulation question is RESOLVED

**What landed (all in `GaugeReduction/GaugeFlowAssembly.lean`, sorry-free, axiom-clean:
`{propext, Classical.choice, Quot.sound}`).**  The previous session named the next target as proving
`chartPushforwardField` `ContinuousOn`/`LipschitzOnWith` in `q`, decomposing through the varying-centre
`tangentCoordChange I y p y`.  That decomposition is the WRONG route and the plan's stated target was
UNDER-hypothesised: the isolated varying-source-centre map `y ↦ tangentCoordChange I y p y` is genuinely
**discontinuous** — its source chart `chartAt H y` jumps with `y`, and via `tangentCoordChange_comp` the
map is the inverse of `tangentCoordChange I p y y`, which still reads the varying chart at `y`.  So NO
fixed-centre/`tangentBundleCore` joint-continuity route exists for an arbitrary base field `X`.  The
**correct route** (this is the resolution): `tangentCoordChange I y p y (X τ y)` is exactly the second
component of the tangent-bundle trivialization `trivializationAt E (TangentSpace I) p` applied to the
section value `⟨y, X τ y⟩` (`TangentBundle.trivializationAt_apply` — both unfold to the same
`fderivWithin ℝ (extChartAt I p ∘ (extChartAt I y).symm) (range I) (extChartAt I y y)`), so regularity
holds **only through the section**, requiring `y ↦ ⟨y, X τ y⟩` to be a genuine continuous / `C^n` section
of the tangent bundle.  The three regularity lemmas, each with that section hypothesis:

* **`continuousOn_chartPushforwardField`** — from `ContinuousOn (fun y => ⟨y, X τ y⟩) (extChartAt I p).source`
  (a continuous tangent-bundle section), `ContinuousOn (chartPushforwardField I X p τ) (extChartAt I p).target`.
  Proof: identify the field on the target with `Prod.snd ∘ trivializationAt … p ∘ section ∘ (extChartAt I p).symm`,
  each factor `ContinuousOn` (trivialization via `Trivialization.continuousOn`).
* **`contDiffOn_chartPushforwardField`** — the `C^n` analogue (`{n} [IsManifold I n M]
  [ContMDiffVectorBundle n E (TangentSpace I) I]`): from `ContMDiffOn I (I.prod 𝓘(ℝ,E)) n (section)
  (extChartAt I p).source`, `ContDiffOn ℝ n (chartPushforwardField I X p τ) (extChartAt I p).target`.
  Uses the **fixed-trivialization** section characterisation `Bundle.Trivialization.contMDiffOn_iff`
  (centred at `p`, not the varying base point, via `MemTrivializationAtlas (trivializationAt E (TangentSpace I) p)`),
  then `contMDiffOn_iff_contDiffOn`.  This is the `C^1`→Lipschitz-ready form.
* **`exists_lipschitzOnWith_chartPushforwardField`** — from the same `C^n` section (`n ≠ 0`) and a convex
  compact `s ⊆ (extChartAt I p).target`, `∃ K, LipschitzOnWith K (chartPushforwardField I X p τ) s`, via
  `ContDiffOn.exists_lipschitzOnWith`.  This is exactly the field-Lipschitz datum consumed by the `hlip`
  hypothesis of `extChartAt_comp_eqOn_of_lipschitzOnWith` (with `s :=` the state tube `state t`).

**Fractions of GAP 1.**  The field-regularity input to the temporal integral-curve uniqueness comparison
(`hlip`) is now supplied.  Remaining GAP-1 core: (i) the model comparison flow `Ψ` of
`chartPushforwardField` and its `C³`-in-initial-condition regularity — the single analytic long-pole,
which reduces to feeding a **globally**-`C^{3,1}` field on all of `E` to `exists_flow_diffeomorph_three`
(`AnalyticPDE/SmoothDependenceManifold.lean:245`); (ii) that theorem needs a SINGLE global Lipschitz
constant + globally-Lipschitz `Dv`/`D2v`/`D3v`, whereas `chartPushforwardField` is regular only on the
chart target — so the next brick is the **bump-function globalisation** of `chartPushforwardField` (cut
off to a compactly-supported globally-`C^{3,1}` field agreeing with it on a neighbourhood of the compact
trajectory), whose flow then feeds `exists_flow_diffeomorph_three` to build `Ψ`.

**Concrete next target.**  The bump-function globalisation: given the compact trajectory sits inside the
chart patch, multiply `chartPushforwardField I X p τ` (extended by `0` off the target, or precomposed with
a fixed chart-symm) by a smooth cutoff `χ : E → ℝ` supported in the chart target and `≡ 1` on a
neighbourhood of the trajectory, obtaining a globally-`C^{3,1}` `v : ℝ → E → E` with a single global
Lipschitz constant; prove its flow agrees with the raw-flow chart representation on the trajectory window
(via `extChartAt_comp_eqOn_of_lipschitzOnWith` with `g := Ψ`), giving `hslicesC3`.  Do NOT rebuild
trivial-case chart closures.

### Progress (2026-07-06, later 11) — Item 2 GAP 1: the compact-support gauge-flow ENTRY POINT is DONE — `exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` inhabits the raw `C³` gauge flow from a compactly-supported `C^N` (`N ≥ 4`) field ALONE, and the bump-globalisation cutoff-product brick is proved

**What landed (all in `AnalyticPDE/ModelManifoldGaugeFlow.lean`, sorry-free, axiom-clean:
`{propext, Classical.choice, Quot.sound}`).**  The previous session named the next target as the
bump-function globalisation feeding `exists_flow_diffeomorph_three`.  A ground-truth read showed the
`ContDiff`-packaged corollary `exists_diffeomorph3GaugeFlowOn_of_contDiff` already discharges the entire
explicit `C^{3,1}` multilinear jet from a single `ContDiff ℝ n (uncurry v)` plus **five uniform-in-time
Lipschitz bounds** on the spatial-derivative fields.  So the real remaining analytic content is *only*
those five uniform bounds, which for a **compactly-supported** field are pure model-space facts.  Seven
reusable bricks, ending in the full compact-support entry point:

* **`norm_iteratedFDeriv_prodMk_left_le`** — `‖iteratedFDeriv ℝ n (fun y ↦ F (s, y)) x‖ ≤
  ‖iteratedFDeriv ℝ n F (s, x)‖`.  The time-slice factors as `(p ↦ F (p + (s,0))) ∘ inr` with
  `inr : E →L ℝ × E` the norm-`≤ 1` inclusion; `ContinuousLinearMap.iteratedFDeriv_comp_right` +
  `iteratedFDeriv_comp_add_right` + `ContinuousMultilinearMap.norm_compContinuousLinearMap_le` +
  `ContinuousLinearMap.norm_inr_le_one`.
* **`exists_bound_iteratedFDeriv_prodMk_left`** — `HasCompactSupport F` ⇒ the slice iterated derivatives
  are **uniformly bounded** in `(s, y)` (`HasCompactSupport.iteratedFDeriv` +
  `HasCompactSupport.exists_bound_of_continuous`, dominated via the slice bound).
* **`exists_lipschitzWith_iteratedFDeriv_prodMk_left`** — a single uniform Lipschitz constant for
  `iteratedFDeriv ℝ n (fun y ↦ F (s,y))` over all `s` (order-`(n+1)` uniform bound +
  `norm_fderiv_iteratedFDeriv` + `lipschitzWith_of_nnnorm_fderiv_le`).  This is the `hD2vmlip`/`hD3vlip`
  shape (orders 2, 3).
* **`exists_lipschitzWith_prodMk_left`** — the same for the slices *themselves* (`hv`), via
  `norm_iteratedFDeriv_one`.
* **`lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ`** — transports a
  `LipschitzWith` bound on `iteratedFDeriv (n+1) f` to `fderiv (iteratedFDeriv n f)` across the currying
  `LinearIsometryEquiv` (`fderiv_iteratedFDeriv` `rfl` + `Isometry.lipschitzWith_iff`).  The `hD3vmlip`
  shape (same constant `M₃` as `hD3vlip`).
* **`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport`** — **the entry point**: from
  `ContDiff ℝ N (uncurry v)` (`N ≥ 4`) + `HasCompactSupport (uncurry v)` ALONE (no separately-supplied
  jet constants), `Nonempty (Diffeomorph3GaugeFlowOn (X := v) s t₀)` on the model manifold `E`.  The two
  nested-`fderiv` hypotheses `hDvlip`/`hD2vclip` are discharged through the two-fold curry `curry2`
  (norm-nonexpansive `norm_curry2_le`, linear `curry2_sub` ⇒ `LipschitzWith 1`) + the uniform order-2
  bound; the rest from the bricks above.  Constants supplied explicitly.
* **`contDiff_and_hasCompactSupport_cutoff_smul`** — the bump-globalisation step: a cutoff multiple
  `χ • w` of a locally-`C^n` field `w` (`ContDiffOn ℝ n w U`) by a globally-`C^n`, compactly-supported
  cutoff `χ` with `tsupport χ ⊆ U` is globally `C^n` AND compactly supported (extension-by-zero:
  `ContDiffOn.contDiffAt` inside `U`, `image_eq_zero_of_notMem_tsupport` off `tsupport χ`).

**Fractions of GAP 1.**  The temporal→spatial bridge (integral-curve uniqueness + fixed-chart-target
`C³` transfer) and the chart-field regularity chain were already done; NOW the entire model flow `Ψ`
construction is reduced to producing a *compactly-supported `C^N` (`N ≥ 4`) representative* of the chart
pushforward field and calling the entry point — the two hardest ingredients (the explicit jet + its
global Lipschitz constants, and the compact-support globalisation smoothness) are supplied.

**Concrete next target.**  Assemble the model flow `Ψ`: (i) establish **joint** `(τ, y)`-smoothness of
the section `y ↦ ⟨y, X τ y⟩` ⇒ joint `ContDiffOn ℝ N (chartPushforwardField)` on
`ℝ ×ˢ (extChartAt I p).target` (the current `contDiffOn_chartPushforwardField` is per-fixed-`τ`; lift to
joint via the joint-smooth section); (ii) pick a smooth cutoff `χ : ℝ × E → ℝ` compactly supported in a
neighbourhood of the (compact) trajectory inside `ℝ ×ˢ target` and `≡ 1` near it
(`IsOpen.exists_contDiff_...`); (iii) feed `w := uncurry (chartPushforwardField …)` and `χ` to
`contDiff_and_hasCompactSupport_cutoff_smul` (with `H := ℝ × E`) ⇒ compactly-supported `C^N` field `v`;
(iv) `exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` ⇒ the raw `C³` gauge flow / `Ψ`;
(v) flow agreement on the trajectory window via `extChartAt_comp_eqOn_of_lipschitzOnWith` (the field
equals the un-cut chart pushforward field where `χ ≡ 1`) + `contMDiffOn_of_extChartAt_conjugation'` ⇒
`hslicesC3`.  Do NOT rebuild trivial-case chart closures.

### Progress (2026-07-06, later 12) — Item 2 GAP 1: steps (i), (iii), (iv) of the model flow `Ψ` assembly are DONE — the bump-globalised chart pushforward field now produces a real `Diffeomorph3GaugeFlowOn` from joint section smoothness + a chart-target cutoff

**What landed (sorry-free, axiom-clean `{propext, Classical.choice, Quot.sound}`).**

* **`contDiffOn_prod_chartPushforwardField`** (`GaugeReduction/GaugeFlowAssembly.lean`) — GAP-1 step (i):
  the joint `(τ, q)` `ContDiffOn ℝ n` of the chart pushforward field on `ℝ ×ˢ (extChartAt I p).target`,
  from joint `C^n` regularity of the time-dependent section `(τ, y) ↦ ⟨y, X τ y⟩` on
  `ℝ ×ˢ (extChartAt I p).source` (product model `𝓘(ℝ,ℝ).prod I`).  Runs the fixed-`p`-trivialization
  characterisation (`Bundle.Trivialization.contMDiffOn_iff`) over the product source `ℝ × M`, composes
  with the time-passenger chart inverse `(τ, q) ↦ (τ, symm q)` built from **CLM projections**
  (`ContinuousLinearMap.fst/snd`, self-charted `ℝ × E`) to sidestep the product-charted `whnf`
  instance-diamond, and reads off through `contMDiffOn_iff_contDiffOn`.  **Plumbing note:** the earlier
  attempt via `rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]` on a product-charted `hcomp`, and
  a fully-spelled type annotation on `hcomp := hsnd.comp hΦ …`, each triggered a `whnf` timeout
  (infinite, not slow — persisted at 1.2M heartbeats).  Fix: build `hΦ` with **self-charted** `ℝ × E`
  source via CLM projections, and **omit the `hcomp` type annotation** (let it infer, then
  `simp only [Function.comp_apply]` in the `congr`).
* **`contDiff_hasCompactSupport_cutoff_chartPushforwardField`** (`AnalyticPDE/ModelManifoldGaugeFlow.lean`)
  — GAP-1 step (iii): `contDiffOn_prod_chartPushforwardField` + `contDiff_and_hasCompactSupport_cutoff_smul`
  ⇒ the cutoff multiple `(τ, q) ↦ χ (τ, q) • chartPushforwardField I X p τ q` is globally `ContDiff ℝ N`
  on `ℝ × E` with compact support (chart target open via `isOpen_extChartAt_target`, needs
  `[I.Boundaryless]`).
* **`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`** (same file) — GAP-1 step (iv) capstone:
  feeds that `(ContDiff, HasCompactSupport)` pair to
  `exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` ⇒ a real
  `Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ,E)) (M := E) (X := fun τ q ↦ χ (τ,q) • chartPushforwardField …) s t₀`
  — the model comparison flow `Ψ`.  (`Function.uncurry v = fun r ↦ χ r • cpf r.1 r.2` holds by `Prod`-eta
  defeq, so the step-(iii) pair applies directly.)

**Concrete next target.**  Two GAP-1 residuals remain between these and the compact-manifold gauge-flow
lift: **(a)** step (ii) — construct the cutoff `χ : ℝ × E → ℝ`, `C^N`, compactly supported in
`ℝ ×ˢ (extChartAt I p).target` and `≡ 1` on a neighbourhood of the (compact) trajectory window
`Icc(-ε)ε ×ˢ {chart image of the compact orbit}` (`IsOpen.exists_contDiff_eqOn_one`-style bump around a
compact set inside an open set); **(b)** supply the joint section-smoothness hypothesis `hX` from the
actual gauge field `X` (currently assumed).  Then step (v) wires `Ψ` to `hslicesC3` via
`extChartAt_comp_eqOn_of_lipschitzOnWith` (field agrees with the un-cut pushforward where `χ ≡ 1`) +
`contMDiffOn_of_extChartAt_conjugation'`.  Do NOT rebuild trivial-case chart closures.

### Progress (2026-07-06, later 13) — Item 2 GAP 1: step (ii) cutoff `χ` is CONSTRUCTED (residual (a) closed), the window corollary packages it with `Ψ`, and the model-flow→step-(v) interface (`hΨ`/`hg'` readouts) is built

**What landed (sorry-free, axiom-clean `{propext, Classical.choice, Quot.sound}`; all in
`AnalyticPDE/ModelManifoldGaugeFlow.lean`).**

* **`exists_contDiff_cutoff_one_nhdsSet_of_isCompact`** — GAP-1 step (ii), residual (a) CLOSED. On a
  finite-dimensional real normed space `F`, for a compact `K` inside an open `U`, a globally-`C^n`
  cutoff `χ : F → ℝ` with compact support, `tsupport χ ⊆ U`, `∀ᶠ x in 𝓝ˢ K, χ x = 1`, and
  `0 ≤ χ ≤ 1`. Construction: interpose a compact `L` with `K ⊆ interior L ⊆ L ⊆ U`
  (`exists_compact_between`, local compactness), apply the model-manifold cutoff
  `exists_contMDiffMap_one_nhds_of_subset_interior` on `𝓘(ℝ, F)`, read `support ⊆ L` (compact) for
  `HasCompactSupport` and `tsupport ⊆ L ⊆ U`, and transfer `ContMDiff → ContDiff`
  (`contMDiff_iff_contDiff`).
* **`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`** — steps (ii)+(iv) packaged.
  From joint `C^n` section regularity `hX` (`4 ≤ n`) and a *compact* window
  `K ⊆ ℝ ×ˢ (extChartAt I p).target`, constructs `χ` (above, on the model `ℝ × E`) and returns both
  `∀ᶠ r in 𝓝ˢ K, χ r = 1` and `Nonempty (Diffeomorph3GaugeFlowOn (cut field) s t₀)` (the model
  comparison flow `Ψ`). Removes the "cutoff assumed" residual of the earlier capstone. (Cast bridge
  `4 ≤ n : ℕ∞` ⟶ `(4 : WithTop ℕ∞) ≤ ↑n` via `WithTop.coe_le_coe` + `simpa`.)
* **`contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn`** — the step-(v) `hΨ` datum. On `M = E`
  every slice `G.maps3 t : E ≃ₘ^3⟮𝓘(ℝ,E),𝓘(ℝ,E)⟯ E` is `ContDiff ℝ 3` (`Diffeomorph.contMDiff` +
  model `contMDiff_iff_contDiff`) — exactly the `hΨ : ContDiff ℝ 3 Ψ` input of
  `contMDiffOn_of_extChartAt_conjugation'`. (Anchoring `G.maps3 t₀ = id` needs no new lemma:
  `SmoothSelfDiffeomorph3Family.AnchoredAt.apply` gives `G.maps3 t₀ q = q` from `G.anchored`.)
* **`hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn`** — the step-(v) `hg'` core. On
  `M = E` the manifold ODE readout `Diffeomorph3GaugeFlowOn.hasMFDerivWithinAt` becomes a genuine
  `HasDerivWithinAt (fun τ ↦ G.maps3 τ q) (Xc t (G.maps3 t q)) s t` via the model-space
  `HasMFDerivWithinAt.hasFDerivWithinAt` + `smulRight_one_eq_toSpanSingleton`. With
  `g := τ ↦ G.maps3 τ (extChartAt I p x)` the comparison curve, this is the integral-curve datum of
  `extChartAt_comp_eqOn_of_lipschitzOnWith` where `χ ≡ 1` (there `Xc = chartPushforwardField`).

**Concrete next target (step (v) glue + residual (b)).** The remaining GAP-1 work is the *glue*
assembling the four bricks above into `hslicesC3` = `∀ t, ContMDiffOn I I 3 (Φ t) U`:
  1. Construct the **compact flow `Φ` on `M`** (Mathlib flow-by-vector-field / the raw compact flow),
     living in the heavy `GaugeReduction/Diffeomorph3FlowExistence.lean` / `ModelGaugeFlowODE.lean`.
  2. **Orbit-containment / `χ ≡ 1` control** — the genuinely delicate step: show the model curve
     `τ ↦ G.maps3 τ (extChartAt I p x)` stays in the `χ ≡ 1` neighbourhood of the orbit window `K` for
     the finite time window, so the cut field reduces to `chartPushforwardField` along it and
     `hasDerivWithinAt_maps3_eval_…` upgrades to the `hg'` of `extChartAt_comp_eqOn_of_lipschitzOnWith`
     (also upgrade `HasDerivWithinAt` on the open `Ioo` window to `HasDerivAt`).
  3. For each `x ∈ U`, `extChartAt_comp_eqOn_of_lipschitzOnWith` (with `g` the model curve) evaluated at
     `t` yields the spatial conjugation `extChartAt I p (Φ t x) = G.maps3 t (extChartAt I p x)`
     (`hconj`); feed that + `contDiff_three_maps3_…` to `contMDiffOn_of_extChartAt_conjugation'`.
  4. Residual (b): supply the joint section-smoothness `hX` from the actual DeTurck gauge field `X`.
Do NOT rebuild trivial-case chart closures; do NOT re-enter the Item-3 BilinearFormBundle geometric-`A`
wall from this frontier.

### Progress (2026-07-06, later 14) — Item 2 GAP 1: the step-(v) glue MACHINERY is now fully assembled (uniform Lipschitz + `hg'` + uniqueness → `hconj` → per-patch slice-`C³`), reducing GAP 1 to the orbit-containment estimate ALONE

**What landed (sorry-free, axiom-clean `{propext, Classical.choice, Quot.sound}`; five additive
theorems, one in `GaugeReduction/GaugeFlowAssembly.lean`, four in
`AnalyticPDE/ModelManifoldGaugeFlow.lean`).**  Together these connect the previously-committed bricks
(`contDiffOn_prod_chartPushforwardField`, `hasDerivWithinAt_maps3_eval_…`,
`contDiff_three_maps3_…`, `extChartAt_comp_eqOn_of_lipschitzOnWith`,
`contMDiffOn_of_extChartAt_conjugation'`) into the entire step-(v) chart-transfer chain, so the ONLY
remaining GAP-1 content is the flow-trajectory-confinement (orbit-containment) estimate.

* **`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField`** (GaugeFlowAssembly) — the
  *time-uniform* `hlip` datum.  A single Lipschitz constant `K` valid for **every** time slice
  `chartPushforwardField I X p t`, `t ∈ Set.Icc a b`: apply `ContDiffOn.exists_lipschitzOnWith` to the
  joint field `contDiffOn_prod_chartPushforwardField` on the compact convex product tube
  `Set.Icc a b ×ˢ s`, then restrict to each fixed time (the shared first coordinate collapses the
  sup-metric `edist (t,q) (t,q')` to `edist q q'` via `Prod.edist_eq` + `edist_self`).  Strengthens the
  per-fixed-time `exists_lipschitzOnWith_chartPushforwardField` to the constant-in-`t` `hlip` shape.
* **`hasDerivAt_maps3_eval_of_cutoff_eqOne`** — the `hg'` datum.  For the model gauge flow `G` of the cut
  field `fun τ q ↦ χ (τ,q) • chartPushforwardField I X p τ q`, on an open window (`s ∈ 𝓝 t`) where
  `χ (t, (G.maps3 t) q) = 1`, the cut-field within-derivative
  `hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn` collapses to the *uncut* field
  (`one_smul`) and upgrades `HasDerivWithinAt → HasDerivAt`.  This is exactly
  `HasDerivAt g (chartPushforwardField I X p t (g t)) t` with `g := fun τ ↦ (G.maps3 τ) q`.
* **`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne`** — step-(v) uniqueness packaging.  Feeds the two data
  above into `extChartAt_comp_eqOn_of_lipschitzOnWith` with the model flow `G` as the comparison curve,
  giving `Set.EqOn (extChartAt I p ∘ γ) (fun τ ↦ (G.maps3 τ) (extChartAt I p x)) (Ioo a b)` — the
  `hconj` precursor — from the raw flow ODE (`hγ`/`hγ_src`), uniform `hlip`, agreement at `t₀` (`heq`),
  and the orbit facts (`hχ`, `hγ_mem`, `hg_mem`).
* **`contMDiffOn_flowSlice_of_cutoff_orbit_control`** — the step-(v) CAPSTONE.  Evaluating that `EqOn`
  at the interior time `t` (`hconj`) and feeding it plus `contDiff_three_maps3_…` (`hΨ`) into
  `contMDiffOn_of_extChartAt_conjugation'` (single chart `p`, `hFU` derived inline from `hγ_src` via
  `extChartAt_source`) yields `ContMDiffOn I I 3 (fun x ↦ Φ t x) U` — the per-patch content of
  `hslicesC3`.  With `contMDiff_of_locally_contMDiffOn` (Mathlib) over a finite chart cover of compact
  `M`, this globalises to `ContMDiff I I 3 (Φ t)` once the orbit facts hold on each patch.
* **`cutoff_eqOne_along_curve_of_graph_subset`** — reduces the `hχ` orbit face to graph-containment:
  `∀ᶠ r in 𝓝ˢ K, χ r = 1` (the cutoff-window property) + `graph ⊆ K` ⟹ `χ ≡ 1` along the curve
  (`Filter.Eventually.self_of_nhdsSet`).

**Fractions of GAP 1.**  The step-(v) glue is now *machinery-complete*: `hlip`, `hg'`, the uniqueness
identification `hconj`, and the per-patch spatial-`C³` transfer are all proved and composed.  The single
remaining GAP-1 obligation is the **orbit-containment estimate** — for `x` in a chart patch and `τ` in
the window: (i) `Φ τ x ∈ (extChartAt I p).source` (`hγ_src`); (ii) the model curve's graph stays in the
cutoff window `K` and both curves stay in the state tube (`hχ` via
`cutoff_eqOne_along_curve_of_graph_subset`, `hγ_mem`/`hg_mem`).  This is the flow-trajectory-confinement
step (choose `K`/window small so the cut-field-flow orbit cannot escape), plus residual (b) supplying the
joint section-smoothness `hX` from the actual DeTurck gauge field, and the finite-cover globalisation.
These modules (`ModelManifoldGaugeFlow`, `GaugeFlowAssembly`) are still raw-material (not yet in the
root import closure); wiring them into the closure happens when the compact gauge-flow existence is
assembled end-to-end.  Do NOT rebuild trivial-case chart closures; do NOT re-enter the Item-3
BilinearFormBundle geometric-`A` wall from this frontier.

### Progress (2026-07-07, later 15) — Item 2 GAP 1: the MODEL-side flow-trajectory-confinement is now MECHANICALLY ASSEMBLED; joint continuity of the model gauge flow is NOT a missing ODE-regularity primitive

**Key finding.**  The joint continuity `(τ, q) ↦ (G.maps3 τ) q` of the model gauge flow — the input the
step-(v) orbit-containment control was assumed to be blocked on — is *already available*.  It is not a
missing Banach→manifold ODE-dependence primitive: the Grönwall joint-continuity theorem
`SmoothDependenceCk.continuous_flow` (uniform-exponential Lipschitz-in-initial-value × integral-curve
continuity-in-time) applies verbatim to any model gauge flow of a uniformly-in-time globally-Lipschitz
field, and the compactly-supported cut field `χ • chartPushforwardField` *is* uniformly Lipschitz
(constant extracted by the already-proved `exists_lipschitzWith_prodMk_left`).

**What landed (sorry-free, axiom-clean `{propext, Classical.choice, Quot.sound}`; four additive theorems
in `AnalyticPDE/ModelManifoldGaugeFlow.lean`).**

* **`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt`** — the *producing* companion of
  `cutoff_eqOne_along_curve_of_graph_subset`.  Abstract tube-lemma confinement: for a flow `Ψ : ℝ → E → E`
  whose space-time graph map is jointly continuous at each anchored point `(t₀, q)` (`q` in a compact `Q`)
  and an open space-time target `W ⊇` the anchored graph, produces an honest window `Ioo a b ∋ t₀` with
  `∀ τ ∈ Ioo a b, ∀ q ∈ Q, (τ, Ψ τ q) ∈ W`.  Proof: `IsCompact.eventually_forall_of_forall_eventually`
  (each pointwise `ContinuousAt.preimage_mem_nhds`) + `mem_nhds_iff_exists_Ioo_subset`.
* **`continuous_maps3_of_lipschitzWith`** — joint continuity of `(τ, q) ↦ (G.maps3 τ) q` for a model gauge
  flow `G : Diffeomorph3GaugeFlowOn (X := X) Set.univ t₀` of a uniformly `K`-Lipschitz `X`, via
  `continuous_flow`: each base curve is a global `IsIntegralCurve` (`hasDerivWithinAt_maps3_eval_…`
  upgraded by `hasDerivWithinAt_univ`), anchored (`SmoothSelfDiffeomorph3Family.AnchoredAt.apply`).
* **`continuous_maps3_of_contDiff_hasCompactSupport`** — the natural-interface form: same joint continuity
  from `ContDiff ℝ N (uncurry v)` + `HasCompactSupport (uncurry v)` (`1 ≤ N`) alone, the uniform Lipschitz
  *derived* internally via `exists_lipschitzWith_prodMk_left`.  This is exactly the data shape
  `contDiff_hasCompactSupport_cutoff_chartPushforwardField` produces for the bump-globalised cut field.
* **`exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith`** — the composition: the full model-flow
  confinement window `∀ τ ∈ Ioo a b, ∀ q ∈ Q, (τ, (G.maps3 τ) q) ∈ W` from a compact `Q` + open
  `W ⊇` anchored graph.

**Fraction of GAP 1.**  The MODEL-curve orbit-containment facts of the step-(v) capstone
(`contMDiffOn_flowSlice_of_cutoff_orbit_control`) — `hχ` (via `cutoff_eqOne_along_curve_of_graph_subset`)
and `hg_mem` — are now mechanically assembled from existing infrastructure: cut-field
`ContDiff`+`HasCompactSupport` ⟶ uniform Lipschitz ⟶ joint continuity ⟶ tube-lemma confinement
`graph ⊆ K₀` (with `K₀` the cutoff window, anchored graph in its interior) ⟶ `χ ≡ 1` along the model
curve.  The remaining GAP-1 obligations are on the **raw manifold flow `Φ`** side (`hγ_src`, `hγ_mem` —
same mechanism but needs `Φ`'s joint continuity on the general compact `M`, i.e. a manifold-target
generalisation of `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` fed by manifold
continuous-dependence à la `ManifoldFlowExistence.exists_nhds_uniform_integralCurve`), plus residual (b)
`hX` and the finite-cover globalisation.  NEXT: the manifold-target confinement + `Φ` joint continuity.

---

## Item 3 (GAP 2) — geometric chart operator `A`: the `lipschitz` field is now DONE (2026-07-07)

The mild/frozen geometric Ricci–DeTurck chart operator
`A τ s = deTurckReactionSectionMap ∇W s + b` (tangent-bundle, fiber-norm-free) now carries the full
**bounded + Lipschitz** analytic package the `TimeDependentGeometricRicciDeTurckBanachChart` demands of
its `A`/`picard` — everything except the `geometric` field:

* **`A`** — the affine tangent-bundle operator (`deTurckReactionSectionMap` + fixed Ricci source `b`),
  already built (`GeometricReactionPicardTangent.lean`).
* **`picard`** — `deTurckReactionSectionMap_add_source_exists_isPicardLindelof` (unconditional
  `IsPicardLindelof`, forward-endpoint auto-chosen), already built.
* **`BanachEvolutionLocalSolutionIn`** — `deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`,
  already built.
* **`lipschitz`** (NEW this session) — the literal chart field
  `∀ t, LipschitzOnWith Kstate (A t) locus` with `Kstate = 2·Kp`:
  - `deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates` (bare reaction),
  - `deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates` (affine, the field),
  - global strengthenings `…_lipschitzWith_…` (bare + affine) = the `hlip` shape for the Banach Picard
    foundation `isPicardLindelof_of_bounded_lipschitz_timeDependent`,
  - `…_add_source_continuous_…` = operator continuity (`LipschitzWith.continuous`).
  Lifted from the per-coordinate bound `deTurckReactionSectionMap_coord_dist_le_inCoordinates`
  (`≤ 2·Kp·dist s s'`) via `lipschitzOnWith_of_forall_coord_dist_le` /
  `lipschitzWith_of_forall_coord_dist_le`; the uniform `Kp` bounds `‖inCoordinates … (P x)‖` over the
  finite compact cover.

**Plumbing pattern discovered (avoid re-losing time).**  For the *affine* `+ b` coordinate bound at
`W := TangentSpace I`, the fixed source `b` cancels via **`coord_add_apply_topFibre` then the fibre
`dist_add_right`** (`simp only [coord_add_apply_topFibre, dist_add_right]`).  The seminormed-fibre
`coord_add_apply` does NOT match the `BilinearFormBundle` hom-fibre topology (the tangent-bundle
`coord_add_apply` matching quirk), and a *section-level* `dist_eq_norm` triggers a `whnf` timeout on the
transported section-space metric diamond (and `dist_add_right` at the section level fails —
`IsIsometricVAdd (CSS)ᵃᵒᵖ CSS` is unsynthesizable).  Global `LipschitzWith` cannot infer `F`/`V`/`et`
with no `stateSet` to pin them — derive it from the `LipschitzOnWith` version at `Set.univ` via
`lipschitzOnWith_univ` instead of re-invoking `lipschitzWith_of_forall_coord_dist_le`.

**The one remaining chart field = `geometric`, and it is the fundamental 2nd-order gap.**  The frozen
operator matches `intrinsicRicciDeTurckRHS` ONLY at the metric-section centre
(`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`);
for a *general continuous* `s ∈ positiveDefiniteLocus` there is no smooth `g` whose Ricci-DeTurck RHS at
`τ` equals `deTurckReactionSectionMap ∇W₀ s + b₀` (the principal `intrinsicRicciFlowRHS` needs two
derivatives of `g`, undefined for merely-continuous `s`).  Closing `geometric` for general `s` is
exactly the parabolic-Schauder smoothing/realization connection (GAP 2 long pole) — it cannot be done
by the frozen affine operator.  **NEXT:** the `RicciDeTurckChartClosureData.realization` decode
(`RicciDeTurckSmoothRealizationData.of_chosenBackground_endpointTimeDerivative_chartRHS`) that turns the
already-built `BanachEvolutionLocalSolutionIn` of the geometric `A` into a genuine
`ChosenIntrinsicDeTurckLocalSolution`, and the `geometric`↔Schauder connection.

### Progress (2026-07-07, later 16) — Item 2 GAP 1: the manifold-target orbit confinement API (the named NEXT) is now PROVED — the raw-manifold `hγ_src`/`hγ_mem` mechanism no longer depends on the model-space-only tube lemma

**Key finding.**  The abstract short-time orbit-graph confinement the raw-manifold side of step (v)
needs is *not* a missing ODE-regularity primitive: the model-space tube lemma
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` uses the model normed space `E` only
through its topology (the elaborator flags `[NormedSpace ℝ E]` as unused there), so it generalises
verbatim to an arbitrary topological-space target `Y` — exactly the setting of the raw manifold gauge
flow `Φ : ℝ → M → M`, where `M` carries no normed-space structure and the `E`-target lemma cannot be
applied directly.

**What landed (sorry-free, axiom-clean `{propext, Classical.choice, Quot.sound}`; three additive
theorems in `AnalyticPDE/ModelManifoldGaugeFlow.lean`, two commits).**

* **`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`** — the
  manifold-target generalisation: for a flow `Ψ : ℝ → Y → Y` (`Y` an arbitrary topological space) whose
  space-time graph map is jointly continuous at each anchored `(t₀, q)` (`q ∈ Q` compact) and an open
  space-time target `W ⊇` the anchored graph, an honest window `Ioo a b ∋ t₀` on which every orbit graph
  stays in `W`.  Proof identical to the `E`-version (`IsCompact.eventually_forall_of_forall_eventually`
  + `ContinuousAt.preimage_mem_nhds` + `mem_nhds_iff_exists_Ioo_subset`).
* **`exists_Ioo_forall_mem_of_continuousAt_source`** — the `Q = {x}` single-orbit source-confinement
  packaged directly for `hγ_src`: joint continuity of `Ψ` at `(t₀, x)` + open `U ∋ Ψ t₀ x` ⟹ a window
  on which `τ ↦ Ψ τ x` stays in `U`.  With `Ψ = Φ`, `x` a chart-patch point, `U = (extChartAt I p).source`
  this is precisely the "orbit stays in the chart source" window the step-(v) chart-conjugation transfer
  (`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne`) requires.  Derived from the general lemma with
  `W = univ ×ˢ U`.
* **`exists_Ioo_forall_forall_graph_mem_compact_of_isCompact_of_continuousAt_manifoldTarget`** — the glue
  from *open-target* confinement to the *compact-window* `graph ⊆ K` datum consumed by
  `cutoff_eqOne_along_curve_of_graph_subset`: apply the open confinement to `interior K`
  (`isOpen_interior`), then `interior_subset`.  This closes the "open target ⟹ compact-window graph
  containment" bridge for the raw-manifold side, uniformly over a compact chart patch.

**Fraction of GAP 1.**  The raw-manifold orbit-containment *mechanism* (`hγ_src`, `hγ_mem`) of the
step-(v) capstone `contMDiffOn_flowSlice_of_cutoff_orbit_control` is now available in reusable abstract
form, symmetric to the model side (`exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith`).  Both
confinement APIs take the flow's joint continuity as a hypothesis.  The one remaining input on the
raw-manifold side is the concrete **joint continuity of `Φ` on the general compact `M`** (manifold
continuous-dependence à la `GaugeReduction/ManifoldFlowExistence.exists_nhds_uniform_integralCurve`),
which lives in the heavy gauge files; plus residual (b) `hX` (the DeTurck gauge field's joint
section-smoothness) and the finite-cover globalisation.  **NEXT:** obtain `Φ`'s joint continuity from the
manifold flow existence and feed it to `exists_Ioo_forall_mem_of_continuousAt_source` /
`…_graph_mem_compact_…_manifoldTarget` to discharge `hγ_src`/`hγ_mem` in the step-(v) capstone, then the
finite-cover globalisation of `contMDiffOn_flowSlice_of_cutoff_orbit_control`.

### Progress (2026-07-07, later 17) — Item 2 GAP 1: the named NEXT is DONE — joint continuity of the raw manifold gauge flow `Φ` at the anchor is now proved for both autonomous AND time-dependent fields, and bundled into the compact gauge flow

**What landed (all in `GaugeReduction/ManifoldFlowExistence.lean`, additive, sorry-free, axiom-clean
`{propext, Classical.choice, Quot.sound}`; four commits).**  The plan later-16 NEXT — obtain `Φ`'s joint
continuity and feed it to `exists_Ioo_forall_mem_of_continuousAt_source` — is now closed on the
continuity side.  The missing datum was that `exists_nhds_uniform_integralCurve` (the manifold flow box)
proves the local flow through the *chart-conjugated Picard flow* `α`, which is `ContinuousOn`, but then
discards that joint continuity.  Four additive theorems reclaim and propagate it:

* **`exists_nhds_uniform_localFlow_continuousOn`** — the jointly-continuous local flow box.  Strengthens
  `exists_nhds_uniform_integralCurve` to expose the explicit local flow map
  `Ψ y t := (extChartAt I x₀).symm (α (extChartAt I x₀ y, t))` together with
  `ContinuousOn (fun p : M × ℝ => Ψ p.1 p.2) (U ×ˢ Ioo (-ε) ε)` (via the chart / model-Picard-`α` /
  chart-symm composition `ContinuousOn.comp` chain), keeping the original integral-curve clause verbatim.
* **`continuousAt_zero_prod_flow_of_isMIntegralCurveOn`** — the *autonomous* joint-continuity-at-anchor
  lemma.  Any anchored flow `Φ` whose orbits solve a `C¹` field's ODE on a uniform window `Ioo (-ε₀) ε₀`
  (for `y` near `x₀`) is `ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x₀)`: the chosen orbit is pinned
  to the flow box's `Ψ` by `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`, transferring
  continuity across the `(t,y) ↦ (y,t)` swap (`ContinuousAt.comp_of_eq` + `ContinuousAt.congr`).
* **`continuousAt_zero_prod_timeDependent_flow_of_hasMFDerivWithinAt`** — the *time-dependent* analogue
  (the form the DeTurck gauge flow actually needs).  The lifted orbit `τ ↦ (τ, Φ τ y)` is an integral
  curve of the autonomous field `(1, X··)` on `ℝ × M` (`autonomousLift_hasMFDerivWithinAt`); matching it
  by autonomous uniqueness to the flow box `Ψ` on `ℝ × M` gives `Φ τ y = (Ψ (0,y) τ).2`, whence
  `ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x₀)`.  All product-manifold instances resolve
  automatically.
* **`exists_timeDependent_flow_compact_continuousAt`** — the payoff: strengthens
  `exists_timeDependent_flow_compact` so the compact time-dependent gauge flow `Φ` additionally satisfies
  `∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)`.  This output has EXACTLY the shape
  `ManifoldFlow.exists_Ioo_forall_mem_of_continuousAt_source` consumes
  (`ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, x)` with `Y = M`, `t₀ = 0`, `Ψ = Φ`).

**Fraction of GAP 1.**  The raw-manifold `Φ`-joint-continuity input to the step-(v) orbit-confinement
(`hγ_src`/`hγ_mem`) is now available end-to-end for the actual compact gauge flow — no longer a "missing
Banach→manifold ODE-regularity primitive", but derived from the manifold flow box's own continuous
Picard `α` + integral-curve uniqueness.  **NEXT:** feed `exists_timeDependent_flow_compact_continuousAt`
into `exists_Ioo_forall_mem_of_continuousAt_source` (open target = a chart source `(extChartAt I p).source`)
to discharge `hγ_src`, and into `…_graph_mem_compact_…_manifoldTarget` for `hγ_mem`, in the step-(v)
capstone `contMDiffOn_flowSlice_of_cutoff_orbit_control`; then residual (b) `hX` (the DeTurck gauge
field's joint section-smoothness) and the finite-cover globalisation.

### Progress (2026-07-07, later 18) — Item 2 GAP 1: the named NEXT is DONE — the raw-manifold `hγ_src`/`hγ_mem`/`heq` faces of step (v) are now MECHANICALLY PRODUCED from the compact flow's joint continuity, on a single common window

**What landed (all in `AnalyticPDE/ModelManifoldGaugeFlow.lean`, namespace
`RicciFlow.AnalyticPDE.SmoothDependenceCk`, additive, sorry-free, axiom-clean
`{propext, Classical.choice, Quot.sound}`; six commits).**  The later-17 NEXT — feed
`exists_timeDependent_flow_compact_continuousAt` into the confinement APIs to discharge `hγ_src`/`hγ_mem` —
is now closed, and bundled onto one window together with `heq`:

* **`exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source`** — the compact-`Q` generalisation
  of the singleton `exists_Ioo_forall_mem_of_continuousAt_source`: every orbit `τ ↦ Ψ τ q` (for `q` in a
  compact `Q`) confined to an open `U` on a **single** window (via the `manifoldTarget` tube lemma with
  `W = univ ×ˢ U`).
* **`exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt`** — the `hγ_src` datum: specialises
  the above to `U = (extChartAt I p).source` and an anchored flow (`Φ 0 = id`), so the anchor condition
  reduces to `Q ⊆ (extChartAt I p).source`.  Gives `∀ τ ∈ Ioo a b, ∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source`.
* **`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod`** — the tube lemma with
  **distinct** domain `Y` / codomain `Z` (the `manifoldTarget` proof never used `Y = Z`).  Needed because
  the `hγ_mem` confined quantity is the **chart image** `extChartAt I p (Φ τ x) : E` of the orbit `Φ τ x : M`.
* **`continuousAt_zero_prod_extChartAt_flow`** — joint continuity of `z ↦ extChartAt I p (Φ z.1 z.2)` at
  `(0, x)` for `x ∈ (extChartAt I p).source` (post-compose `Φ`'s joint continuity with `continuousAt_extChartAt'`).
* **`exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt`** — the `hγ_mem` datum: the `…_prod` tube
  lemma applied to the chart-composed flow, giving `∀ τ ∈ Ioo a b, ∀ x ∈ Q, (τ, extChartAt I p (Φ τ x)) ∈ W`
  for an open space-time target `W` (take `W` = the state graph `{z | z.2 ∈ state z.1}` for the capstone).
* **`exists_Ioo_forall_and`** — anchor-preserving intersection of two `Ioo`-window confinements
  (`max`/`min` endpoints).  The generic glue for merging step (v)'s several confinement windows into one.
* **`exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt`** — `hγ_src` **and** `hγ_mem` on
  a single common window (the two above merged by the combinator).
* **`exists_timeDependent_flow_compact_extChartAt_source_and_mem`** — END-TO-END: from the field jet `hX`,
  `exists_timeDependent_flow_compact_continuousAt` gives the flow `Φ` + orbit ODE on `Ioo (-ε) ε` +
  joint continuity; intersecting with the confinement window yields a **single** window `Ioo a b ∋ 0` on
  which `hγ` (ODE, `mono`-restricted), `hγ_src`, and `hγ_mem` all hold, over a compact patch
  `Q ⊆ (extChartAt I p).source` — the raw-manifold input package of the step-(v) capstone, produced
  unconditionally from the field's jet.
* **`extChartAt_flow_eq_maps3_at_zero`** — the `heq` datum at the common anchor `0`: with both `Φ` and the
  model gauge flow `G` anchored at `0`, `extChartAt I p (Φ 0 x) = (G.maps3 0) (extChartAt I p x)`
  (both sides `= extChartAt I p x`).  Choosing the capstone's reference time `t₀ = 0` discharges `heq` free.
* **`isCompact_extChartAt_image`** — compactness of `extChartAt I p '' Q`, the model-space initial set
  `Q_E` over which the model-curve confinement `exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith`
  (the `hg_mem`/`hχ` faces) is taken — the bridge between the two sides' initial sets.

**Shape check.**  Modulo trivial `∀`-reordering (`∀ τ, ∀ x` ↔ `∀ x, ∀ τ`), `U ⊆ Q`, and `W` = the state
graph, these producers have EXACTLY the `hγ_src`/`hγ_mem`/`heq` shapes of
`contMDiffOn_flowSlice_of_cutoff_orbit_control`.  The raw-manifold orbit-control confinement is now
mechanically assembled; the model-curve `hg_mem`/`hχ`-graph faces reduce (over `isCompact_extChartAt_image`)
to the already-proved `exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith` +
`cutoff_eqOne_along_curve_of_graph_subset`.

**Fraction of GAP 1.**  All the ORBIT-CONFINEMENT content of step (v) is now producible from the compact
flow's joint continuity + the compact chart patch.  **NEXT:** the FINAL step-(v) assembly — merge the raw
bundle (`exists_timeDependent_flow_compact_extChartAt_source_and_mem`) with the model-curve confinements
over `isCompact_extChartAt_image` via `exists_Ioo_forall_and`, choose `t₀ = 0` for `heq`, and feed all of
`hγ`,`hγ_src`,`hγ_mem`,`hg_mem`,`hχ`,`heq` into `contMDiffOn_flowSlice_of_cutoff_orbit_control` — leaving
ONLY the field-analytic faces `hlip` (`chartPushforwardField` Lipschitz on `state τ`) and `hnhds`, plus
the residual (b) `hX` (DeTurck gauge field joint section-smoothness) and the finite-cover globalisation.

### Progress (2026-07-07, later 19) — Item 2 GAP 1: step (v) is ASSEMBLED and GLOBALISED — the per-patch slice-`C³` capstone, its `Φ`-input variant, the finite-cover glue, and the end-to-end field-jets→global-slice-`C³` composition all land

**What landed (all in `AnalyticPDE/ModelManifoldGaugeFlow.lean`, namespace
`RicciFlow.AnalyticPDE.SmoothDependenceCk`, additive, sorry-free, axiom-clean
`{propext, Classical.choice, Quot.sound}`; six commits).**  The later-18 NEXT — the FINAL step-(v)
assembly — is now DONE, together with the finite-cover globalisation that follows it:

* **`exists_Ioo_maps3_cutoff_eqOne_and_state_mem`** — the model-side `hχ` + `hg_mem` face bundle on a
  single window, the model analogue of the raw-side `…_extChartAt_source_and_mem`: from a model gauge
  flow `G` of a uniformly-`K`-Lipschitz field, a compact initial set `Q`, a cutoff `χ ≡ 1` near a
  compact window `Kwin`, and an open state tube, it confines orbits into `interior Kwin` (⇒ `χ ≡ 1` via
  `cutoff_eqOne_along_curve_of_graph_subset`) and into the state (⇒ `hg_mem`), merged by
  `exists_Ioo_forall_and`.
* **`exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem`** — END-TO-END model side: from the
  chart field jet `hXchart` (`C^N`, `N ≥ 4`) + cutoff `χ`, it CONSTRUCTS the model gauge flow `G`
  (`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`), DERIVES the cut field's uniform
  Lipschitz constant from its compact support (`exists_lipschitzWith_prodMk_left`), and feeds the bundle
  above — yielding `G` + `hχ` + `hg_mem` from field data alone.
* **`contMDiffOn_flowSlice_perPatch_of_field_jets`** — the FINAL step-(v) per-patch capstone: wires the
  raw-side flow bundle (`exists_timeDependent_flow_compact_extChartAt_source_and_mem`) + the model-side
  producer above + the anchor-`heq` (`extChartAt_flow_eq_maps3_at_zero`, `t₀ = 0`) into
  `contMDiffOn_flowSlice_of_cutoff_orbit_control` (with `sTime = univ` ⇒ `hnhds = univ_mem`, constant
  `state τ = state₀`), giving `ContMDiffOn I I 3 (Φ t)` on the patch `U` from the two field jets alone.
  KEY: the raw-bundle field `X : ℝ → (x:M) → TangentSpace I x` and the capstone/`chartPushforwardField`
  field `X : ℝ → M → E` UNIFY BY DEFEQ (`TangentSpace I x ≡ E`) — one `X` feeds both sides, no coercion.
* **`contMDiffOn_flowSlice_perPatch_of_flow`** — the `Φ`-input variant (finite-cover globalisation
  ENABLER): takes the GLOBAL compact flow `Φ` (anchored + orbit ODE on `Ioo (-ε) ε` + joint continuity,
  the output of `exists_timeDependent_flow_compact_continuousAt`) as a HYPOTHESIS and produces the
  per-patch slice-`C³` window for THAT same `Φ`, intersecting the raw-confinement / model / ODE windows
  explicitly.  Decouples the ONE global flow from the per-patch model work; no `[CompactSpace M]` needed.
* **`exists_Ioo_forall_contMDiff_of_finite_cover`** — the finite-cover glue: given a finite OPEN cover
  `U : ι → Set M` and, per patch, a window on which `Φ t` is `ContMDiffOn (U i)`, the finite intersection
  of windows is an open nhd of `0` (`isOpen_iInter_of_finite`) containing an honest `Ioo c d ∋ 0`, on
  which `contMDiff_of_locally_contMDiffOn` upgrades the per-patch `ContMDiffOn` to global `ContMDiff`.
* **`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`** — step (v) GLOBALISED: from the
  global DeTurck field jet `hXraw` + the per-patch field-analytic data over a finite cover, it builds ONE
  global flow `Φ` and yields `ContMDiff I I 3 (Φ t)` on a window `Ioo c d ∋ 0` (flow existence +
  `perPatch_of_flow` per patch + finite-cover glue).

**Fraction of GAP 1.**  The step-(v) assembly and its globalisation are now MECHANICALLY COMPLETE:
`{raw flow, model flow, cutoff, orbit control, window intersection, finite-cover glue}` all compose,
green and axiom-clean.  What remains for the general compact `M` is to SUPPLY the per-patch
cutoff-flow package from the ACTUAL Ricci-DeTurck gauge field `X` — the residual `(b) hX` (the two field
jets `hXraw`/`hXchart i` for the real gauge field), the per-patch cutoff `χ i` (a chart-window bump), the
Lipschitz state tube `state₀ i` with its `hlip i` (`chartPushforwardField` Lipschitz), and the initial
placements — plus a concrete finite chart cover.  **NEXT:** discharge the field-analytic residuals
(`hlip i` via `exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField` on a compact tube; the
placements by choosing `state₀`/`Kwin` as nhds of the compact chart-image of `Q_M`), and construct the
finite chart cover of compact `M`, then feed all into
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover` for the general-`M` `hslicesC3` window.

### Progress (2026-07-07, later 20) — Item 2 GAP 1: the FIELD-INDEPENDENT capstone obligations are discharged — the finite chart cover and the window/placement package

**What landed (both in `AnalyticPDE/ModelManifoldGaugeFlow.lean`, namespace
`RicciFlow.AnalyticPDE.SmoothDependenceCk`, additive, sorry-free, axiom-clean
`{propext, Classical.choice, Quot.sound}`; two commits).**  Two of the three residual data families the
step-(v) globalisation capstone `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover` still
consumed — the ones that are purely topological / geometric and carry NO gauge-field content — are now
produced unconditionally from compactness of `M`:

* **`exists_finite_chart_cover_compact`** — the cover-side data package
  `hopen`/`hcover`/`hU`/`hUQ`/`hQ_M`/`hQ_M_src`.  For a compact Hausdorff manifold `M`, produces a finite
  index type `ι`, chart centres `p : ι → M`, open patches `U : ι → Set M` covering `M` inside chart
  sources, and compact patches `Q_M : ι → Set M` with `U i ⊆ Q_M i ⊆ (extChartAt I (p i)).source`.
  Proof: `M` compact + Hausdorff ⇒ locally compact, so `exists_compact_subset` gives a per-point compact
  chart neighbourhood; the interiors cover `M`, and `isCompact_univ.elim_finite_subcover` extracts the
  finite subcover (`extChartAt_source` for the chart-source containment).  KEY: index type is `Type uM`
  (M's universe) via an explicit `universe uM`, so the existentially-quantified `ι` is directly
  consumable by the capstone's `{ι : Type*}`.
* **`exists_compact_window_of_compact_patch`** — the `Kwin`/`hplace_win` data package.  For a compact
  patch `Q ⊆ (extChartAt I p).source` (boundaryless `I`, finite-dim `E`), a compact window `Kwin ⊆ ℝ × E`
  with `Kwin ⊆ univ ×ˢ (extChartAt I p).target` and every anchored chart image
  `((0 : ℝ), extChartAt I p x) ∈ interior Kwin` for `x ∈ Q`.  Proof: the chart image is compact
  (`isCompact_extChartAt_image`) inside the open target (`image_source_eq_target`,
  `isOpen_extChartAt_target`); `E` finite-dim ⇒ locally compact, so `exists_compact_between` gives a
  compact `C` with image `⊆ interior C ⊆ C ⊆ target`, and `Kwin := Icc (-1) 1 ×ˢ C` works
  (`interior_prod_eq`, `interior_Icc`).

**Reduction achieved.**  The window's `Kwin ⊆ univ ×ˢ target` feeds the ALREADY-EXISTING cutoff producer
`exists_contDiff_cutoff_one_nhdsSet_of_isCompact` (`K := Kwin`, `U := univ ×ˢ target`) — which supplies
`χ`/`hχC`/`hχc`/`hsub`/`hcut` — so the cutoff residual is NOT missing infrastructure.  Of the capstone's
inputs, only the genuinely FIELD-SPECIFIC ones remain: the two gauge-field jets `hXraw`/`hXchart i`, the
Lipschitz state tube `state₀ i` with `hlip i` (`chartPushforwardField` Lipschitz on `state₀`), and the
associated `hstate i`/`hplace_state i`.  **NEXT:** discharge the field-specific residuals from the actual
Ricci-DeTurck gauge field — `hlip i` via `exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField` on
a compact CONVEX tube (a chart-ball patch: choose `Q_M`'s chart-image a closed ball, so `state₀ :=` its
interior is a convex Lipschitz tube ⊆ target), then wire the finite cover + window + cutoff + field data
into `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`.  (Note the smooth-bump cutoff forces
`N ≤ ∞`, i.e. the field regularity exponent is not analytic `ω` — an honest constraint compatible with
`4 ≤ N`.)

### Item 3 (GAP 2) later-21 — geometric-A `picard` field + `realization` INPUT assembled at the chart centre (three commits; each `{propext, Classical.choice, Quot.sound}`)

Ground-truth state of the frozen geometric operator `A τ s = deTurckReactionSectionMap ∇W s +
intrinsicRicciFlowRHSSectionSpace g t` on the tangent-bundle `BilinearFormBundle` section space
(`AnalyticPDE/GeometricReactionPicardTangent.lean`): its `A`/`lipschitz`/`hlip`/`hcenter` coordinate
bounds, the unconditional `IsPicardLindelof`, the `BanachEvolutionLocalSolutionIn`, and the centre-point
`geometric` identity (`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`,
in `DeTurckReactionAssembly.lean`) were ALL already present.  This session connected the two previously
independent halves needed to feed the chart-closure `realization` field:

* **`deTurckFrozenGeometric_exists_isPicardLindelof`** — the literal `picard`-field datum for the
  concrete geometric operator: `IsPicardLindelof A ⟨t₀,…⟩ σ₀ a 0 (Mc+2Kp·a) (2Kp)` on an auto-chosen
  forward window, with the geometric coefficient `P := ∇W` and source `b := intrinsicRicciFlowRHSSectionSpace g t`
  (thin specialisation of `deTurckReactionSectionMap_add_source_exists_isPicardLindelof`).
* **`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus`** — the
  geometric Banach evolution solution CONSTRAINED to `positiveDefiniteLocus`, obtained by discharging the
  closed-ball bridge's `hsub` via the a-priori positivity containment
  `ContinuousRiemannianMetric.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus` (openness of
  the positive-definite locus).  σ₀ := `g₀.toSection`.
* **`…_positiveDefiniteLocus_ivp`** — the IVP-vocabulary form: σ₀ := `InitialValueProblem.toContinuousSectionSpace … ivp`
  (definitionally the initial-metric section), `t₀ := ivp.initialTime`.  This is EXACTLY the `sol` shape the
  `RicciDeTurckChartClosureData.realization` field consumes, `BanachEvolutionLocalSolutionIn chart.A
  (positiveDefiniteLocus …) ivp.initialTime (toContinuousSectionSpace … ivp)`, modulo identifying the
  frozen geometric operator with `chart.A`.

**Reduction achieved.**  For the concrete tangent-bundle geometric operator, the chart fields
`A`/`hT`/`picard`/`lipschitz` and the realization `sol` INPUT are now all constructed; the centre-point
`geometric` holds.  **NEXT (still the long pole):** the chart `geometric` field for ALL `s ∈
positiveDefiniteLocus` (the frozen operator satisfies it only at the metric section — a general `s`
requires realising the symmetric value `reaction s + b` as a DeTurck correction of some background, an
honest first-order background solve), and the `realization` DECODE producing a smooth `metric` family
from the Banach curve (`chartRHS_eq_intrinsic` along the whole interval needs the state-dependent /
mild operator, not the frozen linearisation).

### Item 2 (GAP 1) later-22 — step-(v) `hlip` residual reduced to the chart field jet: window-restricted Lipschitz variants + convex open-ball tube atoms (three commits; each `{propext, Classical.choice, Quot.sound}`)

Ground-truth read of the step-(v) globalisation chain found an impedance mismatch: the per-patch capstone
`contMDiffOn_flowSlice_perPatch_of_flow` and the finite-cover capstone
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover` demand the field-Lipschitz control
`hlip : ∀ τ : ℝ, LipschitzOnWith K (chartPushforwardField …) state₀`, yet internally `hlip τ` is used only
for `τ` in the (bounded) slice-`C³` window they build (it is passed as `(fun τ _ => hlip τ)` to the inner
lemma `contMDiffOn_flowSlice_of_cutoff_orbit_control`, whose own `hlip` is already `∀ τ ∈ Set.Ioo a b`).
The bounded-time field-Lipschitz producer
`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField` only delivers Lipschitz on
a compact `Set.Icc a b`, so the `∀ τ : ℝ` shape blocked feeding it in.  This session removed the mismatch
and reduced the `hlip`/`state₀`/`hstate` residual to the chart field jet on a convex ball tube:

* **`contMDiffOn_flowSlice_perPatch_of_flow_windowLip`** and
  **`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip`** (`ModelManifoldGaugeFlow.lean`)
  — additive window-restricted variants requiring `hlip` only on a fixed `Set.Icc cw dw`
  (`0 ∈ Set.Ioo cw dw`); the internally-built slice-`C³` window is intersected with `Set.Ioo cw dw`, so
  every `τ` fed to `hlip` lies in `Set.Icc cw dw`.  Proof mirrors the originals with the extra window
  intersection and one `Set.Ioo_subset_Icc_self` composition.
* **`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball`**
  (`GaugeFlowAssembly.lean`) — from the chart field jet, a uniform-over-`Icc a b` field-Lipschitz bound on
  an OPEN ball `state₀ := Metric.ball c ρ` whose closure lies in the chart target (`closedBall` is compact
  by finite-dim `ProperSpace` and convex; the bound restricts along `Metric.ball_subset_closedBall`).  This
  is exactly the open convex `state₀`/`hstate`/`hlip` tube the `windowLip` capstone consumes.
* **`exists_pos_closedBall_subset_extChartAt_target`** (`ModelManifoldGaugeFlow.lean`) — for boundaryless
  `I`, a positive-radius closed ball around `extChartAt I p p` sits in the open chart target, supplying the
  `closedBall ⊆ target` hypothesis of the ball-Lipschitz lemma at any chart centre.

**Reduction achieved.**  With `…_windowLip` + the two ball atoms, the step-(v) capstone's
`hlip`/`state₀`/`hstate` residuals reduce to: place each patch's chart image in a ball whose closure lies
in the target (a chart-source shrink), and supply the two gauge-field jets `hXraw`/`hXchart i`.  That
chart-source shrink is now also DONE:

* **`exists_finite_chart_ball_cover_compact`** (`ModelManifoldGaugeFlow.lean`) — the finite BALL cover of
  compact `M`: strengthens `exists_finite_chart_cover_compact` so each compact patch `Q_M i` has
  `extChartAt I (p i) '' Q_M i ⊆ Metric.ball (extChartAt I (p i) (p i)) (ρ i)` with
  `Metric.closedBall … (ρ i) ⊆ (extChartAt I (p i)).target`.  The patch is the chart symm-image of a
  half-radius closed ball (compact via `IsCompact.image_of_continuousOn`, `⊆ source` via `map_target`,
  image the half-ball via `right_inv`); the open cover set is `source ∩ chart⁻¹'(ball)`
  (`ContinuousOn.isOpen_inter_preimage`).

**Net reduction.**  The step-(v) globalisation capstone's cover-side data (`hopen`/`hcover`/`hU`/`hUQ`/
`hQ_M`/`hQ_M_src`) AND the convex-tube data (`state₀ := Metric.ball … (ρ i)` with `hstate`/`hlip`/
`hplace_state`) are now ALL producible from compact `M` + the per-patch chart field jet `hXchart i`
(feed `exists_finite_chart_ball_cover_compact`'s `ρ i`/`closedBall ⊆ target` into
`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball`).  The window/cutoff data
(`Kwin`/`hplace_win`/`χ`) come from `exists_compact_window_of_compact_patch` + the existing bump cutoff.
**NEXT:** the genuinely field-analytic core — the two gauge-field jets `hXraw` (global `C¹` product-tangent
jet) and `hXchart i` (`C^N`, `N ≥ 4`, per patch) of the REAL Ricci-DeTurck gauge field — then wire the
whole package into `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip` for the
general-`M` `hslicesC3` window.  (GAP 2's chart `geometric`-for-all-`s` field remains the point-4 long
pole: `ofLipschitzBoundedContinuous` still takes `hgeom` as a hypothesis, and the frozen operator supplies
it only at the metric section.)

### Item 2 (GAP 1) later-23 — the field-independent GAP-1 assembly is CLOSED: compact-`M` `C³` flow-slice regularity now follows from a SINGLE global field-smoothness hypothesis (two commits; each `{propext, Classical.choice, Quot.sound}`)

The later-22 NEXT — "wire the whole package into `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip`" — is DONE.  Two additive lemmas close the entire field-*independent* portion of GAP 1, reducing the general-compact-`M` step-(v) `hslicesC3` obligation to ONE hypothesis: the joint space-time smoothness of the gauge field.

* **`PoincareCurvature.ManifoldFlow.contMDiff_spaceTimeField_of_contMDiff_tangentSection`**
  (`GaugeReduction/ManifoldFlowExistence.lean`) — the **space-time tangent-jet bridge**.  Every compact
  time-dependent gauge-flow existence lemma (`exists_timeDependent_flow_compact_*`,
  `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`) consumes `hXraw` as a `C^n` section of
  the *product* tangent bundle `TangentBundle ((𝓘(ℝ,ℝ)).prod I) (ℝ × M)` — the exotic autonomisation field
  `(1, X)`.  This lemma produces that datum from the NATURAL smoothness
  `ContMDiff ((𝓘(ℝ,ℝ)).prod I) I.tangent n (fun p ↦ ⟨p.2, X p.1 p.2⟩)` of the underlying field
  `X : ℝ → (x:M) → TangentSpace I x`.  Proof: pair the constant `∂_t` unit section on `ℝ` (pulled back
  along `Prod.fst`) with the `X` section via `ContMDiff.prodMk`, then transport through the smooth inverse
  of Mathlib's tangent-bundle-of-a-product equivalence `equivTangentBundleProd`
  (`contMDiff_equivTangentBundleProd_symm`).  (New import: `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`.)
* **`exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact`**
  (`AnalyticPDE/ModelManifoldGaugeFlow.lean`, namespace `RicciFlow.AnalyticPDE.SmoothDependenceCk`) — the
  **end-to-end GAP-1 assembly**.  From the single hypothesis
  `hXfield : ContMDiff ((𝓘(ℝ,ℝ)).prod I) I.tangent ∞ (fun p ↦ ⟨p.2, X p.1 p.2⟩)` (compact boundaryless
  finite-dim `M`), produces a global flow `Φ` on `Ioo c d ∋ 0`, anchored `Φ 0 = id`, with every slice
  `Φ t` `ContMDiff I I 3`.  Internally discharges ALL field-independent capstone data: the finite chart
  BALL cover (`exists_finite_chart_ball_cover_compact`), the two field jets `hXraw` (the bridge above) and
  `hXchart` (`ContMDiff.contMDiffOn`, using `I.tangent = I.prod 𝓘(ℝ,E)`), the per-patch field-Lipschitz
  tube on the chart ball (`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball`), the compact
  space-time cutoff window (`exists_compact_window_of_compact_patch`) and its smooth bump
  (`exists_contDiff_cutoff_one_nhdsSet_of_isCompact`), fed to the `…_windowLip` capstone with
  `cw,dw := -1,1`, `state₀ i :=` the chart ball, `N := ∞`.

**Net reduction.**  GAP 1's field-independent scaffolding — cover, both jets, tube, window, cutoff,
globalisation — now composes into ONE lemma taking ONLY the global joint smoothness of the field.  Note
this lemma is GENERIC in `X`: it is the general compact-manifold `C³` flow-slice regularity for *any*
`C^∞` time-dependent vector field.  **NEXT (the remaining GAP-1 geometric core):** the global joint
space-time smoothness `hXfield` of the REAL Ricci–DeTurck gauge field — i.e. a JOINT `(t,x)` version of
`intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffOn_intrinsicDeTurckOneForm`.  Ground-truth: all
existing DeTurck-field smoothness is SPATIAL (fixed `t`); the joint version needs a *time-dependent*
Riemannian-bundle raising framework (the `rieszMap`/`contMDiffOn_rieszMap_section` lemmas fix ONE metric
via `[IsContMDiffRiemannianBundle I 2 E TM]`), which does not yet exist — a genuine missing sub-project.
Also still open: packaging the forward `C³` flow into the `Diffeomorph3GaugeFlowOn` deliverable needs the
inverse-slice `C³` + flow uniqueness (feeds `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`).

### Item 2 (GAP 1 upstream) later-24 — the field-independent linear-algebra core of joint space-time Riemannian raising: base-polymorphic, arbitrary-order matrix det/adjugate/inverse + Cramer-solve smoothness (two commits; each `{propext, Classical.choice, Quot.sound}`)

The later-23 NEXT identified the sole remaining GAP-1 obstruction as the joint `(t,x)` smoothness of the
real Ricci–DeTurck gauge field, which reduces to *time-dependent* Riemannian raising: the spatial raising
`CovariantDerivative.contMDiffOn_rieszMap_section` reduces raising a co-vector to inverting the local-frame
Gram matrix (coefficient formula `localFrame_coeff_rieszMap`: `cᵢ = ∑ⱼ (Gram⁻¹)ᵢⱼ · ω(frameⱼ)`), but its
smoothness support (`contMDiffOn_localFrameGramMatrix_inv`) is proved only for a *fixed base manifold* `M`
and at the *single order* `2`.  Running that argument jointly over the space-time base `ℝ × M` needs those
facts for an *arbitrary base* and *arbitrary order*.  This session isolated exactly that field-independent
core into a new, Mathlib-only module, wired into the root import graph:

* **`PoincareCurvature/Analysis/MatrixSmoothness.lean`** (namespace `PoincareCurvature.MatrixSmoothness`):
  - `contDiff_det`, `contDiff_updateRow`, `contDiff_adjugate` — det and adjugate are polynomial in the
    entries, hence `ContDiff ℝ n` for *every* order `n` (generalising the `private`, order-`2`
    `contDiff_matrix_det`/`_adjugate` buried in `LeviCivita.lean`).
  - `contMDiffOn_matrixDet`/`_matrixAdjugate`/`_matrixDetInv` — the manifold-level compositions over an
    *arbitrary* base `(J : ModelWithCorners ℝ E' H')`, `N` a charted space.
  - **`contMDiffOn_matrixInv`** — for any `ContMDiffOn` family of matrices over any base with nonzero
    determinant, the entrywise inverse is `ContMDiffOn` at the same order (via
    `A⁻¹ = (det A)⁻¹ • adjugate A`, `Matrix.inv_def` + `Ring.inverse_eq_inv`).  The base-polymorphic,
    arbitrary-order generalisation of `contMDiffOn_localFrameGramMatrix_inv`.
  - `contMDiffOn_matrixEntry`/`_vecEntry`, **`contMDiffOn_mulVec`** (matrix–vector product, componentwise
    finite-sum induction; scalar products via `.smul` + `smul_eq_mul` to stay order-polymorphic — the Lie
    `ContMDiffMul` instance is unavailable at a *variable* order), and **`contMDiffOn_matrixInv_mulVec`**
    — on the nonsingular locus the linear solve `x ↦ (A x)⁻¹ *ᵥ (b x)` is `ContMDiffOn`.  This last one is
    *exactly* the shape of the raised-covector coefficient formula, packaging `contMDiffOn_matrixInv` for
    the raising assembly.

**Net.**  With `contMDiffOn_matrixInv_mulVec` instantiated at `N := ℝ × M`, `J := 𝓘(ℝ,ℝ).prod I`, the
raised-covector coefficients `cᵢ(t,x)` are jointly `(t,x)`-smooth as soon as the two *inputs* are: the
joint-`(t,x)` Gram matrix `A(t,x) = Gram_{g_t}(x)` and the joint-`(t,x)` pairing `b(t,x)ⱼ = ω_t(x)(frameⱼ)`.
**NEXT:** supply those two inputs.  `b` is the joint-`(t,x)` traced DeTurck one-form (already spatial;
needs the time slot).  `A` is the joint-`(t,x)` local-frame Gram matrix of a *time-dependent* metric — i.e.
the joint version of `contMDiffOn_localFrameGramMatrix`, whose only genuinely-new input is joint-`(t,x)`
smoothness of the inner product `⟪frameᵢ, frameⱼ⟫_{g_t}` (a `MetricFamily`/`TimeDependentRiemannianMetric`
joint-smoothness hypothesis, not yet exposed).  Then assemble the raised section over `ℝ × M` (via
`contMDiffOn_iff_localFrame_coeff`) to obtain the joint field jet `hXfield`, and feed it to the CLOSED
field-independent assembly `exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact`.

### Item 2 (GAP 1 upstream) later-25 — completing the base-polymorphic matrix-calculus core: matrix product / transpose / dot product / bilinear-form smoothness (two commits; each `{propext, Classical.choice, Quot.sound}`)

The later-24 core supplied det/adjugate/inverse/`mulVec`/`matrixInv_mulVec`.  This session rounded out the
field-independent, base-polymorphic (`J : ModelWithCorners ℝ E' H'`), arbitrary-order matrix calculus in
`PoincareCurvature/Analysis/MatrixSmoothness.lean` so that *any* local Riemannian tensor formula can be run
jointly over the space-time base `ℝ × M`:

* **`contMDiffOn_transpose`** — the transpose of a `ContMDiffOn` matrix family is `ContMDiffOn` (entrywise).
* **`contMDiffOn_matrix_mul`** — the product `x ↦ (A x) * (B x)` of two `ContMDiffOn` matrix families is
  `ContMDiffOn` (double `contMDiffOn_pi_space` + finite-sum induction, mirroring `contMDiffOn_mulVec`).
  This is what the Christoffel/curvature contractions `g⁻¹ · (∂g) · g⁻¹` of the joint DeTurck field need.
* **`contMDiffOn_dotProduct`** — the scalar `x ↦ (a x) ⬝ᵥ (b x)` of two `ContMDiffOn` vector families.
* **`contMDiffOn_bilinForm`** — the coordinate bilinear form `x ↦ (u x) ⬝ᵥ ((A x) *ᵥ (v x))` = `Uᵀ G V`,
  i.e. the local expression for evaluating a matrix-valued tensor (e.g. the metric readout `G(t,x)`) on two
  vector fields; the tensor-evaluation atom for the joint Gram matrix and one-form pairing.

**Net.**  Products, inverses, contractions, and quadratic/bilinear tensor evaluations are now all available
`ContMDiffOn` over an arbitrary base at arbitrary order, purely in the `ι → ι → ℝ` normed-space readout
world (no `BilinearFormBundle` fibre-instance diamonds).  **NEXT is unchanged** and remains the genuine
GAP-1 obstruction: expose joint-`(t,x)` smoothness of the metric family (a `MetricFamily`/
`TimeDependentRiemannianMetric` joint-smoothness datum), feed the joint Gram readout `G(t,x)` and one-form
pairing `b(t,x)ⱼ` into `contMDiffOn_matrixInv_mulVec` + `contMDiffOn_bilinForm`, and assemble the raised
section over `ℝ × M` to obtain `hXfield` for the CLOSED field-independent flow assembly.

### Item 2 (GAP 1 upstream) later-26 — the ENTIRE field-independent joint space-time raising chain, assembled to the per-patch raised section (eight commits; each `{propext, Classical.choice, Quot.sound}`)

The later-25 NEXT — "feed the joint Gram readout and one-form pairing into `contMDiffOn_matrixInv_mulVec`
and assemble the raised section over `ℝ × M`" — is now DONE end-to-end, in two new Mathlib-only modules
wired into the root import graph.  The genuinely-new geometric input (joint `(t,x)` smoothness of the
time-dependent metric on frames) is supplied by a *parametrized* version of Mathlib's `inner_bundle`.

* **`PoincareCurvature/Analysis/ParametrizedInner.lean`** (namespace `PoincareCurvature.ParametrizedInner`):
  - `contMDiffWithinAt/At/On/·_metricSection_apply₂` and `·_paramBilin_apply₂` — the parametrized
    `inner_bundle`: for a fibrewise bilinear-form section `ψ m : E (b m) →L[ℝ] E (b m) →L[ℝ] ℝ` depending
    on the FULL parameter `m` (not just `b m`), applied to two jointly-smooth sections, the scalar
    `m ↦ ψ m (v m) (w m)` is `C^n`.  Proof = `clm_bundle_apply₂` into the trivial `ℝ`-bundle, then read
    off the fibre.  With `M := ℝ × M`, `b := Prod.snd`, `ψ (t,x) := (g t).inner x` this is the joint
    `(t,x)` smoothness of a TIME-DEPENDENT metric evaluated on fixed frames — the input Mathlib's
    single-metric `[IsContMDiffRiemannianBundle]` cannot give.
  - `contMDiff…_paramLinear_apply` — the linear analogue (dual-bundle section `φ m : E (b m) →L[ℝ] ℝ`),
    via `clm_bundle_apply`, for the one-form pairing.
* **`PoincareCurvature/Analysis/TimeDependentGram.lean`** (same namespace):
  - `contMDiffOn_frameSection_prodSnd` — the time-independent local frame section over the space-time
    base (`contMDiffOn_localFrame_baseSet ∘ Prod.snd`).
  - `contMDiffOn_timeDependentGramReadout` — the joint Gram readout `G(t,x)ᵢⱼ = (g t).inner x (frameᵢ)
    (frameⱼ)`, `ContMDiffOn` valued in `ι → ι → ℝ`.
  - `contMDiffOn_timeDependentOneFormPairing` — the joint one-form pairing `b(t,x)ⱼ = ω t x (frameⱼ)`,
    `ContMDiffOn` valued in `ι → ℝ`.
  - `timeDependentGram_pos` / `timeDependentGram_det_ne_zero` — nonsingularity of the Gram matrix from
    metric positive-definiteness (`g.pos`), via a controlled CLM bilinear expansion (first arg, then
    second, keeping Gram indices aligned with coefficient indices); discharges the `hdet` hypothesis of
    `contMDiffOn_matrixInv_mulVec` UNCONDITIONALLY.
  - `contMDiffOn_timeDependentRaisedCoeff` — the raised-covector coefficients `cᵢ(t,x) =
    (G(t,x)⁻¹ *ᵥ b(t,x))ᵢ` (feeding the above three into `MatrixSmoothness.contMDiffOn_matrixInv_mulVec`).
  - `contMDiffOn_raisedSection_of_coeff` — the raised SECTION `(t,x) ↦ ∑ᵢ cᵢ(t,x) • frameᵢ(x)` (a section
    along `Prod.snd`) is `ContMDiffOn`, by composing the smooth inverse trivialization `e.symm`
    (`contMDiffOn_symm`) with the smooth coordinate map `(t,x) ↦ (x, ∑ᵢ cᵢ • basᵢ)` and identifying via
    `mk_symm` + `symmL` linearity + `frameᵢ(x) = e.symm x (basᵢ)`.
  - **`contMDiffOn_timeDependentRaisedSection`** — the capstone composition: given a time-dependent metric
    `g` and one-form `ω`, both jointly `(t,x)`-smooth as fibrewise sections over `ℝ ×ˢ u`, the raised
    section `(t,x) ↦ ∑ᵢ (G⁻¹ *ᵥ b)ᵢ • frameᵢ(x)` is `ContMDiffOn` over `univ ×ˢ u` — the per-chart-patch
    `hXfield`, i.e. exactly the tangent-section input to
    `contMDiff_spaceTimeField_of_contMDiff_tangentSection`.

**Net.**  The entire field-independent joint space-time raising is now assembled from the coefficient
level up to the raised section, UNCONDITIONALLY (Gram nonsingularity proved from positive-definiteness).
**NEXT:** supply the two remaining GEOMETRIC inputs for the REAL Ricci–DeTurck gauge field — (i) the joint
`(t,x)` metric section smoothness `hg` (a `MetricFamily` joint-smoothness datum: `(t,x) ↦ (g t).inner x`
as a `ContMDiffOn` bilinear-form section) and (ii) the joint `(t,x)` one-form section smoothness `hω` for
the traced DeTurck one-form — then instantiate `contMDiffOn_timeDependentRaisedSection` at `V := TM`,
`IB := I`, feed the per-patch jet through `contMDiff_spaceTimeField_of_contMDiff_tangentSection`, and
globalise over the finite chart cover (already assembled) to obtain the general-compact-`M` `hXfield`.

### Item 2 (GAP 1) later-27 — geometric raising inputs discharged for static data, coordinate-freeness of the raised field, and the local→global smoothness glue (five commits; each `{propext, Classical.choice, Quot.sound}`)

Two fronts advanced toward producing the general-compact-`M` `hXfield`: (a) the two geometric inputs
`hg`/`hω` of the raising capstone were discharged in the time-INDEPENDENT case, and (b) the raised
field was shown to be the honest, trivialization-independent metric dual of the one-form, plus the pure
local→global smoothness glue was built.

* In `PoincareCurvature/Analysis/TimeDependentGram.lean`:
  - `contMDiff_constMetricSection_prodSnd` / `contMDiff_constOneFormSection_prodSnd` — the constant
    (time-independent) family instances of the capstone hypotheses `hg` / `hω`: a static metric section
    (`g₀.contMDiff ∘ Prod.snd`) resp. a spatially-smooth static covector section are jointly `(t,x)`
    smooth over `ℝ × B`.
  - `contMDiffOn_timeIndependentRaisedSection` — discharges BOTH capstone inputs from the two lemmas
    above, giving the per-patch raised gauge-field jet for a static gauge (positive-dimensional,
    general `B`).
  - `raisedVector_inner_localFrame_eq` — Cramer/Gram identity: the raised vector
    `v = ∑ᵢ (G⁻¹ *ᵥ b)ᵢ • frameᵢ(x)` satisfies `g.inner x v (frameₖ x) = ω x (frameₖ x)` for every
    frame index, using Gram symmetry `Gᵢⱼ = Gⱼᵢ` and `G · G⁻¹ = 1` (`timeDependentGram_det_ne_zero`).
  - `raisedVector_inner_eq` — extends the raising equation from frame vectors to ALL `w : V x` via the
    local-frame basis expansion; hence `g.inner x v = ω x`, i.e. `v` is the metric dual of `ω`.
  - `eq_of_forall_inner_eq` — left nondegeneracy of a `ContMDiffRiemannianMetric` (from
    positive-definiteness).
  - `raisedVector_trivialization_independent` — the raised vector is INDEPENDENT of the chosen
    trivialization/basis (even over different index types): both realizations are the unique metric
    dual, identified by nondegeneracy.  This is the compatibility that lets the per-chart raised
    sections glue into ONE global gauge field.
* In `PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ModelManifoldGaugeFlow.lean`:
  - `contMDiff_of_locally_contMDiffOn_univ_prod` — pure-locality glue: a map on `ℝ × M` is `ContMDiff`
    as soon as, around every `x : M`, it is `ContMDiffOn` on `univ ×ˢ (open nbhd)`.
  - `exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact` — compact-`M`
    gauge flow (anchored, `ContMDiff I I 3` slices on a window around `0`) from the gauge-field jet in
    the *local* per-chart form the raising capstone produces, gluing to the global `hXfield` via the
    lemma above and feeding `exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact`.

**Net.**  For STATIC gauge data the whole per-patch → flow pipeline is now inhabitable, and the raised
field is proved coordinate-free.  **NEXT:** assemble the general (time-dependent) `hXfield` by (1)
defining the global raised gauge field coordinate-free (or patchwise, well-defined by
`raisedVector_trivialization_independent`), (2) identifying it with the per-chart local-frame
expression on each patch, (3) feeding the capstone's per-patch `ContMDiffOn` through
`contMDiff_of_locally_contMDiffOn_univ_prod` to the global `hXfield`, and (4) applying
`exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact`; the residual genuine
input is the joint `(t,x)` smoothness of the real (time-dependent) DeTurck metric/one-form.

### Item 2 (GAP 1) later-28 — coordinate-free global raised gauge field + per-patch smoothness assembled; final tangent-bundle flow instantiation blocked by a Mathlib instance wall (two commits; each `{propext, Classical.choice, Quot.sound}`)

The NEXT of later-27 was executed: the global raised gauge field is now defined coordinate-free and its
per-patch joint `(t,x)`-smoothness is packaged in the exact shape the compact-`M` flow assembly consumes.

* In `PoincareCurvature/Analysis/TimeDependentGram.lean`:
  - `raisedGaugeField g ω bas y` — the **globally-defined** metric-raised gauge field, defined via the
    canonical trivialization `trivializationAt F V y` and a fixed model basis; a genuine global section
    of `V`.
  - `raisedGaugeField_eq_localFrame` — on *every* trivialization patch it equals the concrete
    local-frame raised expression (via `raisedVector_trivialization_independent`), so the raising
    capstone's per-patch smoothness transfers to it.
  - `raisedGaugeField_inner_eq` — it is the honest metric dual: `g.inner y (raisedGaugeField …) = ω y`.
  - `contMDiffOn_raisedGaugeField_tangentSection` — the raised-field section
    `(t,y) ↦ TotalSpace.mk' F y (raisedGaugeField (g t) (ω t) bas y)` is `ContMDiffOn` on
    `ℝ ×ˢ (trivializationAt F V x).baseSet`, from `hg`/`hω` (capstone ∘ patch identity).
  - `exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection` — packages the above as the exact
    `∃ s, IsOpen s ∧ x ∈ s ∧ ContMDiffOn … (univ ×ˢ s)` local-jet hypothesis consumed by
    `exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact`.  All trivialization
    handling lives inside this abstract vector-bundle statement.

**BLOCKER (for the general-`M` flow capstone `exists_gaugeFlow_Ioo_of_timeDependent_raisingData`).**  The
final step — instantiate `exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection` at `V := TangentSpace I`
inside a theorem carrying the full compact-manifold instance set (`[IsManifold I ∞ M]`,
`[ContMDiffVectorBundle 2/∞ …]`, `[BoundarylessManifold]`, `[CompactSpace]`, …) and feed it to the flow
assembly — is blocked by a Mathlib instance-resolution pathology: synthesizing
`VectorBundle ℝ E (TangentSpace I)` / `FiberBundle E (TangentSpace I)` in that heavy context runs a
non-terminating `whnf` (the `ContMDiffVectorBundle` monotonicity instances + the
`TopologicalSpace (TotalSpace E (TangentSpace I))` total-space topology are reached by two defeq-but-not-
syntactic paths — a diamond).  Symptoms: `failed to synthesize FiberBundle E (TangentSpace I)` at the
lemma application, with a `(deterministic) timeout at whnf` PANIC from the error-suggestion mechanism.
The `VectorBundle` search succeeds in a *minimal* context (`[IsManifold I 1 M] [ContMDiffVectorBundle ∞ …]`
only) with `synthInstance.maxHeartbeats 4000000`, but blows up once the extra manifold instances are
present; `@`-pinning `inst_7 := instTopologicalSpaceTangentBundle` and adding explicit
`[FiberBundle …] [VectorBundle …]` binders did not defeat the diamond.  The uncommitted flow-theorem
attempt was reverted; the tree is green at HEAD with the five abstract lemmas above committed.

**NEXT.**  Defeat the tangent-bundle instance wall so the abstract lemma composes through the flow
assembly.  Candidate routes: (a) prove a small once-off `TangentSpace.contMDiffVectorBundle`-anchored
lemma that discharges `FiberBundle`/`VectorBundle E (TangentSpace I)` from a *single canonical path* and
reuse it as a `local instance` to break the diamond; (b) restate the flow assembly to consume the
raised-field jet through an explicitly-instanced interface (pass the bundle instances positionally);
(c) isolate which manifold instance triggers the `whnf` blowup (bisecting the instance set in a scratch)
and route around it.  The analytic/geometric content (Items 1,2 raising) is done — this is purely a
Lean instance-plumbing gate on the final `exists_gaugeFlow_Ioo_of_timeDependent_raisingData` capstone.

### Item 2 (GAP 1) later-29 — the flow capstone is BUILT: the tangent-bundle instance wall is DEFEATED (one commit; `{propext, Classical.choice, Quot.sound}`)

The later-28 BLOCKER is closed.  `exists_gaugeFlow_Ioo_of_timeDependent_raisingData`
(`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/CompactGaugeFlowRaising.lean`, a new
additive module) composes the coordinate-free raised gauge field with the compact-manifold `C³`
flow-by-time-dependent-vector-field, on a **general** compact boundaryless manifold, with NO
restricting instance:

> from `g : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`, `om : ℝ → Ω¹`, and the joint
> `(t,x)`-smoothness `hg`/`hom` of the metric inner and one-form, there is `Φ : ℝ → M → M` and an open
> `Ioo c d ∋ 0` with `Φ 0 = id` and each `Φ t` `C³` — the metric-raised gauge flow.

**The wall and how it was defeated (record so the technique is not re-lost).**  Instantiating the
abstract vector-bundle lemma `exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection` at
`V := TangentSpace I` crosses a genuine, *non-terminating* `whnf` instance diamond.  The precise
diagnosis:
* `open scoped ContDiff` reserves `ω` (analytic-smoothness marker) and supplies `∞`; the abstract
  lemma's `ω` binder name is inadmissible downstream — use `om`.  `ContMDiffVectorBundle ∞ …`
  elaborates only with the full heavy-manifold import context.
* The fibre of `TangentSpace I` carries TWO defeq-but-not-syntactic `AddCommGroup` paths —
  `instAddCommGroupTangentSpace` (canonical) vs the `NormedAddCommGroup`-derived one — so a *fresh*
  `VectorBundle ℝ E (TangentSpace I)` search and `TangentSpace.vectorBundle` disagree; the section-level
  defeq that bridges the abstract lemma's `TotalSpace E (TangentSpace I)` / model `I.prod 𝓘(ℝ,E)` to the
  flow lemma's `TangentBundle I M` / `I.tangent` then loops in `whnf` (times out even at 20 000 000
  heartbeats).
* **Fix.**  (1) `@`-pin **every** bundle instance of the abstract lemma positionally, bridging each with
  a *tactic-mode* `by exact` (`by exact TangentSpace.vectorBundle` unifies the two paths where a bare
  term `:=` reports a spurious type mismatch).  (2) `refine flow_lemma (X := <the same @-pinned
  raisedGaugeField expression>) (fun x => ?_)`, then discharge each `x` by `obtain`-ing the `@`-pinned
  abstract lemma and `exact ⟨s, hs_open, hxs, hcont⟩`: because `X` and the lemma conclusion are now
  **syntactically identical** on the section, the only residual defeq is the definitional
  `I.tangent = I.prod 𝓘(ℝ,E)`, discharged cheaply instead of through the diamond.  `set_option
  (synthInstance.)maxHeartbeats 4000000` covers the by-exact bridges.

**Fraction of GAP 1.**  The field-independent scaffolding (later-23) and the geometric raising chain
(later-27/28) already reduced the compact-`M` step-(v) `C³` slice regularity to the single
joint-smoothness hypothesis; that hypothesis is exactly `hg`/`hom`, and the flow now lands from it
unconditionally.  GAP 1's flow-existence capstone is therefore CONSTRUCTED.  **NEXT:** connect the
gauge one-form `om` and metric `g` of the DeTurck setup to the `hg`/`hom` joint-smoothness inputs (the
geometric raising data of the actual Ricci–DeTurck gauge), then thread the resulting `C³` flow into the
Item 1 time-derivative / DeTurck reduction.  (GAP 2's geometric chart `A`/Schauder realization remains
the point-4 long pole.)

### Item 2 (GAP 1) later-30 — metric-dual (`raisedGaugeField`) algebra toolkit committed; the DeTurck↔raisedGaugeField identity is diamond-blocked at the definition site (three commits; each `{propext, Classical.choice, Quot.sound}`)

The later-29 NEXT was to connect the actual DeTurck gauge (`g`, `intrinsicDeTurckOneForm`) to the flow
capstone's `raisedGaugeField g om`.  The natural bridge is the pointwise identity
`intrinsicDeTurckVectorField g bg t = raisedGaugeField (g t) (intrinsicDeTurckOneForm g bg t) bas`
(both are the metric dual `♯` of the one-form; `intrinsicDeTurckGaugeField = -` of it, cf.
`raisedGaugeField_neg`).  The *algebraic* half of that bridge is now committed, and the identity's
*analytic* half is diagnosed as a genuine instance-diamond obstacle.

* In `PoincareCurvature/Analysis/TimeDependentGram.lean` (all general, abstract-`V`, wall-free):
  - `raisedGaugeField_eq_of_inner_eq` / `raisedGaugeField_eq_of_forall_inner_eq` — **uniqueness of the
    metric dual**: any `v` with `g.inner y v = ω y` equals `raisedGaugeField g ω bas y`
    (`eq_of_forall_inner_eq` ∘ `raisedGaugeField_inner_eq`).  This is exactly the tool that identifies a
    concretely-built dual (e.g. a Riesz `♯ω`) with the coordinate-free `raisedGaugeField` — once the
    two are put in one instance path.
  - `raisedGaugeField_zero` / `_add` / `_smul` / `_neg` / `_sub` — the metric dual is **linear in the
    one-form** (proved through the uniqueness bridge + bilinearity of `g.inner`).  `_neg` gives the
    reverse gauge field `-♯ω = ♯(-ω)`; `_sub` matches the DeTurck one-form's Christoffel-difference
    structure.

* **BLOCKER (the identity itself).**  `intrinsicDeTurckVectorField g bg t x = raisedGaugeField (g t) ω
  bas x` cannot be stated-and-proved as a plain equality without defeating a *compounded* tangent-bundle
  instance diamond that is strictly worse than the later-29 flow-capstone wall:
  - `raisedGaugeField … x` at `V := TangentSpace I` needs `FiberBundle E (TangentSpace I)`; as a fresh
    lemma-application argument this synthesis enters a non-terminating `whnf` (even though
    `example : FiberBundle E TM := inferInstance` succeeds standalone — the failure is metavar/telescope
    order, `inst_8 : ∀x, NAG (V x)` being resolved before `inst_10 : FiberBundle` and fixing an
    incompatible `AddCommGroup` path: `instAddCommGroupTangentSpace` vs `NormedAddCommGroup…toAddCommMonoid`).
  - The later-29 capstone technique (full positional `@`-pin of every bundle instance with `by exact`
    bridges + `synthInstance.maxHeartbeats 4000000`) makes `raisedGaugeField` *elaborate*, but the
    equality then times out at `isDefEq`/`whnf` on the **LHS**: `intrinsicDeTurckVectorField` unfolds to
    `letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩; CovariantDerivative.rieszMap x (ω x)`, so
    reconciling the `rieszMap` `RiemannianBundle` path against `raisedGaugeField`'s pinned
    `FiberBundle/VectorBundle` path loops.  The capstone never touched `rieszMap`, so it did not hit this
    second path; the identity does.
  - Verified fact used by the intended proof (holds by `rfl`): under
    `letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩`, `⟪u, w⟫ = (g t).inner x u w`.  So once
    the two are in one instance path, the identity closes in one line via
    `raisedGaugeField_eq_of_forall_inner_eq` + `rieszMap_apply_inner`.

* **NEXT.**  Defeat the compounded diamond at the *definition site*, not the use site: give a single
  once-off `local instance`/lemma discharging `FiberBundle`/`VectorBundle E (TangentSpace I)` from the
  SAME canonical `AddCommGroup`/`Module` path that `rieszMap`'s `RiemannianBundle` uses (candidate: state
  `intrinsicDeTurckVectorField_eq_raisedGaugeField` with both sides built through one `@`-pinned
  `raisedGaugeField`/`rieszMap` expression whose fibre instances are literally shared, so `isDefEq` is
  syntactic).  With that identity in hand, `raisedGaugeField_neg` turns it into the gauge-field form and
  the later-29 flow capstone yields the DeTurck `C³` gauge flow directly.  (GAP 2's geometric chart
  `A`/Schauder realization remains the point-4 long pole.)

### Item 3 (GAP 2) later-31 — the geometric frozen chart operator's symmetry is certified: `A s ∈ symmetricLocus` + defect-zero, without the `geometric` field (two commits; each `{propext, Classical.choice, Quot.sound}`)

Ground-truth state on entry: the geometric-A `picard`/`lipschitz`/Banach-evolution-solution for the
frozen operator `A s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`
(`deTurckFrozenGeometric_exists_isPicardLindelof`, `..._nonempty_banachEvolutionLocalSolutionIn_*`)
are DONE.  The chart's remaining `geometric` field (`∀ s ∈ locus, ∃ g bg, A τ s = intrinsicRicciDeTurckRHS
g bg τ`) is a GENUINE math gap: the frozen (bounded, coefficient-frozen-at-`g₀,t`) operator satisfies
the identification ONLY at `s = (g t).toSection` (`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`),
never for all `s` — the true state-dependent operator that would satisfy `geometric` is 2nd-order
unbounded, so `picard` fails on it.  Reconciling the two (bounded ⟺ geometric) IS the parabolic
long pole (`realization`/`encode`), unchanged.

This session added, in `AnalyticPDE/GeometricReactionPicardTangent.lean` (all additive, axiom-clean),
the **symmetry certification** of the frozen geometric chart operator — the direct frozen-operator
analogues of the chart's `A_mem_symmetricLocus` / `A_coordwiseSymmetryDefect_eq_zero`, established
WITHOUT the (unavailable) `geometric` field:
* `deTurckReactionSectionMap_mem_symmetricLocus` — the `∇W` reaction summand lands in `symmetricLocus`
  for EVERY section `s` (symmetric or not): `deTurckReactionSectionMap_apply` gives `s x (P u) v +
  s x (P v) u`, manifestly symmetric in `(u,v)`; `ring`.  Unconditional.
* `deTurckReactionSectionMap_add_mem_symmetricLocus` — `reaction s + b ∈ symmetricLocus` whenever
  `b` is.  Proved via the `symmetricSectionSubmodule` add-closure (`mem_symmetricSectionSubmodule_iff`
  + `add_mem`), which DODGES the `SeminormedAddCommGroup (BilinearFormBundle x)` Π-fibre diamond that
  blocks a direct `ContinuousSectionSpace.add_apply` evaluation at `V := TangentSpace I` (the same
  fibre-seminorm wall this file's coord-readout bridges were built to avoid — recorded so it is not
  re-hit).  Needs `x0`/`het`.
* `deTurckFrozenGeometric_A_mem_symmetricLocus` — the concrete frozen operator lands in
  `symmetricLocus` (the `(-2)•Ric` source is symmetric by `intrinsicRicciFlowRHSSectionSpace_symm`).
* `deTurckFrozenGeometric_A_coordwiseSymmetryDefect_eq_zero` — its
  `coordwiseSymmetryDefectContinuousLinearMap` vanishes (via `..._eq_zero_iff`), the defect-zero datum
  the symmetric-carrier / interval-defect chart machinery consumes.

**Value.**  Certifies the geometric chart operator's Banach evolution VELOCITY is symmetric, so its
solution curve stays a symmetric metric family — a realization-side consistency ingredient available
independently of the chart assembly.  **NEXT (unchanged long pole):** the `geometric` field
reconciliation and the `realization`/`encode` parabolic smoothing (`SmoothIntrinsicDeTurckRealization`
/ `SmoothMetricSectionCurveData` from the frozen Banach solution) remain the point-4 critical path.
A concrete next inch: the frozen operator's Banach solution curve stays in `positiveDefiniteLocus`
(already the solution's constraint) AND `symmetricLocus` (now that its velocity is certified
symmetric) — package the curve's symmetric-positive-definite membership toward the realized metric.

### Item 3 (GAP 2) later-32 — the frozen geometric Ricci–DeTurck Banach solution curve is certified symmetric-positive-definite, in the IVP `realization` shape (two commits; each `{propext, Classical.choice, Quot.sound}`)

The later-31 NEXT inch — "package the curve's symmetric-positive-definite membership toward the
realized metric" — is now discharged.  Key observation defeating the apparent need for the `geometric`
field: the ODE symmetric-carrier invariance
`exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn`
routes the symmetric-positive-definite conclusion PURELY through *velocity symmetry*
(`A τ s ∈ symmetricLocus`) — NOT through the chart's `geometric` identification.  We already have the
velocity symmetry for the frozen operator (`deTurckFrozenGeometric_A_mem_symmetricLocus`, later-31), and
its `picard` (`deTurckFrozenGeometric_exists_isPicardLindelof`) and uniform Lipschitz
(`deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates`).  Feeding these three
to the invariance lemma yields, in `AnalyticPDE/GeometricReactionPicardTangent.lean` (additive,
axiom-clean):
* `deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus` — the
  frozen geometric operator, anchored at the metric section of a genuine continuous Riemannian metric
  `g₀`, admits a positive-definite-locus Banach evolution local solution, forward-unique on the overlap,
  **whose curve stays in `symmetricPositiveDefiniteLocus` at every time of its interval** (the
  coordinatewise antisymmetric defect solves the same linear ODE, starts at `0` since `g₀` is symmetric,
  hence stays `0`).
* `deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus_ivp` —
  the IVP-vocabulary specialisation (`g₀ := ivp.initialMetric.toContinuousRiemannianMetric`,
  `t₀ := ivp.initialTime`), so the produced `sol` is anchored at
  `InitialValueProblem.toContinuousSectionSpace … ivp` — *exactly* the shape the chart-closure
  `RicciDeTurckChartClosureData.realization` / `SmoothMetricSectionCurveData` consume — now additionally
  certified to trace a symmetric-positive-definite metric family (the `mem_spd` ingredient).

**Formulation resolution (as requested by the primary directive).**  `picard : IsPicardLindelof A` is a
Banach-space (bounded / Cauchy–Lipschitz) requirement.  Ground-truth: the frozen (coefficient-frozen-at-
`g₀,t`) geometric operator `A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`
is a BOUNDED 0th-order operator that inhabits `picard` and `lipschitz` DIRECTLY (Mathlib Banach ODE
closes it) — but satisfies the geometric identification `A τ s = intrinsicRicciDeTurckRHS g bg τ` ONLY at
the single metric section `s = (g t).toSection`
(`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`),
never for all `s ∈ positiveDefiniteLocus`.  The operator that satisfies `geometric` for all `s` is the
true state-dependent 2nd-order Ricci–DeTurck RHS, which is C⁰-UNBOUNDED, so `picard` fails on it.  Hence
`picard` and `geometric` are in direct tension and NO single bounded `A` inhabits both; closing the chart
genuinely requires the parabolic mild/Schauder reconciliation (a mild/regularised representative that is
bounded+Lipschitz AND faithfully represents the RHS via the heat-semigroup smoothing gain).  This is the
unchanged point-4 long pole.  The later-32 results are the honest realization-side consistency
ingredients (`sol` in realization shape + symmetric-PD certification of its curve) that the reconciliation
will consume; they are available independently of it.

**NEXT (unchanged long pole).**  The `SmoothMetricSectionCurveData` for the frozen solution needs its
`contMDiff` field (spatial `C²` of every time slice) — which, even for the *bounded* frozen operator, is
a genuine analytic result (C⁰ Banach ODE solution with a smooth-coefficient 0th-order generator stays
spatially `C²`, needing a uniform-`C²` bound on the Picard iterates), and for the *real* operator is the
full parabolic Schauder gain.  Absent that, the chart's `geometric`/`realization` reconciliation remains
the critical path.

### Item 2 (GAP 1) later-33 — the later-30 DeTurck↔`raisedGaugeField` instance diamond is DEFEATED: the intrinsic DeTurck vector field is the coordinate-free metric-raised gauge field (two commits; each `{propext, Classical.choice, Quot.sound}`)

The later-30 `NEXT` — "defeat the compounded tangent-bundle instance diamond so that
`intrinsicDeTurckVectorField g bg t x = raisedGaugeField (g t) (intrinsicDeTurckOneForm g bg t) bas x`
can be stated and proved" — is now discharged.  The diamond that stalled a prior session (the
`rieszMap` `RiemannianBundle` path vs `raisedGaugeField`'s `FiberBundle`/`VectorBundle` path, looping at
`whnf`/`isDefEq` even under a full positional `@`-pin + 4M heartbeats) is broken by a three-part
technique, committed in the new leaf module
`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/DeTurckRaisedGaugeField.lean`
(non-`module`, importing both `RicciFlow.DeTurck` and `Analysis.TimeDependentGram`):

* **`intrinsicDeTurckVectorField_eq_raisedGaugeField`** — the pointwise metric-dual identity.  Proof
  shape that beats the diamond:
  1. Prove the *scalar* pairing `hv : ∀ w, (g t).inner x (intrinsicDeTurckVectorField g bg t x) w =
     intrinsicDeTurckOneForm g bg t x w` FIRST, entirely inside the `RiemannianBundle` world
     (`letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩`; `change inner ℝ (rieszMap …) w = …`;
     `rieszMap_apply_inner`).  No `raisedGaugeField` appears in this subgoal, so the two instance paths
     are never inside one subterm.
  2. Feed `hv` to the uniqueness lemma `raisedGaugeField_eq_of_forall_inner_eq`, which *produces* the
     metric-dual equation rather than reconciling two pre-built sides.  Pin every tangent-bundle instance
     positionally with `@` to the CANONICAL `inferInstance` / `TangentSpace.fiberBundle` /
     `TangentSpace.vectorBundle` (matching the raising capstone's proven-good pins — crucially the
     fibre `NormedAddCommGroup`/`NormedSpace` are left to `inferInstance`, i.e. the same instance
     `rieszMap` uses, NOT `inferInstanceAs (NormedAddCommGroup E)`, which is a syntactically-different
     defeq term that keeps the diamond alive).
  3. `attribute [local irreducible] raisedGaugeField in` around the theorem — THIS is the decisive
     stroke: with `raisedGaugeField` opaque, the final `exact`'s `isDefEq` compares the produced and goal
     `raisedGaugeField` applications *syntactically* (they are the identical `@`-pinned term) instead of
     `whnf`-unfolding the big local-frame/Gram-inverse sum and looping on the fibre instance mismatch.
* **`neg_intrinsicDeTurckVectorField_eq_raisedGaugeField_neg`** — the reverse (DeTurck gauge) field form
  `-intrinsicDeTurckVectorField g bg t x = raisedGaugeField (g t) (-intrinsicDeTurckOneForm g bg t) bas x`
  (`intrinsicDeTurckGaugeField` is definitionally `-intrinsicDeTurckVectorField`).  Proof: `rw` the
  identity, then `@`-pinned `raisedGaugeField_neg` (metric dual is linear ⇒ negates with the one-form).

**Value.**  This is the pointwise bridge the later-29 flow capstone
(`exists_gaugeFlow_Ioo_of_timeDependent_raisingData`, which flows `raisedGaugeField (g t) (om t) bas`)
needs to be read as flowing the *genuine* DeTurck vector field: with `om := intrinsicDeTurckOneForm`, the
capstone's field IS `intrinsicDeTurckVectorField` by this identity.  The general instance-pinning
technique (`have`-first scalar reduction + canonical `inferInstance` fibre pins + `local irreducible`
on the coordinate-free field) is now a reusable tool for any future `rieszMap`↔`raisedGaugeField`
reconciliation.  **NEXT (Item 2 GAP 1 residual).**  Applying the capstone to the DeTurck case still
needs the smoothness-ladder reconciliation: the capstone consumes `C^∞` joint `(t, x)` data
(`g : ℝ → ContMDiffRiemannianMetric I ∞`, `hg`/`hom` at level `∞`), whereas a `MetricFamily` is `C²`; so
the residual is either a `C²`-regularity version of the raising capstone or a `C^∞` upgrade of the
DeTurck one-form's joint smoothness.  (GAP 2's geometric chart `A`/Schauder realization remains the
point-4 long pole.)
