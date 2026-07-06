
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
