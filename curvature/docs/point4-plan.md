
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
