
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
