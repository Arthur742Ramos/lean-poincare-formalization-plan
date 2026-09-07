# Contracted-Bianchi compatibility audit — 2026-09-06

## Verified local result

`LeviCivitaRegularity.lean` constructs a proof of
`leviCivitaConnection.ContMDiffCovariantDerivative 1` from a C² metric, using
Koszul pairings and the actual metric-dual frame. No regularity assumption on
the connection or the seed chart choice is introduced. The result is C¹;
arbitrary finite orders and C² connection regularity are not yet proved here.

`LeviCivitaBochner.lean` specializes the actual raw curvature corrected
commutator, frame-independent gradient contraction, and Bochner flux identity
to that constructed connection. It does not identify raw Ricci with a bundled
Ricci tensor. Uniqueness remains equality on sections differentiable at the
evaluation point, not equality of connection objects on arbitrary junk inputs.

Both modules build. The checked regularity and Bochner declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or new
axioms are present.

## Source and provenance

Audited the sibling `contracted-bianchi/PoincareCurvature` source, not
`schur-rigidity`. Repository HEAD at inspection:
`8a5ce6ac8ef01e65d1e8a0eaeb53888180fc931a`.
The curvature-path history records Arthur Freitas Ramos as author of
`62247eaa896503a8cbe1f6245ac95ad4a062a644` (2026-09-04,
"Prove contracted Bianchi from a manifold connection") and
`12cebb809524d0cd185c6cd7bcb5b73d3562bce1`
("Repair contracted Bianchi Challenge render boundary"). The path was clean
at inspection. These are repository provenance records, not a mathematical
priority claim. No root LICENSE file was found in the sibling package.

Both packages pin Lean 4.33.0 and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
There is no `Curvature/Basic.lean` in the inspected sibling: the relevant
foundation is split into `Raw.lean` and `Tensor.lean`.

## Exact module scope

All paths below are relative to
`PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/`.

| Module | Actual scope |
| --- | --- |
| `Along.lean` | Covariant differentiation along fields using the native mathlib connection. |
| `Curvature/Raw.lean` | Raw commutator `curvatureAux`, with the same order/sign as `AlmostSchur.rawCurvature`. |
| `Curvature/Tensor.lean` | Canonical bump-supported smooth extensions, multilinear fibre curvature, left/middle tensoriality, right-slot locality and coefficient-based representative rules. |
| `Curvature/Bianchi.lean` | First and corrected second Bianchi identities and curvature symmetries under the stated regularity/torsion/metric hypotheses. |
| `Curvature/Contractions.lean` | `ricciEndomorphism x u w v = curvatureTensor x v u w`, its trace as bilinear Ricci, scalar trace, and conditional symmetry/connection-independence results. |
| `Curvature/ContractedBianchi.lean` | Corrected curvature derivative evaluated on canonical extensions and its cyclic second Bianchi identity. Not yet the double contraction itself. |
| `Curvature/ContractedBianchiBridge.lean` | Derived derivative skew/pair symmetries and the double-sum contraction identity. Explicitly does not identify these sums with derivatives of Ricci/scalar fields or Einstein divergence. |

Independent sibling build:
`lake build PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge`
passed (2979 jobs). Axiom checks for `curvatureTensor`, `ricciCurvature`,
`scalarCurvature`, and `curvatureCovariantDerivativeInner_doubleContraction`
returned only the three standard Lean axioms listed above.

## Compatibility limits and extraction decision

1. The native `CovariantDerivative` type and raw commutator sign align.
   Bundled curvature/Ricci require Hausdorff base space and C¹ connection
   regularity; the smooth finite-dimensional tangent-bundle assumptions align
   after supplying the appropriate regularity instances.
2. The raw-to-tensor evaluation rule is **not yet unconditional for arbitrary
   locally smooth right-slot sections**. One rule requires eventual equality
   with the canonical extension. The stronger
   `curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right`
   instead requires globally C² totalized chart coefficients. This global
   hypothesis does not follow merely from local C² regularity of a gradient;
   it needs a localization/extension argument. Its left and middle fields are
   also globally C¹, whereas our coordinate frames are only locally regular.
3. Double contraction assumes both C¹ and C² connection instances. Our newly
   proved C¹ result does not discharge the C² requirement. Nor does importing
   the contraction theorem provide the missing trace/differentiation bridge.
4. Importing `Tensor.lean` transitively imports the sibling's substantial
   `LeviCivita.lean`, `Existence.lean`, `Metric.lean`, `RiemannianSection.lean`,
   and `ContinuousSection.lean` infrastructure. It is not a five-file isolated
   curvature dependency. These imports remain inside PoincareCurvature/mathlib;
   no schur-rigidity import was found in the audited tree.

No sibling source has been copied or imported into AlmostSchur in this step.
A narrow attributed port of the extension/tensoriality and contraction core is
plausible, but should first separate it from the sibling LC existence/uniqueness
infrastructure and prove the local right-slot representative bridge. This avoids
silently importing stronger regularity assumptions or a broader uniqueness API.

## Follow-up implementation: local Ricci milestone (2026-09-06)

The preceding no-port statement describes the initial audit. The subsequent
user-authorized extraction is now in `AlmostSchur/CurvatureVendor/`, with eight
Lean modules and `PROVENANCE.json`. It uses committed source only, pinned to
`12cebb809524d0cd185c6cd7bcb5b73d3562bce1`, with exact source paths and Git blob
identities. The sibling LC existence/uniqueness infrastructure is excluded.
`Tensor` gets an explicit mathlib LocalFrame import, and `Contractions` gets a
local finite-dimensional tangent-fibre instance; both replace transitive imports
that were deliberately removed. All adaptations are hashed and described.

New proofs:

- `LocalCurvatureExtensions.exists_contMDiff_section_germ_with_coefficients`
  (declaration namespace `AlmostSchur`) constructs globally Cⁿ cutoff sections
  and globally Cⁿ totalized chart coefficients from a locally Cⁿ section, for
  every finite natural n.
- `LocalCurvatureTensor.curvatureAux_eq_curvatureTensor_of_contMDiffAt`
  proves the raw-to-bundled evaluation rule for locally C² tangent fields.
  The right-slot global coefficient hypothesis is fully discharged.
- `BundledRicciBochner.rawRicciGradient_eq_ricciCurvature` identifies the actual
  raw contraction with bundled Ricci on the gradient from local C³ scalar
  regularity and C¹ connection regularity. No compatibility or torsion premise
  is required for that identification. The ambient metric is C².
- `BundledRicciBochner.leviCivita_divergence_bochnerFlux_ricci` specializes the
  constructed LC flux identity to genuine bundled Ricci.

The theorem names after the module names above are all in namespace
`AlmostSchur`; the retained vendor declarations are in `CovariantDerivative`.
All four geometry targets (local extensions, local tensor bridge, bundled Ricci
bridge, and vendored contracted-Bianchi bridge) build. The checked new and
vendored endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

Run `python3 scripts/check-curvature-provenance.py` to verify exact coverage of
all eight vendor Lean files, source commit/path/blob identities, recomputed Git
blob identities, source/local SHA-256, and deterministic unified-diff SHA-256.
It is read-only and network-free; `--source-repo PATH` can name another local
clone containing the pinned Git objects. `--print-records` only prints computed
records for an explicit manifest update, never changes files. The checker was
tested for deterministic replay and rejection of six corruptions (four hash
fields, missing coverage, and altered local bytes).

At the requested audit pause, root imports and the shared axiom audit have not
been edited by this work. Higher LC regularity and the Ricci/scalar
trace-differentiation bridge remain pending. Vendoring a double-contraction
theorem does not establish those missing geometric identifications.
