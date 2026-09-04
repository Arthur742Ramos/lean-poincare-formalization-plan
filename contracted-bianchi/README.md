# Contracted second Bianchi identity

This directory is a separate Lean project and a separate Palomar surface.  It
is intentionally not another version of the registered `curvature/` project:
the project path is `contracted-bianchi/`, the Comparator theorem names are
different, and a future intake must leave the external `existing_id` field
blank.

## Mathematical result

The selected theorem is the contracted second Bianchi identity

\[
  \operatorname{div}(\operatorname{Ric})
    = \tfrac12\,d(\operatorname{Scal}),
\]

and its immediate geometric consequence

\[
  \operatorname{div}\left(\operatorname{Ric}
    - \tfrac12\operatorname{Scal}\,g\right)=0.
\]

In the Lean surface, `curvature` and its covariant derivative are genuine
multilinear tensors represented by nested `LinearMap`s.  `ricci` and
`scalarCurvature` are displayed finite orthonormal-basis trace contractions,
and `einsteinTensor` and `einsteinDivergence` expose the corresponding
Einstein tensor and divergence.  The conclusion is therefore not a theorem
about an unconstrained scalar family.

The proof performs the finite contraction of the cyclic second Bianchi identity.
The hypotheses used by that contraction are explicit fields of
`CurvatureDerivativeData`: the derivative's pair skew-symmetry, pair
interchange symmetry, and cyclic second-Bianchi identity.  This standalone
project records the contraction layer separately and does not silently claim
that every derivative symmetry has already been bridged to a particular metric
connection.

## Source relationship and authorship

The mathematics is classical differential geometry, presented here as a
formalization/adaptation rather than an original theorem.  The primary source
relationship is to Arthur L. Besse's *Einstein Manifolds*, whose treatment of
the Bianchi identities, Ricci contraction, scalar curvature, and the
divergence-free Einstein tensor supplies the mathematical origin.  Mathlib
supplies the finite-dimensional formal infrastructure; it is not being cited
as the mathematical origin of the contracted identity.

The authors are Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de
Queiroz.  The detailed agent contribution and human oversight record is in
`AGENT-CONTRIBUTION.md`.

## Reproducibility

The project pins Lean 4.33.0 and a Mathlib revision in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.  `Challenge.lean` is the standalone
statement surface; `Solution.lean` contains the proof.  `comparator.json`
selects only the two headline conclusions and their auditable definitions.
