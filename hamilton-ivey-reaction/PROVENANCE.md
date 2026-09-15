# Provenance

## Mathematical source

The theorem follows the normalization and the nonlinear calculation in the
proof of Theorem 1.3 of Bing-Long Chen, Guoyi Xu, and Zhuhong Zhang, *Local
pinching estimates in 3-dim Ricci flow*, Mathematical Research Letters 20
(2013), 845--855, arXiv:1206.1814.  In particular, equation (2.13) defines the
defect, equation (2.21) displays its reaction term, and equations
(2.24)--(2.31) establish the coercive lower bound used here.

The Lean development proves the real-analysis and ordered-eigenvalue steps; it
does not copy source code from the paper or from another formalization.

## Formal source

The sole formal dependency is Mathlib at commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, as pinned by `lakefile.toml` and
`lake-manifest.json`.

No files, declarations, proofs, build products, or generated artifacts from an
external Ricci-flow formalization repository are imported, vendored, or
adapted.  This subproject also does not reuse proof files from another
subproject in this repository.

## New material

All declarations under `HamiltonIveyReaction/`, the Mathlib-only Challenge,
the Solution bridge, and the package checks were written for this result.  The
selected theorem combines the exact curvature-ODE derivative, strict reaction
coercivity, and a proved one-dimensional invariant-region argument to preserve
the Hamilton--Ivey defect.
