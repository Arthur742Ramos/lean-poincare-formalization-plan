# Almost-Schur feasibility audit

Implementation follow-up: see `../almost-schur/README.md`. The external
candidate now rebuilds at both its original pin and an explicitly patched
Lean 4.33 pin, with axiom checks for the three audited endpoint theorems.
The new project has proved gradient, Hessian/Laplacian and trace-free tensor
norm foundations. The audit below records the initial search; its original
"not built" observations are historical, not the latest validation status.
The full almost-Schur inequality and equality case remain unproved.

Date: 2026-09-06. Status: source/dependency audit completed; theorem not
implemented, no replacement Comparator prepared, no submission authorized by
this document. The maintainer authorized pursuing this direction, beginning
with feasibility. Existing Schur proofs remain unchanged.

## Exact mathematical target

Source: De Lellis and Topping, [arXiv:1003.3527v2](https://arxiv.org/html/1003.3527v2),
Theorem 0.1 (Theorem 1.1 in the published version,
DOI [10.1007/s00526-011-0413-z](https://doi.org/10.1007/s00526-011-0413-z)).
On a nonempty connected closed smooth Riemannian n-manifold, n >= 3,
with nonnegative Ricci curvature, prove

`∫ (R - average R)^2 ≤ (4*n*(n-1)/(n-2)^2) * ∫ |Ric - (R/n)*g|^2`,

using Riemannian volume, and prove equality iff the metric is Einstein.
This is an existing research result; no original mathematical discovery or
first-formalization claim is made.

The paper's proof uses mean-zero Poisson solvability, contracted Bianchi,
tensor integration by parts, Cauchy–Schwarz and integrated Bochner. Equality
requires an additional rigidity argument, not just cancellation of the
inequality. The optimality argument uses high-frequency sphere deformations
and is separate from proving the estimate with its displayed coefficient.
Counterexamples without the curvature hypothesis are also separate results.

## Semantic traps to exclude

- Connectedness is explicit in our target. Without it, a disjoint union of
  differently scaled round spheres has zero traceless Ricci but nonconstant
  scalar curvature relative to one global mean. This is a mathematical
  counterexample to silently dropping connectedness, not a Lean test result.
- Require a nonempty manifold and prove finite positive total volume before
  dividing by it. A totalized inverse does not discharge positivity.
- Tensor norms must be Hilbert–Schmidt norms, not operator norms. Prove basis
  independence and the trace-free orthogonal decomposition.
- Our existing divergence has the opposite sign to the paper's codifferential
  convention. Establish the sign bridge explicitly.
- Smoothness, boundarylessness and genuine Ricci nonnegativity must refer to
  the actual metric and its Levi–Civita connection. Do not substitute arbitrary
  scalar/tensor fields satisfying convenient identities.
- Use a genuine volume density, or prove the required compatibility for a
  Hausdorff-measure construction. Merely naming a measure Riemannian volume
  does not prove integration by parts.
- The final statement cannot assume Poisson solvability, integrated Bochner,
  or the desired norm estimate in place of proving them for these manifolds.
- A proof with the stated coefficient is not itself a proof of optimality.

## Audited versions and search scope

Existing project: Lean `v4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Read the source headers and relevant declarations, and searched the pinned
Mathlib and `curvature/PoincareCurvature` Lean sources for Poisson equation,
Laplace–Beltrami, Riemannian volume, Bochner formula and almost-Schur.

Also inspected upstream Mathlib's file tree at
`633b366493a76df88a2bff099ed0cbf711a59ec9`. Its relevant filenames provide no
evidence that simply upgrading supplies the missing geometric analysis.
This is a bounded search, not a proof that no differently named result exists.
No toolchain or dependency pin was changed.

## Dependency assessment

| Obligation | Concrete evidence | Assessment |
| --- | --- | --- |
| Geometric contracted Bianchi | `IntrinsicBianchi.lean`, `divergenceRicci_eq_half_differential_scalarCurvature` | Existing proof; adapt to traceless Ricci and source sign convention |
| Scalar and bilinear differentiation | `ScalarDerivative.lean`, `RicciDerivative.lean`, `BilinearDerivativeTensor.lean` | Existing local geometry, not an integration theory |
| Gradient, Hessian, Laplace–Beltrami | Mathlib `Analysis/InnerProductSpace/Laplacian.lean` defines an operator on vector spaces | Need intrinsic constructions and connection/trace identities |
| Volume and positivity | Mathlib Riemannian distance; external Hausdorff-volume work below | Candidate building blocks; smooth density and integration compatibility remain unverified |
| Closed-manifold integration by parts | Mathlib `MeasureTheory/Integral/DivergenceTheorem.lean` treats Euclidean rectangular boxes | Manifold assembly and tensor specialization not located |
| Mean-zero Poisson equation | No matching theorem located in audited sources | Major blocker: existence plus smooth regularity |
| Sobolev compactness | Mathlib Fourier/Bessel-potential Sobolev spaces; external manifold Rellich below | Not interchangeable with an intrinsic Poisson solver |
| Integrated Bochner identity | No matching geometric formula located | Must prove, including curvature and sign conventions |
| Equality rigidity | Mathlib `IntegralCurve/ExistUnique.lean` gives local curves; `UniformTime.lean` globalizes uniform local existence | Need compact-manifold gradient completeness and equality argument, or a proved alternative |
| Optimality | No suitable sphere variation/spectral implementation audited | Separate substantial milestone; not claimed |

## External dependency candidate: inspect, do not silently adopt

[abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov/tree/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23),
commit `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`, Apache-2.0,
copyright/author Adam Benenson. Uses Lean `v4.29.1`, Mathlib
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

Read the actual volume definition, chart-data construction and final global
compactness theorem, not just the README. Volume is dimensional Hausdorff
measure for the induced Riemannian extended metric. The compactness theorem
takes `RiemannianFiniteChartData`; `exists_riemannianFiniteChartData` constructs
such data. The project contains useful finite-atlas and Sobolev infrastructure.

A source scan found no `sorry`, `admit` or `axiom` tokens in its library.
This is **not** a build, kernel/axiom-closure certification, semantic audit of
every helper, or compatibility check with our Lean version. No source was
vendored or added to the Lake manifest. No Poisson solver or geometric
Bochner formula was located there. In particular, Hausdorff-volume finiteness
does not establish the density formula needed for our integration identities.

If adopted later, pin the exact version, preserve notices, add a structured
`related_formalizations` relationship, rebuild independently and audit the
full theorem dependencies. Keep non-Mathlib imports out of the Challenge.

## Ordered implementation gates

1. Audit/build the external candidate in isolation at its original pin; test
   migration separately. Prove volume compatibility, positivity and finiteness.
2. Develop intrinsic gradient/Hessian/Laplacian and manifold integration by parts.
3. Establish mean-zero Poincare/coercivity, weak Poisson existence and smooth
   elliptic regularity. Identify and prove all compactness/completeness bridges.
4. Prove integrated Bochner and derive the actual almost-Schur estimate.
5. Prove equality rigidity. Audit every assumption against the source.
6. Only after those gates, prepare a separate focused Challenge/Solution
   artifact with full attribution and independent kernel verification.

The first hard go/no-go is analytic infrastructure, not an algebraic
inequality lemma. The development is plausible as a substantial new project,
but is not currently an end-to-end implementation task with all prerequisites
available. Do not estimate completion from the short length of the paper.

## Prior-formalization search

Web searches for almost-Schur with Lean/formalization did not identify an
existing end-to-end Lean proof in the returned results. They did identify the
Rellich candidate above. Search coverage is incomplete; this does not establish
novelty or priority. The formalization should remain source-based.
