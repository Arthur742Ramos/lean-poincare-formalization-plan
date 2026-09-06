# Schur rigidity and geometric contracted Bianchi

This is a **new Palomar entry**, separate from `contracted-bianchi/`. It must
never be submitted as a version of the earlier entry. Its Comparator
path is `schur-rigidity/comparator.json`; the submission's existing-ID field
must be blank.

## Selected theorem package

For a smooth finite-dimensional real Riemannian manifold and its sufficiently
regular torsion-free metric-compatible connection:

1. The covariant divergence of the actual Ricci tensor is one half of the
   differential of the actual scalar curvature.
2. The actual Einstein tensor has zero covariant divergence.
3. On a connected manifold of dimension at least three, a differentiable
   function `lambda` satisfying `Ric = lambda * g` is constant.
4. In dimension three, the Einstein condition determines the full curvature
   tensor, hence gives constant sectional curvature once Schur constancy is
   established.

The mathematical results are classical. This project claims a formalization,
not a new mathematical discovery or established priority among Lean proofs.

The four selected declarations in namespace `SchurEntry` are
`geometricContractedBianchi`, `divergenceEinstein`, `schur`, and
`threeDimensionalEinstein_constantCurvature`. The last theorem gives one
constant `K` for the **full curvature tensor** everywhere:
`Rm(u,v,z,t) = K (g(u,t)g(v,z) - g(u,z)g(v,t))`.
In particular, evaluation at orthonormal `(u,v,v,u)` gives sectional curvature
`K`. The proof obtains `K = c/2` for the constant Einstein factor `c`.

## Auditable geometric boundary

[Challenge.lean](Challenge.lean) imports only Mathlib and displays eight
definitions. Curvature is the connection commutator including its Lie-bracket
correction. Ricci and scalar curvature are its orthonormal contractions. The
bilinear derivative is the actual manifold differential minus both connection
corrections; divergence is its orthonormal trace. Metric compatibility is the
displayed inner-product Leibniz identity.

The statement requires a smooth Hausdorff real manifold with finite-dimensional
complete model space. Tangent-bundle regularity through order three,
connection regularity through order two, and metric regularity through order
two are supplied; lower-order instances are explicit for typeclass inference.
The connection is torsion-free and metric-compatible.

The boundary takes globally `C^3` tangent-vector extensions anchored at every
point. Conclusions hold for **every** such family: the proof identifies the
displayed operations with intrinsic curvature and derivatives. Contracted
Bianchi, Einstein divergence, a Ricci differentiation bridge, and a
neighborhood-wide orthonormal frame are **not** hypotheses. No compactness,
geodesic completeness or sigma-compactness is required. Connectedness and the
dimension restrictions occur only in the rigidity results. The Einstein
factor need only be manifold-differentiable.

The Challenge contains exactly four intentional theorem placeholders and no
definition placeholders. [Solution.lean](Solution.lean) proves all four and
repeats the same definitions. Comparator compares all selected statements and
all eight definitions. Only `propext`, `Quot.sound`, and `Classical.choice`
are permitted axioms.

## Proof structure

1. `CurvatureEvaluation` and `SchurLocalFrame`: unrestricted smooth extension
   evaluation and a canonical local frame.
2. `ScalarDerivative`, `BilinearDerivativeTensor`, `RicciDerivative`: inverse
   Gram differentiation, actual metric-trace differentiation, extension
   independence and the Ricci trace/derivative interchange.
3. `IntrinsicBianchi`: actual contracted Bianchi and Einstein divergence.
4. `SchurMetricDerivative`, `SchurContractionAlgebra`, `SchurAssembly`,
   `SchurConstancy`: the Einstein factor has zero differential, hence is
   globally constant on the connected manifold.
5. `SchurThreeDimensional` and `SchurRigidity`: full three-dimensional
   curvature algebra combined with the global constancy theorem.

Internal `_of_trace_bridge` lemmas expose an intermediate assembly step.
The final proofs discharge that bridge using the proved Ricci differentiation
theorem. It is not assumed at the submission boundary.

## Reproduction

Pinned Lean: **4.33.0**. Pinned Mathlib:
`db584cd6d46c92f209a44c0f1c829460d327499d`.
This directory is an independent Lake project, without sibling-project Lean
dependencies.

```sh
cd schur-rigidity
lake exe cache get
lake build
python3 scripts/check-challenge-boundary.py
bash scripts/verify-comparator.sh
```

The last command requires Linux with Landlock, Cargo, Go, Git, Python and Lake.
Comparator, Lean4Export, NanoDa and Landrun revisions are pinned; NanoDa is
enabled. On macOS, `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` explicitly opts into
development replay **without** a real Landlock sandbox. This is not a
substitute for the Linux workflow.

See [VERIFICATION.md](VERIFICATION.md) for completed checks and
[SUBMISSION.md](SUBMISSION.md) for intake instructions. Preparation and
mechanical checks are not submission, editorial acceptance or registration.

## Scope and attribution

The inherited `PoincareCurvature/` library is preserved with its attribution.
Its earlier double-contracted identity is a dependency, not a selected theorem
of this new entry. See [PROVENANCE.md](PROVENANCE.md),
[formalization.yaml](formalization.yaml), and
[AGENT-CONTRIBUTION.md](AGENT-CONTRIBUTION.md).

We do not prove space-form classification, completeness, isometry to a
standard model, Lorentzian geometry, Ricci-flow existence, surgery, or Poincare.
Classical sources include Carroll's [Section 3, equations (3.90)–(3.96)](https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll3.html)
and the Mannheim [curvature chapter, Theorems 5.12 and 5.23](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/FSS2024/Riemannian_Geometry/Web/RGch5.html).
