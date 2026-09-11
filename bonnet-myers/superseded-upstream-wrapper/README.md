# Bonnet--Myers

This focused package exposes the complete Bonnet--Myers theorem for a smooth
finite-dimensional real Riemannian manifold.

For a complete induced Riemannian metric, connected manifold, model dimension
`n ≥ 2`, and actual Ricci lower bound

```text
Ric(v,v) ≥ (n - 1) K g(v,v),   K > 0,
```

the headline theorem
`BonnetMyers.bonnet_myers` proves both

* `CompactSpace M`, and
* `Metric.ediam Set.univ ≤ ENNReal.ofReal (π / √K)`.

The curvature in `RicciLowerBound` is the upstream library's constructed
Levi--Civita Ricci tensor.  `CompleteMetric` packages completeness of the
metric induced by the supplied Riemannian metric; it does not use an
unrelated ambient metric instance.

The minimizing-geodesic, second-variation, diameter, and compactness proofs
are imported from the pinned `DifferentialGeometry` v0.1.2 source at commit
`1b535dd102b94cc42b107cca27059687888f08b3`.  The local contribution is a
small, clearly named public interface and combined headline.  This package
makes no originality or priority claim for the classical theorem.

## Verification

From this directory:

```sh
lake build BonnetMyers
lake env lean BonnetMyers/Axioms.lean
```

The second command prints the transitive axioms of all three public
declarations.  They should be only Lean/Mathlib's classical foundations:
`propext`, `Classical.choice`, and `Quot.sound`.
