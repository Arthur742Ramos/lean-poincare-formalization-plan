# Research-interest assessment

Hamilton--Ivey pinching is a dimension-three mechanism behind Ricci-flow
singularity analysis and geometrization.  The selected result formalizes a
nontrivial theorem-level stage of the proof: the logarithmic barrier's exact
reaction derivative, its strict inward-pointing estimate at a hypothetical
negative minimum, derivation of the scalar lower barrier, and preservation of
the defect along every ordered curvature-reaction ODE solution. Its
audience is researchers in geometric analysis, dynamical systems, parabolic
PDE, and formalized differential geometry.

The formal theorem improves the repository in three concrete ways:

- it fixes the twice-sectional-curvature normalization and the `1 + Kt`
  scaling in a mechanically checked statement;
- it proves rather than assumes the logarithmic `exp(2)/4` inequality and the
  ordered-eigenvalue mixed-term bound; and
- it proves and applies a reusable one-dimensional invariant-region barrier
  principle, yielding `w(t) >= 0` from the standard initial least-eigenvalue
  bound.

This is nevertheless not the full geometric Hamilton--Ivey theorem. The exact
selected result is a faithful invariant-region theorem for the curvature ODE,
not a theorem about a Ricci-flow metric on a manifold. That is a coherent,
nontrivial result with a plausible specialist audience and is materially
stronger than a standalone reaction calculation. Independent review must still
decide whether this ODE theorem alone clears Palomar's research-interest bar.
The strongest eventual contribution to the repository's main objective remains
the local geometric estimate, if its scope is explicitly selected and its proof is completed. The current `curvature/` follow-up derives actual curvature evolution from `IsRicciFlowOn` under explicit joint time--space/spatial regularity and proves a conditional geometric pinching endpoint with explicit support-contact regularity. Those hypotheses remain explicit; this is not unconditional regularity theory.

**External-overlap update (2026-09-20).** An upstream Lean formalization at [`qinz1yang/differential-geometry`, commit `4fbccdfc73f986ce59d7bb66e8bb078f8007ffe2`](https://github.com/qinz1yang/differential-geometry/blob/4fbccdfc73f986ce59d7bb66e8bb078f8007ffe2/DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonIvey/MaximumPrinciple.lean) already proves the global compact-flow Hamilton--Ivey estimate. Accordingly, neither this ODE result nor the conditional global geometric endpoint is currently cleared as a distinct Palomar entry for that classical global theorem. Chen--Xu--Zhang's local estimate ([Theorem 1.3](https://arxiv.org/html/1206.1814)) is a possible separate target, not implemented here. This is a research-interest disclosure, not reused code; no new Palomar intake is authorized.
