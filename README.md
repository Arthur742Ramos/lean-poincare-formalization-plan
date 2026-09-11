# Lean Poincaré formalization program

This repository develops Lean infrastructure toward a formal proof of the
three-dimensional Poincaré conjecture by Perelman's Ricci-flow-with-surgery
route. It contains both a research roadmap and concrete, proof-bearing Lean
projects.

The Poincaré conjecture is **not yet formalized here**. The first three roadmap
milestones are proved; the current dependency frontier is general
compact-manifold Ricci-flow local existence and uniqueness (milestone 4).

## Start here

- [Current status](docs/status.md): authoritative milestone state and evidence
- [Roadmap](docs/roadmap.md): the mathematical route from curvature to the final
  topological and smooth corollaries
- [Dependencies](docs/dependencies.md): which layers unlock later work
- [Point-4 plan](docs/point4/README.md): the present local-existence boundary and
  completion gate
- [Documentation index](docs/README.md): submissions, package documentation,
  and historical development logs
- [`curvature/`](curvature/README.md): the main Lean package and build commands

## Verified headline status

| Milestones | State | Meaning |
| --- | --- | --- |
| 1–3 | Proved | Static curvature, curvature identities and Levi–Civita existence, and time-dependent geometry are implemented in Lean. |
| 4 | Open | Substantial Ricci–DeTurck infrastructure exists, but the unconditional general compact-manifold theorem required by the audit is missing. |
| 5–15 | Future | These depend on the Ricci-flow and geometric-analysis layers before them. |

The status table deliberately distinguishes proved results from conditional
bridges, interfaces, supporting infrastructure, and future targets. See
[`docs/status.md`](docs/status.md) for the exact definitions.

## Completion standard

A roadmap milestone is complete only when its target mathematical statement is
proved in Lean. Existing Mathlib results may be reused, but the following do
not count as completion:

- an interface or theorem boundary without its construction;
- an added axiom or unchecked assumption;
- `sorry`, `admit`, or another placeholder proof term;
- documentation or API scaffolding;
- a theorem proved only under restrictions absent from the milestone statement.

For milestone 4, the executable authority is
[`curvature/scripts/point4_audit.sh`](curvature/scripts/point4_audit.sh). Do not
call that milestone complete unless a full run prints
`VERDICT: POINT 4 CLOSED` and exits successfully.

## Repository map

The main implementation is the nested Lean project under `curvature/`. The
repository also contains focused theorem projects and submission artifacts,
including Contracted Bianchi, Lichnerowicz–Obata, Schur rigidity, and
Bonnet–Myers. Their publication or intake state is tracked separately from the
mathematical roadmap in
[`docs/palomar-submission-plan.md`](docs/palomar-submission-plan.md).

Historical progress logs are retained under [`docs/history/`](docs/history/).
They are evidence of how the implementation developed, not current status
authorities.

## License

See [LICENSE](LICENSE).
