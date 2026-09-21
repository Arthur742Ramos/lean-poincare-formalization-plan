# Milestone 4.1 — Gauge-pulled metric time derivative

**Status:** proposed
**Parent:** [Point 4](README.md) (Ricci-flow local existence and uniqueness),
workstream **A. Gauge-pulled metric time derivative**
**Depends on:** none (first milestone of the Point-4 closing sequence)

## Goal

Prove the general nonidentity time-dependent pullback formula

```text
d/dt (Φ_t^* g_t) = Φ_t^* (∂_t g_t + Lie_{X_t} g_t)
```

in the repository's bundled tensor vocabulary, **for the actual DeTurck
gauge family** used by the general Ricci–DeTurck solution — not a model,
identity, or endpoint-only case.

## Why this milestone first

Of the three remaining Point-4 integration workstreams, this is the smallest
closable piece: scalar-to-tensor reductions, bilinear chain rules, endpoint
variants, and several model-coordinate pieces already exist. What is missing
is a single theorem that supplies the required derivative package for the
actual gauge family. Closing it unblocks the gauge-transport step of the
Point-4 architecture (Ricci–DeTurck solution → gauge flow → intrinsic Ricci
flow).

## Acceptance criteria

The milestone is closed when **all** of the following hold:

1. **Theorem.** A proved theorem in `curvature/PoincareCurvature/` stating
   the pullback derivative formula above for the actual time-dependent
   DeTurck gauge family, in the bundled tensor vocabulary used by the
   general Ricci–DeTurck solution.
2. **Sorry-free.** The new code passes the repository's forbidden-term scan
   (`curvature/scripts/point4_scan.py cheats`): no `sorry`, `admit`,
   `sorryAx`, `axiom`, `opaque`, `native_decide`, or `decide!`.
3. **Built.** The new module is imported in the `PoincareCurvature` import
   tree and its `lake build` succeeds (no orphaned files).
4. **Recorded.** `docs/point4/README.md` marks workstream A closed with a
   pointer to the theorem.

## Non-goals

- Workstream B (compact-manifold `C³` gauge flow) and workstream C
  (quasilinear Ricci–DeTurck PDE closure) are separate milestones.
- This milestone alone does not close Point 4; the Point-4 audit
  (`curvature/scripts/point4_audit.sh` printing `VERDICT: POINT 4 CLOSED`)
  remains the sole authority for that.

## Verification

A reviewer checks criteria 1–4 directly: read the theorem statement, run the
scan script, build the module, and confirm the README update. No new
audit infrastructure is required.
