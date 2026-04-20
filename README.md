# Lean Formalization Roadmap for the Poincare Conjecture

This repository is a working plan for a serious Lean formalization effort around
the 3-dimensional Poincare Conjecture, with the proof route understood as
Perelman's Ricci-flow-with-surgery program.

The point of this repo is not to claim that the theorem is already formalized.
It is not. The goal here is to break the project into chunks that are large
enough to be independently meaningful, and in many cases paper-worthy in the
style of the Annals of Formalized Mathematics.

## Contents

- `docs/roadmap.md`: the main roadmap, with AFM-scale project slices
- `docs/dependencies.md`: dependency structure and a suggested execution order
- `curvature/`: Lean/mathlib subproject for milestone 1, the curvature package bootstrap

## Current framing

The roadmap assumes:

- public Lean/mathlib does not yet contain a completed formal proof of the
  Poincare Conjecture
- the real difficulty is not just the final theorem, but the missing geometric
  analysis infrastructure required to even state Perelman's arguments cleanly
- several intermediate deliverables would already be major formalization papers

## Scope

This is intentionally a research-program repository, not an implementation
repository.

The current exception is `curvature/`, which turns milestone 1 into a concrete
Lean package with initial code at the covariant-derivative/curvature boundary.
