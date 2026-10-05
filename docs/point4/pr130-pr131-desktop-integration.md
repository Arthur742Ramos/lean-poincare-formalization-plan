# Desktop integration of PR130 and PR131

This source joins the exact reviewed PR130 repair
`6cdbc00828607d80e180a9cffc0cc3376b3b7e42` and merged master
`a0132cd55e2540b2fd26adecea9a07b51f1b8292`. All Lean and probe bytes from
both parents are preserved. The root library, root provenance and Point-4
README use PR130's existing changes; master has the historical PR129 bytes.

The sole authored overlap is the shared C2 source guard. Its complete master
body and existing PR131 adapter remain unchanged. A count-one insertion before
the original entry point installs the exact two-parent inventory and PR130's
existing import/provenance checks. The new union guard verifies both immutable
parent trees, every source blob, logical Git file modes, actual public paths,
physical Lean paths and the exact shared-guard transform. The inherited axiom,
workflow, audit and boundaryless-type predicates are untouched.

The separate PR130 and PR131 standalone inventory reports still describe
their historical single-unit scopes. They are not advertised as passing on
this union. Broader YAML/schema, Linux, full-build and inherited-evidence gates
remain pending under the user's waiver of hosted checks. Targeted adapter tests
and final-tree independent review are required. Synthetic tests certify only
the changed adapter behavior. Point 4 remains OPEN; no canonical target or
universal C2 obstruction claim is added.

The successful exact Lean 4.33/Mathlib PR130 build and ten-surface probe receipts
are retained as historical exact-source evidence. A narrow final-head replay
is recorded separately. This document does not itself certify a compiler run,
independent review, publication or merge.
