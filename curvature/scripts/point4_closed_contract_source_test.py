#!/usr/bin/env python3
"""Source invariants for the narrow closed-manifold contract milestone.

These checks are not Lean proof verification. The hosted workflow must also
compile the contract, run the kernel signature regressions and run all five
completion gates, including the unchanged full library build.
"""
from __future__ import annotations

import hashlib
import pathlib
import re

from point4_scan import strip_comments

ROOT = pathlib.Path(__file__).resolve().parents[1]
LOCAL = ROOT / "PoincareCurvature/Geometry/Manifold/RicciFlow/LocalExistence.lean"
CONTRACT = ROOT / "PoincareCurvature/Geometry/Manifold/RicciFlow/PointFourContract.lean"


def normalized(text: str) -> str:
    return " ".join("\n".join(strip_comments(text)).split())


def declaration(text: str, name: str) -> str:
    code = "\n".join(strip_comments(text))
    start = re.search(rf"^(?:structure|def|abbrev) {re.escape(name)}\b", code, re.M)
    assert start, name
    tail = code[start.start():]
    end = re.search(r"\n(?:@\[|(?:noncomputable )?(?:lemma|theorem|def|abbrev|structure|instance)\b|end\b|section\b|variable\b)", tail)
    return " ".join((tail[:end.start()] if end else tail).split())


# Exact existing declaration bodies at immutable base
# db5bf257fa4c452b6f120ef49d916da31fe44da4. The interface data and equations,
# including all-C² IVPs, weak candidates, ordinary derivatives and Icc endpoints,
# must not silently change as part of this scope correction.
EXPECTED_INTERFACE_DIGESTS = {
    'MetricFamily': '53b99e8f1b45483380ead9e216a8482399becca8b3aa071c48644b9703f2e272',
    'HasTimeDerivativeAt': '9ce4e199bd2b6a99ac7638207d2365b9b7e8629d46dab66d824a2a9220ed106d',
    'HasTimeDerivativeOn': 'a506dfcef47ed054272d910e0fb60fbefe32e8706136dcdf65a806ad32eca808',
    'InitialValueProblem': '35219dd1cb918cc0d6fba20c9daf121fa2ff25fcadbab6ac24c03871c77685ef',
    'IntrinsicSolution': 'a21177739c18c6da74c8bc58d1cbbd134385c16b24ff83c4aaca0616f8f332c3',
    'IntrinsicLocalSolution': 'd0130ed50c43ad8c178f86a806227dea295a60a04a7e56565a2430aecc22fdb5',
    'IntrinsicLocalExistenceUniqueness': '52a9809d7dac700a7a150fd63c4821b8e5a0f58aefcc1b97b376ab829c4f6c23',
    'IntrinsicLocalExistenceUniquenessFamily': '7f084a7299ea965599f17d2db67d1fc1e7c343767780e7a93b46ff88b0cd37da',
}

source = LOCAL.read_text()
for name, digest in EXPECTED_INTERFACE_DIGESTS.items():
    actual = hashlib.sha256(declaration(source, name).encode()).hexdigest()
    assert actual == digest, f"Existing interface changed: {name}: {actual}"

expected = """
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M],
      IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)"""
actual = declaration(CONTRACT.read_text(), "PointFourClosedManifoldContract")
assert actual == "abbrev PointFourClosedManifoldContract := " + normalized(expected), actual
assert (ROOT / "scripts/point4_target.txt").read_text().strip() == \
    "intrinsicLocalExistenceUniquenessFamily_pointFour"
print("Closed-contract source invariants passed; no existence proof is asserted")
