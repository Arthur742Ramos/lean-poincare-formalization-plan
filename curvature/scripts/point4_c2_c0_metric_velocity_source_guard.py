#!/usr/bin/env python3
"""Exact literal-C2/C0 metric-velocity release union; source checks never certify a Lean build."""
from __future__ import annotations
import argparse
import functools
import hashlib
import importlib
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
sys.dont_write_bytecode = True

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = 'e6b54dd0d7e73a51eb8efb083764b68ae8305a5a'
C2_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SOURCE_GUARD = 'curvature/scripts/point4_c2_c0_metric_velocity_source_guard.py'
MODULE_PREFIX = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/'
MODULE_NAMES = ('C0GaussianEndpoint', 'C0FiniteAtlasGaussian', 'C0EndpointCompactPositivity', 'C2MetricVelocityExtension')
MODULES = tuple(MODULE_PREFIX + name + '.lean' for name in MODULE_NAMES)
PROBE = 'curvature/scripts/point4_c2_c0_metric_velocity_probe.lean'
WORKFLOW = '.github/workflows/point4-c2-c0-metric-velocity.yml'
DOSSIER = 'docs/point4/c2-c0-metric-velocity/'
METADATA = DOSSIER + 'formalization.yaml'
CLOSURE_MANIFEST = DOSSIER + 'MASTER-CLOSURE-MANIFEST.json'
MATHLIB = 'db584cd6d46c92f209a44c0f1c829460d327499d'

RELEASE_GUARD = SOURCE_GUARD
RELEASE_TEST = 'curvature/scripts/point4_c2_c0_metric_velocity_mock_test.py'
SELF_PATHS = {RELEASE_GUARD, RELEASE_TEST}
# Self-authored guard/test bodies are reviewed source. All public paths are fixed;
# every approved mathematical and inherited blob is additionally pinned by its exact identity.
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1')
ENTRY_POINT = "\nif __name__ == '__main__':\n    main()\n"
C2_ORIGINAL_SHA256 = '2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47'
C2_ADAPTER = "\n# Reviewed literal-C2/C0 metric velocity inventory adapter. All inherited gate bodies remain\n# unchanged; the source guard pins this count-one insertion and exact union.\nif (ROOT / 'curvature/scripts/point4_c2_c0_metric_velocity_source_guard.py').is_file():\n    import sys as _metric_velocity_sys\n    _metric_velocity_sys.dont_write_bytecode = True\n    import point4_c2_c0_metric_velocity_source_guard as _metric_velocity_release\n    _metric_velocity_release.install_c2_inventory_adapter(globals())\n\n"
UNIT_FILE_SHA256 = {'.github/workflows/point4-c2-c0-metric-velocity.yml': '3bca55c2b29333871b09213ce586e3315c8678993692e33eff85346062dfe10c', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0EndpointCompactPositivity.lean': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0FiniteAtlasGaussian.lean': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean': '122a2a7631e85adcf031894226a0237e8791770ebb4f784b8af4b57a38e010ea', 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C2MetricVelocityExtension.lean': '0c6c921536d3cade268948431dd254dd7c602cc04f2d8d4aa7365ab6c39793b7', 'curvature/scripts/point4_c2_c0_metric_velocity_probe.lean': 'c987c8196eba6c879be41a925571c94cd42cf8b04f55b0ab9cfd8c24293e826b', 'docs/point4/c2-c0-metric-velocity/CORRECTED-AUTHOR-FINAL-SOURCE-MANIFEST.json': 'c2368e4cff67ad2ed984d7b94515196001a76d0711c5fb72a4377278a5de5f1a', 'docs/point4/c2-c0-metric-velocity/CORRECTED-AUTHOR-SOURCE-REPORT.md': '41d9c7f125618223f99b008e306ddbd181b021bd33f4685a1b316870070b920e', 'docs/point4/c2-c0-metric-velocity/FINAL-SOURCE-MANIFEST.json': 'c2368e4cff67ad2ed984d7b94515196001a76d0711c5fb72a4377278a5de5f1a', 'docs/point4/c2-c0-metric-velocity/HISTORY-NOTE.md': '47811f7b32f6a3dd0f04c6e9949dce5355e1d5f37fbd5c1d6e2c8672e7c276fa', 'docs/point4/c2-c0-metric-velocity/MASTER-CLOSURE-MANIFEST.json': '49e0eaf78384943bd91932b422f721504fc1e2f0bffe23f9166c6a80eb8dd06d', 'docs/point4/c2-c0-metric-velocity/RELEASE-PATTERN-MANIFEST.json': 'cc1f0aa4325aee4486f73822377f4667c231e9cd3fac1e816c90c288d51a42b8', 'docs/point4/c2-c0-metric-velocity/RELEASE.md': '2a53ba1c9e78b8ccb0dca7e710ce73b074d028c14c6296e49ee3b4f73f92e1e1', 'docs/point4/c2-c0-metric-velocity/SOURCE-REPORT.md': '41d9c7f125618223f99b008e306ddbd181b021bd33f4685a1b316870070b920e', 'docs/point4/c2-c0-metric-velocity/formalization.yaml': '07b7939a7bf2395cda06b8aedfcd305ffc3ffa3217199b2300464c268212d921', 'docs/point4/c2-c0-metric-velocity/frozen-001-to-frozen-003.patch': '15351558b7c673db8542f791b67c8753931c6045f3547ff19f33d3edff8118b5', 'docs/point4/c2-c0-metric-velocity/frozen-003-IMPORT-GRAPH.json': 'aecf6415067c6b8c96f5fc8893d8aba00e0682fb5c2d6c17a54cd040f15e9c6a', 'docs/point4/c2-c0-metric-velocity/frozen-003-to-frozen-001.patch': 'c097b685fedc8ed6ad16d063723b78201d4b4951276e847d9a27a36f591d64a8', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-001/C0EndpointCompactPositivity.lean.txt': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-001/C0FiniteAtlasGaussian.lean.txt': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-001/C0GaussianEndpoint.lean.txt': '16d76518ea457c778d54c2d9c7366af5c530eed81006f9b2454245d7d2df079d', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-001/C2MetricVelocityExtension.lean.txt': 'ea20369d7a63dba3da0d64b964efafe4d2a7ae68c26bc9986bf0868bcac5a24d', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-001/SOURCE-MANIFEST.json': '6fe8395f909f639948a8d41274b9c547709514f2d68d3fdd89b9fa6c3e015118', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-002/C0EndpointCompactPositivity.lean.txt': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-002/C0FiniteAtlasGaussian.lean.txt': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-002/C0GaussianEndpoint.lean.txt': 'dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-002/C2MetricVelocityExtension.lean.txt': '31dbda60b3c654061973de61557cb4dcabe2ab22f32361ba76937f697d84159c', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-002/SOURCE-MANIFEST.json': 'fd2b321720a3ed5f70a051e2cb3ec8e0a15be7e02f3a82b30903a7ddf5a50774', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-003/C0EndpointCompactPositivity.lean.txt': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-003/C0FiniteAtlasGaussian.lean.txt': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-003/C0GaussianEndpoint.lean.txt': 'dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-003/C2MetricVelocityExtension.lean.txt': '0c6c921536d3cade268948431dd254dd7c602cc04f2d8d4aa7365ab6c39793b7', 'docs/point4/c2-c0-metric-velocity/historical-source/frozen-003/SOURCE-MANIFEST.json': '9863890b258643bf0de3b8948c6db623f0192cde614115fca5003005add65dc9', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/EXACT3A8-CONTRACT-RECEIPTS.json': '1f0eff0c9ae1bb81e4e9f020f9fa0ff920cc822a9f34e84838deb7a63ad7ecf5', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Analysis__Calculus__Deriv__Basic.lean.txt': 'da1d29570f45bd14f5a37aa5b024d46b3076a47f04e9315bf72cd65f6505d55b', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Analysis__Calculus__Deriv__Mul.lean.txt': '9eaf8d222c347ea647939daa68fac11edeb7c2572719246ce03d43cb04c94b44', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Geometry__Manifold__PartitionOfUnity.lean.txt': 'dea35887e7f3c058fde7c988e99dda3bf12ecf142784cce8baa84644e892f384', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Geometry__Manifold__VectorBundle__ContMDiffSection.lean.txt': '06fb03179d5f63e43c0a646aa0f87e8903e3189c7b0a7866ce0c7dbad3dc630c', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Geometry__Manifold__VectorBundle__Riemannian.lean.txt': 'e3d87dc3514ff67c64f5c223071dd46842ccaa1138af5df3383e3f283d103b2b', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__Algebra__Module__Spaces__ContinuousLinearMap.lean.txt': '72115f36a523bcfee4dc9979a16067bc1429c576a1524d27f00a44fc64bb521a', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__Algebra__Monoid.lean.txt': 'cf858f52c0f84ad0f0f950ddc0c76128c4893ced7620d0c7a4cef1c9c3ddab56', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__Algebra__Support.lean.txt': 'aab196644260f0c77d8aab52c3151df9c49880c1e9b8ee08cb97193a6ef994a9', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__ContinuousMap__BoundedCompactlySupported.lean.txt': 'd3c748be9a560274e8be6246cdd5ae4eb345ae9279176c7be340f873d2e38ac6', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__ContinuousMap__Bounded__Basic.lean.txt': 'efd930a132ec7cba53752f43961815b719a27514573e52e9894cf5e7fc2e421d', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__FiberBundle__Constructions.lean.txt': 'f0fd3cc7ed96557b9ec6c892438de027366c1d6d730e574070ec6c050e19231d', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__MetricSpace__Pseudo__Lemmas.lean.txt': '0194113c847c252d63b1e3d924a818c3ab72343b2112acf7b0d5c13d133a6431', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__UniformSpace__HeineCantor.lean.txt': '307718982cda076dc252c6506dc9ab94a3c84e3eb92516dda94e364afc0bf07a', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/Mathlib__Topology__VectorBundle__Hom.lean.txt': '8cfe2d2c3dbac2533b45407ebe8c83b6b9cf651c577e8bc3857bba2798d95dd2', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/PINNED-API-SOURCE-RECEIPTS.json': 'c0983af84c5907002c6cd94e680f4e9b25d74767af58ec50243e3e2a6fb70a03', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/READ-ONLY-SOURCE-RECEIPTS.json': '5e38c9f9954edebf38d9fcb1c82585bae33e8727109bf9912f43e964172feb65', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/curvature__PoincareCurvature__Geometry__Manifold__RicciFlow__LocalExistence.lean.txt': 'bf9de4bf83c75b4373d72842dae0eaca96fd2e333df48336f393ff998cce1ddf', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/curvature__PoincareCurvature__Geometry__Manifold__RicciFlow__PointFourContract.lean.txt': '36842cb3898b3a510a597877e7394f7a8e84ab6f716916e7baecb3f7572d1fca', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/exact3a8__curvature__PoincareCurvature__Geometry__Manifold__RicciFlow__LocalExistence.lean.txt': 'bf9de4bf83c75b4373d72842dae0eaca96fd2e333df48336f393ff998cce1ddf', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/exact3a8__curvature__PoincareCurvature__Geometry__Manifold__RicciFlow__PointFourContract.lean.txt': '36842cb3898b3a510a597877e7394f7a8e84ab6f716916e7baecb3f7572d1fca', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/exact3a8__curvature__PoincareCurvature__Geometry__Manifold__VectorBundle__CovariantDerivative__TimeDependent.lean.txt': 'f7d94bc70f0445019dc88bfa3f5ee5d0d6f577d2b57ebeb102e15b6e94aae004', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/exact3a8__curvature__lake-manifest.json': '225d4a9c29a303ce6cc8eb4db7a369c64a2c8666b180758e0ce7097fd2a6935e', 'docs/point4/c2-c0-metric-velocity/pinned-api-source/exact3a8__curvature__lean-toolchain': '302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b', 'docs/point4/c2-c0-metric-velocity/source-review/ADDITIONAL-API-BYTE-AUDIT.tsv': 'c01e86dd5dca92961e572a7af09c560d3272de6de247aed1bd26d1819f9feab8', 'docs/point4/c2-c0-metric-velocity/source-review/AUTHOR-IMPORT-GRAPH.json': '64581be653d2ab17ebfab3a288cb7321a4512ab7bc58dd70397380e3e76749bc', 'docs/point4/c2-c0-metric-velocity/source-review/COMMENT-STRIPPED-PROOF-HOLE-SCAN.txt': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'docs/point4/c2-c0-metric-velocity/source-review/PROJECT-BYTE-AUDIT.tsv': '4fa6112e1293e777b73fa7dc82f9062f9a324a1021887bd5719eb08d052ec67a', 'docs/point4/c2-c0-metric-velocity/source-review/PROJECT-IMPORT-AUDIT.tsv': '9f8f8146c1e41024810b841e05e8896b91c48932fe0a32f2ff2fe41785e99446', 'docs/point4/c2-c0-metric-velocity/source-review/PROVIDED-API-BYTE-AUDIT.tsv': 'b6404fece933bfb8fcb134f1de0aa1df9fe0863d316863b49ab9ffd5876d1b30', 'docs/point4/c2-c0-metric-velocity/source-review/REVIEW-INDEX.json': 'f462e191d1b3acccabb5ca726817c5e93b361c80a55245ac99fe3a2e6af727dd', 'docs/point4/c2-c0-metric-velocity/source-review/REVIEW-MANIFEST.json': 'ecf2d9cab7d03e987ab367723fd3aa2f63159b8394d6d31d672014d4959a9fcf', 'docs/point4/c2-c0-metric-velocity/source-review/REVIEW.md': 'fe937c82aee7f994a5fef19a0d54cfb789988fb2f8df3b9900d66d8290e359a1', 'docs/point4/c2-c0-metric-velocity/source-review/REVIEWED-SOURCE-MANIFEST.json': '6fe8395f909f639948a8d41274b9c547709514f2d68d3fdd89b9fa6c3e015118', 'docs/point4/c2-c0-metric-velocity/source-review/TEXTUAL-PROOF-HOLE-SCAN.txt': '3e596fd0e7453e946d8058d2d447bb4578850deb98ecc6e1601dc0141bda6af9', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/BYTE-ROUNDTRIP-AUDIT.txt': 'e11ddc0b106af2a662304372c96d45f7aa1c134a69b2a6af5adfc809002477de', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/FORWARD-REPLAY.txt': '3298399e4cc014b3887f9175e5a88663265b299859db235819ccb2524d98555f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/REVERSE-REPLAY.txt': '3298399e4cc014b3887f9175e5a88663265b299859db235819ccb2524d98555f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/REVIEW-MANIFEST.json': '77cfbef1ac45361e39a683a68da5904a3a332d3ee828862a980d8bb45ae6f624', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/REVIEW.md': 'bf0f8e8e03ed5760ceadeed4edacb506f165b5ffb0befd1257d6a02337b9dc03', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/REVIEWED-SOURCE-MANIFEST.json': 'fd2b321720a3ed5f70a051e2cb3ec8e0a15be7e02f3a82b30903a7ddf5a50774', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0EndpointCompactPositivity.lean': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0FiniteAtlasGaussian.lean': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean': 'dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C2MetricVelocityExtension.lean': '31dbda60b3c654061973de61557cb4dcabe2ab22f32361ba76937f697d84159c', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/forward.patch': '7aba4400f67623dfcd952692ea7e7830d5ad78cc83fe11595781298af0ee1455', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0EndpointCompactPositivity.lean': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0FiniteAtlasGaussian.lean': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean': '16d76518ea457c778d54c2d9c7366af5c530eed81006f9b2454245d7d2df079d', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C2MetricVelocityExtension.lean': 'ea20369d7a63dba3da0d64b964efafe4d2a7ae68c26bc9986bf0868bcac5a24d', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-002/reverse.patch': '6e3137ecb7aec5f454f95858802d21c859d64e09ab813b8942c3048fce37ac3c', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/BYTE-ROUNDTRIP-AUDIT.txt': 'e11ddc0b106af2a662304372c96d45f7aa1c134a69b2a6af5adfc809002477de', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/FORWARD-REPLAY.txt': '3298399e4cc014b3887f9175e5a88663265b299859db235819ccb2524d98555f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/REVERSE-REPLAY.txt': '3298399e4cc014b3887f9175e5a88663265b299859db235819ccb2524d98555f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/REVIEW-MANIFEST.json': '0c4e3cb926cce8f904f0dd8cb64feadb0fbf75354cc0593f8087ab806932dfdb', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/REVIEW.md': '07c9bce974d0fe9b4bf4d7044263bdf520dfeecc018873078674c4481ee4c5fa', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/REVIEWED-SOURCE-MANIFEST.json': '9863890b258643bf0de3b8948c6db623f0192cde614115fca5003005add65dc9', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0EndpointCompactPositivity.lean': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0FiniteAtlasGaussian.lean': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean': 'dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/forward-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C2MetricVelocityExtension.lean': '0c6c921536d3cade268948431dd254dd7c602cc04f2d8d4aa7365ab6c39793b7', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/forward.patch': '15351558b7c673db8542f791b67c8753931c6045f3547ff19f33d3edff8118b5', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0EndpointCompactPositivity.lean': '45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0FiniteAtlasGaussian.lean': '474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean': '16d76518ea457c778d54c2d9c7366af5c530eed81006f9b2454245d7d2df079d', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/reverse-reconstruction/curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C2MetricVelocityExtension.lean': 'ea20369d7a63dba3da0d64b964efafe4d2a7ae68c26bc9986bf0868bcac5a24d', 'docs/point4/c2-c0-metric-velocity/source-review/replacement-frozen-003/reverse.patch': 'c097b685fedc8ed6ad16d063723b78201d4b4951276e847d9a27a36f591d64a8'}

# The public frozen-003 identity remains historical. This active candidate is
# exactly five proof-only replacements, reversible to the full approved bytes.
PROOF_REPAIR_PATH = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/C0GaussianEndpoint.lean'
PROOF_REPAIR_PARENT = '6d8482764236bb71b101d313669b5271f4597d00'
PROOF_REPAIR_ORIGINAL_SHA256 = 'dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8'
PROOF_REPAIR_SHA256 = '122a2a7631e85adcf031894226a0237e8791770ebb4f784b8af4b57a38e010ea'
PROOF_REPAIR_TRANSFORMS = ((b'  simpa only [gaussianPath] using houter.comp ht\n', b'  change ContinuousAt (heatFlowPathBcf f \xe2\x88\x98 smoothingTime) 0\n  exact houter.comp ht\n'), (b'  exact (by simpa only [Real.norm_eq_abs] using\n    (gaussianPath f h).norm_coe_le_norm z).trans (norm_gaussianPath_le f h)\n', b'  have habs : |gaussianPath f h z| \xe2\x89\xa4 \xe2\x80\x96gaussianPath f h\xe2\x80\x96 := by\n    simpa only [Real.norm_eq_abs] using (gaussianPath f h).norm_coe_le_norm z\n  exact habs.trans (norm_gaussianPath_le f h)\n'), (b'  simpa only [heatSemigroupNDbcf_apply] using\n    contDiff_two_heatSemigroupND (smoothingTime_pos hh) f\n', b'  have hcoe : (heatSemigroupNDbcf (smoothingTime_pos hh) f : (Fin n \xe2\x86\x92 \xe2\x84\x9d) \xe2\x86\x92 \xe2\x84\x9d) =\n      heatSemigroupND (smoothingTime h) f := by\n    funext z\n    exact heatSemigroupNDbcf_apply (smoothingTime_pos hh) f z\n  rw [hcoe]\n  exact contDiff_two_heatSemigroupND (smoothingTime_pos hh) f\n'), (b'    simpa only [sub_self, norm_zero] using\n      (ha.sub continuousAt_const).norm.tendsto\n', b'    simpa only [Pi.sub_apply, sub_self, norm_zero] using\n      (ha.sub (continuousAt_const : ContinuousAt (fun _ : \xe2\x84\x9d => a 0) 0)).norm.tendsto\n'), (b'    simp only [\xe2\x86\x90 mul_assoc, inv_mul_cancel\xe2\x82\x80 (norm_ne_zero_iff.mpr hh), one_mul]\n', b'    simp only [\xe2\x86\x90 mul_assoc, inv_mul_cancel\xe2\x82\x80 (norm_ne_zero_iff.mpr hh), one_mul]\n    exact le_rfl\n'))

# Importlib writes a module's bytecode before executing its body. Suppression
# must therefore be set by the interpreter-startup environment, never by a
# cache exemption or deletion after the inherited caller has imported C2.
STARTUP_ENV = "    env:\n      PYTHONDONTWRITEBYTECODE: '1'\n"
STARTUP_WORKFLOWS = {
    '.github/workflows/point4-linear-heat-geometry.yml': (
        '2cfd17bf27e5e5983bf8a524948382a1965dcd7f6a44a5a5efe44bae91dbf582',
        'linear_heat_geometry',
        '  linear_heat_geometry:\n    name: Exact-head combined source, all 127 axiom occurrences, closed contract and full audit\n'),
    '.github/workflows/point4-c2-initial-heat.yml': (
        'bb3efbcc8a477181aea2857a002f2d5eb7b7670ad34527dd231d9cfa5c543f3d',
        'c2_initial_heat',
        '  c2_initial_heat:\n    name: Exact-head C2 union, all 150 axiom occurrences, current contract and full audit\n'),
    '.github/workflows/point4-weighted-initial-heat.yml': (
        '3b52ebefb56317864cc95ba9dacf8276776d51d82e25f5ad83e2083638f4be8a',
        'weighted_initial_heat',
        '  weighted_initial_heat:\n    name: Exact-head weighted heat certificate with unchanged full audit\n'),
}


# Exact old primary workflow plus two reversible, independent Git checkpoints.
EXACT_HEAD_WORKFLOW_BASE = '6d8482764236bb71b101d313669b5271f4597d00'
EXACT_HEAD_WORKFLOW_PATH = '.github/workflows/point4-c2-c0-metric-velocity.yml'
EXACT_HEAD_WORKFLOW_JOB = 'c2_c0_metric_velocity'
EXACT_HEAD_WORKFLOW_ORIGINAL_SHA256 = 'ccfa96a33bfc5d6466987c73bb490ba48ff7d0e8c01f5424ea426aa39170efe9'
EXACT_HEAD_WORKFLOW_SHA256 = '3bca55c2b29333871b09213ce586e3315c8678993692e33eff85346062dfe10c'
EXACT_HEAD_BEFORE_ANCHOR = '      - name: Install pinned safe YAML parser from the official package registry\n'
EXACT_HEAD_AFTER_ANCHOR = '      - name: Preserve exact-head evidence\n'
EXACT_HEAD_PREFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness before candidate gates\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'
EXACT_HEAD_POSTFLIGHT = '      - name: Check immutable release HEAD and tracked cleanliness after candidate gates\n        if: always()\n        env:\n          GIT_NO_LAZY_FETCH: \'1\'\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          set -euo pipefail\n          test "$(/usr/bin/git --no-replace-objects rev-parse HEAD)" = "$EXPECTED_SHA"\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --cached --no-ext-diff --no-textconv --ignore-submodules=none --exit-code HEAD -- .\n          /usr/bin/git --no-replace-objects -c core.fileMode=true -c core.fsmonitor=false diff --no-ext-diff --no-textconv --ignore-submodules=none --exit-code -- .\n          /usr/bin/python3 -I -B - <<\'PY_TRACKED_SOURCE\'\n          import hashlib, os, pathlib, stat, subprocess\n          root = pathlib.Path(\'.\').absolute()\n          def git(*args):\n              return subprocess.check_output([\'/usr/bin/git\', \'--no-replace-objects\', \'-C\', str(root), *args])\n          expected_sha = os.environ[\'EXPECTED_SHA\']\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD mismatch\'\n          head = {}\n          for record in git(\'ls-tree\', \'-rz\', expected_sha).split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, kind, oid = descriptor.decode().split()\n              path = name.decode()\n              assert kind == \'blob\' and mode in {\'100644\', \'100755\'} and path not in head\n              head[path] = (mode, oid)\n          index = {}\n          for record in git(\'ls-files\', \'--stage\', \'-z\').split(b\'\\0\')[:-1]:\n              descriptor, name = record.split(b\'\\t\', 1)\n              mode, oid, stage = descriptor.decode().split()\n              path = name.decode()\n              assert stage == \'0\' and path not in index\n              index[path] = (mode, oid)\n          assert index == head, \'Independent tracked index/HEAD identity mismatch\'\n          for path, (mode, oid) in head.items():\n              physical = root / path\n              for parent in physical.parents:\n                  assert stat.S_ISDIR(parent.lstat().st_mode), \'Independent tracked source directory/symlink drift\'\n                  if parent == root:\n                      break\n              actual_mode = physical.lstat().st_mode\n              assert stat.S_ISREG(actual_mode) and bool(actual_mode & 0o111) == (mode == \'100755\'), \'Independent tracked source file/mode drift\'\n              data = physical.read_bytes()\n              blob = hashlib.sha1(b\'blob \' + str(len(data)).encode() + b\'\\0\' + data).hexdigest()\n              assert blob == oid, \'Independent tracked physical/HEAD blob mismatch: \' + path\n          assert git(\'rev-parse\', \'HEAD\').decode().strip() == expected_sha, \'Independent expected release HEAD changed during tracked inspection\'\n          PY_TRACKED_SOURCE\n'


def raw_git(*args: str) -> bytes:
    """Read the actual committed self objects without Git replacement refs."""
    return subprocess.check_output(['/usr/bin/git', '--no-replace-objects', '-C', str(ROOT), *args], env=ENV)


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(ROOT), *args], env=ENV)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def adapted_c2_guard(original: bytes) -> bytes:
    assert sha256(original) == C2_ORIGINAL_SHA256, 'Inherited guard original digest changed'
    source = original.decode()
    assert source.count(ENTRY_POINT) == 1, 'Inherited guard needs exactly one original entry point'
    assert C2_ADAPTER not in source, 'Inherited guard adapter already present'
    return source.replace(ENTRY_POINT, C2_ADAPTER + ENTRY_POINT.lstrip('\n'), 1).encode()


def parse_workflow(source: str) -> dict:
    import yaml
    class StrictWorkflowLoader(yaml.BaseLoader):
        def construct_mapping(self, node, deep=False):
            result = {}
            for key_node, value_node in node.value:
                key = self.construct_object(key_node, deep=deep)
                assert isinstance(key, str), 'Workflow mapping key must be a string'
                assert key not in result, f'Duplicate workflow YAML mapping key: {key}'
                result[key] = self.construct_object(value_node, deep=deep)
            return result
    data = yaml.load(source, Loader=StrictWorkflowLoader)
    assert isinstance(data, dict), 'Workflow must be a mapping'
    return data


def adapted_startup_workflow(path: str, original: bytes) -> bytes:
    assert path in STARTUP_WORKFLOWS, 'Unapproved startup workflow path'
    digest, job, anchor = STARTUP_WORKFLOWS[path]
    assert sha256(original) == digest, f'Inherited startup workflow original digest changed: {path}'
    source = original.decode()
    assert source.count(anchor) == 1, 'Startup workflow needs exactly one pinned job header'
    assert STARTUP_ENV not in source, 'Startup workflow adapter already present'
    before = parse_workflow(source)
    assert 'env' not in before and 'env' not in before['jobs'][job], 'Inherited startup environment changed'
    adapted = source.replace(anchor, anchor + STARTUP_ENV, 1)
    wanted = json.loads(json.dumps(before))
    wanted['jobs'][job]['env'] = {'PYTHONDONTWRITEBYTECODE': '1'}
    assert parse_workflow(adapted) == wanted, 'Startup workflow semantic remainder changed'
    assert adapted.count(STARTUP_ENV) == 1, 'Startup workflow adapter must occur once'
    assert adapted.replace(STARTUP_ENV, '', 1).encode() == original, 'Startup workflow byte remainder changed'
    return adapted.encode()


def restored_startup_workflow(path: str, actual: bytes) -> bytes:
    # Validate exact bytes and duplicate-free semantics before restoring the
    # original input for the unchanged inherited workflow validator.
    original = baseline_sources()[path][1]
    expected = adapted_startup_workflow(path, original)
    assert parse_workflow(actual.decode()) == parse_workflow(expected.decode()), 'Startup workflow semantic drift'
    assert actual == expected, f'Exact startup workflow changed: {path}'
    assert actual.decode().count(STARTUP_ENV) == 1, 'Startup workflow adapter count changed'
    restored = actual.decode().replace(STARTUP_ENV, '', 1).encode()
    assert restored == original, 'Startup workflow inherited remainder changed'
    return restored


@functools.lru_cache(maxsize=1)
def baseline_sources() -> dict[str, tuple[str, bytes]]:
    records = git('ls-tree', '-rz', BASE)
    assert records.endswith(b'\0'), 'Baseline inventory must be NUL-terminated'
    result = {}
    for record in records.split(b'\0'):
        if not record:
            continue
        descriptor, path_bytes = record.split(b'\t', 1)
        mode, kind, object_id = descriptor.decode().split()
        path = path_bytes.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}, 'Unsupported baseline file type'
        assert path not in result, 'Duplicate baseline path'
        result[path] = (mode, git('show', f'{BASE}:{path}'))
    assert len(result) == 1641, 'Baseline source count changed'
    return result





def adapted_gaussian_proofs(original: bytes) -> bytes:
    assert sha256(original) == PROOF_REPAIR_ORIGINAL_SHA256, 'Historical Gaussian proof identity drift'
    actual = original
    for before, after in PROOF_REPAIR_TRANSFORMS:
        assert actual.count(before) == 1 and after not in actual, 'Gaussian forward proof transform must occur once'
        actual = actual.replace(before, after, 1)
    assert sha256(actual) == PROOF_REPAIR_SHA256, 'Repaired Gaussian proof identity drift'
    return actual


def restored_gaussian_proofs(actual: bytes) -> bytes:
    assert sha256(actual) == PROOF_REPAIR_SHA256, 'Repaired Gaussian proof identity drift'
    original = actual
    for before, after in reversed(PROOF_REPAIR_TRANSFORMS):
        assert original.count(after) == 1, 'Gaussian reverse proof transform must occur once'
        original = original.replace(after, before, 1)
    assert sha256(original) == PROOF_REPAIR_ORIGINAL_SHA256, 'Historical Gaussian proof identity drift'
    assert adapted_gaussian_proofs(original) == actual, 'Gaussian full-source byte roundtrip failed'
    historical_path = DOSSIER + 'historical-source/frozen-003/C0GaussianEndpoint.lean.txt'
    historical = (ROOT / historical_path).read_bytes()
    assert sha256(historical) == UNIT_FILE_SHA256[historical_path] == PROOF_REPAIR_ORIGINAL_SHA256
    assert original == historical == git('show', f'{PROOF_REPAIR_PARENT}:{PROOF_REPAIR_PATH}'), 'Gaussian reverse source differs from public historical head'
    frozen = json.loads((ROOT / (DOSSIER + 'FINAL-SOURCE-MANIFEST.json')).read_text())
    assert frozen['current_source_identity'] == 'frozen-003', 'Historical approved manifest identity drift'
    row, = [row for row in frozen['current_files'] if row['file'] == 'C0GaussianEndpoint.lean']
    assert (len(original), sha256(original), git_blob_identity(original)) == (row['bytes'], row['sha256'], row['git_blob_sha1']), 'Reverse-normalized Gaussian source does not match approved full-source manifest'
    return original


def check_unit_blob(path: str, actual: bytes) -> None:
    assert path in UNIT_FILE_SHA256, f'Non-enumerated release blob: {path}'
    assert sha256(actual) == UNIT_FILE_SHA256[path], f'Exact release blob changed: {path}'
    if path == PROOF_REPAIR_PATH:
        restored_gaussian_proofs(actual)


def check_source_closure() -> None:
    graph = json.loads((ROOT / CLOSURE_MANIFEST).read_text())
    assert (graph['base'], graph['review_source_baseline'], graph['contract_reference']) == (
        BASE, '90cc7ebed996f28acb57ef9948d37f114088bd4d',
        '3a8ed697d1f0366f8370efb2fa9e524b68d27e97'), 'Project provenance pin drift'
    assert graph['all_reachable_inherited_sources_match'] is True
    assert (graph['inherited_module_count'], graph['project_module_count'], graph['external_frontier_count']) == (59, 63, 93)
    assert graph['external_graph_complete'] is False, 'Uninspected external graph may not be promoted'
    records = {}
    for row in graph['records']:
        assert row['module'] not in records, 'Duplicate closure module'
        data = (ROOT / row['path']).read_bytes()
        assert len(data) == row['bytes'] and sha256(data) == row['sha256']
        assert git_blob_identity(data) == row['git_blob_sha1'], 'Inherited closure blob drift'
        assert data == baseline_sources()[row['path']][1], 'Closure does not match master'
        records[row['module']] = row
    for name in MODULE_NAMES:
        path = MODULE_PREFIX + name + '.lean'
        data = (ROOT / path).read_bytes()
        records[path.removeprefix('curvature/').removesuffix('.lean').replace('/', '.')] = {
            'path': path, 'imports': source_imports(data),
            'legacy': not bool(re.search(rb'^module\s*$', data, re.M))}
    assert len(records) == 63
    todo = [path.removeprefix('curvature/').removesuffix('.lean').replace('/', '.') for path in MODULES]
    visited, external = set(), set()
    while todo:
        module = todo.pop()
        if module in visited:
            continue
        if module not in records:
            external.add(module)
            continue
        visited.add(module)
        row = records[module]
        data = (ROOT / row['path']).read_bytes()
        assert source_imports(data) == row['imports'], 'Actual import closure drift'
        legacy = not bool(re.search(rb'^module\s*$', data, re.M))
        assert legacy == row['legacy'], 'Source header drift'
        for child in row['imports']:
            assert legacy or child not in records or not records[child]['legacy'], 'Modern-to-legacy project import edge'
        todo.extend(row['imports'])
    assert visited == set(records), 'Unreachable/missing reviewed project module'
    assert external == set(graph['external_frontier']) and len(external) == 93, 'External frontier drift'
    assert (ROOT / 'curvature/lean-toolchain').read_bytes() == b'leanprover/lean4:v4.33.0\n'
    packages = json.loads((ROOT / 'curvature/lake-manifest.json').read_text())['packages']
    mathlib = [package for package in packages if package['name'] == 'mathlib']
    assert len(mathlib) == 1 and mathlib[0]['rev'] == MATHLIB, 'Mathlib pin drift'


def source_imports(source: bytes) -> list[str]:
    result = []
    for line in source.decode().splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+([^\n]+)', line)
        if match:
            result.extend(name for name in match.group(1).split('--')[0].split()
                          if re.fullmatch(r'[A-Za-z0-9_.]+', name))
    return result



def check_new_workflow(actual: bytes) -> None:
    check_unit_blob(WORKFLOW, actual)
    parsed = parse_workflow(actual.decode())
    assert set(parsed['jobs']) == {'c2_c0_metric_velocity'}, 'Primary workflow job drift'
    job = parsed['jobs']['c2_c0_metric_velocity']
    assert job['env'] == {'PYTHONDONTWRITEBYTECODE': '1'}, 'Primary interpreter-startup environment drift'
    assert parsed['permissions'] == {'contents': 'read'}, 'Workflow permission drift'
    assert 'env' not in parsed, 'Unexpected workflow-global environment'
    for step in job['steps']:
        assert 'continue-on-error' not in step, 'Qualification gate may not be optional'
        assert 'PYTHONDONTWRITEBYTECODE' not in step.get('env', {}), 'Step-level startup suppression override'
        assert 'if' not in step or step['if'] == 'always()', 'Mandatory qualification stage may not be skipped'


def check_new_metadata(source: str) -> None:
    guard = c2_guard()
    parsed = guard.parse_metadata(source)
    entries = guard.metadata_entries(source)
    wanted = {
        f'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/{BASE}/curvature',
        'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/90cc7ebed996f28acb57ef9948d37f114088bd4d/curvature',
        'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/3a8ed697d1f0366f8370efb2fa9e524b68d27e97/curvature',
        f'https://github.com/leanprover-community/mathlib4/tree/{MATHLIB}/Mathlib',
    }
    assert set(entries) == wanted and all(value[0] == 'builds-on' for value in entries.values()), 'New parsed provenance drift'
    assert parsed['status']['main_results'] == [] and 'OPEN' in parsed['status']['scope'], 'Supporting scope drift'
    assert parsed['review']['status'] == 'pending', 'Source approval cannot promote integration/kernel review status'
    check_unit_blob(METADATA, source.encode())


def check_new_probe(output: str) -> None:
    source = (ROOT / PROBE).read_text()
    names = c2_guard().check_axiom_output(source, output)
    assert len(names) == 29, 'Reviewed actual axiom surface count changed'
    begin, end = 'C2_C0_METRIC_VELOCITY_TYPES_BEGIN', 'C2_C0_METRIC_VELOCITY_TYPES_END'
    assert output.count(begin) == 1 and output.count(end) == 1, 'Missing/duplicate complete type report'
    types = output.split(begin, 1)[1].split(end, 1)[0]
    for token in ('ExpectedC2C0MetricVelocity', 'c2C0MetricVelocityFullSignatureAssignment',
                  'ContinuousSymmetricVelocity', 'RicciFlow.MetricFamily', 'RicciFlow.metricTensor',
                  'ContMDiffRiemannianMetric', 'gaussianTensor', 'endpointTensor', 'centeredMetric',
                  'exists_c2_metricFamily_with_c0_endpoint_velocity',
                  'c2C0MetricVelocityCanonicalContext', 'c2C0MetricVelocityRankZeroContext',
                  'c2C0MetricVelocityEmptyManifoldContext', 'HasDerivAt', 'BoundarylessManifold'):
        assert token in types, f'Missing complete mathematical type: {token}'
    for token in ('HasDerivWithinAt', 'ModelWithCorners.Boundaryless', 'I.Boundaryless',
                  'initialHolder', 'BoundedC3', 'sorryAx'):
        assert token not in types, f'Unapproved mathematical premise/surface: {token}'


def check_release_self_sources() -> None:
    """Bind each reviewed self file to stage-zero index and committed HEAD.

    A source-only development tree can be staged, but it is not an exact-head
    release until the reviewed files are committed. No self digest is recursive.
    """
    paths = sorted(SELF_PATHS)
    head = {}
    for record in nul_records(raw_git('ls-tree', '-rz', 'HEAD', '--', *paths)):
        descriptor, name = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = name.decode()
        assert path in SELF_PATHS and path not in head, 'Committed self inventory drift'
        assert kind == 'blob' and mode == '100644' and re.fullmatch(r'[0-9a-f]{40}', oid), 'Committed self blob/mode drift'
        head[path] = (mode, oid)
    assert set(head) == SELF_PATHS, 'Missing committed self source'
    index = {}
    for record in nul_records(raw_git('ls-files', '--stage', '-z', '--', *paths)):
        descriptor, name = record.split(b'\t', 1)
        mode, oid, stage = descriptor.decode().split()
        path = name.decode()
        assert path in SELF_PATHS and path not in index and stage == '0', 'Unmerged/missing self index source'
        assert re.fullmatch(r'[0-9a-f]{40}', oid), 'Self index blob identity drift'
        index[path] = (mode, oid)
    assert index == head, 'Self index/committed HEAD blob or mode mismatch'
    for path, (mode, oid) in head.items():
        actual = ROOT / path
        physical = actual.lstat().st_mode
        assert stat.S_ISREG(physical) and not physical & 0o111, 'Self physical file/mode drift'
        data = actual.read_bytes()
        identity = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert identity == oid, 'Self physical/committed HEAD blob mismatch: ' + path



def adapted_exact_head_workflow(original: bytes) -> bytes:
    """Insert two independent checkpoints; every original byte stays exact."""
    assert sha256(original) == EXACT_HEAD_WORKFLOW_ORIGINAL_SHA256, 'Original primary workflow digest drift'
    source = original.decode()
    assert source.count(EXACT_HEAD_BEFORE_ANCHOR) == 1 and source.count(EXACT_HEAD_AFTER_ANCHOR) == 1, 'Primary workflow checkpoint anchor count drift'
    assert EXACT_HEAD_PREFLIGHT not in source and EXACT_HEAD_POSTFLIGHT not in source, 'Primary workflow checkpoints already present'
    adapted = source.replace(EXACT_HEAD_BEFORE_ANCHOR, EXACT_HEAD_PREFLIGHT + EXACT_HEAD_BEFORE_ANCHOR, 1)
    adapted = adapted.replace(EXACT_HEAD_AFTER_ANCHOR, EXACT_HEAD_POSTFLIGHT + EXACT_HEAD_AFTER_ANCHOR, 1)
    before = parse_workflow(source)
    after = parse_workflow(adapted)
    steps = after['jobs'][EXACT_HEAD_WORKFLOW_JOB]['steps']
    assert len(steps) == len(before['jobs'][EXACT_HEAD_WORKFLOW_JOB]['steps']) + 2, 'Primary workflow checkpoint count drift'
    assert steps.pop(-2) == parse_workflow('steps:\n' + EXACT_HEAD_POSTFLIGHT)['steps'][0], 'Post-gate exact-head checkpoint drift'
    assert steps.pop(1) == parse_workflow('steps:\n' + EXACT_HEAD_PREFLIGHT)['steps'][0], 'Pre-gate exact-head checkpoint drift'
    assert after == before, 'Original primary workflow semantics changed'
    assert adapted.count(EXACT_HEAD_PREFLIGHT) == adapted.count(EXACT_HEAD_POSTFLIGHT) == 1, 'Duplicate exact-head checkpoint'
    assert adapted.replace(EXACT_HEAD_PREFLIGHT, '', 1).replace(EXACT_HEAD_POSTFLIGHT, '', 1).encode() == original, 'Original primary workflow bytes changed'
    assert sha256(adapted.encode()) == EXACT_HEAD_WORKFLOW_SHA256, 'Adapted primary workflow digest drift'
    return adapted.encode()


def restored_exact_head_workflow(actual: bytes) -> bytes:
    original = git('show', EXACT_HEAD_WORKFLOW_BASE + ':' + EXACT_HEAD_WORKFLOW_PATH)
    expected = adapted_exact_head_workflow(original)
    assert parse_workflow(actual.decode()) == parse_workflow(expected.decode()), 'Primary workflow exact-head semantic drift'
    assert actual == expected, 'Primary workflow exact-head bytes changed'
    restored = actual.decode().replace(EXACT_HEAD_PREFLIGHT, '', 1).replace(EXACT_HEAD_POSTFLIGHT, '', 1).encode()
    assert restored == original, 'Primary workflow original remainder changed'
    return restored


def expected_sources() -> dict[str, tuple[str, bytes]]:
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True, env=ENV)
    baseline = baseline_sources()
    expected = {path: (BASE, data) for path, (_, data) in baseline.items()}
    expected[C2_GUARD] = (BASE, adapted_c2_guard(baseline[C2_GUARD][1]))
    for path in STARTUP_WORKFLOWS:
        expected[path] = (BASE, adapted_startup_workflow(path, baseline[path][1]))
    assert not set(UNIT_FILE_SHA256) & set(baseline), 'New release path overlaps baseline'
    assert not SELF_PATHS & (set(baseline) | set(UNIT_FILE_SHA256)), 'Guard/test path collision'
    for path in UNIT_FILE_SHA256:
        data = (ROOT / path).read_bytes()
        check_unit_blob(path, data)
        expected[path] = (BASE, data)
    check_release_self_sources()
    restored_exact_head_workflow((ROOT / EXACT_HEAD_WORKFLOW_PATH).read_bytes())
    check_inventory()
    return expected


def public_paths() -> set[str]:
    return set(baseline_sources()) | set(UNIT_FILE_SHA256) | SELF_PATHS


def nul_records(output: bytes) -> list[bytes]:
    assert not output or output.endswith(b'\0'), 'Git inventory must be NUL-terminated'
    records = output.split(b'\0')[:-1] if output else []
    assert all(records), 'Empty inventory record'
    return records


def nul_paths(output: bytes) -> set[str]:
    paths = [record.decode() for record in nul_records(output)]
    assert len(paths) == len(set(paths)), 'Duplicate inventory path'
    return set(paths)


LAKE_ROOTS = ('curvature/.lake', 'hamilton-ivey-reaction/.lake')
MANIFESTS = ('curvature/lake-manifest.json', 'hamilton-ivey-reaction/lake-manifest.json')
# The pinned ProofWidgets widgetPackageLock target uses Lake's text-file hash.
# Lake 4.33 writes exactly 16 lowercase hex bytes beside this tracked input.
# This is one fixed sidecar, never a package-wide or arbitrary .hash exemption.
PROOFWIDGETS_REV = '4be2e3d5087eeb272cf5a8853b8f9dd025ef5957'
PROOFWIDGETS_LOCK = 'curvature/.lake/packages/proofwidgets/widget/package-lock.json'
PROOFWIDGETS_LOCK_BLOB = '06d5baf2fae78fed1fdae485f4c2c054a0bccfb2'
PROOFWIDGETS_LOCK_SIZE = 172140
PROOFWIDGETS_FINGERPRINT = PROOFWIDGETS_LOCK + '.hash'
# Source-derived for the pinned Linux/little-endian Lean 4.33 text hash;
# this is not a compiler/runtime qualification claim. See release integration.
PROOFWIDGETS_LOCK_HASH = b'179e66574f04806e'
OUTPUT_SUFFIXES = {'.olean', '.ilean', '.private', '.server', '.ir', '.sig', '.hash',
                   '.trace', '.lock', '.json', '.c', '.o', '.export', '.rsp', '.a', '.so', '.h',
                   '.dll', '.dylib', '.bc', '.exe', '.js', '.map', '.css', '.html',
                   '.svg', '.png', '.woff', '.woff2', '.wasm'}


def runtime_path(path: str) -> bool:
    return any(path.startswith(root + '/') for root in LAKE_ROOTS)


def lake_runtime_roots() -> set[str]:
    roots = set(LAKE_ROOTS)
    baseline = baseline_sources()
    for path in MANIFESTS:
        if path in baseline:
            manifest = json.loads(baseline[path][1])
            parent = pathlib.PurePosixPath(path).parent
            roots |= {str(parent / '.lake/packages' / package['name'] / '.lake')
                      for package in manifest['packages'] if package['type'] == 'git'}
    return roots


def generated_build_path(path: str) -> bool:
    p = pathlib.PurePosixPath(path)
    if '__pycache__' in p.parts or p.suffix in {'.lean', '.py', '.pyc', '.pyo'}:
        return False
    for root in lake_runtime_roots():
        relative = path.removeprefix(root + '/')
        if relative == path:
            continue
        if relative.startswith(('build/', 'config/')):
            return p.suffix in OUTPUT_SUFFIXES or relative in {'build/bin/cache', 'build/bin/leantar'}
        if relative.startswith('lakefile.olean'):
            return relative in {'lakefile.olean', 'lakefile.olean.trace', 'lakefile.olean.hash'}
    return False


def git_at(root: pathlib.Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(root), *args], env=ENV)


def git_blob_identity(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def dependency_inventory() -> tuple[set[str], set[str]]:
    # Dependency source is not an arbitrary .lake exemption: each physically
    # present package must have the pinned HEAD and every tracked blob/mode.
    # The full physical walk below rejects all other source and Python caches.
    sources, git_roots = set(), set()
    baseline = baseline_sources()
    for manifest_path in MANIFESTS:
        if manifest_path not in baseline:
            continue  # Small synthetic fixtures have no dependency manifests.
        manifest = json.loads(baseline[manifest_path][1])
        assert manifest['packagesDir'] == '.lake/packages', 'Dependency layout drift'
        parent = pathlib.PurePosixPath(manifest_path).parent
        packages_root = parent / '.lake/packages'
        wanted = {package['name']: package['rev'] for package in manifest['packages'] if package['type'] == 'git'}
        actual_root = ROOT / packages_root
        if not actual_root.exists():
            continue
        assert actual_root.is_dir() and not actual_root.is_symlink(), 'Non-directory dependency root'
        assert {p.name for p in actual_root.iterdir()} <= set(wanted), 'Unexpected dependency package'
        for package_dir in actual_root.iterdir():
            assert package_dir.is_dir() and not package_dir.is_symlink(), 'Symlink/non-directory dependency'
            revision = wanted[package_dir.name]
            assert git_at(package_dir, 'rev-parse', 'HEAD').decode().strip() == revision, 'Dependency HEAD drift'
            git_root = package_dir.relative_to(ROOT).as_posix() + '/.git'
            assert (package_dir / '.git').exists(), 'Missing dependency Git metadata'
            git_roots.add(git_root)
            for record in nul_records(git_at(package_dir, 'ls-tree', '-rz', revision)):
                descriptor, name = record.split(b'\t', 1)
                mode, kind, oid = descriptor.decode().split()
                path = package_dir / name.decode()
                assert kind == 'blob' and mode in {'100644', '100755', '120000'}, 'Unsupported dependency source type'
                relative = path.relative_to(ROOT).as_posix()
                assert relative not in sources, 'Duplicate dependency source'
                assert '__pycache__' not in pathlib.PurePosixPath(relative).parts and path.suffix not in {'.pyc', '.pyo'}, 'Dependency interpreter cache'
                if mode == '120000':
                    assert stat.S_ISLNK(path.lstat().st_mode), 'Pinned dependency symlink type drift'
                    data = os.readlink(path).encode()
                else:
                    check_mode(relative, path.lstat().st_mode, mode)
                    data = path.read_bytes()
                assert git_blob_identity(data) == oid, f'Dependency source drift: {relative}'
                sources.add(relative)
    return sources, git_roots


def runtime_fingerprints(dependencies: set[str]) -> set[str]:
    path = ROOT / PROOFWIDGETS_FINGERPRINT
    if not path.exists() and not path.is_symlink():
        return set()
    # Require the unchanged manifest entry, verified package HEAD and full
    # dependency inventory before reading the fixed regular source and sidecar.
    manifest = json.loads(baseline_sources()['curvature/lake-manifest.json'][1])
    assert manifest['packagesDir'] == '.lake/packages', 'Fingerprint dependency layout drift'
    packages = [p for p in manifest['packages'] if p['name'] == 'proofwidgets']
    assert len(packages) == 1, 'Fingerprint package identity drift'
    package = packages[0]
    assert (package['type'], package['url'], package['rev']) == (
        'git', 'https://github.com/leanprover-community/ProofWidgets4', PROOFWIDGETS_REV), 'Fingerprint package pin drift'
    assert PROOFWIDGETS_LOCK in dependencies, 'Fingerprint parent is not a verified dependency source'
    package_dir = ROOT / 'curvature/.lake/packages/proofwidgets'
    assert git_at(package_dir, 'rev-parse', 'HEAD').decode().strip() == PROOFWIDGETS_REV, 'Fingerprint dependency HEAD drift'
    for parent in path.parents:
        if parent == ROOT:
            break
        assert stat.S_ISDIR(parent.lstat().st_mode), f'Non-directory/symlink fingerprint parent: {parent}'
    source = ROOT / PROOFWIDGETS_LOCK
    check_mode(PROOFWIDGETS_LOCK, source.lstat().st_mode, '100644')
    assert source.stat().st_size == PROOFWIDGETS_LOCK_SIZE, 'Fingerprint source size drift'
    assert git_blob_identity(source.read_bytes()) == PROOFWIDGETS_LOCK_BLOB, 'Fingerprint source blob drift'
    check_mode(PROOFWIDGETS_FINGERPRINT, path.lstat().st_mode, '100644')
    assert path.stat().st_size == 16, 'Fingerprint must be exactly 16 bytes'
    with path.open('rb') as stream:
        fingerprint = stream.read(17)
    assert re.fullmatch(rb'[0-9a-f]{16}', fingerprint), 'Noncanonical Lake fingerprint'
    assert fingerprint == PROOFWIDGETS_LOCK_HASH, 'Pinned input fingerprint mismatch'
    return {PROOFWIDGETS_FINGERPRINT}


def check_inventory_sets(tracked: set[str], untracked: set[str], physical: set[str], dependencies: set[str] | None = None, git_roots: set[str] | None = None, fingerprints: set[str] | None = None) -> None:
    assert not tracked & untracked, 'Overlapping tracked/untracked inventory'
    assert set(baseline_sources()) <= tracked, 'Inherited source must stay tracked'
    assert not any(runtime_path(path) for path in tracked), 'Tracked Lake cache forbidden'
    dependencies, git_roots = dependencies or set(), git_roots or set()
    fingerprints = fingerprints or set()
    assert fingerprints <= {PROOFWIDGETS_FINGERPRINT}, 'Unapproved runtime fingerprint path'
    def runtime_file(path):
        # Git reports an untracked nested repository as one trailing-slash
        # directory record. Its pinned source inventory was validated separately.
        return path in dependencies or path in fingerprints or generated_build_path(path) or any(
            path == root.removesuffix('/.git') + '/' or path == root or path.startswith(root + '/')
            for root in git_roots)
    untracked_source = {path for path in untracked if not runtime_file(path)}
    assert untracked_source <= set(UNIT_FILE_SHA256) | SELF_PATHS, 'Unexpected untracked/ignored source or cache'
    check_public_paths(tracked | untracked_source)
    check_public_paths(physical)


def check_inventory() -> None:
    tracked_modes = {}
    tracked_objects = {}
    for record in nul_records(git('ls-files', '--stage', '-z')):
        descriptor, name = record.split(b'\t', 1)
        mode, oid, stage = descriptor.decode().split()
        path = name.decode()
        assert stage == '0' and mode in {'100644', '100755'}, 'Unmerged/non-regular tracked source'
        assert path not in tracked_modes, 'Duplicate tracked path'
        tracked_modes[path] = mode
        assert re.fullmatch(r'[0-9a-f]{40}', oid), 'Unexpected tracked object identity'
        tracked_objects[path] = oid
    # --others deliberately includes ignored files; .gitignore cannot hide a
    # new proof, target, workflow, interpreter cache or arbitrary public blob.
    untracked = nul_paths(git('ls-files', '-z', '--others'))
    dependencies, git_roots = dependency_inventory()
    fingerprints = runtime_fingerprints(dependencies)
    physical = set()
    for directory, directories, files in os.walk(ROOT, followlinks=False):
        for name in list(directories):
            child = pathlib.Path(directory) / name
            path = child.relative_to(ROOT).as_posix()
            if path == '.git' or path in git_roots:
                directories.remove(name)
            elif path in dependencies and child.is_symlink():
                # Exact pinned dependency symlink already checked without following.
                directories.remove(name)
            else:
                assert not child.is_symlink(), f'Symlinked public directory: {path}'
                assert name != '__pycache__', f'Interpreter cache forbidden: {path}'
        for name in files:
            path = (pathlib.Path(directory) / name).relative_to(ROOT).as_posix()
            if path == '.git' or path in git_roots:
                continue
            if path in dependencies:
                continue
            if path in fingerprints or generated_build_path(path):
                assert stat.S_ISREG((ROOT / path).lstat().st_mode), f'Non-regular runtime file: {path}'
            else:
                physical.add(path)
    check_inventory_sets(set(tracked_modes), untracked, physical, dependencies, git_roots, fingerprints)
    baseline = baseline_sources()
    for path in public_paths():
        wanted = baseline[path][0] if path in baseline else '100644'
        if path in tracked_modes:
            assert tracked_modes[path] == wanted, f'Tracked executable-mode drift: {path}'
            data = (ROOT / path).read_bytes()
            identity = git_blob_identity(data)
            assert identity == tracked_objects[path], f'Index/physical blob mismatch: {path}'
        check_mode(path, (ROOT / path).lstat().st_mode, wanted)


def check_public_paths(actual: set[str]) -> None:
    expected = public_paths()
    assert actual == expected, ('Unexpected/missing exact release public path', sorted(actual ^ expected))


def check_physical_lean(actual: set[str]) -> None:
    assert actual == {path for path in public_paths() if path.endswith('.lean')}, 'Physical proof inventory drift'


def check_mode(path: str, actual_mode: int, wanted: str) -> None:
    assert stat.S_ISREG(actual_mode), f'Non-regular/symlink public path: {path}'
    assert bool(actual_mode & 0o111) == (wanted == '100755'), f'Public executable-mode drift: {path}'


def check_modes() -> None:
    baseline = baseline_sources()
    for path in public_paths():
        mode = baseline[path][0] if path in baseline else '100644'
        check_mode(path, (ROOT / path).lstat().st_mode, mode)


def install_c2_inventory_adapter(namespace: dict) -> None:
    assert '_metric_velocity_release_original_expected_sources' not in namespace, 'Duplicate inventory adapter installation'
    assert '_metric_velocity_release_original_check_workflow' not in namespace, 'Duplicate workflow adapter installation'
    original_expected = namespace['expected_sources']
    original_check_workflow = namespace['check_workflow']
    original_editable = set(namespace['EDITABLE'])
    original_added = set(namespace['ADDED'])
    assert original_added == {
        'curvature/scripts/point4_c2_initial_heat_source_test.py',
        'curvature/scripts/point4_c2_initial_heat_mock_test.py',
        '.github/workflows/point4-c2-initial-heat.yml',
        'docs/point4/c2-initial-heat-integration.md',
    }, 'Inherited C2 additions changed'
    assert original_editable == {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml',
                                 'docs/status.md', 'docs/point4/README.md'}, 'Inherited C2 edit scope changed'
    def full_expected_sources():
        # Execute the unchanged legacy reconstruction before admitting this unit.
        legacy = original_expected()
        baseline = baseline_sources()
        assert set(legacy) == set(baseline) - original_editable - original_added, 'Inherited exact union drift'
        for path, (_, data) in legacy.items():
            assert data == baseline[path][1], f'Inherited reconstruction no longer matches master: {path}'
        return expected_sources()
    def startup_checked_workflow(actual: bytes):
        original = restored_startup_workflow('.github/workflows/point4-c2-initial-heat.yml', actual)
        original_check_workflow(original)
    namespace['_metric_velocity_release_original_expected_sources'] = original_expected
    namespace['_metric_velocity_release_original_check_workflow'] = original_check_workflow
    namespace['check_workflow'] = startup_checked_workflow
    namespace['expected_sources'] = full_expected_sources
    namespace['ADDED'] = original_added | SELF_PATHS
    # Import, provenance, axiom, type and audit functions are untouched. The
    # workflow wrapper checks one exact startup-only transform, then executes
    # the unchanged original validator on the reconstructed original bytes.


def c2_guard():
    return importlib.import_module('point4_c2_initial_heat_source_test')


def check_root_metadata(source: str) -> None:
    c2_guard().check_metadata(source)
    assert source.encode() == baseline_sources()['curvature/formalization.yaml'][1], 'Root metadata must stay byte-identical'


def main(argv=None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--schema', type=pathlib.Path)
    parser.add_argument('--probe-log', type=pathlib.Path)
    parser.add_argument('--axiom-dir', type=pathlib.Path)
    parser.add_argument('--audit-json', type=pathlib.Path)
    parser.add_argument('--audit-rc', type=int)
    args = parser.parse_args(argv)
    guard = c2_guard()
    expected = expected_sources()
    for path, (_, wanted) in expected.items():
        guard.check_equal(path, (ROOT / path).read_bytes(), wanted)
    check_inventory()
    check_source_closure()
    check_new_workflow((ROOT / WORKFLOW).read_bytes())
    check_root_metadata((ROOT / 'curvature/formalization.yaml').read_text())
    metadata = (ROOT / METADATA).read_text()
    check_new_metadata(metadata)
    inherited_args = []
    for option, value in (('--schema', args.schema), ('--axiom-dir', args.axiom_dir),
                          ('--audit-json', args.audit_json), ('--audit-rc', args.audit_rc)):
        if value is not None:
            inherited_args.extend([option, str(value)])
    # Every original optional evidence gate keeps its original parser and requirements.
    guard.main(inherited_args)
    if args.schema:
        import jsonschema
        schema = args.schema.read_bytes()
        assert sha256(schema) == guard.SCHEMA_SHA256, 'Full official schema identity changed'
        jsonschema.validate(guard.parse_metadata(metadata), json.loads(schema))
    if args.probe_log:
        check_new_probe(args.probe_log.read_text())
    print(json.dumps({'baseline': BASE, 'public_paths': len(public_paths()),
                      'inherited_files_byte_identical': len(baseline_sources()) - 4,
                      'exact_inherited_guard_adapters': 1,
                      'exact_startup_workflow_adapters': len(STARTUP_WORKFLOWS),
                      'actual_source_modules': len(MODULES), 'historical_reviewed_source_snapshot': 'frozen-003',
                      'active_proof_repair': 'five-reversible-gaussian-elaboration-fragments',
                      'inherited_closure_matches_master': 59,
                      'root_imports_and_metadata_byte_identical': True,
                      'lean_verified': False, 'point4': 'OPEN'}, indent=2))
    print('Source-only release checks passed; exact Lean 4.33/db584 module/probe/full-build/kernel gates remain separate')


# BEGIN exact finite incoming-leaf-134
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == 'c82ce9939d310076d1b40ce72017e05a20ee22db12ce332a61537a4f8e77f264', "Incoming composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
_curvature_comp.install_curvature_leaf(globals(),134)
# END exact finite incoming-leaf-134

if __name__ == '__main__':
    main()
