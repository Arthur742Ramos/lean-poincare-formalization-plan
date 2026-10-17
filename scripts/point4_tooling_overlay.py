"""Authenticate a finite tooling addition over an unchanged proof-source commit.

This admits Source, not native proofs, cache hits, workflow results or a merge.
Legacy validators authenticate and execute on the actual admitted tooling HEAD.
"""
from __future__ import annotations

import argparse
import sys
import types
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess

BASE_HEAD = '5d1b3e2c123a8bdfd036a0e4d8495586c4a6d1b9'
BASE_TREE = '8081325e22bc0314d6106a311f92606e7e03f9d3'
SELF = 'scripts/point4_tooling_overlay.py'
ADDITIONS = {'.github/actions/point4-consolidated-cache/action.yml': {'mode': '100644', 'blob': '8546fa5a597bb9fd7a44a533f70668202f37499d', 'sha256': '64167c0ef61567921a4d8acdaf9dd1563d68ad1b737ecc8d64cec8b5b9bce428', 'bytes': 4274}, '.github/workflows/point4-consolidated.yml': {'mode': '100644', 'blob': '266fad5ef76da95e030db57f3fc3c7ac2738b8ed', 'sha256': '59f65182b78bfdfddad7dc46e3f3590dec047fb5307c36962d019c32aadeacfd', 'bytes': 9232}, 'scripts/point4_cache/point4_ci_cache.py': {'mode': '100644', 'blob': 'e5264f269d4897ebaaaf8b61ee65d1c0ce90842c', 'sha256': '76bc96b7b03b71e2a24321b2e4973870fbcf0711b15a7ed8a19abe104c2b438f', 'bytes': 21594}, 'scripts/point4_cache/point4_ci_cache_test.py': {'mode': '100644', 'blob': '3a46c4e50dbb5014c80b104f962ac48ea196339a', 'sha256': '773ab8e1fc05071528877d825dec8a130de391b0cdb71a5070f6a529a8752635', 'bytes': 19650}, 'scripts/point4_ci/command_broker.py': {'mode': '100755', 'blob': '1949b4e6d19047ea0dce2144a0e2b5b806c599e2', 'sha256': 'fd249c9782b5d1c9eee39c91783386a0280926725f7937c23ddf2eb4f27bc2a2', 'bytes': 12012}, 'scripts/point4_ci/identity.py': {'mode': '100644', 'blob': '906808a44e8f9161b88350113f84e2a1af15a85f', 'sha256': '8816ff5f2043db8390a85bd044527d71b1e1081739bced5f2a693b55327d8c24', 'bytes': 21981}, 'scripts/point4_ci/plan.json': {'mode': '100644', 'blob': 'adbd3c0f6f9b990f779f148e2567e7bbb862eedb', 'sha256': '5f37653d2dfec219146f6f2412dd88e393d05c2e7a1ef6a2b6aa52e32cb03eff', 'bytes': 330175}, 'scripts/point4_ci/runner.py': {'mode': '100644', 'blob': '447d6e745ebb8da4b438d9b7727d127468f726c4', 'sha256': '1e84a0e9537266eb5009f326fe7b1612e6749558f17b6e7a530533532fa1b6d8', 'bytes': 82244}, 'scripts/point4_ci/test_runner.py': {'mode': '100644', 'blob': 'fa3d2fca675c399aa74e7139e1f9c3ff1269a55d', 'sha256': '5bff32ae91c28d1a056c691df00d5b6d58d53e7db3db630b01ad0ece3f166ece', 'bytes': 62229}, 'scripts/point4_tooling_overlay_test.py': {'mode': '100644', 'blob': '3ef016f62dde5cb444e3990eb7bd5de32a1b140d', 'sha256': 'ed25945ea77bef4085ae7ee4ea193af1b3c33163448fae0f21c923f60db432a9', 'bytes': 38213}}
POLICY_SHA256 = '658eec8bd5b388d01ccf18ee70aed483afeb4c70547ee03cf18d099f900d8a9d'
TRANSPORT_PATH = '.github/workflows/point4-hamilton-release-audit.yml'
TRANSPORT = {'before_blob': 'd01da7fcde04da7f1988ca5076afbe45f59dc89a', 'before_sha256': '1d8849f98be74899334bedc94ed68c46b1270c420e9454f66a27d28e791d4c2d', 'after_blob': '829d120c7906035d9143a35935731d0b592fd617', 'after_sha256': '6f8bd895146f718953e1d47b089d4d6e11aaf9d424bee9e727f3a54972162311', 'after_bytes': 15305, 'ports': [['  workflow_dispatch:\n', '  workflow_dispatch:\n    inputs:\n      consolidated_tooling:\n        description: Run the separate consolidated tooling validation instead of upstream Hamilton work\n        type: boolean\n        required: false\n        default: false\n'], ['  upstream-checkpoint:\n', "  upstream-checkpoint:\n    if: ${{ !(github.event_name == 'workflow_dispatch' && inputs.consolidated_tooling) }}\n"]], 'append_exact': "\n  consolidated-tooling:\n    if: ${{ github.event_name == 'workflow_dispatch' && inputs.consolidated_tooling }}\n    uses: ./.github/workflows/point4-consolidated.yml\n"}
TRANSPORT_POLICY_SHA256 = 'ce2dd1d5b77d8a594e57c6b963140607b0b2d352a0858083f38243a4e4246dc6'
TRANSPORT_REQUIRED_PORTS = [['  workflow_dispatch:\n', '  workflow_dispatch:\n    inputs:\n      consolidated_tooling:\n        description: Run the separate consolidated tooling validation instead of upstream Hamilton work\n        type: boolean\n        required: false\n        default: false\n'], ['  upstream-checkpoint:\n', "  upstream-checkpoint:\n    if: ${{ !(github.event_name == 'workflow_dispatch' && inputs.consolidated_tooling) }}\n"]]
TRANSPORT_REQUIRED_APPEND = "\n  consolidated-tooling:\n    if: ${{ github.event_name == 'workflow_dispatch' && inputs.consolidated_tooling }}\n    uses: ./.github/workflows/point4-consolidated.yml\n"
OTHER_PATHS = frozenset({
    '.github/workflows/point4-consolidated.yml',
    '.github/actions/point4-consolidated-cache/action.yml',
    'scripts/point4_cache/point4_ci_cache.py',
    'scripts/point4_cache/point4_ci_cache_test.py',
    'scripts/point4_ci/runner.py',
    'scripts/point4_ci/command_broker.py',
    'scripts/point4_ci/identity.py',
    'scripts/point4_ci/plan.json',
    'scripts/point4_ci/test_runner.py',
    'scripts/point4_tooling_overlay_test.py',
})
LEGACY_HELPER = 'curvature/scripts/point4_smooth_master_composition.py'
LEGACY_TEST = 'curvature/scripts/point4_smooth_master_composition_test.py'
LEGACY_MAP = 'docs/point4/smooth-master-composition/identity-map.json'
LEGACY_PATHS = frozenset(('curvature/scripts/chart_port_candidate_check.py', 'curvature/scripts/point4_c2_c0_metric_velocity_mock_test.py', 'curvature/scripts/point4_c2_c0_metric_velocity_source_guard.py', 'curvature/scripts/point4_c2_metric_localization_source_test.py', 'curvature/scripts/point4_c2_resonance_guard.py', 'curvature/scripts/point4_c2_resonance_mock_test.py', 'curvature/scripts/point4_hamilton_native_mock_test.py', 'curvature/scripts/point4_hamilton_native_source_guard.py', 'curvature/scripts/point4_pr130_pr133_inventory.py', 'curvature/scripts/point4_smooth_forward_release_guard.py', 'curvature/scripts/point4_smooth_forward_release_mock_test.py', 'curvature/scripts/point4_smooth_master_composition.py', 'curvature/scripts/point4_smooth_master_composition_test.py', 'curvature/scripts/point4_two_sided_heat_mock_test.py', 'curvature/scripts/point4_two_sided_heat_source_guard.py', 'curvature/scripts/point4_weighted_hessian_release_guard.py', 'docs/point4/smooth-master-composition/identity-map.json'))
LEGACY_REPLACEMENTS = {'curvature/scripts/chart_port_candidate_check.py': {'before_mode': '100644', 'before_blob': 'bcaf1bf09bdb8a5f7c43cbe0f8fc930cfa1669ec', 'before_sha256': 'af2da4a8ba5da829737ca4df58166a3cf7fd5cfd7779c6359ff7313663460745', 'before_bytes': 28627, 'mode': '100644', 'blob': '3f9835e886df969add0ccb3715814a650e8e2512', 'sha256': '843ac50cced8a3a21365a74be6581c82103a9d201af0eab8518bd9efe3023862', 'bytes': 28627}, 'curvature/scripts/point4_c2_c0_metric_velocity_mock_test.py': {'before_mode': '100644', 'before_blob': '1bd9abd4227885505f68b8ecaf6251d7ae142d95', 'before_sha256': 'c8649bd9364f45c58b2764f6100a505bea0614bad0c0a698451df2ab73a6975b', 'before_bytes': 66628, 'mode': '100644', 'blob': 'dbc1f049941d22775af4a297b58543046a2b2fb2', 'sha256': '81c8d56e7b313ec186e6672fcc8ce674159d026467003c7a13ced0e2f49edf45', 'bytes': 66628}, 'curvature/scripts/point4_c2_c0_metric_velocity_source_guard.py': {'before_mode': '100644', 'before_blob': '4261020e7f14c0058bb9fceeeca7107ef7692889', 'before_sha256': '40dc7950d73110952c7023faa3650af48bda13d41846f488e520c5f6448cad2b', 'before_bytes': 67078, 'mode': '100644', 'blob': '07b1648aa5b5761c9a5e44c47a366d646fb69cfb', 'sha256': '4bb34f9bb3613347f9c5b9e22bfb17e50b7526b427ac522f73a3ea739c085cc8', 'bytes': 67143}, 'curvature/scripts/point4_c2_metric_localization_source_test.py': {'before_mode': '100644', 'before_blob': '3668da4dae065e8292a6e2f7ece62e1e453fe2b7', 'before_sha256': 'de9020cb6272a30ccd0b29c332773cc50c62ce545ad6b53251c1a96f6187a5a2', 'before_bytes': 16625, 'mode': '100644', 'blob': '34e3597b351a394ba240cc45fb4b95cf6859f07d', 'sha256': '7c35f5362cfcc0900ade2fc2a4b15addd25705e5a337bb1b4fced35c9172b4c8', 'bytes': 16625}, 'curvature/scripts/point4_c2_resonance_guard.py': {'before_mode': '100644', 'before_blob': 'e332b7c59b9acae820090567ee3c77866bd37606', 'before_sha256': 'c38816ca7efff894d5607111befe7c5708e306cd7cae8778e9aea6f2550fe70d', 'before_bytes': 8307, 'mode': '100644', 'blob': '842f7b0f97a8deeb925bab0ce26557ea1f982821', 'sha256': 'fd695d36967b5b963e665deb0003a5b5c08ab4ff6b6a8aa3bb371eeeedb1309c', 'bytes': 8307}, 'curvature/scripts/point4_c2_resonance_mock_test.py': {'before_mode': '100644', 'before_blob': 'a9d22154674ee7967c08bb3ef4f7547e99d2549c', 'before_sha256': '1c221d6bced1030c42586639904fe07e6ea5d1ccc9d59ed19bc92f9634a94507', 'before_bytes': 14834, 'mode': '100644', 'blob': '94aca8eac610c12ff4afe045ccaed7e3b6c26c3a', 'sha256': '1a475d35fefdc54e96690df73bc1ab4ffe3fcd1e63e76d161aeaf4d08bf7d128', 'bytes': 14834}, 'curvature/scripts/point4_hamilton_native_mock_test.py': {'before_mode': '100644', 'before_blob': 'ae6f7ffbc58904641f1be036c0b32e9f33dc3903', 'before_sha256': '810188062b04ad4cdd2ded51fbb05d69bdc5431cbb2ec46af8e1553a9740a8b7', 'before_bytes': 30642, 'mode': '100644', 'blob': 'cf735d3640f80f66f6bf5a332abe13c1a2621ffa', 'sha256': '0e8762e226bf6e7a6c81495d68d76ae877446b87b7795cf965a7628ecab7a5b4', 'bytes': 30642}, 'curvature/scripts/point4_hamilton_native_source_guard.py': {'before_mode': '100644', 'before_blob': '7bc8d8f39d00604668214aad8ab27080e17fe6c4', 'before_sha256': 'acd9c72ee8a2a05d35cb58fcfbe38310fdd197d684bc0390229b6b4c411798bc', 'before_bytes': 28316, 'mode': '100644', 'blob': '86499f7379cf9a3fa788496ddcf9efe9152bd486', 'sha256': '4ad9605c1c021cf29de34ac7056c1beb62f2eefd00391c917eaa0c0b56ce1abd', 'bytes': 28381}, 'curvature/scripts/point4_pr130_pr133_inventory.py': {'before_mode': '100644', 'before_blob': '2face411bfc349e8b9219322d663da4f5a7e7312', 'before_sha256': '459a0c2eeecf7d322a38bfe67a8534a49ea403c81d8a3b72000b54f963750d5b', 'before_bytes': 5889, 'mode': '100644', 'blob': 'f6ed29702e69179b5a95a96aa5b47b8010a577d0', 'sha256': '3f011f6504189612a740fa3a3f16da34772ed607ef5c0a8cc77f9367f3df4d26', 'bytes': 5889}, 'curvature/scripts/point4_smooth_forward_release_guard.py': {'before_mode': '100644', 'before_blob': 'be8f1d07e5a5150c1fae8eab16dc45891b975146', 'before_sha256': '905605cebcdac0ab5c6374a62a2c88cce13db1d2659be9f8abfb431802000f66', 'before_bytes': 17859, 'mode': '100644', 'blob': 'd1a3fce8f3aaff6a68f9ff12c2bf68fea81ece7c', 'sha256': '40040cfd0513f18c236b969c3114e6c3232fa5a7cfecc64ac013b970aa138f75', 'bytes': 17859}, 'curvature/scripts/point4_smooth_forward_release_mock_test.py': {'before_mode': '100644', 'before_blob': '0e403b24f4c0b4c43e8988a44f07d88dc404d40f', 'before_sha256': '48c0979f9b20a5c68bdd86909b11177109c0c28cab9c8fdb22a25c9086ea8194', 'before_bytes': 28729, 'mode': '100644', 'blob': '058327caddaf9963b4dd9e12ea22deb9aa10a67c', 'sha256': 'd77268e52178d4214424e8b08888a3317a83376bf29c8ccf69ba04568cc579ce', 'bytes': 28729}, 'curvature/scripts/point4_smooth_master_composition.py': {'before_mode': '100644', 'before_blob': 'c347bdb143bcc69754d62e005d949ee3a6a3aea1', 'before_sha256': '62aa047cdd4ab15f99bb11552227ab26a28b5f871b1597340397df8b20fd9a84', 'before_bytes': 2842318, 'mode': '100644', 'blob': 'd7c4262b1e504db73c30636940ca3944e94b05de', 'sha256': '6df3dedfd2a69e39891cfd666fa8be5f064ded4d44ce3e65e898d1f6fcd26540', 'bytes': 2949180}, 'curvature/scripts/point4_smooth_master_composition_test.py': {'before_mode': '100644', 'before_blob': '7378991ea40d6d86abddaaa70d3ebfe0fe82f5cb', 'before_sha256': '7d14b99e3ba176586a7171df983d83505f92fb4e33693bf2e93fa7da8e4c7b12', 'before_bytes': 299624, 'mode': '100644', 'blob': 'caf6c2bc73d681a01eba1b086b0f8009b76361a0', 'sha256': '9b18ac296270e48b18ce3a70a0532f2ebeacd4cd0f6a432904ca2da2ea620be0', 'bytes': 299848}, 'curvature/scripts/point4_two_sided_heat_mock_test.py': {'before_mode': '100644', 'before_blob': 'f038e96f9299beefb2b04f87bfc188b549992a28', 'before_sha256': 'fea88014d6760734a191585789b3abbe6838d7323bb16dbafc266e45caf296c6', 'before_bytes': 84846, 'mode': '100644', 'blob': '4f8b064e728c855cc0834231f43f2470364a7dc3', 'sha256': 'd1d2dcd934b350c2770ca602f762ad6373f884aaae2176396cdd301f5085b21b', 'bytes': 84846}, 'curvature/scripts/point4_two_sided_heat_source_guard.py': {'before_mode': '100644', 'before_blob': '703dd6c7d86b5e128cfff64db8638bf82cb86e8d', 'before_sha256': 'ebef0d1734d3b02961763bbd0b093412ce6ee4f4136579f27c815f7be54e2c85', 'before_bytes': 55477, 'mode': '100644', 'blob': 'b14c90d2aead0afb969b0981a9b7ae0d76e51974', 'sha256': '5f863359719e7f3ab9df78e862ab8dc25ea2180c6d66df1c7a5196c43d053f5a', 'bytes': 55542}, 'curvature/scripts/point4_weighted_hessian_release_guard.py': {'before_mode': '100644', 'before_blob': '76bd462918cde021f9f43cc3875998719e2d5cb6', 'before_sha256': '676def9ff5da9f739eb8662a2ed14aeb0fff86aceabbe05ee7006b616dc33e06', 'before_bytes': 55524, 'mode': '100644', 'blob': 'fdd5f18980b3809253d8c9e5bb9d48a2869e09ee', 'sha256': '912adc0718aee60ecfcf5a681172ca69d0b9787c186c978f92b69ceb3550e51e', 'bytes': 55654}}
LEGACY_POLICY_SHA256 = '5220ab9193e808e0b7da30dd626e8e833dd5ac5e6009fb7fa78ba23dc9f2e369'
MAX_FILE_BYTES = 8 * 1024 * 1024
MAX_SOURCE_BYTES = 128 * 1024 * 1024
MAX_GIT_BYTES = 4 * 1024 * 1024


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def blob_id(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def regular_bytes(path, maximum=MAX_FILE_BYTES):
    path = Path(path)
    require(path.is_absolute(), 'Absolute tooling input required')
    for parent in path.parents:
        info = parent.lstat()
        require(stat.S_ISDIR(info.st_mode) and not getattr(info, 'st_file_attributes', 0) & 1024,
                'Nonreal tooling input parent')
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and not getattr(before, 'st_file_attributes', 0) & 1024,
            'Nonregular tooling input')
    require(0 <= before.st_size <= maximum, 'Tooling input byte cap')
    def sticky(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    with path.open('rb') as handle:
        require(sticky(os.fstat(handle.fileno())) == sticky(before), 'Tooling open drift')
        raw = handle.read(maximum + 1)
        require(sticky(os.fstat(handle.fileno())) == sticky(before), 'Tooling read drift')
    require(len(raw) == before.st_size and sticky(path.lstat()) == sticky(before), 'Tooling input POST drift')
    return raw


def git(root, *args):
    for name in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_OBJECT_DIRECTORY',
                 'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_REPLACE_REF_BASE'):
        require(not os.environ.get(name), 'Git environment override forbidden: ' + name)
    env = dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')
    result = subprocess.run(['git', '--no-replace-objects', '-c', 'core.fsmonitor=false',
                             '-C', str(root), *args], env=env, check=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    require(len(result.stdout) <= MAX_GIT_BYTES and len(result.stderr) <= MAX_GIT_BYTES,
            'Git metadata byte cap')
    return result.stdout


def parse_tree(raw):
    require(bool(raw) and raw.endswith(b'\0'), 'Incomplete native Git tree')
    rows = {}
    for entry in raw.split(b'\0')[:-1]:
        descriptor, name = entry.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = name.decode('utf8')
        parts = PurePosixPath(path).parts
        require(mode in ('100644', '100755') and kind == 'blob' and re.fullmatch('[0-9a-f]{40}', oid),
                'Unsupported native Source entry')
        require(parts and '/'.join(parts) == path and not path.startswith('/') and all(p not in ('', '.', '..') for p in parts)
                and '\\' not in path and path not in rows, 'Unsafe/duplicate native Source path')
        rows[path] = (mode, oid)
    require(len(rows) == len({p.casefold() for p in rows}), 'Native Source case alias')
    return rows


def policy():
    require(type(ADDITIONS) is dict and set(ADDITIONS) == OTHER_PATHS, 'Unfrozen tooling policy')
    require(sha256(canonical(ADDITIONS)) == POLICY_SHA256, 'Finite tooling policy mutation')
    require(len(OTHER_PATHS) == 10 and SELF not in OTHER_PATHS, 'Tooling path policy drift')
    rows = {}
    for path, row in ADDITIONS.items():
        require(not path.endswith('.lean') and type(row) is dict
                and set(row) == {'mode', 'blob', 'sha256', 'bytes'}, 'Invalid tooling row')
        wanted_mode = '100755' if path == 'scripts/point4_ci/command_broker.py' else '100644'
        require(row['mode'] == wanted_mode and re.fullmatch('[0-9a-f]{40}', row['blob'])
                and re.fullmatch('[0-9a-f]{64}', row['sha256']), 'Invalid tooling mode/digest')
        require(type(row['bytes']) is int and 0 < row['bytes'] <= MAX_FILE_BYTES, 'Invalid tooling byte count')
        rows[path] = dict(row)
    return rows


def transport_policy():
    require(type(TRANSPORT) is dict and set(TRANSPORT) == {
        'before_blob', 'before_sha256', 'after_blob', 'after_sha256', 'after_bytes', 'ports', 'append_exact'},
        'Unfrozen finite dispatch transport policy')
    require(sha256(canonical(TRANSPORT)) == TRANSPORT_POLICY_SHA256, 'Dispatch transport policy mutation')
    for key in ('before_blob', 'after_blob'):
        require(re.fullmatch('[0-9a-f]{40}', TRANSPORT[key]), 'Invalid dispatch transport blob')
    for key in ('before_sha256', 'after_sha256'):
        require(re.fullmatch('[0-9a-f]{64}', TRANSPORT[key]), 'Invalid dispatch transport SHA')
    require(type(TRANSPORT['after_bytes']) is int and 0 < TRANSPORT['after_bytes'] <= MAX_FILE_BYTES,
            'Invalid dispatch transport byte count')
    require(type(TRANSPORT['ports']) is list and 0 < len(TRANSPORT['ports']) <= 10,
            'Finite dispatch transport ports required')
    require(TRANSPORT['ports'] == TRANSPORT_REQUIRED_PORTS
            and TRANSPORT['append_exact'] == TRANSPORT_REQUIRED_APPEND,
            'Dispatch default/mode/append behavior differs from exact reviewed transport')
    for port in TRANSPORT['ports']:
        require(type(port) is list and len(port) == 2 and all(type(v) is str and v for v in port)
                and port[0] != port[1], 'Invalid dispatch transport port')
    return json.loads(json.dumps(TRANSPORT))


def transport_inverse(current_raw, previous_raw, transport):
    require(blob_id(previous_raw) == transport['before_blob']
            and sha256(previous_raw) == transport['before_sha256'], 'Whole original dispatch Source drift')
    require(blob_id(current_raw) == transport['after_blob']
            and sha256(current_raw) == transport['after_sha256']
            and len(current_raw) == transport['after_bytes'], 'Whole current dispatch Source drift')
    restored = current_raw.decode('utf8')
    appended = transport['append_exact']
    require(restored.endswith(appended) and restored.count(appended) == 1, 'Dispatch exact append drift')
    restored = restored[:-len(appended)]
    for before, after in reversed(transport['ports']):
        require(restored.count(after) == 1, 'Dispatch inverse port missing/duplicate')
        restored = restored.replace(after, before, 1)
    require(restored.encode() == previous_raw, 'Whole dispatch Source inverse drift')
    for before, after in transport['ports']:
        require(restored.count(before) == 1, 'Dispatch forward port missing/duplicate')
        restored = restored.replace(before, after, 1)
    require((restored + appended).encode() == current_raw, 'Whole dispatch Source forward drift')
    return previous_raw




def legacy_policy():
    require(type(LEGACY_REPLACEMENTS) is dict and set(LEGACY_REPLACEMENTS) == LEGACY_PATHS - {LEGACY_MAP},
            'Unfrozen exact legacy epoch replacement policy')
    require(sha256(canonical(LEGACY_REPLACEMENTS)) == LEGACY_POLICY_SHA256,
            'Finite legacy epoch replacement policy mutation')
    require(len(LEGACY_PATHS) == 17 and LEGACY_HELPER in LEGACY_PATHS and LEGACY_TEST in LEGACY_PATHS,
            'Legacy epoch path set drift')
    rows = {}
    for path, row in LEGACY_REPLACEMENTS.items():
        require(not path.endswith('.lean') and type(row) is dict and set(row) == {
            'before_mode', 'before_blob', 'before_sha256', 'before_bytes',
            'mode', 'blob', 'sha256', 'bytes'}, 'Invalid exact legacy epoch row')
        require(row['before_mode'] == row['mode'] == '100644', 'Legacy epoch mode drift')
        for key in ('before_blob', 'blob'):
            require(re.fullmatch('[0-9a-f]{40}', row[key]), 'Invalid legacy epoch native blob')
        for key in ('before_sha256', 'sha256'):
            require(re.fullmatch('[0-9a-f]{64}', row[key]), 'Invalid legacy epoch SHA')
        for key in ('before_bytes', 'bytes'):
            require(type(row[key]) is int and 0 < row[key] <= MAX_FILE_BYTES, 'Legacy epoch byte cap')
        rows[path] = dict(row)
    return rows

def verify_legacy_epoch(root, expected_head, expected, additions, transport, legacy):
    """Run the authenticated original current verifier on this real checkout.

    MAP has its established committed-HEAD self entry. Its complete contents
    must equal the original derived tensor_map_record inside verify_current;
    neither MAP nor overlay SELF is exempted from native/index/physical checks.
    H never calls this overlay, so there is no recursive verifier dependency.
    """
    name = 'point4_smooth_master_composition'
    require(name not in sys.modules, 'Foreign/preloaded legacy epoch helper')
    source = root / LEGACY_HELPER
    raw = regular_bytes(source)
    require(sha256(raw) == legacy[LEGACY_HELPER]['sha256']
            and blob_id(raw) == legacy[LEGACY_HELPER]['blob'], 'Legacy helper import seal drift')
    previous_path = list(sys.path)
    previous_modules = set(sys.modules)
    sys.path.insert(0, str(root / 'curvature/scripts'))
    module = None
    try:
        module = types.ModuleType(name)
        module.__file__ = str(source)
        module.__package__ = None
        sys.modules[name] = module
        # Compile only the exact authenticated physical Source above; never
        # consult or create Python bytecode files in the Source checkout.
        exec(compile(raw, str(source), 'exec', dont_inherit=True), module.__dict__)
        require(Path(module.__file__).resolve() == source and module.ROOT == root,
                'Legacy helper execution root drift')
        require(module.CURVATURE_TOOLING_POLICY['additions'] == additions
                and module.CURVATURE_TOOLING_POLICY['transport'] == transport
                and module.CURVATURE_TOOLING_POLICY['self_path'] == SELF,
                'Legacy epoch/coordinator finite policy mismatch')
        original_helper = git(root, 'show', BASE_HEAD + ':' + LEGACY_HELPER)
        original_test = git(root, 'show', BASE_HEAD + ':' + LEGACY_TEST)
        require(module.curvature_tooling_helper_inverse(raw) == original_helper
                and module.curvature_tooling_test_inverse(regular_bytes(root / LEGACY_TEST)) == original_test,
                'Whole legacy helper/test predecessor inverse drift')
        require(git(root, 'rev-parse', 'HEAD').decode().strip() == expected_head,
                'Actual legacy epoch HEAD drift')
        require(module.verify_current() == expected, 'Original complete current legacy epoch identity differs')
        require(regular_bytes(source) == raw and legacy_policy() == legacy,
                'Legacy epoch Source/policy POST drift')
        return {'actual_current_head': expected_head, 'source_paths': len(expected),
                'full_original_current_verifier_executed': True,
                'full_derived_MAP_equality_and_native_binding': True,
                'helper_and_test_whole_predecessor_inverses': True,
                'policy_sha256': LEGACY_POLICY_SHA256}
    finally:
        sys.path[:] = previous_path
        # Remove only modules introduced by this owned import whose exact
        # source resides in this checkout. A later admission runs fresh full
        # predicates; this is no cached PASS or mutable foreign H namespace.
        for imported_name in tuple(set(sys.modules) - previous_modules):
            imported = sys.modules.get(imported_name)
            location = getattr(imported, '__file__', None)
            if type(location) is str and Path(location).is_absolute() and Path(location).is_relative_to(root):
                del sys.modules[imported_name]

def expected_tree(base, current, additions, transport, legacy=None):
    """Exact finite epoch over the unchanged Lean/proof-source baseline."""
    legacy = legacy_policy() if legacy is None else legacy
    require(type(base) is dict and len(base) == 2185, 'Baseline Source count drift')
    require(set(legacy) == LEGACY_PATHS - {LEGACY_MAP} and LEGACY_PATHS <= set(base),
            'Exact legacy epoch replacement paths differ')
    require(set(additions) == OTHER_PATHS and not (set(base) & (OTHER_PATHS | {SELF})),
            'Tooling/base path overlap')
    require(not ({p.casefold() for p in base} & {p.casefold() for p in OTHER_PATHS | {SELF}}),
            'Tooling/base path alias')
    require(SELF in current and current[SELF][0] == '100644', 'Current tracked overlay helper missing')
    require(base.get(TRANSPORT_PATH) == ('100644', transport['before_blob']), 'Original dispatch entry drift')
    expected = dict(base)
    expected[TRANSPORT_PATH] = ('100644', transport['after_blob'])
    for path, row in legacy.items():
        require(base[path] == (row['before_mode'], row['before_blob']), 'Original exact legacy row drift: ' + path)
        expected[path] = row['mode'], row['blob']
    require(LEGACY_MAP in current and current[LEGACY_MAP][0] == '100644', 'Committed descriptive MAP missing')
    # The sole MAP self placeholder is independently checked by the original
    # complete derived-MAP oracle before this admission can return success.
    expected[LEGACY_MAP] = current[LEGACY_MAP]
    for path, row in additions.items():
        expected[path] = row['mode'], row['blob']
    expected[SELF] = current[SELF]
    require(len(expected) == 2196 and current == expected,
            'Unknown tracked addition/deletion/proof/legacy Source/mode change')
    return expected


def verify_tooling_overlay(expected_head, root=None):
    root = Path(root) if root is not None else Path(__file__).absolute().parents[1]
    require(root.is_absolute() and root == root.resolve(), 'Canonical tooling root required')
    require(re.fullmatch('[0-9a-f]{40}', expected_head or ''), 'External tooling commit required')
    require(git(root, 'rev-parse', 'HEAD').decode().strip() == expected_head, 'Tooling HEAD drift')
    require(git(root, 'rev-parse', BASE_HEAD + '^{tree}').decode().strip() == BASE_TREE,
            'Exact baseline tree drift')
    base = parse_tree(git(root, 'ls-tree', '-rz', BASE_HEAD))
    current_raw = git(root, 'ls-tree', '-rz', 'HEAD')
    current = parse_tree(current_raw)
    additions = policy()
    transport = transport_policy()
    legacy = legacy_policy()
    expected = expected_tree(base, current, additions, transport, legacy)
    for path, row in legacy.items():
        previous = git(root, 'show', BASE_HEAD + ':' + path)
        require(len(previous) == row['before_bytes'] and sha256(previous) == row['before_sha256'],
                'Original legacy whole Source provenance drift: ' + path)
    transport_inverse(regular_bytes(root / TRANSPORT_PATH),
                      git(root, 'show', BASE_HEAD + ':' + TRANSPORT_PATH), transport)
    index_raw = git(root, 'ls-files', '--stage', '-z')
    require(index_raw.endswith(b'\0'), 'Incomplete current index')
    index = {}
    for entry in index_raw.split(b'\0')[:-1]:
        descriptor, name = entry.split(b'\t', 1)
        mode, oid, stage = descriptor.decode().split()
        path = name.decode('utf8')
        require(stage == '0' and path not in index, 'Unmerged/duplicate current index')
        index[path] = mode, oid
    require(index == expected, 'Complete tooling index differs from committed Source')
    total, seals = 0, {}
    for path, (mode, oid) in expected.items():
        raw = regular_bytes(root / path)
        info = (root / path).lstat()
        require(not info.st_mode & 0o7000 and bool(info.st_mode & 0o111) == (mode == '100755') and blob_id(raw) == oid,
                'Tooling physical mode/native blob drift: ' + path)
        total += len(raw)
        require(total <= MAX_SOURCE_BYTES, 'Complete Source aggregate exceeded')
        seals[path] = {'mode': mode, 'blob': oid, 'bytes': len(raw), 'sha256': sha256(raw)}
        if path in additions:
            require(seals[path] == additions[path], 'Tooling SHA/bytes row differs: ' + path)
        if path in legacy:
            require(seals[path] == {key: legacy[path][key] for key in ('mode', 'blob', 'bytes', 'sha256')},
                    'Exact legacy physical Source row differs: ' + path)
    # Tooling checkout is Source-only. Runtime outputs and dependencies belong
    # in the real detached execution worktree, under the unchanged legacy guards.
    require(not git(root, 'ls-files', '--others', '-z'), 'Untracked tooling input/output forbidden')
    legacy_actual = verify_legacy_epoch(root, expected_head, expected, additions, transport, legacy)
    for path, row in seals.items():
        raw = regular_bytes(root / path)
        require(len(raw) == row['bytes'] and sha256(raw) == row['sha256']
                and not (root / path).lstat().st_mode & 0o7000
                and bool((root / path).lstat().st_mode & 0o111) == (row['mode'] == '100755'),
                'Complete physical Source POST drift: ' + path)
    require(git(root, 'rev-parse', 'HEAD').decode().strip() == expected_head
            and git(root, 'ls-tree', '-rz', 'HEAD') == current_raw
            and git(root, 'ls-files', '--stage', '-z') == index_raw, 'Native Git Source POST drift')
    require(policy() == additions and transport_policy() == transport and legacy_policy() == legacy, 'Tooling policy POST drift')
    return {'schema': 'point4-finite-tooling-overlay-v1',
            'tooling_head': expected_head, 'tooling_tree': git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(),
            'execution_head': expected_head, 'execution_tree': git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(),
            'proof_base_head': BASE_HEAD, 'proof_base_tree': BASE_TREE,
            'source_paths': len(expected), 'source_bytes': total,
            'source_catalogue_sha256': sha256(canonical(seals)), 'tooling_additions': additions,
            'self_source': seals[SELF], 'base_sources_unchanged_except_exact_dispatch_transport': False,
            'base_sources_unchanged_except_exact_legacy_epoch_and_dispatch': True,
            'dispatch_transport': {'path': TRANSPORT_PATH, 'policy': transport},
            'all_lean_sources_unchanged': True, 'legacy_helper_and_map_unchanged': False,
            'legacy_epoch_complete_current_identity_verified': True, 'legacy_epoch_actual': legacy_actual,
            'index_and_physical_prepost': True, 'untracked_tooling_paths': 0,
            'required_execution_gate': 'Actual admitted tooling HEAD; original complete validators and native commands',
            'native_qualification': False, 'workflow_status_credit': False, 'point4': 'OPEN'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-sha', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    root = Path(__file__).absolute().parents[1]
    out = Path(args.output)
    require(out.is_absolute() and out.parent == out.parent.resolve() and not out.is_relative_to(root),
            'Fresh absolute output outside tooling worktree required')
    for parent in out.parents:
        require(stat.S_ISDIR(parent.lstat().st_mode), 'Nonreal output parent')
    result = verify_tooling_overlay(args.expected_sha, root)
    raw = canonical(result) + b'\n'
    require(len(raw) <= 1024 * 1024, 'Overlay receipt byte cap')
    fd = os.open(out, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as handle:
        handle.write(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
