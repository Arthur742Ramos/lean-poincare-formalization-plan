"""Authenticate a finite tooling addition over an unchanged proof-source commit.

This admits Source, not native proofs, cache hits, workflow results or a merge.
Legacy validators execute separately in a real detached baseline worktree.
"""
from __future__ import annotations

import argparse
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
ADDITIONS = {'.github/actions/point4-consolidated-cache/action.yml': {'mode': '100644', 'blob': '8546fa5a597bb9fd7a44a533f70668202f37499d', 'sha256': '64167c0ef61567921a4d8acdaf9dd1563d68ad1b737ecc8d64cec8b5b9bce428', 'bytes': 4274}, '.github/workflows/point4-consolidated.yml': {'mode': '100644', 'blob': '0b139c09406daed14dd45a1f8c1a55a1150e86b5', 'sha256': 'c5a23206926624b6a5008916c97e4d66b88c3fc223840a0191d58f1c5a81932c', 'bytes': 6582}, 'scripts/point4_cache/point4_ci_cache.py': {'mode': '100644', 'blob': 'e5264f269d4897ebaaaf8b61ee65d1c0ce90842c', 'sha256': '76bc96b7b03b71e2a24321b2e4973870fbcf0711b15a7ed8a19abe104c2b438f', 'bytes': 21594}, 'scripts/point4_cache/point4_ci_cache_test.py': {'mode': '100644', 'blob': '3a46c4e50dbb5014c80b104f962ac48ea196339a', 'sha256': '773ab8e1fc05071528877d825dec8a130de391b0cdb71a5070f6a529a8752635', 'bytes': 19650}, 'scripts/point4_ci/command_broker.py': {'mode': '100755', 'blob': '1949b4e6d19047ea0dce2144a0e2b5b806c599e2', 'sha256': 'fd249c9782b5d1c9eee39c91783386a0280926725f7937c23ddf2eb4f27bc2a2', 'bytes': 12012}, 'scripts/point4_ci/identity.py': {'mode': '100644', 'blob': '858ca4129030edbd9a319f213480a8d79861503e', 'sha256': '576b530f7c0a02765349257a60b263b8b60650991425b454602df4d5dcb106ac', 'bytes': 19500}, 'scripts/point4_ci/plan.json': {'mode': '100644', 'blob': '1e33782cf066a07f235ecd231bc7a021ce31acc8', 'sha256': '3a79299d0cdc34de98504f06ec65c7aedf662ac35f63a14a517bb71b363f5764', 'bytes': 251128}, 'scripts/point4_ci/runner.py': {'mode': '100644', 'blob': '79c3b9d1fef46c241e2ea7c14f8d64afa5e26d4b', 'sha256': 'd1fbceea2bfca1841e48fb8c6b5dcc8467213d07893e04aeb01c190dd517704b', 'bytes': 42162}, 'scripts/point4_ci/test_runner.py': {'mode': '100644', 'blob': 'e3d2e6368c90bdbc1857b37161656ee2f2279f80', 'sha256': 'ebf2a033054a5210377a49167f3cbf0e48b220531e6b1f8d519f42bc219869ec', 'bytes': 29710}, 'scripts/point4_tooling_overlay_test.py': {'mode': '100644', 'blob': '0ae8bc22578fda99bf86e9cef3baef49731a6e16', 'sha256': 'f5b09b04c3e69d452a08b99e23663fbffb9b4548eb56fa774b4800c2879d2252', 'bytes': 10967}}
POLICY_SHA256 = '26b615b4575c08fa504f2d81346ef234596951105d52f701549aee7d4a06bb72'
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


def expected_tree(base, current, additions, transport):
    """Only an exact reversible dispatch bridge may change existing Source."""
    require(type(base) is dict and len(base) == 2185, 'Baseline Source count drift')
    require(set(additions) == OTHER_PATHS and not (set(base) & (OTHER_PATHS | {SELF})),
            'Tooling/base path overlap')
    require(not ({p.casefold() for p in base} & {p.casefold() for p in OTHER_PATHS | {SELF}}),
            'Tooling/base path alias')
    require(SELF in current and current[SELF][0] == '100644', 'Current tracked overlay helper missing')
    require(base.get(TRANSPORT_PATH) == ('100644', transport['before_blob']), 'Original dispatch entry drift')
    expected = dict(base)
    expected[TRANSPORT_PATH] = ('100644', transport['after_blob'])
    for path, row in additions.items():
        expected[path] = row['mode'], row['blob']
    # As with other reviewed executable Source, the helper itself is bound to
    # the externally approved commit/native Git blob, avoiding self-hash cycles.
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
    expected = expected_tree(base, current, additions, transport)
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
    # Tooling checkout is Source-only. Runtime outputs and dependencies belong
    # in the real detached execution worktree, under the unchanged legacy guards.
    require(not git(root, 'ls-files', '--others', '-z'), 'Untracked tooling input/output forbidden')
    for path, row in seals.items():
        raw = regular_bytes(root / path)
        require(len(raw) == row['bytes'] and sha256(raw) == row['sha256']
                and not (root / path).lstat().st_mode & 0o7000
                and bool((root / path).lstat().st_mode & 0o111) == (row['mode'] == '100755'),
                'Complete physical Source POST drift: ' + path)
    require(git(root, 'rev-parse', 'HEAD').decode().strip() == expected_head
            and git(root, 'ls-tree', '-rz', 'HEAD') == current_raw
            and git(root, 'ls-files', '--stage', '-z') == index_raw, 'Native Git Source POST drift')
    require(policy() == additions and transport_policy() == transport, 'Tooling policy POST drift')
    return {'schema': 'point4-finite-tooling-overlay-v1',
            'tooling_head': expected_head, 'tooling_tree': git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(),
            'execution_head': BASE_HEAD, 'execution_tree': BASE_TREE,
            'source_paths': len(expected), 'source_bytes': total,
            'source_catalogue_sha256': sha256(canonical(seals)), 'tooling_additions': additions,
            'self_source': seals[SELF], 'base_sources_unchanged_except_exact_dispatch_transport': True,
            'dispatch_transport': {'path': TRANSPORT_PATH, 'policy': transport},
            'all_lean_sources_unchanged': True, 'legacy_helper_and_map_unchanged': True,
            'index_and_physical_prepost': True, 'untracked_tooling_paths': 0,
            'required_execution_gate': 'Real detached baseline worktree; original complete validators and native commands',
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
