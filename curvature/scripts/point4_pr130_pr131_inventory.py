#!/usr/bin/env python3
"""Exact two-parent source inventory; compiler evidence is a separate receipt."""
from __future__ import annotations
import hashlib
import importlib
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
REPAIR = '6cdbc00828607d80e180a9cffc0cc3376b3b7e42'
MASTER = 'a0132cd55e2540b2fd26adecea9a07b51f1b8292'
TREES = {REPAIR: 'b266849c61f0895a2a0e87e43baded4a7dcf2141',
         MASTER: '9401fcd8272746e77db182de22b394d8605f901a'}
SHARED_GUARD = 'curvature/scripts/point4_c2_initial_heat_source_test.py'
SHARED_DIFFERENCES = {SHARED_GUARD, 'curvature/PoincareCurvature.lean',
                      'curvature/formalization.yaml', 'docs/point4/README.md'}
ADDED = {'curvature/scripts/point4_pr130_pr131_inventory.py',
         'curvature/scripts/point4_pr130_pr131_inventory_test.py',
         'docs/point4/pr130-pr131-desktop-integration.md'}
ANCHOR = b"\nif __name__ == '__main__':\n    main()\n"
HOOK = b"\n# Exact reviewed-parent union; inherited evidence gate bodies remain unchanged.\nimport point4_pr130_pr131_inventory as _joint_inventory\n_joint_inventory.install_c2_inventory_adapter(globals())\n"
MASTER_GUARD_BLOB = 'e59e39c415c5e0344c9ad72936eb748618d85f37'

def git(*args: str, data: bytes | None = None) -> bytes:
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(ROOT),
                                    *args], input=data)

def blob_id(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def transform_shared_guard(original: bytes) -> bytes:
    assert blob_id(original) == MASTER_GUARD_BLOB, 'Exact master guard changed'
    assert original.count(ANCHOR) == 1 and HOOK not in original, 'Count-one adapter required'
    return original.replace(ANCHOR, HOOK + ANCHOR, 1)

def resolve_inventory(repair: dict, master: dict) -> dict:
    differences = {p for p in repair.keys() & master.keys() if repair[p] != master[p]}
    assert differences == SHARED_DIFFERENCES, 'Unexpected parent overlap'
    assert not ADDED & (repair.keys() | master.keys()), 'New adapter path collision'
    result = dict(master)
    result.update(repair)
    result[SHARED_GUARD] = master[SHARED_GUARD]
    return result

def tree(sha: str) -> dict:
    assert git('rev-parse', sha+'^{tree}').decode().strip() == TREES[sha]
    result = {}
    for record in git('ls-tree', '-rz', sha).split(b'\0'):
        if not record: continue
        info, path = record.split(b'\t'); mode, kind, digest = info.decode().split()
        assert kind == 'blob' and mode in {'100644', '100755'}
        result[path.decode()] = (mode, digest)
    return result

def validate_inventory(expected: dict, actual: dict) -> None:
    assert set(actual) == set(expected), 'Unexpected/missing public source path'
    assert all(actual[p] == expected[p] for p in expected), 'Source bytes/modes drift'

def public_paths(tracked: set, untracked: set) -> set:
    for p in tracked:
        assert not {'.lake', '.development', '__pycache__'} & set(pathlib.PurePosixPath(p).parts), 'Tracked cache forbidden'
        assert not p.endswith(('.pyc', '.olean', '.ilean')), 'Tracked artifact forbidden'
    return tracked | {p for p in untracked
                      if not ('__pycache__' in pathlib.PurePosixPath(p).parts and p.endswith('.pyc'))}

def expected_sources() -> dict:
    wanted = resolve_inventory(tree(REPAIR), tree(MASTER))
    raw_guard = git('cat-file', 'blob', MASTER_GUARD_BLOB)
    wanted[SHARED_GUARD] = ('100644', blob_id(transform_shared_guard(raw_guard)))
    actual = {}
    tracked = set(git('ls-files', '-z', '--cached').decode().split('\0')) - {''}
    untracked = set(git('ls-files', '-z', '--others', '--exclude-standard').decode().split('\0')) - {''}
    paths = public_paths(tracked, untracked)
    index_modes = {}
    for record in git('ls-files', '--stage', '-z').split(b'\0'):
        if record:
            info, path = record.split(b'\t'); mode, _, stage = info.decode().split()
            assert stage == '0', 'Unresolved merge entry'
            index_modes[path.decode()] = mode
    for p in ADDED:
        wanted[p] = ('100644', blob_id((ROOT/p).read_bytes()))
    for p in paths:
        path = ROOT/p
        assert path.is_file() and not path.is_symlink(), 'Nonregular public source'
        assert not {'.lake', '.development', '__pycache__'} & set(pathlib.PurePosixPath(p).parts), 'Tracked cache forbidden'
        actual[p] = (index_modes.get(p, '100644'), blob_id(path.read_bytes()))
    validate_inventory(wanted, actual)
    physical = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean')
                if not {'.git', '.lake', '.toolchain'} & set(p.parts)}
    assert physical == {p for p in wanted if p.endswith('.lean')}, 'Physical proof inventory drift'
    return {p: ('exact-PR130-PR131-parent-union', (ROOT/p).read_bytes()) for p in wanted}

def install_c2_inventory_adapter(namespace: dict) -> None:
    assert '_pr130_pr131_original_expected_sources' not in namespace, 'Duplicate joint adapter'
    assert '_manifold_release_original_expected_sources' in namespace, 'Master adapter missing'
    namespace['_pr130_pr131_original_expected_sources'] = namespace['expected_sources']
    namespace['expected_sources'] = expected_sources
    def check_imports(raw):
        importlib.import_module('point4_c2_metric_localization_source_test').legacy_check_imports(raw)
    def check_metadata(raw):
        importlib.import_module('point4_c2_metric_localization_source_test').legacy_check_metadata(raw)
    namespace['check_imports'] = check_imports
    namespace['check_metadata'] = check_metadata
    namespace['ADDED'] = set(namespace['ADDED']) | ADDED

def main() -> None:
    for parent in (REPAIR, MASTER):
        subprocess.run(['git', '--no-replace-objects', '-C', str(ROOT),
                        'merge-base', '--is-ancestor', parent, 'HEAD'], check=True)
    sources = expected_sources()
    print(f'Exact two-parent union: {len(sources)} source paths; original Lean/probe bytes preserved; Point 4 OPEN')

if __name__ == '__main__':
    main()
