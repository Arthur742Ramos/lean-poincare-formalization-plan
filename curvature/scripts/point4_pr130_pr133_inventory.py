#!/usr/bin/env python3
"""Exact two-parent source inventory; compiler evidence is a separate receipt."""
from __future__ import annotations
import hashlib
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
REPAIR = '4618f0e9c140dfbcd1093f91cbfd40839aa1a503'
MASTER = 'f59fb6799f77d5d9cc298fef2632e8ebf887b97b'
TREES = {REPAIR: '47a3dc90207dde27dbdd414d7da6043266f76b81',
         MASTER: '9ab0bbc6ba97352e903a0489cf89fddb97757a17'}
PRIOR_ROOTS = {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml', 'docs/point4/README.md'}
SHARED_DIFFERENCES = {'curvature/scripts/point4_manifold_heat_release_guard.py', 'curvature/PoincareCurvature.lean', 'curvature/scripts/point4_linear_heat_geometry_source_test.py', 'curvature/scripts/point4_manifold_heat_release_mock_test.py', '.github/workflows/point4-c2-initial-heat.yml', 'curvature/scripts/point4_c2_initial_heat_source_test.py', 'docs/point4/README.md', 'curvature/scripts/point4_linear_heat_geometry_mock_test.py', 'curvature/scripts/point4_manifold_heat_source_test.py', 'curvature/formalization.yaml', '.github/workflows/point4-linear-heat-geometry.yml', 'curvature/scripts/point4_c2_initial_heat_mock_test.py', '.github/workflows/point4-weighted-initial-heat.yml'}
ADDED = {'curvature/scripts/point4_pr130_pr133_inventory.py', 'curvature/scripts/point4_pr130_pr133_inventory_test.py', 'docs/point4/pr130-pr133-desktop-integration.md'}

def git(*args: str, data: bytes | None = None) -> bytes:
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(ROOT),
                                    *args], input=data)

def blob_id(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def resolve_inventory(repair: dict, master: dict) -> dict:
    differences = {p for p in repair.keys() & master.keys() if repair[p] != master[p]}
    assert differences == SHARED_DIFFERENCES, 'Unexpected parent overlap'
    assert not ADDED & (repair.keys() | master.keys()), 'New adapter path collision'
    result = dict(repair)
    result.update(master)
    for path in PRIOR_ROOTS:
        result[path] = repair[path]
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
    return {p: ('exact-PR130-PR131-PR133-parent-union', (ROOT/p).read_bytes()) for p in wanted}

def main() -> None:
    for parent in (REPAIR, MASTER):
        subprocess.run(['git', '--no-replace-objects', '-C', str(ROOT),
                        'merge-base', '--is-ancestor', parent, 'HEAD'], check=True)
    sources = expected_sources()
    print(f'Exact two-parent union: {len(sources)} source paths; exact master dispatch and prior Lean/probe bytes preserved; Point 4 OPEN')

if __name__ == '__main__':
    main()
