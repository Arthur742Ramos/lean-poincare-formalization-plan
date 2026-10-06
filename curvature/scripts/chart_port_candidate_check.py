"""Admit one independently reviewed tree, without changing inherited guards."""
from pathlib import Path
import argparse, hashlib, json, os, re, stat, subprocess, sys

BASE = '1664872ce762ee027b76cb515befb0ae829b2711'
BASE_TREE = '6d74e9612cf6e16f2d027012cede68e5e0a23483'
META = 'curvature/third-party/differential-geometry/'
APPROVED_SOURCE_TABLE_SHA256 = '69f2b44e5fdd6cde1d4173e1282eb7d422aea6026e53909eaa7057d8f10a712e'
EXTRA = {META + x for x in ('LICENSE', 'NOTICE', 'README.upstream.md', 'SOURCE-PROVENANCE.json', 'minimal-upstream-port.patch')}
EXTRA |= {'docs/point4/local-chart-connection.md', '.github/workflows/point4-local-chart-connection.yml',
          'curvature/scripts/chart_port_candidate_check.py', 'curvature/scripts/chart_port_ci.py'}
EXTRA.add('curvature/scripts/chart_port_artifacts.py')
EXTRA |= {'curvature/scripts/test_chart_port_ci.py',
          '.github/workflows/point4-local-chart-environment-setup.yml'}

# Finite output names follow the pinned Lake 4.33 module layout. Local proof
# outputs are outside the checkout, so no local .lake/build files are admitted.
# This order is source-qualified for the immutable workspace manifest: root
# index 0, reverse direct dependency order, breadth-first resolution. It is not
# a generic claim that arbitrary manifest arrays determine Lake indices.
PINNED_PACKAGE_CONFIGS = (
    ('HamiltonIveyReaction', 'lakefile.toml'), ('mathlib', 'lakefile.lean'),
    ('plausible', 'lakefile.toml'), ('LeanSearchClient', 'lakefile.toml'),
    ('importGraph', 'lakefile.toml'), ('proofwidgets', 'lakefile.lean'),
    ('aesop', 'lakefile.toml'), ('Qq', 'lakefile.toml'),
    ('batteries', 'lakefile.toml'), ('Cli', 'lakefile.toml'))
CONFIG_OUTPUT_SUFFIXES = ('.olean', '.olean.trace', '.olean.lock')

def configuration_outputs(root):
    manifest = json.loads((root / 'curvature/lake-manifest.json').read_text())
    assert manifest['name'] == 'PoincareCurvature'
    assert manifest['lakeDir'] == '.lake'
    assert tuple((p['name'], p['configFile']) for p in manifest['packages']) == PINNED_PACKAGE_CONFIGS
    # The two pinned Lean configurations are legacy sources. Lake writes their
    # olean, trace and lock under the workspace config directory (indices 2, 6).
    return {'curvature/.lake/config/' + str(index) + '/lakefile' + suffix
            for index, (_, config) in enumerate(PINNED_PACKAGE_CONFIGS, 1)
            if config == 'lakefile.lean' for suffix in CONFIG_OUTPUT_SUFFIXES}
IMPORT_SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig', '.ilean', '.trace', '.ltar')

BATTERIES_ROOT = 'curvature/.lake/packages/batteries'
BATTERIES_PIN = '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d'
# The pinned tree has exactly one documentation link. This is a finite source
# catalog, independent of build-output admission; no code link is admitted.
BATTERIES_LINK = ('docs/README.md', '32d46ee883b58d6a383eed06eb98f33aa6530ded',
                  b'../README.md', 'README.md', '4cd48268d7a14d8f5867862c549534cac08ebd45', 5427)

def dependency_links(root, dependencies):
    links = {}
    for dep_rel, entries in dependencies.items():
        declared = {p for p, (mode, _, _) in entries.items() if mode == '120000'}
        if dep_rel == BATTERIES_ROOT:
            assert git(root / dep_rel, 'rev-parse', 'HEAD').decode().strip() == BATTERIES_PIN, 'Batteries pin differs'
            assert tree_entries(root / dep_rel, BATTERIES_PIN) == entries, 'Batteries inventory differs from pinned tree'
            path, link_blob, raw, target, target_blob, target_bytes = BATTERIES_LINK
            assert declared == {path}, 'Batteries link catalog differs'
            assert entries[path] == ('120000', 'blob', link_blob), 'Batteries link declaration differs'
            assert entries.get(target) == ('100644', 'blob', target_blob), 'Batteries regular target declaration differs'
            # Exact ../README.md from docs/ names this same-package regular file.
            links[dep_rel + '/' + path] = (link_blob, raw, dep_rel + '/' + target, target_blob, target_bytes)
        else:
            assert not declared, 'Undeclared dependency link: ' + dep_rel
    return links

def physical_inventory(root, public_entries, dependencies=None):
    """Enumerate actual files/directories, including ignored and untracked ones."""
    dependencies = dependencies or {}
    links = dependency_links(root, dependencies)
    expected = dict(public_entries)
    outputs, git_dirs = set(), {'.git'}
    if dependencies:
        outputs.update(configuration_outputs(root))
        for dep_rel, dep_entries in dependencies.items():
            assert dep_rel.startswith('curvature/.lake/packages/')
            assert dep_rel.count('/') == 3
            git_dirs.add(dep_rel + '/.git')
            for path, entry in dep_entries.items():
                expected[dep_rel + '/' + path] = entry
                if path.endswith('.lean'):
                    stem = path[:-5]
                    for suffix in IMPORT_SUFFIXES:
                        out = dep_rel + '/.lake/build/lib/lean/' + stem + suffix
                        outputs.update((out, out + '.hash'))
                    for suffix in ('.c', '.bc'):
                        out = dep_rel + '/.lake/build/ir/' + stem + suffix
                        outputs.update((out, out + '.hash'))
    files_allowed = set(expected) | outputs
    directories = set()
    for path in files_allowed | git_dirs:
        parts = path.split('/')
        directories.update('/'.join(parts[:i]) for i in range(1, len(parts)))
    observed, observed_outputs, observed_links = {}, [], []
    def visit(directory):
        for item in os.scandir(directory):
            rel = Path(item.path).relative_to(root).as_posix()
            if item.is_symlink():
                assert rel in links and rel not in public_entries, 'Physical symlink: ' + rel
                link_blob, raw, target, target_blob, target_bytes = links[rel]
                assert expected[rel] == ('120000', 'blob', link_blob)
                # Passing a bytes path returns the raw link bytes without following it.
                data = os.readlink(os.fsencode(item.path))
                assert isinstance(data, bytes) and data == raw, 'Physical link text differs: ' + rel
                actual_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                assert actual_blob == link_blob, 'Physical link blob differs: ' + rel
                observed[rel] = ('120000', 'blob', actual_blob)
                observed_links.append(dict(path=rel, pin=BATTERIES_PIN, link_blob=actual_blob,
                    raw_bytes=len(data), raw_sha256=digest(data), target=target, target_blob=target_blob))
                continue
            if rel in git_dirs:
                assert item.is_dir(follow_symlinks=False), 'Expected Git metadata directory: ' + rel
                continue
            if item.is_dir(follow_symlinks=False):
                assert rel in directories, 'Unexpected physical directory: ' + rel
                visit(Path(item.path))
            else:
                assert item.is_file(follow_symlinks=False), 'Unexpected physical node: ' + rel
                assert rel in files_allowed, 'Unexpected physical file: ' + rel
                if rel in outputs:
                    observed_outputs.append(rel)
                    continue
                data = Path(item.path).read_bytes()
                for _, _, target, _, target_bytes in links.values():
                    if rel == target:
                        assert len(data) == target_bytes, 'Physical link target size differs: ' + rel
                mode, kind, blob = expected[rel]
                assert kind == 'blob' and mode in {'100644', '100755'}, (rel, mode, kind)
                actual_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                assert actual_blob == blob, 'Physical bytes differ from committed blob: ' + rel
                if os.name != 'nt':
                    physical_mode = '100755' if item.stat(follow_symlinks=False).st_mode & 0o111 else '100644'
                    assert physical_mode == mode, 'Physical mode differs: ' + rel
                observed[rel] = (mode, kind, actual_blob)
    visit(root)
    assert set(observed) == set(expected), 'Missing physical public/dependency file'
    assert {r['path'] for r in observed_links} == set(links), 'Missing physical declared link'
    for _, _, target, target_blob, _ in links.values():
        assert observed[target] == ('100644', 'blob', target_blob), 'Physical regular link target differs'
    return dict(public_files=len(public_entries), dependency_files=len(expected)-len(public_entries),
                declared_build_outputs=sorted(observed_outputs), public_identity_sha256=digest(json.dumps(observed, sort_keys=True).encode()),
                declared_source_links=sorted(observed_links, key=lambda r:r['path']),
                full_physical_inventory_checked=True, local_project_cache_admitted=False)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(root, *args):
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(root), *args])

def tree_entries(root, ref):
    entries = {}
    for record in git(root, 'ls-tree', '-r', '-z', ref).split(b'\0'):
        if not record:
            continue
        info, path = record.split(b'\t', 1)
        mode, kind, blob = info.decode().split()
        entries[path.decode()] = (mode, kind, blob)
    return entries

def imports(data):
    text = data.decode('utf8')
    clean, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
            continue
        if depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
            continue
        if text[i] == '\n' or not depth:
            clean.append(text[i])
        i += 1
    result = []
    for line in ''.join(clean).splitlines():
        line = line.split('--', 1)[0]
        m = re.match(r'^\s*(?:(?:public|meta)\s+)?import\s+(?:all\s+)?(.+)', line)
        if m:
            result.extend(m.group(1).split())
    return result

def check_probe(data):
    text = data.decode('utf8')
    names = ['ChartPort.projectChosen_eq_chartLeviCivita',
             'DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on',
             'DifferentialGeometry.Geometry.Connection.chartLeviCivita_isMetricCompatibleOn',
             'DifferentialGeometry.Geometry.Connection.koszul_local_uniqueness',
             'ContMDiffSection.exists_eq_at', 'RicciFlow.SmoothForward.toC2']
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    assert [n for n, _ in rows] == names, 'Missing, duplicate, reordered or extra axiom evidence'
    for name, body in rows:
        body = re.sub(r'\b(propext|Classical\.choice|Quot\.sound)\.\{[^{}]*\}', r'\1', body)
        assert [x.strip() for x in body.split(',')] == ['propext', 'Classical.choice', 'Quot.sound'], (name, body)
    for prefix in ('theorem ChartPort.projectChosen_eq_chartLeviCivita',
                   'def DifferentialGeometry.Geometry.Connection.chartLeviCivita',
                   'def DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet',
                   'theorem DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on',
                   'theorem DifferentialGeometry.Geometry.Connection.chartLeviCivita_isMetricCompatibleOn'):
        assert prefix in text, 'Missing full printed declaration: ' + prefix
    assert 'sorryAx' not in text and 'error:' not in text
    return dict(axiom_declarations=names, allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                full_printed_type_and_proof=True, raw_log_sha256=digest(data))

def admit(root, expected_sha, expected_tree, dependencies=None):
    assert re.fullmatch('[0-9a-f]{40}', expected_sha)
    assert re.fullmatch('[0-9a-f]{40}', expected_tree)
    assert git(root, 'rev-parse', 'HEAD').decode().strip() == expected_sha
    assert git(root, 'rev-parse', 'HEAD^{tree}').decode().strip() == expected_tree
    assert git(root, 'rev-parse', BASE + '^{tree}').decode().strip() == BASE_TREE
    subprocess.run(['git', '--no-replace-objects', '-C', str(root), 'merge-base', '--is-ancestor', BASE, expected_sha], check=True)
    assert not git(root, 'diff', '--name-only', 'HEAD'), 'Tracked working tree differs from admitted commit'
    assert not git(root, 'diff', '--cached', '--name-only', 'HEAD'), 'Index differs from admitted commit'
    base, current = tree_entries(root, BASE), tree_entries(root, 'HEAD')
    index = {}
    for record in git(root, 'ls-files', '--stage', '-z').split(b'\0'):
        if record:
            info, path = record.split(b'\t', 1)
            mode, blob, stage = info.decode().split()
            assert stage == '0', 'Unmerged index entry'
            index[path.decode()] = (mode, 'blob', blob)
    assert index == current, 'Index path/hash/mode inventory differs from HEAD'
    physical = physical_inventory(root, current, dependencies)
    prov = json.loads((root / (META + 'SOURCE-PROVENANCE.json')).read_text())
    assert prov['base_commit'] == BASE and prov['base_tree'] == BASE_TREE
    assert prov['mathlib_commit'] == 'db584cd6d46c92f209a44c0f1c829460d327499d'
    rows = prov['new_sources']
    approved_rows = [{k:r[k] for k in ('module', 'path', 'bytes', 'sha256')} for r in rows]
    assert digest(json.dumps(sorted(approved_rows, key=lambda r:r['path']), sort_keys=True, separators=(',', ':')).encode()) == APPROVED_SOURCE_TABLE_SHA256
    new_paths = {r['path'] for r in rows}
    assert len(rows) == len(new_paths) == 58
    assert sum(p.startswith('curvature/DifferentialGeometry/') for p in new_paths) == 55
    assert {p for p in new_paths if p.startswith('curvature/ChartPort/')} == {
        'curvature/ChartPort/MetricAPI.lean', 'curvature/ChartPort/ChartIdentity.lean', 'curvature/ChartPort/ChartIdentityEvidence.lean'}
    assert set(base) <= set(current), 'Base path deletion'
    assert set(current) - set(base) == new_paths | EXTRA, 'Unexpected added paths'
    assert len({p.casefold() for p in current}) == len(current), 'Case-fold path collision'
    assert [p for p in base if base[p] != current[p]] == ['curvature/lakefile.toml'], 'Inherited path/hash/mode change'
    config = git(root, 'show', BASE + ':curvature/lakefile.toml')
    addition = b'\n[[lean_lib]]\nname = "DifferentialGeometry"\nmoreLeanArgs = ["-j1", "-M5632", "-DautoImplicit=false", "-DmaxSynthPendingDepth=3"]\n\n[[lean_lib]]\nname = "ChartPort"\nmoreLeanArgs = ["-j1", "-M5632", "-DautoImplicit=false", "-DmaxSynthPendingDepth=3"]\n'
    assert (root / 'curvature/lakefile.toml').read_bytes() == config + addition
    for p in new_paths | EXTRA | {'curvature/lakefile.toml'}:
        mode, kind, blob = current[p]
        assert (mode, kind) == ('100644', 'blob'), (p, mode, kind)
        data = (root / p).read_bytes()
        assert not (root / p).is_symlink()
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
    modules = {}
    for r in rows:
        data = (root / r['path']).read_bytes()
        assert digest(data) == r['sha256'] and len(data) == r['bytes'], r['path']
        assert imports(data) == r['imports']
        modules[r['module']] = r
    inherited = prov['inherited_sources']
    assert len(inherited) == 13 and sum(r['literal_local_blob_matches_base'] for r in inherited) == 1
    for r in inherited:
        assert base[r['path']][2] == r['base_git_blob_sha']
        data = (root / r['path']).read_bytes()
        assert digest(data) == r['public_base_sha256']
        name = r['path'][10:-5].replace('/', '.')
        modules[name] = dict(module=name, path=r['path'], sha256=digest(data), imports=imports(data), role='inherited source')
    ordered, active, visited, external = [], set(), set(), set()
    def visit(name):
        if name.startswith('Mathlib.'):
            external.add(name)
            return
        assert name in modules, 'Unexpected local import ' + name
        assert name not in active, 'Import cycle'
        if name in visited:
            return
        active.add(name)
        for dep in modules[name]['imports']:
            visit(dep)
        active.remove(name)
        visited.add(name)
        ordered.append(modules[name])
    visit('ChartPort.ChartIdentityEvidence')
    assert len(ordered) == 71 and visited == set(modules)
    assert sorted(external) == prov['external_mathlib_roots']
    assert len(prov['mathlib_support_sources']) == 31 and prov['mathlib_source_modifications'] == 0
    assert digest((root / (META + 'minimal-upstream-port.patch')).read_bytes()) == prov['original_patch_sha256']
    return dict(candidate_sha=expected_sha, candidate_tree=expected_tree, base=BASE, base_tree=BASE_TREE,
                additions=len(new_paths | EXTRA), modified_paths=['curvature/lakefile.toml'],
                inherited_paths=len(base), all_inherited_validators_unchanged=True,
                physical_inventory=physical,
                closure=ordered, external_mathlib_roots=sorted(external), point4='OPEN', general_targets='OPEN')

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-sha')
    ap.add_argument('--expected-tree')
    ap.add_argument('--probe-log', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if args.probe_log:
        result = check_probe(args.probe_log.read_bytes())
    else:
        root = Path(__file__).resolve().parents[2]
        result = admit(root, args.expected_sha, args.expected_tree)
    raw = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(raw + '\n')
    print(raw)
