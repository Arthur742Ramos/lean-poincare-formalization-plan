"""Admit one independently reviewed tree, without changing inherited guards."""
from pathlib import Path
import argparse, hashlib, json, os, re, stat, subprocess, sys

BASE = '1664872ce762ee027b76cb515befb0ae829b2711'
BASE_TREE = '6d74e9612cf6e16f2d027012cede68e5e0a23483'
META = 'curvature/third-party/differential-geometry/'
APPROVED_SOURCE_TABLE_SHA256 = '69f2b44e5fdd6cde1d4173e1282eb7d422aea6026e53909eaa7057d8f10a712e'
RICCI_DRAFT_BASE = '3818bef6722e8c9810739a9fce26b5ec07bec98a'
RICCI_DRAFT_BASE_TREE = '990d9fbe4fc8994c9dbafe278bbc1ccc71371f7b'
APPROVED_RICCI_SOURCE_TABLE_SHA256 = '04749486e28c3270c2429026e2b53e4db2fe57adbd96d6ec422fbf063c2f2114'
APPROVED_RICCI_PROBE_CONTRACTS_SHA256 = '00c985f73d88685daa6f99d730e1b8efa5e31820821501feccddfb0d1295d780'
RICCI_MODIFIED_PATHS = {'curvature/scripts/chart_port_candidate_check.py',
                        'curvature/scripts/chart_port_ci.py',
                        'curvature/scripts/test_chart_port_ci.py',
                        'curvature/third-party/differential-geometry/SOURCE-PROVENANCE.json',
                        'docs/point4/local-chart-connection.md'}
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
# The Batteries pin has exactly one documentation link. Its identity is
# retained in the complete fixed dependency catalog below.
BATTERIES_LINK = ('docs/README.md', '32d46ee883b58d6a383eed06eb98f33aa6530ded',
                  b'../README.md', 'README.md', '4cd48268d7a14d8f5867862c549534cac08ebd45', 5427)

PINNED_GIT_DEPENDENCIES = {
    'mathlib': 'db584cd6d46c92f209a44c0f1c829460d327499d',
    'plausible': 'b7eb3304aeae834b12dda98993a37f6a41f6f0bb',
    'LeanSearchClient': '5f4d51b81cbd3f6b32b156bfad9056621a040404',
    'importGraph': '16f02aa7642864af59f1ff0e384a015994db9118',
    'proofwidgets': '4be2e3d5087eeb272cf5a8853b8f9dd025ef5957',
    'aesop': '3448c0bcc5ce01b2d1546e483ec3620e32df3d0e',
    'Qq': '92c15be17b7caf78c2ad767ec40f89052d908d81',
    'batteries': BATTERIES_PIN,
    'Cli': '6130a47896ce867c6a4a55373441e59e565bad0f'}
# Complete mode-120000 catalogs of all nine immutable Git trees: three aliases
# total. The two archived benchmark aliases and targets are checked as bytes;
# neither executing benchmarks nor other code links is authorized here.
PINNED_DEPENDENCY_LINKS = {name: () for name in PINNED_GIT_DEPENDENCIES}
PINNED_DEPENDENCY_LINKS['batteries'] = (
    (*BATTERIES_LINK[:4], '100644', *BATTERIES_LINK[4:]),)
PINNED_DEPENDENCY_LINKS['mathlib'] = (
    ('scripts/bench/build/fake-root/bin/lean.py', '819298943e1a8c331413fb55e2c4bbc98d05e562',
     b'lean', 'scripts/bench/build/fake-root/bin/lean', '100755', '2ce14c08b2c7ba3d38c6e552e1c5d25de7f1a527', 2336),
    ('scripts/bench/size/run.py', 'e5224d533ef27b001224859a9b36696846a7e7fe',
     b'run', 'scripts/bench/size/run', '100755', '38bea958139cfd9297e73219d509adb63c811eb3', 1545))

def dependency_links(root, dependencies):
    links = {}
    if dependencies:
        assert set(dependencies) == {'curvature/.lake/packages/' + name for name in PINNED_GIT_DEPENDENCIES}, 'Pinned dependency root inventory differs'
    for dep_rel, entries in dependencies.items():
        name = dep_rel.rsplit('/', 1)[1]
        pin = PINNED_GIT_DEPENDENCIES[name]
        assert git(root / dep_rel, 'rev-parse', 'HEAD').decode().strip() == pin, 'Pinned dependency pin differs: ' + name
        assert tree_entries(root / dep_rel, pin) == entries, 'Dependency inventory differs from pinned tree: ' + name
        declared = {p for p, (mode, _, _) in entries.items() if mode == '120000'}
        catalog = PINNED_DEPENDENCY_LINKS[name]
        assert declared == {r[0] for r in catalog}, 'Pinned dependency link catalog differs: ' + name
        for path, link_blob, raw, target, target_mode, target_blob, target_bytes in catalog:
            assert entries[path] == ('120000', 'blob', link_blob), 'Pinned link declaration differs: ' + dep_rel + '/' + path
            assert entries.get(target) == (target_mode, 'blob', target_blob), 'Pinned regular target declaration differs: ' + dep_rel + '/' + target
            # Catalog targets are fixed same-package paths: README.md or the
            # same-directory executable source. No physical link is followed.
            links[dep_rel + '/' + path] = (link_blob, raw, dep_rel + '/' + target, target_mode, target_blob, target_bytes, pin)
    return links

def package_root_relationships(root, pkg, manifest, env):
    """Bounded observations before admission; these grant no root exceptions."""
    def observe(path):
        row = dict(declared_path=str(path))
        try:
            mode = os.lstat(path).st_mode
        except FileNotFoundError:
            row.update(node_kind='missing', exists=False)
        else:
            kind = ('symlink' if stat.S_ISLNK(mode) else 'directory' if stat.S_ISDIR(mode)
                    else 'regular_file' if stat.S_ISREG(mode) else 'other')
            row.update(node_kind=kind, exists=True)
            if kind == 'symlink':
                raw = os.readlink(os.fsencode(path))
                row.update(raw_link_bytes=len(raw), raw_link_hex=raw.hex(), raw_link_text=os.fsdecode(raw))
        resolved = path.resolve(strict=False)
        row.update(resolved_path=str(resolved), resolved_within_checkout=resolved.is_relative_to(root.resolve()))
        return row
    rows = []
    for package in manifest['packages']:
        name, kind = package['name'], package['type']
        if kind == 'git':
            declared = pkg / manifest['packagesDir'] / name
            node = observe(declared)
            actual = None; pin_error = None
            if node['exists']:
                try:
                    actual = git(declared, 'rev-parse', 'HEAD').decode().strip()
                except subprocess.CalledProcessError as exc:
                    pin_error = dict(exit_code=exc.returncode, action='git --no-replace-objects rev-parse HEAD')
            rows.append(dict(name=name, manifest_type=kind, root=node,
                manifest_pin=package['rev'], expected_pin=PINNED_GIT_DEPENDENCIES.get(name), actual_pin=actual,
                pin_read_error=pin_error, pins_match=actual == package['rev'] == PINNED_GIT_DEPENDENCIES.get(name)))
        elif kind == 'path':
            declared = pkg / package['dir']; node = observe(declared)
            expected = root / 'hamilton-ivey-reaction'
            rows.append(dict(name=name, manifest_type=kind, manifest_dir=package['dir'], root=node,
                expected_checkout_relative_root='hamilton-ivey-reaction',
                observed_expected_root_relationship=node['exists'] and node['resolved_path'] == str(expected.resolve()),
                expected_pin=None, actual_pin=None, pin_relation='committed public source; not a Git dependency pin',
                generated_package_mirror=observe(pkg / manifest['packagesDir'] / name)))
    paths = {}
    for key in ('LEAN_SRC_PATH', 'LEAN_PATH'):
        values = [p for p in env.get(key, '').split(os.pathsep) if p]
        paths[key] = dict(truncated=len(values) > 128, observations=[observe(p if p.is_absolute() else pkg / p)
            for p in map(Path, values[:128])])
    return dict(diagnostic_only=True, root_link_exceptions_granted=False, packages=rows, configured_paths=paths,
        declared_relationship_source='Lean d8b18978322de05a8f3dba51ef03cf5461676c17 Lake/Load/Materialize.lean PackageEntry.materialize')

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
                link_blob, raw, target, target_mode, target_blob, target_bytes, pin = links[rel]
                assert expected[rel] == ('120000', 'blob', link_blob)
                # Passing a bytes path returns the raw link bytes without following it.
                data = os.readlink(os.fsencode(item.path))
                assert isinstance(data, bytes) and data == raw, 'Physical link text differs: ' + rel
                actual_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
                assert actual_blob == link_blob, 'Physical link blob differs: ' + rel
                observed[rel] = ('120000', 'blob', actual_blob)
                observed_links.append(dict(path=rel, pin=pin, link_blob=actual_blob,
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
                for _, _, target, _, _, target_bytes, _ in links.values():
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
    for _, _, target, target_mode, target_blob, _, _ in links.values():
        assert observed[target] == (target_mode, 'blob', target_blob), 'Physical regular link target differs'
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

def check_ricci_extension_probe(data, contract):
    text = data.decode('utf8')
    assert 'sorryAx' not in text and 'error:' not in text
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    rows = []
    for match in re.finditer(pattern, text):
        body = re.sub(r'\b(propext|Classical\.choice|Quot\.sound)\.\{[^{}]*\}', r'\1', match.group(2) or '')
        values = [value.strip() for value in body.split(',') if value.strip()]
        assert set(values) <= {'propext', 'Classical.choice', 'Quot.sound'}, match.group(1)
        rows.append([match.group(1), values])
    assert rows == contract['axiom_rows'], 'Missing, duplicate, reordered or changed extension axiom evidence'
    assert rows and contract['full_printed_declarations'], 'Empty extension evidence contract'
    for name in contract['full_printed_declarations']:
        pattern = r'(?m)^(?:@\[[^\n]*\]\s*)*(?:theorem|def|opaque|abbrev|axiom|instance|structure|class)\s+' + re.escape(name) + r'(?=\.\{|\s|:|$)'
        assert re.search(pattern, text), 'Missing full extension declaration: ' + name
    return dict(module=contract['module'], axiom_rows=rows,
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
    extension = prov['geometric_ricci_extension']
    assert extension['schema_version'] == 1
    assert extension['dependent_base_sha'] == RICCI_DRAFT_BASE
    assert extension['dependent_base_tree'] == RICCI_DRAFT_BASE_TREE
    assert git(root, 'rev-parse', RICCI_DRAFT_BASE + '^{tree}').decode().strip() == RICCI_DRAFT_BASE_TREE
    subprocess.run(['git', '--no-replace-objects', '-C', str(root), 'merge-base', '--is-ancestor', RICCI_DRAFT_BASE, expected_sha], check=True)
    extension_rows = extension['sources']
    keys = ('module', 'path', 'bytes', 'sha256', 'git_blob', 'mode', 'imports', 'role')
    bound_rows = [{key: row[key] for key in keys} for row in extension_rows]
    assert digest(json.dumps(sorted(bound_rows, key=lambda row: row['path']), sort_keys=True, separators=(',', ':')).encode()) == APPROVED_RICCI_SOURCE_TABLE_SHA256
    assert extension['source_table_sha256'] == APPROVED_RICCI_SOURCE_TABLE_SHA256
    extension_paths = {row['path'] for row in extension_rows}
    assert len(extension_rows) == len(extension_paths) == 23
    assert sum(row['role'] == 'mathematical source' for row in extension_rows) == 13
    assert sum(row['role'] == 'probe' for row in extension_rows) == 10
    contracts = extension['probe_contracts']
    assert digest(json.dumps(contracts, sort_keys=True, separators=(',', ':')).encode()) == APPROVED_RICCI_PROBE_CONTRACTS_SHA256
    assert extension['probe_contracts_sha256'] == APPROVED_RICCI_PROBE_CONTRACTS_SHA256
    assert len(contracts) == 10 and {row['module'] for row in contracts} == {row['module'] for row in extension_rows if row['role'] == 'probe'}
    dependent = tree_entries(root, RICCI_DRAFT_BASE)
    assert set(dependent) <= set(current), 'Dependent base path deletion'
    assert set(current) - set(dependent) == extension_paths, 'Unexpected dependent draft additions'
    assert {path for path in dependent if dependent[path] != current[path]} == RICCI_MODIFIED_PATHS, 'Unexpected dependent base change'
    assert set(base) <= set(current), 'Base path deletion'
    assert set(current) - set(base) == new_paths | EXTRA | extension_paths, 'Unexpected added paths'
    assert len({p.casefold() for p in current}) == len(current), 'Case-fold path collision'
    assert [p for p in base if base[p] != current[p]] == ['curvature/lakefile.toml'], 'Inherited path/hash/mode change'
    config = git(root, 'show', BASE + ':curvature/lakefile.toml')
    addition = b'\n[[lean_lib]]\nname = "DifferentialGeometry"\nmoreLeanArgs = ["-j1", "-M5632", "-DautoImplicit=false", "-DmaxSynthPendingDepth=3"]\n\n[[lean_lib]]\nname = "ChartPort"\nmoreLeanArgs = ["-j1", "-M5632", "-DautoImplicit=false", "-DmaxSynthPendingDepth=3"]\n'
    assert (root / 'curvature/lakefile.toml').read_bytes() == config + addition
    for p in new_paths | EXTRA | extension_paths | {'curvature/lakefile.toml'}:
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
    legacy_closure = list(ordered)
    legacy_external = sorted(external)
    for row in extension_rows:
        assert row['module'] not in modules
        data = (root / row['path']).read_bytes()
        assert len(data) == row['bytes'] and digest(data) == row['sha256'], row['path']
        assert imports(data) == row['imports']
        assert current[row['path']] == (row['mode'], 'blob', row['git_blob'])
        modules[row['module']] = row
    for contract in contracts:
        assert modules[contract['module']]['sha256'] == contract['source_sha256']
    for row in extension_rows:
        visit(row['module'])
    assert len(ordered) == 94 and visited == set(modules)
    assert sorted(external) == extension['external_mathlib_roots']
    extension_closure = ordered[71:]
    assert len(extension_closure) == 23 and {row['module'] for row in extension_closure} == {row['module'] for row in extension_rows}
    return dict(candidate_sha=expected_sha, candidate_tree=expected_tree, base=BASE, base_tree=BASE_TREE,
                additions=len(new_paths | EXTRA | extension_paths), modified_paths=['curvature/lakefile.toml'],
                inherited_paths=len(base), all_inherited_validators_unchanged=True,
                physical_inventory=physical,
                closure=legacy_closure, legacy_external_mathlib_roots=legacy_external,
                extension_closure=extension_closure, extension_probe_contracts=contracts,
                dependent_base=RICCI_DRAFT_BASE, dependent_base_tree=RICCI_DRAFT_BASE_TREE,
                dependent_modified_paths=sorted(RICCI_MODIFIED_PATHS),
                external_mathlib_roots=sorted(external), point4='OPEN', general_targets='OPEN')

# BEGIN exact finite auxiliary-138
import hashlib as _curvature_hashlib, pathlib as _curvature_pathlib, sys as _curvature_sys
_curvature_sys.dont_write_bytecode = True
_curvature_root = _curvature_pathlib.Path(__file__).resolve().parents[2]
_curvature_helper = _curvature_root / 'curvature/scripts/point4_smooth_master_composition.py'
assert _curvature_helper.is_file() and not _curvature_helper.is_symlink()
assert _curvature_hashlib.sha256(_curvature_helper.read_bytes()).hexdigest() == '16dd081d6873024649fa235294d570db3aa0a61818c07ee96a4157f4bd32b64d', "Auxiliary composition helper identity drift"
import point4_smooth_master_composition as _curvature_comp
_curvature_comp.install_curvature_auxiliary(globals(),138)
# END exact finite auxiliary-138

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
