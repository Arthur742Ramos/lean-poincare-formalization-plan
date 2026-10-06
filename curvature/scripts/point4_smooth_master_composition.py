#!/usr/bin/env python3
"""Finite source composition; source/evidence validation is not Lean closure.

Current weighted checks are leaves. Historical subprocesses execute immutable
original entry points; no current adapter is installed in their checkouts.
"""
from __future__ import annotations
import argparse, contextlib, functools, hashlib, importlib, json, os
import pathlib, re, stat, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
MASTER = 'e883681caa862277857ee825a547502e8f3ec036'
SUPPORT = '93ed035498e0bf02096202d2f2895d906fb88234'
LOCALIZATION = '6cdbc00828607d80e180a9cffc0cc3376b3b7e42'
TREES = {MASTER: '10740092a77d5457a981154ea0d75a11120c54dd',
         SUPPORT: '51b59d500108f632e3fa7d7993d14d74fd1491a7'}
HELPER = 'curvature/scripts/point4_smooth_master_composition.py'
TEST = 'curvature/scripts/point4_smooth_master_composition_test.py'
MAP = 'docs/point4/smooth-master-composition/identity-map.json'
DOC = 'docs/point4/smooth-master-composition.md'
NEW = {HELPER, TEST, MAP, DOC}
WEIGHTED = 'curvature/scripts/point4_weighted_hessian_release_guard.py'
LOCAL = 'curvature/scripts/point4_c2_metric_localization_source_test.py'
CONSISTENCY = 'curvature/scripts/point4_pr130_pr133_inventory.py'
SMOOTH = 'curvature/scripts/point4_smooth_forward_release_guard.py'
FIXTURE = 'curvature/scripts/point4_smooth_forward_release_mock_test.py'
WORKFLOW = '.github/workflows/point4-smooth-forward-support.yml'
EDITED = {WEIGHTED, LOCAL, CONSISTENCY, SMOOTH, FIXTURE, WORKFLOW}
SHARED = {'.github/workflows/point4-c2-initial-heat.yml',
 '.github/workflows/point4-linear-heat-geometry.yml',
 '.github/workflows/point4-weighted-initial-heat.yml',
 'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml',
 'curvature/scripts/point4_c2_initial_heat_mock_test.py',
 'curvature/scripts/point4_c2_initial_heat_source_test.py',
 'curvature/scripts/point4_linear_heat_geometry_mock_test.py',
 'curvature/scripts/point4_linear_heat_geometry_source_test.py',
 'curvature/scripts/point4_manifold_heat_release_guard.py',
 'curvature/scripts/point4_manifold_heat_release_mock_test.py',
 'curvature/scripts/point4_manifold_heat_source_test.py', 'docs/point4/README.md'}
ROOT_CHANGES = {'curvature/PoincareCurvature.lean', 'curvature/formalization.yaml', 'docs/point4/README.md'}
WEIGHTED_MISSING = {'.github/workflows/point4-c2-metric-localization.yml',
 'curvature/PoincareCurvature/Analysis/CompactlySupportedC2Jet.lean',
 'curvature/PoincareCurvature/Analysis/FiniteCoordinateBilinear.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessInitialMetricLocalization.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/EuclideanC2Localization.lean',
 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/PositiveFrozenC2Localization.lean',
 'curvature/scripts/point4_c2_metric_localization_mock_test.py',
 'curvature/scripts/point4_c2_metric_localization_probe.lean', LOCAL,
 'curvature/scripts/point4_pr130_pr131_inventory.py',
 'curvature/scripts/point4_pr130_pr131_inventory_test.py', CONSISTENCY,
 'curvature/scripts/point4_pr130_pr133_inventory_test.py',
 'docs/point4/c2-metric-localization.md',
 'docs/point4/pr130-pr131-desktop-integration.md',
 'docs/point4/pr130-pr133-desktop-integration.md'}
ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
ENTRY = "\nif __name__ == '__main__':"
WF_ANCHOR = '      - name: Preserve exact-head evidence\n'
WF_STEP = "      - name: Check ordinary current composition and real historical validator routes\n        env:\n          EXPECTED_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n        run: |\n          PYTHONDONTWRITEBYTECODE=1 python3 curvature/scripts/point4_smooth_master_composition_test.py --real-runtime --schema /tmp/point4-manifold-heat-official-schema.json\n"
_owner = None
_depth = 0

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def blob_id(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def git(*args, root=None):
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(root or ROOT), *args], env=ENV)

def parse_tree(data):
    assert data and data.endswith(b'\0'), 'Incomplete source tree'
    result = {}
    for record in data.split(b'\0')[:-1]:
        descriptor, path = record.split(b'\t', 1)
        mode, kind, oid = descriptor.decode().split()
        path = path.decode()
        assert kind == 'blob' and mode in {'100644', '100755'}
        assert re.fullmatch(r'[0-9a-f]{40}', oid) and path not in result
        assert not pathlib.PurePosixPath(path).is_absolute() and '..' not in pathlib.PurePosixPath(path).parts
        result[path] = mode, oid
    return result

def parent_tree(commit):
    if commit in TREES:
        assert git('rev-parse', commit+'^{tree}').decode().strip() == TREES[commit]
    return parse_tree(git('ls-tree', '-rz', commit))

def resolve_union(master, support):
    assert len(master) == 1704 and len(support) == 1672
    assert {p for p in master.keys() & support.keys() if master[p] != support[p]} == SHARED
    assert len(master.keys()-support.keys()) == 51 and len(support.keys()-master.keys()) == 19
    assert not NEW & (master.keys() | support.keys())
    result = dict(support)
    result.update(master)
    assert len(result) == 1723
    return result

def bootstrap(path, helper_sha):
    assert re.fullmatch(r'[0-9a-f]{64}', helper_sha)
    methods = {WEIGHTED: 'install_weighted', LOCAL: 'install_localization',
               CONSISTENCY: 'install_consistency', SMOOTH: 'install_smooth'}
    if path == FIXTURE:
        action = "if __name__ == '__main__':\n    _smooth_master.run_support_fixtures(sys.argv[1:])\n    raise SystemExit(0)\n"
    else:
        assert path in methods
        action = '_smooth_master.' + methods[path] + '(globals())\n'
    # Pin before import. These imports and count-one hooks are finite policy,
    # not records authorized by the descriptive JSON identity map.
    return ("\n# Reviewed finite smooth/master composition; original validator bodies survive.\n"
        "import hashlib as _composition_hashlib, pathlib as _composition_pathlib, stat as _composition_stat, sys as _composition_sys\n"
        "_composition_file = _composition_pathlib.Path(__file__).resolve().parents[2] / '" + HELPER + "'\n"
        "assert _composition_stat.S_ISREG(_composition_file.lstat().st_mode) and not _composition_file.lstat().st_mode & 0o111\n"
        "assert _composition_hashlib.sha256(_composition_file.read_bytes()).hexdigest() == '" + helper_sha + "', 'Composition executable binding changed'\n"
        + ("_composition_sys.modules.setdefault('point4_weighted_hessian_release_guard', _composition_sys.modules[__name__])\n" if path == WEIGHTED else '')
        + "import point4_smooth_master_composition as _smooth_master\n" + action)

def transform(path, original, helper_sha, fixture_sha=None, workflow_sha=None):
    source = original.decode()
    assert '_smooth_master.' not in source, 'Previously transformed source is not an input'
    if path == WORKFLOW:
        assert source.count(WF_ANCHOR) == 1 and WF_STEP not in source
        return source.replace(WF_ANCHOR, WF_STEP+WF_ANCHOR, 1).encode()
    if path == SMOOTH:
        assert fixture_sha and workflow_sha
        # Replace only the two selected FILE_SHA256 values, never other code.
        import ast
        a=source.index('FILE_SHA256 = ');b=source.index('\nADDED = ',a)
        mapping=ast.literal_eval(source[a+len('FILE_SHA256 = '):b])
        assert set(mapping)|{SMOOTH} == set(parent_tree(SUPPORT))-set(parent_tree(MASTER))
        mapping[FIXTURE]=fixture_sha;mapping[WORKFLOW]=workflow_sha
        source=source[:a]+'FILE_SHA256 = '+repr(mapping)+source[b:]
    assert path in EDITED and source.count(ENTRY) == 1, 'Adapter boundary must be count-one'
    return source.replace(ENTRY, bootstrap(path,helper_sha)+ENTRY,1).encode()

def original_bytes(path, master, support):
    parent = MASTER if path in master else SUPPORT
    data = git('show', parent+':'+path)
    assert blob_id(data) == (master if parent == MASTER else support)[path][1]
    return data

def expected_identity():
    master, support = parent_tree(MASTER), parent_tree(SUPPORT)
    union = resolve_union(master, support)
    helper_sha = sha256((ROOT/HELPER).read_bytes())
    originals = {p:original_bytes(p,master,support) for p in EDITED}
    changes = {p:transform(p,originals[p],helper_sha) for p in EDITED-{SMOOTH}}
    changes[SMOOTH]=transform(SMOOTH,originals[SMOOTH],helper_sha,
        sha256(changes[FIXTURE]),sha256(changes[WORKFLOW]))
    expected = dict(union)
    for path,data in changes.items():expected[path]='100644',blob_id(data)
    # New code/docs are bound to the exact committed HEAD/index/physical bytes.
    # Independent review must approve that external head; this is no self-review.
    head = parse_tree(git('ls-tree','-rz','HEAD'))
    for path in NEW:
        assert path in head and head[path][0]=='100644'
        expected[path]=head[path]
    return expected, originals, changes

def map_record(expected, originals, changes):
    master,support=parent_tree(MASTER),parent_tree(SUPPORT)
    return {'parents':{MASTER:TREES[MASTER],SUPPORT:TREES[SUPPORT]},
        'paths':len(expected),'canonical_point4':'OPEN','smooth_general_target':'OPEN',
        'provenance':[{'id':'https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/'+c+'/curvature',
            'relationship':'builds-on','note':'Exact inherited mathematical/probe source; only finite validator composition is new.'} for c in (MASTER,SUPPORT)],
        'weighted_missing_master':{p:list(master[p]) for p in sorted(WEIGHTED_MISSING)},
        'parent_identity':{MASTER:{p:list(master[p]) for p in sorted(master)},SUPPORT:{p:list(support[p]) for p in sorted(support)}},
        'resolutions':{p:{'selected':'master','master':list(master[p]),'support':list(support[p])} for p in sorted(SHARED)},
        'transforms':{p:{'parent':MASTER if p in master else SUPPORT,'original_blob':blob_id(originals[p]),
            'original_sha256':sha256(originals[p]),'final_blob':blob_id(changes[p]),'final_sha256':sha256(changes[p]),
            'mode':'100644','count':1} for p in sorted(EDITED)},
        'identity':{p:([expected[p][0],'<committed-HEAD>'] if p==MAP else list(expected[p])) for p in sorted(expected)}}

def verify_current():
    head = git('rev-parse','HEAD').decode().strip()
    assert re.fullmatch(r'[0-9a-f]{40}',head)
    if os.environ.get('EXPECTED_SHA'):assert head==os.environ['EXPECTED_SHA'], 'External expected HEAD drift'
    for commit in (MASTER,SUPPORT):
        subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'merge-base','--is-ancestor',commit,'HEAD'],check=True,env=ENV)
    expected,originals,changes=expected_identity()
    committed=parse_tree(git('ls-tree','-rz','HEAD'))
    assert committed==expected, 'Committed full source identity differs from finite policy'
    index={}
    for record in git('ls-files','--stage','-z').split(b'\0')[:-1]:
        descriptor,path=record.split(b'\t',1);mode,oid,stage=descriptor.decode().split();path=path.decode()
        assert stage=='0' and path not in index
        index[path]=mode,oid
    assert index==expected, 'Complete current index identity drift'
    for path,(mode,oid) in expected.items():
        file=ROOT/path
        for parent in file.parents:
            assert stat.S_ISDIR(parent.lstat().st_mode), 'Public symlink/non-directory parent'
            if parent==ROOT:break
        st=file.lstat().st_mode
        assert stat.S_ISREG(st) and bool(st&0o111)==(mode=='100755'), 'Current public mode drift: '+path
        assert blob_id(file.read_bytes())==oid, 'Current physical source drift: '+path
    physical={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean') if not {'.git','.lake','.toolchain'}&set(p.parts)}
    assert physical=={p for p in expected if p.endswith('.lean')}, 'Current physical proof inventory drift'
    # Reuse the unchanged reviewed runtime classifier for the complete public
    # physical/untracked inventory, not only tracked files and Lean suffixes.
    weighted=importlib.import_module('point4_weighted_hessian_release_guard')
    with replacements(weighted.__dict__,{'public_paths':lambda:set(expected)}):
        weighted.check_inventory()
    assert json.loads((ROOT/MAP).read_text())==map_record(expected,originals,changes), 'Descriptive identity map drift'
    assert git('rev-parse','HEAD').decode().strip()==head
    return expected

@contextlib.contextmanager
def replacements(namespace, updates):
    global _owner,_depth
    if _depth:
        assert namespace is _owner, 'Nested callback ownership changed'
    originals={name:namespace[name] for name in updates}
    first=not _depth
    if first:_owner=namespace
    _depth+=1
    try:
        namespace.update(updates)
        yield
    finally:
        namespace.update(originals)
        _depth-=1
        if first:_owner=None

def weighted_leaf(namespace, schema=None):
    expected=verify_current()
    local=importlib.import_module('point4_c2_metric_localization_source_test')
    if schema:current_root_schema(schema,local)
    original_expected=namespace['expected_sources']
    original_helpers=namespace['historical_c2']
    touched=[]
    def helpers():
        module=original_helpers()
        before=module.check_imports,module.check_metadata
        touched.append((module,before))
        # These genuine functions keep their own exact INTEGRATION_PARENT blobs.
        module.check_imports=local.legacy_check_imports
        module.check_metadata=local.legacy_check_metadata
        return module
    def composed_sources():
        inherited=original_expected() # original ancestry/transform/self/workflow validation
        assert set(parent_tree(MASTER))-namespace['_composition_original_public_paths']()==WEIGHTED_MISSING
        for path,(_,data) in inherited.items():
            if path not in ROOT_CHANGES:
                assert blob_id(data)==expected[path][1], 'Inherited weighted reconstruction drift: '+path
        return {p:('current-finite-composition',(ROOT/p).read_bytes()) for p in expected}
    try:
        with replacements(namespace,{'expected_sources':composed_sources,
             'public_paths':lambda:set(expected),'historical_c2':helpers}):
            report=namespace['_composition_original_check_current'](schema)
        verify_current()
        if schema:current_root_schema(schema,local)
        return {'scope':'current master/smooth composition', 'public_paths':len(expected),
            'master_root_imports_provenance_validated':True,'canonical_point4':'OPEN','smooth_general_target':'OPEN',
            'lean_verified':False,'original_weighted_report_historical_inventory_shape_only':report}
    finally:
        for module,before in reversed(touched):module.check_imports,module.check_metadata=before

PATH_FLAGS={'--schema','--probe-log','--axiom-dir','--audit-json','--compile-log',
 '--evidence-dir','--smooth-probe-log','--smooth-completion-log','--smooth-audit-json','--baseline-repo','--manifest'}
def absolute_arguments(args):
    result=list(args)
    for i,value in enumerate(result):
        if value in PATH_FLAGS:
            assert i+1<len(result), 'Missing path argument'
            result[i+1]=str(pathlib.Path(result[i+1]).resolve())
        elif any(value.startswith(flag+'=') for flag in PATH_FLAGS):
            flag,path=value.split('=',1);result[i]=flag+'='+str(pathlib.Path(path).resolve())
    return result

def historical(commit,path,args):
    args=absolute_arguments(args)
    with tempfile.TemporaryDirectory(prefix='point4-composition-history-') as directory:
        target=pathlib.Path(directory)/'source'
        subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'worktree','add','--detach',str(target),commit],check=True,env=ENV)
        try:
            def verify():
                assert git('rev-parse','HEAD',root=target).decode().strip()==commit
                assert git('write-tree',root=target).strip()==git('rev-parse',commit+'^{tree}').strip()
                wanted=parent_tree(commit)
                assert parse_tree(git('ls-tree','-rz','HEAD',root=target))==wanted
                for p,(mode,oid) in wanted.items():
                    file=target/p;st=file.lstat().st_mode
                    for parent in file.parents:
                        assert stat.S_ISDIR(parent.lstat().st_mode)
                        if parent==target:break
                    assert stat.S_ISREG(st) and bool(st&0o111)==(mode=='100755')
                    assert blob_id(file.read_bytes())==oid
                assert not git('status','--porcelain','--untracked-files=all',root=target)
            verify()
            print('HISTORICAL_VALIDATOR_BEGIN',commit,path,flush=True)
            historical_args=list(args)
            if '--manifest' in historical_args:
                i=historical_args.index('--manifest')+1
                historical_args[i]=str(pathlib.Path(historical_args[i]).with_name(pathlib.Path(historical_args[i]).name+'.historical-'+commit+'.json'))
            elif any(a.startswith('--manifest=') for a in historical_args):
                i=next(i for i,a in enumerate(historical_args) if a.startswith('--manifest='))
                path_arg=pathlib.Path(historical_args[i].split('=',1)[1])
                historical_args[i]='--manifest='+str(path_arg.with_name(path_arg.name+'.historical-'+commit+'.json'))
            subprocess.run([sys.executable,'-B',str(target/path),*historical_args],cwd=target,check=True,env=ENV)
            verify()
            print('HISTORICAL_VALIDATOR_END',commit,path,flush=True)
        finally:
            subprocess.run(['git','--no-replace-objects','-C',str(ROOT),'worktree','remove',str(target)],check=True,env=ENV)

def evidence_parser(path):
    parser=argparse.ArgumentParser()
    if path.endswith('_mock_test.py'):return None
    common=['schema','axiom-dir','audit-json']
    if path.endswith('point4_manifold_heat_source_test.py'):
        common=['baseline-repo','probe-log']
    elif path.endswith('point4_manifold_heat_release_guard.py'):
        common+=['probe-log']
    for name in common:parser.add_argument('--'+name,type=pathlib.Path)
    if 'audit-json' in common:parser.add_argument('--audit-rc',type=int)
    return parser

def current_evidence(path,args):
    verify_current()
    parser=evidence_parser(path)
    if parser is None:return
    parsed=parser.parse_args(args)
    if getattr(parsed,'schema',None):current_root_schema(parsed.schema)
    module=importlib.import_module(pathlib.PurePosixPath(path).stem)
    inherited=module.c2_guard() if 'manifold_heat_release' in path else module
    if getattr(parsed,'axiom_dir',None):
        folder=parsed.axiom_dir
        if 'c2_initial' in path or 'manifold_heat_release' in path:
            assert {p.name for p in folder.iterdir()}=={p+'.log' for p in inherited.PROBES}
        total=0;distinct=set()
        for name in inherited.PROBES:
            source=(ROOT/f'curvature/scripts/point4_{name}_probe.lean').read_text()
            names=inherited.check_axiom_output(source,(folder/(name+'.log')).read_text())
            total+=len(names);distinct|=names
        assert total==(150 if 'c2_initial' in path or 'manifold_heat_release' in path else 127)
        if 'c2_initial' in path or 'manifold_heat_release' in path:assert len(distinct)==144
        inherited.check_boundaryless_types((folder/'boundaryless_chart_frames.log').read_text())
    if getattr(parsed,'audit_json',None):
        assert parsed.audit_rc is not None
        (module.c2_guard() if 'manifold_heat_release' in path else module).check_audit(json.loads(parsed.audit_json.read_text()),parsed.audit_rc)
    if getattr(parsed,'probe_log',None):
        function=module.check_new_probe if 'release_guard' in path else module.check_probe
        function(parsed.probe_log.read_text())

def current_root_schema(schema,local=None):
    local=local or importlib.import_module('point4_c2_metric_localization_source_test')
    raw=pathlib.Path(schema).read_bytes()
    assert sha256(raw)==local.SCHEMA_SHA256, 'Current root official schema digest drift'
    import jsonschema
    jsonschema.validate(local.strict_yaml((ROOT/'curvature/formalization.yaml').read_bytes()),json.loads(raw))

def weighted_current_inherited_evidence(namespace,args):
    parser=argparse.ArgumentParser()
    for name in ('schema','probe-log','compile-log','axiom-dir','audit-json','evidence-dir'):
        parser.add_argument('--'+name,type=pathlib.Path)
    parser.add_argument('--audit-rc',type=int)
    parsed=parser.parse_args(args)
    inherited=[]
    for name in ('schema','axiom-dir','audit-json','audit-rc'):
        value=getattr(parsed,name.replace('-','_'))
        if value is not None:
            inherited.extend(['--'+name,str(value.resolve()) if isinstance(value,pathlib.Path) else str(value)])
    path='curvature/scripts/point4_manifold_heat_release_guard.py'
    current_evidence(path,inherited)
    if parsed.evidence_dir:
        # The original direct weighted body also validates this directory and
        # its paths. Its requested manifold evidence must be checked currently.
        namespace['check_evidence_inventory'](parsed.evidence_dir)
        current_evidence(path,['--probe-log',str((parsed.evidence_dir/'manifold-probe.log').resolve())])

def current_smooth_evidence(namespace,args):
    parser=argparse.ArgumentParser()
    for name in ('schema','probe-log','axiom-dir','audit-json','smooth-probe-log',
                 'smooth-completion-log','smooth-audit-json'):
        parser.add_argument('--'+name,type=pathlib.Path)
    for name in ('audit-rc','smooth-completion-rc','smooth-audit-rc'):
        parser.add_argument('--'+name,type=int)
    parsed=parser.parse_args(args)
    inherited=[]
    for name in ('schema','probe-log','axiom-dir','audit-json','audit-rc'):
        value=getattr(parsed,name.replace('-','_'))
        if value is not None:inherited.extend(['--'+name,str(value)])
    current_evidence('curvature/scripts/point4_manifold_heat_release_guard.py',inherited)
    metadata=(ROOT/namespace['METADATA']).read_text()
    namespace['check_new_metadata'](metadata)
    if parsed.schema:
        import jsonschema
        raw=parsed.schema.read_bytes()
        guard=namespace['legacy']().c2_guard()
        assert sha256(raw)==guard.SCHEMA_SHA256
        jsonschema.validate(guard.parse_metadata(metadata),json.loads(raw))
    for path in (namespace['PROBE'],namespace['COMPLETION']):
        assert sha256((ROOT/path).read_bytes())==namespace['FILE_SHA256'][path]
    if parsed.smooth_probe_log:namespace['check_support_probe'](parsed.smooth_probe_log.read_text())
    assert (parsed.smooth_completion_log is None)==(parsed.smooth_completion_rc is None)
    if parsed.smooth_completion_log:
        namespace['check_completion_open'](parsed.smooth_completion_log.read_text(),parsed.smooth_completion_rc)
    assert (parsed.smooth_audit_json is None)==(parsed.smooth_audit_rc is None)
    if parsed.smooth_audit_json:
        namespace['check_smooth_audit_open'](json.loads(parsed.smooth_audit_json.read_text()),parsed.smooth_audit_rc)
    verify_current()

@contextlib.contextmanager
def weighted_execution(namespace):
    def historical_gate(path,args):
        print('HISTORICAL_WEIGHTED_BASE_BEGIN',namespace['BASE'],path,flush=True)
        namespace['_composition_original_historical_gate'](path,args)
        print('HISTORICAL_WEIGHTED_BASE_END',namespace['BASE'],path,flush=True)
    with replacements(namespace,{'check_current':lambda schema=None:weighted_leaf(namespace,schema),
                                 'historical_gate':historical_gate}):yield

def install_weighted(namespace):
    assert '_composition_original_main' not in namespace, 'Duplicate weighted composition installation'
    for name in ('main','run_inherited','check_current','public_paths','historical_gate'):
        namespace['_composition_original_'+name]=namespace[name]
    original_main=namespace['main'];original_run=namespace['run_inherited']
    @functools.wraps(original_run)
    def run(path,argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        current_evidence(path,args)
        with weighted_execution(namespace):original_run(path,args)
        current_evidence(path,args)
    @functools.wraps(original_main)
    def main(argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        weighted_current_inherited_evidence(namespace,args)
        with weighted_execution(namespace):result=original_main(args)
        weighted_current_inherited_evidence(namespace,args)
        return result
    namespace['run_inherited']=run;namespace['main']=main

def localization_current(namespace,schema):
    namespace['check_ancestry']()
    namespace['legacy_check_imports']((ROOT/'curvature/PoincareCurvature.lean').read_bytes())
    raw=(ROOT/'curvature/formalization.yaml').read_text()
    namespace['legacy_check_metadata'](raw)
    schema=pathlib.Path(schema)
    assert sha256(schema.read_bytes())==namespace['SCHEMA_SHA256']
    import jsonschema
    jsonschema.validate(namespace['strict_yaml'](raw),json.loads(schema.read_bytes()))
    for p in ('curvature/lean-toolchain','curvature/lakefile.toml','curvature/lake-manifest.json',
              'curvature/scripts/point4_audit.sh','curvature/scripts/point4_scan.py',
              'curvature/scripts/point4_target.txt','curvature/scripts/point4_closed_contract_source_test.py'):
        assert (ROOT/p).read_bytes()==namespace['blob'](namespace['INTEGRATION_PARENT'],p)
    assert (ROOT/'curvature/lean-toolchain').read_text()==namespace['TOOLCHAIN']
    scanner=ROOT/'curvature/scripts/point4_scan.py'
    result=subprocess.run([sys.executable,str(scanner),'locate','intrinsicLocalExistenceUniquenessFamily_pointFour',str(ROOT/namespace['PREFIX'])],capture_output=True)
    assert result.returncode!=0
    subprocess.run([sys.executable,str(ROOT/'curvature/scripts/point4_closed_contract_source_test.py')],check=True,env=ENV)
    cheats=subprocess.check_output([sys.executable,str(scanner),'cheats',str(ROOT/namespace['PREFIX'])],text=True)
    assert cheats.strip()=='TOTAL 0'

def install_localization(namespace):
    assert '_composition_original_main' not in namespace
    namespace['_composition_original_main']=namespace['main']
    def main(argv=None):
        parser=argparse.ArgumentParser()
        parser.add_argument('--schema',type=pathlib.Path,required=True);parser.add_argument('--manifest',type=pathlib.Path)
        args=absolute_arguments(sys.argv[1:] if argv is None else argv);parsed=parser.parse_args(args)
        verify_current();localization_current(namespace,parsed.schema)
        # Historical manifest output remains external and is not relabelled current.
        historical(LOCALIZATION,LOCAL,args)
        verify_current();localization_current(namespace,parsed.schema)
        if parsed.manifest:
            parsed.manifest.write_text(json.dumps({'candidate':git('rev-parse','HEAD').decode().strip(),
                'parents':[MASTER,SUPPORT],'source_only':True,'point4':'OPEN',
                'source_sha256':{p:sha256((ROOT/p).read_bytes()) for p in verify_current()}},indent=2)+'\n')
            verify_current()
    namespace['main']=main

def install_consistency(namespace):
    assert '_composition_original_main' not in namespace
    namespace['_composition_original_main']=namespace['main']
    def main():
        argparse.ArgumentParser().parse_args()
        verify_current();historical(MASTER,CONSISTENCY,[]);verify_current()
    namespace['main']=main

def install_smooth(namespace):
    assert '_composition_original_main' not in namespace
    original=namespace['main'];namespace['_composition_original_main']=original
    @functools.wraps(original)
    def main(argv=None):
        args=absolute_arguments(sys.argv[1:] if argv is None else argv)
        verify_current()
        print('CURRENT_SMOOTH_SEMANTIC_BODY_BEGIN: original inventory counters are historical shape; current identity is 1727 paths',flush=True)
        original(args) # current real smooth metadata/schema/probe/completion/audit gates
        print('CURRENT_SMOOTH_SEMANTIC_BODY_END',flush=True)
        historical(SUPPORT,SMOOTH,args) # original scoped route; no current hooks
        current_smooth_evidence(namespace,args)
        if any(a=='--smooth-audit-rc' or a.startswith('--smooth-audit-rc=') for a in args):
            # Retain the caller's observed auditor status, after both real routes
            # have validated it. The inherited artifact wildcard includes this log.
            output=pathlib.Path(tempfile.gettempdir())/'point4-smooth-forward-composition-inputs.log'
            output.write_text(json.dumps({'head':git('rev-parse','HEAD').decode().strip(),
                'validated_current_arguments':args,'source_only':True})+'\n')
    namespace['main']=main

def run_support_fixtures(argv):
    parser=argparse.ArgumentParser();parser.add_argument('--real-composed',action='store_true')
    parser.parse_args(argv)
    verify_current();historical(SUPPORT,FIXTURE,argv)
    subprocess.run([sys.executable,'-B',str(ROOT/TEST)],cwd=ROOT,check=True,env=ENV)
    verify_current()
