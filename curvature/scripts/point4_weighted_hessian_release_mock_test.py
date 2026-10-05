#!/usr/bin/env python3
"""Adversarial source-only fixtures. Synthetic outputs are never Lean evidence."""
import copy
from contextlib import contextmanager
import os
import py_compile
import subprocess
import sys
import pathlib
import tempfile
from unittest import mock
import stat
import unittest
import point4_weighted_hessian_release_guard as release

class WeightedHessianReleaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.baseline = release.baseline_sources()
        cls.expected = release.expected_sources()

    def test_all_inherited_bytes_modes_and_exact_adapters(self):
        adapters = release.adapters()
        self.assertEqual(sum(p.endswith('.py') for p in adapters), 7)
        self.assertEqual(sum(p.endswith('.yml') for p in adapters), 3)
        for path,(mode,original) in self.baseline.items():
            wanted = release.reconstruct_adapter(path,original) if path in adapters else original
            self.assertEqual((release.ROOT/path).read_bytes(),wanted)
            release.check_mode(path,(release.ROOT/path).lstat().st_mode,mode)
        for path,spec in adapters.items():
            original = self.baseline[path][1]
            actual = release.reconstruct_adapter(path,original)
            before,after = spec['before'].encode(),spec['after'].encode()
            self.assertEqual(actual.replace(after,before,1),original)
            for wrong in (original+b'\n',actual,original.replace(before,b'',1),original.replace(before,before*2,1)):
                with self.assertRaises(AssertionError): release.reconstruct_adapter(path,wrong)
            for wrong in (actual+b'\n',actual.replace(after,b'',1),actual.replace(after,after*2,1)):
                self.assertNotEqual(release.sha256(wrong),spec['transformed_sha256'])

    def test_startup_workflow_original_semantics_and_duplicate_rejection(self):
        for path,spec in release.adapters().items():
            if 'startup_job' not in spec: continue
            original = self.baseline[path][1]
            actual = release.reconstruct_adapter(path,original)
            self.assertEqual(actual.replace(b"    env:\n      PYTHONDONTWRITEBYTECODE: '1'\n",b'',1),original)
            wanted = release.parse_workflow(original.decode())
            wanted['jobs'][spec['startup_job']]['env']={'PYTHONDONTWRITEBYTECODE':'1'}
            self.assertEqual(release.parse_workflow(actual.decode()),wanted)
            for wrong in (actual.replace(b"PYTHONDONTWRITEBYTECODE: '1'",b"PYTHONDONTWRITEBYTECODE: '0'"), actual.replace(b"PYTHONDONTWRITEBYTECODE: '1'",b"PYTHONDONTWRITEBYTECODE: '1'\n      PYTHONDONTWRITEBYTECODE: '0'")):
                self.assertNotEqual(release.sha256(wrong),spec['transformed_sha256'])
            with self.assertRaises(AssertionError):
                release.parse_workflow(actual.decode().replace("PYTHONDONTWRITEBYTECODE: '1'","PYTHONDONTWRITEBYTECODE: '1'\n      PYTHONDONTWRITEBYTECODE: '0'",1))

    def test_real_startup_rejects_empty_hidden_stale_and_identical_caches_without_erasing(self):
        patch = release.git('diff','--binary',release.BASE)
        with tempfile.TemporaryDirectory(prefix='weighted-hessian-cache-fixture-') as parent:
            root = pathlib.Path(parent)/'source'
            subprocess.run(['git','-C',str(release.ROOT),'worktree','add','--detach',str(root),release.BASE],check=True,env=release.ENV,stdout=subprocess.DEVNULL)
            try:
                subprocess.run(['git','-C',str(root),'apply','--index','--binary','-'],input=patch,check=True,env=release.ENV)
                cache=root/'curvature/scripts/__pycache__'
                cache.mkdir()
                own=cache/('point4_c2_initial_heat_source_test.'+sys.implementation.cache_tag+'.pyc')
                for case in ('empty','hidden.lean','stale.pyc','identical-own-pyc'):
                    attack=None
                    if case=='hidden.lean':
                        attack=cache/'hidden.lean'; attack.write_bytes(b'axiom hidden : False\n')
                    elif case=='stale.pyc':
                        attack=own; attack.write_bytes(b'preexisting invalid cache')
                    elif case=='identical-own-pyc':
                        attack=own; py_compile.compile(str(root/'curvature/scripts/point4_c2_initial_heat_source_test.py'),cfile=str(attack),doraise=True)
                    before=attack.read_bytes() if attack else None
                    env=dict(os.environ)
                    workflow=release.parse_workflow((root/'.github/workflows/point4-linear-heat-geometry.yml').read_text())
                    env.update(workflow['jobs']['linear_heat_geometry']['env'])
                    result=subprocess.run([sys.executable,'curvature/scripts/point4_linear_heat_geometry_source_test.py'],cwd=root,env=env,capture_output=True,text=True,timeout=180)
                    with self.subTest(case=case):
                        self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)
                        self.assertIn('Interpreter cache forbidden:',result.stderr)
                        self.assertTrue(cache.is_dir())
                        if attack: self.assertEqual(attack.read_bytes(),before,'Gate erased rejected cache evidence')
                    if attack: attack.unlink()
                cache.rmdir()
            finally:
                subprocess.run(['git','-C',str(release.ROOT),'worktree','remove','--force',str(root)],check=True,env=release.ENV)

    def test_exact_import_and_helper_preamble_edits_preserve_all_math_bytes(self):
        for path,spec in release.source_transformations().items():
            original = (release.ROOT/spec['original_path']).read_bytes()
            actual = release.reconstruct_module(path,original)
            self.assertEqual(actual,(release.ROOT/path).read_bytes())
            for wrong in (original+b'\n',original.replace(b'namespace RicciFlow',b'namespace Wrong',1),original.replace(b' := by',b' := sorry',1)):
                if wrong != original:
                    with self.assertRaises(AssertionError): release.reconstruct_module(path,wrong)
        helper = release.PREFIX+'WeightedDuhamelIntegrand.lean'
        original=(release.ROOT/release.source_transformations()[helper]['original_path']).read_bytes()
        self.assertFalse(original.startswith(b'module'))
        actual=(release.ROOT/helper).read_bytes()
        self.assertTrue(actual.startswith(b'module\n\npublic import '))
        self.assertIn(b'\n@[expose] public noncomputable section\n',actual)
        for before,after in reversed(release.MODULE_COMPATIBILITY_EDITS[helper]):
            actual=actual.replace(after.encode(),before.encode(),1)
        # The first reviewed import qualification remains exactly reversible.
        actual=actual.replace(b'import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedHessianTimeEnvelope\n',b'import WeightedHessianTimeEnvelope\n',1)
        self.assertEqual(actual,original)

    def test_module_compatibility_allowlist_rejects_missing_extra_or_changed_edits(self):
        specs=release.source_transformations()
        for path,allowed in release.MODULE_COMPATIBILITY_EDITS.items():
            original=(release.ROOT/specs[path]['original_path']).read_bytes()
            for mutate in ('missing','changed','extra'):
                wrong=copy.deepcopy(specs)
                target=wrong[path]['transformations']
                if mutate=='missing': target.pop()
                elif mutate=='changed': target[-1]['after']+='-- unreviewed change\n'
                else: target.append({'before':'namespace RicciFlow\n','after':'namespace Unreviewed\n','count':1})
                with self.subTest(path=path,mutate=mutate),mock.patch.object(release,'source_transformations',return_value=wrong):
                    with self.assertRaises(AssertionError): release.reconstruct_module(path,original)

    def test_real_project_module_graph_rejects_legacy_cycles_and_hidden_imports(self):
        sources={p:data for p,(_,data) in self.expected.items() if p.endswith('.lean')}
        report=release.check_module_import_graph(sources)
        self.assertEqual(report['project_legacy_imports'],0)
        self.assertGreater(report['project_modules'],9)
        self.assertGreater(report['project_import_edges'],9)
        helper=release.PREFIX+'WeightedDuhamelIntegrand.lean'
        integral=release.PREFIX+'WeightedDuhamelHessianIntegral.lean'
        regularizer=release.PREFIX+'EuclideanHeatRegularizerC2Trace.lean'
        modern=release.PREFIX+'EuclideanHeatHessian.lean'
        attacks=(
            (helper,sources[helper].replace(b'module\n',b'-- module\n',1)),
            (modern,sources[modern].replace(b'module\n',b'',1)),
            (regularizer,sources[regularizer].replace(b'.EuclideanHeatFrechet\n',b'.EuclideanHeatInitialTrace\n',1)),
            (helper,sources[helper]+b'\npublic import '+integral.removeprefix('curvature/').removesuffix('.lean').replace('/','.').encode()+b'\n'),
            (helper,sources[helper]+b'\npublic import PoincareCurvature.HiddenTarget\n'),
            (modern,sources[modern].replace(b'public import ',b'import ',1)),
        )
        for path,data in attacks:
            wrong=dict(sources);wrong[path]=data
            with self.subTest(path=path,data=data[:30]),self.assertRaises(AssertionError):
                release.check_module_import_graph(wrong)
        comments=dict(sources);comments[helper]+=b'\n/- public import PoincareCurvature.HiddenTarget -/\n'
        self.assertEqual(release.check_module_import_graph(comments),report)

    def test_every_current_union_path_is_required_and_extras_rejected(self):
        valid = release.public_paths()
        release.check_public_paths(valid)
        for path in valid:
            with self.assertRaises(AssertionError): release.check_public_paths(valid-{path})
        for path in ('CanonicalTarget.lean','extra.txt','.github/workflows/hidden.yml','pending/WeightedStrongTrace.lean','odd\nname'):
            with self.assertRaises(AssertionError): release.check_public_paths(valid|{path})

    def test_duplicate_yaml_and_metadata_drift_rejected(self):
        workflow = (release.ROOT/release.WORKFLOW).read_text()
        release.parse_workflow(workflow)
        for original,wrong in [('contents: read','contents: read\n  contents: write'),('build: false','build: false\n          build: true'),('timeout-minutes: 350','timeout-minutes: 350\n    timeout-minutes: 1')]:
            with self.assertRaises(AssertionError): release.parse_workflow(workflow.replace(original,wrong,1))
        metadata=(release.ROOT/release.METADATA).read_text()
        release.check_metadata(metadata)
        for wrong in (metadata+'\n',metadata.replace('review:\n  status: "pending"','review:\n  status: "approved"'),metadata.replace('version: "v0.4"','version: "v0.4"\nversion: "v0.3"'),metadata.replace('relationship: "builds-on"','relationship: "formalizes"',1)):
            with self.assertRaises(AssertionError): release.check_metadata(wrong)

    def test_actual_probe_axioms_complete_types_and_rank_zero_rejections(self):
        source=(release.ROOT/release.PROBE).read_text()
        names=release.historical_c2().probe_names(source)
        output='\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
        output+='\nWEIGHTED_HESSIAN_TYPES_BEGIN\n'+'\n'.join(names)+'\nIntervalIntegrable Continuous BoundedContinuousFunction Fin n heatDuhamelHessianEntryND heatHessianEntryHolderMoment LittleWeightedSpatialHolder Tendsto fderiv UniformContinuous\nWEIGHTED_HESSIAN_TYPES_END\n'
        rank_names = release.re.findall(r'^#check @(\S+) 0$',source,release.re.M)
        output+='WEIGHTED_HESSIAN_RANK_ZERO_BEGIN\n'+'\n'.join(rank_names)+' Fin 0\nWEIGHTED_HESSIAN_RANK_ZERO_END\n'
        release.check_probe(output)
        for name in rank_names:
            prefix,rank=output.split('WEIGHTED_HESSIAN_RANK_ZERO_BEGIN')
            with self.assertRaises(AssertionError): release.check_probe(prefix+'WEIGHTED_HESSIAN_RANK_ZERO_BEGIN'+rank.replace(name,'MISSING',1))
        for wrong in (output.replace('Quot.sound','sorryAx',1),output+"\n'Unknown.theorem' does not depend on any axioms",output.replace(names[0],names[1],1),output.replace('WEIGHTED_HESSIAN_TYPES_END','MISSING'),output.replace('Fin 0','Fin 1'),output+'\nerror: probe failed'):
            with self.assertRaises(AssertionError): release.check_probe(wrong)

    def test_exact_evidence_inventory_missing_extra_empty_and_symlink_rejections(self):
        with tempfile.TemporaryDirectory() as parent:
            root=pathlib.Path(parent)/'evidence'; root.mkdir()
            for name in release.EVIDENCE_PATHS:
                path=root/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(b'fixture only')
            release.check_evidence_inventory(root)
            for name in release.EVIDENCE_PATHS:
                path=root/name; data=path.read_bytes(); path.unlink()
                with self.assertRaises(AssertionError): release.check_evidence_inventory(root)
                path.write_bytes(data)
            for name in ('extra.log','hidden.lean','__pycache__/stale.pyc','inherited-probes/extra.log'):
                path=root/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(b'fixture only')
                with self.assertRaises(AssertionError): release.check_evidence_inventory(root)
                path.unlink()
                if path.parent.name=='__pycache__': path.parent.rmdir()
            empty=root/'unexplained'; empty.mkdir()
            with self.assertRaises(AssertionError): release.check_evidence_inventory(root)
            empty.rmdir()
            alias=pathlib.Path(parent)/'alias'; alias.symlink_to(root,target_is_directory=True)
            with self.assertRaises(AssertionError): release.check_evidence_inventory(alias)
            alias.unlink()
            path=root/'probe.log'; path.unlink(); path.symlink_to(root/'source.log')
            with self.assertRaises(AssertionError): release.check_evidence_inventory(root)
            path.unlink(); path.write_bytes(b'fixture only')
            release.check_evidence_inventory(root)

    def test_compile_receipt_must_name_every_new_unit_and_exact_head(self):
        sha='a'*40
        modules=[p.removeprefix('curvature/').removesuffix('.lean').replace('/','.') for p in release.source_transformations()]
        valid='WEIGHTED_HESSIAN_COMPILED '+sha+' '+' '.join(modules)
        release.check_compile_receipt(valid,sha)
        for wrong in (valid.replace(modules[0],'',1),valid.replace(sha,'b'*40),valid+'\n'+valid,valid+'\nfailed'):
            with self.assertRaises(AssertionError): release.check_compile_receipt(wrong,sha)

    def test_exact_tracked_untracked_ignored_inventory_and_caches(self):
        valid = release.public_paths()
        baseline = set(self.baseline)
        additions = valid - baseline
        release.check_inventory_sets(valid, set(), valid)
        release.check_inventory_sets(baseline, additions, valid)
        release.check_inventory_sets(valid, {'curvature/.lake/build/lib/Foo.olean'}, valid)
        for path in valid:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid - {path}, set(), valid - {path})
        bad_paths = ('extra.lean', 'extra.txt', '.github/workflows/unknown.yml',
                     '__pycache__/scan.cpython-311.pyc', '__pycache__/hidden.lean',
                     'curvature/scripts/__pycache__/scan.cpython-311.pyc',
                     'ignored/new-target.lean', 'curvature/.toolchain/hidden.lean',
                     'other/.lake/cache.olean', 'name\nwith-newline.bin',
                     'curvature/.lake/hidden.lean', 'curvature/.lake/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/Hidden.lean',
                     'curvature/.lake/__pycache__/hidden.cpython-311.pyc',
                     'curvature/.lake/packages/mathlib/Unpinned.lean',
                     'curvature/PoincareCurvature/CanonicalTarget.lean')
        for path in bad_paths:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid | {path}, set(), valid | {path})
            with self.subTest(untracked=path), self.assertRaises(AssertionError):
                release.check_inventory_sets(valid, {path}, valid | {path})
        with self.assertRaises(AssertionError):
            release.check_inventory_sets(valid | {'curvature/.lake/hidden.lean'}, set(), valid)
        with self.assertRaises(AssertionError):
            release.check_inventory_sets(valid, {release.MODULE}, valid)
        self.assertEqual(release.nul_paths(b'one\ntwo\0three\0'), {'one\ntwo', 'three'})
        for wrong in (b'not terminated', b'dup\0dup\0', b'\0', b'one\0\0'):
            with self.assertRaises(AssertionError):
                release.nul_paths(wrong)

    def test_real_physical_ignored_files_caches_symlinks_and_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'base.lean').write_text('base')
            (root / 'guard.py').write_text('guard')
            def identity(data):
                return release.hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest().encode()
            records = b'100644 ' + identity(b'base') + b' 0\tbase.lean\0'
            records += b'100644 ' + identity(b'guard') + b' 0\tguard.py\0'
            def fake_git(*args):
                return records if args == ('ls-files', '--stage', '-z') else b''
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value={'base.lean': ('100644', b'base')}), \
                 mock.patch.object(release, 'UNIT_FILE_SHA256', {}), \
                 mock.patch.object(release, 'SELF_PATHS', {'guard.py'}), \
                 mock.patch.object(release, 'git', side_effect=fake_git):
                release.check_inventory()
                for name in ('curvature/.lake/hidden.lean', 'curvature/.lake/CanonicalTarget.lean',
                             'curvature/.lake/build/lib/Hidden.lean',
                             'curvature/.lake/__pycache__/hidden.cpython-311.pyc',
                             'curvature/.lake/packages/mathlib/Unpinned.lean',
                             'hamilton-ivey-reaction/.lake/build/Hidden.lean'):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b'arbitrary hidden source or cache')
                    with self.subTest(hidden=name), self.assertRaises(AssertionError):
                        release.check_inventory()
                    path.unlink()
                    while path.parent != root and not any(path.parent.iterdir()):
                        parent = path.parent
                        parent.rmdir()
                        path = parent
                for name in ('ignored.lean', 'hidden.txt', 'odd\nname.bin'):
                    path = root / name
                    path.write_bytes(b'extra')
                    with self.subTest(name=name), self.assertRaises(AssertionError):
                        release.check_inventory()
                    path.unlink()
                cache = root / '__pycache__'
                cache.mkdir()
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                cache.rmdir()
                (root / 'linked').symlink_to(root, target_is_directory=True)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'linked').unlink()
                original = (root / 'guard.py').read_bytes()
                (root / 'guard.py').unlink()
                (root / 'guard.py').symlink_to(root / 'base.lean')
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'guard.py').unlink()
                (root / 'guard.py').write_bytes(original)
                (root / 'guard.py').chmod(0o755)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                (root / 'guard.py').chmod(0o644)
                release.check_inventory()
                (root / 'guard.py').write_bytes(b'unstaged different bytes')
                with self.assertRaises(AssertionError):
                    release.check_inventory()

    def test_bounded_runtime_outputs_and_path_dependency_build_root(self):
        valid = release.public_paths()
        outputs = ('curvature/.lake/build/lib/lean/Foo.olean',
                   'curvature/.lake/build/lib/lean/Foo.olean.private',
                   'curvature/.lake/build/lib/lean/Foo.olean.server',
                   'curvature/.lake/build/ir/Foo.c.o.export',
                   'curvature/.lake/config/1/lakefile.olean.lock',
                   'curvature/.lake/build/bin/cache',
                   'hamilton-ivey-reaction/.lake/build/ir/HamiltonIveyReaction.c',
                   'curvature/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean')
        for path in outputs:
            self.assertTrue(release.generated_build_path(path), path)
        release.check_inventory_sets(valid, set(outputs), valid)
        for path in ('curvature/.lake/hidden.txt', 'curvature/.lake/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/CanonicalTarget.lean',
                     'curvature/.lake/build/lib/__pycache__/x.cpython-311.pyc',
                     'curvature/.lake/packages/unknown/.lake/build/lib/Foo.olean',
                     'curvature/.lake/packages/mathlib/Unpinned.lean'):
            self.assertFalse(release.generated_build_path(path), path)

    def test_dependency_pinned_head_blob_mode_and_symlink_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            package = root / 'curvature/.lake/packages/mathlib'
            package.mkdir(parents=True)
            (package / '.git').mkdir()
            (package / 'Known.lean').write_bytes(b'known source')
            (package / 'Pinned.py').symlink_to('Known.lean')
            revision = 'c' * 40
            manifest = {'packagesDir': '.lake/packages', 'packages': [
                {'type': 'git', 'name': 'mathlib', 'rev': revision}]}
            tree = ('100644 blob ' + release.git_blob_identity(b'known source') + '\tKnown.lean\0'
                    + '120000 blob ' + release.git_blob_identity(b'Known.lean') + '\tPinned.py\0').encode()
            def package_git(path, *args):
                return (revision + '\n').encode() if args == ('rev-parse', 'HEAD') else tree
            baseline = {'curvature/lake-manifest.json': ('100644', release.json.dumps(manifest).encode())}
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'git_at', side_effect=package_git):
                sources, git_roots = release.dependency_inventory()
                self.assertEqual(sources, {'curvature/.lake/packages/mathlib/Known.lean',
                                           'curvature/.lake/packages/mathlib/Pinned.py'})
                self.assertEqual(git_roots, {'curvature/.lake/packages/mathlib/.git'})
                (package / 'Known.lean').write_bytes(b'wrong source')
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
                (package / 'Known.lean').write_bytes(b'known source')
                (package / 'Known.lean').chmod(0o755)
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
                (package / 'Known.lean').chmod(0o644)
                (package / 'Pinned.py').unlink()
                (package / 'Pinned.py').symlink_to('different target')
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'git_at', return_value=b'wrong-head\n'):
                with self.assertRaises(AssertionError):
                    release.dependency_inventory()

    @contextmanager
    def fingerprint_fixture(self):
        # Physical candidate with a synthetic pinned source, no compiler/cache
        # download. Only the fixture's source identity/size are substituted.
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            package = root / 'curvature/.lake/packages/proofwidgets'
            (package / 'widget').mkdir(parents=True)
            (package / '.git').mkdir()
            lock = root / release.PROOFWIDGETS_LOCK
            source = b'verified synthetic lockfile\n'
            lock.write_bytes(source)
            fingerprint = root / release.PROOFWIDGETS_FINGERPRINT
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            manifest = {'packagesDir': '.lake/packages', 'packages': [{
                'name': 'proofwidgets', 'type': 'git', 'rev': release.PROOFWIDGETS_REV,
                'url': 'https://github.com/leanprover-community/ProofWidgets4'}]}
            baseline = {'base.lean': ('100644', b'base'),
                        'curvature/lake-manifest.json': ('100644', release.json.dumps(manifest).encode())}
            for name, (_, data) in baseline.items():
                (root / name).write_bytes(data)
            (root / 'guard.py').write_bytes(b'guard')
            records = b''.join(('100644 ' + release.git_blob_identity(data) + ' 0\t' + name + '\0').encode()
                               for name, data in {**{p: d for p, (_, d) in baseline.items()}, 'guard.py': b'guard'}.items())
            tree = ('100644 blob ' + release.git_blob_identity(source) + '\twidget/package-lock.json\0').encode()
            def root_git(*args):
                return records if args == ('ls-files', '--stage', '-z') else b'curvature/.lake/packages/proofwidgets/\0'
            def package_git(path, *args):
                self.assertEqual(path, package)
                return (release.PROOFWIDGETS_REV + '\n').encode() if args == ('rev-parse', 'HEAD') else tree
            with mock.patch.object(release, 'ROOT', root), \
                 mock.patch.object(release, 'baseline_sources', return_value=baseline), \
                 mock.patch.object(release, 'UNIT_FILE_SHA256', {}), \
                 mock.patch.object(release, 'SELF_PATHS', {'guard.py'}), \
                 mock.patch.object(release, 'PROOFWIDGETS_LOCK_SIZE', len(source)), \
                 mock.patch.object(release, 'PROOFWIDGETS_LOCK_BLOB', release.git_blob_identity(source)), \
                 mock.patch.object(release, 'git', side_effect=root_git), \
                 mock.patch.object(release, 'git_at', side_effect=package_git):
                release.check_inventory()
                yield root, lock, fingerprint, source, baseline
                release.check_inventory()

    def test_exact_verified_fingerprint_rejects_bad_oversized_and_wrong_hash(self):
        with self.fingerprint_fixture() as (_, _, fingerprint, _, _):
            cases = (b'', b'0' * 15, b'0' * 17, b'0' * 65536,
                     b'0' * 16, b'g' * 16, b'179E66574F04806E',
                     release.PROOFWIDGETS_LOCK_HASH + b'\n', b'\0' * 16)
            for wrong in cases:
                fingerprint.write_bytes(wrong)
                with self.subTest(size=len(wrong)), self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertEqual(fingerprint.read_bytes(), wrong, 'Gate changed rejected fingerprint evidence')
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            self.assertFalse(release.generated_build_path(release.PROOFWIDGETS_FINGERPRINT))
            sources, _ = release.dependency_inventory()
            self.assertEqual(release.runtime_fingerprints(sources), {release.PROOFWIDGETS_FINGERPRINT})
            with self.assertRaises(AssertionError):
                release.runtime_fingerprints(set())

    def test_exact_verified_fingerprint_rejects_symlink_directory_and_mode_drift(self):
        with self.fingerprint_fixture() as (_, lock, fingerprint, source, _):
            fingerprint.unlink()
            for target in (lock, fingerprint.parent / 'missing'):
                fingerprint.symlink_to(target)
                with self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertTrue(fingerprint.is_symlink())
                fingerprint.unlink()
            fingerprint.mkdir()
            with self.assertRaises(AssertionError):
                release.check_inventory()
            fingerprint.rmdir()
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            fingerprint.chmod(0o755)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            fingerprint.chmod(0o644)
            lock.unlink()
            lock.symlink_to(fingerprint)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            lock.unlink()
            lock.write_bytes(source)
            lock.chmod(0o755)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            lock.chmod(0o644)

    def test_exact_verified_fingerprint_rejects_parent_source_head_and_manifest_drift(self):
        with self.fingerprint_fixture() as (_, lock, fingerprint, source, baseline):
            lock.write_bytes(source.replace(b'verified', b'modified'))
            with self.assertRaises(AssertionError):
                release.check_inventory()
            self.assertNotEqual(lock.read_bytes(), source)
            lock.write_bytes(source)
            with mock.patch.object(release, 'git_at', return_value=b'wrong-head\n'), self.assertRaises(AssertionError):
                release.check_inventory()
            sources, _ = release.dependency_inventory()
            for field, value in (('rev', 'a' * 40), ('url', 'https://example.invalid/ProofWidgets4'),
                                 ('name', 'wrong-package'), ('type', 'path')):
                wrong = copy.deepcopy(release.json.loads(baseline['curvature/lake-manifest.json'][1]))
                wrong['packages'][0][field] = value
                altered = dict(baseline)
                altered['curvature/lake-manifest.json'] = ('100644', release.json.dumps(wrong).encode())
                with mock.patch.object(release, 'baseline_sources', return_value=altered), self.assertRaises(AssertionError):
                    release.runtime_fingerprints(sources)
            widget = lock.parent
            renamed = widget.with_name('displaced-widget')
            widget.rename(renamed)
            widget.symlink_to(renamed, target_is_directory=True)
            with self.assertRaises(AssertionError):
                release.check_inventory()
            widget.unlink()
            renamed.rename(widget)
            self.assertEqual(fingerprint.read_bytes(), release.PROOFWIDGETS_LOCK_HASH)

    def test_fingerprint_does_not_admit_other_paths_hidden_lean_or_caches(self):
        with self.fingerprint_fixture() as (root, _, fingerprint, _, _):
            paths = (
                'curvature/.lake/packages/proofwidgets/widget/package.json.hash',
                'curvature/.lake/packages/proofwidgets/widget/package-lock.json.hash.extra',
                'curvature/.lake/packages/proofwidgets/widget/other/package-lock.json.hash',
                'curvature/.lake/packages/mathlib/widget/package-lock.json.hash',
                'hamilton-ivey-reaction/.lake/packages/proofwidgets/widget/package-lock.json.hash',
                'curvature/.lake/packages/proofwidgets/widget/Hidden.lean',
                'curvature/.lake/packages/proofwidgets/widget/__pycache__/hidden.lean',
                'curvature/.lake/packages/proofwidgets/widget/stale.pyc',
                'curvature/.lake/packages/proofwidgets/.lake/build/Hidden.lean',
            )
            for name in paths:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
                with self.subTest(path=name), self.assertRaises(AssertionError):
                    release.check_inventory()
                self.assertEqual(path.read_bytes(), release.PROOFWIDGETS_LOCK_HASH)
                path.unlink()
                while path.parent != root and not any(path.parent.iterdir()):
                    parent = path.parent
                    parent.rmdir()
                    path = parent
            fingerprint.unlink()
            release.check_inventory()  # Sidecar is optional before Lake writes it.
            fingerprint.write_bytes(release.PROOFWIDGETS_LOCK_HASH)
            public = release.public_paths()
            with self.assertRaises(AssertionError):
                release.check_inventory_sets(public | {release.PROOFWIDGETS_FINGERPRINT}, set(), public)
            with self.assertRaises(AssertionError):
                release.check_inventory_sets(public, set(), public, fingerprints={'other.hash'})

    def test_physical_lean_union_no_ignored_or_hidden_canonical_target(self):
        valid = {path for path in release.public_paths() if path.endswith('.lean')}
        release.check_physical_lean(valid)
        for path in valid:
            with self.subTest(path=path), self.assertRaises(AssertionError):
                release.check_physical_lean(valid - {path})
        for path in ('ignored/hidden.lean', '__pycache__/hidden.lean', 'CanonicalTarget.lean'):
            with self.assertRaises(AssertionError):
                release.check_physical_lean(valid | {path})

    def test_regular_file_modes_reject_symlink_and_executable_drift(self):
        release.check_mode('plain', stat.S_IFREG | 0o644, '100644')
        release.check_mode('script', stat.S_IFREG | 0o755, '100755')
        for mode, wanted in ((stat.S_IFLNK | 0o777, '100644'), (stat.S_IFDIR | 0o755, '100644'),
                             (stat.S_IFREG | 0o755, '100644'), (stat.S_IFREG | 0o644, '100755')):
            with self.subTest(mode=mode, wanted=wanted), self.assertRaises(AssertionError):
                release.check_mode('path', mode, wanted)
        release.check_modes()


if __name__ == '__main__':
    unittest.main()
