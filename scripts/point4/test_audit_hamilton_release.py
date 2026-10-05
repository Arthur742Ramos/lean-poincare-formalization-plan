"""Small source-scheduler tests; no Lean build, network, or object cache."""
import importlib.util
import pathlib
import threading
import time
import unittest

spec = importlib.util.spec_from_file_location(
    "hamilton_audit", pathlib.Path(__file__).with_name("audit-hamilton-release.py"))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class DependencyReadyTests(unittest.TestCase):
    def test_each_source_once_after_imports_with_two_worker_bound(self):
        order = ["A", "B", "C", "D", "E"]
        graph = {"A": ["Mathlib.X"], "B": [], "C": ["A"],
                 "D": ["A", "B"], "E": ["C", "D"]}
        lock = threading.Lock()
        finished, calls = set(), []
        active, peak = 0, 0

        def build(module):
            nonlocal active, peak
            with lock:
                self.assertTrue((set(graph[module]) & set(order)) <= finished)
                calls.append(module)
                active += 1
                peak = max(peak, active)
            time.sleep(0.005)
            with lock:
                active -= 1
            return 0, 0.005, None

        def completed(module, result):
            self.assertEqual(result[0], 0)
            with lock:
                finished.add(module)

        self.assertIsNone(audit.dependency_ready_build(
            order, graph, build, completed, jobs=2))
        self.assertEqual(sorted(calls), sorted(order))
        self.assertEqual(len(calls), len(order))
        self.assertEqual(finished, set(order))
        self.assertLessEqual(peak, 2)

    def test_failure_stops_new_children_and_retains_running_result(self):
        calls, results = [], []
        order = ["Bad", "Independent", "Child"]
        graph = {"Bad": [], "Independent": [], "Child": ["Bad"]}

        def build(module):
            calls.append(module)
            time.sleep(0.005 if module == "Bad" else 0.02)
            return (7 if module == "Bad" else 0), 0.01, None

        failure = audit.dependency_ready_build(
            order, graph, build, lambda m, r: results.append((m, r[0])), jobs=2)
        self.assertEqual(failure, ("Bad", 7))
        self.assertEqual(set(calls), {"Bad", "Independent"})
        self.assertEqual(set(results), {("Bad", 7), ("Independent", 0)})

    def test_serial_fallback_and_cycle_are_not_certified(self):
        order = ["A", "B"]
        calls = []
        self.assertIsNone(audit.dependency_ready_build(
            order, {"A": [], "B": ["A"]},
            lambda m: (calls.append(m) or 0, 0, None), lambda m, r: None, jobs=1))
        self.assertEqual(calls, order)
        with self.assertRaises(AssertionError):
            audit.dependency_ready_build(
                order, {"A": ["B"], "B": ["A"]},
                lambda m: (0, 0, None), lambda m, r: None, jobs=2)

    def test_resource_guard_cannot_silently_skip_source(self):
        with self.assertRaises(RuntimeError):
            audit.dependency_ready_build(
                ["A"], {"A": []}, lambda m: (0, 0, None),
                lambda m, r: None, jobs=2, can_launch=lambda active: False)



class ChainBatchTests(unittest.TestCase):
    def test_chain_cover_and_off_batch_dependencies_bound_compilers(self):
        order = ["A", "B", "C", "D", "E", "F", "G", "H"]
        graph = {"A": [], "B": [], "C": ["A"], "D": ["A"],
                 "E": ["B", "C"], "F": ["D", "E"], "G": [], "H": ["F", "G"]}
        for jobs in (1, 2):
            built = set()
            batches = audit.chain_batches(order, graph, jobs)
            for batch in batches:
                self.assertLessEqual(len(batch["chains"]), jobs)
                flattened = [m for chain in batch["chains"] for m in chain]
                self.assertEqual(set(flattened), set(batch["modules"]))
                self.assertEqual(len(flattened), len(batch["modules"]))
                for chain in batch["chains"]:
                    for first, second in zip(chain, chain[1:]):
                        self.assertIn(first, graph[second])
                for module in batch["modules"]:
                    self.assertTrue(set(graph[module]) <= built)
                    built.add(module)
            self.assertEqual(built, set(order))
            self.assertLess(len(batches), len(order))

    def test_cyclic_incomplete_and_unknown_graph_cannot_pass(self):
        for order, graph in [(["A"], {"A": ["A"]}),
                             (["A"], {"A": ["Missing"]}),
                             (["A", "A"], {"A": []}), (["A"], {})]:
            with self.assertRaises(AssertionError):
                audit.chain_batches(order, graph, 2)

    def test_fresh_project_objects_but_official_dependency_objects_allowed(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            path = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
            path.parent.mkdir(parents=True)
            path.touch()
            self.assertEqual(audit.assert_no_project_objects(root), [])
            for relative in ("DifferentialGeometry/X.olean", ".lake/build/lib/lean/X.olean.private", "DifferentialGeometry.olean"):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.touch()
                with self.assertRaises(AssertionError):
                    audit.assert_no_project_objects(root)
                path.unlink()


class CompilerObserverTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        spec = importlib.util.spec_from_file_location(
            "hamilton_observer", pathlib.Path(__file__).with_name("observe-hamilton-compiler.py"))
        self.observer = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.observer)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.evidence = self.root / "evidence"
        for name in ("compiler-records", "module-build-logs", "module-setups"):
            (self.evidence / name).mkdir(parents=True)
        self.module = "DifferentialGeometry.Γ"
        self.source = self.root / "DifferentialGeometry/Γ.lean"
        self.source.parent.mkdir()
        self.source.write_text("theorem actual : True := True.intro\n")
        self.compiler = self.root / "official/bin/lean"
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_text("mock pinned compiler identity\n")
        self.control = {"root": str(self.root), "evidence": str(self.evidence),
                        "compiler": str(self.compiler), "sysroot": str(self.compiler.parent.parent),
                        "compiler_sha256": self.observer.digest(self.compiler), "jobs": 2,
                        "allowed_modules": [self.module], "modules": {
                            self.module: {"position": 1, "source_sha256": self.observer.digest(self.source),
                                          "project_imports": []}}}
        stem = self.module.replace(".", "/")
        self.olean = self.root / f".lake/build/lib/lean/{stem}.olean"
        self.setup = self.root / f".lake/build/ir/{stem}.setup.json"
        self.olean.parent.mkdir(parents=True)
        self.setup.parent.mkdir(parents=True)
        self.setup.write_text('{"name":"' + self.module + '","options":{"autoImplicit":false}}\n')
        self.args = [str(self.source.relative_to(self.root)), "-o", str(self.olean),
                     "-i", str(self.olean.with_suffix(".ilean")), "-c", str(self.setup.with_suffix("").with_suffix(".c")),
                     "--setup", str(self.setup), "--json"]

    def fake_run(self, command, **kwargs):
        from types import SimpleNamespace
        self.assertEqual(command, [str(self.compiler), *self.args])
        self.assertEqual(kwargs["cwd"], str(self.root))
        self.assertEqual(kwargs["env"]["LEAN_SYSROOT"], self.control["sysroot"])
        self.olean.write_bytes(b"actual mock compiler object")
        return SimpleNamespace(returncode=0, stdout=b"", stderr=b"")

    def invoke(self, run=None, acquire=None):
        return self.observer.observe(self.control, self.args, cwd=self.root,
                                     run=run or self.fake_run,
                                     acquire=acquire or (lambda control: None))

    def record(self):
        import json
        return json.loads((self.evidence / "compiler-records/0001.json").read_text())

    def test_actual_argv_setup_source_and_result_are_preserved(self):
        before = self.setup.read_bytes()
        self.assertEqual(self.invoke(), 0)
        result = self.record()
        self.assertEqual(result["argv"], self.args)
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["status"], "finished")
        self.assertEqual(result["setup_sha256"], self.observer.digest(self.setup))
        self.assertEqual(self.setup.read_bytes(), before)
        self.assertEqual(set(audit.compiler_records(self.evidence, self.control["modules"], required=True)), {self.module})

    def test_real_nonzero_and_signal_exit_are_not_fabricated(self):
        from types import SimpleNamespace
        for code in (7, -9):
            with self.subTest(code=code):
                self.assertEqual(self.invoke(run=lambda *a, **k: SimpleNamespace(returncode=code, stdout=b"", stderr=b"")), code)
                self.assertEqual(self.record()["exit_code"], code)
                with self.assertRaises(AssertionError):
                    audit.compiler_records(self.evidence, self.control["modules"], required=True)
                (self.evidence / "compiler-records/0001.json").unlink()
                (self.evidence / "compiler-records/0001.reserved").unlink()
                (self.evidence / "compiler-stop.json").unlink()

    def test_fake_success_missing_object_and_timeout_fail_closed(self):
        from types import SimpleNamespace
        import subprocess
        failures = [lambda *a, **k: SimpleNamespace(returncode=0, stdout=b"", stderr=b""),
                    lambda *a, **k: (_ for _ in ()).throw(subprocess.TimeoutExpired("mock", 1))]
        for run in failures:
            with self.assertRaises((AssertionError, subprocess.TimeoutExpired)):
                self.invoke(run=run)
            self.assertEqual(self.record()["status"], "inconclusive")
            with self.assertRaises(AssertionError):
                audit.compiler_records(self.evidence, self.control["modules"], required=True)
            (self.evidence / "compiler-records/0001.json").unlink()
            (self.evidence / "compiler-records/0001.reserved").unlink()
            (self.evidence / "compiler-stop.json").unlink()

    def test_duplicate_does_not_overwrite_first_real_exit(self):
        self.invoke()
        before = (self.evidence / "compiler-records/0001.json").read_bytes()
        self.olean.unlink()
        with self.assertRaises(FileExistsError):
            self.invoke()
        self.assertEqual((self.evidence / "compiler-records/0001.json").read_bytes(), before)
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)

    def test_missing_wrong_index_and_outside_project_evidence_rejected(self):
        import json
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)
        self.invoke()
        path = self.evidence / "compiler-records/0001.json"
        value = json.loads(path.read_text())
        value["module"] = "Other.Project"
        path.write_text(json.dumps(value))
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)
        value["module"] = self.module
        path.write_text(json.dumps(value))
        path.rename(path.with_name("9999.json"))
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)

    def test_unexpected_source_args_setup_compiler_or_preexisting_object_rejected(self):
        from unittest.mock import patch
        for mutation in (lambda: self.control.update(allowed_modules=[]),
                         lambda: self.args.append("-Ddebug.skipKernelTC=true"),
                         lambda: self.setup.write_text('{"name":"Wrong"}'),
                         lambda: self.compiler.write_text("changed compiler"),
                         lambda: self.source.write_text("changed source"),
                         lambda: self.olean.touch()):
            with self.subTest(mutation=mutation):
                original = (self.control["allowed_modules"][:], self.args[:], self.setup.read_bytes(),
                            self.compiler.read_bytes(), self.source.read_bytes())
                mutation()
                with self.assertRaises(AssertionError):
                    self.invoke(run=lambda *a, **k: self.fail("Compiler must not launch"))
                self.control["allowed_modules"], self.args = original[:2]
                self.setup.write_bytes(original[2]); self.compiler.write_bytes(original[3]); self.source.write_bytes(original[4])
                if self.olean.exists(): self.olean.unlink()
                for path in (self.evidence / "compiler-records").iterdir(): path.unlink()
                (self.evidence / "compiler-stop.json").unlink()

    def test_dependency_requires_actual_finished_success(self):
        self.control["modules"][self.module]["project_imports"] = ["DifferentialGeometry.Parent"]
        self.control["modules"]["DifferentialGeometry.Parent"] = {"position": 2}
        with self.assertRaises(FileNotFoundError):
            self.invoke()

    def test_resource_guard_serializes_and_checks_each_launch(self):
        import fcntl
        active = (self.evidence / "compiler-slot-0.lock").open("a")
        fcntl.flock(active, fcntl.LOCK_EX)
        pauses = []
        def pause(seconds):
            pauses.append(seconds)
            active.close()
        lease = self.observer.take_slot(self.control, available=lambda: 0,
                                        disk_free=lambda: 2 * self.observer.GIB, pause=pause)
        self.assertEqual(pauses, [0.1])
        lease.close()
        with self.assertRaises(AssertionError):
            self.observer.take_slot(self.control, disk_free=lambda: 0)
        (self.evidence / "compiler-stop.json").write_text("{}")
        with self.assertRaises(AssertionError):
            self.observer.take_slot(self.control, disk_free=lambda: 2 * self.observer.GIB)

    def test_real_slot_lifetime_has_at_most_two_active_compilers(self):
        import concurrent.futures
        lock = threading.Lock()
        active, peak = 0, 0
        def mocked_compiler():
            nonlocal active, peak
            lease = self.observer.take_slot(self.control, available=lambda: 9 * self.observer.GIB,
                                             disk_free=lambda: 2 * self.observer.GIB)
            with lock:
                active += 1
                peak = max(peak, active)
            time.sleep(0.015)
            with lock:
                active -= 1
            lease.close()
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            list(executor.map(lambda _: mocked_compiler(), range(4)))
        self.assertLessEqual(peak, 2)
        self.assertEqual(active, 0)

    def test_log_or_setup_hash_changes_are_not_certified(self):
        self.invoke()
        path = self.evidence / "module-build-logs/0001.stdout.log"
        path.write_bytes(b"tampered log")
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)
        path.write_bytes(b"")
        import gzip
        (self.evidence / "module-setups/0001.json.gz").write_bytes(gzip.compress(b"tampered setup"))
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control["modules"], required=True)

    def test_shim_is_isolated_and_official_toolchain_is_unchanged(self):
        sysroot = self.compiler.parent.parent
        (sysroot / "lib").mkdir()
        (sysroot / "lib/unchanged").write_bytes(b"original library")
        (sysroot / "bin/lake").write_bytes(b"original lake")
        before = self.compiler.read_bytes()
        control_path = self.evidence / "control.json"
        env = audit.make_compiler_shim(self.evidence, sysroot, pathlib.Path(__file__), control_path)
        shim = self.evidence / "observed-toolchain"
        self.assertEqual((shim / "lib").resolve(), (sysroot / "lib").resolve())
        self.assertEqual((shim / "bin/lake").resolve(), (sysroot / "bin/lake").resolve())
        self.assertFalse((shim / "bin/lean").is_symlink())
        self.assertEqual(self.compiler.read_bytes(), before)
        self.assertEqual(env["LAKE_ARTIFACT_CACHE"], "false")
        self.assertEqual(env["LAKE_CACHE_DIR"], "")
        import shutil
        shutil.rmtree(shim)
        self.assertEqual((sysroot / "lib/unchanged").read_bytes(), b"original library")
        self.assertEqual(self.compiler.read_bytes(), before)

    def test_metadata_queries_forward_actual_compiler_and_real_environment(self):
        import json, os, sys
        from unittest.mock import patch
        path = self.evidence / "control.json"
        path.write_text(json.dumps(self.control))
        for query in self.observer.INFO_QUERIES:
            with patch.dict(os.environ, {"HAMILTON_COMPILER_CONTROL": str(path), "LEAN_SYSROOT": "audit-shim"}), \
                 patch.object(sys, "argv", ["observer", query]), \
                 patch.object(os, "execve", side_effect=RuntimeError("mock exec handoff")) as execute:
                with self.assertRaisesRegex(RuntimeError, "mock exec handoff"):
                    self.observer.main()
                command, argv, env = execute.call_args.args
                self.assertEqual(command, str(self.compiler))
                self.assertEqual(argv, [str(self.compiler), query])
                self.assertEqual(env["LEAN_SYSROOT"], self.control["sysroot"])

    def test_lossless_file_spooling_real_mock_child_and_resource_evidence(self):
        """Python fixture only: exercise real file descriptors, wait and logs."""
        import hashlib, io, subprocess
        from types import SimpleNamespace
        from unittest.mock import patch
        self.compiler.write_text(
            "#!/usr/bin/env python3\nimport pathlib, sys\n"
            "pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'mock object')\n"
            "sys.stdout.buffer.write(b'a' * (2 * 1024 * 1024) + b'\\x00tail\\n')\n"
            "sys.stderr.buffer.write(b'actual mock stderr\\n')\n")
        self.compiler.chmod(0o755)
        self.control['compiler_sha256'] = self.observer.digest(self.compiler)
        stdout, stderr = io.BytesIO(), io.BytesIO()
        with patch.object(self.observer.sys, 'stdout', SimpleNamespace(buffer=stdout)), \
             patch.object(self.observer.sys, 'stderr', SimpleNamespace(buffer=stderr)):
            self.assertEqual(self.invoke(run=subprocess.run), 0)
        expected = b'a' * (2 * 1024 * 1024) + b'\x00tail\n'
        self.assertEqual(stdout.getvalue(), expected)
        self.assertEqual(stderr.getvalue(), b'actual mock stderr\n')
        self.assertEqual((self.evidence / 'module-build-logs/0001.stdout.log').read_bytes(), expected)
        result = self.record()
        self.assertEqual(result['stdout_sha256'], hashlib.sha256(expected).hexdigest())
        self.assertGreater(result['resources']['child_maximum_rss_bytes'], 0)
        self.assertGreaterEqual(result['resources']['child_user_cpu_seconds'], 0)
        self.assertGreaterEqual(result['resources']['child_system_cpu_seconds'], 0)
        audit.compiler_records(self.evidence, self.control['modules'], required=True)

    def test_log_copy_and_hash_use_bounded_reads(self):
        import io, hashlib
        from unittest.mock import patch
        data = b'z' * (3 * 1024 * 1024 + 7)
        class BoundedReader(io.BytesIO):
            def read(self, size=-1):
                self_size = size
                if not 0 < self_size <= 1024 * 1024:
                    raise AssertionError('Unbounded log read')
                return super().read(size)
        sink = io.BytesIO()
        with patch.object(pathlib.Path, 'open', side_effect=lambda *a, **k: BoundedReader(data)):
            self.observer.forward_log('mock', sink)
            self.assertEqual(self.observer.digest('mock'), hashlib.sha256(data).hexdigest())
            self.assertEqual(audit.file_digest('mock'), hashlib.sha256(data).hexdigest())
        self.assertEqual(sink.getvalue(), data)

    def test_partial_logs_survive_interruption_without_a_successful_exit(self):
        def interrupted(command, **kwargs):
            kwargs['stdout'].write(b'partial stdout\n')
            kwargs['stderr'].write(b'partial stderr\n')
            raise KeyboardInterrupt('mock cancellation')
        with self.assertRaises(KeyboardInterrupt):
            self.invoke(run=interrupted)
        self.assertEqual(self.record()['status'], 'inconclusive')
        self.assertNotIn('exit_code', self.record())
        self.assertEqual((self.evidence / 'module-build-logs/0001.stdout.log').read_bytes(), b'partial stdout\n')
        self.assertEqual((self.evidence / 'module-build-logs/0001.stderr.log').read_bytes(), b'partial stderr\n')
        with self.assertRaises(AssertionError):
            audit.compiler_records(self.evidence, self.control['modules'], required=True)

    def test_missing_stream_logs_are_not_certified(self):
        self.invoke()
        for stream in ('stdout', 'stderr'):
            path = self.evidence / f'module-build-logs/0001.{stream}.log'
            path.unlink()
            with self.assertRaises(FileNotFoundError):
                audit.compiler_records(self.evidence, self.control['modules'], required=True)
            path.write_bytes(b'')

    def test_active_batch_rejects_unscheduled_source_and_mid_compile_change(self):
        import json
        path = self.evidence / 'active-batch.json'
        self.control['active_batch_path'] = str(path)
        path.write_text(json.dumps({'batch': 1, 'allowed_modules': []}))
        with self.assertRaisesRegex(AssertionError, 'outside the active'):
            self.invoke()
        (self.evidence / 'compiler-stop.json').unlink()
        path.write_text(json.dumps({'batch': 1, 'allowed_modules': [self.module]}))
        def changed(command, **kwargs):
            result = self.fake_run(command, **kwargs)
            path.write_text(json.dumps({'batch': 2, 'allowed_modules': [self.module]}))
            return result
        with self.assertRaisesRegex(AssertionError, 'Active batch changed'):
            self.invoke(run=changed)
        self.assertEqual(self.record()['batch'], 1)
        self.assertEqual(self.record()['exit_code'], 0)
        self.assertEqual(self.record()['status'], 'inconclusive')

    def test_waiting_observer_sigterm_does_not_claim_a_compiler_exit(self):
        import fcntl, json, os, signal, subprocess, sys
        held = [(self.evidence / f'compiler-slot-{index}.lock').open('a') for index in range(2)]
        for stream in held:
            fcntl.flock(stream, fcntl.LOCK_EX)
        path = self.evidence / 'control.json'
        path.write_text(json.dumps(self.control))
        env = dict(os.environ, HAMILTON_COMPILER_CONTROL=str(path))
        process = subprocess.Popen([sys.executable, str(pathlib.Path(self.observer.__file__)), *self.args],
                                   cwd=self.root, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            deadline = time.monotonic() + 3
            record_path = self.evidence / 'compiler-records/0001.json'
            while not record_path.exists() and time.monotonic() < deadline and process.poll() is None:
                time.sleep(0.01)
            self.assertTrue(record_path.exists())
            self.assertEqual(self.record()['status'], 'waiting')
            os.kill(process.pid, signal.SIGTERM)
            self.assertEqual(process.wait(timeout=3), -signal.SIGTERM)
            self.assertEqual(self.record()['status'], 'waiting')
            self.assertNotIn('exit_code', self.record())
            self.assertFalse(self.olean.exists())
            with self.assertRaises(AssertionError):
                audit.compiler_records(self.evidence, self.control['modules'], required=True)
        finally:
            if process.poll() is None:
                process.kill()
            process.wait(timeout=3)
            for stream in held:
                stream.close()
        lease = self.observer.take_slot(self.control, available=lambda: 9 * self.observer.GIB,
                                        disk_free=lambda: 2 * self.observer.GIB)
        self.assertEqual(lease.audit_launch_resources['active_compiler_leases_before'], 0)
        lease.close()


class PersistentBatchGateTests(unittest.TestCase):
    def test_missing_interrupted_failed_changed_and_misindexed_batches_rejected(self):
        import json, tempfile
        batches = [{'modules': ['A', 'B'], 'chains': [['A', 'B']]},
                   {'modules': ['C'], 'chains': [['C']]}]
        with tempfile.TemporaryDirectory() as tmp:
            output = pathlib.Path(tmp)
            (output / 'batch-results').mkdir()
            paths = [output / f'batch-results/{index:04d}.json' for index in (1, 2)]
            valid = [{'batch': index, 'targets': ['+' + tip + ':olean'],
                      'status': 'finished', 'lake_job_success': True}
                     for index, tip in ((1, 'B'), (2, 'C'))]
            with self.assertRaises(AssertionError):
                audit.batch_records(output, batches, required=True)
            for path, value in zip(paths, valid):
                path.write_text(json.dumps(value))
            self.assertEqual(audit.batch_records(output, batches, required=True), valid)
            for mutation in ({'status': 'running'}, {'lake_job_success': False},
                             {'targets': ['+A:olean']}, {'batch': True}, {'batch': 99}):
                paths[0].write_text(json.dumps(dict(valid[0], **mutation)))
                with self.assertRaises(AssertionError):
                    audit.batch_records(output, batches, required=True)
            paths[0].write_text(json.dumps(valid[0]))
            paths[0].rename(paths[0].with_name('0099.json'))
            with self.assertRaises(AssertionError):
                audit.batch_records(output, batches, required=True)

    def test_resource_summary_rejects_missing_or_violated_launch_evidence(self):
        value = {'launch_resources': {'active_compiler_leases_before': 1,
                                      'available_memory_bytes': 8 * 1024 ** 3,
                                      'free_disk_bytes': 1024 ** 3},
                 'resources': {'child_user_cpu_seconds': 2.5,
                               'child_system_cpu_seconds': 0.5,
                               'child_maximum_rss_bytes': 4096}}
        summary = audit.resource_summary({'M': value}, 2)
        self.assertEqual(summary['measured_compilers'], 1)
        self.assertEqual(summary['recorded_peak_compiler_leases_at_launch'], 2)
        self.assertFalse(summary['hard_cpu_or_memory_cap'])
        for key, replacement in (('active_compiler_leases_before', 2),
                                 ('available_memory_bytes', 8 * 1024 ** 3 - 1),
                                 ('free_disk_bytes', 1024 ** 3 - 1)):
            original = value['launch_resources'][key]
            value['launch_resources'][key] = replacement
            with self.assertRaises(AssertionError):
                audit.resource_summary({'M': value}, 2)
            value['launch_resources'][key] = original
        value['launch_resources'].pop('available_memory_bytes')
        with self.assertRaises(KeyError):
            audit.resource_summary({'M': value}, 2)

    def test_frontend_resource_sampling_is_observed_and_not_a_hard_cap(self):
        import os, sys, tempfile
        with tempfile.TemporaryDirectory() as tmp:
            samples = audit.ProcessGroupSamples()
            with (pathlib.Path(tmp) / 'frontend.log').open('wb') as stream:
                code = audit.run_batch([sys.executable, '-c', 'import time; time.sleep(0.12)'],
                                       root=tmp, env=os.environ.copy(), stream=stream,
                                       refresh=lambda: None, sample=samples, poll_seconds=0.01,
                                       grace_seconds=0.1, kill_seconds=1)
            self.assertEqual(code, 0)
            self.assertGreater(samples.value['samples'], 0)
            self.assertGreater(samples.value['sampled_peak_group_rss_bytes'], 0)
            self.assertGreaterEqual(samples.value['sampled_peak_group_processes'], 1)
            self.assertGreaterEqual(samples.value['sampled_peak_frontend_threads'], 1)
            self.assertIn('not a hard', samples.value['measurement'])

    def test_source_owned_driver_is_one_store_quiet_and_awaits_before_advancing(self):
        # Static contract regression only, deliberately not an API typecheck.
        # Exact official Lake compilation remains a separate hosted gate.
        driver = pathlib.Path(__file__).with_name('build-hamilton-batches.lean').read_text()
        self.assertEqual(driver.count('ws.runFetchM '), 1)
        self.assertIn('let job ← buildSpecs specs', driver)
        self.assertIn('let _ ← job.await', driver)
        self.assertIn('verbosity := .quiet', driver)
        self.assertIn('updateDeps := false, updateToolchain := false', driver)
        self.assertNotIn('compileLeanModule', driver)
        self.assertNotIn('IO.Process.spawn', driver)
        workflow = pathlib.Path(audit.__file__).parents[2] / '.github/workflows/point4-hamilton-release-audit.yml'
        self.assertIn('lake env lean --plugin', workflow.read_text())
        self.assertIn('../campaign/scripts/point4/build-hamilton-batches.lean', workflow.read_text())

    def test_chain_tips_reach_every_scheduled_module_and_ready_width_is_bounded(self):
        order = [f'M{index}' for index in range(40)]
        graph = {module: [parent for j, parent in enumerate(order[:i])
                          if j == i - 1 or (i * 7 + j) % 11 == 0]
                 for i, module in enumerate(order)}
        graph['M10'] = ['M2', 'M5']
        graph['M20'] = ['M4', 'M8', 'M12']
        graph['M30'] = ['M11', 'M19', 'M27']
        for jobs in (1, 2):
            built = set()
            for batch in audit.chain_batches(order, graph, jobs):
                scheduled = set(batch['modules'])
                reached = set()
                def visit(module):
                    if module in built or module in reached:
                        return
                    self.assertIn(module, scheduled)
                    reached.add(module)
                    for parent in graph[module]:
                        visit(parent)
                for chain in batch['chains']:
                    visit(chain[-1])
                self.assertEqual(reached, scheduled)
                pending = set(scheduled)
                while pending:
                    ready = [m for m in pending if set(graph[m]) <= built]
                    self.assertTrue(ready)
                    self.assertLessEqual(len(ready), jobs)
                    # Adversarially complete just one ready source at a time.
                    chosen = sorted(ready)[-1]
                    pending.remove(chosen)
                    built.add(chosen)
            self.assertEqual(built, set(order))


class EndpointGateTests(unittest.TestCase):
    def test_signatures_and_standard_axioms_still_required(self):
        names = list(audit.TARGETS.values())
        valid = "\n".join(f"@{n} : True\n'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
        self.assertEqual(set(audit.endpoint_output(valid, 0)), set(names))
        for output, code in ((valid, 7), (valid.replace("@" + names[0], "missing"), 0),
                             (valid.replace("propext", "sorryAx"), 0),
                             (valid + "\n'" + names[0] + "' depends on axioms: [propext]", 0),
                             (valid.split("@" + names[1])[0], 0)):
            with self.assertRaises(AssertionError):
                audit.endpoint_output(output, code)


class CancellationTests(unittest.TestCase):
    def test_actual_sigterm_marks_inconclusive_and_drains_mock_descendants(self):
        """Three tiny Python processes only; no Lean or native build."""
        import json, os, signal, subprocess, sys, tempfile
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            child = root / "mock_child.py"
            child.write_text(
                "import json, os, pathlib, signal, subprocess, sys, time\n"
                "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                "grandchild = subprocess.Popen([sys.executable, '-c', "
                "'import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)'])\n"
                "pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(), grandchild.pid]))\n"
                "time.sleep(60)\n")
            parent = root / "mock_audit_parent.py"
            source = pathlib.Path(audit.__file__).resolve()
            parent.write_text(
                "import importlib.util, json, os, pathlib, signal, sys\n"
                f"spec = importlib.util.spec_from_file_location('audit', {str(source)!r})\n"
                "audit = importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)\n"
                "root = pathlib.Path(sys.argv[1])\n"
                "report = {'kernel_audit_status': 'RUNNING: mock source compilation'}\n"
                "before = signal.getsignal(signal.SIGTERM)\n"
                "def save(): (root / 'report.json').write_text(json.dumps(report))\n"
                "try:\n"
                "    with audit.audit_execution(report, save):\n"
                "        with (root / 'child.log').open('w') as stream:\n"
                "            audit.run_batch([sys.executable, str(root / 'mock_child.py'), str(root / 'pids.json')], "
                "root=root, env=os.environ.copy(), stream=stream, refresh=lambda: None, "
                "poll_seconds=0.01, grace_seconds=0.15, kill_seconds=1)\n"
                "except audit.AuditInterrupted:\n"
                "    report['handler_restored'] = signal.getsignal(signal.SIGTERM) == before\n"
                "    save(); sys.exit(23)\n")
            pids = []
            with (root / "parent.log").open("w") as log:
                process = subprocess.Popen([sys.executable, str(parent), str(root)],
                                           stdout=log, stderr=subprocess.STDOUT)
                try:
                    deadline = time.monotonic() + 3
                    path = root / "pids.json"
                    while not path.exists() and time.monotonic() < deadline and process.poll() is None:
                        time.sleep(0.01)
                    self.assertTrue(path.exists(), (root / "parent.log").read_text())
                    pids = json.loads(path.read_text())
                    started = time.monotonic()
                    os.kill(process.pid, signal.SIGTERM)
                    self.assertEqual(process.wait(timeout=3), 23, (root / "parent.log").read_text())
                    self.assertLess(time.monotonic() - started, 2)
                    report = json.loads((root / "report.json").read_text())
                    self.assertTrue(report["kernel_audit_status"].startswith("INCONCLUSIVE:"))
                    self.assertTrue(report["handler_restored"])
                    for pid in pids:
                        stat = pathlib.Path(f"/proc/{pid}/stat")
                        # An orphan awaiting init reap is not a running compiler.
                        self.assertTrue(not stat.exists() or stat.read_text().split()[2] == "Z",
                                        f"Mock descendant {pid} remains running")
                finally:
                    if pids:
                        try: os.killpg(pids[0], signal.SIGKILL)
                        except ProcessLookupError: pass
                    if process.poll() is None:
                        process.kill()
                    process.wait(timeout=3)

    def test_exited_mock_lake_group_is_drained_and_actual_exit_retained(self):
        """A dead owner must not leave its live child/grandchild running."""
        import json, os, signal, sys, tempfile
        for code in (0, 7, -9):
            with self.subTest(actual_exit=code), tempfile.TemporaryDirectory() as tmp:
                root = pathlib.Path(tmp)
                child = root / "mock_child.py"
                child.write_text(
                    "import json, os, pathlib, signal, subprocess, sys, time\n"
                    "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                    "grandchild = subprocess.Popen([sys.executable, '-c', "
                    "'import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)'])\n"
                    "pathlib.Path(sys.argv[1]).write_text(json.dumps([int(sys.argv[2]), os.getpid(), grandchild.pid]))\n"
                    "time.sleep(60)\n")
                owner = root / "mock_lake.py"
                owner.write_text(
                    "import os, pathlib, signal, subprocess, sys, time\n"
                    "root = pathlib.Path(sys.argv[1])\n"
                    "subprocess.Popen([sys.executable, str(root / 'mock_child.py'), str(root / 'pids.json'), str(os.getpid())])\n"
                    "deadline = time.monotonic() + 3\n"
                    "while not (root / 'pids.json').exists() and time.monotonic() < deadline: time.sleep(0.01)\n"
                    "if not (root / 'pids.json').exists(): sys.exit(99)\n"
                    "code = int(sys.argv[2])\n"
                    "if code < 0: os.kill(os.getpid(), signal.SIGKILL)\n"
                    "sys.exit(code)\n")
                pids = []
                try:
                    started = time.monotonic()
                    with (root / "group.log").open("w") as stream:
                        actual = audit.run_batch([sys.executable, str(owner), str(root), str(code)],
                                                 root=root, env=os.environ.copy(), stream=stream,
                                                 refresh=lambda: None, poll_seconds=0.01,
                                                 grace_seconds=0.15, kill_seconds=1)
                    self.assertEqual(actual, code, (root / "group.log").read_text())
                    self.assertLess(time.monotonic() - started, 2)
                    pids = json.loads((root / "pids.json").read_text())
                    deadline = time.monotonic() + 1
                    while time.monotonic() < deadline:
                        running = [pid for pid in pids if pathlib.Path(f"/proc/{pid}/stat").exists()
                                   and pathlib.Path(f"/proc/{pid}/stat").read_text().split()[2] != "Z"]
                        if not running: break
                        time.sleep(0.01)
                    self.assertEqual(running, [], "Exited Lake left running mock descendants")
                finally:
                    path = root / "pids.json"
                    if path.exists():
                        pids = json.loads(path.read_text())
                    if pids:
                        try: os.killpg(pids[0], signal.SIGKILL)
                        except ProcessLookupError: pass

    def test_spawn_signal_is_deferred_until_cleanup_handle_exists(self):
        import os, signal
        from unittest.mock import Mock, patch
        report = {"kernel_audit_status": "RUNNING: mock"}
        before = signal.getsignal(signal.SIGTERM)
        process = Mock(pid=987654321)
        def spawn(*args, **kwargs):
            os.kill(os.getpid(), signal.SIGTERM)
            return process
        saved = []
        with patch.object(audit.subprocess, "Popen", side_effect=spawn), \
             patch.object(audit, "drain_process_group") as cleanup:
            with self.assertRaises(audit.AuditInterrupted):
                with audit.audit_execution(report, lambda: saved.append(report.copy())):
                    audit.run_batch(["mock"], root=".", env={}, stream=None, refresh=lambda: None)
            cleanup.assert_called_once_with(process, grace_seconds=30, kill_seconds=5)
        self.assertEqual(signal.getsignal(signal.SIGTERM), before)
        self.assertTrue(saved[-1]["kernel_audit_status"].startswith("INCONCLUSIVE:"))


if __name__ == "__main__":
    unittest.main()
