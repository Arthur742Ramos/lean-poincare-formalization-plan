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
