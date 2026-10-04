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


if __name__ == "__main__":
    unittest.main()
