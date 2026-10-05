#!/usr/bin/env python3
"""Negative tests for probe validation; synthetic output is not compiler evidence."""
import importlib.util
import pathlib
import re
import unittest

PATH = pathlib.Path(__file__).with_name('point4_manifold_heat_source_test.py')
spec = importlib.util.spec_from_file_location('point4_manifold_heat_source_test', PATH)
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


class ProbeGuard(unittest.TestCase):
    def setUp(self):
        expected = re.findall(r'^#print axioms (\S+)', (guard.ROOT / guard.PROBE).read_text(), re.M)
        self.output = '\n'.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in expected)
        self.output += '\nMANIFOLD_HEAT_TYPES_BEGIN\n' + 'BoundarylessManifold I M\n' * 4
        self.output += 'MANIFOLD_HEAT_TYPES_END\n'

    def test_expected_shape(self):
        guard.check_probe(self.output)

    def test_new_axiom_rejected(self):
        with self.assertRaises(AssertionError):
            guard.check_probe(self.output.replace('Quot.sound', 'Quot.sound, sorryAx', 1))

    def test_missing_axiom_surface_rejected(self):
        with self.assertRaises(AssertionError):
            guard.check_probe('\n'.join(self.output.splitlines()[1:]))

    def test_duplicate_axiom_surface_rejected(self):
        with self.assertRaises(AssertionError):
            guard.check_probe(self.output.splitlines()[0] + '\n' + self.output)

    def test_global_model_requirement_rejected(self):
        for replacement in ('ModelWithCorners.Boundaryless I', 'I.Boundaryless'):
            with self.subTest(replacement=replacement), self.assertRaises(AssertionError):
                guard.check_probe(self.output.replace('BoundarylessManifold I M', replacement, 1))

    def test_missing_manifold_requirement_rejected(self):
        with self.assertRaises(AssertionError):
            guard.check_probe(self.output.replace('BoundarylessManifold I M\n', '', 1))

    def test_duplicate_markers_rejected(self):
        with self.assertRaises(AssertionError):
            guard.check_probe(self.output + '\nMANIFOLD_HEAT_TYPES_BEGIN\n')


if __name__ == '__main__':
    unittest.main()
