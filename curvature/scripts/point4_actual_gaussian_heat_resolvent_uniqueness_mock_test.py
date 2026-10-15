#!/usr/bin/env python3
"""Parser and provenance rejection controls; never mathematical qualification."""
import pathlib
import stat
import tempfile
import unittest
from unittest.mock import patch
import point4_actual_gaussian_heat_resolvent_uniqueness_guard as gate


class ActualUniquenessGateTests(unittest.TestCase):
    def setUp(self):
        self.source = (gate.ROOT / gate.PROBE).read_text(encoding='utf8')
        self.lines = ['@' + name.rsplit('.', 1)[1] + ' : complete expected signature\n' + "'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in gate.NAMES]
        self.output = '\n'.join(self.lines)

    def test_exact_source_pair(self):
        self.assertEqual(gate.check_pair(), self.source)

    def test_exact_record_parser_control(self):
        self.assertEqual(gate.check_output(self.source, self.output), set(gate.NAMES))

    def test_missing_duplicate_extra_records(self):
        for value in ('\n'.join(self.lines[:-1]), self.output + '\n' + self.lines[0], self.output + "\n'foreign.theorem' depends on axioms: [propext]"):
            with self.assertRaises(AssertionError):
                gate.check_output(self.source, value)

    def test_extra_duplicate_empty_axiom_groups(self):
        for value in (self.output.replace('Quot.sound]', 'Quot.sound, sorryAx]', 1), self.output.replace('Quot.sound]', 'Quot.sound, Quot.sound]', 1), self.output.replace('[propext, Classical.choice, Quot.sound]', '[]', 1)):
            with self.assertRaises(AssertionError):
                gate.check_output(self.source, value)

    def test_missing_duplicate_type_and_compile_error(self):
        for value in (self.output.replace('@' + gate.NAMES[0].rsplit('.', 1)[1] + ' :', 'foreign :', 1), self.output + '\n@' + gate.NAMES[0].rsplit('.', 1)[1] + ' : duplicate', self.output + '\nprobe.lean:1:0: error: failed'):
            with self.assertRaises(AssertionError):
                gate.check_output(self.source, value)

    def test_probe_record_provenance_drift(self):
        with self.assertRaises(AssertionError):
            gate.check_output(self.source.replace(gate.NAMES[0], 'foreign'), self.output)

    def test_math_and_probe_byte_drift(self):
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            for p in gate.PINS:
                target = root / p
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((gate.ROOT / p).read_bytes())
            for p in gate.PINS:
                target = root / p
                before = target.read_bytes()
                target.write_bytes(before + b'\n-- drift\n')
                with self.assertRaises(AssertionError):
                    gate.check_pair(root)
                target.write_bytes(before)

    def test_alias_guard(self):
        target = gate.ROOT / gate.PROBE
        original = pathlib.Path.lstat
        def changed(path):
            value = original(path)
            if path == target:
                class Alias:
                    st_mode = stat.S_IFLNK
                    st_file_attributes = 0x400
                return Alias()
            return value
        with patch.object(pathlib.Path, 'lstat', changed):
            with self.assertRaises(AssertionError):
                gate.regular(target)

    def test_source_input_mutation(self):
        original = gate.regular
        seen = {}
        def changed(path):
            before = original(path)
            seen[path] = seen.get(path, 0) + 1
            return before + b'POST drift' if path == gate.ROOT / gate.MODULE and seen[path] == 2 else before
        with patch.object(gate, 'regular', changed):
            with self.assertRaises(AssertionError):
                gate.check_pair()


if __name__ == '__main__':
    unittest.main()
