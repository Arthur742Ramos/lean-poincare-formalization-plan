#!/usr/bin/env python3
"""Source/output rejection controls, never mathematical qualification."""
import pathlib
import stat
import tempfile
import unittest
from unittest.mock import patch
import point4_actual_gaussian_heat_resolvent_guard as gate

class ResolventGateTests(unittest.TestCase):
    def setUp(self):
        self.source = (gate.ROOT/gate.PROBE).read_text(encoding='utf8')
        self.lines = ['@'+name.rsplit('.', 1)[1]+' : complete expected signature\n'+"'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in gate.NAMES]
        self.output = '\n'.join(self.lines)

    def test_exact_source_pair(self):
        self.assertEqual(gate.check_pair(), self.source)

    def test_exact_record_parser_control(self):
        self.assertEqual(gate.check_output(self.source, self.output), set(gate.NAMES))

    def test_missing_duplicate_extra_actual_records(self):
        for value in ('\n'.join(self.lines[:-1]), self.output+'\n'+self.lines[0], self.output+"\n'foreign.theorem' depends on axioms: [propext]"):
            with self.assertRaises(AssertionError): gate.check_output(self.source, value)

    def test_extra_duplicate_or_empty_actual_axioms(self):
        for value in (self.output.replace('Quot.sound]', 'Quot.sound, sorryAx]', 1), self.output.replace('Quot.sound]', 'Quot.sound, Quot.sound]', 1), self.output.replace('[propext, Classical.choice, Quot.sound]', '[]', 1)):
            with self.assertRaises(AssertionError): gate.check_output(self.source, value)

    def test_missing_duplicate_type_or_error_output(self):
        for value in (self.output.replace('@'+gate.NAMES[0].rsplit('.', 1)[1]+' :', 'foreign :', 1), self.output+'\n@'+gate.NAMES[0].rsplit('.', 1)[1]+' : duplicate', self.output+'\nprobe.lean:1:0: error: failed'):
            with self.assertRaises(AssertionError): gate.check_output(self.source, value)

    def test_probe_provenance_drift(self):
        with self.assertRaises(AssertionError): gate.check_output(self.source.replace(gate.NAMES[0], 'foreign'), self.output)

    def test_math_and_probe_byte_drift(self):
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            for p in gate.PINS:
                file = root/p;file.parent.mkdir(parents=True, exist_ok=True);file.write_bytes((gate.ROOT/p).read_bytes())
            for p in gate.PINS:
                file = root/p;raw = file.read_bytes();file.write_bytes(raw+b'\n-- mutation\n')
                with self.assertRaises(AssertionError): gate.check_pair(root)
                file.write_bytes(raw)

    def test_alias_guard(self):
        path = gate.ROOT/gate.PROBE
        actual = pathlib.Path.lstat
        def changed(p):
            value = actual(p)
            if p == path:
                class Alias:
                    st_mode = stat.S_IFLNK
                    st_file_attributes = 0x400
                return Alias()
            return value
        with patch.object(pathlib.Path, 'lstat', changed):
            with self.assertRaises(AssertionError): gate.regular(path)

    def test_source_input_mutation(self):
        original = gate.regular; seen = {}
        def changed(path):
            raw = original(path);seen[path] = seen.get(path, 0)+1
            return raw+b'POST drift' if path == gate.ROOT/gate.MODULE and seen[path] == 2 else raw
        with patch.object(gate, 'regular', changed):
            with self.assertRaises(AssertionError): gate.check_pair()

if __name__ == '__main__':
    unittest.main()
