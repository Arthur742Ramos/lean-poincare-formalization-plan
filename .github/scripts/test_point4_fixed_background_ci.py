"""Synthetic rejection/resource controls. These supply no Lean proof PASS credit."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

import point4_fixed_background_ci as ci


def fixture():
    headers = '\n'.join('theorem ' + n + '.{u} : True := True.intro' for n in ci.TYPE_NAMES)
    records = '\n'.join("'" + n + "' depends on axioms: [propext, Classical.choice.{u}, Quot.sound]"
                        for n in ci.AXIOM_NAMES)
    return (ci.MARKERS[0] + '\n' + headers + '\n' + ci.MARKERS[1] + '\n' + records + '\n').encode()


class OutputControls(unittest.TestCase):
    def test_complete_ordered_fixture(self):
        self.assertEqual(len(ci.guard_output(fixture())['axiom_records']), 7)

    def test_missing_duplicate_extra_reordered_axiom_records(self):
        text = fixture().decode()
        lines = text.splitlines()
        for altered in [lines[:-1], lines + [lines[-1]], lines[:-2] + lines[-2:][::-1],
                        lines + ["'extra' does not depend on any axioms"]]:
            with self.subTest(altered=altered[-1]), self.assertRaises(ValueError):
                ci.guard_output(('\n'.join(altered) + '\n').encode())

    def test_nonstandard_malformed_and_duplicate_axiom_bases(self):
        for atom in ['sorryAx', 'Lean.ofReduceBool', 'Classical.choice.{u} garbage',
                     'propext, propext', 'Classical.choice, Classical.choice.{u}', '']:
            with self.subTest(atom=atom), self.assertRaises(ValueError):
                ci.guard_output(fixture().replace(b'propext', atom.encode(), 1))

    def test_marker_signature_error_and_trailing_text_rejection(self):
        value = fixture()
        bad = [value.replace(ci.MARKERS[0].encode(), b''),
               value + ci.MARKERS[1].encode(),
               value.replace(ci.TYPE_NAMES[0].encode(), b'wrong', 1),
               value.replace(ci.TYPE_NAMES[0].encode(), ci.TYPE_NAMES[1].encode(), 1),
               b'error: failed elaboration\n' + value,
               value + b'unexpected trailing output\n', b'\xff' + value]
        for raw in bad:
            with self.subTest(raw=raw[:30]), self.assertRaises((ValueError, UnicodeError)):
                ci.guard_output(raw)

    def test_empty_and_oversized_output(self):
        for raw in [b'', b'x' * (ci.LOG_LIMIT + 1)]:
            with self.assertRaises(ValueError):
                ci.guard_output(raw)


class ProcessControls(unittest.TestCase):
    def test_success_and_failure_exit_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.assertEqual(ci.run_process([sys.executable, '-c', 'print(42)'], root, root, 'ok', 3), b'42\n')
            with self.assertRaises(ValueError):
                ci.run_process([sys.executable, '-c', 'raise SystemExit(7)'], root, root, 'bad', 3)
            row = json.loads((root / 'bad.json').read_text())
            self.assertEqual(row['exit_code'], 7)
            self.assertTrue(row['leader_reaped'] and row['no_live_stage_descendants'])

    def test_timeout_with_TERM_ignoring_child_is_quiesced(self):
        code = 'import os,signal,time; p=os.fork(); signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(30)'
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(TimeoutError):
                ci.run_process([sys.executable, '-c', code], root, root, 'timeout', 0.3)
            row = json.loads((root / 'timeout.json').read_text())
            self.assertTrue(row['leader_reaped'] and row['no_live_stage_descendants'])

    def test_leader_exit_does_not_leave_a_running_child(self):
        code = ('import os,time; p=os.fork(); '
                'os._exit(0) if p else (os.close(1),os.close(2),time.sleep(30))')
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            ci.run_process([sys.executable, '-c', code], root, root, 'descendant', 3)
            self.assertTrue(json.loads((root / 'descendant.json').read_text())['no_live_stage_descendants'])

    def test_output_overflow_is_bounded_and_quiesced(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(ValueError):
                ci.run_process([sys.executable, '-c', 'print("x"*17000000)'], root, root, 'overflow', 3)
            self.assertLessEqual((root / 'overflow.log').stat().st_size, ci.LOG_LIMIT)
            self.assertTrue(json.loads((root / 'overflow.json').read_text())['no_live_stage_descendants'])

    def test_existing_evidence_cannot_exceed_total_bound(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with (root / 'existing-artifact').open('wb') as stream:
                stream.truncate(ci.LOG_BUDGET)
            with self.assertRaises(ValueError):
                ci.run_process([sys.executable, '-c', 'print(42)'], root, root, 'total', 3)
            self.assertTrue(json.loads((root / 'total.json').read_text())['no_live_stage_descendants'])
            self.assertLessEqual(sum(p.stat().st_size for p in root.iterdir()), ci.EVIDENCE_LIMIT)

    def test_metadata_limit_includes_overwrite_and_preserves_previous_receipt(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with (root / 'existing-artifact').open('wb') as stream:
                stream.truncate(ci.EVIDENCE_LIMIT - 256)
            receipt = root / 'receipt.json'
            ci.write_json(receipt, {'status': 'failure receipt retained'})
            previous = receipt.read_bytes()
            with self.assertRaises(ValueError):
                ci.write_json(receipt, {'oversized': 'x' * 1024})
            self.assertEqual(receipt.read_bytes(), previous)
            self.assertLessEqual(sum(p.stat().st_size for p in root.iterdir()), ci.EVIDENCE_LIMIT)


if __name__ == '__main__':
    unittest.main()
