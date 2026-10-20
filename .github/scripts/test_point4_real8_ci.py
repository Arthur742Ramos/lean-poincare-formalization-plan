"""Controller rejection and ownership tests; no Lean/runtime PASS credit."""
import io
import json
from pathlib import Path
import signal
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import point4_real8_ci as ci


class OwnershipControls(unittest.TestCase):
    def run_case(self, code, succeeds, timeout=3):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            if succeeds:
                ci.run_process([sys.executable, '-c', code], root, root, 'stage', timeout)
            else:
                with self.assertRaises((ValueError, InterruptedError)):
                    ci.run_process([sys.executable, '-c', code], root, root, 'stage', timeout)
            row = json.loads((root / 'stage.json').read_text())
            self.assertTrue(row['closure']['leader_reaped'])
            self.assertTrue(row['closure']['no_live_owned_descendants'])
            self.assertFalse(ci.owned_processes())
            return row

    def test_original_exit_and_nonzero_preserved(self):
        self.assertEqual(self.run_case('print(42)', True)['exit_code'], 0)
        self.assertEqual(self.run_case('raise SystemExit(7)', False)['exit_code'], 7)

    def test_timeout_reaps_TERM_ignoring_child_in_a_new_session(self):
        code = ('import os,signal,time; p=os.fork(); '
                'os.setsid() if p==0 else None; '
                'signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(30)')
        row = self.run_case(code, False, 0.3)
        self.assertGreaterEqual(len(row['closure']['KILL_groups']), 2)

    def test_successful_leader_cannot_abandon_new_session_descendant(self):
        code = ('import os,time; p=os.fork(); '
                '(time.sleep(.1),os._exit(0)) if p else (os.setsid(),time.sleep(30))')
        row = self.run_case(code, False)
        self.assertIn('left live descendants', row['error'])

    def test_supervisor_signal_reaps_nested_session(self):
        code = ('import os,signal,time; parent=os.getppid(); p=os.fork(); '
                '(time.sleep(.15),os.kill(parent,signal.SIGTERM),time.sleep(30)) '
                'if p else (os.setsid(),time.sleep(30))')
        self.assertIn('Supervisor signal', self.run_case(code, False)['error'])

    def test_output_overflow_is_rejected_and_reaped(self):
        row = self.run_case('print("x"*17000000)', False)
        self.assertIn('16MiB', row['error'])

    def test_launch_failure_restores_signal_handlers_and_mask(self):
        handlers = {s: signal.getsignal(s) for s in ci.SIGNALS}
        mask = signal.pthread_sigmask(signal.SIG_BLOCK, ())
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(FileNotFoundError):
                ci.run_process(['/nonexistent-exact-command'], root, root, 'launch', 1)
        self.assertEqual({s: signal.getsignal(s) for s in ci.SIGNALS}, handlers)
        self.assertEqual(signal.pthread_sigmask(signal.SIG_BLOCK, ()), mask)


class InputControls(unittest.TestCase):
    def test_exact_eight_results_required(self):
        names = ['test_route_' + str(i) for i in range(8)]
        raw = ('\n'.join(f'{n} (__main__.RealValidatorTests.{n}) ... ok' for n in names) +
               '\n\n----------------------------------------------------------------------\nRan 8 tests in 12.4s\n\nOK\n').encode()
        ci.check_real8_output(raw, names)
        for bad in [raw.replace(b'... ok', b'... skipped', 1), raw.replace(b'Ran 8', b'Ran 7'),
                    raw + b'extra output', raw.replace(b'... ok', b'... FAIL', 1)]:
            with self.assertRaises(ValueError):
                ci.check_real8_output(bad, names)

    def test_regular_read_rejects_symlink(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'target').write_bytes(b'actual')
            (root / 'link').symlink_to(root / 'target')
            with self.assertRaises(OSError):
                ci.identity(root / 'link')

    def test_zip_namespace_hash_and_selection_are_authenticated(self):
        buffer = io.BytesIO()
        members = {}
        with zipfile.ZipFile(buffer, 'w') as archive:
            for i in range(52):
                name = f'member-{i:02d}.log'
                data = b'x' * (4500 if i < 18 else 4420 if i == 18 else 0)
                archive.writestr(name, data)
        raw = buffer.getvalue()
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for i, info in enumerate(archive.infolist()):
                members[info.filename] = dict(ci.pin(archive.read(info)), CRC32=info.CRC,
                    selected_for_preserved_guard_inputs=i < 19)
        descriptor = {'archive': ci.pin(raw), 'archive_members': members,
                      'historical_input_origin': {'scope': 'Synthetic controller test only'}}
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            work, evidence = root / 'work', root / 'evidence'
            work.mkdir(); evidence.mkdir()
            with patch('urllib.request.urlopen', return_value=io.BytesIO(raw)):
                _, selected = ci.recover_inputs(descriptor, work, evidence)
            self.assertEqual(len(selected), 19)
            members['member-00.log']['sha256'] = '0' * 64
            bad_work = root / 'bad-work'; bad_work.mkdir()
            with patch('urllib.request.urlopen', return_value=io.BytesIO(raw)), self.assertRaises(ValueError):
                ci.recover_inputs(descriptor, bad_work, evidence)


if __name__ == '__main__':
    unittest.main()
