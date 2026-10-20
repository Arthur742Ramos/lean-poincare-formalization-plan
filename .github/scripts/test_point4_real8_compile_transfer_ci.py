"""Synthetic packaging controls; no compiled-proof or real8 credit."""
import hashlib
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile

import point4_real8_compile_transfer_ci as transfer


class PayloadControls(unittest.TestCase):
    def split_fixture(self, root, count=1500):
        export = root / 'export'; export.mkdir()
        archive = export/'compiled-closure.zip'; archive.write_bytes(bytes(index % 251 for index in range(count)))
        manifest = export/'compiled-closure-manifest.json'; manifest.write_bytes(b'{"synthetic":true}\n')
        return export, {'archive':transfer.ci.identity(archive), 'manifest':transfer.ci.identity(manifest)}

    def test_chunked_payload_exact_contiguous_rejoin_and_small_descriptor(self):
        with tempfile.TemporaryDirectory() as temp, patch.object(transfer, 'PART_BYTES_LIMIT', 512):
            root = Path(temp); export, record = self.split_fixture(root)
            result = transfer.split_public_payload(export, root/'transfer', record, {'sha256':'synthetic'}, time.monotonic()+10)
            self.assertEqual(result['part_count'],3)
            joined = b''.join((root/'transfer'/f'part-{i:02d}'/f'compiled-closure.zip.part-{i:02d}').read_bytes() for i in range(3))
            self.assertEqual(joined, (export/'compiled-closure.zip').read_bytes())
            descriptor=json.loads((root/'transfer/manifest/compiled-closure-parts.json').read_bytes())
            self.assertEqual(descriptor['archive'], record['archive'])
            self.assertEqual([r['bytes'] for r in descriptor['parts'].values()], [512,512,476])
            self.assertEqual((root/'transfer/manifest/compiled-closure-manifest.json').read_bytes(), b'{"synthetic":true}\n')

    def test_chunk_count_hash_and_deadline_fail_closed(self):
        for failure in ('count','hash','deadline'):
            with tempfile.TemporaryDirectory() as temp, patch.object(transfer, 'PART_BYTES_LIMIT', 100):
                root=Path(temp);export,record=self.split_fixture(root,700 if failure=='count' else 500)
                if failure=='hash':record['archive']['sha256']='0'*64
                with self.assertRaises(ValueError):transfer.split_public_payload(export, root/'transfer', record, {},
                    time.monotonic()+(-1 if failure=='deadline' else 10))
                self.assertFalse((root/'transfer/manifest/compiled-closure-parts.json').exists())

    def test_first_successful_full_content_catalogue_identity_is_exact(self):
        rows={'.lake/build/Project.olean':{'bytes':3,'sha256':'known'}}
        pin=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        with patch.object(transfer,'FIRST_SUCCESSFUL_COMPILED_CATALOGUE_SHA256',pin):
            self.assertEqual(transfer.require_first_compiled_catalogue(rows)['file_count'],1)
            with self.assertRaises(ValueError):transfer.require_first_compiled_catalogue(dict(rows,extra={'bytes':0,'sha256':'new'}))
            with self.assertRaises(ValueError):transfer.require_first_compiled_catalogue({'.lake/build/Project.olean':{'bytes':3,'sha256':'changed'}})

    def fixture(self, root):
        pkg = root / 'curvature'
        paths = ['.lake/build/lib/lean/Project.olean', '.lake/build/lib/lean/Project.olean.private',
                 '.lake/build/lib/lean/Project.olean.server', '.lake/build/ir/Project.c',
                 '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean',
                 '.lake/packages/mathlib/.lake/build/lib/libMathlib.so',
                 '.lake/packages/mathlib/.lake/build/bin/cache', '.lake/lakefile.olean']
        for name in paths:
            p = pkg / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(b'public synthetic bytes')
        (pkg / 'not-a-build-input.log').write_bytes(b'excluded synthetic input')
        return pkg, paths

    def test_complete_companions_native_IR_and_configs_retained(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); pkg, paths = self.fixture(root)
            record = transfer.build_payload(pkg, root / 'export', time.monotonic() + 10)
            manifest = json.loads((root / 'export/compiled-closure-manifest.json').read_text())
            self.assertEqual(set(manifest['files']), set(paths))
            self.assertEqual(record['member_count'], len(paths))
            self.assertEqual(manifest['files']['.lake/lakefile.olean']['role'],
                             'hosted-config-provenance-only-do-not-install')
            with zipfile.ZipFile(root / 'export/compiled-closure.zip') as archive:
                self.assertEqual(set(archive.namelist()), set(paths))
                for name in paths:
                    self.assertEqual(transfer.ci.pin(archive.read(name)),
                        {k: manifest['files'][name][k] for k in ('bytes', 'sha256')})

    def test_symlink_cannot_be_exported(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); pkg, _ = self.fixture(root)
            (pkg / '.lake/build/link').symlink_to(pkg / 'not-a-build-input.log')
            with self.assertRaises(ValueError):transfer.build_payload(pkg, root / 'export', time.monotonic() + 10)

    def test_individual_and_aggregate_uncompressed_limits(self):
        for field in ('FILE_BYTES_LIMIT', 'UNCOMPRESSED_LIMIT', 'FILE_COUNT_LIMIT'):
            with tempfile.TemporaryDirectory() as temp, patch.object(transfer, field, 1):
                root = Path(temp); pkg, _ = self.fixture(root)
                with self.assertRaises(ValueError):transfer.build_payload(pkg, root / 'export', time.monotonic() + 10)
                self.assertFalse((root / 'export/compiled-closure.zip').exists())

    def test_compressed_limit_rejects_before_oversized_write(self):
        with tempfile.TemporaryDirectory() as temp, patch.object(transfer, 'ARCHIVE_LIMIT', 100):
            root = Path(temp); pkg, _ = self.fixture(root)
            with self.assertRaises(ValueError):transfer.build_payload(pkg, root / 'export', time.monotonic() + 10)
            self.assertLessEqual((root / 'export/compiled-closure.zip.partial').stat().st_size, 100)
            self.assertFalse((root / 'export/compiled-closure.zip').exists())

    def test_expired_deadline_prevents_export(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); pkg, _ = self.fixture(root)
            with self.assertRaises(ValueError):transfer.build_payload(pkg, root / 'export', time.monotonic() - 1)
            self.assertFalse((root / 'export/compiled-closure.zip').exists())

    def test_path_dependency_generated_files_cannot_be_silently_omitted(self):
        with tempfile.TemporaryDirectory() as temp:
            proof = Path(temp); root = proof / 'hamilton-ivey-reaction'; root.mkdir()
            for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                (root / name).write_bytes(b'public synthetic configuration')
            self.assertFalse(transfer.path_dependency_state(proof)['lake_directory_exists'])
            (root / '.lake/empty').mkdir(parents=True)
            self.assertTrue(transfer.path_dependency_state(proof)['compiled_files_absent'])
            (root / '.lake/omitted.olean').write_bytes(b'reject')
            with self.assertRaises(ValueError):transfer.path_dependency_state(proof)


if __name__ == '__main__':
    unittest.main()
