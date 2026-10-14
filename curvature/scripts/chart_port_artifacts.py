"""Lean 4.33 import files, following Environment.lean and Lake.Build.Module."""
from pathlib import Path
import re

def without_comments(data):
    text = data.decode('utf8')
    clean, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
            continue
        if depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
            continue
        if text[i] == '\n' or not depth:
            clean.append(text[i])
        i += 1
    return '\n'.join(line.split('--', 1)[0] for line in ''.join(clean).splitlines())

def is_module_source(source_bytes):
    header = without_comments(source_bytes).lstrip()
    return re.match(r'module(?:\s|$)', header) is not None

def required_import_files(olean, source_bytes):
    """Legacy IR is embedded; module-system IR and olean parts are separate."""
    paths = [olean]
    if is_module_source(source_bytes):
        paths += [Path(str(olean) + '.server'), Path(str(olean) + '.private'),
                  olean.with_suffix('.ir.sig'), olean.with_suffix('.ir')]
    elif olean.with_suffix('.ir.sig').exists():
        # Environment.readIRPartsOfMod loads full IR whenever ir.sig exists.
        paths += [olean.with_suffix('.ir.sig'), olean.with_suffix('.ir')]
    return paths

def artifact_status(name, artifact_roots, source_bytes):
    """Inspect the first package root, following pinned Lean findWithExt."""
    relative = name.replace('.', '/') + '.olean'
    for root in artifact_roots:
        olean = root / relative
        package = root / name.split('.')[0]
        if not (package.is_dir() or package.with_suffix('.olean').exists()):
            continue
        needed = required_import_files(olean, source_bytes)
        missing = [str(p) for p in needed if not p.is_file() or p.is_symlink()]
        for path in needed:
            for parent in path.parents:
                if not parent.is_dir() or parent.is_symlink():
                    missing.append(str(parent))
                if parent == root:
                    break
        return dict(ready=not missing, selected_olean=str(olean), required=[str(p) for p in needed], missing=missing,
                    source_module_system=is_module_source(source_bytes), lean_version='4.33.0')
    return dict(ready=False, selected_olean=None, required=[relative], missing=[relative],
                source_module_system=is_module_source(source_bytes), lean_version='4.33.0')


def materialize_pinned_mathlib_cache(cache_root, owned_root, source_root, source_inventory):
    """Copy genuine dependency companions into one owned Mathlib package root.

    Copies confer no fresh-build credit. Partial cached modules still require
    the unchanged finite fallback and all required import companions.
    """
    import hashlib, os, stat
    cache_root, owned_root, source_root = map(Path, (cache_root, owned_root, source_root))
    assert cache_root == source_root / '.lake/build/lib/lean'
    source_catalog = {p:tuple(row) for p,row in source_inventory.items()}
    assert not (owned_root / 'Mathlib').exists(), 'Owned Mathlib package root already exists'
    suffixes = ('.olean.private', '.olean.server', '.olean', '.ir.sig', '.ir')

    def check_path(path, stop, directory=False):
        path.relative_to(stop)
        assert stat.S_ISDIR(stop.lstat().st_mode), 'Namespace root/link drift'
        for parent in path.parents:
            assert stat.S_ISDIR(parent.lstat().st_mode), 'Namespace ancestor/link drift'
            if parent == stop:
                break
        assert (stat.S_ISDIR if directory else stat.S_ISREG)(path.lstat().st_mode), 'Namespace entry/link drift'

    def file_record(path, stop):
        check_path(path, stop)
        before = path.stat(); h = hashlib.sha256(); size = 0
        with path.open('rb') as stream:
            opened = os.fstat(stream.fileno())
            assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns) == (opened.st_dev,opened.st_ino,opened.st_size,opened.st_mtime_ns), 'Namespace file changed before read'
            while chunk := stream.read(65536):
                h.update(chunk); size += len(chunk)
            final = os.fstat(stream.fileno())
        check_path(path, stop); after = path.stat()
        assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns) == (final.st_dev,final.st_ino,final.st_size,final.st_mtime_ns) == (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns), 'Namespace file changed during read'
        return dict(kind='file',bytes=size,sha256=h.hexdigest())

    def inventory(root, stop):
        check_path(root, stop, True); result = {}
        for base, dirs, files in os.walk(root, followlinks=False):
            base = Path(base); check_path(base, stop, True)
            for name in sorted(dirs):
                path = base / name; check_path(path, stop, True)
                relative = path.relative_to(root).as_posix()
                assert relative not in result
                result[relative] = dict(kind='directory')
            for name in sorted(files):
                path = base / name; relative = path.relative_to(root).as_posix()
                assert relative not in result
                result[relative] = file_record(path, stop)
        return result

    namespace = cache_root / 'Mathlib'
    cache_before = inventory(namespace, source_root)
    records, sources = {}, {}
    for relative, row in sorted(cache_before.items()):
        if row['kind'] != 'file':
            continue
        suffix = next((s for s in suffixes if relative.endswith(s)), None)
        if suffix is None:
            continue  # Trace, ilean and lock metadata confer no import readiness.
        source_relative = 'Mathlib/' + relative[:-len(suffix)] + '.lean'
        assert source_relative in source_catalog, 'Cached module outside pinned source inventory'
        if source_relative not in sources:
            source = source_root / source_relative
            source_record = file_record(source, source_root)
            check_path(source, source_root); raw = source.read_bytes(); check_path(source, source_root)
            mode, kind, blob = source_catalog[source_relative]
            assert mode in ('100644','100755') and kind == 'blob'
            assert len(raw) == source_record['bytes'] and hashlib.sha256(raw).hexdigest() == source_record['sha256']
            assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob, 'Pinned cached source drift'
            sources[source_relative] = dict(source_record,blob=blob)
        records[relative] = row
    assert records and len(records) <= 5 * len(source_catalog), 'Finite pinned companion bound exceeded'
    assert stat.S_ISDIR(owned_root.lstat().st_mode), 'Owned root/link drift'
    owned_namespace = owned_root / 'Mathlib'; owned_namespace.mkdir()
    for relative, row in sorted(records.items()):
        incoming_path = namespace / relative; target = owned_namespace / relative
        target.parent.mkdir(parents=True,exist_ok=True)
        check_path(incoming_path, source_root); check_path(target.parent, owned_root, True)
        h = hashlib.sha256(); size = 0
        with incoming_path.open('rb') as incoming, target.open('xb') as outgoing:
            while chunk := incoming.read(65536):
                h.update(chunk); size += len(chunk); outgoing.write(chunk)
        assert dict(kind='file',bytes=size,sha256=h.hexdigest()) == row, 'Cached input changed during owned copy'
        assert file_record(incoming_path,source_root) == row
        assert file_record(target,owned_root) == row
    assert inventory(namespace,source_root) == cache_before, 'Full cached namespace PREPOST drift'
    owned_after = inventory(owned_namespace,owned_root)
    assert {p:row for p,row in owned_after.items() if row['kind']=='file'} == records, 'Exact owned companion inventory drift'
    expected_dirs = {str(Path(p).parent).replace('\\','/') for p in records if str(Path(p).parent) != '.'}
    expected_dirs |= {str(parent).replace('\\','/') for p in records for parent in Path(p).parents if str(parent) != '.'}
    assert {p for p,row in owned_after.items() if row['kind']=='directory'} == expected_dirs, 'Exact owned directory inventory drift'
    for relative, row in sources.items():
        assert file_record(source_root / relative,source_root) == {k:v for k,v in row.items() if k!='blob'}, 'Pinned cached source PREPOST drift'
    assert {p:tuple(row) for p,row in source_inventory.items()} == source_catalog, 'Pinned source catalog PREPOST drift'
    return dict(namespace='Mathlib',cache_root=str(cache_root),owned_root=str(owned_root),
                cached_companions=records,pinned_sources=sources,cached_namespace_inventory=cache_before,
                owned_namespace_inventory=owned_after,copied_dependency_cache=True,fresh_local_compilations=0)
