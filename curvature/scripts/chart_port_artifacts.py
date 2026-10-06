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
    """Inspect the first olean found, matching Lean's search-path precedence."""
    relative = name.replace('.', '/') + '.olean'
    for root in artifact_roots:
        olean = root / relative
        if not olean.exists():
            continue
        needed = required_import_files(olean, source_bytes)
        missing = [str(p) for p in needed if not p.is_file() or p.is_symlink()]
        return dict(ready=not missing, selected_olean=str(olean), required=[str(p) for p in needed], missing=missing,
                    source_module_system=is_module_source(source_bytes), lean_version='4.33.0')
    return dict(ready=False, selected_olean=None, required=[relative], missing=[relative],
                source_module_system=is_module_source(source_bytes), lean_version='4.33.0')
