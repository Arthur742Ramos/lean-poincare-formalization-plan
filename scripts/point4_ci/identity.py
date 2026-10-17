"""Exact-input identity for one consolidated run; cache hits never certify proofs."""
from __future__ import annotations

import hashlib
import fcntl
import json
import os
import platform
from pathlib import Path
import re
import stat
import subprocess

MAX_SOURCE_BYTES = 128 * 1024 * 1024
MAX_SOURCE_FILE = 8 * 1024 * 1024
MAX_SOURCE_FILES = 10000


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "Duplicate JSON key")
            result[key] = value
        return result
    return json.loads(data.decode("utf8"), object_pairs_hook=pairs,
                      parse_constant=lambda _: require(False, "Non-finite JSON"))


def regular(path, maximum=MAX_SOURCE_FILE):
    path = Path(path)
    require(path.is_absolute(), "Absolute file path required")
    for parent in path.parents:
        require(stat.S_ISDIR(parent.lstat().st_mode), "Non-directory/symlink ancestor")
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= maximum, "Nonregular/oversized input")
    sticky = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    with path.open("rb") as handle:
        require(sticky(os.fstat(handle.fileno())) == sticky(before), "Input changed at open")
        data = handle.read(maximum + 1)
        require(sticky(os.fstat(handle.fileno())) == sticky(before), "Input changed while reading")
    require(len(data) == before.st_size and sticky(path.lstat()) == sticky(before), "Input changed after reading")
    return data


# New coordinator/broker writes share this single bounded ledger. Native legacy
# processes' own build/resource output domains retain their original contracts.
LEDGER_LIMIT = 64 * 1024 * 1024
DEFAULT_OUTPUT_BYTES = 24 * 1024 * 1024 * 1024
DEFAULT_OUTPUT_ENTRIES = 300000


class OutputBudget:
    def __init__(self, root, initialize=False, maximum=DEFAULT_OUTPUT_BYTES,
                 entries=DEFAULT_OUTPUT_ENTRIES):
        self.root = Path(root)
        require(self.root.is_absolute() and self.root == self.root.resolve(), 'Canonical budget root required')
        self.maximum, self.entries = maximum, entries
        self.lock = self.root / 'output-budget.lock'
        self.path = self.root / 'output-budget.json'
        if initialize:
            require(maximum >= LEDGER_LIMIT and entries >= 3, 'Budget cannot hold its own fixed metadata')
            with self.lock.open('xb'):
                pass
            value = dict(schema='point4-output-reservation-v1', maximum=maximum, entries=entries,
                         bytes=LEDGER_LIMIT, count=3, reservations={})
            with self.path.open('xb') as handle:
                handle.write(canonical(value))

    def reserve(self, path, size=0, kind='file'):
        path = Path(path)
        require(path.is_absolute() and type(size) is int and size >= 0 and kind in ('file','directory','symlink'), 'Invalid output reservation')
        key = digest(canonical(dict(path=str(path),kind=kind)))
        lock_fd = os.open(self.lock, os.O_RDWR | os.O_NOFOLLOW)
        try:
            require(stat.S_ISREG(os.fstat(lock_fd).st_mode), 'Invalid budget lock')
            fcntl.flock(lock_fd, fcntl.LOCK_EX)
            fd = os.open(self.path, os.O_RDWR | os.O_NOFOLLOW)
            try:
                require(stat.S_ISREG(os.fstat(fd).st_mode) and os.fstat(fd).st_size <= LEDGER_LIMIT, 'Invalid budget ledger')
                raw = os.read(fd, LEDGER_LIMIT + 1)
                require(len(raw) <= LEDGER_LIMIT, 'Budget ledger exceeded')
                value = strict_json(raw)
                require(value['schema']=='point4-output-reservation-v1' and value['maximum']==self.maximum
                        and value['entries']==self.entries, 'Budget policy differs')
                previous = value['reservations'].get(key)
                next_size = max(size, previous or 0)
                added = next_size - (previous or 0)
                added_count = 1 if previous is None else 0
                require(value['bytes'] + added <= self.maximum, 'Output byte reservation exhausted')
                require(value['count'] + added_count <= self.entries, 'Output file reservation exhausted')
                value['bytes'] += added; value['count'] += added_count
                value['reservations'][key] = next_size
                encoded = canonical(value)
                require(len(encoded) <= LEDGER_LIMIT, 'Budget metadata reservation exhausted')
                os.lseek(fd,0,os.SEEK_SET)
                view=memoryview(encoded)
                while view:
                    written=os.write(fd,view);require(written>0,'Budget ledger write failed');view=view[written:]
                os.ftruncate(fd,len(encoded));os.fsync(fd)
            finally:
                os.close(fd)
        finally:
            fcntl.flock(lock_fd, fcntl.LOCK_UN);os.close(lock_fd)

    def mkdir(self,path,exist_ok=False):
        self.reserve(path,kind='directory')
        Path(path).mkdir(exist_ok=exist_ok)
        require(stat.S_ISDIR(Path(path).lstat().st_mode),'Invalid output directory')

    def file(self,path,maximum=DEFAULT_OUTPUT_BYTES):
        return ReservedFile(self,path,maximum)


class ReservedFile:
    def __init__(self,budget,path,maximum):
        self.budget,self.path,self.maximum=budget,Path(path),maximum
        self.written=0
        budget.reserve(self.path)
        self.handle=self.path.open('xb')

    def write(self,data):
        require(isinstance(data,(bytes,bytearray,memoryview)), 'Binary output required')
        require(self.written+len(data)<=self.maximum,'Per-file output reservation exhausted')
        self.budget.reserve(self.path,self.written+len(data))
        self.handle.write(data);self.written+=len(data)
        return len(data)

    def __enter__(self):return self
    def __exit__(self,*args):self.handle.close()


def output_budget():
    return OutputBudget(Path(os.environ['P4_CI_BUDGET_ROOT']))


def command(argv, cwd, env=None, maximum=1024 * 1024):
    value = subprocess.run(argv, cwd=cwd, env=env, check=True, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=120)
    require(len(value.stdout) <= maximum and len(value.stderr) <= maximum, "Identity command output too large")
    return value.stdout


def git(root, *args):
    return command(["git", "--no-replace-objects", "-c", "core.fsmonitor=false", "-C", str(root), *args], root,
                   maximum=32 * 1024 * 1024 if 'ls-tree' in args else 1024 * 1024)


def source_identity(root, expected_sha, expected_tree):
    root = Path(root)
    require(root.is_absolute() and root == root.resolve(), "Canonical repository root required")
    head = git(root, "rev-parse", "HEAD").decode().strip()
    tree = git(root, "rev-parse", "HEAD^{tree}").decode().strip()
    require(re.fullmatch(r"[a-f0-9]{40}", expected_sha or "") and head == expected_sha, "Candidate HEAD differs")
    require(re.fullmatch(r"[a-f0-9]{40}", expected_tree or "") and tree == expected_tree, "Candidate tree differs")
    git(root, "diff", "--exit-code", "HEAD", "--", ".")
    git(root, "diff", "--cached", "--exit-code", "HEAD", "--", ".")
    raw = git(root, "ls-tree", "-rz", "HEAD")
    require(len(raw) <= 4 * 1024 * 1024, "Source catalogue too large")
    rows, total = {}, 0
    for record in raw.split(b"\0")[:-1]:
        descriptor, name = record.split(b"\t", 1)
        mode, kind, oid = descriptor.decode().split()
        name = name.decode("utf8")
        require(mode in ("100644", "100755") and kind == "blob", "Unsupported tracked Source kind")
        rel = Path(name)
        require(not rel.is_absolute() and all(x not in ("", ".", "..") for x in rel.parts), "Unsafe Source path")
        require(name not in rows and len(rows) < MAX_SOURCE_FILES, "Source duplicate/count exceeded")
        data = regular(root / rel)
        require(bool((root / rel).stat().st_mode & 0o111) == (mode == "100755"), "Source mode differs")
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == oid, "Physical Source differs from native Git blob")
        total += len(data)
        require(total <= MAX_SOURCE_BYTES, "Source aggregate exceeded")
        rows[name] = dict(mode=mode, blob=oid, bytes=len(data), sha256=digest(data))
    return dict(head=head, tree=tree, files=len(rows), bytes=total, catalogue_sha256=digest(canonical(rows)))


def toolchain_identity(root, real_lake, plan):
    package = Path(root) / "curvature"
    toolchain = regular(package / "lean-toolchain")
    require(toolchain == b"leanprover/lean4:v4.33.0\n", "Wrong package toolchain")
    manifest_data = regular(package / "lake-manifest.json")
    manifest = strict_json(manifest_data)
    dependencies = []
    for row in manifest["packages"]:
        if row["type"] == "git":
            require(re.fullmatch(r"[A-Za-z0-9_-]+", row["name"] or ""), "Unsafe dependency")
            dep = package / ".lake/packages" / row["name"]
            head = git(dep, "rev-parse", "HEAD").decode().strip()
            require(head == row["rev"] and re.fullmatch(r"[0-9a-f]{40}", head), "Dependency revision differs")
            git(dep, "diff", "--exit-code", "HEAD", "--", ".")
            git(dep, "diff", "--cached", "--exit-code", "HEAD", "--", ".")
            dependencies.append(dict(name=row["name"], head=head))
            if row["name"] == "mathlib":
                require(head == plan["mathlib_commit"], "Wrong Mathlib")
    require(any(r["name"] == "mathlib" for r in dependencies), "Mathlib missing")
    version = command([real_lake, "env", "lean", "--version"], package).decode().strip()
    require(re.fullmatch(r"Lean \(version 4\.33\.0, [^\n,]+, commit " + plan["compiler_commit"] + r", Release\)", version), "Wrong official compiler")
    prefix = Path(command([real_lake, "env", "lean", "--print-prefix"], package).decode().strip())
    compiler = regular(prefix / "bin/lean", 512 * 1024 * 1024)
    return dict(version=version, compiler_sha256=digest(compiler),
                selected_lake_sha256=digest(regular(prefix / 'bin/lake', 512 * 1024 * 1024)),
                lake_launcher_path=real_lake, lake_launcher_resolved=str(Path(real_lake).resolve()),
                lake_launcher_sha256=digest(regular(Path(real_lake).resolve(), 512 * 1024 * 1024)),
                toolchain_sha256=digest(toolchain),
                manifest_sha256=digest(manifest_data), lakefile_sha256=digest(regular(package / "lakefile.toml")),
                dependencies=dependencies)


def stream_seal(path, maximum=2 * 1024 * 1024 * 1024):
    """Hash large compiled inputs without retaining them in memory."""
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_size <= maximum, 'Invalid compiled input')
    sticky = lambda x: (x.st_dev, x.st_ino, x.st_mode, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
    checksum, total = hashlib.sha256(), 0
    with path.open('rb') as handle:
        require(sticky(os.fstat(handle.fileno())) == sticky(before), 'Compiled input changed at open')
        while True:
            chunk = handle.read(1024 * 1024)
            if not chunk:
                break
            checksum.update(chunk); total += len(chunk)
            require(total <= maximum, 'Compiled input grew beyond bound')
        require(sticky(os.fstat(handle.fileno())) == sticky(before), 'Compiled input changed during hash')
    require(total == before.st_size and sticky(path.lstat()) == sticky(before), 'Compiled input changed after hash')
    return dict(bytes=total, mode=stat.S_IMODE(before.st_mode), sha256=checksum.hexdigest())


def reject_untracked_modules(root):
    """Reject ignored or untracked Lean/native module injection outside builds."""
    top = Path(git(root, 'rev-parse', '--show-toplevel').decode().strip()).resolve()
    tree = git(root, 'ls-tree', '--full-tree', '-rz', 'HEAD')
    tracked = set()
    for record in tree.split(b'\0')[:-1]:
        _, name = record.split(b'\t', 1)
        tracked.add(name.decode('utf8'))
    count = 0
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [n for n in dirs if n not in ('.git', '.lake')]
        count += len(dirs) + len(files)
        require(count <= 300000, 'Dependency Source namespace bound exceeded')
        for name in dirs:
            require(not (Path(parent) / name).is_symlink(), 'Dependency Source directory alias')
        for name in files:
            path = Path(parent) / name
            if path.suffix in ('.lean', '.olean', '.ilean', '.so', '.dylib', '.dll', '.a'):
                require(path.relative_to(top).as_posix() in tracked, 'Untracked/ignored module injection')


def effective_search_resolution(search, package, roots, packages):
    """Resolve Lake's paths in the same cwd used to query its environment."""
    require(package.is_absolute() and package == package.resolve(), 'Noncanonical Lake environment cwd')
    require(type(search) is dict and set(search) == {'LEAN_PATH', 'LEAN_SRC_PATH'}
            and all(type(value) is str for value in search.values()), 'Malformed Lake search environment')
    resolved_search = {}
    for name, value in search.items():
        resolved_search[name] = []
        for raw in filter(None, value.split(os.pathsep)):
            path = Path(raw)
            if not path.is_absolute():
                path = package / path
            require(path.is_dir(), 'Missing/non-directory effective Lean search root: ' + name + '=' + raw)
            resolved = path.resolve(strict=True)
            require(any(resolved.is_relative_to(base) for base in roots) or
                    any(resolved == pkg.resolve() for pkg in packages),
                    'Unknown effective Lean search root: ' + name + '=' + raw)
            resolved_search[name].append(dict(raw=raw, resolved=str(resolved)))
    return dict(package_cwd=str(package), paths=resolved_search)


def compiled_identity(root, real_lake, plan):
    """Seal complete live build/corelib/plugin trees and effective search roots.

    This deliberately hashes bytes on every PRE/POST; no metadata-only shortcut
    treats a changed import as an identical native proof environment.
    """
    package = Path(root) / 'curvature'
    prefix = Path(command([real_lake, 'env', 'lean', '--print-prefix'], package).decode().strip()).resolve()
    search = strict_json(command([real_lake, 'env', 'python3', '-c',
        'import json,os;print(json.dumps({k:os.environ.get(k, "") for k in ("LEAN_PATH","LEAN_SRC_PATH")}))'], package))
    manifest = strict_json(regular(package / 'lake-manifest.json'))
    packages = [package]
    for row in manifest['packages']:
        if row['type'] == 'git':
            packages.append(package / '.lake/packages' / row['name'])
        elif row['type'] == 'path':
            # Lake manifest path dependencies are relative to the package root.
            candidate = (package / row['dir']).resolve()
            require(candidate.is_relative_to(Path(root)), 'External path dependency')
            packages.append(candidate)
        else:
            raise RuntimeError('Unknown dependency kind')
    roots, config_files = [prefix / 'lib'], []
    if (prefix / 'src').is_dir():
        roots.append(prefix / 'src')
    for pkg in packages:
        reject_untracked_modules(pkg)
        lake = pkg / '.lake'
        if lake.exists():
            require(not lake.is_symlink() and lake.is_dir(), 'Aliased Lake output root')
            for path in lake.iterdir():
                if path.is_file() and not path.is_symlink():
                    config_files.append(path)
            if (lake / 'build').exists():
                roots.append(lake / 'build')
                lib = lake / 'build/lib/lean'
                if lib.is_dir():
                    module_count = 0
                    for parent, dirs, files in os.walk(lib, followlinks=False):
                        module_count += len(dirs) + len(files)
                        require(module_count <= 300000, 'Compiled module namespace exceeded')
                        for name in files:
                            # Lean's split/private/server oleans share the same
                            # source module stem; no package may shadow a module
                            # it has no checked-out Source for.
                            if '.olean' in name or name.endswith('.ilean'):
                                path = Path(parent) / name
                                rel = path.relative_to(lib).as_posix()
                                stem = rel.split('.olean', 1)[0] if '.olean' in rel else rel[:-len('.ilean')]
                                require((pkg / (stem + '.lean')).is_file(), 'Injected compiled module has no package Source')
    roots = sorted(set(path.resolve() for path in roots))
    search_resolution = effective_search_resolution(search, package, roots, packages)
    rows, total, count = {}, 0, 0
    for base in roots:
        require(base.is_dir() and not base.is_symlink(), 'Compiled root alias')
        for parent, dirs, files in os.walk(base, followlinks=False):
            count += len(dirs) + len(files)
            require(count <= 300000, 'Compiled namespace bound exceeded')
            for name in dirs:
                require(not (Path(parent) / name).is_symlink(), 'Compiled directory alias')
            for name in files:
                path = Path(parent) / name
                if path.is_symlink():
                    before_alias = path.lstat()
                    link = os.readlink(path)
                    target = path.resolve(strict=True)
                    require(any(target.is_relative_to(x) for x in roots), 'Compiled alias escapes sealed roots')
                    row = dict(link=link, target=str(target), **stream_seal(target))
                    after_alias = path.lstat()
                    sticky_alias = lambda x: (x.st_dev, x.st_ino, x.st_mode, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
                    require(sticky_alias(before_alias) == sticky_alias(after_alias) and os.readlink(path) == link, 'Compiled alias changed during seal')
                else:
                    row = stream_seal(path)
                total += row['bytes']
                require(total <= 32 * 1024 * 1024 * 1024, 'Compiled aggregate bound exceeded')
                rows[str(path)] = row
    for path in config_files:
        row = stream_seal(path); total += row['bytes']
        require(total <= 32 * 1024 * 1024 * 1024, 'Compiled aggregate bound exceeded')
        rows[str(path)] = row
    return dict(search=search, search_resolution=search_resolution,
                roots=[str(x) for x in roots], files=len(rows), bytes=total,
                inventory_sha256=digest(canonical(rows)))


def execution_identity(root, real_lake, plan, argv, cwd, env):
    source = source_identity(root, env.get("P4_CI_EXPECTED_SHA"), env.get("P4_CI_EXPECTED_TREE"))
    toolchain = toolchain_identity(root, real_lake, plan)
    compiled = compiled_identity(root, real_lake, plan)
    # Hash values, never disclose environment secrets in receipts. Provenance-only
    # case/step fields do not affect the invoked command; all other env participates.
    effective = {k: digest(v.encode()) for k, v in env.items()
                 if k not in ("P4_CI_CASE", "P4_CI_STEP", "_", "SHLVL")}
    return dict(source=source, toolchain=toolchain, compiled_inputs=compiled, argv=argv, cwd=str(Path(cwd).resolve()),
                environment_sha256=digest(canonical(effective)),
                platform=dict(system=platform.system(), machine=platform.machine(), release=platform.release()),
                plan_sha256=digest(canonical(plan)),
                tooling_source=source_identity(Path(env["P4_CI_TOOLING_ROOT"]), env["P4_CI_TOOLING_SHA"], env["P4_CI_TOOLING_TREE"]),
                broker_sha256=digest(regular(Path(__file__).absolute().with_name("command_broker.py"))),
                identity_module_sha256=digest(regular(Path(__file__).absolute())))
