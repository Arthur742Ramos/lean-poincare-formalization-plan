"""Verify the immutable source and deterministic adaptations of CurvatureVendor.

Read-only; no network access. Source Git objects must be available locally.
Use --source-repo PATH for a separate clone containing the pinned commit.
--print-records prints computed hashes for manual manifest updates; it never writes.
"""

from pathlib import Path, PurePosixPath
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "AlmostSchur/CurvatureVendor/PROVENANCE.json"
VENDOR = ROOT / "AlmostSchur/CurvatureVendor"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), *args], check=True, capture_output=True
    ).stdout


def checked_relative(value):
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or str(path) != value:
        raise ValueError("noncanonical relative path: " + value)
    return path


def validate(manifest, repo, refresh=False):
    commit = manifest["source_commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("source_commit must be a full immutable SHA-1")
    if git(repo, "cat-file", "-t", commit).strip() != b"commit":
        raise ValueError("source_commit does not name a commit")
    records = manifest["files"]
    targets = [r["target"] for r in records]
    actual = {str(p.relative_to(ROOT)) for p in VENDOR.rglob("*.lean")}
    if len(targets) != len(set(targets)) or set(targets) != actual:
        raise ValueError("manifest must cover every vendored Lean file exactly once")
    computed = []
    for record in records:
        target = checked_relative(record["target"])
        source_path = checked_relative(record["source_path"])
        local_path = ROOT / target
        if local_path.is_symlink() or not local_path.resolve().is_relative_to(VENDOR.resolve()):
            raise ValueError("vendored target escapes its directory: " + str(target))
        blob = git(repo, "rev-parse", f"{commit}:{source_path}").decode().strip()
        if not re.fullmatch(r"[0-9a-f]{40}", record["source_blob"]) or blob != record["source_blob"]:
            raise ValueError("commit/path/blob mismatch: " + str(source_path))
        if git(repo, "cat-file", "-t", blob).strip() != b"blob":
            raise ValueError("source object is not a blob")
        source = git(repo, "cat-file", "blob", blob)
        identity = hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
        if identity != blob:
            raise ValueError("source blob identity mismatch")
        local = local_path.read_bytes()
        text = local.decode("utf-8")
        if re.search(r"^(?:public )?import PoincareCurvature\.", text, flags=re.M):
            raise ValueError("external sibling import: " + str(target))
        delta = "".join(difflib.unified_diff(
            source.decode("utf-8").splitlines(keepends=True),
            text.splitlines(keepends=True),
            fromfile=str(source_path), tofile=str(target), n=3,
        )).encode("utf-8")
        hashes = {
            "source_sha256": sha256(source),
            "local_sha256": sha256(local),
            "adaptation_sha256": sha256(delta),
        }
        if not record.get("changes"):
            raise ValueError("missing adaptation description: " + str(target))
        if not refresh:
            for key, value in hashes.items():
                if record.get(key) != value:
                    raise ValueError(key + " mismatch: " + str(target))
        computed.append({**record, **hashes})
    return computed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-repo", type=Path, default=ROOT)
    parser.add_argument("--print-records", action="store_true")
    args = parser.parse_args()
    try:
        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        records = validate(manifest, args.source_repo, args.print_records)
    except (KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print("curvature provenance FAILED: " + str(error), file=sys.stderr)
        return 1
    if args.print_records:
        print(json.dumps(records, indent=2, ensure_ascii=False))
    else:
        print(f"curvature provenance OK: {len(records)} files, commit {manifest['source_commit']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
