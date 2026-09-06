"""Check the complete vendored source inventory and its recorded adapted bytes."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
record = json.loads((root / "dependencies/rellich-vendored.json").read_text())
assert record["repository"] == "https://github.com/abenenson/rellich-kondrachov"
assert record["commit"] == "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"
assert record["relationship"] == "adapts"
rows = record["files"]
paths = {row["path"] for row in rows}
assert len(rows) == len(paths) == 33
assert paths == {str(p.relative_to(root)) for p in (root / "RellichKondrachov").rglob("*.lean")}
for row in rows:
    path = root / row["path"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == row["adapted_sha256"], path
    assert "Authors: Adam Benenson" in path.read_text(), path
    assert len(row["source_sha256"]) == 64
print(f"All {len(rows)} adapted files match the immutable-source inventory and retain author notices.")
