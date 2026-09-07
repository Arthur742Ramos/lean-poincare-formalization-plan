"""Reject regressions discovered by the semantic entry audit, using isolated fixtures."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("entry_validator", ROOT / "scripts/validate-formalization.py")
validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(validator)


def check_fixture(change, message=None):
    with tempfile.TemporaryDirectory(prefix="almost-schur-entry-regression-") as folder:
        fixture = Path(folder)
        for name in ("Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml", "LICENSE"):
            shutil.copyfile(ROOT / name, fixture / name)
        comparator = json.loads((fixture / "comparator.json").read_text())
        metadata = yaml.safe_load((fixture / "formalization.yaml").read_text())
        change(comparator, metadata)
        (fixture / "comparator.json").write_text(json.dumps(comparator))
        (fixture / "formalization.yaml").write_text(yaml.safe_dump(metadata))
        validator.ROOT = fixture
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                validator.main()
        except SystemExit as error:
            if message is None or message not in str(error):
                raise AssertionError(f"unexpected validator failure: {error}") from error
        else:
            if message is not None:
                raise AssertionError("entry validator accepted a known regression")


check_fixture(lambda c, m: None)
check_fixture(
    lambda c, m: c.update(theorem_names=["AlmostSchurEntry.almostSchur_from_identities"]),
    "theorem surface changed",
)
check_fixture(lambda c, m: c["definition_names"].remove("AlmostSchurEntry.Geometry.curvature"),
              "every geometric statement definition")
check_fixture(lambda c, m: m["sources"][0]["authors"].__setitem__(0, "Pierre De Lellis"),
              "bibliographic source authors")


def omit_selected_result(comparator, metadata):
    metadata["status"]["main_results"] = [
        row for row in metadata["status"]["main_results"]
        if row["declaration"] not in comparator["theorem_names"]
    ]


check_fixture(omit_selected_result, "recorded among the main results")
print("Entry baseline passed; algebra-only selection, missing definition, wrong attribution, "
      "and missing selected result were rejected.")
