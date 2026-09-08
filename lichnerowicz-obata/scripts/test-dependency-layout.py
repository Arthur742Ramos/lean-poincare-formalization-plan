"""Regression tests for the registry's project-scoped build sandbox."""

import copy
import importlib.util
import json
from pathlib import Path
import tomllib
import unittest

spec = importlib.util.spec_from_file_location(
    "package_check", Path(__file__).with_name("check-package.py"))
package = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package)


class DependencyLayout(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((package.ROOT / "lake-manifest.json").read_text())
        self.config = tomllib.loads((package.ROOT / "lakefile.toml").read_text())

    def test_pinned_git_layout(self):
        package.check_dependency_layout(self.manifest, self.config)

    def test_original_sibling_manifest_is_rejected(self):
        self.manifest["packages"][0] = {
            "name": "AlmostSchur", "type": "path", "dir": "../almost-schur"}
        with self.assertRaises(SystemExit):
            package.check_dependency_layout(self.manifest, self.config)

    def test_sibling_lakefile_is_rejected(self):
        self.config["require"] = [{"name": "AlmostSchur", "path": "../almost-schur"}]
        with self.assertRaises(SystemExit):
            package.check_dependency_layout(self.manifest, self.config)

    def test_git_subdirectory_is_rejected(self):
        self.manifest["packages"][0]["subDir"] = "almost-schur"
        with self.assertRaises(SystemExit):
            package.check_dependency_layout(self.manifest, self.config)

    def test_old_git_dependency_is_rejected(self):
        self.manifest["packages"].append({"type": "git", "name": "AlmostSchur"})
        with self.assertRaises(SystemExit):
            package.check_dependency_layout(self.manifest, self.config)

    def test_vendor_inventory_matches_pin(self):
        package.check_flat_vendor()

    def test_library_output_override_is_rejected(self):
        self.config["lean_lib"][0]["buildDir"] = "vendor/almost-schur/.lake"
        with self.assertRaises(SystemExit):
            package.check_dependency_layout(self.manifest, self.config)


if __name__ == "__main__":
    unittest.main()
