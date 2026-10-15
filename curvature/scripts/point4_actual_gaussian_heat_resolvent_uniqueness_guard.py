#!/usr/bin/env python3
"""Exact supporting-result gate for the actual scalar right-domain equation."""
from __future__ import annotations
import argparse
import hashlib
import pathlib
import re
import stat
import sys

sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[2]
MODULE = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ActualGaussianHeatResolventUniqueness.lean'
PROBE = 'curvature/scripts/point4_actual_gaussian_heat_resolvent_uniqueness_probe.lean'
PINS = {
    MODULE: '6b33fd9b8981fc8c3a5155767cb9e001d4fcd6dfd3944122e04177b63a03dfed',
    PROBE: 'fdeba06a3d758c7dbf53083060a3a1370dcff09a2a4d0fded49dd67a281229f9',
}
NAMES = tuple('RicciFlow.AnalyticPDE.' + name for name in (
    'eq_zero_of_actualHeat_right_generator_positive_eigenvalue',
    'actualHeat_right_generator_equation_unique',
    'eq_actualGaussianHeatResolvent_of_actualHeat_right_generator_equation',
    'existsUnique_actualHeat_right_generator_equation',
))
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def regular(path):
    for p in (path, *path.parents):
        value = p.lstat()
        assert not stat.S_ISLNK(value.st_mode) and not getattr(value, 'st_file_attributes', 0) & 0x400, 'Input alias: ' + str(p)
        assert stat.S_ISREG(value.st_mode) if p == path else stat.S_ISDIR(value.st_mode), str(p)
    return path.read_bytes()


def check_pair(root=ROOT):
    before = {p: regular(root / p) for p in PINS}
    for p, expected in PINS.items():
        assert hashlib.sha256(before[p]).hexdigest() == expected, 'Qualified Source drift: ' + p
    source = before[PROBE].decode('utf8')
    assert tuple(re.findall(r'^#print axioms (\S+)$', source, re.M)) == NAMES
    assert len(re.findall(r'^def \w+FullSignatureAssignment\s*:', source, re.M)) == 4
    assert source.count('\nexample ') == 2 and 'Fin 0' in source and 'lam \u2022 u - 0' in source
    assert {p: regular(root / p) for p in PINS} == before, 'Source input mutation'
    return source


def check_output(source, output):
    expected = tuple(re.findall(r'^#print axioms (\S+)$', source, re.M))
    assert expected == NAMES and len(set(expected)) == 4, 'Probe record contract drift'
    records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [name for name, _ in records] + clean
    assert len(names) == 4 and set(names) == set(expected), 'Missing/duplicate/extra actual axiom record'
    assert not clean, 'Qualified four-group axiom view changed'
    for name, raw in records:
        items = [item.strip() for item in raw.split(',') if item.strip()]
        assert len(items) == len(set(items)) == 3 and set(items) == STANDARD, (name, items)
    for name in expected:
        assert len(re.findall(r'^@' + re.escape(name.rsplit('.', 1)[1]) + r'\s*:', output, re.M)) == 1, 'Missing/duplicate full type output: ' + name
    assert not re.search(r'(^|\n).*\berror:', output), 'Failed probe compilation'
    return set(names)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--axiom-output', type=pathlib.Path)
    args = parser.parse_args()
    import point4_smooth_master_composition as current
    current.verify_current()
    source = check_pair()
    if args.axiom_output:
        before = regular(args.axiom_output)
        check_output(source, before.decode('utf8'))
        assert regular(args.axiom_output) == before, 'Actual output mutation'
    print('Actual scalar Gaussian right-domain uniqueness Source' + (' and four actual full-type/standard-axiom groups' if args.axiom_output else '') + ' verified; Point4 OPEN.')


if __name__ == '__main__':
    main()
