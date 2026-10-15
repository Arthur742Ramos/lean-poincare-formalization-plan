#!/usr/bin/env python3
"""Focused supporting-result gate; full Point4 and inverse-domain claims remain OPEN."""
from __future__ import annotations
import argparse
import hashlib
import pathlib
import re
import stat
import sys
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[2]
MODULE = 'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ActualGaussianHeatResolvent.lean'
PROBE = 'curvature/scripts/point4_actual_gaussian_heat_resolvent_probe.lean'
PINS = {MODULE: '3789a35b51db6ec8b429c82365a3a8b590464b80ad3375bd084b8c86d789913b',
        PROBE: 'c241ee02b22368fe808ea428ba4ca30e5e7168c15a9dddc3ff58f28a78890f5e'}
NAMES = tuple('RicciFlow.AnalyticPDE.' + name for name in (
    'integrableOn_actualHeatResolventIntegrand', 'norm_actualGaussianHeatResolvent_le',
    'heatFlowPathBcf_actualGaussianHeatResolvent_shift', 'hasDerivWithinAt_actualGaussianHeatResolvent_zero',
    'uniformContinuous_actualGaussianHeatResolvent', 'exists_actualGaussianHeat_generator_range_witness'))
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def regular(path):
    for p in (path, *path.parents):
        s = p.lstat()
        assert not stat.S_ISLNK(s.st_mode) and not getattr(s, 'st_file_attributes', 0) & 0x400, 'Source alias: '+str(p)
        assert stat.S_ISREG(s.st_mode) if p == path else stat.S_ISDIR(s.st_mode), str(p)
    return path.read_bytes()

def check_pair(root=ROOT):
    before = {p: regular(root/p) for p in PINS}
    for p, h in PINS.items():
        assert hashlib.sha256(before[p]).hexdigest() == h, 'Qualified Source drift: '+p
    source = before[PROBE].decode('utf8')
    assert tuple(re.findall(r'^#print axioms (\S+)$', source, re.M)) == NAMES
    assert len(re.findall(r'^def \w+FullSignatureAssignment\s*:', source, re.M)) == 7
    assert source.count('\nexample ') == 2 and 'Fin 0' in source and 'dif_neg (lt_irrefl (0 : ℝ))' in source
    assert {p: regular(root/p) for p in PINS} == before, 'Source input mutation'
    return source

def check_output(source, output):
    expected = tuple(re.findall(r'^#print axioms (\S+)$', source, re.M))
    assert expected == NAMES and len(set(expected)) == 6, 'Probe record contract drift'
    records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    clean = re.findall(r"'([^']+)' does not depend on any axioms?", output)
    names = [name for name, _ in records] + clean
    assert len(names) == 6 and set(names) == set(expected), 'Missing/duplicate/extra actual axiom record'
    assert not clean, 'Actual qualified six-group axiom view changed'
    for name, raw in records:
        items = [x.strip() for x in raw.split(',') if x.strip()]
        assert len(items) == len(set(items)) == 3 and set(items) == STANDARD, (name, items)
    for name in expected:
        assert len(re.findall(r'^@'+re.escape(name.rsplit('.', 1)[1])+r'\s*:', output, re.M)) == 1, 'Missing/duplicate full type output: '+name
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
        raw = regular(args.axiom_output)
        check_output(source, raw.decode('utf8'))
        assert regular(args.axiom_output) == raw, 'Actual output mutation'
    print('Qualified Source pair'+(' and six actual full-type/standard-axiom groups' if args.axiom_output else '')+' verified; Point4 OPEN.')

if __name__ == '__main__':
    main()
