#!/usr/bin/env python3
"""Separate smooth-target audit. Run full builds only under parent admission.

Copied-cache elaboration is development evidence only. Canonical audit gates
and their source/regression guards remain independently required and unchanged.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys
from datetime import datetime, timezone

parser = argparse.ArgumentParser()
parser.add_argument('--no-build', action='store_true')
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
evidence = args.output.resolve()
evidence.mkdir(parents=True, exist_ok=False)
gates = {}
def command(name, argv):
    start = datetime.now(timezone.utc).isoformat()
    log = evidence / (name+'.log')
    try:
        with log.open('wb') as stream:
            proc = subprocess.run(argv, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
        code = proc.returncode
    except OSError as exc:
        log.write_bytes(str(exc).encode()); code = None
    digest = hashlib.sha256()
    with log.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''): digest.update(chunk)
    (evidence / (name+'.json')).write_text(json.dumps({'argv':argv,'cwd':str(root),
        'start_utc':start,'end_utc':datetime.now(timezone.utc).isoformat(),
        'exit':code,'log_sha256':digest.hexdigest()},indent=2),encoding='utf8')
    with log.open('rb') as stream: data = stream.read(1024*1024+1)
    # Full build logs remain lossless on disk; only bounded gate output is parsed.
    return code == 0, data.decode('utf8', errors='replace') if len(data)<=1024*1024 else ''

try:
    toolchain = (root/'lean-toolchain').read_text().strip()
    manifest = json.loads((root/'lake-manifest.json').read_text())
    mathlib = [p for p in manifest['packages'] if p['name']=='mathlib']
    gates['pins'] = toolchain == 'leanprover/lean4:v4.33.0' and len(mathlib)==1 and mathlib[0]['rev']=='db584cd6d46c92f209a44c0f1c829460d327499d'
except (OSError, KeyError, ValueError): gates['pins'] = False

try:
    baseline = json.loads((root/'scripts/point4_smooth_forward_interface_sha256.json').read_text())
    gates['frozen_interfaces'] = bool(baseline) and all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in baseline.items())
except (OSError, ValueError): gates['frozen_interfaces'] = False

scan_ok, scan = command('source-scan',[sys.executable,'scripts/point4_scan.py','cheats','PoincareCurvature'])
gates['source_scan'] = scan_ok and bool(re.search(r'^TOTAL 0$',scan,re.M))
version_ok, version = command('compiler-version',['lake','env','lean','--version'])
gates['official_version'] = version_ok and 'version 4.33.0' in version and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version

gates['full_build'] = False
gates['new_module_build'] = False
if not args.no_build and gates['pins'] and gates['official_version'] and gates['frozen_interfaces']:
    gates['full_build'], _ = command('full-build',['lake','build'])
    gates['new_module_build'], _ = command('smooth-module-build',['lake','build','PoincareCurvature.Geometry.Manifold.RicciFlow.SmoothForwardContract'])

gates['exact_type'], probe = command('completion',['lake','env','lean','scripts/point4_smooth_forward_completion.lean'])
target = 'RicciFlow.SmoothForward.existenceUniquenessFamily_pointFourSmoothForwardModel'
allowed = {'propext','Classical.choice','Quot.sound'}
blocks = re.findall(re.escape(target)+r"' depends on axioms:\s*\[([^\]]*)\]",probe)
no_axioms = re.findall(re.escape(target)+r"' does not depend on any axioms",probe)
gates['standard_axioms'] = gates['exact_type'] and (
    (len(blocks)==1 and not no_axioms and {x.strip() for x in blocks[0].split(',') if x.strip()} <= allowed)
    or (len(no_axioms)==1 and not blocks))

closed = not args.no_build and all(gates.values())
report={'scope':'separate smooth forward model target','target':target,'gates':gates,
    'verdict':'SMOOTH FORWARD TARGET CLOSED' if closed else 'SMOOTH FORWARD TARGET OPEN',
    'canonical_point4':'NO STATUS CHANGE; canonical completion requires its own actual audit'}
(evidence/'verdict.json').write_text(json.dumps(report,indent=2),encoding='utf8')
print(json.dumps(report))
raise SystemExit(0 if closed else 1)
