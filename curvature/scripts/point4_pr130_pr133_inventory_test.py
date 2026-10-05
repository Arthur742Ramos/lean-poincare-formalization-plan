#!/usr/bin/env python3
"""Only the new exact-parent inventory composition is tested here."""
import point4_pr130_pr133_inventory as guard

def rejects(fn, *args):
    try: fn(*args)
    except AssertionError: return
    raise AssertionError('Invalid composition was accepted')

def main():
    prior=guard.tree(guard.REPAIR); master=guard.tree(guard.MASTER)
    union=guard.resolve_inventory(prior,master)
    assert set(union)==set(prior)|set(master)
    for p in union:
        assert union[p]==(prior[p] if p in guard.PRIOR_ROOTS or p not in master else master[p])
    for p in set(prior)&set(master):
        if p.endswith('.lean') and p not in guard.PRIOR_ROOTS:
            assert prior[p]==master[p]==union[p], 'Competing mathematical bytes'
    for p in ('curvature/scripts/point4_c2_initial_heat_source_test.py',
              'curvature/scripts/point4_weighted_hessian_release_guard.py'):
        assert union[p]==master[p], 'Master dispatcher must remain exact'
    bad=dict(master); bad['curvature/scripts/point4_audit.sh']=('100644','0'*40)
    rejects(guard.resolve_inventory,prior,bad)
    bad=dict(master); bad['curvature/PoincareCurvature/Analysis/TimeDependentGram.lean']=('100644','0'*40)
    rejects(guard.resolve_inventory,prior,bad)
    bad=dict(master); p=next(iter(guard.SHARED_DIFFERENCES)); bad[p]=prior[p]
    rejects(guard.resolve_inventory,prior,bad)
    bad=dict(master); bad[next(iter(guard.ADDED))]=('100644','0'*40)
    rejects(guard.resolve_inventory,prior,bad)
    guard.validate_inventory(union,dict(union))
    for p in ('curvature/scripts/point4_c2_initial_heat_source_test.py',
              'curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/BoundarylessInitialMetricLocalization.lean'):
        bad=dict(union); bad[p]=('100644','0'*40); rejects(guard.validate_inventory,union,bad)
    bad=dict(union); bad['curvature/Unexpected.lean']=('100644','0'*40)
    rejects(guard.validate_inventory,union,bad)
    bad=dict(union); bad.pop('curvature/scripts/point4_c2_metric_localization_probe.lean')
    rejects(guard.validate_inventory,union,bad)
    bad=dict(union); p='curvature/scripts/point4_c2_initial_heat_source_test.py';bad[p]=('100755',union[p][1])
    rejects(guard.validate_inventory,union,bad)
    assert guard.public_paths({'a.py'},{'__pycache__/a.cpython-312.pyc'})=={'a.py'}
    rejects(guard.public_paths,{'__pycache__/a.pyc'},set())
    rejects(guard.public_paths,{'build.olean'},set())
    assert '__pycache__/evil.lean' in guard.public_paths(set(),{'__pycache__/evil.lean'})
    assert 'outside.pyc' in guard.public_paths(set(),{'outside.pyc'})
    guard.main()
    print('New composition passed: exact master dispatch, prior root selection, unchanged mathematical bytes, eleven rejection cases; no compiler evidence simulated')

if __name__ == '__main__':
    main()
