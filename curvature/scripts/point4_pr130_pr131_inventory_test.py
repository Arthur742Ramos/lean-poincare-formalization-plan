#!/usr/bin/env python3
"""Changed adapter tests; no fabricated compiler evidence."""
import point4_pr130_pr131_inventory as guard

def rejects(fn, *args):
    try: fn(*args)
    except AssertionError: return
    raise AssertionError('Invalid adapter input was accepted')

def main():
    repair = guard.tree(guard.REPAIR); master = guard.tree(guard.MASTER)
    union = guard.resolve_inventory(repair, master)
    assert set(union) == set(repair) | set(master)
    for p in set(master)-set(repair): assert union[p] == master[p]
    for p in repair:
        assert union[p] == (master[p] if p == guard.SHARED_GUARD else repair[p])
    raw = guard.git('cat-file', 'blob', guard.MASTER_GUARD_BLOB)
    adapted = guard.transform_shared_guard(raw)
    assert adapted.replace(guard.HOOK, b'', 1) == raw
    rejects(guard.transform_shared_guard, adapted)
    rejects(guard.transform_shared_guard, raw+b'# drift\n')
    bad = dict(master); bad['curvature/scripts/point4_audit.sh'] = ('100644', '0'*40)
    rejects(guard.resolve_inventory, repair, bad)
    bad = dict(master); bad[next(iter(guard.ADDED))] = ('100644', '0'*40)
    rejects(guard.resolve_inventory, repair, bad)
    guard.validate_inventory(union, dict(union))
    for mutation in ('extra', 'missing', 'bytes', 'mode'):
        bad = dict(union)
        if mutation == 'extra': bad['curvature/Unexpected.lean'] = ('100644', '0'*40)
        if mutation == 'missing': bad.pop(guard.SHARED_GUARD)
        if mutation == 'bytes': bad[guard.SHARED_GUARD] = ('100644', '0'*40)
        if mutation == 'mode': bad[guard.SHARED_GUARD] = ('100755', union[guard.SHARED_GUARD][1])
        rejects(guard.validate_inventory, union, bad)
    marker = object(); evidence = object()
    namespace = {'_manifold_release_original_expected_sources': marker,
                 'expected_sources': marker, 'ADDED': {'prior'},
                 'check_axiom_output': evidence, 'check_audit': evidence,
                 'check_workflow': evidence}
    guard.install_c2_inventory_adapter(namespace)
    assert namespace['_pr130_pr131_original_expected_sources'] is marker
    assert namespace['expected_sources'] is guard.expected_sources
    assert all(namespace[k] is evidence for k in ('check_axiom_output','check_audit','check_workflow'))
    from types import SimpleNamespace
    payload = object(); calls = []
    def imports(value):
        assert value is payload
        calls.append('imports')
    def metadata(value):
        assert value is payload
        calls.append('metadata')
        raise AssertionError('Downstream provenance rejection must propagate')
    original_import = guard.importlib.import_module
    def load(name):
        assert name == 'point4_c2_metric_localization_source_test'
        return SimpleNamespace(legacy_check_imports=imports, legacy_check_metadata=metadata)
    try:
        guard.importlib.import_module = load
        namespace['check_imports'](payload)
        rejects(namespace['check_metadata'], payload)
        assert calls == ['imports', 'metadata']
    finally:
        guard.importlib.import_module = original_import
    rejects(guard.install_c2_inventory_adapter, namespace)
    rejects(guard.install_c2_inventory_adapter, {'expected_sources': marker})
    assert guard.public_paths({'a.py'}, {'__pycache__/a.cpython-312.pyc'}) == {'a.py'}
    rejects(guard.public_paths, {'__pycache__/a.pyc'}, set())
    assert '__pycache__/evil.lean' in guard.public_paths(set(), {'__pycache__/evil.lean'})
    assert 'outside.pyc' in guard.public_paths(set(), {'outside.pyc'})
    guard.main()
    print('Changed adapter controls: exact union/transform/install/cache/delegation pass; twelve rejection cases pass; evidence predicates untouched')

if __name__ == '__main__':
    main()
