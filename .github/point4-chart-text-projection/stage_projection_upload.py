"""Trusted fixed allowlist staging of new derived text evidence only. No network."""
import hashlib,json,os,pathlib,re,stat
ROOT=pathlib.Path('/tmp/poincare-chart2813-projection');S=ROOT/'source';D=ROOT/'pure';E=ROOT/'input';T=ROOT/'transfer-controller';C=ROOT/'pure-controller';PUBLIC=ROOT/'public'
CAP=256*1024**2;STICKY={}
def sha(raw):return hashlib.sha256(raw).hexdigest()
def identity(i):return [i.st_dev,i.st_ino,i.st_mode,i.st_uid,i.st_gid,i.st_size,i.st_mtime_ns,i.st_ctime_ns]
def read(path,cap=16*1024**2):
    assert path.is_absolute() and path.is_relative_to(ROOT)
    for node in (path,*path.parents):
        m=node.lstat().st_mode;assert not stat.S_ISLNK(m)
        assert stat.S_ISREG(m)if node==path else stat.S_ISDIR(m)
    before=path.stat();assert 0<=before.st_size<=cap
    with path.open('rb')as f:
        assert identity(os.fstat(f.fileno()))==identity(before);raw=f.read(cap+1)
        assert identity(os.fstat(f.fileno()))==identity(before)
    assert len(raw)==before.st_size and identity(path.stat())==identity(before)
    key=str(path)
    if key in STICKY:assert STICKY[key]==identity(before)
    else:STICKY[key]=identity(before)
    return raw

def load(raw):
    def pairs(rows):
        result={}
        for k,v in rows:assert k not in result;result[k]=v
        return result
    def reject(value):raise ValueError('nonfinite JSON')
    return json.loads(raw.decode('utf8',errors='strict'),object_pairs_hook=pairs,parse_constant=reject)

def main():
    assert pathlib.Path(__file__)==S/'stage_projection_upload.py'
    self_raw=read(pathlib.Path(__file__),1024**2)
    assert not PUBLIC.exists() and not PUBLIC.is_symlink()
    assert os.environ['GITHUB_REPOSITORY']=='Arthur742Ramos/lean-poincare-formalization-plan' and os.environ['GITHUB_EVENT_NAME']=='workflow_dispatch'
    actual_run=int(os.environ['GITHUB_RUN_ID']);actual_head=os.environ['GITHUB_SHA'];assert os.environ['GITHUB_RUN_ATTEMPT']=='1'
    assert os.environ['GITHUB_REF']=='refs/heads/point4/chart2813-derived-text-evidence-20261016'
    assert actual_run>0 and re.fullmatch('[0-9a-f]{40}',actual_head)
    control_raw=read(C/'launcher-result.json',1024**2);control=load(control_raw)
    assert type(control['exit'])is int and control['exit']==0 and control['timeout']is False and control['reaped']is True and 0<control['elapsed_seconds']<=125
    stdout=read(C/'stdout.log');stderr=read(C/'stderr.log')
    assert sha(stdout)==control['stdout_sha256'] and stderr==b'' and sha(stderr)==control['stderr_sha256']
    lines=stdout.decode('utf8',errors='strict').splitlines();assert len(lines)==2
    selected=load(lines[0].encode());launcher=load(lines[1].encode())
    assert selected['status']=='BOUNDED_TEXT_SELECTION_PASS' and selected['objects_read']==0 and selected['qualification_credit']==0
    assert launcher['exact_source_unchanged']is True and launcher['qualification_credit']==0
    index_raw=read(D/'SELECTED-TEXT-INDEX.json',8*1024**2);index=load(index_raw)
    assert selected['output']=={'path':str(D/'SELECTED-TEXT-INDEX.json'),'sha256':sha(index_raw),'bytes':len(index_raw)}
    assert index['projection_run_id']==actual_run and index['projection_head']==actual_head
    assert index['head']=='2813ef52a21e13be08532f36ee9f26faf319da72' and index['tree']=='13f982c1be40478cc14b523ea76ed3642fb3ae7e'
    assert index['run_id']==38838232477 and index['job_id']==116772055358 and index['artifact_id']==12021496276
    assert index['archive_sha256']=='743ea30a9daf0fdd8928871d2dfce22411b470f4270acddc817bc4c3c983f716'
    assert index['original_archive_rehashed_by_local_Codex']is False and index['hosted_original_archive_stream_hash_verified_PREPOST']is True
    assert index['inputs_unchanged']is True and index['inputs_PRE']==index['inputs_POST'] and index['object_payloads_read']==0
    assert index['selected_member_count']==len(index['selected_members'])==257 and index['aggregate_raw_bytes']<=128*1024**2
    assert index['resource_PRE']==launcher['launcher_resource_PRE'] or all(index['resource_PRE'][k]==launcher['launcher_resource_PRE'][k]for k in index['resource_PRE']if k!='peak_rss_bytes')
    for row in (launcher['launcher_resource_PRE'],launcher['launcher_resource_POST']):
        assert row['binding']=='source-reviewed-kernel-singleton-v1' and row['cpu_seconds_hard']==120
        assert row['threads']==row['CPU_count']==1 and row['nproc_hard']==0 and row['address_space_hard']==row['aggregate_reader_memory_ceiling']==3*1024**3
        assert row['no_new_privileges']is True and row['effective_permitted_ambient_capabilities_zero']is True and row['parent_death_signal']==9
        assert row['uid']==os.getuid()>0 and row['affinity']==[control['cpu']] and 0<row['peak_rss_bytes']<=3*1024**3
    rows={};count=0
    def add(path,name,expected=None):
        nonlocal count
        assert re.fullmatch('[A-Za-z0-9_.-]{1,160}',name) and name not in rows and name!='DERIVED-UPLOAD-MANIFEST.json'
        assert len(rows)<4095
        raw=read(path);assert len(raw)<=16*1024**2
        if expected is not None:assert [sha(raw),len(raw)]==expected
        assert count+len(raw)<=CAP;count+=len(raw)
        rows[name]={'source_logical_path':str(path),'sha256':sha(raw),'bytes':len(raw)}
    add(D/'SELECTED-TEXT-INDEX.json','SELECTED-TEXT-INDEX.json')
    for row in index['selected_members'].values():
        assert type(row['pieces'])is list and 0<len(row['pieces'])<=2048
        for piece in row['pieces']:
            path=pathlib.Path(piece['path']);assert path.parent==D and re.fullmatch('TEXT-PIECE-[0-9]{4}.json',path.name)
            add(path,path.name,[piece['sha256'],piece['bytes']])
    assert len(rows)-1==index['derived_piece_count']<=2048
    for folder,name,public_name in [(E,'HOSTED-TRANSFER.json','HOSTED-TRANSFER.json'),(T,'result.json','TRANSFER-CONTROLLER.json'),(T,'stdout.log','TRANSFER-STDOUT.log'),(T,'stderr.log','TRANSFER-STDERR.log'),(C,'launcher-result.json','PURE-CONTROLLER.json'),(C,'stdout.log','PURE-STDOUT.log'),(C,'stderr.log','PURE-STDERR.log'),(D,'SELECTOR-ADMISSION.json','SELECTOR-ADMISSION.json'),(D,'C6-ADMISSION.json','C6-ADMISSION.json')]:add(folder/name,public_name)
    for name in ('RUN-TERMINAL.json','JOBS-TERMINAL.json','ARTIFACTS-METADATA.json'):add(E/name,'ORIGINAL-'+name)
    for name in ('trusted_artifact_transfer.py','select_chart_current_SOURCE_ONLY.py','linux_singleton_launcher.py','build_projection_admission.py','stage_projection_upload.py','PURE-SOURCE-APPROVAL.json','PINNED-SOURCES.sha256'):add(S/name,'SOURCE-'+name)
    for name in ('chart_port_ci.py','point4-local-chart-connection.yml'):add(S/'original'/name,'ORIGINAL-SOURCE-'+name)
    # Exact allowlist only: never the original ZIP, native objects, credentials, or redirect URLs.
    manifest={'schema':'new-hosted-derived-chart-text-upload-v1','projection_run_id':actual_run,'projection_head':actual_head,
        'producer_run_id':38838232477,'producer_head':index['head'],'producer_artifact_id':12021496276,
        'producer_artifact_sha256':index['archive_sha256'],'producer_archive_locally_rehashed_by_Codex':False,
        'producer_archive_hash_verified_in_hosted_transfer_and_pure_stream_PREPOST':True,'source_logical_paths_preserved_without_materializing_arbitrary_paths':True,
        'files':rows,'files_excluding_this_manifest':len(rows),'bytes_excluding_this_manifest':count,
        'aggregate_upload_byte_cap':CAP,'qualification_credit':0,'Point4':'OPEN'}
    encoded=(json.dumps(manifest,sort_keys=True,indent=2,allow_nan=False)+'\n').encode();assert len(encoded)<=8*1024**2 and count+len(encoded)<=CAP
    # Aggregate final serialized support+text size is checked BEFORE the first staging write.
    PUBLIC.mkdir(mode=0o700)
    for name,row in rows.items():
        raw=read(pathlib.Path(row['source_logical_path']));assert sha(raw)==row['sha256'] and len(raw)==row['bytes']
        with (PUBLIC/name).open('xb')as f:assert f.write(raw)==len(raw)
        assert read(PUBLIC/name)==raw
    with (PUBLIC/'DERIVED-UPLOAD-MANIFEST.json').open('xb')as f:assert f.write(encoded)==len(encoded)
    assert read(PUBLIC/'DERIVED-UPLOAD-MANIFEST.json')==encoded
    assert read(pathlib.Path(__file__),1024**2)==self_raw
    assert set(p.name for p in PUBLIC.iterdir())==set(rows)|{'DERIVED-UPLOAD-MANIFEST.json'}
    for name,row in rows.items():
        assert sha(read(pathlib.Path(row['source_logical_path'])))==row['sha256'] and sha(read(PUBLIC/name))==row['sha256']
    print(json.dumps({'derived_upload':'READY','files':len(rows)+1,'total_serialized_bytes':count+len(encoded),'manifest_sha256':sha(encoded),'original_ZIP_uploaded':False,'qualification_credit':0}))
if __name__=='__main__':main()
