"""Trusted source-pinned admission builder. No network or candidate execution."""
import hashlib,json,os,pathlib,re,stat
ROOT=pathlib.Path('/tmp/poincare-chart2813-projection')
S=ROOT/'source';D=ROOT/'pure';E=ROOT/'input';T=ROOT/'transfer-controller'
HEAD='2813ef52a21e13be08532f36ee9f26faf319da72'
SELECTOR_SHA='8bd7d6336c1e5205e9129ec7887ba23ea173c4e435a736b881f8e275655b1274'
TRANSFER_SHA='5db387e5a763a6828b7e5e501d98583410ad3f3c8e3f8d156a3aca348ad9d5b3'
LAUNCHER_SHA='c6c835c9b9e0b026c213f3fdf0e21a9565002dc78b5ca7bf17f45d4837769979'
ZIP_SHA='743ea30a9daf0fdd8928871d2dfce22411b470f4270acddc817bc4c3c983f716'
ZIP_BYTES=883922056
REPOSITORY='Arthur742Ramos/lean-poincare-formalization-plan'
STICKY={}
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

def write(path,value):
    assert path.parent==D and not path.exists() and not path.is_symlink()
    raw=(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n').encode();assert len(raw)<=1024**2
    with path.open('xb')as f:assert f.write(raw)==len(raw)
    assert read(path,1024**2)==raw
    return sha(raw)

def main():
    assert pathlib.Path(__file__)==S/'build_projection_admission.py'
    source=read(pathlib.Path(__file__),1024**2)
    assert os.environ['GITHUB_REPOSITORY']==REPOSITORY and os.environ['GITHUB_EVENT_NAME']=='workflow_dispatch'
    run=int(os.environ['GITHUB_RUN_ID']);head=os.environ['GITHUB_SHA'];attempt=os.environ['GITHUB_RUN_ATTEMPT']
    ref=os.environ['GITHUB_REF'];assert run>0 and attempt=='1' and re.fullmatch('[0-9a-f]{40}',head) and head!=HEAD
    assert ref=='refs/heads/point4/chart2813-derived-text-evidence-20261016'
    assert not D.exists() and not D.is_symlink();D.mkdir(mode=0o700)
    actor=read(S/'select_chart_current_SOURCE_ONLY.py',1024**2);assert sha(actor)==SELECTOR_SHA
    transfer=read(S/'trusted_artifact_transfer.py',1024**2);assert sha(transfer)==TRANSFER_SHA
    launcher=read(S/'linux_singleton_launcher.py',1024**2);assert sha(launcher)==LAUNCHER_SHA
    review_raw=read(S/'PURE-SOURCE-APPROVAL.json',1024**2);review=load(review_raw)
    assert review['reader_sha256']==SELECTOR_SHA and review['independent_exact_source_approved']is True
    assert review['singleton_no_dynamic_execution_or_resource_widening_reviewed']is True
    assert review['input_source_prepost_and_finite_payload_limits_reviewed']is True
    assert review['qualification_credit']==0 and type(review['conditional_final_release_requirements'])is list and len(review['conditional_final_release_requirements'])>0
    # These are OBSERVED provenance seals after the distinct transfer role exits.
    names=[E/'HOSTED-TRANSFER.json',T/'result.json',T/'stdout.log',T/'stderr.log'];raws={p:read(p,8*1024**2)for p in names}
    capture=load(raws[E/'HOSTED-TRANSFER.json']);controller=load(raws[T/'result.json']);terminal=load(raws[T/'stdout.log'])
    assert controller['exit']==0 and type(controller['exit'])is int and controller['timeout']is False and controller['reaped']is True
    assert controller['source_sha256']==TRANSFER_SHA and controller['projection_run']==run and controller['projection_head']==head
    assert capture['projection_run_id']==run and capture['projection_head']==head and capture['transfer_source_sha256']==TRANSFER_SHA
    assert capture['canonical_sha256']==ZIP_SHA and capture['bytes']==ZIP_BYTES
    assert controller['child_pid']==capture['transfer_child_pid'] and controller['owner_pid']==capture['transfer_owner_pid']
    assert terminal=={'transfer':'PASS','canonical_sha256':ZIP_SHA,'bytes':ZIP_BYTES,'receipt_sha256':sha(raws[E/'HOSTED-TRANSFER.json']),'qualification_credit':0}
    assert sha(raws[T/'stdout.log'])==controller['stdout_sha256'] and raws[T/'stderr.log']==b'' and sha(b'')==controller['stderr_sha256']
    assert 0<controller['elapsed_seconds']<=185
    runtime={str(p):{'sha256':sha(raw),'bytes':len(raw)}for p,raw in raws.items()}
    admission={'schema':'pr146-current-chart-text-selection-admission-v1','execution_authorized':True,'root_serial_release':True,
        'independent_exact_source_review_approved':True,'reader_sha256':SELECTOR_SHA,'pending_inputs':[],'qualification_credit':0,
        'observed_runtime_transfer_input_seals':runtime,'projection_run_id':run,'projection_head':head,'repository':REPOSITORY,
        'projection_ref':ref,'projection_event':'workflow_dispatch','projection_attempt':1,'pure_source_review_sha256':sha(review_raw),
        'runtime_seals_are_observed_provenance_not_replacement_static_authority':True,'Point4':'OPEN'}
    # Preserve actor source bytes exactly; this is the original c6 reader path.
    with (D/'select_chart_current_SOURCE_ONLY.py').open('xb')as f:assert f.write(actor)==len(actor)
    assert read(D/'select_chart_current_SOURCE_ONLY.py',1024**2)==actor
    admission_sha=write(D/'SELECTOR-ADMISSION.json',admission)
    c6={'independent_exact_source_approved':True,'launcher_sha256':LAUNCHER_SHA,
        'reader_absolute_path':str(D/'select_chart_current_SOURCE_ONLY.py'),'reader_sha256':SELECTOR_SHA,
        'reader_arguments':[str(D/'SELECTOR-ADMISSION.json'),admission_sha,SELECTOR_SHA],
        'source_admission':review['source_admission'],'singleton_no_dynamic_execution_or_resource_widening_reviewed':True,
        'input_source_prepost_and_finite_payload_limits_reviewed':True,'qualification_credit':0}
    c6_sha=write(D/'C6-ADMISSION.json',c6)
    assert read(pathlib.Path(__file__),1024**2)==source
    for p,raw in raws.items():assert read(p,8*1024**2)==raw
    assert read(S/'select_chart_current_SOURCE_ONLY.py',1024**2)==actor and read(S/'trusted_artifact_transfer.py',1024**2)==transfer
    assert read(S/'linux_singleton_launcher.py',1024**2)==launcher and read(S/'PURE-SOURCE-APPROVAL.json',1024**2)==review_raw
    print(json.dumps({'admission':'READY','c6_admission_sha256':c6_sha,'reader_sha256':SELECTOR_SHA,'projection_run_id':run,'projection_head':head,'qualification_credit':0}))
if __name__=='__main__':main()
