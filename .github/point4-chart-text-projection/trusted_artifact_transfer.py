"""Trusted finite read-only artifact transfer, separate from the pure c6 reader.
No candidate source is imported or executed. Tokens and redirect URLs are never
written or printed. Only the fixed canonical artifact can be transferred.
"""
import argparse,ctypes,hashlib,json,math,os,pathlib,re,resource,signal,stat,subprocess,sys,time,urllib.request,urllib.error,urllib.parse
from pathlib import Path
ROOT=Path('/tmp/poincare-chart2813-projection')
MEMORY=3*1024**3
ZIP_BYTES=883922056
ZIP_SHA='743ea30a9daf0fdd8928871d2dfce22411b470f4270acddc817bc4c3c983f716'
ARTIFACT=12021496276
RUN=38838232477
JOB=116772055358
HEAD='2813ef52a21e13be08532f36ee9f26faf319da72'
TREE='13f982c1be40478cc14b523ea76ed3642fb3ae7e'
REPOSITORY='Arthur742Ramos/lean-poincare-formalization-plan'
API='https://api.github.com/repos/'+REPOSITORY+'/actions/artifacts/'+str(ARTIFACT)
ZIP=ROOT/'input/ORIGINAL-CHART.zip'
RECEIPT=ROOT/'input/HOSTED-TRANSFER.json'

def digest(raw): return hashlib.sha256(raw).hexdigest()

def regular(path):
    assert path.is_absolute()
    for node in (path,*path.parents):
        mode=node.lstat().st_mode
        assert not stat.S_ISLNK(mode), str(node)
        assert stat.S_ISREG(mode) if node==path else stat.S_ISDIR(mode)

def configure(expected_owner,cpu,cpu_seconds):
    libc=ctypes.CDLL(None,use_errno=True)
    libc.prctl.argtypes=[ctypes.c_int,ctypes.c_ulong,ctypes.c_ulong,
                        ctypes.c_ulong,ctypes.c_ulong]
    libc.prctl.restype=ctypes.c_int
    assert libc.prctl(1,signal.SIGKILL,0,0,0)==0 # PR_SET_PDEATHSIG
    assert os.getppid()==expected_owner, 'owner died before resource binding'
    resource.setrlimit(resource.RLIMIT_NPROC,(0,0))
    resource.setrlimit(resource.RLIMIT_AS,(MEMORY,MEMORY))
    resource.setrlimit(resource.RLIMIT_CPU,(cpu_seconds,cpu_seconds))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    resource.setrlimit(resource.RLIMIT_FSIZE,(ZIP_BYTES,ZIP_BYTES))
    os.sched_setaffinity(0,{cpu})
    def resources():
        status=dict(line.split(':',1) for line in
                    Path('/proc/self/status').read_text().splitlines() if ':' in line)
        assert os.getuid()!=0 and os.geteuid()==os.getuid()
        assert all(int(status[name].strip(),16)==0 for name in
                   ('CapEff','CapPrm','CapAmb'))
        assert status['NoNewPrivs'].strip()=='1'
        assert int(status['Threads'].strip())==1
        assert resource.getrlimit(resource.RLIMIT_NPROC)==(0,0)
        assert resource.getrlimit(resource.RLIMIT_AS)==(MEMORY,MEMORY)
        assert resource.getrlimit(resource.RLIMIT_CPU)==(cpu_seconds,cpu_seconds)
        assert os.sched_getaffinity(0)=={cpu}
        assert os.getppid()==expected_owner
        parent_death=ctypes.c_int()
        # GET_PDEATHSIG has a pointer argument, so bypass the integer-only prototype.
        query=ctypes.CFUNCTYPE(ctypes.c_int,ctypes.c_int,ctypes.c_void_p,
              ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong)(('prctl',libc))
        assert query(2,ctypes.byref(parent_death),0,0,0)==0
        assert parent_death.value==signal.SIGKILL
        peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
        assert 0<peak<=MEMORY
        return dict(platform='linux',binding='source-reviewed-finite-artifact-transfer-child-v1',
                    pid=os.getpid(),owner_pid=expected_owner,uid=os.getuid(),
                    nproc_hard=0,threads=1,address_space_hard=MEMORY,
                    aggregate_transfer_child_memory_ceiling=MEMORY,
                    memory_basis='one kernel-enforced task; virtual AS bounds resident/committed memory',
                    CPU_count=1,affinity=[cpu],cpu_seconds_hard=cpu_seconds,
                    parent_death_signal=signal.SIGKILL,no_new_privileges=True,
                    effective_permitted_ambient_capabilities_zero=True,
                    peak_rss_bytes=peak,general_windows_job_equivalence=False)
    resources()
    return resources

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,request,fp,code,message,headers,newurl):return None


def strict_json(raw):
    def pairs(rows):
        result={}
        for k,v in rows:
            assert k not in result,'duplicate metadata key';result[k]=v
        return result
    def reject(value):raise ValueError('nonfinite JSON')
    return json.loads(raw.decode('utf8',errors='strict'),object_pairs_hook=pairs,parse_constant=reject)


def identity(info):return [info.st_dev,info.st_ino,info.st_mode,info.st_uid,info.st_gid,info.st_size,info.st_mtime_ns,info.st_ctime_ns]


STICKY = {}


def fixed_file(path,cap):
    regular(path);before=path.stat();assert 0<=before.st_size<=cap
    with path.open('rb')as stream:
        opened=os.fstat(stream.fileno());assert identity(before)==identity(opened)
        raw=stream.read(cap+1);assert identity(os.fstat(stream.fileno()))==identity(opened)
    assert identity(path.stat())==identity(before) and len(raw)==before.st_size
    key=str(path)
    if key in STICKY:assert STICKY[key]==identity(before)
    else:STICKY[key]=identity(before)
    return raw


def transfer(args):
    resource_snapshot=configure(args.child_owner,args.cpu,120)
    assert resource.getrlimit(resource.RLIMIT_FSIZE)==(ZIP_BYTES,ZIP_BYTES)
    source=Path(__file__);source_raw=fixed_file(source,1024**2);assert digest(source_raw)==args.source_sha
    assert ROOT.is_dir() and not ROOT.is_symlink() and (ROOT/'input').is_dir() and not (ROOT/'input').is_symlink()
    assert not ZIP.exists() and not ZIP.is_symlink() and not RECEIPT.exists() and not RECEIPT.is_symlink()
    token=os.environ.pop('PROJECTION_API_TOKEN');assert token and '\n' not in token and '\r' not in token
    before=resource_snapshot();start=time.monotonic();opener=urllib.request.build_opener(NoRedirect())
    api_headers={'Accept':'application/vnd.github+json','Authorization':'Bearer '+token,
        'X-GitHub-Api-Version':'2022-11-28','User-Agent':'poincare-immutable-text-projection'}
    with opener.open(urllib.request.Request(API,headers=api_headers),timeout=15)as response:
        assert response.status==200;metadata_raw=response.read(1024**2+1);assert len(metadata_raw)<=1024**2 and response.read(1)==b''
    descriptor=strict_json(metadata_raw)
    assert descriptor['id']==ARTIFACT and descriptor['size_in_bytes']==ZIP_BYTES and descriptor['digest']=='sha256:'+ZIP_SHA
    assert descriptor['name']=='local-chart-connection-'+HEAD+'-1' and descriptor['expired'] is False
    producer=descriptor['workflow_run'];assert producer['id']==RUN and producer['head_sha']==HEAD
    assert producer['repository_id']==producer['head_repository_id']==1217066549
    try:
        response=opener.open(urllib.request.Request(API+'/zip',headers=api_headers),timeout=15)
    except urllib.error.HTTPError as error:
        if error.code!=302:raise
        location=error.headers['Location'];error.close()
    else:
        response.close();raise ValueError('artifact API lacked its normal redirect')
    del token,api_headers
    assert type(location)is str and 0<len(location)<=16384
    target=urllib.parse.urlsplit(location)
    assert target.scheme=='https' and target.hostname and target.hostname.endswith('.blob.core.windows.net')
    assert target.username is None and target.password is None and target.port in (None,443) and not target.fragment
    # A new request deliberately carries NO API Authorization/cookie headers.
    request=urllib.request.Request(location,headers={'User-Agent':'poincare-immutable-text-projection'})
    assert not request.has_header('Authorization')
    h=hashlib.sha256();count=0
    with opener.open(request,timeout=15)as response:
        assert response.status==200
        length=response.headers.get('Content-Length');assert length is None or int(length)==ZIP_BYTES
        with ZIP.open('xb')as stream:
            while count<ZIP_BYTES:
                assert time.monotonic()-start<=180
                block=response.read(min(1024**2,ZIP_BYTES-count));assert block
                assert stream.write(block)==len(block);count+=len(block);h.update(block)
            assert response.read(1)==b'' and count==ZIP_BYTES and h.hexdigest()==ZIP_SHA
            stream.flush();os.fsync(stream.fileno());final_stat=os.fstat(stream.fileno())
    del location,target,request,opener
    regular(ZIP);assert identity(ZIP.stat())==identity(final_stat) and ZIP.stat().st_size==ZIP_BYTES
    after=resource_snapshot();assert resource.getrlimit(resource.RLIMIT_FSIZE)==(ZIP_BYTES,ZIP_BYTES)
    assert {k:v for k,v in before.items()if k!='peak_rss_bytes'}=={k:v for k,v in after.items()if k!='peak_rss_bytes'}
    assert before['peak_rss_bytes']<=after['peak_rss_bytes']<=MEMORY
    assert fixed_file(source,1024**2)==source_raw
    receipt={'schema':'hosted-finite-read-only-canonical-artifact-transfer-v1','repository':REPOSITORY,'head':HEAD,'tree':TREE,
        'run_id':RUN,'job_id':JOB,'attempt':1,'artifact_id':ARTIFACT,'artifact_descriptor':descriptor,'path':str(ZIP),
        'canonical_sha256':h.hexdigest(),'bytes':count,'descriptor_digest_matches':True,'authorized_hosted_read_only_transfer':True,
        'tool':'github_actions_fixed_artifact_native_transfer','metadata_HTTP_status':200,'redirect_HTTP_status':302,'archive_HTTP_status':200,
        'API_credential_forwarded_to_storage':False,'signed_location_persisted':False,'network_denial_fallbacks':0,
        'transfer_source_sha256':args.source_sha,'projection_run_id':args.projection_run,'projection_head':args.projection_head,
        'transfer_child_pid':os.getpid(),'transfer_owner_pid':args.child_owner,'resources_PRE':before,'resources_POST':after,
        'transfer_only_file_size_hard':ZIP_BYTES,'transfer_only_CPU_seconds_hard':120,'transfer_only_wall_seconds':180,
        'transfer_profile_is_pure_reader_profile':False,'aggregate_parent_or_multi_phase_resource_claim':False,
        'qualification_credit':0,'Point4':'OPEN'}
    raw=(json.dumps(receipt,sort_keys=True,indent=2,allow_nan=False)+'\n').encode();assert len(raw)<=8*1024**2
    with RECEIPT.open('xb')as stream:assert stream.write(raw)==len(raw)
    assert fixed_file(RECEIPT,8*1024**2)==raw
    print(json.dumps({'transfer':'PASS','canonical_sha256':h.hexdigest(),'bytes':count,'receipt_sha256':digest(raw),'qualification_credit':0}),flush=True)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--source-sha',required=True);parser.add_argument('--projection-run',type=int,required=True)
    parser.add_argument('--projection-head',required=True);parser.add_argument('--child-owner',type=int);parser.add_argument('--cpu',type=int);args=parser.parse_args()
    assert re.fullmatch('[0-9a-f]{64}',args.source_sha) and re.fullmatch('[0-9a-f]{40}',args.projection_head) and args.projection_run>0
    source=Path(__file__);assert source==ROOT/'source/trusted_artifact_transfer.py' and digest(fixed_file(source,1024**2))==args.source_sha
    if args.child_owner is not None:
        assert args.child_owner>0 and args.cpu is not None
        try:transfer(args)
        except BaseException as error:
            # Neither str(error), token, nor request/redirect URLs are emitted.
            print(json.dumps({'transfer':'FAILED','exception_type':type(error).__name__,
                'HTTP_status':error.code if isinstance(error,urllib.error.HTTPError)else None,'qualification_credit':0}),flush=True)
            return 1
        return 0
    token=os.environ.pop('PROJECTION_API_TOKEN');assert token
    directory=ROOT/'transfer-controller';directory.mkdir(exist_ok=False);cpu=min(os.sched_getaffinity(0));started=time.monotonic()
    env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','PROJECTION_API_TOKEN':token}
    with (directory/'stdout.log').open('xb')as stdout,(directory/'stderr.log').open('xb')as stderr:
        proc=subprocess.Popen([sys.executable,'-I','-B',str(source),'--source-sha',args.source_sha,
            '--projection-run',str(args.projection_run),'--projection-head',args.projection_head,
            '--child-owner',str(os.getpid()),'--cpu',str(cpu)],env=env,stdin=subprocess.DEVNULL,
            stdout=stdout,stderr=stderr,start_new_session=True)
        del token,env
        def cleanup(signum,frame):
            if proc.poll()is None:os.killpg(proc.pid,signal.SIGKILL)
            proc.wait(timeout=5);raise SystemExit(128+signum)
        signal.signal(signal.SIGTERM,cleanup);signal.signal(signal.SIGINT,cleanup);expired=False
        try:proc.wait(timeout=180)
        except subprocess.TimeoutExpired:
            expired=True;os.killpg(proc.pid,signal.SIGKILL);proc.wait(timeout=5)
    assert digest(fixed_file(source,1024**2))==args.source_sha
    result={'schema':'finite-artifact-transfer-controller-v1','exit':proc.returncode,'timeout':expired,'reaped':True,
        'elapsed_seconds':time.monotonic()-started,'child_pid':proc.pid,'owner_pid':os.getpid(),'cpu':cpu,
        'stdout_sha256':digest(fixed_file(directory/'stdout.log',16*1024**2)),
        'stderr_sha256':digest(fixed_file(directory/'stderr.log',16*1024**2)),
        'source_sha256':args.source_sha,'projection_run':args.projection_run,'projection_head':args.projection_head,'qualification_credit':0}
    (directory/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True);return 0 if proc.returncode==0 and not expired else 1


if __name__=='__main__':raise SystemExit(main())
