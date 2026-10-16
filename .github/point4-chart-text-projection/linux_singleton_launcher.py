"""Narrow, opt-in Linux launcher for independently reviewed saved-text readers.

Not a general sandbox. No evidence reader is authorized by this file's existence.
An exact source/admission SHA and human/parent source review are required. The
module name linux_singleton_resources is injected before executing that source.
No system setting is modified. Every limit applies only to the owned child.
"""
import argparse
import ast
import ctypes
import hashlib
import importlib
import json
import os
from pathlib import Path
import resource
import signal
import stat
import subprocess
import sys
import time
import types

MEMORY = 3 * 1024**3
ALLOWED_IMPORTS = frozenset(('ast','base64','binascii','datetime','hashlib',
    'json','math','os','pathlib','re','stat','sys','zipfile',
    'linux_singleton_resources'))
FORBIDDEN_ATTRIBUTES = frozenset(('fork','forkpty','posix_spawn','posix_spawnp',
    'system','popen','execv','execve','execl','execle','execlp','execlpe',
    'execvp','execvpe','spawnl','spawnle','spawnlp','spawnlpe','spawnv',
    'spawnve','spawnvp','spawnvpe','startfile','sched_setaffinity','setrlimit',
    'prlimit','setuid','seteuid','setresuid','setreuid','setgid','setegid',
    'setresgid','setregid','setgroups','kill','killpg','setsid','setpgid',
    'settrace','setprofile','_getframe','__subclasses__','__globals__',
    '__code__','__class__','__dict__','__bases__','__builtins__',
    'modules','meta_path','path_hooks','path_importer_cache'))
FORBIDDEN_NAMES = frozenset(('exec','eval','compile','__import__','globals',
    'locals','vars','setattr','delattr','breakpoint','input'))

def digest(raw): return hashlib.sha256(raw).hexdigest()

def regular(path):
    assert path.is_absolute()
    for node in (path,*path.parents):
        mode=node.lstat().st_mode
        assert not stat.S_ISLNK(mode), str(node)
        assert stat.S_ISREG(mode) if node==path else stat.S_ISDIR(mode)

def source_admission(raw):
    """Conservative syntax screen; exact source review remains mandatory."""
    tree=ast.parse(raw)
    imports=[]; calls=[]
    for node in ast.walk(tree):
        if isinstance(node,(ast.Import,ast.ImportFrom)):
            names=([part.name for part in node.names] if isinstance(node,ast.Import)
                   else [node.module])
            assert not isinstance(node,ast.ImportFrom) or node.level==0
            assert all(name in ALLOWED_IMPORTS for name in names), names
            imports.extend(names)
        if isinstance(node,ast.Attribute):
            assert node.attr not in FORBIDDEN_ATTRIBUTES, (node.lineno,node.attr)
            assert not node.attr.startswith('__'), (node.lineno,node.attr)
        if isinstance(node,ast.Name):
            assert node.id not in FORBIDDEN_NAMES, (node.lineno,node.id)
        if isinstance(node,ast.Call):
            # Dynamic call targets and decorators need a separate implementation.
            assert isinstance(node.func,(ast.Name,ast.Attribute)), node.lineno
            if isinstance(node.func,ast.Name) and node.func.id=='getattr':
                assert len(node.args)==3 and not node.keywords
                assert isinstance(node.args[1],ast.Constant) and node.args[1].value=='st_file_attributes'
                assert isinstance(node.args[2],ast.Constant) and node.args[2].value==0
            calls.append([node.lineno,ast.unparse(node.func)])
        if isinstance(node,(ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef)):
            assert not node.decorator_list
        assert not isinstance(node,(ast.AsyncFunctionDef,ast.Await,ast.Yield,
                                    ast.YieldFrom,ast.Global,ast.Nonlocal))
    return dict(imports=sorted(set(imports)),call_sites=calls,
                generic_sandbox_claim=False,
                independent_exact_source_review_required=True)

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
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*1024**2,16*1024**2))
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
        return dict(platform='linux',binding='source-reviewed-kernel-singleton-v1',
                    pid=os.getpid(),owner_pid=expected_owner,uid=os.getuid(),
                    nproc_hard=0,threads=1,address_space_hard=MEMORY,
                    aggregate_reader_memory_ceiling=MEMORY,
                    memory_basis='one kernel-enforced task; virtual AS bounds resident/committed memory',
                    CPU_count=1,affinity=[cpu],cpu_seconds_hard=cpu_seconds,
                    parent_death_signal=signal.SIGKILL,no_new_privileges=True,
                    effective_permitted_ambient_capabilities_zero=True,
                    peak_rss_bytes=peak,general_windows_job_equivalence=False)
    resources()
    return resources

def child(admission_path,admission_sha,expected_owner,cpu,cpu_seconds):
    # Setup runs before transferred source is opened, parsed, imported, or released.
    resources=configure(expected_owner,cpu,cpu_seconds)
    regular(admission_path)
    admission_raw=admission_path.read_bytes()
    assert digest(admission_raw)==admission_sha
    admission=json.loads(admission_raw)
    assert admission['independent_exact_source_approved'] is True
    assert admission['launcher_sha256']==digest(Path(__file__).read_bytes())
    reader=Path(admission['reader_absolute_path']);regular(reader)
    raw=reader.read_bytes();assert digest(raw)==admission['reader_sha256']
    screened=source_admission(raw)
    assert screened==admission['source_admission']
    assert admission['singleton_no_dynamic_execution_or_resource_widening_reviewed'] is True
    assert admission['input_source_prepost_and_finite_payload_limits_reviewed'] is True
    for name in screened['imports']:
        if name!='linux_singleton_resources':importlib.import_module(name)
    # zipfile may lazily request an encoding module when reading member names.
    importlib.import_module('encodings.cp437')
    module=types.ModuleType('linux_singleton_resources')
    module.resources=resources
    sys.modules[module.__name__]=module
    sys.argv=[str(reader),*admission['reader_arguments']]
    before=resources()
    code=compile(raw,str(reader),'exec')
    namespace=dict(__name__='__main__',__file__=str(reader),__package__=None)
    exec(code,namespace)
    after=resources()
    assert digest(reader.read_bytes())==admission['reader_sha256']
    assert digest(admission_path.read_bytes())==admission_sha
    # No launcher receipt pretends to be mathematical qualification.
    print(json.dumps(dict(launcher_resource_PRE=before,launcher_resource_POST=after,
                          exact_source_unchanged=True,qualification_credit=0)))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--admission',type=Path,required=True)
    parser.add_argument('--admission-sha',required=True)
    parser.add_argument('--output-directory',type=Path,required=True)
    parser.add_argument('--wall-seconds',type=int,default=120)
    parser.add_argument('--cpu-seconds',type=int,default=120)
    parser.add_argument('--child-owner',type=int)
    parser.add_argument('--cpu',type=int)
    args=parser.parse_args()
    assert 1<=args.wall_seconds<=600 and 1<=args.cpu_seconds<=600
    assert len(args.admission_sha)==64 and all(c in '0123456789abcdef' for c in args.admission_sha)
    if args.child_owner is not None:
        child(args.admission,args.admission_sha,args.child_owner,args.cpu,args.cpu_seconds)
        return
    assert args.output_directory.is_absolute()
    args.output_directory.mkdir(exist_ok=False)
    stdout_path=args.output_directory/'stdout.log';stderr_path=args.output_directory/'stderr.log'
    cpu=min(os.sched_getaffinity(0)); started=time.monotonic()
    with stdout_path.open('xb') as stdout,stderr_path.open('xb') as stderr:
        proc=subprocess.Popen([sys.executable,'-I','-B',str(Path(__file__).resolve()),
            '--admission',str(args.admission),'--admission-sha',args.admission_sha,
            '--output-directory',str(args.output_directory),
            '--cpu-seconds',str(args.cpu_seconds),'--wall-seconds',str(args.wall_seconds),
            '--child-owner',str(os.getpid()),'--cpu',str(cpu)],
            stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
        def cleanup(signum,frame):
            if proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL)
            proc.wait(timeout=5)
            raise SystemExit(128+signum)
        signal.signal(signal.SIGTERM,cleanup);signal.signal(signal.SIGINT,cleanup)
        expired=False
        try:proc.wait(timeout=args.wall_seconds)
        except subprocess.TimeoutExpired:
            expired=True;os.killpg(proc.pid,signal.SIGKILL);proc.wait(timeout=5)
    report=dict(exit=proc.returncode,timeout=expired,reaped=True,
                elapsed_seconds=time.monotonic()-started,cpu=cpu,
                stdout_sha256=digest(stdout_path.read_bytes()),
                stderr_sha256=digest(stderr_path.read_bytes()),qualification_credit=0)
    (args.output_directory/'launcher-result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
    if proc.returncode:raise SystemExit(1)

if __name__=='__main__':main()
