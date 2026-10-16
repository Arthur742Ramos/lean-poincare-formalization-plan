"""SOURCE ONLY TEMPLATE. Bounded current chart text selection; no candidate imports or objects.
Concrete artifact/source/input pins and independent review are required before execution.
"""
import ast, binascii, hashlib, json, math, os, pathlib, re, stat, sys, zipfile
from linux_singleton_resources import resources
ROOT = pathlib.Path('/tmp/poincare-chart2813-projection')
D = ROOT/'pure'
SOURCE = ROOT/'source'
TRANSFER = ROOT/'transfer-controller'
E = ROOT/'input'
REPO = ROOT/'prepared-source'
HEAD = '2813ef52a21e13be08532f36ee9f26faf319da72'
TREE = '13f982c1be40478cc14b523ea76ed3642fb3ae7e'
RUN = 38838232477
JOB = 116772055358
WORKFLOW = '.github/workflows/point4-local-chart-connection.yml'
ARTIFACT = 12021496276
ZIP_NAME = 'ORIGINAL-CHART.zip'
ZIP_SHA = '743ea30a9daf0fdd8928871d2dfce22411b470f4270acddc817bc4c3c983f716'
ZIP_BYTES = 883922056
PINS = {'/tmp/poincare-chart2813-projection/input/RUN-TERMINAL.json': ['41398dcae962d72e67510a540a51b268d56a962dc74de9c8a7db5d490b9ab670', 17659], '/tmp/poincare-chart2813-projection/input/JOBS-TERMINAL.json': ['d5b1ce430026e5d073a16ce721480615c1e9099c352f2b738513725d0408809f', 4039], '/tmp/poincare-chart2813-projection/input/ARTIFACTS-METADATA.json': ['f29b39175f9f7fc5e3ec5440c34f334955b3cce140e9263c679ddb179c0ed3c5', 1042], '/tmp/poincare-chart2813-projection/prepared-source/curvature/scripts/chart_port_ci.py': ['95dcfdaf007d91c07a4e56cb20866c889228b6bcf0f923177b0b4eda38725c2b', 84973], '/tmp/poincare-chart2813-projection/prepared-source/.github/workflows/point4-local-chart-connection.yml': ['5f910f3373e2eb049a7ca3d2828148e0f8a3d32fdb5e88b9e14ab718de9998fd', 5000], '/tmp/poincare-chart2813-projection/input/ORIGINAL-CHART.zip': ['743ea30a9daf0fdd8928871d2dfce22411b470f4270acddc817bc4c3c983f716', 883922056], '/tmp/poincare-chart2813-projection/source/trusted_artifact_transfer.py': ['5db387e5a763a6828b7e5e501d98583410ad3f3c8e3f8d156a3aca348ad9d5b3', 13395]}
TRANSFER_SOURCE_SHA = '5db387e5a763a6828b7e5e501d98583410ad3f3c8e3f8d156a3aca348ad9d5b3'
ENCODED_OUTPUT = {'bytes':0,'files':0}
OUTPUT = D/'SELECTED-TEXT-INDEX.json'
STICKY = {}
def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def metadata(s):
    return [s.st_dev,s.st_ino,s.st_mode,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def regular(path, cap):
    require(path.is_absolute() and str(path) == os.path.abspath(path) and
        (path.is_relative_to(E) or path.is_relative_to(D) or path.is_relative_to(REPO) or path.is_relative_to(SOURCE) or path.is_relative_to(TRANSFER)), 'input root')
    for node in (path,*path.parents):
        s = node.lstat()
        require(not stat.S_ISLNK(s.st_mode), 'input symlink')
        require(stat.S_ISREG(s.st_mode) if node == path else stat.S_ISDIR(s.st_mode), 'input type')
    before = path.stat()
    require(0 <= before.st_size <= cap, 'input finite size')
    with path.open('rb') as stream:
        opened = os.fstat(stream.fileno())
        require(metadata(before) == metadata(opened), 'input open race')
        raw = stream.read(cap+1)
        require(metadata(opened) == metadata(os.fstat(stream.fileno())), 'input read race')
    require(metadata(before) == metadata(path.stat()) and len(raw) == before.st_size, 'input path race')
    key = str(path)
    if key in STICKY:
        require(STICKY[key] == metadata(before), 'input metadata drift')
    else:
        STICKY[key] = metadata(before)
    return raw

def strict_json(raw):
    def pairs(rows):
        result = {}
        for k,v in rows:
            require(k not in result, 'duplicate JSON key')
            result[k] = v
        return result
    def constant(value):
        raise ValueError('nonfinite JSON constant '+value)
    def number(value):
        result = float(value)
        require(math.isfinite(result), 'nonfinite JSON float')
        return result
    text = raw.decode('utf8',errors='strict')
    require(text.encode('utf8',errors='strict') == raw, 'stored UTF8 roundtrip')
    result = json.loads(text,object_pairs_hook=pairs,parse_constant=constant,parse_float=number)
    stack,count = [(result,0)],0
    while stack:
        value,depth = stack.pop()
        count += 1
        require(depth <= 64 and count <= 1000000, 'finite JSON shape')
        if isinstance(value,dict):
            require(all(type(k) is str and len(k) <= 4096 for k in value), 'finite JSON keys')
            stack.extend((v,depth+1) for v in value.values())
        elif isinstance(value,list):
            stack.extend((v,depth+1) for v in value)
        elif isinstance(value,str):
            require(len(value) <= 4*1024**2, 'finite JSON string')
            value.encode('utf8',errors='strict')
    return result

def canonical(name, directory):
    require(type(name) is str and 0 < len(name) <= 1024 and '\\' not in name and ':' not in name
        and all(ord(c) >= 32 and ord(c) != 127 for c in name), 'ZIP path controls')
    core = name[:-1] if directory else name
    require(bool(core) and not core.startswith('/') and all(x not in ('','.','..') for x in core.split('/'))
        and pathlib.PurePosixPath(core).as_posix() == core, 'ZIP path alias')
    return core

def resource_check(row):
    require(row['platform'] == 'linux' and row['binding'] == 'source-reviewed-kernel-singleton-v1'
        and row['threads'] == row['CPU_count'] == 1 and row['nproc_hard'] == 0
        and row['address_space_hard'] == row['aggregate_reader_memory_ceiling'] == 3*1024**3
        and row['parent_death_signal'] == 9 and row['no_new_privileges'] is True
        and row['effective_permitted_ambient_capabilities_zero'] is True
        and 0 < row['peak_rss_bytes'] <= 3*1024**3, 'singleton resource contract')

def zip_identity(path):
    require(path == E / ZIP_NAME and path.is_absolute(), 'fixed archive')
    for node in (path,*path.parents):
        info = node.lstat()
        require(not stat.S_ISLNK(info.st_mode), 'archive alias')
        require(stat.S_ISREG(info.st_mode) if node == path else stat.S_ISDIR(info.st_mode), 'archive type')
    before = path.stat()
    require(before.st_size == ZIP_BYTES and 0 < ZIP_BYTES <= 3*1024**3, 'finite canonical archive')
    h = hashlib.sha256()
    with path.open('rb') as stream:
        require(metadata(os.fstat(stream.fileno())) == metadata(before), 'archive open race')
        remaining = ZIP_BYTES
        while remaining:
            block = stream.read(min(1024**2,remaining))
            require(bool(block), 'archive early EOF')
            h.update(block); remaining -= len(block)
        require(stream.read(1) == b'' and metadata(os.fstat(stream.fileno())) == metadata(before), 'archive read race')
    require(metadata(path.stat()) == metadata(before) and h.hexdigest() == ZIP_SHA, 'archive path/hash drift')
    if str(path) in STICKY: require(STICKY[str(path)] == metadata(before), 'archive metadata drift')
    else: STICKY[str(path)] = metadata(before)
    return {'sha256':h.hexdigest(),'bytes':before.st_size,'metadata':metadata(before)}


def output(raw,path,cap):
    require(path.parent == D and len(raw) <= cap <= 8*1024**2 and not path.exists() and not path.is_symlink(), 'fresh fixed finite output')
    for node in (D,*D.parents):
        info=node.lstat();require(stat.S_ISDIR(info.st_mode) and not stat.S_ISLNK(info.st_mode), 'output parent alias')
    require(ENCODED_OUTPUT['bytes']+len(raw)<=256*1024**2 and ENCODED_OUTPUT['files']<2049,'aggregate encoded output cap BEFORE write')
    with path.open('xb') as stream: require(stream.write(raw) == len(raw), 'complete output write')
    ENCODED_OUTPUT['bytes']+=len(raw);ENCODED_OUTPUT['files']+=1
    require(regular(path,cap) == raw, 'output readback')
    return {'path':str(path),'sha256':sha(raw),'bytes':len(raw)}


def main():
    require(len(sys.argv)==4 and all(re.fullmatch('[0-9a-f]{64}',v) for v in sys.argv[2:]), 'exact manifest/source pins')
    require(PINS is not None and type(ARTIFACT) is int, 'unreleased template')
    self_path=pathlib.Path(__file__);require(self_path == D/'select_chart_current_SOURCE_ONLY.py','fixed source')
    manifest_path=pathlib.Path(sys.argv[1]);require(manifest_path==D/'SELECTOR-ADMISSION.json','fixed admission')
    source=regular(self_path,1024**2);manifest_raw=regular(manifest_path,1024**2)
    require(sha(source)==sys.argv[3] and sha(manifest_raw)==sys.argv[2],'source/admission hashes')
    manifest=strict_json(manifest_raw)
    require(manifest['schema']=='pr146-current-chart-text-selection-admission-v1'
        and manifest['execution_authorized'] is True and manifest['root_serial_release'] is True
        and manifest['independent_exact_source_review_approved'] is True
        and manifest['reader_sha256']==sys.argv[3] and manifest['pending_inputs']==[]
        and manifest['qualification_credit']==0,'unreleased selection')
    require(not OUTPUT.exists() and not any(D.glob('TEXT-PIECE-*.json')),'fresh derived output namespace')
    runtime=manifest['observed_runtime_transfer_input_seals']
    expected_runtime={str(E/'HOSTED-TRANSFER.json'),str(TRANSFER/'result.json'),str(TRANSFER/'stdout.log'),str(TRANSFER/'stderr.log')}
    require(type(runtime)is dict and set(runtime)==expected_runtime,'fixed trusted-producer runtime input names')
    for name,row in runtime.items():
        require(set(row)=={'sha256','bytes'} and re.fullmatch('[0-9a-f]{64}',row['sha256']) and type(row['bytes'])is int and 0<=row['bytes']<=8*1024**2,'finite observed runtime input seal')
        require(name not in PINS,'runtime seal cannot replace static authority');PINS[name]=(row['sha256'],row['bytes'])
    pre_resource=resources();resource_check(pre_resource)
    pre={};raws={}
    for name,(expected,size) in PINS.items():
        p=pathlib.Path(name)
        if p==E/ZIP_NAME:
            require(expected==ZIP_SHA and size==ZIP_BYTES,'archive source pin')
        else:
            raw=regular(p,16*1024**2);require(sha(raw)==expected and len(raw)==size,'sealed input mismatch '+name)
            pre[name]={'sha256':expected,'bytes':size,'metadata':STICKY[name]};raws[name]=raw
    run=strict_json(raws[str(E/'RUN-TERMINAL.json')]);jobs=strict_json(raws[str(E/'JOBS-TERMINAL.json')])
    artifacts=strict_json(raws[str(E/'ARTIFACTS-METADATA.json')]);capture=strict_json(raws[str(E/'HOSTED-TRANSFER.json')]);controller=strict_json(raws[str(TRANSFER/'result.json')])
    require(run['id']==RUN and run['head_sha']==HEAD and run['head_commit']['tree_id']==TREE
        and run['repository']['full_name']=='Arthur742Ramos/lean-poincare-formalization-plan'
        and run['path']==WORKFLOW and run['run_attempt']==1 and run['event']=='workflow_dispatch'
        and run['status']=='completed' and run['conclusion']=='success'
        and [(p['number'],p['head']['sha']) for p in run['pull_requests']]==[(146,HEAD)]
        and run['head_branch']=='point4/joint-metric-defect-and-ci-cache-20261015','exact successful current run')
    require(jobs['total_count']==len(jobs['jobs'])==1,'complete job set');job=jobs['jobs'][0]
    require(job['id']==JOB and job['run_id']==RUN and job['head_sha']==HEAD and job['run_attempt']==1
        and job['status']=='completed' and job['conclusion']=='success'
        and [s['name'] for s in job['steps']]==['Set up job','Checkout reviewed candidate','Admit exact candidate tree before running candidate code','Test chart driver resource and setup controls','Install the official pinned toolchain without build or caches','Rebuild source and probe under owned resource limits','Preserve small first compiler failure summary independently','Preserve exact candidate source and build receipts','Post Checkout reviewed candidate','Complete job']
        and all(s['status']=='completed' and s['conclusion']=='success' for s in job['steps']),'complete successful current job/steps')
    require(artifacts['total_count']==len(artifacts['artifacts'])==1,'complete canonical descriptor set');artifact=artifacts['artifacts'][0]
    require(artifact['id']==ARTIFACT and artifact['name']=='local-chart-connection-'+HEAD+'-1'
        and artifact['expired'] is False and artifact['size_in_bytes']==ZIP_BYTES and artifact['digest']=='sha256:'+ZIP_SHA
        and artifact['workflow_run']['id']==RUN and artifact['workflow_run']['head_sha']==HEAD
        and artifact['workflow_run']['repository_id']==artifact['workflow_run']['head_repository_id']==1217066549,'canonical artifact')
    binding={'repository':'Arthur742Ramos/lean-poincare-formalization-plan','head':HEAD,'tree':TREE,'run_id':RUN,'job_id':JOB,'attempt':1,'artifact_id':ARTIFACT}
    require(all(capture[k]==v for k,v in binding.items()) and capture['path']==str(E/ZIP_NAME)
        and capture['canonical_sha256']==ZIP_SHA and capture['bytes']==ZIP_BYTES
        and capture['descriptor_digest_matches'] is True and capture['authorized_hosted_read_only_transfer'] is True
        and capture['tool']=='github_actions_fixed_artifact_native_transfer','supported canonical provenance')
    require(capture['schema']=='hosted-finite-read-only-canonical-artifact-transfer-v1' and capture['artifact_descriptor']==artifact
        and capture['transfer_source_sha256']==TRANSFER_SOURCE_SHA and sha(raws[str(SOURCE/'trusted_artifact_transfer.py')])==TRANSFER_SOURCE_SHA
        and capture['API_credential_forwarded_to_storage'] is False and capture['signed_location_persisted'] is False
        and capture['network_denial_fallbacks']==0 and capture['metadata_HTTP_status']==capture['archive_HTTP_status']==200
        and capture['redirect_HTTP_status']==302 and capture['transfer_only_file_size_hard']==ZIP_BYTES
        and capture['transfer_only_CPU_seconds_hard']==120 and capture['transfer_only_wall_seconds']==180
        and capture['transfer_profile_is_pure_reader_profile'] is False and capture['aggregate_parent_or_multi_phase_resource_claim'] is False,'exact separately reviewed finite transfer role')
    require(type(capture['projection_run_id'])is int and capture['projection_run_id']>0
        and re.fullmatch('[0-9a-f]{40}',capture['projection_head']) and capture['projection_head']!=HEAD
        and capture['projection_run_id']==manifest['projection_run_id'] and capture['projection_head']==manifest['projection_head'],'finite distinct projection context')
    for r in (capture['resources_PRE'],capture['resources_POST']):
        require(r['platform']=='linux' and r['binding']=='source-reviewed-finite-artifact-transfer-child-v1'
            and r['threads']==r['CPU_count']==1 and r['nproc_hard']==0
            and r['address_space_hard']==r['aggregate_transfer_child_memory_ceiling']==3*1024**3
            and r['parent_death_signal']==9 and r['no_new_privileges'] is True
            and r['effective_permitted_ambient_capabilities_zero'] is True and 0<r['peak_rss_bytes']<=3*1024**3
            and type(r['pid'])is int and r['pid']>0 and type(r['owner_pid'])is int and r['owner_pid']>0 and r['pid']!=r['owner_pid']
            and type(r['uid'])is int and r['uid']==os.getuid()>0 and type(r['cpu_seconds_hard'])is int and r['cpu_seconds_hard']==120
            and type(controller['cpu'])is int and controller['cpu']>=0 and r['affinity']==[controller['cpu']]
            and r['general_windows_job_equivalence'] is False
            and r['pid']==capture['transfer_child_pid'] and r['owner_pid']==capture['transfer_owner_pid'],'transfer actual child resource contract')
    require({k:v for k,v in capture['resources_PRE'].items()if k!='peak_rss_bytes'}=={k:v for k,v in capture['resources_POST'].items()if k!='peak_rss_bytes'}
        and capture['resources_PRE']['peak_rss_bytes']<=capture['resources_POST']['peak_rss_bytes'],'transfer resource PREPOST')
    require(controller['schema']=='finite-artifact-transfer-controller-v1' and type(controller['exit'])is int and controller['exit']==0
        and controller['timeout'] is False and controller['reaped'] is True and 0<controller['elapsed_seconds']<=185
        and controller['child_pid']==capture['transfer_child_pid'] and controller['owner_pid']==capture['transfer_owner_pid']
        and controller['source_sha256']==TRANSFER_SOURCE_SHA and controller['projection_run']==capture['projection_run_id']
        and controller['projection_head']==capture['projection_head'],'transfer terminated and reaped before pure selector')
    require(sha(raws[str(TRANSFER/'stdout.log')])==controller['stdout_sha256']
        and raws[str(TRANSFER/'stderr.log')]==b'' and sha(b'')==controller['stderr_sha256'],'complete transfer terminal streams')
    transfer_terminal=strict_json(raws[str(TRANSFER/'stdout.log')])
    require(transfer_terminal=={'transfer':'PASS','canonical_sha256':ZIP_SHA,'bytes':ZIP_BYTES,'receipt_sha256':sha(raws[str(E/'HOSTED-TRANSFER.json')]),'qualification_credit':0},'transfer terminal receipt byte linkage')
    pre[str(E/ZIP_NAME)]=zip_identity(E/ZIP_NAME)
    namespace=[];text_entries=[];objects=0;declared_total=0;selected={};schema={};piece_count=0;aggregate=0
    with (E/ZIP_NAME).open('rb') as handle:
        require(metadata(os.fstat(handle.fileno()))==STICKY[str(E/ZIP_NAME)],'ZIP open identity')
        with zipfile.ZipFile(handle) as archive:
            entries=archive.infolist();require(0<len(entries)<=100000,'original chart namespace bound')
            names=set();folded=set();offsets=set();kinds={};spellings={}
            for entry in entries:
                require(entry.orig_filename==entry.filename,'ZIP original-name normalization')
                directory=entry.is_dir();core=canonical(entry.orig_filename,directory);mode=entry.external_attr>>16
                require(core not in names and core.casefold() not in folded,'ZIP duplicate/name alias');names.add(core);folded.add(core.casefold());kinds[core.casefold()]=directory
                parts=core.split('/')
                for i in range(1,len(parts)+1):
                    component='/'.join(parts[:i]);key=component.casefold()
                    require(key not in spellings or spellings[key]==component,'implicit directory spelling alias');spellings[key]=component
                require(not entry.flag_bits&1 and entry.compress_type in (zipfile.ZIP_STORED,zipfile.ZIP_DEFLATED)
                    and not mode&0o7000 and stat.S_IFMT(mode) in ((0,stat.S_IFDIR) if directory else (0,stat.S_IFREG))
                    and (directory or not entry.external_attr&0x10),'ZIP type/encryption/compression')
                require(0<=entry.file_size<=3*1024**3 and 0<=entry.compress_size<=ZIP_BYTES
                    and 0<=entry.CRC<=0xffffffff and 0<=entry.header_offset<ZIP_BYTES
                    and entry.header_offset not in offsets,'finite central metadata');offsets.add(entry.header_offset)
                require(not directory or entry.file_size==0,'directory payload');declared_total+=entry.file_size
                namespace.append({'name':entry.orig_filename,'directory':directory,'mode':mode,'bytes':entry.file_size,'compressed_bytes':entry.compress_size,'CRC':entry.CRC,'compression':entry.compress_type,'header_offset':entry.header_offset})
                suffix=pathlib.PurePosixPath(core).suffix
                if not directory and suffix in ('.json','.stdout','.stderr','.log','.txt'):
                    require(entry.file_size<=16*1024**2,'original per-text bound');aggregate+=entry.file_size
                    require(aggregate<=128*1024**2,'original aggregate text bound');text_entries.append(entry)
                elif not directory and suffix in ('.olean','.ilean','.ir','.c','.o','.so','.a','.trace','.hash'):
                    objects+=1
            require(0<len(text_entries)<=1000,'original selected-text count bound')
            for core in kinds:
                parts=core.split('/')
                for i in range(1,len(parts)):require('/'.join(parts[:i]) not in kinds or kinds['/'.join(parts[:i])] is True,'ZIP file/parent collision')
            expected={e.orig_filename for e in text_entries}
            required={'run.json','admission.json','configured-admission.json','final-physical-admission.json','cache-hash-plan.json','coherent-pinned-Mathlib-cache.json','cache-master.stdout','cache-extraction.json','package-root-relationships.json','full-type-proof-axiom-probe.stdout','probe-verdict.json'}
            require(required<=expected,'complete auxiliary text names')
            probes=sorted(n for n in expected if re.fullmatch(r'(full-type-proof-axiom-probe|ricci-extension-probe-[0-9]+)\.stdout',n));require(len(probes)==11,'complete eleven fresh raw probes')
            for entry in text_entries:
                with archive.open(entry) as stream:
                    raw=stream.read(16*1024**2+1);require(len(raw)==entry.file_size and stream.read(1)==b'','exact text size/EOF')
                require(binascii.crc32(raw)==entry.CRC,'text CRC');text=raw.decode('utf8',errors='strict');require(text.encode('utf8',errors='strict')==raw,'strict stored UTF8 roundtrip')
                if entry.orig_filename.endswith('.json'):
                    value=strict_json(raw);schema[entry.orig_filename]={'type':('dict' if type(value)is dict else 'list' if type(value)is list else 'str' if type(value)is str else 'bool' if type(value)is bool else 'int' if type(value)is int else 'float' if type(value)is float else 'NoneType'),'keys':sorted(value) if type(value) is dict else None}
                if entry.orig_filename=='run.json':
                    saved=strict_json(raw);require(saved['candidate_sha']==HEAD and saved['candidate_tree']==TREE
                        and saved['build']==saved['full_candidate_qualification']=='PASSED'
                        and saved['fresh_combined_modules']==83 and saved['fresh_combined_probes']==11
                        and saved['point4']==saved['general_targets']=='OPEN','successful current raw receipt')
                pieces=[];restored=hashlib.sha256();raw_length=0
                for offset in range(0,max(1,len(text)),262144):
                    part=text[offset:offset+262144];part_raw=part.encode('utf8',errors='strict');restored.update(part_raw);raw_length+=len(part_raw)
                    require(len(part_raw)<=1024**2 and piece_count<2048,'finite derived pieces')
                    payload={'member':entry.orig_filename,'piece_index':len(pieces),'text':part,'raw_UTF8_sha256':sha(part_raw),'raw_UTF8_bytes':len(part_raw)}
                    encoded=(json.dumps(payload,ensure_ascii=False,sort_keys=True,allow_nan=False)+'\n').encode('utf8')
                    record=output(encoded,D/('TEXT-PIECE-%04d.json'%piece_count),8*1024**2);record.update(piece_index=len(pieces),raw_UTF8_sha256=sha(part_raw),raw_UTF8_bytes=len(part_raw));pieces.append(record);piece_count+=1
                require(raw_length==len(raw) and restored.hexdigest()==sha(raw),'whole member preserved across derived segments')
                selected[entry.orig_filename]={'bytes':len(raw),'sha256':sha(raw),'CRC':entry.CRC,'compressed_bytes':entry.compress_size,'pieces':pieces}
        require(metadata(os.fstat(handle.fileno()))==STICKY[str(E/ZIP_NAME)],'ZIP descriptor POST')
    post={}
    for name,(expected,size) in PINS.items():
        p=pathlib.Path(name)
        if p==E/ZIP_NAME:post[name]=zip_identity(p)
        else:
            raw=regular(p,16*1024**2);post[name]={'sha256':sha(raw),'bytes':len(raw),'metadata':STICKY[name]}
    require(pre==post and regular(self_path,1024**2)==source and regular(manifest_path,1024**2)==manifest_raw,'all inputs/source PREPOST')
    for row in selected.values():
        for piece in row['pieces']:
            piece_raw=regular(pathlib.Path(piece['path']),8*1024**2)
            require(len(piece_raw)==piece['bytes'] and sha(piece_raw)==piece['sha256'],'derived output whole-set POST')
    post_resource=resources();resource_check(post_resource)
    require(pre_resource.keys()==post_resource.keys() and all(pre_resource[k]==post_resource[k] for k in pre_resource if k!='peak_rss_bytes')
        and pre_resource['peak_rss_bytes']<=post_resource['peak_rss_bytes'],'resource PREPOST')
    result=dict(binding,schema='pr146-current-chart-segmented-selected-text-v1',reader_sha256=sys.argv[3],manifest_sha256=sys.argv[2],artifact=artifact,archive_sha256=ZIP_SHA,
        complete_namespace_metadata=namespace,ZIP_members=len(namespace),skipped_object_members=objects,declared_total_uncompressed_bytes=declared_total,
        selected_members=selected,selected_member_count=len(selected),aggregate_raw_bytes=aggregate,derived_piece_count=piece_count,JSON_schema=schema,raw_probe_names=probes,
        object_payloads_read=0,filesystem_archive_path_extraction=False,derived_segmented_JSON_text_views_written=True,
        inputs_PRE=pre,inputs_POST=post,inputs_unchanged=True,resource_PRE=pre_resource,resource_POST=post_resource,
        projection_run_id=capture['projection_run_id'],projection_head=capture['projection_head'],
        original_archive_hash_verification='HOSTED_CANONICAL_BYTE_TRANSFER_AND_PURE_STREAM_PREPOST',
        original_archive_rehashed_by_local_Codex=False,hosted_original_archive_stream_hash_verified_PREPOST=True,
        qualification_credit=0,scope='New hosted derived text evidence; original artifact stays distinct; independent local semantic qualification pending',Point4='OPEN')
    encoded=(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2,allow_nan=False)+'\n').encode('utf8');out=output(encoded,OUTPUT,8*1024**2)
    print(json.dumps({'status':'BOUNDED_TEXT_SELECTION_PASS','output':out,'selected_members':len(selected),'raw_bytes':aggregate,'pieces':piece_count,'objects_read':0,'qualification_credit':0}))


if __name__=='__main__':main()
