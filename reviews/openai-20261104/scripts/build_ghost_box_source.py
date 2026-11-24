#!/usr/bin/env python3
"""Fresh build of the ghost-box source-identification lemmas, not the final value.

Reuses the pinned submission's compiled libraries. Checks every received
source hash before building the one review module and auditing its axioms.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--work', required=True, type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, work = args.source.resolve(), args.work.resolve()
    if work.exists(): raise SystemExit('Choose a fresh work directory.')
    pin = json.loads((repo/'provenance/submission.json').read_text())
    manifest = source.parent/'SOURCES.sha256'
    assert sha(manifest) == pin['manifest_sha256']
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split(maxsplit=1)
        p = (source.parent/name.removeprefix('*')).resolve(strict=True)
        assert p.is_relative_to(source.parent) and sha(p) == expected, name
        count += 1
    assert count == pin['files_in_manifest']
    project = work/'project'
    project.mkdir(parents=True)
    module = 'GhostBoxSource'
    original = repo/'checks/matching'/f'{module}.lean'
    shutil.copy2(original,project/original.name)
    shutil.copy2(source/'lean-toolchain',project/'lean-toolchain')
    (project/'lakefile.toml').write_text(
        'name = "ghost_box_review"\nversion = "0.1.0"\npackagesDir = '+
        json.dumps(str(source/'.lake/packages'))+
        '\n[[lean_lib]]\nname = "GhostBoxReview"\nroots = ["GhostBoxSource"]'+
        '\n[[require]]\nname = "yang_mills"\npath = '+json.dumps(str(source))+'\n')
    lake_manifest = json.loads((source/'lake-manifest.json').read_text())
    lake_manifest['name']='ghost_box_review'
    lake_manifest['packagesDir']=str(source/'.lake/packages')
    for p in lake_manifest['packages']: p['inherited']=True
    lake_manifest['packages'].append({'type':'path','name':'yang_mills','scope':'',
        'dir':str(source),'inherited':False,'configFile':'lakefile.toml','manifestFile':'lake-manifest.json'})
    (project/'lake-manifest.json').write_text(json.dumps(lake_manifest,indent=2)+'\n')
    output=project/'.lake/build/lib/lean'
    output.mkdir(parents=True)
    log=work/'GhostBoxSource.log'
    lake=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
    command=[lake,'env','lean','-o',str(output/(module+'.olean')),str(project/original.name)]
    started=datetime.now(timezone.utc).isoformat()
    with log.open('w') as stream:
        result=subprocess.run(command,cwd=project,stdout=stream,stderr=subprocess.STDOUT)
    text=log.read_text()
    axioms={name:re.findall(r'[\w.]+',v) for name,v in
        re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
    assert result.returncode == 0, text
    assert len(axioms)==6 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
    assert sha(original)==sha(project/original.name)
    record={'status':'passed','started_utc':started,'finished_utc':datetime.now(timezone.utc).isoformat(),
        'scope':'Actual source histories, order-four membership, rank, zero tree counterterms, and finite-reader reduction. Does not prove the evaluated ghost-box constant or exhaustiveness of the ghost projection in Lean.',
        'source':'checks/matching/GhostBoxSource.lean','source_sha256':sha(original),
        'log':'evidence/matching/ghost-box-source.log','log_sha256':sha(log),
        'command':command,'project':str(project),'exit_code':result.returncode,'printed_axioms':axioms,
        'submission_manifest_sha256':pin['manifest_sha256'],'submission_files_verified':count,
        'source_build_reused':True,'fresh_review_build':True,'comparator_run':False,
        'warnings':[x for x in text.splitlines() if 'warning:' in x]}
    (work/'ghost-box-source.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__': main()
