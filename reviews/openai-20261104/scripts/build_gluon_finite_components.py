#!/usr/bin/env python3
"""Fresh build and axiom audit of the gluon finite-value proof components.

This does NOT certify GluonLoop.SubmittedFinitePartTest. The actual
noninteger evaluator-to-heat-density bridge remains an analytic argument.
"""
import argparse, hashlib, json, re, shutil, subprocess
from pathlib import Path
from datetime import datetime, timezone
import build_ghost_finite as ghost

NEW_MODULES=['GluonLoopVertex','GluonLoopTrace','GluonLoopFinite','GluonLoopHeat','GluonLoopTensor']
EXPECTED={
 'GluonVertex.field_W','GluonTrace.trace_value','GluonLoop.submitted_finite_reading',
 'GluonLoop.submitted_finite_derivative','GluonLoop.primitive_deriv',
 'GluonLoop.primitive_large','GluonLoop.primitive_small','GluonLoop.finite_constants',
 'GluonHeat.split_radial_T','GluonHeat.split_radial_L','GluonHeat.heatPolynomial_integral',
 'GluonTensor.finite_sturdy','GluonTensor.finite_scale_word'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',required=True,type=Path)
    parser.add_argument('--work',required=True,type=Path)
    args=parser.parse_args()
    repo=Path(__file__).resolve().parents[1]
    source,work=args.source.resolve(),args.work.resolve()
    if work.exists():raise SystemExit('Use a fresh work directory.')
    pin=json.loads((repo/'provenance/submission.json').read_text())
    if ghost.sha(source.parent/'SOURCES.sha256')!=pin['manifest_sha256']:
        raise SystemExit('Wrong pinned submission manifest.')
    ghost.MODULES=ghost.MODULES+NEW_MODULES
    project,evidence=work/'project',work/'evidence'
    ghost.prepare(repo,source,project)
    evidence.mkdir()
    output=project/'.lake/build/lib/lean';output.mkdir(parents=True)
    record={'status':'running','started_utc':ghost.now(),'source':str(source),
      'source_build_reused':True,'review_build_initially_absent':True,
      'project':str(project),'submission_manifest_sha256':pin['manifest_sha256'],
      'scope':'Gluon finite-value components only. Not a proof of SubmittedFinitePartTest.',
      'full_evaluator_identity':'not_formalized','modules':[],'printed_axioms':{}}
    receipt=evidence/'gluon-finite-components.json'
    ghost.save(receipt,record)
    lake=shutil.which('lake') or '/Users/oai/.elan/bin/lake'
    for module in ghost.MODULES:
        file=project/(module+'.lean');log=evidence/(module+'.log')
        command=[lake,'env','lean','-o',str(output/(module+'.olean')),str(file)]
        with log.open('w') as stream:
            result=subprocess.run(command,cwd=project,stdout=stream,stderr=subprocess.STDOUT)
        record['modules'].append({'module':module,'source':'checks/matching/'+file.name,
          'source_sha256':ghost.sha(file),'log':'evidence/matching/gluon-finite-components/'+log.name,
          'log_sha256':ghost.sha(log),'command':command,'exit_code':result.returncode})
        text=log.read_text()
        if module in NEW_MODULES:
            record['printed_axioms'].update({name:re.findall(r'[\w.]+',contents)
              for name,contents in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)})
        ghost.save(receipt,record)
        print(module+': '+('passed' if result.returncode==0 else 'FAILED'),flush=True)
        if result.returncode:
            record.update(status='failed',finished_utc=ghost.now());ghost.save(receipt,record)
            print(text[-10000:]);raise SystemExit(result.returncode)
    expected={'YMReview.NovemberMatching.'+name for name in EXPECTED}
    if set(record['printed_axioms'])!=expected:raise SystemExit('Missing axiom audit.')
    if any(set(a)-ghost.ALLOWED for a in record['printed_axioms'].values()):
        raise SystemExit('Nonstandard axiom in proof component.')
    for item in record['modules']:
        if ghost.sha(repo/item['source'])!=item['source_sha256']:raise SystemExit('Sources changed during build.')
    record.update(status='passed',finished_utc=ghost.now(),review_sources_unchanged=True)
    ghost.save(receipt,record)
    print('All 13 gluon component audits passed. Full submitted finite target remains unproved in Lean.')

if __name__=='__main__':main()
