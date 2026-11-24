#!/usr/bin/env python3
"""Build and axiom-audit the full independent finite gluon-bubble comparison.

Uses a fresh review overlay and already-built, pinned November libraries.
Does not change the submission or claim a new whole-submission rebuild.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

MODULES = [
    'GhostConventionCheck', 'GhostLoopBenchmark', 'GhostLoopFiniteEvaluation',
    'GhostLoopTrace', 'GhostLoopRadial', 'GhostLoopContinuation', 'GhostLoopJet',
    'GhostLoopInfrared', 'GhostLoopMellin', 'GhostLoopPrimitive', 'GhostLoopFlow',
    'GhostLoopUnit', 'GhostLoopTensor', 'GhostLoopSolution', 'GhostFiniteAudit',
    'GluonLoopVertex',
    'GluonLoopTrace',
    'GluonLoopFinite',
    'GluonLoopHeat',
    'GluonLoopTensor',
    'GluonLoopContraction',
    'GluonLoopYeast',
    'GluonLoopGaussian',
    'GluonLoopCarpet',
    'GluonLoopRadial',
    'GluonLoopContinuation',
    'GluonLoopJet',
    'GluonLoopInfrared',
    'GluonLoopJetParameter',
    'GluonLoopFlow',
    'GluonLoopUnit',
    'GluonLoopSolution',
    'GluonFiniteAudit',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGET = 'YMReview.NovemberMatching.GluonSolution.acceptance'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def now():
    return datetime.now(timezone.utc).isoformat()


def prepare(repo, source, project):
    project.mkdir(parents=True)
    for module in MODULES:
        shutil.copyfile(repo / 'checks/matching' / (module + '.lean'), project / (module + '.lean'))
    shutil.copyfile(source / 'lean-toolchain', project / 'lean-toolchain')
    (project / 'lakefile.toml').write_text(
        'name = "gluon_finite_review"\nversion = "0.1.0"\npackagesDir = ' +
        json.dumps(str(source / '.lake/packages')) +
        '\n[leanOptions]\nmaxHeartbeats = 0\nmaxRecDepth = 4096\n' +
        '[[lean_lib]]\nname = "GluonFiniteReview"\nroots = ' + json.dumps(MODULES) +
        '\n[[require]]\nname = "yang_mills"\npath = ' + json.dumps(str(source)) + '\n')
    manifest = json.loads((source / 'lake-manifest.json').read_text())
    manifest['name'] = 'gluon_finite_review'
    manifest['packagesDir'] = str(source / '.lake/packages')
    for dep in manifest['packages']:
        dep['inherited'] = True
    manifest['packages'].append({'type': 'path', 'name': 'yang_mills', 'scope': '',
        'dir': str(source), 'inherited': False, 'configFile': 'lakefile.toml',
        'manifestFile': 'lake-manifest.json'})
    save(project / 'lake-manifest.json', manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--work', required=True, type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, work = args.source.resolve(), args.work.resolve()
    if work.exists():
        raise SystemExit('Use a new --work directory; previous records are retained.')
    pin = json.loads((repo / 'provenance/submission.json').read_text())
    if sha(source.parent / 'SOURCES.sha256') != pin['manifest_sha256']:
        raise SystemExit('Wrong submission manifest.')
    project, evidence = work / 'project', work / 'evidence'
    prepare(repo, source, project)
    evidence.mkdir()
    output = project / '.lake/build/lib/lean'
    output.mkdir(parents=True)
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    record = {'status': 'running', 'started_utc': now(), 'project': str(project),
        'source': str(source), 'target': TARGET, 'definition_holes': [],
        'submission_manifest_sha256': pin['manifest_sha256'],
        'source_build_reused': True, 'review_build_initially_absent': True,
        'lean_toolchain': (source / 'lean-toolchain').read_text().strip(), 'modules': []}
    receipt = evidence / 'gluon-finite-build.json'
    save(receipt, record)
    for module in MODULES:
        file = project / (module + '.lean')
        log = evidence / (module + '.log')
        command = [lake, 'env', 'lean', '-o', str(output / (module + '.olean')), str(file)]
        started = now()
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
        item = {'module': module, 'source': 'checks/matching/' + file.name,
            'source_sha256': sha(file), 'log': 'evidence/matching/gluon-finite-build/' + log.name,
            'log_sha256': sha(log), 'command': command, 'started_utc': started,
            'finished_utc': now(), 'exit_code': result.returncode}
        record['modules'].append(item)
        save(receipt, record)
        print(module + ': ' + ('passed' if result.returncode == 0 else 'FAILED'), flush=True)
        if result.returncode:
            record.update(status='failed', finished_utc=now())
            save(receipt, record)
            print(log.read_text()[-10000:], flush=True)
            raise SystemExit(result.returncode)
    audit = (evidence / 'GluonFiniteAudit.log').read_text()
    axioms = {name: re.findall(r'[\w.]+', contents) for name, contents in
        re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)}
    if TARGET not in axioms or any(set(values) - ALLOWED for values in axioms.values()):
        raise SystemExit('Missing target axiom report or unpermitted axiom.')
    for item in record['modules']:
        if sha(repo / item['source']) != item['source_sha256']:
            raise SystemExit('Review source changed during build: ' + item['source'])
    record.update(status='passed', finished_utc=now(), printed_axioms=axioms,
        review_sources_unchanged=True,
        warnings=[{'module': item['module'], 'message': line} for item in record['modules']
            for line in (evidence / (item['module'] + '.log')).read_text().splitlines() if 'warning:' in line],
        scope='Full SubmittedFinitePartTest, not only its pole or a conditional implication.')
    save(receipt, record)
    print('Full finite target: build and standard-axiom audit passed.', flush=True)


if __name__ == '__main__':
    main()
