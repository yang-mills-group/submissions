#!/usr/bin/env python3
"""Freeze and check the November combined targets using existing source builds.

Requires the reviewed submission and built Comparator/lean4export checkouts.
Creates a new overlay project, never overwrites a previous run. On macOS uses
upstream fake-landrun.sh: this is a development check, not an isolated run.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True, help='Built November lean/ directory')
    parser.add_argument('--tools', type=Path, required=True, help='Parent of comparator/ and lean4export/')
    parser.add_argument('--work', type=Path, required=True, help='New run directory')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, toolroot, work = (p.resolve() for p in (args.source, args.tools, args.work))
    if work.exists():
        raise SystemExit('Choose a new --work directory; existing evidence is never overwritten.')
    audit = json.loads((repo / 'evidence/independent-checks/AxiomAudit.json').read_text())
    if audit['status'] != 'passed':
        raise SystemExit('Compile and audit AxiomAudit before freezing the target.')
    modules = []
    for item in audit['modules']:
        rel = Path(*item['module'].split('.')).with_suffix('.lean')
        path = repo / 'checks' / rel
        if sha(path) != item['source_sha256']:
            raise SystemExit(f'Review source changed since audit: {rel}')
        modules.append({'module': item['module'], 'path': str(rel), 'sha256': sha(path)})
    pin = json.loads((repo / 'provenance/submission.json').read_text())
    manifest = source.parent / 'SOURCES.sha256'
    if sha(manifest) != pin['manifest_sha256']:
        raise SystemExit('Submission manifest is not the pinned November input.')

    def verify_submission():
        count = 0
        for line in manifest.read_text().splitlines():
            expected, rel = line.split(maxsplit=1)
            path = (source.parent / rel.removeprefix('*')).resolve(strict=True)
            if not path.is_relative_to(source.parent) or sha(path) != expected:
                raise SystemExit(f'Submission mismatch: {rel}')
            count += 1
        if count != pin['files_in_manifest']:
            raise SystemExit(f'Wrong submission manifest count: {count}')
        return {'files_checked': count, 'manifest_sha256': sha(manifest), 'checked_utc': now()}

    before = verify_submission()
    pins = {'comparator': 'd03acab154d269c06e60e4de7e4cc85deebff94b',
            'lean4export': '4e7915201d3f9f04470d9eae002fa695f7cdc589'}
    tool_records = []
    for name, revision in pins.items():
        checkout = toolroot / name
        head = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(checkout), 'status', '--porcelain',
                                        '--untracked-files=no'], text=True).strip()
        if head != revision or dirty:
            raise SystemExit(f'Tool pin mismatch or tracked changes: {name}')
        binary = checkout / '.lake/build/bin' / name
        tool_records.append({'name': name, 'revision': head,
                             'toolchain': (checkout / 'lean-toolchain').read_text().strip(),
                             'binary': str(binary), 'binary_sha256': sha(binary)})
    project = work / 'project'
    project.mkdir(parents=True)
    evidence = work / 'evidence'
    evidence.mkdir()
    for module in modules:
        target = project / module['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(repo / 'checks' / module['path'], target)
    shutil.copyfile(repo / 'comparator/NovemberChallenge.lean', project / 'NovemberChallenge.lean')
    shutil.copyfile(repo / 'comparator/combined.json', project / 'comparator.json')
    shutil.copyfile(source / 'lean-toolchain', project / 'lean-toolchain')
    roots = [x['module'] for x in modules] + ['NovemberChallenge']
    lakefile = ('name = "november_review"\nversion = "0.1.0"\n'
                'packagesDir = ' + json.dumps(str(source / '.lake/packages')) + '\n'
                '[leanOptions]\nmaxHeartbeats = 0\nmaxRecDepth = 4096\n'
                '[[lean_lib]]\nname = "NovemberReview"\nroots = ' + json.dumps(roots) + '\n'
                '[[require]]\nname = "yang_mills"\npath = ' + json.dumps(str(source)) + '\n')
    (project / 'lakefile.toml').write_text(lakefile)
    lake_manifest = json.loads((source / 'lake-manifest.json').read_text())
    lake_manifest['name'] = 'november_review'
    lake_manifest['packagesDir'] = str(source / '.lake/packages')
    for dependency in lake_manifest['packages']:
        dependency['inherited'] = True
    lake_manifest['packages'].append({'type': 'path', 'name': 'yang_mills', 'scope': '',
                                     'dir': str(source), 'inherited': False,
                                     'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json'})
    save(project / 'lake-manifest.json', lake_manifest)
    files = [{'path': str(p.relative_to(project)), 'sha256': sha(p)}
             for p in sorted(project.rglob('*')) if p.is_file()]
    save(evidence / 'prepared-inputs.json', {
        'prepared_utc': now(), 'source': str(source), 'project': str(project),
        'review_modules': modules, 'project_files': files, 'tools': tool_records,
        'submission_before': before, 'submission_build_reused': True,
        'project_build_initially_absent': True, 'definition_holes': [],
        'mode': 'macOS development; upstream fake-landrun; no optional second kernel'})
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    env = os.environ.copy()
    env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    overrides = {'LEAN_NUM_THREADS': '4',
                 'COMPARATOR_LANDRUN': str(toolroot / 'comparator/scripts/fake-landrun.sh'),
                 'COMPARATOR_LEAN4EXPORT': str(toolroot / 'lean4export/.lake/build/bin/lean4export')}
    env.update(overrides)
    command = [lake, 'env', str(toolroot / 'comparator/.lake/build/bin/comparator'), 'comparator.json']
    log = evidence / 'combined-comparator.log'
    receipt = evidence / 'combined-comparator.json'
    record = {'status': 'running', 'started_utc': now(), 'command': command,
              'cwd': str(project), 'environment_overrides': overrides, 'log': log.name}
    save(receipt, record)
    started = time.monotonic()
    print('Comparator started: ' + str(log), flush=True)
    with log.open('w') as stream:
        proc = subprocess.Popen(command, cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record['pid'] = proc.pid
        save(receipt, record)
        code = proc.wait()
    output = log.read_text()
    passed = code == 0 and 'Your solution is okay!' in output and 'Lean default kernel accepts the solution' in output
    record.update(status='checking_inputs', exit_code=code, finished_utc=now(),
                  elapsed_seconds=round(time.monotonic()-started, 2), log_sha256=sha(log))
    save(receipt, record)
    try:
        for item in files:
            if sha(project / item['path']) != item['sha256']:
                raise SystemExit(f'Frozen comparator input changed: {item["path"]}')
        save(evidence / 'input-stability.json', {'project_files_unchanged': True,
                                              'submission_after': verify_submission()})
    except BaseException as error:
        record.update(status='failed_input_stability', input_error=str(error))
        save(receipt, record)
        raise
    record['status'] = 'passed' if passed else 'failed'
    save(receipt, record)
    print('Comparator: ' + record['status'], flush=True)
    if not passed:
        print(output[-8000:], flush=True)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
