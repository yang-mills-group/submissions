#!/usr/bin/env python3
"""Compile the all-orders statement-alignment theorem in a fresh review overlay.

Uses already-built November libraries; it is not a new full submission build or
Comparator run. The all-order submitted Matching target has separate receipts.
"""
import argparse
from datetime import datetime, timezone
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import build_ghost_finite as overlay


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source, work = args.source.resolve(), args.work.resolve()
    if work.exists():
        raise SystemExit('Choose a fresh work directory to preserve earlier records.')
    pin = json.loads((repo / 'provenance/submission.json').read_text())
    manifest = source.parent / 'SOURCES.sha256'
    if overlay.sha(manifest) != pin['manifest_sha256']:
        raise SystemExit('Unexpected submission manifest.')
    count = 0
    for line in manifest.read_text().splitlines():
        expected, rel = line.split(maxsplit=1)
        p = (source.parent / rel.removeprefix('*')).resolve(strict=True)
        if not p.is_relative_to(source.parent) or overlay.sha(p) != expected:
            raise SystemExit('Submission mismatch: ' + rel)
        count += 1
    if count != pin['files_in_manifest']:
        raise SystemExit('Incomplete submission manifest.')
    project, evidence = work / 'project', work / 'evidence'
    overlay.MODULES = ['AllOrdersStatement']
    overlay.prepare(repo, source, project)
    evidence.mkdir()
    file = project / 'AllOrdersStatement.lean'
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    command = [lake, 'env', 'lean', str(file)]
    log = evidence / 'all-orders-statement.log'
    record = {'status': 'running', 'started_utc': overlay.now(),
              'command': command, 'cwd': str(project),
              'source': 'checks/matching/AllOrdersStatement.lean',
              'source_sha256': overlay.sha(file),
              'log': 'evidence/matching/all-orders-statement.log',
              'submission_manifest_sha256': pin['manifest_sha256'],
              'submission_files_verified': count,
              'submission_build_reused': True, 'fresh_overlay': True,
              'target': 'YMReview.NovemberMatching.AllOrders.submitted',
              'scope': 'Shared witnesses and all-orders remainder statement; reuses the public graph reference. Not an independent validation of all graph rules.'}
    receipt = evidence / 'all-orders-statement.json'
    overlay.save(receipt, record)
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
    output = log.read_text()
    axioms = {name: re.findall(r'[\w.]+', contents) for name, contents in
              re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
    passed = (result.returncode == 0 and record['target'] in axioms and
              not any(set(values) - overlay.ALLOWED for values in axioms.values()) and
              overlay.sha(repo / record['source']) == record['source_sha256'])
    record.update(status='passed' if passed else 'failed', exit_code=result.returncode,
                  finished_utc=overlay.now(), log_sha256=overlay.sha(log),
                  printed_axioms=axioms,
                  warnings=[s for s in output.splitlines() if 'warning:' in s])
    overlay.save(receipt, record)
    print(output)
    print('All-orders statement: ' + record['status'])
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
