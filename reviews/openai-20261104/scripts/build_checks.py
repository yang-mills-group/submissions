#!/usr/bin/env python3
"""Compile review sources against an existing November build; never reuse October oleans."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path, help='Built November lean/ directory')
    parser.add_argument('--target', default='OSAudit')
    parser.add_argument('--fresh', action='store_true')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    source = args.source.resolve(strict=True)
    checks = repo / 'checks'
    build = repo / '.build'
    logs = repo / 'evidence/independent-checks'
    logs.mkdir(parents=True, exist_ok=True)
    build.mkdir(exist_ok=True)
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    env = os.environ.copy()
    env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    base = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=source, env=env, text=True).strip()
    # Resolve relative entries before moving the working directory or hashing them.
    paths = [str((source / p).resolve()) if not Path(p).is_absolute() else p for p in base.split(os.pathsep)]
    if any('october' in p.lower() or 'ym-rebuild' in p.lower() for p in paths):
        raise SystemExit('Refusing an October source/cache on the November search path.')
    env['LEAN_PATH'] = str(build) + os.pathsep + os.pathsep.join(paths)
    env['LEAN_NUM_THREADS'] = '4'
    lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=source, env=env, text=True).strip()
    modules = {}
    visiting = set()
    order = []
    external = {}
    source_context = sha(source / 'lean-toolchain') + sha(source / 'lake-manifest.json')

    def visit(name):
        if name in modules:
            return modules[name]['fingerprint']
        rel = Path(*name.split('.'))
        path = (checks / rel).with_suffix('.lean')
        if not path.is_file():
            providers = [(Path(p) / rel).with_suffix('.olean') for p in paths]
            found = next((p for p in providers if p.is_file()), None)
            if found is None:
                raise SystemExit(f'Missing built external import: {name}')
            if name not in external:
                external[name] = {'path': str(found), 'sha256': sha(found)}
            return external[name]['sha256']
        if name in visiting:
            raise SystemExit(f'Cyclic review import: {name}')
        visiting.add(name)
        imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)', path.read_text(), re.M)
        dependency_hashes = [visit(dep) for dep in imports]
        fingerprint = hashlib.sha256((source_context + sha(path) + ''.join(dependency_hashes)).encode()).hexdigest()
        modules[name] = {'path': str(path), 'sha256': sha(path), 'fingerprint': fingerprint}
        visiting.remove(name)
        order.append(name)
        return fingerprint

    visit(args.target)
    record = {'target': args.target, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_root': str(source), 'lean_path': env['LEAN_PATH'],
              'lean_version': subprocess.check_output([lean, '--version'], text=True).strip(),
              'status': 'running', 'fresh_review_build': args.fresh, 'modules': [],
              'external_imports': external, 'comparator_run': False}
    receipt = logs / (args.target + '.json')
    started = time.monotonic()
    for name in order:
        data = modules[name]
        rel = Path(*name.split('.'))
        out = (build / rel).with_suffix('.olean')
        stamp = (build / rel).with_suffix('.fingerprint')
        log = logs / (name + '.log')
        out.parent.mkdir(parents=True, exist_ok=True)
        cached = (not args.fresh and out.is_file() and stamp.is_file() and log.is_file()
                  and stamp.read_text() == data['fingerprint'])
        command = [lean, '--root=' + str(checks), '-o', str(out), data['path']]
        t = time.monotonic()
        if cached:
            output = log.read_text()
            code = 0
        else:
            result = subprocess.run(command, cwd=source, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            output, code = result.stdout, result.returncode
            log.write_text(output)
        if sha(Path(data['path'])) != data['sha256']:
            raise SystemExit(f'Source changed during compilation: {name}; rerun the build.')
        entry = {'module': name, 'source_sha256': data['sha256'], 'exit_code': code,
                 'cached': cached, 'command': command, 'seconds': round(time.monotonic()-t, 3),
                 'log': str(log.relative_to(repo)), 'log_sha256': sha(log),
                 'warnings': len(re.findall(r'\bwarning:', output))}
        record['modules'].append(entry)
        receipt.write_text(json.dumps(record, indent=2) + '\n')
        print(f'{name}: {"cached" if cached else "passed" if code == 0 else "FAILED"}', flush=True)
        if code:
            record['status'] = 'failed'
            receipt.write_text(json.dumps(record, indent=2) + '\n')
            print(output, flush=True)
            raise SystemExit(code)
        stamp.write_text(data['fingerprint'])
    reports = []
    for name in order:
        output = (logs / (name + '.log')).read_text()
        for decl, block in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
            axioms = re.findall(r'[\w.]+', block)
            if not set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}:
                raise SystemExit(f'Unexpected axiom dependency for {decl}: {axioms}')
            reports.append({'declaration': decl, 'axioms': axioms})
    if not reports:
        raise SystemExit('No axiom-audit output; refusing to record a verified audit.')
    if args.target == 'AxiomAudit':
        required = {'YMReview.November.combined_acceptance',
                    'YMReview.Acceptance.combined_acceptance',
                    'YMReview.November.public_realizes', 'YMReview.November.public_os'}
        missing = required - {r['declaration'] for r in reports}
        if missing:
            raise SystemExit(f'Missing final theorem audits: {sorted(missing)}')
    for name, data in modules.items():
        if sha(Path(data['path'])) != data['sha256']:
            raise SystemExit(f'Source changed during build: {name}; rerun the build.')
    record.update(status='passed', seconds=round(time.monotonic()-started, 3), axiom_reports=reports,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    receipt.write_text(json.dumps(record, indent=2) + '\n')
    print(f'{args.target}: {len(order)} review modules; {len(reports)} axiom reports; standard axioms only.', flush=True)


if __name__ == '__main__':
    main()
