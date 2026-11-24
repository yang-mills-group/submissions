#!/usr/bin/env python3
"""Check copied artifacts and, optionally, the pinned submission. No Lean run."""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    checksum = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            checksum.update(block)
    return checksum.hexdigest()


def check_file(path, expected):
    actual = digest(path)
    if actual != expected:
        raise SystemExit(f'Hash mismatch: {path}: {actual} != {expected}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, help='Received submission root containing SOURCES.sha256')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    artifacts = json.loads((repo / 'provenance/artifacts.json').read_text())
    for entry in artifacts['files']:
        check_file(repo / entry['path'], entry['sha256'])
    records = repo / 'evidence/supplied-targets'
    receipt_count = 0
    for path in records.glob('*.json'):
        receipt = json.loads(path.read_text())
        if 'log_sha256' in receipt:
            check_file(records / Path(receipt['log']).name, receipt['log_sha256'])
            receipt_count += 1
    recheck = json.loads((records / 'patched-comparator-recheck.json').read_text())
    for result in recheck['results']:
        check_file(records / Path(result['run']['log']).name, result['run']['log_sha256'])
        check_file(records / (result['selector'] + '.json'), result['config_sha256'])
    independent = repo / 'evidence/independent-checks'
    for name in ['OSAudit', 'AxiomAudit']:
        path = independent / (name + '.json')
        if not path.exists():
            continue
        receipt = json.loads(path.read_text())
        if receipt['status'] != 'passed':
            raise SystemExit(f'Independent audit is not passed: {name}')
        for item in receipt['modules']:
            source = repo / 'checks' / Path(*item['module'].split('.')).with_suffix('.lean')
            check_file(source, item['source_sha256'])
            check_file(repo / item['log'], item['log_sha256'])
        print(f'{name}: {len(receipt["modules"])} source/log pairs verified.')
    comparator = repo / 'evidence/combined-targets'
    if comparator.exists():
        receipt = json.loads((comparator / 'combined-comparator.json').read_text())
        if receipt['status'] != 'passed':
            raise SystemExit('Combined Comparator did not pass.')
        check_file(comparator / Path(receipt['log']).name, receipt['log_sha256'])
        prepared = json.loads((comparator / 'prepared-inputs.json').read_text())
        for item in prepared['review_modules']:
            check_file(repo / 'checks' / item['path'], item['sha256'])
        frozen = {item['path']: item['sha256'] for item in prepared['project_files']}
        check_file(repo / 'comparator/NovemberChallenge.lean', frozen['NovemberChallenge.lean'])
        check_file(repo / 'comparator/combined.json', frozen['comparator.json'])
        stability = json.loads((comparator / 'input-stability.json').read_text())
        if not stability['project_files_unchanged'] or stability['submission_after']['manifest_sha256'] != prepared['submission_before']['manifest_sha256']:
            raise SystemExit('Comparator input stability check did not pass.')
        print('Combined Comparator: source, reference, configuration and log hashes verified.')
    pin = json.loads((repo / 'provenance/submission.json').read_text())
    matching = repo / 'evidence/matching'
    if matching.exists():
        audit = json.loads((matching / 'diagram-reference-audit.json').read_text())
        if audit['status'] != 'passed':
            raise SystemExit('Diagram reference audit did not pass.')
        check_file(repo / audit['source'], audit['source_sha256'])
        check_file(repo / audit['log'], audit['log_sha256'])
        specifications = json.loads((matching / 'independent-tests-build.json').read_text())
        check_file(repo / 'checks/matching/IndependentMatchingTests.lean', specifications['file_sha256'])
        check_file(matching / 'independent-tests-build.log', specifications['log_sha256'])
        for name in ['ghost-convention-check', 'counterterm-audit', 'ghost-loop-benchmark', 'ghost-loop-finite-evaluation']:
            record = json.loads((matching / (name + '.json')).read_text())
            if record['status'] != 'passed':
                raise SystemExit(f'Matching audit did not pass: {name}')
            check_file(repo / record['source'], record['source_sha256'])
            check_file(repo / record['log'], record['log_sha256'])
        print('Matching: diagram, ghost, counterterm, loop benchmark, finite integral checks and initial specification source/log hashes verified.')
        finite = json.loads((matching / 'ghost-finite-build.json').read_text())
        target = 'YMReview.NovemberMatching.GhostSolution.acceptance'
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        if finite['status'] != 'passed' or finite['target'] != target or finite['definition_holes']:
            raise SystemExit('Full finite ghost-loop build/target did not pass.')
        if target not in finite['printed_axioms'] or any(
                set(values) - allowed for values in finite['printed_axioms'].values()):
            raise SystemExit('Full finite ghost-loop axiom audit is missing or has extra axioms.')
        for item in finite['modules']:
            check_file(repo / item['source'], item['source_sha256'])
            check_file(repo / item['log'], item['log_sha256'])
            if item['exit_code'] != 0:
                raise SystemExit('Finite ghost-loop module did not compile: ' + item['module'])
        directory = matching / 'ghost-finite-comparator'
        receipt = json.loads((directory / 'ghost-finite-comparator.json').read_text())
        if receipt['status'] != 'passed' or receipt['exit_code'] != 0:
            raise SystemExit('Finite ghost-loop Comparator did not pass.')
        log = directory / Path(receipt['log']).name
        check_file(log, receipt['log_sha256'])
        output = log.read_text()
        if not all(marker in output for marker in [
                'Your solution is okay!', 'Lean default kernel accepts the solution']):
            raise SystemExit('Finite ghost-loop Comparator success markers are missing.')
        prepared = json.loads((directory / 'prepared-inputs.json').read_text())
        if prepared['target'] != target or prepared['definition_holes']:
            raise SystemExit('Wrong finite ghost-loop frozen target or definition holes.')
        check_file(matching / 'ghost-finite-build.json', prepared['audit_receipt_sha256'])
        for item in prepared['review_modules']:
            check_file(repo / item['repository_source'], item['sha256'])
        frozen = {item['path']: item['sha256'] for item in prepared['project_files']}
        check_file(repo / 'comparator/GhostFiniteChallenge.lean', frozen['GhostFiniteChallenge.lean'])
        check_file(repo / 'comparator/ghost-finite.json', frozen['comparator.json'])
        stability = json.loads((directory / 'input-stability.json').read_text())
        if not stability['project_files_unchanged']:
            raise SystemExit('Finite ghost-loop input stability did not pass.')
        for snapshot in [prepared['submission_before'], stability['submission_after']]:
            if (snapshot['manifest_sha256'] != pin['manifest_sha256'] or
                    snapshot['files_checked'] != pin['files_in_manifest']):
                raise SystemExit('Finite ghost-loop submission verification is incomplete.')
        print('Full finite ghost-loop: 15-module build, axiom audit, frozen target, Comparator log and input stability verified.')
        statement = json.loads((matching / 'all-orders-statement.json').read_text())
        target = 'YMReview.NovemberMatching.AllOrders.submitted'
        if statement['status'] != 'passed' or statement['exit_code'] != 0 or statement['target'] != target:
            raise SystemExit('All-orders statement alignment did not pass.')
        check_file(repo / statement['source'], statement['source_sha256'])
        check_file(repo / statement['log'], statement['log_sha256'])
        if target not in statement['printed_axioms'] or any(
                set(values) - allowed for values in statement['printed_axioms'].values()):
            raise SystemExit('All-orders statement audit is missing or has extra axioms.')
        if (statement['submission_manifest_sha256'] != pin['manifest_sha256'] or
                statement['submission_files_verified'] != pin['files_in_manifest']):
            raise SystemExit('All-orders statement submission pin mismatch.')
        print('All-orders statement: source, log, standard-axiom audit and submission pin verified.')
        box_path = matching / 'ghost-box-source.json'
        if box_path.exists():
            box = json.loads(box_path.read_text())
            if (box['status'] != 'passed' or box['exit_code'] != 0 or
                    box['submission_manifest_sha256'] != pin['manifest_sha256'] or
                    box['submission_files_verified'] != pin['files_in_manifest']):
                raise SystemExit('Ghost-box structural check or source pin failed.')
            expected = {'tree_result', 'tree_pole', 'family_member', 'family_slots',
                        'finite_reading', 'actual_pole'}
            if ({name.rsplit('.', 1)[-1] for name in box['printed_axioms']} != expected or
                    any(set(a) - allowed for a in box['printed_axioms'].values())):
                raise SystemExit('Ghost-box structural axiom audit is missing or has extra axioms.')
            check_file(repo / box['source'], box['source_sha256'])
            check_file(repo / box['log'], box['log_sha256'])
            print('Ghost box: six structural lemmas verified; final finite-value proposition is not proved in Lean.')
        section23_path = matching / 'section23-audit.json'
        if section23_path.exists():
            review = json.loads(section23_path.read_text())
            if (review['status'] != 'passed' or review['exit_code'] != 0 or
                    review['submission_manifest_sha256'] != pin['manifest_sha256'] or
                    review['submission_files_verified'] != pin['files_in_manifest'] or
                    len(review['printed_axioms']) != 11 or
                    any(set(a) - allowed for a in review['printed_axioms'].values())):
                raise SystemExit('Section 2.3 audit or source pin failed.')
            check_file(repo / review['source'], review['source_sha256'])
            check_file(repo / review['log'], review['log_sha256'])
            algebra = json.loads((matching / 'section23-algebra.json').read_text())
            if (algebra['status'] != 'passed' or
                    sum(x['cubic_momentum_coefficients'] for x in algebra['vertex_tests']) != 69888 or
                    sum(x['quartic_tensor_entries'] for x in algebra['vertex_tests']) != 86272 or
                    len(algebra['wilson_affine_SU2_plaquettes']) != 4):
                raise SystemExit('Section 2.3 exact algebra receipt failed.')
            print('Section 2.3: density identities, nine submitted bridges and exact algebra receipts verified; no general forest-equivalence claim.')
        gluon_path = matching / 'gluon-polarization-audit.json'
        if gluon_path.exists():
            gluon = json.loads(gluon_path.read_text())
            if (gluon['status'] != 'passed' or gluon['exit_code'] != 0 or
                    gluon['submission_manifest_sha256'] != pin['manifest_sha256'] or
                    gluon['submission_files_verified'] != pin['files_in_manifest'] or
                    len(gluon['printed_axioms']) != 9 or
                    any(set(a) - allowed for a in gluon['printed_axioms'].values())):
                raise SystemExit('Gluon polarization audit or source pin failed.')
            check_file(repo / gluon['source'], gluon['source_sha256'])
            check_file(repo / gluon['log'], gluon['log_sha256'])
            reference = json.loads((matching / 'gluon-bubble-reference.json').read_text())
            check_file(repo / 'scripts/check_gluon_bubble_reference.py', reference['script_sha256'])
            if (reference['status'] != 'passed' or reference['explicit_index_checks'] != 48 or
                    reference['transverse_pole'] != '25/12' or
                    reference['transverse_finite_constant'] != '89/36' or
                    reference['extra_trace_finite_difference'] != '1/3'):
                raise SystemExit('Gluon-bubble reference receipt failed.')
            print('Historical gluon trace diagnostics and independent finite reference verified.')
        components_path = matching / 'gluon-finite-components.json'
        if components_path.exists():
            components = json.loads(components_path.read_text())
            if (components['status'] != 'passed' or
                    components['full_evaluator_identity'] != 'not_formalized' or
                    components['submission_manifest_sha256'] != pin['manifest_sha256'] or
                    len(components['printed_axioms']) != 13 or
                    any(set(a) - allowed for a in components['printed_axioms'].values())):
                raise SystemExit('Gluon finite component audit failed or misstated its scope.')
            for item in components['modules']:
                check_file(repo / item['source'], item['source_sha256'])
                check_file(repo / item['log'], item['log_sha256'])
                if item['exit_code'] != 0:
                    raise SystemExit('Gluon component dependency failed: ' + item['module'])
            heat = json.loads((matching / 'gluon-finite-heat.json').read_text())
            check_file(repo / 'scripts/check_gluon_finite_heat.py', heat['script_sha256'])
            if (heat['status'] != 'passed' or
                    heat['channels']['transverse']['finite_constant'] != '89/36' or
                    heat['channels']['longitudinal']['finite_constant'] != '-1/2' or
                    heat['channels']['transverse']['extra_vector_trace_finite_contribution'] != '1/3'):
                raise SystemExit('Gluon finite heat calculation failed.')
            print('Historical gluon component evidence: 13 axiom audits and heat receipt verified.')
        finite = json.loads((matching / 'gluon-finite-build.json').read_text())
        target = 'YMReview.NovemberMatching.GluonSolution.acceptance'
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        if finite['status'] != 'passed' or finite['target'] != target or finite['definition_holes']:
            raise SystemExit('Full finite gluon-bubble build/target did not pass.')
        if target not in finite['printed_axioms'] or any(
                set(values) - allowed for values in finite['printed_axioms'].values()):
            raise SystemExit('Full finite gluon-bubble axiom audit is missing or has extra axioms.')
        for item in finite['modules']:
            check_file(repo / item['source'], item['source_sha256'])
            check_file(repo / item['log'], item['log_sha256'])
            if item['exit_code'] != 0:
                raise SystemExit('Finite gluon-bubble module did not compile: ' + item['module'])
        directory = matching / 'gluon-finite-comparator'
        receipt = json.loads((directory / 'gluon-finite-comparator.json').read_text())
        if receipt['status'] != 'passed' or receipt['exit_code'] != 0:
            raise SystemExit('Finite gluon-bubble Comparator did not pass.')
        log = directory / Path(receipt['log']).name
        check_file(log, receipt['log_sha256'])
        output = log.read_text()
        if not all(marker in output for marker in [
                'Your solution is okay!', 'Lean default kernel accepts the solution']):
            raise SystemExit('Finite gluon-bubble Comparator success markers are missing.')
        prepared = json.loads((directory / 'prepared-inputs.json').read_text())
        if prepared['target'] != target or prepared['definition_holes']:
            raise SystemExit('Wrong finite gluon-bubble frozen target or definition holes.')
        check_file(matching / 'gluon-finite-build.json', prepared['audit_receipt_sha256'])
        for item in prepared['review_modules']:
            check_file(repo / item['repository_source'], item['sha256'])
        frozen = {item['path']: item['sha256'] for item in prepared['project_files']}
        check_file(repo / 'comparator/GluonFiniteChallenge.lean', frozen['GluonFiniteChallenge.lean'])
        check_file(repo / 'comparator/gluon-finite.json', frozen['comparator.json'])
        stability = json.loads((directory / 'input-stability.json').read_text())
        if not stability['project_files_unchanged']:
            raise SystemExit('Finite gluon-bubble input stability did not pass.')
        for snapshot in [prepared['submission_before'], stability['submission_after']]:
            if (snapshot['manifest_sha256'] != pin['manifest_sha256'] or
                    snapshot['files_checked'] != pin['files_in_manifest']):
                raise SystemExit('Finite gluon-bubble submission verification is incomplete.')
        print('Full finite gluon-bubble: 33-module build, axiom audit, frozen target, Comparator log and input stability verified.')
    manifest = repo / 'provenance/SUBMISSION-SOURCES.sha256'
    check_file(manifest, pin['manifest_sha256'])
    print(f'Artifacts: {len(artifacts["files"])} verified; receipt log hashes: {receipt_count} verified.')
    if args.source is not None:
        source = args.source.resolve(strict=True)
        check_file(source / pin['manifest'], pin['manifest_sha256'])
        count = 0
        for line in manifest.read_text().splitlines():
            expected, filename = line.split(maxsplit=1)
            path = (source / filename.removeprefix('*')).resolve(strict=True)
            if not path.is_relative_to(source):
                raise SystemExit(f'Manifest path outside source: {filename}')
            check_file(path, expected)
            count += 1
        if count != pin['files_in_manifest']:
            raise SystemExit(f'Unexpected manifest count: {count}')
        print(f'Submission: {count} files verified against the pinned manifest.')
    print('This checks file integrity only; it does not compile Lean or rerun Comparator.')


if __name__ == '__main__':
    main()
