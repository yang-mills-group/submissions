#!/usr/bin/env python3
"""Record the October-to-November source port. Text checks complement Lean, not replace it."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    # Preserve line boundaries while removing nested Lean comments and strings.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated block comment')
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--october', type=Path, required=True, help='Pinned October checks directory')
    parser.add_argument('--source', type=Path, required=True, help='November lean/ source directory')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    checks = repo / 'checks'
    baseline = json.loads((repo / 'provenance/october-checks.json').read_text())
    files = []
    for entry in baseline['files']:
        old = args.october / entry['path']
        if sha(old) != entry['october_sha256']:
            raise SystemExit(f'October baseline mismatch: {old}')
        newpath = entry['path'].replace('YangMills/OSRecon/', 'NovemberOSRecon/')
        new = checks / newpath
        a, b = old.read_text(), new.read_text()
        status = ('identical' if a == b else 'module-path-only'
                  if a.replace('YangMills.OSRecon', 'NovemberOSRecon') == b else 'adapted')
        files.append(dict(entry, november_path=newpath, november_sha256=sha(new), status=status))

    def declaration(text, name):
        text = code_only(text)
        match = re.search(r'^(?:structure|def) ' + name + r'\b', text, re.M)
        if match is None:
            raise SystemExit(f'Missing independent declaration: {name}')
        rest = text[match.end():]
        end = re.search(r'^(?:structure|def|theorem|end|variable|namespace)\b', rest, re.M)
        return re.sub(r'\s+', '', text[match.start():match.end()] + (rest[:end.start()] if end else rest))

    independent = ['LatticeAndScale', 'PhaseAndOS', 'TranslationWard', 'OperatorContent',
                   'LeadingTrace', 'Accepted', 'CombinedAcceptance']
    before = (args.october / 'AcceptanceSpec.lean').read_text()
    after = (checks / 'AcceptanceSpec.lean').read_text()
    for name in independent:
        if declaration(before, name) != declaration(after, name):
            raise SystemExit(f'Independent target changed: {name}')
    old_ope = code_only((args.october / 'OPESpec.lean').read_text())
    new_ope = code_only((checks / 'OPESpec.lean').read_text())
    old_ope = old_ope.replace('import ChallengeSpec', 'import YangMills.CorrelationHierarchy').replace('T.actor', 'T.channelField')
    if re.sub(r'\s+', '', old_ope) != re.sub(r'\s+', '', new_ope):
        raise SystemExit('OPE specification changed beyond the recorded import and channel-field rename.')

    suspicious = []
    for path in sorted(checks.rglob('*.lean')):
        for match in re.finditer(r'\b(?:sorry|admit|axiom|unsafe)\b', code_only(path.read_text())):
            suspicious.append({'path': str(path.relative_to(repo)), 'token': match.group()})
    if suspicious:
        raise SystemExit(f'Review-source admission/axiom/unsafe tokens: {suspicious}')

    seen, submission, external = set(), [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        rel = Path(*module.split('.')).with_suffix('.lean')
        path = checks / rel
        if not path.is_file():
            path = args.source / rel
            if not path.is_file():
                external.add(module)
                return
            submission.append(module)
        for line in re.findall(r'^import\s+([^\n]+)', code_only(path.read_text()), re.M):
            for dep in line.split():
                visit(dep)

    visit('NovemberCombined')
    if 'Comparators.Matching.Solution' in seen:
        raise SystemExit('Matching solution is reachable from the independent existence target.')
    result = {'checked_utc': datetime.now(timezone.utc).isoformat(),
              'scope': 'Text and import checks; not a semantic equivalence proof or Comparator replay.',
              'baseline': {k: baseline[k] for k in ['repository', 'revision', 'path']},
              'files': files, 'unchanged_independent_declarations': independent,
              'ope_only_import_and_channel_field_rename': True,
              'review_admissions_axioms_unsafe_tokens': suspicious,
              'submission_import_module_count': len(submission),
              'matching_solution_reachable': False,
              'external_import_module_count': len(external)}
    dest = repo / 'evidence/independent-checks/port-audit.json'
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'baseline_files': len(files), 'unchanged_predicates': independent,
                      'statuses': {s: sum(f['status'] == s for f in files)
                                   for s in ['identical', 'module-path-only', 'adapted']},
                      'matching_solution_reachable': False}, indent=2))


if __name__ == '__main__':
    main()
