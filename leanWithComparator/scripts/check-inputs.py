#!/usr/bin/env python3
"""Fail closed on changes to the FC specification, original proofs or harness."""
import argparse
import datetime
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-dependencies', action='store_true')
parser.add_argument('--receipt-dir', type=Path)
args = parser.parse_args()
pins = json.loads((ROOT / 'pins.json').read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *arguments):
    return subprocess.check_output(['git', '-C', str(path), *arguments], text=True).strip()


for name, expected in pins['files_sha256'].items():
    assert sha(ROOT / name) == expected, 'Harness hash mismatch: ' + name
raw = (ROOT / 'sources/pr-statement.lean').read_bytes()
assert hashlib.sha256(raw).hexdigest() == pins['pr_statement_sha256']
assert raw.count(b'\nnamespace Endotactic\n') == 1
assert raw.count(b'\nend Endotactic\n') == 1
expected = raw.replace(b'\nnamespace Endotactic\n', b'\nnamespace EndotacticFC\n', 1)
expected = expected.replace(b'\nend Endotactic\n', b'\nend EndotacticFC\n', 1)
assert (ROOT / 'Challenge.lean').read_bytes() == expected, 'Unexpected Challenge changes'
assert (ROOT / 'Solution.lean').read_text() == (
    'import EndotacticPublication.FCPresentation\n\n'
    '/-! The original pinned proofs. This module does not import Challenge. -/\n'
)
assert (ROOT / 'lean-toolchain').read_text().strip() == pins['lean_toolchain']
config = json.loads((ROOT / 'comparator.json').read_text())
assert config['theorem_names'] == pins['targets'] and len(pins['targets']) == 2
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
assert config['definition_names'] == [] and config['enable_nanoda'] is False
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
revs = {p['name']: p['rev'] for p in manifest['packages']}
assert revs == pins['dependency_commits'], 'Locked dependency set changed'
actual = {}
for package, revision in revs.items():
    path = ROOT / '.lake/packages' / package
    if not path.is_dir():
        assert not args.require_dependencies, 'Missing dependency: ' + package
        continue
    actual[package] = git(path, 'rev-parse', 'HEAD')
    assert actual[package] == revision, 'Dependency checkout differs: ' + package
proof = ROOT / '.lake/packages/endotacticPermanence'
if proof.is_dir():
    for name, digest in pins['proof_files_sha256'].items():
        assert sha(proof / name) == digest, 'Original proof source changed: ' + name
    assert not git(proof, 'diff', '--name-only', 'HEAD', '--', *pins['proof_files_sha256'])
fc = ROOT / '.lake/packages/formal_conjectures'
if fc.is_dir():
    assert (fc / pins['pr_statement_path']).read_bytes() == raw, 'FC original differs'
    assert not git(fc, 'diff', '--name-only', 'HEAD'), 'FC dependency has tracked changes'
    assert (fc / 'lean-toolchain').read_text().strip() == pins['lean_toolchain']
record = {
    'status': 'PASS',
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'harness_commit': git(ROOT, 'rev-parse', 'HEAD'),
    'fc_head': pins['pr_head'], 'proof_commit': pins['proof_commit'],
    'targets': pins['targets'], 'dependency_commits': actual,
    'proof_source_file_count': len(pins['proof_files_sha256']),
    'pins_sha256': sha(ROOT / 'pins.json'), 'files_sha256': pins['files_sha256'],
    'run': {k: os.environ.get(k) for k in
            ['GITHUB_REPOSITORY', 'GITHUB_SHA', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']},
}
if args.receipt_dir:
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    (args.receipt_dir / 'inputs.json').write_text(json.dumps(record, indent=2) + '\n')
    diff = difflib.unified_diff(raw.decode().splitlines(True), expected.decode().splitlines(True),
                                fromfile='FC-original.lean', tofile='Challenge.lean')
    (args.receipt_dir / 'challenge.diff').write_text(''.join(diff))
print('PASS: exact FC input, two namespace lines, original proof sources, dependencies and harness')
