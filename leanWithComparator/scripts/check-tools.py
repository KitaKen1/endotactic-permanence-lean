#!/usr/bin/env python3
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
pins = json.loads((root / 'pins.json').read_text())
tools = Path(os.environ['COMPARATOR_TOOLS'])
record = {'status': 'PASS', 'commits': {}, 'versions': {}, 'binary_sha256': {}}
for name, key in [('comparator', 'comparator_commit'), ('lean4export', 'lean4export_commit'), ('landrun', 'landrun_commit')]:
    actual = subprocess.check_output(['git', '-C', str(tools / name), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == pins[key], 'Tool commit differs: ' + name
    record['commits'][name] = actual
for name in ['comparator', 'lean4export']:
    tool = tools / name
    assert (tool / 'lean-toolchain').read_bytes() == (root / 'lean-toolchain').read_bytes()
    changed = subprocess.check_output(['git', '-C', str(tool), 'diff', '--name-only', 'HEAD'], text=True).splitlines()
    assert changed == ['lean-toolchain'], 'Unexpected checker source changes: ' + name
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=tool, text=True).strip()
    assert re.search(r'Lean \(version 4\.33\.1(?:,|\))', version), version
    record['versions'][name] = version
    record['binary_sha256'][name] = hashlib.sha256((tool / '.lake/build/bin' / name).read_bytes()).hexdigest()
assert not subprocess.check_output(['git','-C',str(tools/'landrun'),'diff','--name-only','HEAD'],text=True).strip()
record['binary_sha256']['landrun'] = hashlib.sha256((tools/'bin/landrun').read_bytes()).hexdigest()
out = root / 'evidence'
out.mkdir(exist_ok=True)
(out / 'checker-environment.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: pinned checker sources, toolchain-only patches, Lean 4.33.1 binaries')
