#!/usr/bin/env python3
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
pins = json.loads((root / 'pins.json').read_text())
text = Path(sys.argv[1]).read_text()
records = {}
for name in pins['targets']:
    pattern = "'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    matches = re.findall(pattern, text)
    assert len(matches) == 1, 'Missing or duplicate axiom report: ' + name
    axioms = [a.strip() for a in matches[0].split(',') if a.strip()]
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    records[name] = axioms
assert 'sorryAx' not in text and 'error:' not in text
Path(sys.argv[2]).write_text(json.dumps({'status': 'PASS', 'targets': records}, indent=2) + '\n')
print('PASS: both original targets use only permitted axioms')
