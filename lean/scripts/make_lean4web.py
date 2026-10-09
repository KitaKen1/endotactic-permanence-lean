#!/usr/bin/env python3
"""Generate a Mathlib-only proof with scoped source modules and a source map."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
OUTPUT = ROOT / "lean4web/EndotacticPermanenceLean4Web.lean"
RENAMES = {"if_pos": "ite_eq_left", "if_neg": "ite_eq_right",
           "dif_pos": "dite_eq_left", "dif_neg": "dite_eq_right",
           "if_true": "ite_true"}


def generate():
    visited, active, sources = set(), set(), []

    def visit(module):
        if module in visited:
            return
        if not module.startswith(("Endotactic.", "EndotacticPublication.")):
            return
        if module in active:
            raise ValueError(f"Cyclic project import: {module}")
        path = LEAN.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.exists():
            raise ValueError(f"Missing project import: {module}")
        active.add(module)
        text = path.read_text()
        for dependency in re.findall(r"^(?:public )?import (\S+)\s*$", text, re.M):
            visit(dependency)
        active.remove(module)
        visited.add(module)
        body = re.sub(r"^(?:public )?import [^\n]+\n", "", text, flags=re.M).strip()
        for old, new in RENAMES.items():
            body = re.sub(r"\b" + old + r"\b", new, body)
        # A Lean module normally starts with fresh open/variable/option scopes.
        # A surrounding section preserves those scopes in the concatenation.
        sources.append((path, body))

    visit("EndotacticPublication.FCPresentation")
    visit("Endotactic.GeneralPermanenceExamples")
    header = '''module

public import Mathlib

/-!
# Endotactic permanence: complete Mathlib-only Lean4Web proof

Generated from the modular proof by lean/scripts/make_lean4web.py.
Target environment: Lean v4.35.0-rc4 and Mathlib
1f414401f69059aa7eead47b53ee40bd38455eeb.
The checked environment and source hashes are in lean/evidence/build_results.json.

Final FC-style targets:
* EndotacticFC.extended_permanence
* EndotacticFC.measurable_extended_permanence

Both use answer(True) outside all quantifiers. The local identity notation
has the same elaborated type as FC's notation; the modular publication audit
also compares the compiled types against the actual FC utility.

Finite natural exponents, positive coefficient boxes, bounded measurable
rates, positive global well-posedness and eventual coordinate bounds are
formalized. Original-convention review and real-exponent/differential-inclusion
extensions remain separate. No custom project or FC imports are needed.
LeanPool attribution is preserved at the adapted source section; see the
repository's THIRD_PARTY_NOTICES.txt and licenses directory.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

#eval Lean.versionString
'''
    content, mapping = header, []
    for path, body in sources:
        name = path.relative_to(LEAN).as_posix()
        line = len(content.splitlines()) + 1
        content += f"\n-- Source: {name}\nsection\n{body}\nend\n"
        mapping.append({"source": name, "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "first_line": line, "last_line": len(content.splitlines())})
    content += "\n#print axioms EndotacticFC.extended_permanence\n"
    content += "#print axioms EndotacticFC.measurable_extended_permanence\n"
    OUTPUT.write_text(content)
    record = {"generator": "lean/scripts/make_lean4web.py", "modules": len(sources),
              "lines": len(content.splitlines()), "renames": RENAMES, "source_map": mapping,
              "output_sha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}
    (ROOT / "lean4web/source-map.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Generated {OUTPUT.name}: {len(sources)} modules, {record['lines']} lines")
    return content


if __name__ == "__main__":
    generate()
