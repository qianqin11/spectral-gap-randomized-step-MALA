#!/usr/bin/env python3
"""Fail closed on missing or nonstandard output from the Lean axiom audit.
Run only after a successful fresh `lake env lean .../DependencyAudit.lean`.
"""
from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path
import static_audit

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ROOT = Path(__file__).resolve().parents[1]

def check(text: str, expected: set[str]) -> list[str]:
    text = re.sub(r'\x1b\[[0-9;]*m', '', text)
    found: dict[str, set[str]] = {}
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", text, re.S):
        found[m[1]] = {x.strip() for x in m[2].split(',') if x.strip()}
    for m in re.finditer(r"'([^']+)'\s+(?:does not depend on any axioms|does not depend on axioms|uses no axioms)", text):
        found[m[1]] = set()
    errors=[]
    for name in sorted(expected - found.keys()): errors.append('Missing audit output: '+name)
    for name, axioms in found.items():
        extra=axioms-ALLOWED
        if extra: errors.append(name+': unexpected axioms '+', '.join(sorted(extra)))
    if re.search(r'\berror:', text, re.I): errors.append('Lean errors found in audit log')
    return errors

def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log',type=Path)
    args=parser.parse_args()
    audit_source = static_audit.strip_comments_and_strings(
        (ROOT / 'UniformRandomMALA/DependencyAudit.lean').read_text(encoding='utf-8')
    )
    expected=set(re.findall(r'^#print axioms\s+(\S+)\s*$', audit_source, re.M))
    errors=check(args.log.read_text(encoding='utf-8'),expected)
    if errors:
        print('AXIOM AUDIT FAILED')
        for error in errors: print('- '+error)
        return 1
    print(f'AXIOM AUDIT PASSED: {len(expected)} declarations; only {sorted(ALLOWED)}')
    return 0

if __name__=='__main__': sys.exit(main())
