#!/usr/bin/env python3
"""Source/packaging gate for the C1 revision; not a Lean elaborator or kernel."""
from __future__ import annotations
import json
import re
import sys
from pathlib import Path
import static_audit

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    errors: list[str] = []
    config = (ROOT / 'lakefile.toml').read_text(encoding='utf-8')
    requires = re.findall(r'\[\[require\]\]\s*name\s*=\s*"([^"]+)"', config)
    if requires != ['mathlib']:
        errors.append(f'Expected mathlib as sole direct library dependency, got {requires}')
    manifest = json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
    direct = [p['name'] for p in manifest['packages'] if not p.get('inherited', False)]
    if direct != ['mathlib']:
        errors.append(f'Unexpected direct dependency in Lake manifest: {direct}')
    graph: dict[str, list[str]] = {}
    for path in static_audit.LEAN_FILES:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        text = static_audit.strip_comments_and_strings(path.read_text(encoding='utf-8'))
        imports = static_audit.IMPORT.findall(text)
        graph[module] = [m for m in imports if m.startswith('UniformRandomMALA')]
        for imported in imports:
            if imported.split('.')[0] not in {'UniformRandomMALA','Mathlib','Lean','Init','Std'}:
                errors.append(f'{module}: extra external import {imported}')
        for forbidden in ['native_decide','implemented_by','unsafe','sorryAx','ofReduceBool']:
            if re.search(r'\b' + forbidden + r'\b', text):
                errors.append(f'{module}: forbidden trust shortcut {forbidden}')
    visiting: set[str] = set()
    done: set[str] = set()
    def walk(module: str) -> None:
        if module in visiting:
            errors.append(f'Import cycle through {module}')
            return
        if module in done: return
        visiting.add(module)
        for dep in graph.get(module,[]): walk(dep)
        visiting.remove(module)
        done.add(module)
    for module in graph: walk(module)
    public_root = 'UniformRandomMALA.AllResults'
    public_reachable: set[str] = set()
    def collect_public(module: str) -> None:
        if module in public_reachable: return
        public_reachable.add(module)
        for dep in graph.get(module, []): collect_public(dep)
    collect_public(public_root)
    for required_public in [
        'UniformRandomMALA.Concrete.C1ToFirstOrder',
        'UniformRandomMALA.DiscreteTime.MomentInterpolation',
        'UniformRandomMALA.Concrete.RejectionMomentsOne',
        'UniformRandomMALA.Concrete.C1MainTheorem',
    ]:
        if required_public not in public_reachable:
            errors.append(
                f'{required_public} is not reachable from {public_root}'
            )
    c1 = static_audit.strip_comments_and_strings((ROOT/'UniformRandomMALA/Concrete/C1ToFirstOrder.lean').read_text(encoding='utf-8'))
    record = c1.split('structure C1Potential',1)[1].split('namespace C1Potential',1)[0]
    if 'ContDiff ℝ 1 U' not in record or '∇ U' not in record:
        errors.append('First-order record does not expose C1 and the actual gradient')
    for forbidden in ['ContDiff ℝ 2','iteratedFDeriv','upperTaylor','PaperAnalyticInterfaces','GapCertificates']:
        if forbidden in record: errors.append('Unexpected input in C1 record: '+forbidden)
    for rel in ['Concrete/C1MainTheorem.lean','Concrete/RejectionMomentsOne.lean']:
        text=static_audit.strip_comments_and_strings((ROOT/'UniformRandomMALA'/rel).read_text(encoding='utf-8'))
        for forbidden in ['HessianBoundedPotential','PaperAnalyticInterfaces','GapCertificates']:
            if forbidden in text: errors.append(f'{rel}: unintended input interface {forbidden}')
    if errors:
        print('FIRST-ORDER SOURCE AUDIT FAILED')
        for error in errors: print('- '+error)
        return 1
    print('FIRST-ORDER SOURCE AUDIT PASSED')
    print(f'Local import graph: {len(graph)} modules; no cycles')
    print('Direct external library: mathlib only (standard transitive dependencies retained)')
    print('C1 input: actual gradient; no Hessian or upper-Taylor certificate field')
    print('No detected native_decide, unsafe, implemented_by, sorryAx, or ofReduceBool')
    print('This is a source check, NOT Lean elaboration or kernel verification.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
