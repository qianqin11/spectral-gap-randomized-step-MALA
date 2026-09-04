#!/usr/bin/env python3
"""Static checks that do not require a Lean executable.

This is deliberately not presented as a substitute for `lake build`.
It catches accidental placeholders, unresolved local imports, unbalanced
comments/delimiters, and packaging mistakes before kernel checking.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_FILES = sorted(ROOT.glob("*.lean")) + sorted((ROOT / "UniformRandomMALA").rglob("*.lean"))
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom)\b")
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string")
    return "".join(out)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def check_delimiters(path: Path, text: str) -> list[str]:
    errors: list[str] = []
    pairs = {")": "(", "]": "[", "}": "{"}
    stack: list[tuple[str, int]] = []
    for idx, ch in enumerate(text):
        if ch in "([{":
            stack.append((ch, idx))
        elif ch in ")]}":
            if not stack or stack[-1][0] != pairs[ch]:
                errors.append(f"{path}: unmatched {ch!r} at offset {idx}")
                return errors
            stack.pop()
    for ch, idx in stack:
        errors.append(f"{path}: unmatched {ch!r} at offset {idx}")
    return errors


def main() -> int:
    errors: list[str] = []
    declarations = 0
    proof_terms = 0
    for path in LEAN_FILES:
        raw = path.read_text(encoding="utf-8")
        try:
            stripped = strip_comments_and_strings(raw)
        except ValueError as exc:
            errors.append(f"{path}: {exc}")
            continue
        for match in FORBIDDEN.finditer(stripped):
            line = stripped.count("\n", 0, match.start()) + 1
            errors.append(f"{path}:{line}: forbidden placeholder {match.group(0)!r}")
        errors.extend(check_delimiters(path, stripped))
        for module in IMPORT.findall(stripped):
            if module.startswith("UniformRandomMALA") and not module_path(module).exists():
                errors.append(f"{path}: unresolved local import {module}")
        declarations += len(re.findall(r"^\s*(?:def|lemma|theorem|structure)\s+", stripped, re.MULTILINE))
        proof_terms += len(re.findall(r"\bby\b", stripped))
        for no, line in enumerate(raw.splitlines(), 1):
            if line.rstrip() != line:
                errors.append(f"{path}:{no}: trailing whitespace")
            if "\t" in line:
                errors.append(f"{path}:{no}: tab character")

    root_imports = set(IMPORT.findall((ROOT / "UniformRandomMALA.lean").read_text(encoding="utf-8")))
    for path in sorted((ROOT / "UniformRandomMALA").rglob("*.lean")):
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        if path.stem != "Prelude" and module not in root_imports:
            errors.append(f"UniformRandomMALA.lean does not import {module}")

    required = [
        ROOT / "lakefile.toml",
        ROOT / "lean-toolchain",
        ROOT / "README.md",
        ROOT / "PAPER_READER_GUIDE.md",
        ROOT / "REUSABLE_RESULTS.md",
        ROOT / "PROOF_STRATEGY_LEDGER.md",
        ROOT / "PACKAGE_MANIFEST.md",
        ROOT / "FORMALIZATION_STATUS.md",
        ROOT / "THEOREM_MAP.md",
        ROOT / "TRUST_BOUNDARY.md",
        ROOT / "UniformRandomMALA" / "MALAOverlap.lean",
        ROOT / "UniformRandomMALA" / "WeakLimitStability.lean",
        ROOT / "UniformRandomMALA" / "GaussianBobkov.lean",
        ROOT / "UniformRandomMALA" / "BakryLedoux.lean",
        ROOT / "UniformRandomMALA" / "SpectralGap.lean",
        ROOT / "UniformRandomMALA" / "AllResults.lean",
    ]
    for path in required:
        if not path.exists():
            errors.append(f"missing required project file: {path.name}")

    if errors:
        print("STATIC AUDIT FAILED")
        for err in errors:
            print(f"- {err}")
        return 1

    print("STATIC AUDIT PASSED")
    print(f"Lean files: {len(LEAN_FILES)}")
    print(f"Declarations: {declarations}")
    print(f"Explicit `by` proof blocks: {proof_terms}")
    print("Placeholders (`sorry`, `admit`, project `axiom`): none")
    print("Local imports: resolved")
    print("Comments, strings, and (), [], {} delimiters: balanced")
    print("NOTE: this is not a Lean kernel check; run `lake build`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
