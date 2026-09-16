#!/usr/bin/env python3
"""Fail-closed identity and packaging audit for the PDF-only manuscript.

This standard-library check does not parse or rebuild LaTeX and does not
certify the PDF's mathematical content, references, or rendering.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
CHECKSUM = ROOT / "validation" / "manuscript-pdf.sha256"


def audit(paper: Path, checksum: Path) -> tuple[list[str], str]:
    errors: list[str] = []
    pdf = paper / "main.pdf"
    if not paper.is_dir():
        errors.append("missing paper directory")
    elif sorted(p.name for p in paper.iterdir()) != ["main.pdf"]:
        errors.append("paper/ must contain only main.pdf")
    if not pdf.is_file():
        errors.append("missing required file: paper/main.pdf")
        return errors, ""
    data = pdf.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if not data.startswith(b"%PDF-") or not data.rstrip().endswith(b"%%EOF"):
        errors.append("main.pdf lacks the expected PDF header or end marker")
    if not checksum.is_file():
        errors.append("missing required file: validation/manuscript-pdf.sha256")
    else:
        match = re.fullmatch(
            r"([0-9a-f]{64})  paper/main\.pdf\n?",
            checksum.read_text(encoding="utf-8"),
        )
        if match is None:
            errors.append("invalid manuscript-pdf.sha256 format")
        elif digest != match[1]:
            errors.append(f"PDF SHA-256 mismatch: actual {digest}; expected {match[1]}")
    return errors, digest


def main() -> int:
    errors, digest = audit(PAPER, CHECKSUM)
    if errors:
        print("MANUSCRIPT PDF AUDIT FAILED", file=sys.stderr)
        for error in errors:
            print("- " + error, file=sys.stderr)
        return 1
    print("MANUSCRIPT PDF AUDIT PASSED")
    print("Bundled manuscript: paper/main.pdf only")
    print("SHA-256: " + digest)
    print("PDF header/end marker and recorded checksum: matched")
    print("TeX, bibliography, and separate figures are not bundled.")
    print("No LaTeX build, reference/citation audit, or Lean kernel check is performed here.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
