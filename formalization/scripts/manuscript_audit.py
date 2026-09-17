#!/usr/bin/env python3
"""Audit the bundled manuscript, bibliography, figures, and Lean references.

Uses only the Python standard library. The theorem-number parser follows the
manuscript's section-based shared theorem/alias counters. A separate LaTeX
build validates the rendered numbering and source/PDF correspondence.
"""
from __future__ import annotations

from collections import Counter
import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LABEL = r"(?:thm|lem|prop|cor|eq|sec|ssec|app|ine|rem):[A-Za-z0-9_-]+"
THEOREM_KINDS = "theorem|lemma|proposition|corollary|remark"


def strip_tex_comments(text: str) -> str:
    return "\n".join(
        strip_line_comment(line) for line in text.splitlines()
    )


def strip_line_comment(line: str) -> str:
    for i, char in enumerate(line):
        if char != "%":
            continue
        backslashes = len(line[:i]) - len(line[:i].rstrip("\\"))
        if backslashes % 2 == 0:
            return line[:i]
    return line


def split_keys(groups: list[str]) -> list[str]:
    return [key.strip() for group in groups for key in group.split(",") if key.strip()]


def theorem_labels(source: str) -> dict[str, tuple[str, str]]:
    """Associate theorem labels (and labels inside them) with kind and number."""
    body = source.split(r"\begin{document}", 1)[-1]
    token = re.compile(
        r"\\appendix\b|\\section(\*)?\s*\{|"
        rf"\\(begin|end)\{{({THEOREM_KINDS})\}}|"
        r"\\label\s*\{([^}]+)\}"
    )
    section = counter = 0
    appendix = False
    current: tuple[str, str] | None = None
    result = {}
    for match in token.finditer(body):
        if match[0].startswith(r"\appendix"):
            appendix, section, counter = True, 0, 0
        elif match[0].startswith(r"\section"):
            if not match[1]:
                section += 1
                counter = 0
        elif match[2] == "begin":
            counter += 1
            prefix = chr(64 + section) if appendix else str(section)
            current = (match[3].capitalize(), f"{prefix}.{counter}")
        elif match[2] == "end":
            current = None
        elif current and match[4]:
            result[match[4]] = current
    return result


def lean_comments(text: str):
    """Yield Lean comments, ignoring strings and respecting nested block comments."""
    i = 0
    while i < len(text):
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            yield i, text[i:end]
            i = end
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            yield start, text[start:i]
        else:
            i += 1


def audit(root: Path) -> tuple[list[str], list[str]]:
    errors, report = [], []
    paper = root / "paper"
    pdf, tex, bib = (paper / name for name in ("main.pdf", "main.tex", "uniform_random_mala.bib"))
    checksum = root / "validation/manuscript-pdf.sha256"
    for path in (pdf, tex, bib, checksum):
        if not path.is_file():
            errors.append(f"missing required file: {path.relative_to(root)}")
    if errors:
        return errors, report
    data = pdf.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if not data.startswith(b"%PDF-") or not data.rstrip().endswith(b"%%EOF"):
        errors.append("main.pdf lacks the expected PDF header or end marker")
    match = re.fullmatch(r"([0-9a-f]{64})  paper/main\.pdf\n?", checksum.read_text(encoding="utf-8"))
    if not match:
        errors.append("invalid manuscript-pdf.sha256 format")
    elif match[1] != digest:
        errors.append(f"PDF SHA-256 mismatch: actual {digest}; expected {match[1]}")
    source = strip_tex_comments(tex.read_text(encoding="utf-8"))
    labels = re.findall(r"\\label\s*\{([^}]+)\}", source)
    label_set = set(labels)
    duplicates = [label for label, count in Counter(labels).items() if count > 1]
    if duplicates:
        errors.append("duplicate TeX labels: " + ", ".join(sorted(duplicates)))
    refs = split_keys(re.findall(r"\\(?:eqref|ref|pageref|autoref|cref|Cref)\s*\{([^}]+)\}", source))
    if missing := set(refs) - label_set:
        errors.append("unresolved TeX references: " + ", ".join(sorted(missing)))
    bib_keys = re.findall(r"@[a-zA-Z]+\s*\{\s*([^,\s]+)\s*,", strip_tex_comments(bib.read_text(encoding="utf-8")))
    if duplicates := [key for key, count in Counter(bib_keys).items() if count > 1]:
        errors.append("duplicate bibliography keys: " + ", ".join(sorted(duplicates)))
    citations = split_keys(re.findall(r"\\cite[a-zA-Z]*\s*(?:\[[^\]]*\]\s*)*\{([^}]+)\}", source))
    if missing := set(citations) - set(bib_keys):
        errors.append("unresolved citations: " + ", ".join(sorted(missing)))
    graphics = re.findall(r"\\includegraphics\s*(?:\[[^\]]*\]\s*)*\{([^}]+)\}", source)
    for graphic in graphics:
        path = (paper / graphic.strip()).resolve()
        if not path.is_relative_to(paper.resolve()):
            errors.append("figure lies outside paper/: " + graphic)
        elif not any(p.is_file() for p in ([path] if path.suffix else [path.with_suffix('.pdf'), path])):
            errors.append("missing figure: " + graphic)
    if not re.search(r"\\newtheorem\{theorem\}\{Theorem\}\[section\]", source):
        errors.append("unsupported theorem counter: expected section-based theorem numbering")
    for kind in ("lemma", "proposition", "corollary", "remark"):
        if rf"\newaliascnt{{{kind}}}{{theorem}}" not in source:
            errors.append(f"unsupported {kind} counter: expected shared theorem alias")
    numbers = theorem_labels(source)
    lean_refs = pairs = 0
    numbered_pair = re.compile(
        rf"\b(Theorem|Lemma|Proposition|Corollary)\s+([A-Z0-9]+\.\d+)"
        rf"\s*\(`({LABEL})`\)"
    )
    numbered_mention = re.compile(
        r"\b(Theorem|Lemma|Proposition|Corollary)\s+([A-Z0-9]+(?:\.\d+)+)\b"
    )
    paths = sorted((root / "UniformRandomMALA").rglob("*.lean")) + sorted(root.glob("*.lean"))
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for offset, comment in lean_comments(text):
            line = text[:offset].count("\n") + 1
            location = f"{path.relative_to(root)}:{line}"
            for label in re.findall(LABEL, comment):
                lean_refs += 1
                if label not in label_set:
                    errors.append(f"{location}: unknown manuscript label {label}")
            for mention in numbered_mention.finditer(comment):
                # The descent lemma cites this external textbook theorem.
                if mention.groups() == ("Theorem", "2.1.5") and "Nesterov" in comment:
                    continue
                if not numbered_pair.match(comment, mention.start()):
                    errors.append(f"{location}: numbered manuscript reference needs an adjacent TeX label: {mention[0]}")
            for kind, number, label in numbered_pair.findall(comment):
                pairs += 1
                if numbers.get(label) != (kind, number):
                    errors.append(f"{location}: {kind} {number} disagrees with {label}: {numbers.get(label)}")
    report.extend([
        f"PDF SHA-256: {digest}",
        "Bundled manuscript: main.tex, main.pdf, bibliography, and referenced figures",
        f"TeX labels: {len(labels)}; references: {len(refs)} uses over {len(set(refs))} labels",
        f"Citations: {len(citations)} key uses over {len(set(citations))} keys; bibliography: {len(bib_keys)} entries",
        f"Figures: {len(graphics)} includes",
        f"Lean manuscript labels: {lean_refs} uses; numbered theorem/label pairs: {pairs}",
        "Source checks only; LaTeX compilation and Lean kernel verification are separate checks.",
    ])
    return errors, report


def main() -> int:
    errors, report = audit(ROOT)
    if errors:
        print("MANUSCRIPT AUDIT FAILED", file=sys.stderr)
        for error in errors:
            print("- " + error, file=sys.stderr)
        return 1
    print("MANUSCRIPT AUDIT PASSED")
    for line in report:
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
