#!/usr/bin/env python3
"""Failure-case tests for manuscript assets and paper-to-Lean references."""
import hashlib
from pathlib import Path
import tempfile
import unittest

from manuscript_audit import audit, strip_tex_comments, theorem_labels


class ManuscriptAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.paper = self.root / "paper"
        self.paper.mkdir()
        (self.root / "validation").mkdir()
        (self.root / "UniformRandomMALA").mkdir()
        self.pdf = self.paper / "main.pdf"
        self.pdf.write_bytes(b"%PDF-1.7\nidentity-test fixture\n%%EOF\n")
        self.checksum = self.root / "validation/manuscript-pdf.sha256"
        self.record_hash()
        self.tex = self.paper / "main.tex"
        self.tex.write_text(r"""
\newtheorem{theorem}{Theorem}[section]
\newaliascnt{lemma}{theorem}
\newaliascnt{proposition}{theorem}
\newaliascnt{corollary}{theorem}
\newaliascnt{remark}{theorem}
\begin{document}
\section{Setup}
\begin{theorem}\label{thm:main} Claim. \end{theorem}
\cref{thm:main} \citep{Reference}
\includegraphics{figure.pdf}
\end{document}
""", encoding="utf-8")
        self.bib = self.paper / "uniform_random_mala.bib"
        self.bib.write_text('@article{Reference, title={Title}}', encoding="utf-8")
        (self.paper / "figure.pdf").write_bytes(b"fixture")
        self.lean = self.root / "UniformRandomMALA/Example.lean"
        self.lean.write_text('/-- Theorem 1.1 (`thm:main`). -/', encoding="utf-8")

    def record_hash(self):
        self.checksum.write_text(
            hashlib.sha256(self.pdf.read_bytes()).hexdigest() + "  paper/main.pdf\n",
            encoding="utf-8",
        )

    def errors(self):
        return audit(self.root)[0]

    def has_error(self, fragment):
        self.assertTrue(any(fragment in error for error in self.errors()), self.errors())

    def append_tex(self, text):
        with self.tex.open('a', encoding='utf-8') as file:
            file.write(text)

    def test_valid_restored_source(self):
        self.assertEqual(self.errors(), [])

    def test_changed_pdf(self):
        self.pdf.write_bytes(b"%PDF-1.7\nchanged\n%%EOF\n")
        self.has_error("mismatch")

    def test_missing_pdf(self):
        self.pdf.unlink()
        self.has_error("missing required file")

    def test_missing_tex(self):
        self.tex.unlink()
        self.has_error("main.tex")

    def test_missing_bibliography(self):
        self.bib.unlink()
        self.has_error("uniform_random_mala.bib")

    def test_missing_checksum(self):
        self.checksum.unlink()
        self.has_error("manuscript-pdf.sha256")

    def test_invalid_checksum(self):
        self.checksum.write_text("invalid\n", encoding="utf-8")
        self.has_error("invalid")

    def test_non_pdf_with_matching_hash(self):
        self.pdf.write_bytes(b"not a PDF")
        self.record_hash()
        self.has_error("header or end marker")

    def test_missing_figure(self):
        (self.paper / "figure.pdf").unlink()
        self.has_error("missing figure")

    def test_unresolved_reference(self):
        self.append_tex(r"\ref{lem:missing}")
        self.has_error("unresolved TeX references")

    def test_duplicate_label(self):
        self.append_tex(r"\label{thm:main}")
        self.has_error("duplicate TeX labels")

    def test_unresolved_citation(self):
        self.append_tex(r"\citep{Missing}")
        self.has_error("unresolved citations")

    def test_missing_lean_label(self):
        self.lean.write_text('/-- Lemma `lem:missing`. -/', encoding='utf-8')
        self.has_error("unknown manuscript label")

    def test_wrong_lean_number(self):
        self.lean.write_text('/-- Theorem 1.2 (`thm:main`). -/', encoding='utf-8')
        self.has_error("disagrees")

    def test_wrong_lean_kind(self):
        self.lean.write_text('/-- Lemma 1.1 (`thm:main`). -/', encoding='utf-8')
        self.has_error("disagrees")

    def test_number_without_label(self):
        self.lean.write_text('/-- Theorem 99.9. -/', encoding='utf-8')
        self.has_error("needs an adjacent TeX label")

    def test_number_with_delayed_label(self):
        self.lean.write_text('/-- Theorem 99.9, see `thm:main`. -/', encoding='utf-8')
        self.has_error("needs an adjacent TeX label")

    def test_explicit_external_reference(self):
        self.lean.write_text('/-- Nesterov, Theorem 2.1.5. -/', encoding='utf-8')
        self.assertEqual(self.errors(), [])

    def test_lean_strings_are_not_references(self):
        self.lean.write_text('def s := "lem:absent"\n/- outer /- nested -/ thm:main -/', encoding='utf-8')
        self.assertEqual(self.errors(), [])

    def test_tex_comments_are_ignored(self):
        self.append_tex('\n% \\label{thm:main} \\ref{missing}\n')
        self.assertEqual(self.errors(), [])
        self.assertEqual(strip_tex_comments(r"keep \% value % comment"), r"keep \% value ")

    def test_appendix_shared_counter_and_equation_anchor(self):
        labels = theorem_labels(r"""
\begin{document}
\section{Introduction}\begin{theorem}\label{thm:first}\end{theorem}
\section*{Unnumbered}\begin{lemma}\label{lem:second}\end{lemma}
\appendix\section{First}\section{Second}\section{Gaussian}
\begin{lemma}\label{eq:mills-two-sided}\end{lemma}
\begin{lemma}\label{lem:gaussian-shift}\end{lemma}
""")
        self.assertEqual(labels['lem:second'], ('Lemma', '1.2'))
        self.assertEqual(labels['eq:mills-two-sided'], ('Lemma', 'C.1'))
        self.assertEqual(labels['lem:gaussian-shift'], ('Lemma', 'C.2'))


if __name__ == "__main__":
    unittest.main()
