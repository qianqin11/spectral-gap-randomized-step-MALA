#!/usr/bin/env python3
"""Check that the PDF packaging gate fails closed on missing or altered input."""
import hashlib
from pathlib import Path
import tempfile
import unittest

from manuscript_audit import audit


class ManuscriptAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.paper = root / "paper"
        self.paper.mkdir()
        self.pdf = self.paper / "main.pdf"
        self.pdf.write_bytes(b"%PDF-1.7\nfixture for identity checks only\n%%EOF\n")
        self.checksum = root / "manuscript-pdf.sha256"
        self.record_hash()

    def record_hash(self):
        self.checksum.write_text(
            hashlib.sha256(self.pdf.read_bytes()).hexdigest() + "  paper/main.pdf\n",
            encoding="utf-8",
        )

    def errors(self):
        return audit(self.paper, self.checksum)[0]

    def test_matching_identity(self):
        self.assertEqual(self.errors(), [])

    def test_changed_pdf(self):
        self.pdf.write_bytes(b"%PDF-1.7\nchanged\n%%EOF\n")
        self.assertTrue(any("mismatch" in error for error in self.errors()))

    def test_missing_pdf(self):
        self.pdf.unlink()
        self.assertTrue(any("missing required file: paper/main.pdf" in e for e in self.errors()))

    def test_extra_paper_file(self):
        (self.paper / "main.tex").write_text("extra source", encoding="utf-8")
        self.assertTrue(any("only main.pdf" in error for error in self.errors()))

    def test_missing_checksum(self):
        self.checksum.unlink()
        self.assertTrue(any("missing required file: validation/" in e for e in self.errors()))

    def test_invalid_checksum(self):
        self.checksum.write_text("invalid\n", encoding="utf-8")
        self.assertTrue(any("invalid" in error for error in self.errors()))

    def test_non_pdf_with_matching_hash(self):
        self.pdf.write_bytes(b"not a PDF")
        self.record_hash()
        self.assertTrue(any("header or end marker" in error for error in self.errors()))


if __name__ == "__main__":
    unittest.main()
