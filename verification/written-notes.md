# Written-note PDF compilation

All seven standalone LaTeX notes were compiled on 2026-11-03 using pdfTeX
3.141592653-2.6-1.40.28 (TeX Live 2025/Debian) and latexmk 4.87.
Their PDFs are included beside their source files in
[`docs/written-proofs`](../docs/written-proofs).

| Note | Pages |
| --- | ---: |
| J03–J04: finite tensor algebra and the iterated seam | 7 |
| J08: Coxeter conjugacy | 5 |
| J09: word-grid moves | 9 |
| J11: torus word grids | 11 |
| Factor lower bound | 12 |
| Statement E | 54 |
| Seven obligations: J05, J06, J07, J21, J10, J15, J14 | 129 |

The final runs had no unresolved references or citations, overfull boxes,
underfull text boxes, or duplicate PDF destinations. J09 retains one underfull
vertical-box diagnostic. J03–J04, J08, the seven-obligation note, and Statement E
also emit the installed `longtable` package's nonfatal infinite-glue
page-splitting diagnostic, described in the
[upstream LaTeX issue](https://github.com/latex3/latex2e/issues/1907)
(accessed 2026-11-03).

Formatting changes made for publication concern display breaks, table widths
and justification, and PDF page anchors. They do not change mathematical
statements or proofs. Compilation does not establish mathematical correctness.
The notes retain the historical limitations described in the
[proof guide](../docs/PROOF_GUIDE.md#written-notes-and-the-final-source).

The [source and PDF checksums](written-notes.sha256) identify the included
versions. From the repository root, run:

```bash
sha256sum -c verification/written-notes.sha256
```
