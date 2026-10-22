# Paper: one of ζ(7), ζ(9), …, ζ(21) is irrational

LaTeX manuscript for the theorem formalised in this repository (`ZetaIrr.Z7.oneOfZeta7To21`).

| file | content |
|---|---|
| `main.tex` | the manuscript (amsart, single file, no figures) |
| `references.bib` | bibliography; the comment above each entry says how it was checked |

## Building

Requires a TeX distribution with `pdflatex` and `bibtex` and the packages `amsart`, `amsmath`, `amssymb`, `amsthm`,
`booktabs`, `array`, `hyperref` (all standard; tested with MiKTeX 25.12, pdfTeX 4.23). From this folder:

```sh
mkdir -p build
pdflatex -output-directory=build main.tex
cp references.bib build/ && (cd build && bibtex main)
pdflatex -output-directory=build main.tex
pdflatex -output-directory=build main.tex
```

or simply `latexmk -pdf -outdir=build main.tex`. The output is `build/main.pdf` (33 pages). `build/` is not
tracked. The last build (2026-10-22) had no errors, no undefined references and no overfull boxes.

## Sources and conventions

- Mathematics: the informal write-up `handoff/zeta7/PROOF_ZETA.md` of the parent project, with numbers, literature
  and the parameter search from `handoff/zeta7/ZETA7.md` §7 and the review outcome from
  `handoff/zeta7/reviews/SUMMARY.md`.
- Where the Lean formalisation differs from PROOF_ZETA.md (integration by parts instead of the kernel split, no
  boundary term, saddle-point size bound, the integrality form of Lemma A(b′), the pointwise bound for all p ≤ n,
  30,137 event intervals, the Lean saddle contour with ρ = 1/20), the paper follows the formalisation; the
  differences are listed in §9.4 of the paper.
- Structure, tone and the presentation of the certificates follow the β(4..36) paper (`lean_beta/paper/`).
- Status labels ([numerical], [heuristic], [proof sketch], …) are used where the template uses them: for statements
  outside the proof of the main theorem.
- Lean declaration names and file paths in §9 refer to commit `1efbed2` of this repository. A cleanup of the Lean
  sources was in progress in the working tree when the paper was written (some unused declarations removed, e.g.
  `Stirling.stirling_sector`); the paper only cites names that exist both at `1efbed2` and in that working tree, but
  the commit hash in §9.1 and in `references.bib` (`ZetaRepo`) should be updated to the published release.
- The repository is not public yet, so the paper gives no URL for it.
