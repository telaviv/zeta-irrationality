# Paper: one of ζ(7), ζ(9), …, ζ(21) is irrational

LaTeX manuscript for the theorem formalised in this repository (`ZetaIrr.Z7.oneOfZeta7To21`).

| file | content |
|---|---|
| `main.tex` | the manuscript (amsart, single file, no figures) |
| `references.bib` | bibliography (with DOIs or arXiv identifiers) |

## Building

Requires a TeX distribution with `pdflatex` and `bibtex` and the standard packages `amsart`, `amsmath`, `amssymb`,
`amsthm`, `booktabs`, `array`, `hyperref`. From this folder:

```sh
mkdir -p build
pdflatex -output-directory=build main.tex
cp references.bib build/ && (cd build && bibtex main)
pdflatex -output-directory=build main.tex
pdflatex -output-directory=build main.tex
```

or simply `latexmk -pdf -outdir=build main.tex`. The output is `build/main.pdf`; `build/` is not tracked.

Section 9 of the paper describes the formalisation; its Lean names and file paths refer to tag v1.0 of this
repository (https://github.com/telaviv/zeta-irrationality).
