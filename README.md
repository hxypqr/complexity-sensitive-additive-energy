# Complexity-Sensitive Additive Energy

Private research workspace for the manuscript **Complexity-Sensitive Additive Energy and Off-Diagonal Young Inequalities on Bounded-Degree Algebraic Varieties** by Xiyu Hu.

> Status: working draft. The manuscript has not yet been peer reviewed or formally published.

## Repository layout

- `paper/`: canonical LaTeX source and the latest compiled PDF.
- `metadata/`: arXiv submission metadata and related publication records.
- `notes/`: proof notes, open questions, computations, and project decisions.
- `references/`: literature tracking and citation notes. Copyrighted papers should not be committed unless redistribution is permitted.
- `formalization/`: proof-assistant roadmap and, later, machine-checked definitions and proofs.

## Build the manuscript

The source is self-contained and uses the `amsart` class. From `paper/`, run:

```text
pdflatex main.tex
pdflatex main.tex
```

The second pass resolves cross-references and the PDF outline.

## Working conventions

- Treat `paper/main.tex` as the canonical manuscript source.
- Name research notes `YYYY-MM-DD-topic.md`.
- Record literature claims with a citation key and a precise location.
- Do not commit passwords, tokens, private referee correspondence, or unrelated unpublished projects.
- Keep formalization code separate from exploratory mathematical notes.

## Rights

No open-source or content license is granted at this stage. All rights are reserved by the author unless a license is added later.
