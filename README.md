# Complexity-Sensitive Additive Energy and Off-Diagonal Young Inequalities on Bounded-Degree Algebraic Varieties

Research repository for the paper by **Xiyu Hu**, School of Mathematical Sciences, University of Chinese Academy of Sciences.

- Preprint: [arXiv:2608.18956](https://arxiv.org/abs/2608.18956)
- Manuscript: [`paper/main.pdf`](paper/main.pdf)
- Source: [`paper/main.tex`](paper/main.tex)
- Contact: [hxypqr@gmail.com](mailto:hxypqr@gmail.com)

## Lean formalization

The repository contains an extensive, audited Lean 4 formalization using Lean and mathlib 4.32.0. The finite combinatorial arguments, recurrence mechanisms, weighted estimates, and sharpness constructions represented in the project are kernel checked. The source contains no `sorry`, `admit`, `opaque`, or custom global `axiom` declarations.

The status is deliberately described as an **audited conditional formalization**, not an unconditional formalization of every paper-facing theorem. Several external algebraic-geometric and analytic results are exposed as proposition-valued inputs, and the bridges that generate the recurrence or dyadic certificates used by Theorems 1.1, 1.2, and 1.4 are not yet proved in Lean. Theorem 1.3 likewise retains explicit Fourier/Parseval and complex-interpolation inputs.

For the exact coverage and trust boundary, see:

- [`docs/FORMALIZATION_STATUS.md`](docs/FORMALIZATION_STATUS.md)
- [`docs/EXTERNAL_THEOREM_AUDIT.md`](docs/EXTERNAL_THEOREM_AUDIT.md)
- [`docs/VERIFICATION.md`](docs/VERIFICATION.md)

### Build and audit

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```text
cd formalization
lake build
lake env lean ComplexitySensitiveEnergy/Audit.lean
```

The committed `lean-toolchain` and `lake-manifest.json` pin the toolchain and all Lake dependencies. GitHub Actions performs a clean build and axiom audit whenever a push or pull request changes the Lean package.

## Repository layout

- `paper/`: canonical LaTeX source and compiled PDF.
- `formalization/`: self-contained Lean package and kernel audit.
- `docs/`: formalization status, external-input audit, and verification record.
- `metadata/`: arXiv metadata and publication records.
- `notes/`: proof notes, open questions, computations, and project decisions.
- `references/`: literature tracking and citation notes.

## Build the manuscript

From `paper/`, run:

```text
pdflatex main.tex
pdflatex main.tex
```

The second pass resolves cross-references and the PDF outline.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). Until a journal version is available, please cite the arXiv preprint.

## Rights

No open-source or content license is currently granted. All rights are reserved by the author unless a license is added later.
