# Verification

This document records the reproducibility check for the Lean formalization accompanying
*Complexity-Sensitive Additive Energy and Off-Diagonal Young Inequalities on
Bounded-Degree Algebraic Varieties*.

## Environment

- Lean: `v4.32.0`, pinned by `formalization/lean-toolchain`
- mathlib: `v4.32.0`, pinned by `formalization/lakefile.toml` and
  `formalization/lake-manifest.json`
- Verification date: 2026-08-20

## Local check

The source project corresponding byte-for-byte to the committed Lean and Lake files was
built locally with the following commands:

```console
lake build
lake env lean ComplexitySensitiveEnergy/Audit.lean
```

The build completed successfully (`8701` jobs). It produced only linter and style
warnings; there were no compilation errors. GitHub Actions performs the independent
clean-checkout build.

The audit file checks representative paper-facing statements with `#print axioms`.
Their reported dependencies were limited to Lean's standard logical foundations:
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` appeared in the audited
dependency sets.

## Continuous integration

The GitHub Actions workflow at `.github/workflows/lean.yml` uses the toolchain pinned by
the project. It builds the nested package, runs `lean-action`'s axiom audit with
`ComplexitySensitiveEnergy` as the audit root, and executes the project-specific audit
file.

## Scope of the verification

This is a verification of the checked Lean source, not a claim that every theorem in
the paper has been derived unconditionally from mathlib. The internal finite
combinatorics, recurrence, weighted, and turning arguments are kernel-checked. Several
paper-facing upper bounds still depend on explicit external theorem/certificate inputs,
including the bridges from `External.Inputs` to the flagged-recurrence,
granular-threefold-recurrence, and turning-dyadic input structures. Until those bridges
are formalized, the corresponding paper-facing results remain conditional.

See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) and
[`EXTERNAL_THEOREM_AUDIT.md`](EXTERNAL_THEOREM_AUDIT.md) for the detailed trust boundary.
